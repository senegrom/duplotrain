"""Command-line interface.

The flow a parent with a box of DUPLO wants::

    duplotrain solve --curve 12 --straight 4 -o out

...and out come ranked pictures of every distinct loop those pieces can build.
"""

from __future__ import annotations

import importlib
import json
import math
import re
import tempfile
from pathlib import Path

import click
from rich.console import Console
from rich.markup import escape
from rich.table import Table

from . import __version__
from .catalog import default_catalog, load_catalog
from .drive import DEFAULT_MAX_RUNS, ClassificationLimitError, DriveLimitError, classify
from .layout import layout_from_dict, layout_to_dict
from .scoring import score_solution
from .sets import SETS, inventory_for_sets
from .solver import SolverConfig, solve
from .validation import MAX_INVENTORY_COUNT, MAX_JSON_BYTES, check_inventory

console = Console()


#: What reading an untrusted JSON file can raise short of a bug: bad values and
#: shapes (JSONDecodeError is a ValueError), unreadable files, absurd nesting.
_BAD_FILE = (ValueError, TypeError, KeyError, OSError, RecursionError)

#: The files ``solve -o`` writes, one pair per saved loop.
_SAVED_NAME = re.compile(r"loop_\d{2,}\.(?:json|png)")
#: The smallest loop ``solve`` looks for unless told otherwise.
_MIN_PIECES = 4


def _catalog(paths: tuple[str, ...]):
    try:
        return load_catalog(*paths) if paths else default_catalog()
    except _BAD_FILE as exc:
        raise click.ClickException(f"bad catalogue file: {exc}") from exc


def _image_target(out: str) -> str:
    """matplotlib saves an extension-less name as PNG; name the file it writes."""
    return out if Path(out).suffix else f"{out}.png"


def _write_image(render_layout, layout: object, target: str, **options: object) -> None:
    try:
        render_layout(layout, path=target, **options)
    except (ValueError, OSError) as exc:  # unknown format, missing directory
        raise click.ClickException(f"cannot write {target}: {exc}") from exc


def _finite(_ctx: click.Context, _param: click.Parameter, value: float) -> float:
    """A --slop budget: FloatRange admits inf and nan, a gap budget must be finite."""
    if not math.isfinite(value):
        raise click.BadParameter("must be finite")
    return value


_catalog_option = click.option(
    "--catalog",
    "catalog_paths",
    multiple=True,
    type=click.Path(exists=True),
    help="Extra piece-catalogue JSON, overriding built-ins by id.",
)


@click.group()
@click.version_option(version=__version__, prog_name="duplotrain")
def main() -> None:
    """Model DUPLO train track and find layouts that loop nicely."""


@main.command()
@_catalog_option
@click.option("--json", "as_json", is_flag=True, help="Machine-readable output.")
def pieces(catalog_paths: tuple[str, ...], as_json: bool) -> None:
    """List the known track pieces."""
    catalog = _catalog(catalog_paths)
    if as_json:
        payload = [
            {
                "id": p.id,
                "name": p.name,
                "category": p.category,
                "ports": len(p.ports),
                "part_numbers": list(p.part_numbers),
                "provisional": p.provisional,
                "notes": p.notes,
            }
            for p in catalog.values()
        ]
        click.echo(json.dumps(payload, indent=2))
        return
    table = Table(title="DUPLO track pieces")
    table.add_column("id", style="bold")
    table.add_column("name")
    table.add_column("ports", justify="right")
    table.add_column("parts")
    table.add_column("notes", max_width=60)
    for p in catalog.values():
        # Catalogue text is printed as it is, never read as markup.
        name = escape(p.name) + (" [dim](provisional)[/dim]" if p.provisional else "")
        table.add_row(escape(p.id), name, str(len(p.ports)), escape(", ".join(p.part_numbers)),
                      escape(p.notes))
    console.print(table)


def _inventory_options(fn):
    for pid in reversed(list(default_catalog())):
        fn = click.option(
            f"--{pid.replace('_', '-')}",
            pid,
            type=click.IntRange(0, MAX_INVENTORY_COUNT),
            default=0,
            help=f"Non-negative whole number of '{pid}' pieces you own.",
        )(fn)
    return fn


@main.command(name="sets")
def sets_cmd() -> None:
    """List the LEGO sets the inventory shortcut knows about."""
    table = Table(title="Known DUPLO train sets (use with: solve --set 10882)")
    table.add_column("set", style="bold")
    table.add_column("name")
    table.add_column("track pieces")
    table.add_column("action stones")
    table.add_column("notes", max_width=60)
    for s in SETS.values():
        table.add_row(
            s.code,
            f"{s.name} ({s.year})",
            ", ".join(f"{n}x {pid}" for pid, n in s.pieces.items()),
            ", ".join(f"{n}x {sid.removeprefix('stone_')}" for sid, n in s.stones.items())
            or "-",
            s.notes,
        )
    console.print(table)


@main.command(name="solve")
@_inventory_options
@click.option(
    "--set",
    "set_codes",
    multiple=True,
    help="Add a whole boxed set's pieces (e.g. --set 10874 --set 10882); repeatable.",
)
@click.option(
    "--inventory",
    "inventory_path",
    type=click.Path(exists=True),
    help=(
        'JSON file {"curve": 12, "straight": 4, ...}; merged with the flags. '
        "Pieces added via --catalog have no dedicated flag and are counted here."
    ),
)
@_catalog_option
@click.option(
    "--slop",
    type=click.FloatRange(min=0),
    default=0.0,
    show_default=True,
    callback=_finite,
    help="Total closing gap (mm) the joints may absorb; 0 = exact loops only.",
)
@click.option("--min-pieces", type=click.IntRange(min=0), default=_MIN_PIECES,
              show_default=True)
@click.option("--max-results", type=click.IntRange(min=1), default=25, show_default=True)
@click.option("--max-nodes", type=click.IntRange(min=1), default=2_000_000, show_default=True)
@click.option("--use-all", is_flag=True, help="Only layouts using every owned piece.")
@click.option(
    "--reversing/--no-reversing",
    default=None,
    help=(
        "Also propose reversing loops (teardrops closing into a switch branch); the "
        "train needs a direction-change stone on the tail. Default: on when a --set "
        "provides that stone."
    ),
)
@click.option(
    "-o",
    "--out",
    type=click.Path(file_okay=False),
    default=None,
    help=(
        "Directory for rendered images and layout JSON, replacing an earlier run's "
        "loop_NN files there; omit for a text listing only."
    ),
)
@click.option("--top", type=click.IntRange(min=0), default=10, show_default=True,
              help="How many to save.")
def solve_cmd(
    inventory_path: str | None,
    set_codes: tuple[str, ...],
    catalog_paths: tuple[str, ...],
    slop: float,
    min_pieces: int,
    max_results: int,
    max_nodes: int,
    use_all: bool,
    reversing: bool | None,
    out: str | None,
    top: int,
    **flag_counts: int,
) -> None:
    """Find closed loops buildable from your pieces."""
    catalog = _catalog(catalog_paths)

    inventory: dict[str, int] = {k: v for k, v in flag_counts.items() if v > 0}
    stones: dict[str, int] = {}
    if set_codes:
        try:
            set_pieces, stones = inventory_for_sets(set_codes)
        except ValueError as exc:
            raise click.ClickException(str(exc)) from exc
        for k, v in set_pieces.items():
            inventory[k] = inventory.get(k, 0) + v
    if inventory_path:
        try:
            raw_counts = json.loads(Path(inventory_path).read_bytes())
            # Validate the file's own values: once merged with the flags', a
            # negative count could hide in the sum.
            check_inventory(raw_counts, catalog)
            for k, v in raw_counts.items():
                inventory[k] = inventory.get(k, 0) + v
        except _BAD_FILE as exc:
            raise click.ClickException(f"bad inventory file: {exc}") from exc
    if not any(inventory.values()):
        raise click.UsageError(
            "Tell me what you own, e.g.:  duplotrain solve --curve 12 --straight 4 "
            "or --set 10874 --set 10882"
        )

    if reversing is None:
        reversing = stones.get("stone_direction", 0) > 0
        if reversing:
            console.print(
                "[dim]Your sets include a direction-change stone: reversing loops "
                "enabled (--no-reversing to disable).[/dim]"
            )

    try:
        config = SolverConfig(
            slop=slop,
            min_pieces=min_pieces,
            max_results=max_results,
            max_nodes=max_nodes,
            use_all_pieces=use_all,
            reversing_loops=reversing,
        )
        # Before the search: an unusable directory must not cost a whole search.
        out_dir = _output_dir(out) if out else None
        with console.status("searching for loops..."):
            result = solve(inventory, catalog, config)
    except ValueError as exc:
        raise click.ClickException(str(exc)) from exc
    stats = result.stats

    scored = sorted(
        (
            (score_solution(sol, inventory).total, sol)
            for sol in result.solutions
        ),
        key=lambda pair: -pair[0],
    )
    # Even a run that finds nothing replaces an earlier run's files.
    if out_dir is not None:
        _clear_earlier_results(out_dir)

    console.print(
        f"[bold]{len(scored)}[/bold] distinct loop(s) found "
        f"({stats.nodes:,} states searched in {stats.duration_s:.1f}s"
        + (f", [yellow]stopped: {stats.stop_reason}[/yellow]" if not stats.complete else "")
        + ")"
    )
    if not scored:
        if not stats.complete:
            console.print("No loop found within the search limits; a closure may still exist.")
            return
        # Suggest only what this run did not try already.
        tips = ["without [bold]--use-all[/bold]"] if use_all else []
        if min_pieces > _MIN_PIECES:
            tips.append("a lower [bold]--min-pieces[/bold]")
        tips.append("more curves (12 make a circle)")
        if not slop:
            tips.append("forced fits with [bold]--slop 5[/bold]")
        console.print("No closed loop fits. Try " + ", or ".join(tips) + ".")
        return

    # One closure label and size per loop, for the table and the pictures alike.
    rows = []
    for score, sol in scored:
        closure = "exact" if sol.exact else f"forced ({sol.gap:.1f} mm)"
        if sol.kind == "reversing":
            closure += " reversing"
        width, height = sol.layout.size()
        rows.append((score, sol, closure, f"{width / 10:.0f} x {height / 10:.0f}"))

    table = Table(title="Loops, nicest first")
    table.add_column("#", justify="right")
    table.add_column("score", justify="right")
    table.add_column("pieces")
    table.add_column("size (cm)", justify="right")
    table.add_column("closure")
    table.add_column("stubs", justify="right")
    for rank, (score, sol, closure, size) in enumerate(rows, start=1):
        counts = " ".join(
            f"{n}x{pid}" for pid, n in sorted(sol.layout.piece_counts.items())
        )
        table.add_row(str(rank), f"{score:.0f}", escape(counts), size, closure,
                      str(sol.open_stubs))
    console.print(table)

    if out_dir is not None:
        render_layout = _get_renderer(required=False)
        for rank, (score, sol, closure, size) in enumerate(rows[:top], start=1):
            stem = out_dir / f"loop_{rank:02d}"
            try:
                with open(f"{stem}.json", "w", encoding="utf-8") as fh:
                    json.dump(layout_to_dict(sol.layout), fh, indent=2)
            except OSError as exc:
                raise click.ClickException(f"cannot write {stem}.json: {exc}") from exc
            if render_layout is not None:
                _write_image(
                    render_layout, sol.layout, f"{stem}.png",
                    title=f"#{rank}  score {score:.0f}  |  {closure}  |  {size} cm",
                )
        console.print(f"Saved the top {min(top, len(scored))} to "
                      f"[bold]{escape(str(out_dir))}[/bold]")


def _get_renderer(required: bool = True):
    try:
        importlib.import_module("matplotlib")
    except ModuleNotFoundError as exc:
        if exc.name != "matplotlib":
            raise
        message = "matplotlib not installed; install duplotrain[render] to render images"
        if required:
            raise click.ClickException(message) from exc
        console.print(f"{message}; writing layout JSON only", style="yellow", markup=False)
        return None
    from .render import render_layout

    return render_layout


def _output_dir(out: str) -> Path:
    """Create *out*, and check this run can write and list it, before the search."""
    out_dir = Path(out)
    try:
        out_dir.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise click.ClickException(f"cannot create {out_dir}: {exc}") from exc
    try:
        with tempfile.TemporaryFile(dir=out_dir):
            pass
        next(out_dir.iterdir(), None)
    except OSError as exc:
        raise click.ClickException(f"cannot write to {out_dir}: {exc}") from exc
    return out_dir


def _clear_earlier_results(out_dir: Path) -> None:
    """Delete an earlier run's loop_NN files from *out_dir*."""
    # The directory holds one run's results: an earlier run's files would
    # outnumber a smaller result set, or picture other loops than the JSON
    # beside them when this run saves no images.
    try:
        for stale in [path for path in out_dir.iterdir()
                      if _SAVED_NAME.fullmatch(path.name) and not path.is_dir()]:
            stale.unlink()
    except OSError as exc:
        raise click.ClickException(
            f"cannot replace the earlier results in {out_dir}: {exc}") from exc


def _load_layout(layout_file: str, catalog):
    try:
        with open(layout_file, "rb") as fh:
            raw = fh.read(MAX_JSON_BYTES + 1)
        if len(raw) > MAX_JSON_BYTES:
            raise ValueError("layout file larger than 2 MB")
        # From bytes, JSON takes UTF-8 (with or without a byte-order mark), -16 or -32.
        return layout_from_dict(json.loads(raw), catalog)
    except _BAD_FILE as exc:
        raise click.ClickException(f"bad layout file: {exc}") from exc


@main.command()
@click.argument("layout_file", type=click.Path(exists=True))
@_catalog_option
@click.option("-o", "--out", type=click.Path(dir_okay=False), default=None)
def render(layout_file: str, catalog_paths: tuple[str, ...], out: str | None) -> None:
    """Render a saved layout JSON to an image."""
    render_layout = _get_renderer()

    catalog = _catalog(catalog_paths)
    layout = _load_layout(layout_file, catalog)
    target = _image_target(out) if out else str(Path(layout_file).with_suffix(".png"))
    _write_image(render_layout, layout, target)
    console.print(f"Wrote [bold]{escape(target)}[/bold]")


@main.command()
@click.argument("layout_file", type=click.Path(exists=True))
@_catalog_option
@click.option(
    "--slop", type=click.FloatRange(min=0), default=0.0, show_default=True, callback=_finite,
    help="Accept this total planar joint gap in mm; never ignores height or heading errors.",
)
def check(layout_file: str, catalog_paths: tuple[str, ...], slop: float) -> None:
    """Check recorded joints and closure. Exit 1 for open or unacceptable layouts.

    A positive --slop accepts a forced fit within that total planar gap budget,
    not an exact closure or a guarantee that physical track will fit.
    """
    catalog = _catalog(catalog_paths)
    layout = _load_layout(layout_file, catalog)
    width, height = layout.size()
    console.print(
        f"{len(layout)} pieces, {layout.track_length() / 10:.0f} cm of track, "
        f"{width / 10:.0f} x {height / 10:.0f} cm footprint"
    )
    issues = layout.joint_issues()
    if layout.is_closed and not issues:
        console.print("[green]Fully closed: every connector is exactly mated.[/green]")
        console.print("Joint geometry checked; collisions elsewhere are not checked.")
        return
    if layout.is_closed:
        console.print("[yellow]Fully linked, but not exactly closed.[/yellow]")
    else:
        console.print(f"[yellow]{len(layout.connectable_ends())} open end(s).[/yellow]")
        if not len(layout):
            console.print("Empty layout; no closed track.")
        for a, b, gap in layout.gaps(limit=5):
            console.print(f"  Open ends {a} <-> {b}: gap {gap:.6g} mm")
    for joint in issues:
        a, b = tuple(joint["a"]), tuple(joint["b"])
        console.print(
            f"  Joint {a} <-> {b}: {', '.join(joint['problems'])}; "
            f"planar gap {joint['gap_mm']:.6g} mm, "
            f"height difference {joint['height_mm']:.6g} mm, "
            f"heading error {joint['heading_error_deg']} deg"
        )
    if issues:
        total_gap = sum(joint["gap_mm"] for joint in issues)
        planar_only = all(joint["problems"] == ["planar gap"] for joint in issues)
        if planar_only:
            console.print(f"Forced fit: total planar gap {total_gap:.6g} mm.")
            if layout.is_closed and slop > 0 and total_gap <= slop:
                console.print(
                    f"Within requested slop budget {slop:g} mm; physical fit not verified."
                )
                return
            console.print(f"Not accepted as closed within slop budget {slop:g} mm.")
        else:
            console.print("[red]Incompatible joint(s); planar slop cannot repair these.[/red]")
    raise click.exceptions.Exit(1)


@main.command(name="classify")
@click.argument("layout_file", type=click.Path(exists=True))
@click.option(
    "--max-runs", type=click.IntRange(min=1), default=DEFAULT_MAX_RUNS, show_default=True,
    help="Maximum simulations; exceeding this budget produces no verdict.",
)
@_catalog_option
def classify_cmd(layout_file: str, catalog_paths: tuple[str, ...], max_runs: int) -> None:
    """Where does a saved layout sit on the looping ladder?

    Simulates a train entering every drivable piece through each of its connectors,
    under every initial switch-tongue setting, with the layout's action stones in
    effect. Joints must be exact: `check` lists any that are not.
    """
    catalog = _catalog(catalog_paths)
    layout = _load_layout(layout_file, catalog)
    if layout.joint_issues():
        # The model follows recorded links: a joint that cannot exist would be
        # driven through as if it did.
        raise click.ClickException(
            "classify needs track whose joints fit exactly; `duplotrain check` lists them")
    try:
        verdict = classify(layout, max_runs=max_runs)
    except ClassificationLimitError as exc:
        raise click.ClickException(str(exc).replace("max_runs", "--max-runs")) from exc
    except (ValueError, DriveLimitError) as exc:  # an empty layout; an endless-run guard
        raise click.ClickException(str(exc)) from exc
    if not verdict.runs:  # only buffers: nowhere to place a train
        raise click.ClickException("nothing to classify: no drivable track")
    ladder = [
        ("locally looping", verdict.locally_looping, "some placement runs forever"),
        ("looping", verdict.looping, "every placement runs forever"),
        ("completely looping", verdict.completely_looping, "and every run covers all track"),
        ("perfectly looping", verdict.perfectly_looping, "and sweeps every tile both ways"),
    ]
    for name, holds, meaning in ladder:
        mark = "[green]yes[/green]" if holds else "[red]no[/red]"
        console.print(f"  {name:20s} {mark}   [dim]{meaning}[/dim]")
    console.print(f"[dim]{verdict.runs} simulated runs[/dim]")
    if verdict.counterexample:
        start, tongues, outcome = verdict.counterexample
        detail = f" with tongues {tongues}" if tongues else ""
        console.print(
            f"first failure: a train entering piece {start[0]} via port {start[1]}"
            f"{detail} -> {outcome}"
        )


@main.command()
@click.option("--port", type=click.IntRange(0, 65535), default=8137, show_default=True)
@click.option("--no-browser", is_flag=True, help="Don't open a browser tab.")
def gui(port: int, no_browser: bool) -> None:
    """Open the interactive track designer in your browser.

    Build track by clicking pieces onto open ends, then let the solver close the
    loop with whatever is left in your box.
    """
    from .gui import run

    try:
        run(port=port, open_browser=not no_browser)
    except OSError as exc:  # the port is taken, or the address is unavailable
        raise click.ClickException(f"cannot serve on port {port}: {exc}") from exc


@main.command()
@click.option("-o", "--out", type=click.Path(dir_okay=False), default="oval.png")
def demo(out: str) -> None:
    """Build and render the classic starter oval (12 curves + 4 straights)."""
    render_layout = _get_renderer()

    catalog = default_catalog()
    result = solve(
        {"curve": 12, "straight": 4},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=5),
    )
    best = result.solutions[0]
    target = _image_target(out)
    _write_image(render_layout, best.layout, target, title="The classic DUPLO oval")
    console.print(
        f"The starter oval closes exactly; picture in [bold]{escape(target)}[/bold]. "
        "Now try:  duplotrain solve --curve 12 --straight 4 --switch 2 -o out"
    )


if __name__ == "__main__":
    main()
