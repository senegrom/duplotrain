# App icons

The editable source is [`duplotrain-icon.svg`](../src/duplotrain/static/duplotrain-icon.svg):
a red toy locomotive with a blue cab, golden wheels and a looping railway on an
ivory tile. Its green background and tile treatment share TheoreticalRacing's
app-icon style; the train artwork is specific to duplotrain.

Regenerate the committed PNG/ICO exports from the repository root:

```sh
python -m pip install -r webapp/requirements-icons.txt
python webapp/export_icons.py
```

Exports include 16/32 px tab PNGs, a 16/32/48 px ICO, Apple 152/167/180 px PNGs,
192/512 px app PNGs and a separate 512 px maskable icon. Every PNG is opaque RGB.
The source fills the square without pre-cut outer corners; the operating system
applies its own mask. The maskable export keeps the entire artwork inside the
central 80%-diameter safe circle.

The HTML explicitly links the icons and Apple standalone/title/status-bar metadata.
The manifest has an explicit `/duplotrain/` ID, distinct from `/TheoreticalRacing/`.
Manifest IDs resolve against the origin, not the manifest directory; `./` would
accidentally identify the shared site root. The ID is an identifier, not a launch
route. Relative scope, start URL and asset URLs keep the same files working on
GitHub Pages and at the local editor's root.
The manifest configures Home Screen launch; it does not add offline support.

The PNG/ICO files are committed as Python package data and copied into
`webapp/dist/` by the static build. They stay out of the Pyodide worker archive.
Image-export dependencies are only needed when changing the artwork, not to
install, build or use the app.

Icon URLs include `duplotrain` and a revision in their physical filenames, following
TheoreticalRacing's cache-isolation approach. For future artwork changes, bump
`v1` in the exporter, HTML, manifest and local server asset allowlist together.
Conventional `favicon.ico` and `apple-touch-icon.png` aliases are also included.
An existing iOS Home Screen shortcut may need to be removed and re-added to
refresh its cached icon.
