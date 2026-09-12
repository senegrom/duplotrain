"""Export the editable train SVG to opaque browser and Home Screen icons.

Install webapp/requirements-icons.txt to regenerate the committed assets.
The app, Python package and static build do not need the image dependencies.
"""

from __future__ import annotations

import io
import shutil
from pathlib import Path

import cairosvg
from PIL import Image

STATIC = Path(__file__).resolve().parents[1] / "src/duplotrain/static"
SIZES = {
    "tab-16": 16,
    "tab-32": 32,
    "apple-152": 152,
    "apple-167": 167,
    "apple-180": 180,
    "app-192": 192,
    "app-512": 512,
}


def export() -> None:
    icons = STATIC / "icons"
    icons.mkdir(parents=True, exist_ok=True)
    png = cairosvg.svg2png(
        url=str(STATIC / "duplotrain-icon.svg"), output_width=1024, output_height=1024,
    )
    with Image.open(io.BytesIO(png)) as rendered:
        master = rendered.convert("RGB")
    for name, size in SIZES.items():
        master.resize((size, size), Image.Resampling.LANCZOS).save(
            icons / f"duplotrain-{name}-v1.png", optimize=True,
        )
    master.save(
        icons / "duplotrain-favicon-v1.ico", format="ICO",
        sizes=[(16, 16), (32, 32), (48, 48)],
    )
    # The entire square artwork fits inside the central 80%-diameter circle:
    # 280 * sqrt(2) / 2 < 512 * .4. Let the OS apply its own outer mask.
    maskable = Image.new("RGB", (512, 512), "#163e32")
    maskable.paste(master.resize((280, 280), Image.Resampling.LANCZOS), (116, 116))
    maskable.save(icons / "duplotrain-maskable-512-v1.png", optimize=True)
    # Conventional discovery paths, alongside explicit app-specific filenames.
    shutil.copyfile(icons / "duplotrain-favicon-v1.ico", STATIC / "favicon.ico")
    shutil.copyfile(icons / "duplotrain-apple-180-v1.png", STATIC / "apple-touch-icon.png")
    print(f"Exported duplotrain favicon, Apple and app icons to {STATIC}")


if __name__ == "__main__":
    export()
