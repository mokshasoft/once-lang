# Once icon: regenerate once.svg, once-dark.svg and every raster made from
# once.svg.
#
#   make          the SVGs and all the files below (all committed)
#   make clean    remove build/
#
# Needs runghc (from `nix develop` at the repo root) and ImageMagick 7
# (magick) with librsvg.

BUILD := build

# transparent background
TRANSPARENT := favicon.ico icon-192.png icon-512.png
# opaque white background: iOS fills transparency with black
OPAQUE := apple-touch-icon.png social-preview.png

.PHONY: all clean

all: once.svg once-dark.svg $(TRANSPARENT) $(OPAQUE)

once.svg once-dark.svg &: Gen.hs
	runghc -Wall Gen.hs

# $(call render,px,bg): once.svg rasterised at a high density, scaled to px;
# no timestamps or other metadata, so a rebuild is byte-identical
PNG_OPTS := -depth 8 -strip -define png:exclude-chunks=date,time
render = magick -background '$(2)' -density 768 once.svg -resize $(1)x$(1)

# browsers pick the size they need from the one file
favicon.ico: once.svg
	@mkdir -p $(BUILD)
	@for s in 16 32 48; do $(call render,$$s,none) $(BUILD)/fav-$$s.png; done
	magick $(BUILD)/fav-16.png $(BUILD)/fav-32.png $(BUILD)/fav-48.png $@

icon-%.png: once.svg
	$(call render,$*,none) $(PNG_OPTS) $@

apple-touch-icon.png: once.svg
	$(call render,180,white) -flatten -alpha off $(PNG_OPTS) $@

# 1280 x 640, GitHub's recommended social preview size: the mark at 480 px,
# centred on white
social-preview.png: once.svg
	$(call render,480,white) -flatten -alpha off -gravity center \
	  -extent 1280x640 $(PNG_OPTS) $@

clean:
	rm -rf $(BUILD)
