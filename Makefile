HUGO ?= hugo
CHECK_DIR ?= /tmp/keydocs-check

.PHONY: prepare serve build check clean

# Resolve and download the Hugo modules pinned in go.mod/go.sum (Hextra).
prepare:
	$(HUGO) mod tidy

# Live preview on http://localhost:1313 with drafts and reloads enabled.
serve:
	$(HUGO) server --logLevel debug --disableFastRender -p 1313

# Production build into public/.
build:
	$(HUGO) --gc --minify

# Build into a scratch directory and check every internal link.
#
# The site is built with a root-relative base URL so that lychee can resolve
# absolute paths such as /devel/architecture/ against CHECK_DIR. External links
# are skipped (--offline); only links into the generated site are verified.
# static/eclipse/index.old.html is an archived copy of the pre-Hugo landing
# page and is excluded: it is not part of the site navigation and still points
# at the old Eclipse image locations.
check:
	rm -rf $(CHECK_DIR)
	$(HUGO) --gc --minify --cleanDestinationDir --baseURL "/" --destination $(CHECK_DIR)
	@command -v lychee >/dev/null 2>&1 || { \
		echo "ERROR: lychee is not installed, so the link check cannot run." >&2; \
		echo "       Install it from https://github.com/lycheeverse/lychee#installation" >&2; \
		exit 1; }
	find $(CHECK_DIR) -type f -name '*.html' ! -name '*.old.html' -print0 \
		| xargs -0 lychee --offline --no-progress --root-dir $(CHECK_DIR)

clean:
	rm -rf public resources $(CHECK_DIR)
