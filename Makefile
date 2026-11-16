HUGO ?= hugo
HUGO_VERSION ?= 0.170.0
CHECK_DIR ?= /tmp/keydocs-check

.DEFAULT_GOAL := build
.PHONY: help prepare serve build check ci update version clean

help:
	@echo "Targets:"
	@echo "  prepare   resolve/download the Hugo modules pinned in go.mod"
	@echo "  serve     live preview on http://localhost:1313"
	@echo "  build     production build into public/ (default)"
	@echo "  check     scratch build + internal link check (needs lychee)"
	@echo "  ci        build + check"
	@echo "  update    update the Hextra module and tidy go.mod/go.sum"
	@echo "  version   print the installed and expected Hugo versions"
	@echo "  clean     remove public/, resources/ and the scratch build"

# Resolve and download the Hugo modules pinned in go.mod/go.sum (Hextra).
prepare:
	$(HUGO) mod tidy

# Live preview on http://localhost:1313 with live reload.
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
check:
	@command -v lychee >/dev/null 2>&1 || { \
		echo "ERROR: lychee is not installed, so the link check cannot run." >&2; \
		echo "       Install it from https://github.com/lycheeverse/lychee#installation" >&2; \
		exit 1; }
	rm -rf $(CHECK_DIR)
	$(HUGO) --gc --minify --cleanDestinationDir --baseURL "/" --destination $(CHECK_DIR)
	find $(CHECK_DIR) -type f -name '*.html' -print0 \
		| xargs -0 lychee --offline --no-progress --root-dir $(CHECK_DIR)

ci: build check

# Update Hextra to its latest release and refresh go.mod/go.sum.
update:
	$(HUGO) mod get -u github.com/imfing/hextra
	$(HUGO) mod tidy

# CI pins Hugo $(HUGO_VERSION); warn when the local binary differs.
version:
	@$(HUGO) version
	@printf 'expected: %s (HUGO_VERSION)\n' "$(HUGO_VERSION)"
	@$(HUGO) version | grep -q "v$(HUGO_VERSION)" \
		|| echo "WARNING: local Hugo does not match $(HUGO_VERSION); CI builds with $(HUGO_VERSION)."

clean:
	rm -rf public resources $(CHECK_DIR)
