prepare:
	pip install --user  mkdocs  mkdocs-material  pymdown-extensions pygments markdown-blockdiag markdown-aafigure==v201904.0004

serve:
	mkdocs serve

build:
	mkdocs build
