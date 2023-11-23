prepare:
	pip install --user mkdocs mkdocs-material pymdown-extensions pygments markdown-blockdiag mkdocs-bibtex markdown-aafigure==v202104.1011 mkdocs-build-plantuml-plugin Pillow Markdown

serve:
	mkdocs serve

build:
	mkdocs build
