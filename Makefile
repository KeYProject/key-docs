prepare:
	pip install --user -r requirements.txt 

serve:
	mkdocs serve --livereload

build:
	mkdocs build
