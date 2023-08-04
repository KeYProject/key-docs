# key-docs

*Author: Alexander Weigl <weigl@kit.edu>*

## Getting Started to Write

An overview about some markdown (extension) is avaiable in `docs/howtodoc.md` or 
https://keyproject.github.io/key-docs/devel/howtodoc/

Webpages are determined by folder structure under `docs/`. Just create or change
files within this folder. The top-level header is the title of this page in the
menu (fallback the filename).

**Pushes to master branch, triggers rebuilding and publishing.**


## Getting Started to Build (locally)

### Using Docker

Run the container:

```
docker run --rm -it --volume $(pwd):/mnt -p 8000:8000 \
    wadoon/key-test-docker:docs bash -c 'cd /mnt && mkdocs serve -a 0.0.0.0:8000'
```

The docs will be available at http://127.0.0.1:8000. If the above does not work for you, try running the container in host network mode:

```
docker run --rm -it --volume $(pwd):/mnt --network host \
    wadoon/key-test-docker:docs bash -c 'cd /mnt && mkdocs serve'
```

### Using system libraries

Install the necessary libraries locally: 

```
$ pip install --user mkdocs mkdocs-material pymdown-extensions pygments \
                     markdown-blockdiag mkdocs-bibtex markdown-aafigure==v201904.0004 \
                     mkdocs-build-plantuml-plugin 'Pillow<10' 'Markdown<3.4'
```

You can start development web-server, which automatically rerender and refresh
on changes, with

```
$ mkdocs serve
```

HTML is build with 

```
$ mkdocs build
```

into `site/`

