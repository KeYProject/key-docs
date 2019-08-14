# How to write documentation

This webpage uses [mkdocs](https://mkdocs.org). Mkdocs generates from a bunch of
markdown files, and a specified template this beautiful web page.

As an author, you can just edit and create new markdown files in the `docs/` of
the corresponding repository: https://git.key-project.org/key/key-docs. On each
commit the generation is automatically started and pushed to this URL.
Therefore, *you do not need to install mkdocs on your computer.* 

The project layout is very simple: There is a configuration file `mkdocs.yml`
which controls the plugins and settings for the generation. And also a content
folder `docs/` which contains Markdown files and additionally resources.


### Local setup 

mkdocs is written in Python. Hence, everything you need is installable via the Python package manager (`pip`). 
For a non-root user install use either `make prepare` or execute the following line:

```
	pip install --user  mkdocs  mkdocs-material  pymdown-extensions pygments markdown-blockdiag markdown-aafigure==v201904.0004
```

This install all needed packages for this webpage inside `$HOME/.local` and after installation the mkdocs executable should be under `$HOME/.local/bin/mkdocs`.


serve:
	mkdocs serve

build:
	mkdocs build

## Commands

* `mkdocs new [dir-name]` - Create a new project.
* `mkdocs serve` - Start the live-reloading docs server.
* `mkdocs build` - Build the documentation site.
* `mkdocs help` - Print this help message.


## Classical Markdown

https://markdown.de/

Headers are introduced with `#`. Multiple `#` increases the header level.

Paragraphs are separated by a blank line.

A 2nd paragraph. You can format your text: *Italic*, **bold**, and `monospace`. 

```
*Italic*, **bold**, and `monospace`. 
```

List are either introduced with `*` or `-`. 
```
* this one
* that one
* the other one
```

* this one
* that one
* the other one

or with numbers  (the systems automatically counts):

```
1. first item
1. second item
1. third item
```

1. first item
1. second item
1. third item


You can quote with `>` like in E-Mails.

> Block quotes are
> written like so.
>
> They can span multiple paragraphs,
> if you like.

Dashes -- (2-dash), --- (em-dash) and ... are automatically converted. Unicode
or HTML fragments are also supported

Code is introduce with ```` or `````. 

```
# Let me re-iterate ...
for i in 1 .. 10 { do-something(i) }
```

As you probably guessed, indented 4 spaces. By the way, instead of
indenting the block, you can use delimited blocks, if you like:

```python
import time
# Quick, count to ten!
for i in range(10):
    # (but not *too* quick)
    time.sleep(0.5)
    print i
```

References by `[text](link)`: For example [a website](http://foo.bar) or
a [local doc](local-doc.html).


size  material      color
----  ------------  ------------
9     leather       brown
10    hemp canvas   natural
11    glass         transparent

Table: Shoes, their sizes, and what they're made of

(The above is the caption for the table.) Pandoc also supports
multi-line tables:

```
First Header  | Second Header
------------- | -------------
Content Cell  | Content Cell
Content Cell  | Content Cell
```

First Header  | Second Header
------------- | -------------
Content Cell  | Content Cell
Content Cell  | Content Cell


**Images** with alternative text and tooltip `![example image](example-image.jpg "An exemplary image")`

![KeYLogo](https://git.key-project.org/uploads/-/system/appearance/logo/1/key-color.png "Kiki is in the middle of the KeY Logo")


## Markdown Extensions:

You should consult the following site for more examples:

* [Admontion](https://squidfunk.github.io/mkdocs-material/extensions/admonition/)
* [CodeHilite](https://squidfunk.github.io/mkdocs-material/extensions/codehilite/)
* [Footnotes](https://squidfunk.github.io/mkdocs-material/extensions/footnotes/)
* [PyMDown](https://squidfunk.github.io/mkdocs-material/extensions/pymdown/)

If you do not find a construct you could also look at: [PyDown
extenstions](https://facelessuser.github.io/pymdown-extensions/#extensions)
directly. Extension are activated in the `mkdocs.yml`.

Here is a short excerpt:


### [Admontion](https://squidfunk.github.io/mkdocs-material/extensions/admonition/)


!!! note
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.


!!! note "Phasellus posuere in sem ut cursus"
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.
    
    
??? note "Phasellus posuere in sem ut cursus"
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.
    

There are a lots of other types and keywords!

### Code Highlighting

    ``` python
    import tensorflow as tf
    ```
    
becomes

``` python
import tensorflow as tf
```

``` bash tab="Bash"
#!/bin/bash

echo "Hello world!"
```

``` c tab="C"
#include <stdio.h>

int main(void) {
  printf("Hello world!\n");
}
```

``` c++ tab="C++"
#include <iostream>

int main() {
  std::cout << "Hello world!" << std::endl;
  return 0;
}
```

``` c# tab="C#"
using System;

class Program {
  static void Main(string[] args) {
    Console.WriteLine("Hello world!");
  }
}
```


### Footnotes

```
Lorem ipsum[^1] dolor sit amet, consectetur adipiscing elit.[^2]
```

Lorem ipsum[^1] dolor sit amet, consectetur adipiscing elit.[^2]

[^1]: Lorem ipsum dolor sit amet, consectetur adipiscing elit.
[^2]:
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.
    
    
### Math

Example:

```
\[
\frac{n!}{k!(n-k)!} = \binom{n}{k}
\]
```

\[
\frac{n!}{k!(n-k)!} = \binom{n}{k}
\]

`Lorem ipsum dolor sit amet: $p(x|y) = \frac{p(y|x)p(x)}{p(y)}$`

Lorem ipsum dolor sit amet: $p(x|y) = \frac{p(y|x)p(x)}{p(y)}$


## Ascii figures

**Currently not enabled due to a bug.**

You can use [asciiflow](http://asciiflow.com/) to draw ascii diagrams easily.

```aafigure
      +-----+   ^
      |     |   |
  --->+     +---o--->
      |     |   |
      +-----+   V
```


```aafigure {"foreground": "#ff0000"}
      +-----+   ^
      |     |   |
  --->+     +---o--->
      |     |   |
      +-----+   V
```


```aafigure
    +---------+         +---------+     +---------+
    |  Shape  |         |  Line   |     |  Point  |
    +---------+         +---------+   2 +---------+
    | draw    +<--------+ start   +----O+ x       |
    | move    +<-+      | end     |     | y       |
    +---------+   \     +---------+     +---------+
                   \
                    \   +---------+
                     +--+ Circle  |
                        +---------+
                        | center  |
                        | radius  |
                        +---------+
```

## Block diagrams

```
blockdiag {
    A -> B -> C -> D;
    A -> E -> F -> G;
}
```

blockdiag {
    A -> B -> C -> D;
    A -> E -> F -> G;
}


```
seqdiag {
    // edge label
    A -> B [label = "call"];
    A <- B [label = "return"];
    // diagonal edge
    A -> B [diagonal, label = "diagonal edge"];
    A <- B [diagonal, label = "return diagonal edge"];
    // color of edge
    A -> B [label = "colored label", color = red];
    // failed edge
    A -> B [label = "failed edge", failed];
}
```

seqdiag {
    // edge label
    A -> B [label = "call"];
    A <- B [label = "return"];
    // diagonal edge
    A -> B [diagonal, label = "diagonal edge"];
    A <- B [diagonal, label = "return diagonal edge"];
    // color of edge
    A -> B [label = "colored label", color = red];
    // failed edge
    A -> B [label = "failed edge", failed];
}
