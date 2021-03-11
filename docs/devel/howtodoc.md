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


<h1>Cinder Theme Specimen</h1>

## Typography

### Typefaces

- Headers: [Inter](https://github.com/rsms/inter)
- Body: [Open Sans](https://www.google.com/fonts/specimen/Open+Sans)
- Code: [Hack](http://sourcefoundry.org/hack/)

### Body Copy

You think water moves fast? You should see ice. <strong>It moves like it has a mind</strong>. Like it knows it killed the world once and got a taste for murder. <em>After the avalanche, it took us a week to climb out</em>. Now, I don't know exactly when we turned on each other, but I know that seven of us survived the slide... and only five made it out.

Now we took an oath, that I'm breaking now. [We said](#) we'd say it was the snow that killed the other two, but it wasn't.  Nature is lethal but it doesn't hold a candle to man.

Like inline code?  Here is a string for you <code>010101010</code>.

### Lead Body Copy

<p class="lead">Vivamus sagittis lacus vel augue laoreet rutrum faucibus dolor auctor. Duis mollis, est non commodo luctus.</p>


### Headings

All HTML headings, `<h1>` through `<h6>`, are available. `.h1` through `.h6` classes are also available, for when you want to match the font styling of a heading but still want your text to be displayed inline.

<h1>h1. Heading</h1>
<h2>h2. Heading</h2>
<h3>h3. Heading</h3>
<h4>h4. Heading</h4>
<h5>h5. Heading</h5>
<h6>h6. Heading</h6>


<h1>h1. Heading <small>Secondary text</small></h1>
<h2>h2. Heading <small>Secondary text</small></h2>
<h3>h3. Heading <small>Secondary text</small></h3>
<h4>h4. Heading <small>Secondary text</small></h4>
<h5>h5. Heading <small>Secondary text</small></h5>
<h6>h6. Heading <small>Secondary text</small></h6>

### Blockquotes

<blockquote>
  <p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
  <footer>Someone famous in <cite title="Source Title">Source Title</cite></footer>
</blockquote>


### Lists

* `mkdocs new [dir-name]` - Create a new project.
* `mkdocs serve` - Start the live-reloading docs server.
* `mkdocs build` - Build the documentation site.
* `mkdocs help` - Print this help message.

### Horizontal Description Lists

<dl class="dl-horizontal">
  <dt>Something</dt>
  <dd>This is something</dd>
  <dt>SomethingElse</dt>
  <dd>This is something else</dd>
</dl>

### Contextual Colors

<p class="text-muted">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
<p class="text-primary">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
<p class="text-success">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
<p class="text-info">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
<p class="text-warning">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>
<p class="text-danger">Lorem ipsum dolor sit amet, consectetur adipiscing elit. Integer posuere erat a ante.</p>

## Code

### Inline Code

This is an example of inline code `#import requests`

<h3>Preformatted Code Blocks <small>with Syntax Highlighting</small></h3>

<pre><code class="python">def request(method, url, **kwargs):
    """Constructs and sends a :class:`Request <Request>`.
    Usage::
      >>> import requests
      >>> req = requests.request('GET', 'https://httpbin.org/get')
      <Response [200]>
    """

    # By using the 'with' statement we are sure the session is closed, thus we
    # avoid leaving sockets open which can trigger a ResourceWarning in some
    # cases, and look like a memory leak in others.
    with sessions.Session() as session:
        return session.request(method=method, url=url, **kwargs)

def get(url, params=None, **kwargs):
    r"""Sends a GET request.
    :param url: URL for the new :class:`Request` object.
    :param params: (optional) Dictionary, list of tuples or bytes to send
        in the body of the :class:`Request`.
    :param \*\*kwargs: Optional arguments that ``request`` takes.
    :return: :class:`Response <Response>` object
    :rtype: requests.Response
    """

    kwargs.setdefault('allow_redirects', True)
    return request('get', url, params=params, **kwargs)
</code></pre>

<div id="language-support"></div>

<small>(Source code sample from the Python <a href="https://github.com/requests/requests">requests library</a>, <a href="https://github.com/requests/requests/blob/master/LICENSE">Apache License, v2.0</a>)</small>


Syntax highlighting support is available for and of the following languages listed on the <a href="https://highlightjs.org/download/">highlightjs website</a>. See the <a href="https://www.mkdocs.org/user-guide/styling-your-docs/">mkdocs "styling your docs"</a> hljs_languages section for info on how to load languages dynamically.

<div class="bs-callout bs-callout-info">
  <h4>Note</h4>
  Include source code formatted in <a href="https://github.github.com/gfm/#fenced-code-blocks" class="alert-link">Github-flavored Markdown fenced code blocks</a> with an <a href="https://github.github.com/gfm/#info-string" class="alert-link">info string</a> that defines the supported programming language to automate syntax highlighting when your site is built.
</div>

## Tables

### Striped Table

<table class="table table-striped">
  <thead>
	  <tr>
	  	<th>#</th>
	  	<th>Head 1</th>
	  	<th>Head 2</th>
	  	<th>Head 3</th>
	  </tr>
	  </thead>
	  <tbody>
	  <tr>
	  	<th scope="row">1</th>
	  	<td>Box 1</td>
	  	<td>Box 2</td>
	  	<td>Box 3</td>
	  </tr>
	    <tr>
	    <th scope="row">2</th>
	  	<td>Box 4</td>
	  	<td>Box 5</td>
	  	<td>Box 6</td>
	  </tr>
	  <tr>
	    <th scope="row">3</th>
	  	<td>Box 7</td>
	  	<td>Box 8</td>
	  	<td>Box 9</td>
	  </tr>
  </tbody>
</table>

### Bordered Table

<table class="table table-bordered">
  <thead>
	  <tr>
	  	<th>#</th>
	  	<th>Head 1</th>
	  	<th>Head 2</th>
	  	<th>Head 3</th>
	  </tr>
	  </thead>
	  <tbody>
	  <tr>
	  	<th scope="row">1</th>
	  	<td>Box 1</td>
	  	<td>Box 2</td>
	  	<td>Box 3</td>
	  </tr>
	    <tr>
	    <th scope="row">2</th>
	  	<td>Box 4</td>
	  	<td>Box 5</td>
	  	<td>Box 6</td>
	  </tr>
	  <tr>
	    <th scope="row">3</th>
	  	<td>Box 7</td>
	  	<td>Box 8</td>
	  	<td>Box 9</td>
	  </tr>
  </tbody>
</table>

## Buttons

### Default Buttons

<a class="btn btn-default" href="#" role="button">Link</a>
<button class="btn btn-default" type="submit">Button</button>
<input class="btn btn-default" type="button" value="Input">
<input class="btn btn-default" type="submit" value="Submit">

### Styled Buttons

<!-- Standard button -->
<button type="button" class="btn btn-default">Default</button>

<!-- Provides extra visual weight and identifies the primary action in a set of buttons -->
<button type="button" class="btn btn-primary">Primary</button>

<!-- Indicates a successful or positive action -->
<button type="button" class="btn btn-success">Success</button>

<!-- Contextual button for informational alert messages -->
<button type="button" class="btn btn-info">Info</button>

<!-- Indicates caution should be taken with this action -->
<button type="button" class="btn btn-warning">Warning</button>

<!-- Indicates a dangerous or potentially negative action -->
<button type="button" class="btn btn-danger">Danger</button>

### Button Sizes

<p>
  <button type="button" class="btn btn-primary btn-lg">Large button</button>
  <button type="button" class="btn btn-default btn-lg">Large button</button>
</p>
<p>
  <button type="button" class="btn btn-primary">Default button</button>
  <button type="button" class="btn btn-default">Default button</button>
</p>
<p>
  <button type="button" class="btn btn-primary btn-sm">Small button</button>
  <button type="button" class="btn btn-default btn-sm">Small button</button>
</p>
<p>
  <button type="button" class="btn btn-primary btn-xs">Extra small button</button>
  <button type="button" class="btn btn-default btn-xs">Extra small button</button>
</p>

### Block Level Buttons

<button type="button" class="btn btn-primary btn-lg btn-block">Block level button</button>
<button type="button" class="btn btn-default btn-lg btn-block">Block level button</button>

## Alerts

<div class="alert alert-primary" role="alert">
  A simple primary alert—check it out!
</div>
<div class="alert alert-secondary" role="alert">
  A simple secondary alert—check it out!
</div>
<div class="alert alert-success" role="alert">
  A simple success alert—check it out!
</div>
<div class="alert alert-danger" role="alert">
  A simple danger alert—check it out!
</div>
<div class="alert alert-warning" role="alert">
  A simple warning alert—check it out!
</div>
<div class="alert alert-info" role="alert">
  A simple info alert—check it out!
</div>
<div class="alert alert-light" role="alert">
  A simple light alert—check it out!
</div>
<div class="alert alert-dark" role="alert">
  A simple dark alert—check it out!
</div>

## Callouts

<div class="bs-callout bs-callout-default">
  <h4>Default Callout</h4>
  This is a default callout.
</div>

<div class="bs-callout bs-callout-primary">
  <h4>Primary Callout</h4>
  This is a primary callout.
</div>

<div class="bs-callout bs-callout-success">
  <h4>Success Callout</h4>
  This is a success callout.
</div>

<div class="bs-callout bs-callout-info">
  <h4>Info Callout</h4>
  This is an info callout.
</div>

<div class="bs-callout bs-callout-warning">
  <h4>Warning Callout</h4>
  This is a warning callout.
</div>

<div class="bs-callout bs-callout-danger">
  <h4>Danger Callout</h4>
  This is a danger callout.
</div>

## Admonitions

The following admonitions are formatted like the callouts above but can be implemented in Markdown when you include the `admonition` Markdown extension in your `mkdocs.yml` file.

Add the following setting to `mkdocs.yml`:

```yaml
markdown_extensions:
  - admonition
```

and then follow the instructions in [the extension documentation](https://python-markdown.github.io/extensions/admonition/) to author admonitions in your documentation.

Cinder currently supports `note`, `warning`, and `danger` admonition types.

!!! note
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.

    <pre><code>
    \# this is a note
    def func(arg) {
      \# notable things are in here!
      return None
    }
    </code></pre>

!!! warning
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.

    <pre><code>
    \# this is a warning
    def func(arg) {
      \# be careful!
      return None
    }
    </code></pre>

!!! danger
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla et euismod
    nulla. Curabitur feugiat, tortor non consequat finibus, justo purus auctor
    massa, nec semper lorem quam in massa.

    <pre><code>
    \# this is dangerous
    def func(arg) {
      \# BOOM!
      return None
    }
    </code></pre>

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
