# Automatically formatting code with Spotless

As a step towards a consistent code style in our code base, we automatically formatted our code with [spotless](https://github.com/diffplug/spotless/tree/main/plugin-gradle).

Currently, we apply spotless to files with the following extensions:
* .key
* .java
* .g4 (ANTLR grammars)

## How Spotless works
Basically, for every format/file type defined in the config file, the task `spotlessCheck` applies the defined function(s) to every file of this format and then checks if the result is equal to the original file.
If not, a violation is reported.
Note that due to this nature of the check, spotless is not able to give any detailed information about the rule that is violated.

The task `spotlessCheck` does not change the actual files on disk.
It is also possible via `spotlessApply` to just apply the changes and write them back.

Note that there are separate tasks of the form `spotless<format>Check/Apply` for every defined format, e.g. `spotlessJavaCheck`.

## License headers
Running `spotlessApply` will also add short license headers to the files (or replace existing headers). The header to be used can be found in the repo in the file `gradle/header`.

## Java formatting

Spotless supports several formatters, for Java files we currently use the Eclipse formatter, since it provides the most options of the available formatters and thus allows us to configure the automatic formatting in a way that it conforms to the KeY code style (https://git.key-project.org/key/key/-/wikis/Code%20Conventions).
The configuration is provided as an XML file and can be found in `scripts/tools/checkstyle/keyCodeStyle.xml`.
It is a version of the [Google Java Style](https://github.com/google/styleguide/blob/gh-pages/eclipse-java-google-style.xml) adapted to [our code conventions](https://git.key-project.org/key/key/-/wikis/Code%20Conventions).

### Configuring the formatter options for Java (Eclipse formatter)

** Warning: This will affect the whole code base! Only change if you are sure! **

The config file for the KeY style is located in `key/scripts/tools/checkstyle/keyCodeStyle.xml`. Please do not just load the file into Eclipse, adapt it and export it again, as this will completely reshuffle the entry lines. At the moment, the entries are ordered lexicographically, which makes it much easier to find similar keys and also to compare diffs with git.

Unfortunately, there seems to be no documentation, so you have to look into the source code of [org.eclipse.jdt.core.formatter.DefaultCodeFormatterConstants](https://github.com/eclipse-jdt/eclipse.jdt.core/blob/master/org.eclipse.jdt.core/formatter/org/eclipse/jdt/core/formatter/DefaultCodeFormatterConstants.java) to see the available settings.
Information about possible values (e.g. for line wrapping and indentation) can be found in [org.eclipse.jdt.internal.formatter.DefaultCodeFormatterOptions](https://github.com/eclipse-jdt/eclipse.jdt.core/blob/master/org.eclipse.jdt.core/formatter/org/eclipse/jdt/internal/formatter/DefaultCodeFormatterOptions.java).

Note that at least three completely different versions of the formatter existed: One old and very buggy one before Eclipse Mars 4.5, one attempt of a rewritten version that never made it into a release, and the current one.
Be careful, since the second one supported some additional keys (see https://bugs.eclipse.org/bugs/attachment.cgi?id=209299), and there are some config files around on the internet (in particular the Google style file linked above) that use these features, for example count dependent alignment.
However, they are not supported in any release of Eclipse. Further information can be found in their bug tracker (long discussion!): https://bugs.eclipse.org/bugs/show_bug.cgi?id=303519

### Disabling the automatic formatter for a part of a file
If a part of the code has custom formatting that needs to be retained, the formatter can be temporarily disabled as shown in the example:

```java
// spotless:off
/*
 * Java comment
 * that must not be reformatted.
 */
// spotless:on
```
Between the pair of `spotless:off/spotless:on`, the code will stay exactly as is.

### Limitations of the Eclipse formatter
The formatter is intended to do whitespace changes, so as a general rule, other changes are usually not possible (line wrapping in JavaDoc/multiline comments works though).

* Enforcing braces on single line if/for/... statements is not possible.
* String literals in code are not split/joined.
* Line comments after arguments of method calls frequently exceed the 100 chars line length limit (see ...).
* This is not really a limitation of the formatter, but there may be fragments (for example JavaDoc `@link`s with long signatures, long import statements, long type declarations, ...) that are unbreakable.

While we could write custom formatting steps to solve these problems, this is very much work and probably not worth the effort.

## Gitlab Job
The Gitlab Job `format` checks the formatting for every commit that is pushed to a MR by running the `spotlessCheck` gradle task. Please make sure that your code conforms to the KeY coding style and the task passes without violations.

## Configuring `git blame` to ignore the large formatting commit(s)
To prevent the large commit that just applies the reformatting from cluttering the result of `git blame`, you can do the following (in the main KeY directory):

```bash
# commit with automatic reformatting
echo 5a906f9d58b36bb348118ccaf964afe232d9bec4 > blame-ignore-refs.txt
# commit with manual formatting corrections
echo a80f6fd1937b52d2a893a1db19567e15c67d52b2 >> blame-ignore-refs.txt
git config blame.ignoreRevsFile <absolute/path/to/project/directory>/blame-ignore-refs.txt
```
Note: It is important to set the **absolute path** to the file, using e.g. `./blame-ignore-refs.txt` does not work.
