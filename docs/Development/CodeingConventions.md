Java Code Conventions
=====================

Please adhere as far as possible to [Sun's Code
Conventions](http://www.oracle.com/technetwork/java/codeconventions-150003.pdf).
While these conventions are no longer updated, they are a good basis for
writing comprehensible code.

**The code conventions will be enforced using [checkstyle](http://checkstyle.org).**

A checkstyle file for the important rules below is available in the repository under `key/scripts/tools/checkstyle/key_checks.xml`.

The rule identifiers in parentheses refer to rules in this checkstyle file.

Here are adapted excerpts of the most important guidelines:
-----------------------------------------------------------

Code conventions are important to programmers for a number of reasons:

-   80% of the lifetime cost of a piece of software goes to maintenance.
-   Hardly any software is maintained for its whole life by the
    original author.
-   Code conventions improve the readability of the software, allowing
    engineers to understand new code more quickly and thoroughly.
-   If you ship your source code as a product, you need to make sure it
    is as well packaged and clean as any other product you create.

JavaDoc
-------

Use [JavaDoc](http://www.oracle.com/technetwork/articles/java/index-137868.html) to
annotate at least:
* every class,
* every field (even if private),
* and every public method that is not a setter or getter.

When you create a new class, add yourself as the author of the class (using `@author`).
If you make a noteworthy contribution to a class, add yourself as a further author.

> (JavadocMethod), (JavadocType), (JavadocVariable)

Indentation
-----------

Four spaces should be used as the unit of indentation. The exact
construction of the indentation (spaces vs. tabs) is unspecified. Tabs
must be set exactly every 8 spaces (not 4).

> (FileTabCharacter), (Indentation)

### Lines

Avoid lines longer than **100** characters.

(The conventions require that all lines are no longer than 80 characters.
For KeY, we have relaxed this rule.)

Avoid trailing spaces in lines.

> (RegexpSingleline-tr-spaces)

### Compound Statements

Compound statements are statements that contain lists of statements
enclosed in braces "{ statements }". See the following sections for
examples.

-   The enclosed statements should be indented one more level than the
    compound statement.
-   The opening brace should be at the end of the line that begins the
    compound statement; the closing brace should begin a line and be
    indented to the beginning of the compound statement.
-   Braces are used around all statements, even single statements, when
    they are part of a control structure, such as a if-else or
    for statement. This makes it easier to add statements without
    accidentally introducing bugs due to forgetting to add braces.

> (LeftCurly), (RightCurly), (NeedBraces)

### if, if-else, if else-if else Statements

The if-else class of statements should have the following form:

     if (condition) {
         statements;
     }

     if (condition) {
         statements;
     } else {
         statements;
     }

     if (condition) {
         statements;
     } else if (condition) {
         statements;
     } else {
         statements;
     }
      
Note: if statements always use braces {}. Avoid the following
error-prone form:

     if (condition) // AVOID! THIS OMITS THE BRACES {}!
         statement;

### try-catch Statements

A try-catch statement should have the following format:

     try {
         statements;
     } catch (ExceptionClass e) {
         statements;
     }

Naming Conventions
------------------

Naming conventions make programs more understandable by
making them easier to read. They can also give information about the
function of the identifier-for example, whether it's a constant,
package, or class-which can be helpful in understanding the code.

### Packages

Package names are always written in all-lowercase ASCII letters \[...\].

Examples:
* com.sun.eng
* com.apple.quicktime.v2
* edu.cmu.cs.bovik.cheese

> (PackageName)

### Classes / Interfaces / Enums

Class names should be nouns, in mixed case with the first letter of each internal word capitalized. Try to keep your class names simple and descriptive. Use whole words-avoid acronyms and abbreviations (unless the abbreviation is much more widely used than the long form, such as URL or HTML).

Examples
* class Raster
* class ImageSprite

> (TypeName)

### Methods

Methods should be verbs, in mixed case with the first letter lowercase, with the first letter of each internal word capitalized.

Examples:
* run();
* runFast();
* getBackground();

> (MethodName)

### Variables

Except for variables, all instance, class, and class constants are in mixed case with a lowercase first letter. Internal words start with capital letters. Variable names should not start with underscore _ or dollar sign $ characters, even though both are allowed.

Variable names should be short yet meaningful. The choice of a variable name should be mnemonic, that is, designed to indicate to the casual observer the intent of its use. One-character variable names should be avoided except for temporary "throwaway" variables. Common names for temporary variables are i, j, k, m, and n for integers; c, d, and e for characters.
	
Examples:
* int             i;
* char            c;
* float           myWidth;

> (LocalFinalVariableName), (LocalVariableName), (ParameterName)

### Constants

The names of variables declared class constants (`static final`) should be all uppercase with words separated by underscores ("_").

Examples
* static final int MIN_WIDTH = 4;
* static final int MAX_WIDTH = 999;
* static final int GET_THE_CPU = 1;

> (ConstantName)

### No prefixes

Be aware that names are *not* to be prefixed by the type of entity they are.

* Do *not* name a private boolean member field `m_updateFlag`, but just `updateFlag`.
* Do *not* name an interface `IJob` and the implementation `Job`. Rather name them `Job` and `JobImpl` if need be.
* *Exception:* If you work in KeY projects related to eclipse Eclipse, interface names *may* begin with capital I as this
  is common practice for Eclipse projects.

Declarations
------------
* One declaration per line is recommended since it encourages commenting.
* Put declarations only at the beginning of blocks. Don't wait to declare variables until their first use.
  (The one exception to the rule is indexes of `for` loops.)
* In a class declaration keep the following order of declarations:
  1. First the public `static` fields, then the protected and then the private.
  2. Then the public instance (non-static) fields, then the protected and then the private.
  3. Constructors
  4. Methods

> (DeclarationOrder), (MultipleVariableDeclarations)

Statements
----------

* Do not use `a++` or `++a` inside expressions, only as individual statements.
* Avoid long methods with more than 60 lines of code.

> (MethodLength), (NoIncrementInExpr)
