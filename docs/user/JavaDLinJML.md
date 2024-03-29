# Embedding JavaDL expressions and functions into JML expressions

*Mattias Ulbrich, 2011-08-31*
              
Currently, JML is the standard specification for KeY (JML&starf; more
precisely). Though it is still possible to specify JavaDL-contracts in `.key`
files, the formalism with model fields, ghost state etc. is really centered on
JML.

The KeY implementation is a bit inert when it comes to extending the JML syntax.
However, often we want to quickly assess a new axiomatisation and want to use it
in the code directly.

An extension of the parser provides us with this possibility now.

## Escaping JavaDL function symbol names

In all JML specifications (also in set statements), function symbols known in
JavaDL can be used in JML if the name is prefixed with `\dl_`.

For instance, consider
```
   \functions {
      int foo(int);
      int bar;
   }
```

we can now refer to the term foo(5) from within JML using `\dl_foo(5)`. The term
`bar` must, however, for technical reasons be succeeded by (), i.e., `\dl_bar()`
This works for predicate symbols, too.

If the first argument of the symbol is of type Heap and the number of actual
parameters is smaller than number of formal parameters, the program variable
"heap" (the current heap) is implicitly added as first parameter. Example:

In KeY:
```
\functions { Seq arr2seq(Heap, Object) }
```

In JML (e.g.):
```
//@ ensures arr2seq(arrayObject) == \emptySeq;
```
equivalent to

```
//@ ensures arr2seq(\dl_heap(), arrayObject) == \emptySeq;
```


## Limitations

* There is no sensible error message if a ill-typed term is used in a
set statement.
* The types supported in JML seems to be hardcoded, and cannot be
easily extended.
* Error messages might mislead and could potentially not point to the
right spot in the sources.
