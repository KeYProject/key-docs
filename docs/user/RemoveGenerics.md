# Applying KeY to programs with generics

## Support

At present, you cannot prove properties about Java programs with
generics in KeY. However, a routine is provided to remove genericity
from Java programs, reducing them to equivalent Java2 programs without
generics. This routine is currently *not* invoked automatically when
source code is loaded, but needs to be run on the sources beforehand.

## Removing Generics from a Program

The removing generics functionality is located in the executable created by

```
./gradlew shadowJar
```

It can be invoked from the key/key.ui/build/libs folder:


```
java -cp key-2.7-exe.jar de.uka.ilkd.key.util.removegenerics.Main
```

If you provide no parameters, a usage information is printed.

If you want to remove generics in the .java-files in directory DIR and
write the results to directory OUT, call:

```
java -cp key-2.7-exe.jar de.uka.ilkd.key.util.removegenerics.Main -d OUT DIR
```

It may be that you need to provide additional classpath information
which can be provided using another `-cp argument` (on the commandline
*behind* the Main classname).

The transformed classes can then be loaded into KeY.

## Technical Details
--------------------

The reason why generics are currently not implemented in KeY lie in the type
system of KeY: There, every Java class is represented by a type of its own. To
talk about "some" type, "type variables" or "type placeholders" would be needed.

Alternatively, the type parameter information could be formalised as predicates
in the logic (`typeof(expr) = java.lang.String`). But this would imply a hybrid
situation with some type information available in the type system and some in
semantic predicates. A reasonable, yet drastic step would be to transfer typing
information to the semantic level entirely.
