# KEP-0003: `\refines`


I propose a new operator in JML `<var> \refines <Type>`. The operator `x \refines T` is similar to `x instanceof T` but does not follow the Java type system, instead it is true iff `x` is a valid refinement of `T` iff. the interface of `\typeOf(x)` is a valid refine of type `T`iff all methods of `\typeOf(x)` that overrides a method in `T` follows the liskov’s substitution principle.
  
Motivation. Consider the follow situation with a method that comes from an external source, e.g., the JDK.

```java
class List<T> {
   List<R> map(Function<T,R> m) { ... }
}
```

I want to specify that `map` is side-effect iff the function `m`is side-effect free. Now I would redefine the `Function` interface.

```java
interface SefFunction<A,B> {  /*@ assignable \nothing; */ B apply(A a); }
class List<T> { List<R> map(SefFunction<T,R> m) { ... }}
```

As `List<T>` comes from an external source. I could now specify it with an additional `.jml` file, but this would rather add a new method with `SefFunction`.
  
Solution. The `\refines`-operator would help

```java
class List<T> { 
     /*@ normal_behavior
         requires m \refines SefFunction<T,R>; 
         assignable \nothing;
     also normal_behavior
         requires true; 
         assignable \everything;
     */
	List<R> map(Function<T,R> m) { ... }
}
```
