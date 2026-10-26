# KEP-0003: `\refines`


I propose a new operator in JML `<var> \refines <Type>`. The operator `x \refines T` is similar to `x instanceof T` but does not follow the Java type system, instead it is true iff `x` is a valid refinement of `T` iff. the interface of `\typeOf(x)` is a valid refine of type `T`iff all methods of `\typeOf(x)` that overrides a method in `T` follows the liskov’s substitution principle.
  
**Motivation.** Consider the follow situation with a method that comes from an
external source, e.g., the JDK.

```java
class List<T> {
   List<R> map(Function<T,R> m) { ... }
}
```

I want to specify that `map` is side-effect iff the function `m`is side-effect free. Now I would redefine the `Function` interface.

```java
interface SefFunction<A,B> {  
    /*@ assignable \nothing; */ 
    B apply(A a); 
}

class List<T> { List<R> map(SefFunction<T,R> m) { ... }}
```

As `List<T>` comes from an external source. I could now specify it with an
additional `.jml` file, but this would rather add a new method with
`SefFunction`.
  
**Solution.** The `\refines`-operator would help. 

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

Of course, as `SefFunction` is JML only, we can make it spec-only definition.

```java
/*@ model interface SefFunction<A,B> {
    /*@ assignable \nothing; */ 
    B apply(A a); 
} */
```

**Flexible footprints** We can also extends this approach to reason with dynamic
footprints.


```java
model interface LimitedSideEffectsFunction<A,B> {
    model \locset footprint();
    
    //@ assignable footprint();
    B apply(A a); 
}
```

```java
class List<T> { 
     /*@ normal_behavior
         requires m \refines LimitedSideEffectsFunction<T,R> lsef; 
         assignable lsef.footprint();
     also normal_behavior
         requires true; 
         assignable \everything;
     */
	List<R> map(Function<T,R> m) { ... }
}
```


**Formal definiton.**

`x \refines T` is true iff.

* The type `\typeOf(x)` offers at least the same interface as `T` following the
  liskov'sches subsitution princples.

* More formal: Let `m` be an arbitrary method of `T`, then there exists `m'` in
  `\typeOf(x)` where `m'` is valid structural and semantical override following
  the substituion principle:
  
  - paramter count is identical
  - each parameter type of `m'` is less strict than `m`.
  - the return type `m'` is the same or more specific than of `m`
  - the `m'`'s precondition is less strict ($pre(m) \rightarrow pre(m')$)
  - the `m'`'s postconditon is more strict ($post(m') \rightarrow pos(m)$)
  - the `m'`'s frames is more strict ($assignable(m') \subseteq assignable(m)$)
  

This means, `\refines` is a structural and also semantical comparison, cf.
with `instanceof` which is nominal as the Java type system.
