author: Alexander Weigl
date: 2023-09-24
title: ADTs
---

# User-defined abstract data types

!!! abstract
    
    KeY allows you to define abstract data types and use them inside the logic and JML specifications. 


## Introduction 

Abstract data types comes in many favours. Often we think on ADTs as the typical *algebraic* data type defined by the its constructor, e.g., a simple list is defined by 

```ocaml
type 'a List = Nil | Cons(a, List)
```

in Ocaml. But Abstract Data Types are wider category, it also contains co-inductive or non-generated data types. Let us model a set inside of KeY. Of course, a set can be modelled using a list and an uniqueness constraint on the list elements, but this model would not be able to reflect infinite sets such as natural numbers or all possible objects. Such data types are defined co-inductive, which comes in an opaque sort, and obeserver functions upon them. 

KeY supports both. 

## Algebraic Data Types (before KeY-2.14.0)

You need to split your Algebraic Data Type into a sort and (constructor) functions. For example, a list would be defined as

```key 
\sorts { List; }
\functions{  \unique List Nil; \unique List Cons(any,List); }
```
You can now define lists inside of JavaDL, .e.g, `Cons(1, Cons(2, Nil))` for the list $\langle 1,2 \rangle$. To reason about the list, you normally need to define an induction scheme. In KeY you declare a Taclet: 

```key
\rules {
   \schemaVariables { 
        \schemavar List list; 
        \schemavar formula fml;   
    }
   induction_on_list {
    \varcond( \notFreeIn(list, fml) )

    "Nil Case"            : \add(  ==> {\subst fml; Nil} fml  );
    "Cons(any,List) Case" : 
        \add(  ==> 
            ( \forall List l; {\subst list; l} fml )
            -> ( \forall List tail; \forall any ele; {\subst list; Cons(ele,tail)} fml )
        );

    "Use Case" : \add(  \forall List l; {\subst list; l} fml ==> );
   };
}
```

The Taclet `induction_on_list` corresponds to the rule: 

$$
    \begin{matrix}
    \Gamma \Rightarrow \Delta, \phi(nil) 
    \\
    \Gamma \Rightarrow \Delta,
    (\forall x : List.~\phi(x)) \rightarrow (\forall e : Any.~\forall tail : List.~~\phi(Cons(e,tail))) 
    \\
    \Gamma, \forall x : List.~\phi(x) \Rightarrow \Delta
    \\ \hline
    \Gamma \Rightarrow \Delta, \forall x : List.~\phi(x)
    \end{matrix}
$$

[A complete example can be found in the KeY repo, in `standard_key/adt/list.key`](https://github.com/KeYProject/key/blob/main/key.ui/examples/standard_key/adt/list.key)

## Algebraic Data Types (with KeY-2.14.0 and beyond)

Since version 2.14.0, the KeY grammar supports the direct notation of algebraic data types. The grammar for ADTs follows the typical syntax in KeY combined with functional language. ADTs are defined within a `\datatypes { ... }` block, and are translated onto the existing infrastructure (Sorts, Functions, Taclets). The grammar is as follows:

```key
\datatypes {
   <name> = <constructor> | ... | <constructor>;
   ...
 }
```
where constructor is a function definition `<cname>( <sort> <argName>, ...)` with named arguments. From a datatype definition, we derive the following logical entities for the signature, on the example of a list `\datatypes { List = Nil  | Cons(any element, List tail); }`:

1. a sort named after the ADT name, e.g., here it would be `List`. 
2. a function for each constructor which takes arguments of the constructor and evaluates to the ADT.
   Here, we would have: 
    ```key
    \functions{ List Nil();  List Cons(any,List); }
    ```     
3. Three taclets for the use in reasoning on the ADT structure. 
  1. Axiom taclets that adds the induction principle as an axiom on the sequence. 
$$
\frac{
(\forall a \in ADT.~ \phi) \leftrightarrow  \phi[a/c_1] \wedge \ldots \wedge \phi[a/c_n] 
\Longrightarrow
}{
\forall a \in ADT.~ \phi[a]
}
$$

  2. Induction taclets for proving a sentence for all ADTs. (Like the induction rule above.) 
$$
\frac{
\begin{matrix}
   \forall a \in ADT; \phi \Longrightarrow \\
   \Longrightarrow \phi[a/c_1]  \\
   \Longrightarrow \ldots      \\
   \Longrightarrow phi[a/c_n]
\end{matrix}
}{
\Longrightarrow \forall a \in ADT.~ \phi[a]
}
$$

   This taclet is a direct consequence of the induction formula.

  3. A case distinction taclet, which allows you to split a proof attempt along the possible different values of an ADT. 
  
     This is a direct consequence of the disjunction $x = c_1 \vee\ldots\vee x = c_n$ resulting from the construction principles of ADTs. This is valid for *generated* ADTs where the values can only be constructed using the constructors. This allows us to make a case distinction about the various constructors. 

\[
\frac{
\begin{matrix}
   x = c_1      \Longrightarrow \\
   \ldots    \Longrightarrow    \\
   x = c_n   \Longrightarrow 
\end{matrix}
}{
     x : ADT ~ \text{(anywhere)}
}
\]

Following our example we obtain the following taclets:

```key
List_Axiom {
    \schemaVar \formula phi;
    \schemaVar \variables List x;
    
    \find(\forall x; phi)
    \varcond(\notFreeIn(x, phi))
    \add(
            \forall x; phi
         <->   {\subst x;Nil}phi
             & \forall List tail; \forall any head; ({\subst x;tail}phi -> {\subst x;Cons(head, tail)}phi)
        ==>
      )
    \displayname "Axiom for List"
  }

List_Ind {
       \schemaVar \formula phi;
       
       "Nil": \add(==> {\subst x;Nil}phi);
       "Cons(anyhead,Listtail)":
           \add(
               ==>
                \forall tail; \forall head; ({\subst x;tail}phi -> {\subst x;Cons(head, tail)}phi)
             );
       "Use case of List":
           \add(\forall x; phi ==>)
       \displayname "Induction for List"
}

List_ctor_split {
          \schemaVar \term MyList var;
          \schemaVar \skolemTerm any head;
          \schemaVar \skolemTerm MyList tail;
          
          \find(var)
          \sameUpdateLevel
          "#var = Nil":  \add(var = Nil ==>);
          "#var = Cons": \add(var = Cons(head, tail) ==>)
          \displayname "case distinction of List"
}
```

## Co-inductive Data Types

Co-inductive types are also possible in KeY. For example, the built-in sorts `Heap` and `LocSet` are co-inductive. There is no direct syntactical support for these datatypes. 


## Using a Data Type in JML 

You can use any sort of the logical signature in JML. For this, you need the prefix the sort name with the `\dl_` to access the JavaDL scope. Some sorts are also direct built-in into JML, like `\map`, and are direct reachable. 

A typical pattern is to have a ghost variable, that represents the current state of a class by using logical datatype and uninterpreted functions. 

```java
public class MyMap {
  //@ public ghost \map logical_dt;

  public void put(Object k, Object v) {
    //@ set logical_dt = \dl_map_put(logical_dt, k, v);
    ...    
  }
}
```

Instead of `\map` you can also use `\dl_map` which points to the same sort. 
