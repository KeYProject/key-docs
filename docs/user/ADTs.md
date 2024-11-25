author: Alexander Weigl
date: 2023-09-24
title: ADTs
---

# User-defined Abstract Data Types

!!! abstract
    
    KeY supports the definition of abstract data types that can be employed both in logic formulas and in JML specifications. 

## Introduction 

Abstract data types manifest in various forms. Typically, one associates abstract data types with *algebraic* data types characterised by their constructors. For instance, a linear list of elements of type `'a` can be represented in OCaml as follows:

```ocaml
type 'a List = Nil | Cons('a, List)
```

However, abstract data types encompass a broader spectrum of structures, including co-inductive or non-generated data types. For example, let us consider the modelling of a set within KeY. While a finite set may be represented using a list along with a uniqueness constraint on the list elements, such a model would encounter limitations in reflecting infinite sets, such as the set of natural numbers or the set of all conceivable objects. Streams (which can understand as the infinite equivalent of lists) are another example which cannot easily be described as an algebraic type. Such infite data structures are defined co-inductively, resulting in an opaque sort with observer functions on them. 

KeY provides support both for algebraic and co-algebraic data types.

!!! bug
     Below you say that co-adts are not supporte in KeY ... ?!

## Algebraic Data Types (since KeY-2.14.0)

!!! info

    Since version 2.14.0, the KeY grammar supports abstract datatypes with special syntax.
    See below for introducing data types manually in earlier versions of KeY.

The grammar for algebraic data types (ADTs) adheres to the typical "syntax style" employed in KeY and incorporates elements familiar from other theorem provers and functional programming languages. ADTs are defined within a `\datatypes { ... }` block, and give rise to new syntactical elements in the logic and calculus: sorts, function symbols, and taclets. The grammar is as follows:

!!! bug

    Where in the .key file is this expected? Anywhere?

```key
\datatypes {
   <name> = <constructor> | ... | <constructor>;
   ...
 }
```
where `<constructor>` is a function declaration of the form `<cname>(<sort> <argName>, ..., <sort> <argName>)` with 0 or more named arguments.
For instance, the linear list is defined in KeY as  `\datatypes { List = Nil  | Cons(any element, List tail); }`. From this definition, the following logical entities are added to the signature and calculus of KeY:

!!! bug
    According to the description it must read "Nil()". Can () be omitted for 0 arguments? Should be made clear.

!!! bug
    Are there not also destructor function symbols? like "element(list)" and "tail(list)"?
    What about axioms like "tail(Cons(x,y)) = y" ?

1.  A new sort corresponding to the ADT name, in this case, `List`.
2.  A new function symbol for each constructor, with the arguments as specified in  the constructor definition and the ADT sort as the resulting sort. In our example, this translates to `\functions{ List Nil();  List Cons(any, List); }`     
3.  Three taclets to reason about the ADT:

    1.  A rule that introduces the induction principle as an axiom on the sequence.
    2.  Induction taclets for proving a sentence for all ADTs. (Like the induction rule above.) 
    3.  A case distinction taclet, which allows you to split a proof attempt along the possible different values of an ADT. 

Let us look at these taclets in further detail. Consider an ADT $A$ with the definition $A = c_1(\bar x_1) \mid \ldots \mid c_n(\bar x_n)$ that has been introduced. There are $n$ constructors ($c_i$) that each take arguments ($\bar x_i$ referring to variables of the respective sorts).

The base induction axiom is then
\begin{equation}
(\forall \bar x_1. \phi[a/c_1(\bar x_1)]) \wedge \ldots \wedge (\forall \bar x_n. \phi[a/c_n(\bar x_n)] \to (\forall a \in A.~ \phi)
\end{equation}
which, rendered as a KeY taclet, allows the introduction of this formula to the antecedent. This is correct since we assume that ADTs are *generated* by their constructors.

!!! bug
    "Induction taclets for proving a sentence for all ADTs. (Like the induction rule above.)"
    Why is this about all ADTs? It is only about a single type, right?

When represented as a splitting rule, we obtain a variant that retains expressiveness equivalent to the original axiom, provided the cut rule is available:

\[
\begin{aligned}
   % \forall a \in A.\ \phi \Longrightarrow \\
   \Longrightarrow ~& \forall \bar x_1.\ \phi[a/c_1(\bar x_1)]  \\
   \Longrightarrow ~& \ldots      \\
   \Longrightarrow ~& \forall \bar x_n.\ \phi[a/c_n(\bar x_n)]  \\
   \hline
   \qquad \Longrightarrow ~& \forall a \in A.~ \phi[a] \qquad
\end{aligned}
\]

This taclet directly follows from the induction formula.

Furthermore, a case distinction taclet facilitates the differentiation of the different constructor cases without necessitating an induction proof. It splits a proof goal into the different possible constructor cases. Let $e:A$ be an expression without free variables of the ADT sort $A$ introduced above:
  
\[
\begin{aligned}
   \exists x_1.\ e = c_1(\bar x_1) & \Longrightarrow \\
   & \ldots \\
   \exists x_n.\ e = c_n(\bar x_n) & \Longrightarrow \\
   \hline
   & \Longrightarrow
\end{aligned}
\]

This follows directly from the disjunction $x = c_1 \vee\ldots\vee x = c_n$ resulting from the construction principles underlying ADTs. This is valid for *generated* ADTs where the values can only be constructed using the constructors. This allows us to make a case distinction about the various constructors. 



!!! bug

    Not yet looked at.

Following our example, we obtain the following taclets:

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

Co-inductive types are also possible in KeY. For example, the built-in sorts `Heap` and `LocSet` are co-inductive. There is no direct syntactical support for these data types. 


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
