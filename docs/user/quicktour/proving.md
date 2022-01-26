## Proving JML Contracts {#sec:application}

Now we apply the described proof obligations to the tutorial example.
First we demonstrate the generation of proof obligations, then we show
how these can be handled by the KeY prover. Please make sure that
the default settings of the KeY prover are selected (see Chapter 
[3.3](#sec:prover){reference-type="ref" reference="sec:prover"}) and the
maximum number of automatic rule applications is 5000. Be aware that the
names of the proof rules and the structure of the proof obligations may
be subject to change in the future.

### Method Specifications

#### Normal Behavior Specification Case.

In the left part of the Proof Obligation Browser, expand the directory
`paycard`. Select the class `PayCard` and then the method `isValid`.
This method is specified by the JML annotation

       public normal_behavior
         requires true;
         ensures result == (unsuccessfulOperations<=3); 
         assignable \nothing;

This JML method specification treats the `normal‘_behavior` case, i.e.,
a method satisfying the precondition (JML boolean expression following
the `requires` keyword) *must not* terminate abruptly throwing an
exception. Further each method satisfying the precondition must

-   terminate (missing diverges clause),

-   satisfy the postcondition -- the JML boolean expression after the
    `ensures` keyword, and

-   only change the locations expressed in the `assignable` clause;
    here: must not change any location. The assignable clause is
    actually redundant in this concrete example, as the method is
    already marked as `pure` which implies `assignable \nothing`.

Within KeY, you can now prove that the implementation satisfies
the different aspects of the specification, i.e., that if the
precondition is satisfied then the method actually terminates normally
and satisfies the postconditon and that the assignable clause is
respected. In addition it is also proven that the object invariants of
the object on which the method call is invoked are preserved.

The contracts pane in the Proof Management window offers only one proof
obligation: `JML normal_behavior opertaion contract`. It summarizes all
parts of the specification which will be considered in the proof.

The selected contract says that a call to this method, if the object
invariant holds ([**pre**] `self.<inv>`), always terminates
normally and that the `return` value is true iff the parameter
`unsuccessfulOperations` is $\leq 3$, Additionally, the object invariant
holds after the method call, therefore it is preserved. The sequent
displayed in the large prover window after loading the proof obligation
exactly reflects this property. We confirm the selection by pressing the
*Start proof* button.

Start the proof by pushing the *Start*-button (the one with the green
"play" symbol). The proof is closed automatically by the strategies. It
might be necessary that you have to push the button more than once if
there are more rule applications needed than you have specified with the
"Max. Rule Applications" slider.

#### Exceptional Behavior Specification Case.

An example of an `exceptional_behavior` specification case can be found
in the JML specification of `PayCard::charge(int amount)`. The
exceptional case reads

      public exceptional_behavior
          requires amount <= 0;

This JML specification is for the exceptional case. In contrast to the
`normal_behavior` case, the precondition here states under which
circumstances the method is expected to terminate abruptly by throwing
an exception.

Use the Proof Management (either by clicking onto the button
![image](figures/proofManagementButton.png){height="2ex"} or
[**File**] $|$ [**Proof Management**]).
Continue as before, but this time, select the method
`PayCard::charge(int amount)`. In contrast to the previous example, the
contracts pane offers you three contracts: two for the normal behavior
case and one for the exceptional case. As we want to prove the contract
for the exceptional case select the contract named: *JML
exceptional_behavior operation contract*.

The KeY proof obligation for this specification requires that if
the parameter `amount` is negative or equal to $0$, then the method
throw a `IllegalArgumentException`.

Start the proof again by pushing the *run strategy*-button. The proof is
closed automatically by the strategies.

#### Generic Behavior Specification Case.

The method specification for method `PayCard::createJuniorCard()` is:

       ensures \result.limit==100;

This is a lightweight specification, for which KeY provides a
proof obligation that requires the method to terminate (maybe abruptly)
and to ensure that, if it terminates normally, the `limit` attribute of
the result equals $100$ in the post-state. By selecting the method and
choosing the *JML operation contract* in the Contract Configurator, an
appropriate JavaDL formula is loaded in the prover. The proof can be
closed automatically by the automatic strategy.

### Type Specifications

The instance invariant of type `PayCard` is

        public invariant log.\inv 
                         && balance >= 0 && limit > 0 
                         && unsuccessfulOperations >= 0 && log != null;

The invariant specifies that the `balance` of a paycard must be
non-negative, that it must be possible to charge it with some money
(`limit > 0`) and that the number of `unsuccessfulOperations` cannot be
negative. Furthermore, the invariant states that the log file, which
keeps track of the transactions, must always exist (`log != null`) and
that the instance referred to by `log` has to satisfy the instance
invariant of its own class type (`log.\inv`).

The method `PayCard::charge()` must preserve this invariant unless it
does not terminate. This proof obligation is covered by proving that
`self.<inv>` must be satisfied in the precondition and must hold in the
postcondition. This has to be covered by all specification cases and is
included in the specification in the Contract Configurator (`self.<inv>`
in the pre- and in the postcondition).

There is one exception: if a method is annotated with the keyword
`helper`, the proof obligation will not include the invariants. An
example for such a method is `LogRecord::setRecord()`. If a method is
declared as helper method, the invariant of the object on which the
method is called does not have to hold for its pre- and postcondition.
For more details, see [@Weiss2011]. The advantage is a simpler proof
obligation; however, the disadvantage is that in order to show that the
method fulfills its contract, it is not possible to rely on the
invariants.

In addition, invariants can also be annotated with an `accessible`
clause. In this clause, all fields and locations on which the invariant
depends have to be included. For example, the invariant of class
`LogRecord` is

     !empty ==> (balance >= 0 && transactionId >= 0);

and it is annotated with the accessible clause

     accessible \inv: this.empty, this.balance, 
     transactionCounter, this.transactionId;

This means the invariant of `LogRecord` depends at most on the fields or
locations given in the `accessible` clause. If one of these fields is
changed by a method, it has to be proven that the invariant still holds.
The accessible clause can simplify proofs because in cases where the
heap is changed but not the mentioned fields and the validity of the
invariant is proven before, we know that the invariant still holds.

### Proof-Supporting JML Annotations

In KeY, JML annotations are not only used to generate proof
obligations but also support proof search. An example are loop
invariants. In our scenario, there is a class `LogFile`, which keeps
track of a number of recent transactions by storing the balances at the
end of the transactions. Consider the constructor `LogFile()` of that
class. To prove the `normal_behavior` specification proof obligation of
the method, one needs to reason about the incorporated `while` loop.
Basically, there are two ways do this in KeY: use induction or use
loop invariants. In general, both methods require interaction with the
user during proof construction. For loop invariants, however, *no
interaction* is needed if the JML `loop_invariant` annotation is used.
In the example, the JML loop invariant indicates that the array
`logArray` contains newly created entries (`fresh(logArray[x])`) and
that these entries are not `null` in the array from the beginning up to
position `i`:

```java
/*@ loop_invariant
  @ 0 <= i && i <= logArray.length &&
  @ (\forall int x; 0 <= x && x < i; logArray[x] != null && \fresh(logArray[x]))
  @ && LogRecord.transactionCounter >= 0;
  @ assignable logArray[*], LogRecord.transactionCounter;
  @ decreases logArray.length - i; 
  @*/	   
while(i<logArray.length){ 
  logArray[i++] = new LogRecord();
}
```

If the annotation had been skipped, we would have been asked during the
proof to enter an invariant or an induction hypothesis. With the
annotation no further interaction is required to resolve the loop.

Select the contract *JML normal behavior operation contract*
`LogFile::LogFile()`.

Choose *Loop treatment* *None* and start the prover. When no further
rules can be applied automatically, select the while loop including
the leading updates, press the mouse button, select the rule
*loopInvariant* and then *Apply Rule*. This rule makes use of the
invariants and assignables specified in the source code. Restart the
strategies and run them until all goals are closed.

As can be seen, KeY makes use of an extension to JML, which is that
*assignable* clauses can be attached to loop bodies, in order to
indicate the locations that can at most be changed by the body. Doing
this makes formalizing the loop invariant considerably simpler as the
specifier needs not to add information to the invariant specifying all
those program variables and fields that are not changed by the loop.
Of course one has to check that the given assignable clause is
correct, this is done by the invariant rule. We refer
to [@KeYBook2016] for further discussion and pointers on this topic.

