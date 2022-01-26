## Appendix

The KeY tool is continually developed, meaning that parts of this
tutorial may be outdated when you read it. Moreover, the JML semantics
are subject to discussion, and there is no formal semantics
specification for JML. Differences between the JML semantics of other
tools and the (implicitly given) semantics in KeY are therefore
possible. The JML dialect of KeY even extends JML in some points (as
we have seen above for *assignable* clauses in *loop_invariants*).

KeY 2.10 has been tested on Linux, MacOS, and Windows.

### List of Menu Options {#app:menuOptions}

In the following, we describe some menu items available in the main
menu of the KeY prover.

* **File** --  File related actions
* **Load Example** -- Opens a file browser with included example
  files.
* **Load** -- Loads a problem or proof file; selecting a directory
        opens the proof management window with the generated proof
        obligation for the chosen specification language
* **Reload** -- Reloads last file loaded.
* **Edit last opened file** -- If a default external editor is set,
        this action opens the last opened file in the default external
        editor.
* **Save** -- Saves the current selected proof. Note, that if there
        are several proofs loaded (see the upper left pane) only the
        one currently worked on is saved.
* **Save as Proof Bundle** -- Saves the current selected proof as
        a bundle containing not only the proof itself but all source
        file required to reload it.
* **Quicksave** -- Saves the current selected proof to a temporary
  file.
* **Quickload** -- Loads the last quicksaved proof.
* **Proof Management** -- Allows browsing through the available proof
  obligations.
* **Load User-defined Taclets** -- Allows to activate and deactivate
        theories given as taclet collection in a `.key` file.
* **Prove**
     * **User-Defined Taclets** -- Loads user-defined taclets and
       generates the corresponding proof obligation.
     * **KeY's Taclets** -- Creates proof obligations for some selected taclets.
     * **Taclets using the batch mode** 
* **Recent Files** -- List the last few loaded files (if they are
  still present).
* **Exit** -- Quits the KeY prover (be warned: the current proof is
        lost!).

* **View** -- Settings influencing the look of the user interface

    * **Use Pretty Syntax** -- If set, infix notation for functions
      and predicates are used.
    * **Use Unicode Symbols** -- If set, unicode symbols instead of
        ASCII symbols are used for logical symbols.
    * **Use Syntax Highlighting** -- Use syntax highlighting in the
      sequent.
    * **Term labels** -- Toggle the visibility of different kinds of
        term labels. As explained in Sec. [3.3](#sec:prover), these do
        not change the semantics of the sequent but carry additional
        information that helps guide the automatic proof search and/or
        user.
    * **Hide Package Prefixes** -- Print unqualified class names in the
        sequent instead of qualified ones.
    * **Show Tooltips in Sequent View** -- Show a tooltip with additional
        information about the currently selected term.
    * **Show Tooltips in Source View** -- Show a tooltip with additional
        information about the currently selected term.
    * **Font size** -- Changes the font size of the sequent and source
      views.
    * **ToolTip options** -- Configures the tooltip shown when hovering
        over a taclet in the list of applicable taclets.
    * **Visual Node Diff** -- Opens a new window which allows to view the
        difference between two chosen proof nodes.
    * **Select goal** -- Select another goal in the current proof.
    * **Heatmap** -- Configure heatmaps. This feature---turned off by
        default---highlights the most recent changes in the sequent.
    * **Layout** -- Save and load the current UI layout.
    * **Exploration** -- Options pertaining to proof exploration.
       * **Exploration mode** -- Enables proof exploration. This
            allows you to rewrite, add, or remove formulas on the
            sequent.
       * **Hide justification** -- Editing the sequent creates
            a *justification branch*, in which you must show that your
            edit does not compromise the correctness of the proof.
            This option allows you to hide these justification
            branches.

* **Proof* -- Proof specific options

   * **Start** -- Run the proof (semi-)automatically w.r.t. to current
        strategy options.
   * **Undo Last Rule Application** -- Undo one proof step.
   * **Prune proof** -- Undo all proof steps below the currently
     selected node.
   * **Abandon Proof** -- Quits the currently active proof. All other
       loaded problems will stay in the KeY prover.
   * **Search in proof tree** -- Opens a textfield in the proof pane,
       which allows to search for a string in the proof tree.
   * **Search in sequent view** -- Opens a window with a textfield in
       the lower-left corner of the current goal pane, which allows to
       search for a string in the sequent view.
   * **Show used contracts** 
   * **Show Active Taclet Options** -- Shows the taclet options chosen
     for the current proof.
   * **Show All Active Settings** -- Opens a window displaying all
     settings used in the current proof.
   * **Show Proof Statistics** -- Shows some general statistics about
     the proof size and interactive steps.
   * **Show Known Types** -- Lists all types present in the current
     proof environment.
   * **Search for Counterexample** -- Searches for a counterexample to
        the current proof. This requires an SMT solver to be
        installed.
    * **Generate Testcases** -- Generate test cases for open goals in
        the proof. This requires an SMT solver to be installed.

* **Options* -- General options
    * **Show Settings** -- Open a settings dialog to configure KeY's
      appearance.
    * **Show Taclet Options** -- In the following, each taclet option is
        described briefly. The respective default settings are given
        in parenthesis. The meaning of all settings is beyond the
        scope of this quicktour. Please use the default settings
        unless you know what you are doing. Note that this list is not
        complete.

        * JavaCard -- ([off]) There are two values for this option:
            [on] and [off]. Switches all
            taclets axiomatising JavaCard specific features like
            transaction on or off.
        * assertions -- ([on]) There exists are different values for
            this option
            * on -- evaluates assert statements and raises an
                `AssertionException` if the condition evaluates to
                false. This behaviour models the behaviour of the Java
                virtual machine with assertions enabled globally.
            * off -- skips evaluation of assert statement. In
                particular, the arguments of the assert statements are
                not evaluated at all. This behaviour models the
                behaviour of the Java virtual machine with assertions
                disabled globally.
            * safe -- using this option ensures that the shown
                property is valid no matter if assertions are globally
                enabled or disabled. Proofs with this option are
                typically harder.

            Please note: There is no support other than option
            [safe] for enabling or disabling assertions
            package or class wise.

        * initialisation -- ([disableStaticInitialisation]) Specifies
            whether static initialization should be considered.

        * intRules -- ([arithmeticSemanticIgnoringOF]) Here you can
            choose between different semantics for Java integer
            arithmetic (for details
            see [@Schlager02][@SchlagerPhD2007][@KeYBook2007]). Three
            choices are offered:

            * javaSemantics -- (Java semantics): Corresponds exactly to the semantics
                defined in the Java language specification. In
                particular this means, that arithmetical operations may
                cause over-/underflow. This setting provides correctness
                but allows over-/underflows causing unwanted
                side-effects. This corresponds to the `code‘_java‘_math`
                macro in JML.

            * arithmeticSemanticsIgnoringOF -- (Arithmetic semantics ignoring overflow, default):
                Treats the primitive finite Java types as if they had
                the same semantics as mathematical integers with
                infinite range. Thus this setting does not fulfil the
                correctness criteria. This corresponds to the
                `code‘_bigint‘_math` macro in JML.

            * arithmeticSemanticsCheckingOF -- (Arithmetic semantics prohibiting overflow): Same as
                above but the result of arithmetical operations is not
                allowed to exceed the range of the Java type as defined
                in the language specification. This setting not only
                enforces the java semantics but also ascertains that no
                overflow occur. This corresponds to the
                `code‘_safe‘_math` macro in JML.

        * programRules -- ([Java]) Changes between different program
            languages[^7].

        * model field -- The semantics of model fields is given by the `represents`
            clause in the JML specification. The setting of this option
            decides how the represents clauses are handeled. It has two
            possible values [treatAsAxiom] and
            [showSatisfiability]:

            * treatAsAxiom -- Represents clauses are seen as axioms. If this option is
                set the satisfiability of the represents clauses is not
                shwon and therefore it may introduce inconsistent
                specifications, e.g., he following contradictory JML
                clause will not be rejected:\
                `//@ represents modelField == modelField + 1;`

            * showSatisfiability -- For every expansion of the represents clause, the
                satisfiability of the definition has to be shown.
                Cross-definition inconsistencies can still be
                formulated, however:\
                `//@ represents modelField1 == modelField2;`\
                `//@ represents modelField2 == modelField1 + 1;`

        * runtime exception -- There are two possible ways for the KeY prover in
            handling runtime exceptions -- [ban] or
            [allow].

            * ban -- If runtime exceptions are banned, KeY treats the
                occurence of runtime exceptions as irrecoverable program
                failure. Setting this option results in smaller proofs
                and is complete for defensive programmed programs, i.e.
                programs which do not intentionally use corner cases.

            * allow -- If runtime exceptions are allowed, KeY treats
                runtime exceptions as defined in the Java language
                specification, i.e. implicit runtime exceptions[^8] are
                raised and therefore such exceptions have to be
                considered in the proof. Setting this option results in
                larger proofs.

        The current setting of the taclet options can be viewed by
        choosing `Proof ->Show Active Taclet Options`.

    * [**Minimize Interaction**] -- If this option is used and the
        automtaic strategy is used, KeY tries to minimize user
        interaction. That means that for example, if the KeY prover is
        able to find instantiations by itself, the user is not asked
        to provide them.

    * [**Right Click for Macros**] -- 

    * [**One Step Simplification**] -- In the KeY prover one step
        simplification is a mechanism to automatically apply several
        simplifying and normalization rule applications to the
        sequent. For the user these rule applications are aggregated
        into one visible rule application [One Step Simplification] in
        the proof tree. Setting this option often leads to simpler
        sequents and results in finding a proof faster, but the user
        lacks transparency of the proof, because the rule applications
        of the one step simplifier are not shown in very detail
        compared to all other rule applications in the KeY prover.

    *  [**Show SMT Solver Options**]: --   This option allows you to choose one or more external decision
        procedures that can be invoked during proofs and to set options
        for each external solver seperately. There is a native interface
        to [Simplify]. A variety of other provers
        [CVC3], [Yices], and [Z3]
        are directly supported via SMTLIB [@RanTin-SMTLIB]. In addition,
        translations of taclets to the SMTLIB language can be written to
        a text file ([Taclet Translation]) to be loaded by
        any SMT prover. There are further options on the set of taclets
        to translate.

* Interaction Logging -- These options configure the interaction log in
    the left pane, which logs all user interactions on the loaded
    proof.

* Origin Tracking -- These options configure the origin tracking
    feature. By default, a JavaDL term's origin in the JML
    specification is tracked throughout the proof and highlighted in
    the source pane when mousing over the term.

### List of all Strategy Tab Settings {#app:strategy}

* Max. Rule Applications

    You can set the number $N_{aut}$ of automatic rule applications
    using the slider. Even if the automatic strategy can still apply
    rules after $N_{aut}$ applications, automatic proving stops.

* Stop At

    Choose when strategy execution shall stop. Possible values are
    `Default`: strategy stops when no rules are applicable or the
    maximal number of steps is reached and `Unclosable`: strategy
    stops in all situations when `Default` stops but also already when
    the first goal is encountered on which no further rule is
    (automatically) applicable.

* One-Step Simplification

    When this is `Enabled`, some sequences of simplification steps are
    combined into a single proof step, resulting in shorter, but less
    transparent proofs.

* Proof splitting

    Influences usage of rules branching a proof tree. Only rules
    working on formulas not on programs fall under the chosen policy,
    i.e., program rules causing splits are still applied even if
    splitting is switched off. The values are `free` (withour
    restrictions), `Delayed` (allows still splitting but prefers other
    rules) and `Off` (no splitting).

* Loop treatment 

    This setting determines how while-loops are treated. They can be
    left untouched (`None`), handled using stated invariant contracts,
    or repeatedly unrolled (`Expand`). If handled using invariants,
    you can either choose the new `Loop Scope` rule (recommended), or
    the legacy `Transformation`-based rule.

* Block treatment 

    It is possible to specify Java blocks with contracts. This option
    allows to set how KeY treats such contracts.

    * `internal contract` -- If this option is set, Java blocks are
       replaced by their contract. Three properties have to be shown
       in the proof:

        -   the validity of the contract
        -   the precondition if the contract is satisfied
        -   the use case of the contract

    * `external contract` -- If this option is set, Java blocks are
        replaced by their contract. Only the precondition and the use
        case are shown in the current proof; the validity is
        outsourced to its own proof obligation which can be selected
        in the `Proof Obligation Browser`.

    * expand -- If this option is set, Java blocks are expanded and
        block contracts are not used.

* Method treatment -- Methods can also be left untouched (`None`),
    have their method contracts applied (`Contracts`), or be inlined,
    i.e. have the method body expanded in place (`Expand`).

* Merge-point statements --   Merge-point statements are annotations in the source code. When two
    proof branches reach the same merge-point statement, they can be
    merged if this setting is set to `Merge`. If it is set to `Skip`,
    the merge-point statements are ignored; if it is set to `None`, the
    automatic proof search stops when encountering a merge-point
    statement. For more details on merge-point statements, see
    [@Steinhoefel2019].

* Dependency contracts

    For the simplification of heap terms setting this option to `On` the
    information in JML's `accessible` clause is used.

* Query treatment

    A query is a method that is used as a function in the logic and
    stems from the specification. There are three options for query
    treatment in KeY:

    * `On` --   Rewrite a query to a method call such that contracts or inlining
        (dependent on the method treatment setting) can be used.

    * `Restricted` --   Same as [On] but with restrictions:

        -   Priority of expanding queries that occur earlier on a branch
            is higher than for queries introduced more recently. This
            approximates in a breath-first search with respect to query
            expansion.
        -   Reexpansion of identical query terms is suppressed.
        -   A query is not expanded if one of its arguments contains a
            literal greater than a computed limit[^9], or smaller than a
            computed limit. This helps detecting loops in a proof
        -   Queries are expanded after the loop body in the
            `Preserves Invariant` branch of the loop invariant rule
        -   Queries are expanded in the `Base Case` and the conclusio of
            the `Step Case` branch when using Auto Induction

    * `Off` --   The query statements are ignored and the proof has to be done
        without using them.

    In addition the KeY prover offers a setting for the expansion
    of local queries in certain safe cases. Safe cases are:

    -   the return type of the expanded method is known

    -   the object on which the methodcall is invoked is self or a
        parent of self.

    This setting is indepedent of the query treatment setting.

* Arithmetic treatment 

    The KeY prover has several options for the treatment of
    arithmetic expressions:

    * `Basic` -- Using this option, polynomial expressions are
        simplified. In the antecedent Gröbner Bases are computed
        polynomials. Linear inequations are handled using (partial)
        Omega procedures.

    * `DefOps` -- Using the option [DefOps], symbols such as:\ `/`,
        `%`, `jdiv`, `jmod`, ..., `int_RANGE`, `short_MIN`, ...,
        `inInt`, `inByte`, ..., `addJint`, `mulJshort`, ... are
        expanded.

    * `Model Search` --   Setting the *model search* option, the
        KeY prover supports non-linear equations and model search.
        Additionally multiplication of inequations with each other and
        systematic case distinctions (cuts) can be performed. This
        method is guaranteed to find counterexamples for invalid goals
        that only contain polynomial (in)equations. Such counterexamples
        turn up as trivially unprovable goals. It is also able to prove
        many more valid goals involving (in)equations, but will in
        general not terminate on such goals.

* Quantifier treatment

    Sometimes quantifiers within the sequent have to be instantiated.
    This can be either done manually (`None`) or automatically with
    different alternatives:

    * `No Splits` --   Instantiate a quantifier only if this will not cause the proof
        to split.

    * `Unrestricted` --   Instantiates a quantifier even when causing splits. However the
        startegy tries to predict the number of caused open branches and
        will prefer those with no or only few splits.

    * `No Splits with Progs` --   Chooses between the `No Splits` and `Unrestricted` behaviour
        depending on prgrams present in the sequent. If a program is
        still present, the `No splits` behavior is used. Otherwise,
        quantifiers are instantiated without restrictions.

* Class axiom rule 
    
    This setting determines how class axioms and invariants are dealt
    with.

    * `Free` --   Class axioms are expanded freely.
    * `Delayed` --   Class axioms are only expanded after symbolic execution, i.e.,
        when there are no more modalities on the sequent.
    * `Off` --  Class axioms are never expanded automatically.

* Auto induction

    This setting can allow the KeY prover to automatically perform
    inductive proofs for certain formulas.

    * `On` -- Perform inductive proofs for formulas of a certain form.
    * `Restricted` --  Perform inductive proofs for formulas of a certain form, but
        only if the name of the induction variable ends with `Ind` or
        `IND`.
    * `Off` -- Don't perform inductive proofs automatically.

Handy Shortcuts and Buttons {#app:shortcuts}
===========================

In the following an overview of all shortcuts currently used in the
KeY prover is given. Additional, if buttons in the toolbar exist,
their actions are listed here as well.

Action/Command                  | Shortcut     |                        Button in Toolbar
--------------------------------|--------------|-----------------------------------------------------------
Load                            | Ctrl+O     |              ![image](figures/open.png){.toolbar-icon}
Reload                          | Ctrl+R    |          ![image](figures/openMostRecent.png){.toolbar-icon}
Save                            | Ctrl+S   |              ![image](figures/saveFile.png){.toolbar-icon}
Proof Management                | Ctrl+M  |        ![image](figures/proofManagementButton.png){.toolbar-icon}
Exit                            | Ctrl+Q |                                      
Edit last opened file           | -  |                   ![image](figures/editFile.png){.toolbar-icon}
Use pretty syntax               | Ctrl+P      |                                
Font size: smaller              | Ctrl+Up      |                               
Font size: larger               | Ctrl+Down     |                              
Start automatic strategy        | Ctrl+S         |     ![image](figures/autoModeStart.png){.toolbar-icon}
Abandon task                    | Ctrl+W           |                           
Undo last rule application      | Ctrl+Z          |       ![image](figures/goalBack.png){.toolbar-icon}
Search in proof tree            | Ctrl+F                                       
Search in sequent view          | F3                                           
Prune tree below selected node  | -                 |   ![image](figures/pruneProof.png){.toolbar-icon}
SMT Solver                      | -                 |   ![image](figures/SMTButton.png){.toolbar-icon}
Taclet options                  | Ctrl+T           |                           
Toggle one Step Simplifier      | Ctrl+Shift+S     | ![image](figures/oneStepSimplifier.png){.toolbar-icon}

Setting Up Own Projects {#app:configuringProjects}
=======================

If not specified otherwise via a classpath directive, KeY includes
a restricted set of signatures of classes and methods from the default
standard library. The current set of classes can be found
at <https://git.key-project.org/key-public/key/-/tree/stable/key/key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux>.

For documentation on how to set up your own classpath, see
<https://www.key-project.org/docs/Using%20KeY/Classpath/>.

[^1]: Potential warnings can be safely ignored here.

[^2]: The complete semantics is more complex; see
    Sect. [4](#sec:provableProp){reference-type="ref"
    reference="sec:provableProp"} and [@JMLReferenceManual11].

[^3]: In this case we assume that you have installed the
    KeY tool as described in
    Sect. [1.2.2](#install:byteandsourcecode){reference-type="ref"
    reference="install:byteandsourcecode"}.

[^4]: App. [6](#app:menuOptions){reference-type="ref"
    reference="app:menuOptions"} contains a list of all available
    options.

[^5]: For a detailed description of both kinds of contracts,
    see [@Weiss2011].

[^6]: Additional conditions stem from invariants.

[^7]: Ensure that *Java* is selected.

[^8]: With implicit exceptions, we mean exceptions not explicitely
    programmed by the developer using `throw new java.lang.exception`.

[^9]: The computation of this limit is done with sophisticated methods
    for loop detection and would go beyond the scope of this quicktour

