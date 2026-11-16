---
title: "Script Variables"
weight: 30
---

The proof script language supports script variables.
These are variables that are managed by the interpreter and are not part of the explicit proof
object&mdash;in contrast to the variables of the
Java program and the logical variables of first oder logic formulas.

As Java or logic variables, we bind the assignments script variables to a sequences.
If a script variable is not assigned in the current selected goal,
we look up its value in the sequence's ancestors, recursively.

## Types

Each variables has a type. Following *simple* types are defined:

* `int`  -- arbitrary precision integers
* `bool` -- true or false
* `string` --  string (`""`)

For the interoperability with KeY we allow that parameterized term types `TERM<S>`,
where `S` is a KeY sort (already defined by in the KeY namespace).
The type hierarchy is fixed.

* `TERM` -- for an unknown sort
* `TERM<S>` -- with sort `S` (e.g. int, locset)

## Special Variables

During the design of our scripting language we arrived at a point,
in which we need access to configuration options of the underlying
theorem prover. We decided to implement an access to these options via variables.
The variable access has advantages over built-in commands. The main advantage is that
you can do conditions other these options.

Here we give a list of the current special variables

### KeY Options

* `__KEY_DEP : BOOL = true`

  Toggles dependency tracking for the prover.

* `__KEY_MAX_STEPS : INT = 10000`

  Must be positive; limits rule applications in automatic proof search.

* `__KEY_METHOD_OPTION : STRING = "method"`

  Selects the method treatment used by the strategy (`method` by default).

* `__KEY_NON_LINEAR_ARITHMETIC : STRING = "none"`

  Selects the non-linear arithmetic mode.

* `__KEY_QUERY : BOOL = false`

  Enables query mode.

* `__KEY_SMT__ACTIVE_SOLVER : STRING = ""`

  Name of the active SMT solver; empty means no solver.

* `__KEY_SMT__CHECK_FOR_SUPPORT : BOOL = true`

  Check that the selected solver supports the required features.

* `__KEY_SMT__INT_BOUND : INT = 3`

  Bit-length bound for integer translation.

* `__KEY_SMT__INVARIANT_ALL : BOOL = false`

  Translate all invariants rather than only the relevant ones.

* `__KEY_SMT__LOCSET_BOUND : INT = 3`

  Bit-length bound for location-set translation.

* `__KEY_SMT__MAX_CONCURRENT_PROCESSES : INT = 5`

  Maximum number of concurrent SMT solver processes.

* `__KEY_SMT__MAX_GENERIC_SORTS : INT = 2`

  Maximum number of generic sorts in the translation.

* `__KEY_SMT__MAX_INTEGER : INT = 2147483645`

  Largest integer used for bounded integer translation.

* `__KEY_SMT__MIN_INTEGER : INT = -2147483645`

  Smallest integer used for bounded integer translation.

* `__KEY_SMT__MODE_OF_PROGRESS_DIALOG : INT = 0`

  Controls the SMT progress dialog.

* `__KEY_SMT__OBJECT_BOUND : INT = 3`

  Bit-length bound for object translation.

* `__KEY_SMT__PATH_FOR_SMT_TRANSLATION : STRING = ""`

  Directory for stored SMT translations; empty disables storing.

* `__KEY_SMT__SEQ_BOUND : INT = 3`

  Bit-length bound for sequence translation.

* `__KEY_SMT__SHOW_RESULTS_AFTER_EXECUTION : BOOL = false`

  Show SMT solver results after execution.

* `__KEY_SMT__STORE_TRANSLATION_TO_FILE : BOOL = false`

  Write the SMT translation to a file.

* `__KEY_SMT__TIMEOUT : INT = 5000`

  SMT solver timeout in milliseconds.

* `__KEY_SMT__USE_BUILTIN_UNIQUENESS : BOOL = false`

  Use the solver's built-in uniqueness for objects.

* `__KEY_SMT__USE_CONSTANTS_FOR_INTEGERS : BOOL = true`

  Use constants for integers in the translation.

* `__KEY_SMT__USE_UI_MULTIPLICATION : BOOL = true`

  Use uninterpreted multiplication.

* `__KEY_SMT__heapBound : INT = 3`

  Bit-length bound for heap translation.

* `__KEY_SMT__useExplicitTypeHierarchy : BOOL = false`

  Translate the type hierarchy explicitly.

* `__KEY_SMT__useNullInstantiation : BOOL = true`

  Instantiate null predicates in the translation.

* `__KEY_STOP_MODE : STRING = "default"`

  Stop mode used by the strategy.

* `__KEY_TIMEOUT : INT = -1`

  Prover timeout in milliseconds; `-1` disables the timeout.

### Interpreter Options

* `__MAX_ITERATIONS_REPEAT : INT = 10000`

  Sets the the upper limit for iterations in repeat loops. Default value is really high.

* `__STRICT_MODE : BOOL = false`

  Defines if the interpreter is in strict or relax mode.

  In strict mode the interpreter throws an exception in following cases:

  * access to undeclared or unassigned variable
  * application of non-applicable rule

  In non-strict mode these errors are ignored&mdash;a warning is given on the console.
