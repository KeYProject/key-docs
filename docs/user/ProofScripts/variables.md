# Variables 

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

  no documentation

* `__KEY_MAX_STEPS : INT = 10000`

  Should be a positive number and is the limit for rule application in automatic proof searchs.
  

* `__KEY_METHOD_OPTION : STRING = "method"`

  no documentation

* `__KEY_NON_LINEAR_ARITHMETIC : STRING = "none"`

  no documentation

* `__KEY_QUERY : BOOL = false`

  no documentation

* `__KEY_SMT__ACTIVE_SOLVER : STRING = ""`

  no documentation

* `__KEY_SMT__CHECK_FOR_SUPPORT : BOOL = true`

  no documentation

* `__KEY_SMT__INT_BOUND : INT = 3`

  no documentation

* `__KEY_SMT__INVARIANT_ALL : BOOL = false`

  no documentation

* `__KEY_SMT__LOCSET_BOUND : INT = 3`

  no documentation

* `__KEY_SMT__MAX_CONCURRENT_PROCESSES : INT = 5`

  no documentation

* `__KEY_SMT__MAX_GENERIC_SORTS : INT = 2`

  no documentation

* `__KEY_SMT__MAX_INTEGER : INT = 2147483645`

  no documentation

* `__KEY_SMT__MIN_INTEGER : INT = -2147483645`

  no documentation

* `__KEY_SMT__MODE_OF_PROGRESS_DIALOG : INT = 0`

  no documentation

* `__KEY_SMT__OBJECT_BOUND : INT = 3`

  no documentation

* `__KEY_SMT__PATH_FOR_SMT_TRANSLATION : STRING = ""`

  no documentation

* `__KEY_SMT__SEQ_BOUND : INT = 3`

  no documentation

* `__KEY_SMT__SHOW_RESULTS_AFTER_EXECUTION : BOOL = false`

  no documentation

* `__KEY_SMT__STORE_TRANSLATION_TO_FILE : BOOL = false`

  no documentation

* `__KEY_SMT__TIMEOUT : INT = 5000`

  no documentation

* `__KEY_SMT__USE_BUILTIN_UNIQUENESS : BOOL = false`

  no documentation

* `__KEY_SMT__USE_CONSTANTS_FOR_INTEGERS : BOOL = true`

  no documentation

* `__KEY_SMT__USE_UI_MULTIPLICATION : BOOL = true`

  no documentation

* `__KEY_SMT__heapBound : INT = 3`

  no documentation

* `__KEY_SMT__useExplicitTypeHierarchy : BOOL = false`

  no documentation

* `__KEY_SMT__useNullInstantiation : BOOL = true`

  no documentation

* `__KEY_STOP_MODE : STRING = "default"`

  no documentation

* `__KEY_TIMEOUT : INT = -1`

  no documentation

### Interpreter Options

* `__MAX_ITERATIONS_REPEAT : INT = 10000`

  Sets the the upper limit for iterations in repeat loops. Default value is really high.

* `__STRICT_MODE : BOOL = false`

  Defines if the interpreter is in strict or relax mode. 
  
  In strict mode the interpreter throws an exception in following cases:
  
  * access to undeclared or unassigned variable
  * application of non-applicable rule
  
  In non-strict mode these errors are ignored&mdash;a warning is given on the console.

