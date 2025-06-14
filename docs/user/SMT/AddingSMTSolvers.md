# Adding a new SMT Solver

KeY loads the definition of SMT solvers from JSON files with the KeY dialect. Users can add new solvers by creating a JSON file on various places.

Here given in order of precedence. 

1. The current working directory: `./smt-solvers.json`
2. Path from system property : `-P key.smt_solvers=<path>`
3. The KeY user configuration folder: `~/.key/smt-solvers.json`
4. All resources with the name `de/uka/ilkd/key/smt/solvertypes/solvers.key.json` in the classpath.

All files are loaded but the lowest number adds / overwrites the solvers defined by the higher numbers. Hence, 
local configuration overwrites user configuration overwrites classpath configuration. 

But all settings can be finally overwritten using the proof independent settings or the KeY settings dialog. 

## Configuration file format

Solver properties files allow developers to

- Add support for an SMT solver currently not used by KeY (as long as it accepts SMT-LIB as input). In this case, 
it will likely be necessary to also implement a new subclass of `de.uka.ilkd.key.smt.communication.AbstractSolverSocket` 
to handle the solver output unless an existing solver socket suffices.
- Add a new variant of an SMT solver, for example "Z3, but only with quantifier-free formulas" or "CVC5, but ignoring all formulas with casts".
- Add a new variant of an SMT solver with specific options / a specific preamble (e.g., Z3 with "(set-option :produce-proofs true)").

This can all be done without writing a lot of own code (except for the solver socket).

To add a solver, specify a properties (*.props*) file following the example below or the already existing properties files in the project.
Afterwards, put the properties file in a `*...\resources\de\uka\ilkd\key\smt\solvertypes*` directory in one of the subprojects of KeY. 
For the solver to be usable, add the file's name to a *solvers.txt* which also should be located in the same directory as the .props file.

If you choose to add the properties file to the specific directory *key.core\src\main\resources\de\uka\ilkd\key\smt\solvertypes*, 
it will be included in an automatically (via gradle task) created *solvers.txt* file in that same directory.


```json
// Every JSON contains a single JSON map, where value are an solver type definition, and the key is a unique identifier for the solver.
{
  "SOLVER_KEY": 
    {
      // The solver's name. Should be unique amongst all used solvers, otherwise it is given a unique name throughout the solver loading process.
      "name": "", 

      // Arbitrary information about the specified solver for the human.
      "info": "",

      // The default command used to start the solver process.
      "command": "",

      // The parameters appended to the command when starting the solver program, e.g. "-in" and "-smt2".
      "params": "--params",

      // The version parameter appended to the command while starting the solver program in order to get its version.
      "version": "--version",

      // The minimum supported version of this solver.
      "minVersion": "0.0.0",

      // The delimiters used by the solver program in its stdout messages.
      "delimiters": ["\n", "\r"],


      // The default solver process timeout (in seconds) as a long value.
      "timeout": 60,

      // The fully qualified class name of the SolverSocket class used by the solver at hand.
      "socketClass": "de.uka.ilkd.key.smt.communication.Z3Socket",

      // The fully qualified class name of the SMTTranslator class used by the solver at hand.
      "translatorClass": "de.uka.ilkd.key.smt.ModularSMTLib2Translator",

      // The SMTHandlers used by this solver.
      "handlers": [
        "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler"
        // ...
      ],

      // The handler options (a list of arbitrary Strings) for the SMTHandlers used by the SMTTranslator.
      "handlerOptions": [
        "option1"
        // ...
      ],

      // The path of the preamble file.
      "preamble": "specialPreamble.smt2",

      // If this is true, the solver is only usable in experimental mode.
      "experimental": true
    }
  ]
}
```
* `name` --  The solver's name. Should be unique amongst all used solvers, otherwise it is given a unique name throughout the solver loading process.
If no name is given, the solver will be called "SMT Solver" or a unique version of that (depending on the other solvers' names).

* `info` -- Arbitrary information about the specified solver.

* `command` -- The default cmd command used to start the solver process. Empty String by default, if the property is not specified.
The current command can later be changed by the user in the settings.

* `params` -- The cmd parameters appended to the command when starting the solver program, e.g. "-in" and "-smt2".
If the property is not specified, the params are an empty String by default. They can later be changed by the user in the settings.
```properties
params=--params
```

* `version` -- The version parameter appended to the command while starting the solver program in order to get its version.
If the property is not specified, it is an empty String "". Note that this cannot be changed later by the user.

* `minVersion` -- The minimum supported version of this solver. By default, this is an empty String. 
Note that different versions are compared to this minimum version lexicographically - if that comparison is not possible, you may have to override the SolverTypeImplementation class.

* `delimiters` -- The delimiters used by the solver program in its stdout messages. Default value is the array {"\n", "\r"}.

* `timeout` -- The default solver process timeout (in seconds) as a long value. 
If the property is not set or <= -1, it is -1 by default, meaning that the general SMT timeout is used.
The current timeout can later be changed by the user in the settings.

* `socketClass` -- The fully qualified class name of the SolverSocket class used by the solver at hand.
SolverSockets are responsible for the interpretation of messages sent by the solver process, so you may need to implement a new one if the added solver so requires.
See the *key.core\src\main\java\\de\uka\ilkd\key\smt\communication* package for currently available SolverSockets and adding new ones.
Currently possible values for SOCKET_CLASS

* `translatorClass` -- The fully qualified class name of the SMTTranslator class used by the solver at hand.
Currently possible values for TRANSLATOR_CLASS (see the *key.core\src\main\java\\de\uka\ilkd\key\smt* package):
SmtLib2Translator (legacy solvers), ModularSMTLib2Translator

* `handlers` -- The SMTHandlers used by this solver. 
  If the property is not specified, it is an empty list by default which leads to all handlers being used.
  Note that this property currently only takes effect if the ModularSMTLib2Translator class is used.
  The handlers' names are expected to be fully qualified. Currently possible values of `HANDLER_CLASS` are for example: 
  BooleanConnectiveHandler, CastHandler, CastingFunctionsHandler, DefinedSymbolsHandler, FieldConstantHandler, InstanceOfHandler, ...

* `handlerOptions` -- The handler options (a list of arbitrary Strings) for the SMTHandlers used by the SMTTranslator. 
If the property is not specified, it is an empty list by default leading to default behavior of the SMTHandlers.
All the used handlers handle the options on their own.

* `preamble` -- 		
The path of the preamble file. By default, the *key.core\src\main\resources\de\uka\ilkd\key\smt\newsmt2\preamble.smt2* file is used as a preamble.
If you want to use another, more solver-specific preamble, the file should be put in the same directory as the .props file for the solver.

* `experimental` --
If this is true, the solver is only usable in experimental mode. The property is false by default, if not specified. Generally, it is a good idea to set this to true for solvers that still use the SmtLib2Translator (legacy translation) instead of the ModularSMTLib2Translator.
