---
history: 
  - Appelhagen
  - Pfeifer
  - Weigl (2025)
date: 2025-12-01
---

# Adding a new SMT Solver

With [pull request 3597](https://github.com/keyproject/key/pull/3597), we switched to a JSON-based configuration format. The previously format was `properties`-based.

KeY allows you to add SMT (configuration) using a JSON-like files. This interface enables you to 
- add support for an SMT solver, with of SMT-LIB as input. 
- add a new variant of an SMT solver, for example *Z3, but only with quantifier-free formulas* or *CVC5, but ignoring all formulas with casts*.
- add a new variant of an SMT solver with specific options or a specific preamble (e.g., Z3 with `(set-option :produce-proofs true)`).

This can all be done without writing a lot of own code (except for the solver socket).


!!! note
    If the SMT solver drops out of the traditional communication scheme (SMT-LIB on stdin and stdou), an integration requires an implementation via the interface of [`AbstractSolverSocket`](https://javadoc.io/doc/org.key-project/key.core/latest/de/uka/ilkd/key/smt/communication/AbstractSolverSocket.html). 

To add a solver, you specify its properties in a JSON file, following the [schema](smt-solvers.schema.json). The SMT solver definitions are loaded from various places (in order of loading):

1. All resources in the classpath under the name `de/uka/ilkd/key/smt/solvertypes/smt-solvers.json`.
3. The KeY user configuration folder: `~/.key/smt-solvers.json`
2. Path given by a system property : `-P key.smt_solvers=<path>`
1. The current working directory: `./smt-solvers.json`

Each file can add or substitute previous entry with the same name. Removal is currently not possible, but the substituation with an empty definition. 

Use (4) to define SMT solvers for single project, more complex projects or scripting should rather use (3), and (2) is for user-specific but project-wide installation. 

## The schema

!!! info 
    A JSON schema file is available here: [smt-solvers.schema.json](smt-solvers.schema.json).

* `string name = "Z3"`
  
    The solver's name. 

    Should be unique amongst all used solvers, otherwise it is given a unique name throughout the solver loading process.

    If no name is given, the solver will be called "SMT Solver" or a unique version of that (depending on the other solvers' names).

* `string info;` 

    Arbitrary information about the specified solver.

* `string command`

    The default cmd command used to start the solver process. Empty String by default, if the property is not specified.

    The current command can later be changed by the user in the settings.

* `string params`
    The cmd parameters appended to the command when starting the solver program, e.g. "-in" and "-smt2".
    If the property is not specified, the params are an empty String by default. They can later be changed by the user in the settings.

* `string version = "";` 

    The version parameter appended to the command while starting the solver program in order to get its version.

    If the property is not specified, it is an empty String. Note that this cannot be changed later by the user.
  
* `string minVersion = "";`

    The minimum supported version of this solver. By default, this is an empty String. 

    Note that different versions are compared to this minimum version lexicographically - if that comparison is not possible, you may have to override the `SolverTypeImplementation` class.

* `array[string] delimiters = ['\n','\r'];`

    The delimiters used by the solver program in its stdout messages. Default value is the array `["\n", "\r"]`.

* `int timeout = -1;`

    The default solver process timeout (in seconds) as a integer value. 

    If the property is not set or non-positive, no timeout is forced. 

    The current timeout can later be changed by the user in the settings.

* `string socketClass="de.uka.ilkd.key.smt.communication.Z3Socket";`

    The fully qualified class name of the SolverSocket class used by the solver at hand.
    SolverSockets are responsible for the interpretation of messages sent by the solver process, so you may need to implement a new one if the added solver so requires.
    See the *key.core\src\main\java\\de\uka\ilkd\key\smt\communication* package for currently available SolverSockets and adding new ones.
    Currently possible values for SOCKET_CLASS

* `string translatorClass = "de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator";`

    The fully qualified class name of the SMTTranslator class used by the solver at hand.
    Currently possible values are subclasses of [SMTTranslator](https://javadoc.io/doc/org.key-project/key.core/latest/de/uka/ilkd/key/smt/SMTTranslator.html).

* `array[string] handlers = [];`

    The SMTHandlers used by this solver. 

    If the property is not specified, it is an empty list by default which leads to all handlers being used.

    Note, that this property currently only takes effect if the `ModularSMTLib2Translator` class is used.
    The handlers' names are expected to be fully qualified. Currently possible values of can be found in the [javadoc as subclasses of `SMTHandler`](https://javadoc.io/doc/org.key-project/key.core/latest/de/uka/ilkd/key/smt/newsmt2/SMTHandler.html).

* `array[string] handlerOptions = [];`

    The handler options (a list of arbitrary strings) for the `SMTHandlers` used by the `SMTTranslator`. 

    If the property is not specified, it is an empty list by default leading to default behavior of the SMTHandlers.

    All the used handlers handle the options on their own.

    ??? warn 
        weigl: Completely unclear how to find such handlers. Or define new ones


* `string preamble = "key.core\src\main\resources\de\uka\ilkd\key\smt\newsmt2\preamble.smt2"`

    A string describing a resource. Traditional, the preamble is loaded from the   classpath, by default, resource is used `de/uka/ilkd/key/smt/newsmt2/preamble.smt2`. 

    If the string starts with either `file:` or `http:` (e.g., `file://mypreamble.smt2` or `http://example.com/preamble.smt2`), the resource is loaded from the file system or URL instead. 
