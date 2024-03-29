# Testing of KeY 

## Usage of RunAllProofs JUnit implementation

*May 2015 Kai Wallisch*

RunAllProofs is a test routine in KeY verifying that a set of .key
files can be opened and proven by the KeY prover without user
interaction. Proofs created during a test are reloaded after saving
them to the file system to test the save/load mechanism.  Also,
RunAllProofs verifies that another set of .key files (containing
invalid statements) can *not* be proven automatically.

The previous version of RunAllProofs was realized as a Perl
script. This has now been replaced by a Java JUnit
implementation. Main benefits of the new implementation are:

 - Can be significantly faster, depending on fork mode settings (see
   subitem "Fork Modes" for more information).
 - Creates possibility for uncovering memory leaks by investigating
   RunAllProofs statistics because intended usage scenario is now to
   execute all tests in a single process (see "Fork Modes" and
   "Statistics" sections below).
 - Better/easier Jenkins integration provided by JUnit.

## RunAllProofs Invocations

The following possibilities are currently available to start a
RunAllProofs test run:

 - Execute shell script `key/scripts/runAllProofs`

 - Execute ant task "runAllProofs" in component key.core.test, for
   instance from root of KeY git repository the following should work:
   
   ```
   ant -buildfile key/key.core.test/build.xml runAllProofs
   ```

 - Execute ant task "test-deploy" in component key.core.test. This
   task is mainly intended for a Jenkins test run. It can be manually
   invoked with:
   ```
        ant -buildfile key/key.core.test/build.xml test-deploy
   ```

The recommended tool for a user to execute RunAllProofs locally is by
executing the shell script `key/scripts/runAllProofs`. Invocation of this
script without any arguments starts a RunAllProofs test run with
standard settings. Check output of `key/scripts/runAllProofs --help`
to see available command line parameters.

Executing ant task `runAllProofs` should do the same as the command
line script.  It is recommended over ant task `test-deploy` for local
test runs.

### Syntax of the Proof Collection/Index File

!!! danger

    This section does not reflect recent KeY developments. In particular, this list is now defined in code.

There is an proof collection (or index) file containing the
declaration the sets of .key files that will be tested during
RunAllProofs test run. This file is currently located in KeY
git-repository at: `key/key.ui/examples/index/automaticJAVADL.txt`.

A small antlr parser was written for this file. Corresponding antlr
grammar is located at: `key/key.core.test/src/de/uka/ilkd/key/proof/runallproofs/proofcollection/ProofCollection.g`.

The proof collection file is composed of the following components:

- Comments
- Settings declarations
- Declarations of test groups

The different components are explained below. It is recommended to look up
`automaticJAVADL.txt` as an example.

#### Comments
------------

The following comment styles are supported:

```
# Single-line shell-style comment

// Single-line C-style comment

/*
 * Multi-line C-style comment
 */
```

#### Settings Declarations

Proof collections settings entries are key-value pairs, which must occur before
the first test group declaration. The following syntax is used for settings
declarations:

```
  key = value
```

A key is an arbitrary identifier composed of letters and digits starting with
a letter. Value can be either of the following:

- an identifier starting with a letter, followed by a combination of
letters and digits
- a number
- a quoted string (a string literal)
- an unquoted path string

Examples:

```
baseDirectory = ../
statisticsFile = ../../key.core.test/testresults/runallproofs/runStatistics.csv
forkMode = perGroup
reloadEnabled = true
userName = "Foo Bar"
tempDir = ../../key.core.test/runallproofs_tmp
multiLine = "String literals
             may contain line breaks!"
```

The following settings are currently supported:

- baseDirectory: Specifies a base directory of the proof lookup. All paths
                 (except base directory path itself) in proof collection file
                 are resolved relative to baseDirectory. The base directory
                 itself can be specified by a relative path as well. It is then
                 resolved relative to location of proof collection file
                 automaticJAVADL.txt. If not specified, parent folder of proof
                 collection file is chosen.

- statisticsFile: If specified, statistics of a run of RunAllProofs run will be
                  written to the given file. If not specified, code for writing
                  statistics is skipped. See subitem "Test Statistics" for more
                  information.

- forkMode: Specifies fork mode that will be used for a test run. See
            subitem "Fork Modes" for explanation of different fork
            modes. If not specified, this setting will default to
            "noFork".

- reloadEnabled: Boolean value (specify "true" or "false"), which specifies
                 whether every successful proof attempt will be followed by
                 a reloading of that proof. The loading mechanism in KeY tends
                 to be unstable - these test cases help detecting weak spots
                 here. Default value is true. Test files that are not expected
                 to be provable will never be reloaded, even if their
                 corresponding proof obligations ends up in a closed proof.

- keySettings: String literal for the default KeY settings, that will be loaded
               before each proof attempt. Defaults to the empty string.

- tempDir: Temporary directory that is used by RunAllProofs for inter process
           communication when running in forked mode.

- forkTimeout: If the fork mode is not set to noFork, the launched subprocesses
               are terminated as soon as the timeout specified here has
               elapsed. No timeout occurs if not specified. Value is in
               seconds.
 
- forkMemory: If the fork mode is not set to noFork, the launched subprocesses
              get the specified amount of heap memory. The value is passed
              directly to the Java process using -Xmx (like 500m or 2G).

!!! note 
    The available options are also listed in automaticJAVADL.txt.
    You should look there, too.

Proof collection settings can be specified in the following ways:

- at the beginning (before the first test group declaration) of proof collection
index file automaticJAVADL.txt

- inside of a test group in `automaticJAVADL.txt`. These settings are then LOCAL
to that particular group.

- as system properties - all system properties starting with
`key.runallproofs.` are assumed to be settings assignments for
RunAllProofs and can be set via JVM arguments in the following
way: `java [...] -Dkey.runallproofs.forkMode=perFile -Dkey.runallproofs.reloadEnabled=false [...]`

If a settings key is assigned mutltiple times at different places, the
declaration with the highest priority takes precedence for that key. Priorities
are determined according to the following order:

- Highest: Declarations via system property `-Dkey.runallproofs.*`
- 2nd-highest: Declarations inside the current test group.
- 2nd-lowest: Declarations in proof collection file outside of a group.
- lowest: Default values. (can be overridden by all other levels)

Proof collection parser is forgiving in the sense that unknown settings are
parsed without an error (unless they are syntactically incorrect) but will not
influence a test run. Caution: Typos in settings may thus escape the developer's
notice!

#### Declarations of test groups

Test groups can be declared in two different ways in a proof collection file.
Either explicitly grouped or ungrouped. Test Files that are grouped together
will be executed in the same subprocess when fork mode "perGroup" is activated.
Each individual file gets its own subprocess in fork mode "perFile" (regardless
of groups). The files are declared by a path name (which is treated relative to
base directory) preceded by a test property to be verified.

All settings declarations must precede test group declarations. However, groups
can have custom settings declarations, overriding the gloval settings. These
settings must precede .key files (see example below) within the group
declarations.

The following test properties are currently supported:

- `provable`: Test whether the corresponding .key file can be proven by KeY. In
             case proof can be closed successfully and reload is enabled, it
             will be saved and reloaded after prover has finished.

- `notprovable`: Verify that the corresponding .key file can not be proven
                automatically by KeY. Proofs are not reloaded for those files.

- `loadable`: With this option, it is only verified if the corresponding .key
             file can be opened successfully by KeY. Proof attempt is skipped
             with this option.

Example for a group declaration with custom/local settings:

```
  group newBook {
    forkMode = perFile
    reloadEnabled = false
    provable ./newBook/09.list_modelfield/ArrayList.add.key
    provable ./newBook/09.list_modelfield/ArrayList.remFirst.key
    provable ./newBook/09.list_modelfield/ArrayList.empty.key
    provable ./newBook/09.list_modelfield/ArrayList.size.key
    provable ./newBook/09.list_modelfield/ArrayList.get.key
  }
```

`.key` file declarations are also allowed outside of groups, for example:

```
  provable ./standard_key/java_dl/methodCall.key
  notprovable ./standard_key/java_dl/jml-min/min-unprovable1.key
```

which is similar to the following explicit group declarations:

```
  group methodCall.key {
    provable ./standard_key/java_dl/methodCall.key
  }
  group min-unprovable1.key {
    notprovable ./standard_key/java_dl/jml-min/min-unprovable1.key 
  }
```


### Fork Modes

There are different fork mode settings available which influence how often fresh
Java virtual machines (JVM) are launched during RunAllProofs test run. Default
is the value "noFork" which prevents RunAllProofs from launching Java processes
entirely (everything is executed within the VM running the test). However, in
case memory leaks occur and have a significant impact on test performance, it is
recommended to use one of the other available fork mode settings.

The following fork modes are available:

- noFork: RunAllProofs is executed in the current JVM
- perGroup: A new JVM is launched for each group of test files.
- perFile: A new JVM is created for each individual test file (regardless of
groups).

Example: Setting fork mode to "perFile" can be done with the following line in
`automaticJAVADL.txt`:

```
forkMode = perFile
```

### Test Statistics

In case a path is specified via settings key "statisticsFile",
RunAllProofs will save proof statistics to that file. It contains
information about runtime, memory consumption, rule applications and
others.

Example for declaration of a statistics file in `automaticJAVADL.txt`:

```
statisticsFile = ../../key.core.test/testresults/runallproofs/runStatistics.csv
```

###  Proof Reloading

RunAllProofs will attempt to reload proofs that were retrieved during
a successful proof attempt for files that are marked *provable*. Proof reloading
can be disabled via settings key `reloadEnabled` as follows:

```
reloadEnabled = true
```
