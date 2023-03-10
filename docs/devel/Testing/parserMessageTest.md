# JUnit Test Suite for Parser Messages

The aim of this test suite is to ensure a that the messages provided to the user
by KeY in case of errors in JML source files contains certain relevant
information. It is implemented by the class:
`de.uka.ilkd.key.parser.messages.ParserMessageTest`

The parameterized JUnit test suite `ParserMessageTest` works in the following way:

1. Create a test case for each subfolder of folder: `key/key.core.test/resources/testcase/parserMessageTest`
Each subfolder will be treated as the root of a Java classpath.
It is assumed that each subfolder contains a single Java file, which contains
a syntax or semantic error.

2. Run each of the test cases, which consist of the following steps:

  1. Instruct the parser to load the Java file contained in the given source
     directory.
  2. Catch the parser exception, that is thrown while parsing the file. In case
no exception is thrown, the test case fails.

  3. Check if the retrieved parser message has the correct format. The desired
format is provided by the first three lines of the given source file. Those
lines have the following syntax (they must be provided in correct order, as it
is defined here):

     - regular expression that must match the given parser message:
     
         `//MSG *regexp*`
         
     - line, in which the error occurs

         `//LINE *number*`
         
     - column, in which the error occurs
     
         `//COL *number*`

