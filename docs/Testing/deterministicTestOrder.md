# Deterministic Order of Test Cases in KeY

In KeY, some test cases rely on a specific execution order. One reason for this may be for example that it is too expensive to always initialize a new ProofEnvironment and therefore the environment is shared between multiple test cases.
To get rid of test cases failing due to wrong order, we implemented a solution to make the execution order of JUnit tests deterministic: A custom JUnit test runner called AutoSuite.

## What does AutoSuite do?
* Automatically scans for tests inside the specified directory.
* Filters specified categories or classes from the tests.
* Sorts the tests to ensure deterministic execution order.
* Runs the tests (via default JUnit mechanism).

## How to define a new test suite that uses AutoSuite as runner?
A new test suite can be defined by setting AutoSuite as runner:
`@RunWith(AutoSuite.class)` In contrast to "normal" JUnit test suites, one does not have to explicitly specify the test classes to include, since the AutoSuite test runner scans the given path (and its subdirectories recursively) and automatically includes all found tests to the suite. The root path has to be defined via `@AutoSuitePath("root/path/of/tests")`.

It is optional to define filters for excluding certain classes or whole test categories from the suite. See the following code as an example of the syntax:

```Java
@RunWith(AutoSuite.class)
@AutoSuitePath("build/classes/java/test")
@AutoSuiteExclude(
    categories = { Interactive.class, Slow.class }
    classes = { MyTest.class, OtherTest.class }
)
public class SomeTests {
}
```

## Where is AutoSuite in use at the moment?
Currently, AutoSuite is used only for tests of core (Tests and FastTests) and symbolic_execution (Tests). As a consequence, the order of other tests, for example in ui, may change between different test runs. To make the order of these tests deterministic, the only thing to do is adding a test suite
with AutoSuite as runner for these projects as well.

## Gradle
To call an AutoSuite from Gradle, just define a task with a filter that only includes only the desired test suite.
```Groovy
testName {
task testXYZ(type: Test) {
    group "verification"
    filter {
        includeTestsMatching "de.uka.ilkd.key.XYZTests"
    }
    ...
}
```

## Debugging
Debug output of AutoSuite can be enabled by setting the system property `key.test.autosuite.debug` to true:
```
$ gradle test -Dkey.test.autosuite.debug=true -i
```
The option `-i` is used here to get output of tests on command line.

