# Testing Infrastructure of KeY

## How to run tests

You can run all tests with:

```
$ gradle test
```

`test` target executes all tests, except *interactive* tests and tests that are considered for `testProveRules` and `testRunAllProves`.
There is `testFast`, that only considers test that are reasonable quick to use them as a developer on your desktop machine.
Use 

```
$ gradle testFast
```

to execute them. We are willing to keep the test time of `testFast` in reasonably slow.
The answer how we determine *fast*, *slow* and *interactive* tests is answered below.

The subproject `:key.core` defines to additional test tasks: `testProveRules` and `testRunAllProves`.
The first one test if the stored taclet proofs are still replayable, the seconds try to proof all examples (`key.example`) 
if they are closeable.

## How to create test cases.

Just drop your a Java file with  JUnit annotation in the test folder (`src/test/java`) 
and it is considered to run with tests. We encourage to use [JUnit Version 4](https://junit.org/junit4/). 

Here are some helpful tips:

1. Declare your test resources early in the method.
1. Use JUnit's `Assume.assumeXXX` and `Assert.assertXXX` to validate if your test whether the test resources are missing. 
1. Use meaningful messages in the assertions. 

## How to get find resources.

In nearly every KeY test, you have find proof files or other resources. You should consider the class `FindResources` 
to get a path to the correct `src/test/resources`.

`FindResources.findFolder(systemProperty, alternatives...)` works as follows: First, it looks up whether the given `systemProperty` is defined and a valid folder by the user (this is done in `build.gradle`). Otherwise it tries every given alternative path until it finds an existing folder. `Null` is returned if no given path exists.
`FindResources` already offers methods for test resources (`src/test/resources`),  testcase folder (`src/test/resources/test) and *global* resource folders
`tacletProofs`, examples dir `key.ui/examples`.

## Usage of `@Ignore`

Use `@Ignore(<reason>)` to deactivate test cases; only in combination with a good and meaningful justification.
An omitted reason leads to reject of the merge request. 

If you disable failing test cases, you should open a corresponding issue.

## Use test categories to decide when your test should be run.

We use JUnit's category system to mark our test cases. Currently we have following categories:

* Interactive -- never consider for unit tests, use for sketches or manual test classes, e.g. UI tests (excluded at target `test` and `testFast`)
* Slow -- slow test cases, automatically only used by Jenkins, but not on Gitlab CI (excluded at target `testFast`)
* Performance -- performance regression tests, only run on demand or on master (excluded at target `test` and `testFast`)

When is a test case considered as slow? We try to keep `testFast`of all subprojects below 5 minutes. 
Our suggestion slow test case consumes more than 10 seconds. Additionally you can mark test cases as slow, 
if they does not increase coverage.

You can create new junit test categories. See `build.gradle` and `key.util/../testcategories/Slow.java`.






