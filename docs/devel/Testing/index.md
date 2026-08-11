# Testing Infrastructure of KeY

## How to run tests

You can run "all tests" with:

```sh
$ gradle test
```

`test` target executes all tests, except *interactive* tests and tests that are
considered for `testProveRules` and `testRunAllProves`. There is `testFast`,
which only considers test that are reasonable quick to use for a developer
during development. Use

```sh
$ gradle testFast
```

to execute them. We are willing to keep the test time with `testFast` reasonably
fast. The answer how we determine *fast*, *slow* and *interactive* tests is
answered below.

The subproject `:key.core` defines two additional test tasks: `testProveRules`
and `testRunAllProves`. The first one tests whether the stored taclet proofs are
still re-playable, the second try to proof all examples (`key.example`).

## How to create test cases.

Just drop your a Java file with the JUnit annotations in a test folder
(`src/test/java`) and it is considered to run along with the other tests. We
encourage to use [JUnit Version 4](https://junit.org/junit4/). For new
sub-modules you can even switch to [Version
5](https://www.baeldung.com/junit-5-gradle).

Here are some helpful tips for comprehensible unit tests:

1. Declare your test resources early in the method.
1. Use JUnit's `Assume.assumeXXX` and `Assert.assertXXX` to validate in your
   test whether the test resources are missing.
1. Use meaningful messages in the assertions.

## How to get find resources.

In nearly every KeY test, you have to locate proof files or other resources. The
class `FindResources` helps to get a path to the correct `src/test/resources`
and other folders. `FindResources.findFolder(systemProperty, alternatives...)`
works as follows: First, it looks up whether the given `systemProperty` is
defined and points to a valid folder (i.e. this is done in `build.gradle`).
Otherwise `findFolder` tries every given alternative path until it finds an
existing folder. `Null` is returned if no given alternative exists.
`FindResources` already offers methods for common test resources folders
(`src/test/resources`), testcase folder (`src/test/resources/test`), and
*global* resource folders `tacletProofs` and examples directory
`key.ui/examples`.

## Usage of `@Ignore`

Use `@Ignore(<reason>)` to deactivate test cases and only in combination with
a good and meaningful justification. An omitted reason leads to reject of the
merge request.

If you disable failing test cases, you should open a corresponding issue.

## Use test categories to decide when your test should be run.

We use JUnit's category system to mark our test cases. Currently we have
following categories:

* Interactive -- never consider for unit tests, use for sketches or manual test
  classes, e.g. UI tests (excluded at target `test` and `testFast`)
* Slow -- slow test cases, automatically only used by Jenkins, but not on Gitlab
  CI (excluded at target `testFast`)
* Performance -- performance regression tests, only run on demand or on master
  (excluded at target `test` and `testFast`)
  
Just annotate your classes or methods with `@Category` annotation, for example:
```Java
@Category(Slow.class)
public MyUnitTest {
   ...
}
```

When is a test case considered as slow? We try to keep `testFast`of all
subprojects below 5 minutes. Our suggestion: A test case is slow if it consumes
more than 20 seconds. Additionally, you should mark test cases as slow, if they
do not impact the coverage.

You can create new JUnit test categories. See `build.gradle` and
`key.util/../testcategories/Slow.java`.

