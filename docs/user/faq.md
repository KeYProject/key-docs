# FAQ

## I get parsing errors that have nothing to do with the Java file I tried to load in KeY.
### Explanation:
When loading a Java source file, KeY searches for all .java files **in the same folder and all subdirectories** and tries to load them also.
### Solution:
It is nearly always a good idea to create a separate directory for each "verification project". This directory should contain Java source and contracts you want to prove plus all dependencies (see next question below).

## I get an error "Could not resolve TypeReference '...'" and "Consider using a classpath if this is a classtype that cannot be resolved". How can I solve this?
### Explanation:
In the Java code you are trying to load, you used a classtype that is unknown to KeY. There are two possible reasons for this:
1) You refer to some **user-defined class** in the code you are trying to load with KeY, and did not include this user-defined class.
2) You refer to a JDK **library class** in your code. In this case, it may be confusing that some classes or methods from the JDK are known (e.g., `java.lang.System`), while others are not (e.g., `java.lang.Byte`).

In KeY, a limited set of classes is loaded by default for each proof of a Java method contract. This includes for example java.lang.Object (since it is the root of Java's class hierarchy), java.lang.String, and some of the exception classes (Throwable, Exception, RuntimeException, ...). See https://git.key-project.org/key-public/key/-/tree/stable/key/key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux for a full list of Java classes loaded by default in the current stable version of KeY. If you are using the single executable JAR file, you can also find the classes in `de/uka/ilkd/key/java/JavaRedux` inside the JAR.

However, even for those classes loaded by default, while some methods come also with predefined contracts, usually **only stubs** of **some** methods are shipped with KeY. This means in practice that even if your proof obligation is loadable, it is most likely not provable without further ado if the code calls some library method(s).

### Solution:

#### Case 1 (user-defined classes)
Just put the user-defined classes in the same directory (or some subdirectory of it).

#### Case 2 (library classes)
##### Adding library classes
If you want to **add library classes** (possibly also equipped with method contracts), the following steps are necessary:
  1. Create a directory where you put library classes (for this example, we assume the directory name to be "classpath").
  2. Put the library classes into it (as a best practice, add subdirectories as usual for packages in Java). For example, we add the following shortened version of `java.lang.Byte`:
        ```java
        package java.lang;

        public final class Byte {
            //@ public ghost byte value;

            /*@ normal_behavior
              @  ensures \result == (int) value;
              @  assignable \strictly_nothing;
              @*/
            public int intValue();

            /*@ normal_behavior
              @  ensures \result.value == b;
              @  ensures \fresh(\result);
              @  assignable \nothing;
              @*/
            public static Byte valueOf(byte b);
        }
        ```
      As you can see, it is not necessary (but possible) to provide implementations for the methods, which deviates a little bit from the "real" Java syntax.
  3. Create a .key file, e.g. "tutorial.key", which contains the following:
        ```
        \classpath "classpath";
        \javaSource "src";

        \chooseContract
        ```
  4. Load the .key file with KeY. Because of the "\chooseContract" directive, KeY opens the contract selection dialog, where you can select your proof obligation as usual. Note that the contracts from files in classpath are not available here (if you want to have them available for proving, add the files to src directory instead).

The resulting directory structure for this example is:
- someDir
  - classpath
    - java
      - lang
        - Byte.java
  - src
    - A.java *(contains the contract(s) we want to prove, and also references Byte.java)*
  - tutorial.key

##### Replacing/adapting library classes
If you want to **replace** some of the library classes shipped with KeY:
  1. Create a directory (called "bcp" in this example).
  2. Unless you know what you are doing, copy the stubs shipped with KeY to the new directory (see the link above, but make sure that it matches the KeY version you are using!).
  3. Replace/adapt the classes by adding new methods, contracts, invariants, ... In our example, we want to add the constant ONE to the BigInteger stub.
        ```java
        package java.math;

        public final class BigInteger extends java.lang.Number implements java.lang.Comparable {
            //@ public final ghost \bigint value;

            //@ public static invariant java.math.BigInteger.ZERO.value == (\bigint) 0;
            public static final java.math.BigInteger ZERO = BigInteger.valueOf(0);

            //@ public static invariant java.math.BigInteger.ONE.value == (\bigint) 1;       // added for this example
            public static final java.math.BigInteger ONE = BigInteger.valueOf(1);            // added for this example

            // ... (leave the rest of the class as is, unless you know what you are doing!)
        }
        ```
  4. Create a .key file, e.g. "tutorial.key", which contains the following:
        ```
        \bootclasspath "bcp";
        \javaSource "src";

        \chooseContract
        ```
  5. Load the .key file with KeY. As in the case described above, KeY opens the contract selection dialog, where you can select your proof obligation. Contracts from bootclasspath are added as axioms, i.e., no proof obligation is created for them.

The resulting directory structure for thid example is:
- someDir
  - bootclasspath
    - java
      - io
        - ...
      - lang
        - Object.java
        - ...
      - math
        - BigInteger.java
      - ...
  - src
    - A.java *(contains the contract(s) we want to prove, and also uses java.math.BigInteger.ONE)*
  - tutorial.key
