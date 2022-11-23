# Logging 

*weigl, November 2022*

Logging is an important topic for libraries and application. There are
framework that helps to master it, but it still remains difficult at
some point.

KeY uses the *Simple Logging Facade for Java* (slf4j) to abstract from
a concrete logging framework, like log4j or `java.util.logging` (jul).
slf4j provides an API of loggers, events, etc. but does not provide
any logging implementation. All KeY libraries are built against slf4j,
and only the KeY application (`key.ui`) embedds a logging framework.

[More information on slf4j are available on their homepage.](https://www.slf4j.org/manual.html)

## How to log

As a KeY developer, you should simply use the API of slf4j. Following shows the typical use:

```java linenums="1"
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class MyImportantThing {
  public static final Logger LOGGER = 
         LoggerFactory.getLogger(MyImportantThing.class); //(1)!

  
  public void foo(int x) {
    LOGGER.debug("A debugging message");
    LOGGER.info("Param {}", x);
    LOGGER.warn("A warning");
    LOGGER.error("An exception occured", new Exception());  
  }
}
```

1.  Using the class for logger category allows a filter based on the packages. For example, we can later surpress all logging messages given by the theorem prover core. 



sl4fj distinguish between different log level: trace, debug, info,
warn and error. The use in KeY should be oriented as follows:

* `error`: Logging on errorneous or exceptional state where the
  regular program execution will terminate. `error` should not be used
  on expected, catched, and handled exceptions when the execution of
  the program continues.
  
    `error` should always indicate an unexpected behavior of the
  program.

    Please log exceptions only once! Avoid the following pattern:
```java
try { ... }
catch(Exception e) {
 LOGGER.error("{}", e);
 throw new RuntimeException(e);
} 
```
  By re-throwing an exception the caller handles it. Either you
  re-throw, or you handle/log it.


* `warn` Warn is for everything that might be critical or surprising
  to the user. For example, a different interpretation of JML
  annotations as the reference manual or found errors in the loaded
  Java program code (javac support).


* `info` is for interresting things which might useful for some
  developer. Normally this does not appear at the console. 
  
* `debug` is only for debugging purposes. It is messy.
  

## How to use KeY as a library

If you embedd KeY as a library, e.g., `key.core`, you should supply
a logging framework or otherwise slf4j will give you a warning ons
stderr. The most simple logging framework is `org.slf4j:slf4j-simple`.

## Configuration of `key.ui`

`key.ui` ships logback as the logging framework for the application,
which is also used for logging within the unit tests.

You can configure via an XML file `logback.xml`. More information in
the [logback's
documentation](https://logback.qos.ch/manual/configuration.html). KeY
is configured to log all messages (incl. debug) into the
`$HOME/.key/logs` and all messages above and incl. `warn` at the
console. You can manipulate the log level for the console via `-v`
switch.


