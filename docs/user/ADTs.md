# User-defined abstract data types

Currently (as of KeY 2.4), it is not entirely possible to define new data types
as a user which are available in JML specifications. Even though functions,
predicates, and proof rules are defined in `.key` files, some things need to be
hard-coded.

The type 'Free' is meant as a basis for adding user-defined theories.  It is
used for 'quick and (not completely) dirty' addition of user-defined theories
which can be given in the taclet language. The data type is built-in into KeY
and can be accessed in JML as `\free`.  In JML, functions and predicates can be
accessed through the escape keyword `\dl_` ([details](JavaDLinJML)).

The type always contains at least one unique function 'atom', the neutral
element. Otherwise, you can define your theory around it by adding functions,
predicates, and rules. To conform with KeY's guidelines, please mark your rules
as either axiomatic or lemma. In order to prove lemma rules in KeY, axiomatic
rules need to syntactically appear before others in the file. 

The theory must be defined in file
`key/key.core/resources/de/uka/ilkd/key/proof/rules/freeADT.key`. Example
theories can be found under key/key.ui/examples/theories. Copy one of these
files to this location and run 'ant compile' in `key/key.core`
