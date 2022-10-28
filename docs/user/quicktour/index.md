# Quicktour 

!!! abstract 

    This article gives an introduction to the KeY system.


## Introduction {#sec:introduction}

When we started writing this document, we aimed at providing a short
tutorial accompanying the reader at their first steps with the
KeY system. The KeY tool is designed as an integrated
environment for creating, analyzing, and verifying software models and
their implementation. The reader shall learn how to install and use
the basic functionality of the KeY tool. Besides practical
advises how to install and get KeY started, we show along
a small project how to use the KeY tool to verify programs.

Verification means proving that a program complies with its
specification in a mathematically rigorous way. In order to fulfill
this task, the specification needs to be given in a formal language
with a precisely defined meaning. In the current version of the
document, we focus on the popular *Java Modeling Language*
(JML) [@JMLReferenceManual11][@Leavens-Baker-Ruby04] as specification
language.

In the next sections, we show how to verify a JML-annotated
(specified) JavaCard program. For this purpose, KeY features
a calculus for the complete JavaCard language including advanced
features like transactions.

Besides JML, the KeY tool supports JavaCardDL as a specification
language.

For a longer discussion on the architecture, design philosophy, and
theoretical underpinnings of the KeY tool  please refer to
[@KeYBook2016]. In case of questions or comments, don't hesitate to
contact the KeYsupport team at
[*support@key-project.org*](mailto:support@key-project.org).

!!! note "Version Information"

    This tutorial was tested for KeY version 2.10.
    
## Contents

1. [Installation](install.md): This chapter explains how to install and run the KeY system.
2. [Loading JML Contracts](loading.md): This chapter explains how to load JML specifications into KeY and gives an introduction to the logical calculus behind KeY. 
3. [ProvingJML Contracts](proving.md): This chapter explains how to apply your knowledge from the previous chapter, showing how KeY generates proof obligations and how to prove them.
4. [Appendix](appendix.md)


## Bibliography

\full_bibliography

