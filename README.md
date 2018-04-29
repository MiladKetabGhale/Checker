# Checker
This repository contains the formalisation of a framework for verified checking of election tallying certificates. 

1. How to obtain to executable machine code:
to obtain to the verified machine code, which is the equivalent executable version of the formalised certificate checker, you need to do the following steps:

1.1. Install the CakeML compiler
1.2. Create a Linux environmental variable which directs to the CakeML directory installed on your system
1.3. Clone this repository into your local repository.
1.4. Under the subdirectory compilation (which now exists in your local repository hosing the remote repository), run the comman Holmake

If successful, the process will take about three to four hours before you obtain the executable certificate checker.

2. The repository which you are currently in, is structured as follows:

2.1 UnVerifiedVoteCounter :: This subdirectory contains the unverified Haskell program which we have evaluated on some of the Australian Legislative Assemly election in order to test our certificate checker.

2.2 compilation :: this subdirectory includes the file check_countCompileScript.sml which includes CakeML code for instantiation of the CakeML compiler correctness theorem with the theorems already proved on the particular example of the certificate checker. Upon executation of Holmake command, eventually the compiler will synthesise the certificate checker.

2.3 Certificate_sample.txt :: it describes the AST of a certificate to be parsed.

2.4 CheckerProgScript.sml :: includes the translation of the computational components of the certificate checker, which are defined as functions in HOL, into a semantically equivalent AST inside CakeML. 

2.5 CheckerProofScript.sml :: contains proofs of correspondences between specification of the certificate checker (and each of its components) with the computational counters of the checker (and its computational components). 

2.6 CheckerScript.sml :: includes all of the computational components of the checker, and the checker itself, defined in HOL.

2.7 CheckerSpecScript.sml :: contains the specification of each of the computational definitions given in the CheckScript.sml. The specification of counting rules, their components and the checker is in this file.

2.8 ParserProgScript.sml :: the translation of parser components into equivalent AST inside CakeML is found in this file.

2.9 ParserScript.sml :: the parser for parsing certificate lines is defined here.

2.10 check_countProgScript.sml :: In the file CheckProgScript and ParserProg, we translated all of the functions defined in HOL, into CakeML with semantic-preservation. This file contains the deep embedding of the translated certificate checker through the function loop, parse_line, and check_count. It also includes the specification and proof of correctness of the each of these three functions with repsect to I/O model of CakeML.

The compiler which is run by the Holmake command, specified in the subdirectory compilation, extracts the function check_count as the execuatable certificate checker.   

 
