# A Computational Interpretation of Compact Closed Categories: Reversible Programming with Negative and Fractional Types

* Chao-Hong Chen (Indiana University)
* Amr Sabry (Indiana University)

## DEPENDENCIES
Agda version 2.6.1

## FILES
The main directory stores several files and directories:
  * `Everything.agda`: Import everything.
  * Section 2:
    * `Pi/Everything`: All theorems for Π
  * Section 3:
    * `RevMachine.agda`: Formalization of reversible machine and partial reversible machine
    * `RevNoRepeat.agda`: Non-repeating lemma for reversible machine
    * `PartialRevNoRepeat.agda`: Non-repeating lemma for partial reversible machine
  * Section 4:
    * `TimeSpace.agda`: Definition and examples for space and time trade-offs
  * Section 5:
    * `Pi-/Everything.agda`: All theorems for Πᵐ
  * Section 6:
    * `PiFrac/Everything.agda`: All theorems for Πᵈ
  * Section 7:
    * `PiQ/Everything.agda`: All theorems for Πℚ
  * Section 8:
    * `PiQ/Examples.agda`: All examples
    * `PiQ/SAT.agda`: SAT solver
    
## Type checking
To type check everything:

    > agda Everything.agda
