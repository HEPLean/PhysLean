/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic 
import PhysLean.Meta.TODO.Basic
/-!

# An example QM problem 

This module contains an example quantum mechanics problem... 


## References 
- abc in ... 

## Implementation note 

This file only contains informal results. 


-/

TODO "29-08-29JTS1" "Include lemmas reltaed to this quantum mechanic problem in particular lemmas 5.2 - 5.3 of ..." 


/-- 
The Hamilatonian of this problem corresponds to H = .... 
-/
informal_def TestQM.Hamiltoian where 
  deps := [``OneDimensional.HilbertSpace, ... ] 
  tag := "29-08-29JTS2"

/-- 
Statement: The hamiltonian of the TEst QM problem is hermitian 
Proof : 
  The follows from triviailty. 
-/
informal_lemma hamiltonian_hermitian where 
  deps := [``TestQM.Hamiltoian] 
  tag := "29-08-29JTS3"


