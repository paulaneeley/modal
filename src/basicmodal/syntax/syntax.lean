/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import basicmodal.language

---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx : Type := set (form)
notation AX `∪` φ := set.insert φ AX


-- Proof system
inductive prfK : ctx → form → Prop 
| ax {AX} {φ} (h : φ ∈ AX) : prfK AX φ
| pl1 {AX} {φ ψ}           : prfK AX (φ ⊃ (ψ ⊃ φ))
| pl2 {AX} {φ ψ χ}         : prfK AX ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {AX} {φ ψ}           : prfK AX (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {AX} {φ ψ}           : prfK AX (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {AX} {φ ψ}           : prfK AX ((φ & ψ) ⊃ φ)
| pl6 {AX} {φ ψ}           : prfK AX ((φ & ψ) ⊃ ψ)
| pl7 {AX} {φ ψ}           : prfK AX (((¬φ) ⊃ (¬ψ)) ⊃ (ψ ⊃ φ))
| kdist {AX} {φ ψ}         : prfK AX ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
| mp {AX} {φ ψ} 
  (hpq: prfK AX (φ ⊃ ψ)) 
  (hp : prfK AX φ)         : prfK AX ψ
| nec {AX} {φ} 
  (hp: prfK AX φ)          : prfK AX (□ φ)