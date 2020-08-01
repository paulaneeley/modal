-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL
variables {agents : Type}


---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx (agents: Type) : Type := set (formPA agents)
notation Γ `∪` φ := set.insert φ Γ

-- Proof system, pg. 26
inductive prfPA : ctx agents → formPA agents → Prop 
| ax {Γ} {φ} 
 (h : φ ∈ Γ)             : prfPA Γ φ
| pl1 {Γ} {φ ψ}          : prfPA Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfPA Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {Γ} {φ ψ}          : prfPA Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl4 {Γ} {φ ψ}          : prfPA Γ ((φ & ψ) ⊃ φ)
| pl5 {Γ} {φ ψ}          : prfPA Γ ((φ & ψ) ⊃ ψ)
| pl6 {Γ} {φ}            : prfPA Γ (~~φ ⊃ φ)
| kdist {Γ} {φ ψ} {a}    : prfPA Γ ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| truth {Γ} {φ} {a}      : prfPA Γ ((K a φ) ⊃ φ)
| posintro {Γ} {φ} {a}   : prfPA Γ ((K a φ) ⊃ (K a (K a φ)))
| negintro {Γ} {φ} {a}   : prfPA Γ ((~(K a φ)) ⊃ (K a ~(K a φ)))
| mp {Γ} {φ ψ} 
  (hpq: prfPA Γ (φ ⊃ ψ)) 
  (hp : prfPA Γ φ)       : prfPA Γ ψ
| nec {Γ} {φ} {a}
  (hp: prfPA Γ φ)        : prfPA Γ (K a φ)
| atomicperm {Γ} {φ} 
  {n}                    : prfPA Γ ((U φ (p n)) ↔ (φ ⊃ (p n)))
| announceneg {Γ} {φ ψ}  : prfPA Γ ((U φ (~ψ)) ↔ (φ ⊃ ~(U φ ψ)))
| announceconj {Γ} 
  {φ ψ χ}                : prfPA Γ ((U φ (ψ & χ)) ↔ ((U φ ψ) & (U φ χ)))
| announceknow {Γ} 
  {φ ψ} {a}              : prfPA Γ ((U φ (K a ψ)) ↔ (φ ⊃ (K a (U φ ψ))))
| announcecomp {Γ} 
  {φ ψ χ}                : prfPA Γ ((U φ (U ψ χ)) ↔ (U (φ & (U φ ψ)) χ))