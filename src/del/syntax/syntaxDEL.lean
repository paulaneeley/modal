/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.languageDEL data.set.basic

variables {agents : Type}


---------------------- Proof System ----------------------


-- Define a context
@[reducible] def ctx (agents: Type) : Type := set (form agents)
instance : has_emptyc (ctx agents) := by apply_instance
notation Γ `∪` φ := set.insert φ Γ


-- Proof system for epistemic logic
inductive prfS5 : ctx agents → form agents → Prop 
| ax {Γ} {φ} (h : φ ∈ Γ) : prfS5 Γ φ
| pl1 {Γ} {φ ψ}          : prfS5 Γ (form.impl φ (form.impl ψ φ))
| pl2 {Γ} {φ ψ χ}        : prfS5 Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {Γ} {φ ψ}          : prfS5 Γ (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {Γ} {φ ψ}          : prfS5 Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {Γ} {φ ψ}          : prfS5 Γ ((φ & ψ) ⊃ φ)
| pl6 {Γ} {φ ψ}          : prfS5 Γ ((φ & ψ) ⊃ ψ)
| pl7 {Γ} {φ ψ}          : prfS5 Γ (((¬φ) ⊃ (¬ψ)) ⊃ (ψ ⊃ φ))
| kdist {Γ} {φ ψ} {a}    : prfS5 Γ ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| truth {Γ} {φ} {a}      : prfS5 Γ ((K a φ) ⊃ φ)
| posintro {Γ} {φ} {a}   : prfS5 Γ ((K a φ) ⊃ (K a (K a φ)))
| negintro {Γ} {φ} {a}   : prfS5 Γ ((¬(K a φ)) ⊃ (K a ¬(K a φ)))
| mp {Γ} {φ ψ} 
  (hpq: prfS5 Γ (φ ⊃ ψ)) 
  (hp : prfS5 Γ φ)       : prfS5 Γ ψ
| nec {Γ} {φ} {a}
  (hp: prfS5 Γ φ)        : prfS5 Γ (K a φ)


-- Define a context
@[reducible] def ctxPA (agents: Type) : Type := set (formPA agents)
--instance : has_emptyc (ctxPA agents) := by apply_instance
notation Γ `∪` φ := set.insert φ Γ

-- Proof system for public announcement logic
inductive prfPA : ctxPA agents → formPA agents → Prop 
| ax {Γ} {φ} (h : φ ∈ Γ) : prfPA Γ φ
| pl1 {Γ} {φ ψ}          : prfPA Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfPA Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {Γ} {φ ψ}          : prfPA Γ (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {Γ} {φ ψ}          : prfPA Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {Γ} {φ ψ}          : prfPA Γ ((φ & ψ) ⊃ φ)
| pl6 {Γ} {φ ψ}          : prfPA Γ ((φ & ψ) ⊃ ψ)
| pl7 {Γ} {φ ψ}          : prfPA Γ (((¬φ) ⊃ (¬ψ)) ⊃ (ψ ⊃ φ))
| kdist {Γ} {φ ψ} {a}    : prfPA Γ ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| truth {Γ} {φ} {a}      : prfPA Γ ((K a φ) ⊃ φ)
| posintro {Γ} {φ} {a}   : prfPA Γ ((K a φ) ⊃ (K a (K a φ)))
| negintro {Γ} {φ} {a}   : prfPA Γ ((¬(K a φ)) ⊃ (K a ¬(K a φ)))
| mp {Γ} {φ ψ} 
  (hpq: prfPA Γ (φ ⊃ ψ)) 
  (hp : prfPA Γ φ)       : prfPA Γ ψ
| nec {Γ} {φ} {a}
  (hp: prfPA Γ φ)        : prfPA Γ (K a φ)
| atomicbot {Γ} {φ}      : prfPA Γ ((U φ ⊥) ↔ (φ ⊃ ⊥))
| atomicperm {Γ} {φ} {n} : prfPA Γ ((U φ (p n)) ↔ (φ ⊃ (p n)))
| announceneg {Γ} {φ ψ}  : prfPA Γ ((U φ (¬ψ)) ↔ (φ ⊃ ¬(U φ ψ)))
| announceconj {Γ} 
  {φ ψ χ}                : prfPA Γ ((U φ (ψ & χ)) ↔ ((U φ ψ) & (U φ χ)))
| announceimp {Γ} 
  {φ ψ χ}                : prfPA Γ ((U φ (ψ ⊃ χ)) ↔ ((U φ ψ) ⊃ (U φ χ)))
| announceknow {Γ} 
  {φ ψ} {a}              : prfPA Γ ((U φ (K a ψ)) ↔ (φ ⊃ (K a (U φ ψ))))
| announcecomp {Γ} 
  {φ ψ χ}                : prfPA Γ ((U φ (U ψ χ)) ↔ (U (φ & (U φ ψ)) χ))


lemma to_prfPA {Γ : ctx agents} {φ : form agents} : prfS5 Γ φ → prfPA (to_PA '' Γ) (to_PA φ) :=
begin
intro h1,
induction h1,
rename h1_h h,
apply prfPA.ax,
use h1_φ,
split,
exact h,
refl,
exact prfPA.pl1,
exact prfPA.pl2,
exact prfPA.pl3,
exact prfPA.pl4,
exact prfPA.pl5,
exact prfPA.pl6,
exact prfPA.pl7,
exact prfPA.kdist,
exact prfPA.truth,
exact prfPA.posintro,
exact prfPA.negintro,
exact prfPA.mp h1_ih_hpq h1_ih_hp,
exact prfPA.nec h1_ih,
end

