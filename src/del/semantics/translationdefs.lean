-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL
variables {agents : Type}


-- Subformulas
def subformulas : formPA agents → set (formPA agents)
  | (formPA.bot) := {⊥}
  | (p n)        := {(p n)}
  | (~ φ)        := {(~φ)} ∪ (subformulas φ)
  | (φ & ψ)      := {(φ & ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (φ ⊃ ψ)      := {(φ ⊃ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (K a φ)      := {(K a φ)} ∪ (subformulas φ)
  | (U φ ψ)      := {(U φ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)


-- Def 7.21, pg. 187, Complexity function c
@[simp] def complexity : formPA agents → ℕ
  | (formPA.bot) := 1
  | (p n)        := 1
  | (φ & ψ)      := 1 + max (complexity φ) (complexity ψ)
  | (φ ⊃ ψ)      := 1 + max (complexity φ) (complexity ψ)
  | (K a φ)      := 1 + (complexity φ)
  | (U φ ψ)      := (4 + (complexity φ)) * (complexity ψ)