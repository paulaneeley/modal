import basicmodal.language

---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx : Type := set (form)
notation Γ `un` φ := set.insert φ Γ

-- Proof system, pg. 26
inductive prfK : ctx → form → Prop 
| ax {Γ} {φ} (h : φ ∈ Γ) : prfK Γ φ
| pl1 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {Γ} {φ ψ}          : prfK Γ (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ φ)
| pl6 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ ψ)
| pl8 {Γ} {φ ψ}          : prfK Γ (((¬φ) ⊃ (¬ψ)) ⊃ (ψ ⊃ φ))
| kdist {Γ} {φ ψ}        : prfK Γ ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
| mp {Γ} {φ ψ} 
  (hpq: prfK Γ (φ ⊃ ψ)) 
  (hp : prfK Γ φ)      : prfK Γ ψ
| nec {Γ} {φ} 
  (hp: prfK Γ φ)       : prfK Γ (□ φ)