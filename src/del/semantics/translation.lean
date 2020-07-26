-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL ..syntax.syntaxDEL data.set.basic
variables {agents : Type}


---------------------- Completeness by Translation ----------------------

-- Subformulas
def subformulas : formPA agents → set (formPA agents)
  | (⊥)      := {⊥}
  | (p n)    := {(p n)}
  | (~ φ)    := {(~φ)} ∪ (subformulas φ)
  | (φ & ψ)  := {(φ & ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (φ ⊃ ψ)  := {(φ ⊃ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (K a φ)  := {(K a φ)} ∪ (subformulas φ)
  | (U φ ψ)  := {(U φ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (D φ ψ)  := {(D φ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)



--lemma subform_self (ψ : formPA agents) : ψ ∈ subformulas(ψ) := sorry
--lemma subform_and (φ ψ : formPA agents) : ψ ∈ subformulas(φ & ψ) := or.inr (subform_self ψ)

-- Def 7.21, pg. 187, Complexity function c

@[simp] def complexity : formPA agents → ℕ
  | (⊥)       := 1
  | (p n)     := 1
  | (φ & ψ)   := 1 + complexity(φ) + complexity(ψ) --1 + max((complexity φ), (complexity ψ))
  | (φ ⊃ ψ)   := 1 + complexity(φ) + complexity(ψ) --1 + max((complexity φ), (complexity ψ))
  | (K a φ)   := 1 + (complexity φ)
  | (U φ ψ)   := (4 + (complexity φ)) * (complexity ψ)
  | (D φ ψ)   := (4 + (complexity φ)) * (complexity ψ)


-- Lemma 7.22, pg 188
lemma cs_1 : ∀ φ ψ : formPA agents, φ ∈ subformulas(ψ) → complexity(φ) ≤ complexity(ψ) := sorry
lemma cs_2 : ∀ φ : formPA agents, ∀ n : nat, complexity(φ ⊃ p n) < complexity(U φ (p n)) := sorry
lemma cs_3 : ∀ φ ψ : formPA agents, complexity(φ ⊃ ~(U φ ψ)) < complexity(U φ (~ψ)) := sorry
lemma cs_4 : ∀ φ ψ χ : formPA agents, complexity((U φ ψ) & (U φ χ)) < complexity(U φ (ψ & χ)) := sorry
lemma cs_5 : ∀ φ ψ : formPA agents, ∀ a : agents, complexity(φ ⊃ (K a (U φ ψ))) < complexity (U φ (K a ψ)) := sorry
lemma cs_6 : ∀ φ ψ χ : formPA agents, complexity(U (φ & (U φ ψ)) χ) < complexity (U φ (U ψ χ)) := sorry




-- Lemmas I'd like to erase
lemma actual_1 : ∀ φ ψ : formPA agents, complexity φ + (1 + (1 + (1 + (complexity φ + 4) * complexity ψ))) < (complexity φ + 4) * (complexity ψ + 2) := sorry
lemma actual_2 : ∀ φ ψ χ : formPA agents, 1 + ((complexity φ + 4) * complexity ψ + (complexity φ + 4) * complexity χ) < (complexity φ + 4) * (complexity ψ + (complexity χ + 1)) := sorry
lemma actual_3 : ∀ φ ψ : formPA agents, complexity φ + (1 + (1 + (complexity φ + 4) * complexity ψ)) < (complexity φ + 4) * (complexity ψ + 1) := sorry
lemma actual_4 : ∀ φ ψ χ : formPA agents, (complexity φ + (1 + (4 + (complexity φ + 4) * complexity ψ))) * complexity χ < (complexity φ + 4) * ((complexity ψ + 4) * complexity χ) := sorry

-- Def 7.20, pg. 186, Translation function t
@[simp] def translate : formPA agents → formPA agents
  | (⊥)            := ⊥
  | (p n)          := p n
  | (φ & ψ)        := (translate φ) & (translate ψ)
  | (φ ⊃ ψ)        := (translate φ) ⊃ (translate ψ)
  | (K a φ)        := K a (translate φ)
  | (U φ (p n))    := translate (φ ⊃ (p n))
  | (U φ (~ψ))     := have _, from actual_1 φ ψ, translate (φ ⊃ ~ (U φ ψ))
  | (U φ (ψ & χ))  := have _, from actual_2 φ ψ χ, translate ((U φ ψ) & (U φ χ))
  | (U φ (K a ψ))  := have _, from actual_3 φ ψ, translate (φ ⊃ (K a (U φ ψ)))
  | (U φ (U ψ χ))  := have _, from actual_4 φ ψ χ, translate (U (φ & (U φ ψ)) χ)
  | (U _ ⊥)         := sorry
  | (U _ (_⊃p _))   := sorry
  | (U _ (_⊃_&_))   := sorry
  | (U _ (_⊃(_⊃_))) := sorry
  | (U _ (_⊃K _ _)) := sorry
  | (U _ (_⊃U _ _)) := sorry
  | (U _ (_⊃D _ _)) := sorry
  | (U _ (D _ _))   := sorry
  | (D _ _)         := sorry
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf complexity⟩] }




theorem equiv_translation (Γ : ctx agents) : ∀ φ : formPA agents, prfPA Γ (φ ↔ (translate φ)) :=
begin
simp,
intro φ,
induction φ, repeat {sorry},
end
























/-
subform self:
begin
induction ψ,
repeat {rw subformulas}, repeat {rw set.mem_singleton_iff},
exact or.inl (or.inl (set.mem_singleton (ψ_φ & ψ_ψ))),
sorry,
exact or.inl (set.mem_singleton (K ψ_a ψ_φ)),
exact or.inl (or.inl (set.mem_singleton (U ψ_φ ψ_ψ))),
exact or.inl (or.inl (set.mem_singleton (D ψ_φ ψ_ψ))),
end


intros φ ψ h1, induction ψ,
repeat {rw subformulas at h1, rw set.mem_singleton_iff at h1, subst h1},
repeat {rename ψ_φ ψ, rename ψ_ψ χ, rename ψ_ih_φ ih_φ, rename ψ_ih_ψ ih_χ},
sorry,
sorry,
repeat {rename ψ_a a, rename ψ_φ ψ, rename ψ_ih ih}, 
repeat {rw subformulas at h1,
cases h1,
rw set.mem_singleton_iff at h1, subst h1},
specialize ih h1, rw complexity, 
sorry,
repeat {rw subformulas at h1,
cases h1, cases h1,
rw set.mem_singleton_iff at h1, subst h1,
specialize ih_φ h1, rw complexity, sorry,
specialize ih_χ h1, rw complexity, sorry}
-/