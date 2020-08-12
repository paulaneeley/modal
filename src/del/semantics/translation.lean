-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL ..syntax.syntaxDEL  ..syntax.syntaxlemmasDEL .translationdefs .translationlemmas
import data.nat.basic --data.set.basic --tactic.linarith
variables {agents : Type}

open prfPA

---------------------- Completeness by Translation ----------------------


-- Def 7.20, pg. 186, Translation function t
@[simp] def translate : formPA agents → formPA agents
  | (formPA.bot)     := ⊥
  | (p n)            := p n
  | (φ & ψ)          := have _, from tr1 φ ψ, have _, from tr2 φ ψ, (translate φ) & (translate ψ)
  | (φ ⊃ ψ)          := have _, from tr1 φ ψ, have _, from tr2 φ ψ, (translate φ) ⊃ (translate ψ)
  | (K a φ)          := K a (translate φ)
  | (U φ formPA.bot) := have _, from tr3 φ,     translate (φ ⊃ ⊥)
  | (U φ (p n))      := have _, from tr3 φ,     translate (φ ⊃ (p n))
  | (U φ (~ψ))       := have _, from tr4 φ ψ,   translate (φ ⊃ ~ (U φ ψ))
  | (U φ (ψ & χ))    := have _, from tr5 φ ψ χ, translate ((U φ ψ) & (U φ χ))
  | (U φ (ψ ⊃ χ))    := have _, from tr5 φ ψ χ, translate ((U φ ψ) ⊃ (U φ χ))
  | (U φ (K a ψ))    := have _, from tr6 φ ψ,   translate (φ ⊃ (K a (U φ ψ)))
  | (U φ (U ψ χ))    := have _, from tr7 φ ψ χ, translate (U (φ & (U φ ψ)) χ)
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf complexity⟩] }


theorem equiv_translation_aux {Γ : ctx agents} : 
  ∀ n : nat, ∀ φ : formPA agents, complexity φ < n → prfPA Γ (φ ↔ (translate φ))
| 0     _          _ := by linarith
| (n+1) formPA.bot _ := mp (mp pl4 iden) iden
| (n+1) (p m)      _ := mp (mp pl4 iden) iden
| (n+1) (φ & ψ)    h :=
  begin
  simp at *, 
  have h1 : complexity φ < n, sorry,
  have h2 : complexity ψ < n, sorry,
  have h3 := equiv_translation_aux n φ h1,
  have h4 := equiv_translation_aux n ψ h2,
  sorry
  end
| (n+1) (φ ⊃ ψ)    h :=
  begin
  simp at *, 
  have h1 : complexity φ < n, sorry,
  have h2 : complexity ψ < n, sorry,
  have h3 := equiv_translation_aux n φ h1,
  have h4 := equiv_translation_aux n ψ h2,
  sorry
  end
| (n+1) (K a φ)    h :=
  begin
  simp at *, 
  have h1 := equiv_translation_aux n φ h,
  sorry
  end
| (n+1) (U φ ψ)    h :=
  begin
  simp at *, 
  have h1 : complexity φ < n, sorry,
  have h2 := equiv_translation_aux n φ h1,

  sorry
  end


theorem equiv_translation (Γ : ctx agents) : ∀ φ : formPA agents, prfPA Γ (φ ↔ (translate φ)) :=
begin
intro φ,
have h : complexity φ < complexity φ + 1, from nat.lt_succ_self _,
simp,
exact equiv_translation_aux (complexity φ + 1) φ h
end















-- theorem equiv_translation_aux {Γ : ctx agents} : 
--   ∀ n : nat, ∀ φ : formPA agents, complexity φ < n → prfPA Γ (φ ↔ (translate φ)) :=
-- begin
-- intros n φ h1,
-- simp, induction n with n ih,
-- linarith,
-- induction φ,
-- sorry, sorry,
-- end