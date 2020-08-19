-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL ..syntax.syntaxDEL ..syntax.syntaxlemmasDEL .translationdefs 
.complexitylemmas .translationfunction .translationlemmas tactic.linarith
variables {agents : Type}

open prfPA

---------------------- Completeness by Translation ----------------------




theorem equiv_translation_aux {Γ : ctx agents} : 
  ∀ n : nat, ∀ φ : formPA agents, complexity φ ≤ n → prfPA Γ (φ ↔ (translate φ))
| 0     φ          _ :=
  begin
  have h1 : complexity φ > 0, from comp_gt_zero, linarith,
  end
| (n+1) formPA.bot _ := mp (mp pl4 iden) iden
| (n+1) (p m)      _ := mp (mp pl4 iden) iden
| (n+1) (φ & ψ)    h :=
  begin
  simp at *, 
  have h1 := compmax1 h,
  have h2 := compmax2 h,
  have h3 := equiv_translation_aux n φ h1,
  have h4 := equiv_translation_aux n ψ h2,
  exact iff_iff_and_iff h3 h4
  end
| (n+1) (φ ⊃ ψ)    h :=
  begin
  simp at *, 
  have h1 := compmax1 h,
  have h2 := compmax2 h,
  have h3 := equiv_translation_aux n φ h1,
  have h4 := equiv_translation_aux n ψ h2,
  exact iff_iff_imp_iff h3 h4
  end
| (n+1) (K a φ)    h :=
  begin
  simp at *, 
  have h1 := equiv_translation_aux n φ h,
  exact iff_k_dist h1,
  end
| (n+1) (U φ ψ)    h :=
  begin
  simp at *, 
  have h1 : complexity φ ≤ n, from updatecomp1 h,
  cases ψ with m ψ χ ψ χ a ψ φ ψ, 
  {rw translate, rw translate, rw translate, 
  have h2 := equiv_translation_aux n φ h1,
  have h1 := atomicbot, exact update_iff1 h2 h1},
  {rw translate, rw translate, rw translate,
  have h2 := equiv_translation_aux n φ h1,
  have h1 := atomicperm, exact update_iff1 h2 h1},
  {rw translate, rw translate,
  have h2 := announceconj,
  have h3 := updatecomphelper,
  have h4 := updatecomphelper,
  have h5 := equiv_translation_aux n (U φ ψ) (eq.substr h3 (updatecompand1 h)),
  have h6 := equiv_translation_aux n (U φ χ) (eq.substr h4 (updatecompand2 h)),
  exact update_iff2 h5 h6 h2},
  {have h2 : prfPA Γ ((U φ (ψ ⊃ χ)) ↔ ((U φ ψ) ⊃ (U φ χ))), from announceimp,
  simp at *,
  have h3 := updatecomphelper,
  have h4 := updatecomphelper,
  have h5 := equiv_translation_aux n (U φ ψ) (eq.substr h3 (updatecompimp1 h)),
  have h6 := equiv_translation_aux n (U φ χ) (eq.substr h4 (updatecompimp2 h)),
  
  sorry},
  {rw translate, rw translate, rw translate, 
  have h2 := equiv_translation_aux n φ h1,
  have h3 := announceknow,
  simp at *,
  have h4 := equiv_translation_aux n (φ ⊃ K a (U φ ψ)) (updatecompknow h),
  exact update_iff3 h2 h3 h4}, 
  {rw translate, sorry} 
  end


theorem equiv_translation (Γ : ctx agents) : ∀ φ : formPA agents, prfPA Γ (φ ↔ (translate φ)) :=
begin
intro φ,
have h : complexity φ ≤ complexity φ + 1, linarith,
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