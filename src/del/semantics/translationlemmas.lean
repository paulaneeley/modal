-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..syntax.syntaxDEL ..syntax.syntaxlemmasDEL .translationfunction
variables {agents : Type}

open prfPA

lemma iff_iff_imp_iff {Γ : ctx agents} {φ ψ χ θ : formPA agents} : 
  prfPA Γ (φ ↔ χ) → prfPA Γ (ψ ↔ θ) → prfPA Γ ((φ ⊃ ψ) ↔ (χ ⊃ θ)) :=
begin
intros h1 h2,
exact (mp (mp pl4 (imp_switch (cut1 (cut (mp pl6 h1) likemp) (mp pl5 h2)))) 
  (imp_switch (cut1 (cut (mp pl5 h1) likemp) (mp pl6 h2))))
end


lemma iff_k_dist {Γ : ctx agents} {φ ψ : formPA agents} {a : agents} :
  prfPA Γ (φ ↔ ψ) → prfPA Γ (K a φ ↔ K a ψ) :=
begin
intro h1,
exact (mp (mp pl4 (mp kdist (nec (mp pl5 h1)))) (mp kdist (nec (mp pl6 h1)))),
end


lemma update_iff1 {Γ : ctx agents} {φ ψ χ : formPA agents} : 
  prfPA Γ (φ ↔ χ) → prfPA Γ (U φ ψ ↔ (φ ⊃ ψ)) → prfPA Γ (U φ ψ ↔ (χ ⊃ ψ)) :=
begin
intros h1 h2,
exact (mp (mp pl4 (cut2 (mp pl6 h1) (mp pl5 h2))) (cut (mp hs2 (mp pl5 h1)) (mp pl6 h2)))
end


lemma update_iff2 {Γ : ctx agents} {φ ψ χ : formPA agents} : 
  prfPA Γ ((U φ ψ) ↔ translate (U φ ψ)) → prfPA Γ ((U φ χ) ↔ translate (U φ χ)) → 
  prfPA Γ ((U φ (ψ & χ) ↔ (U φ ψ & U φ χ))) → 
  prfPA Γ ((U φ (ψ & χ) ↔ translate (U φ ψ) & translate (U φ χ))) :=
begin
intros h1 h2 h3,
exact (mp (mp pl4 (cut (mp pl5 h3) (imp_and_and_imp 
  (mp (mp pl4 (mp pl5 h1)) (mp pl5 h2))))) (cut (imp_and_and_imp 
  (mp (mp pl4 (mp pl6 h1)) (mp pl6 h2))) (mp pl6 h3)))
end


lemma update_iff3 {Γ : ctx agents} {φ ψ : formPA agents} {a : agents} : 
  prfPA Γ (φ ↔ translate φ) → prfPA Γ ((U φ (K a ψ) ↔ (φ ⊃ K a (U φ ψ)))) → 
  prfPA Γ ((φ ⊃ K a (U φ ψ)) ↔ translate (φ ⊃ K a (U φ ψ))) → 
  prfPA Γ (U φ (K a ψ) ↔ (translate φ ⊃ K a (translate (U φ ψ)))) :=
begin
simp at *,
intros h1 h2 h3, sorry
end


lemma update_iff4 {Γ : ctx agents} {φ ψ χ : formPA agents} : 
  prfPA Γ ((U φ ψ) ↔ translate (U φ ψ)) → prfPA Γ ((U φ χ) ↔ translate (U φ χ)) → 
  prfPA Γ ((U φ (ψ ⊃ χ) ↔ (U φ ψ & U φ χ))) → 
  prfPA Γ ((U φ (ψ ⊃ χ) ↔ translate (U φ ψ) ⊃ translate (U φ χ))) :=
begin
sorry
end