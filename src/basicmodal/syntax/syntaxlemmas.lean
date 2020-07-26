-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..language ..syntax.syntax ..syntax.soundness data.set.basic

open prfK
local attribute [instance] classical.prop_decidable


---------------------- Helper Lemmas ----------------------


lemma iden {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ φ) :=
begin
exact mp (mp (@pl2 _ φ (φ ⊃ φ) φ) pl1) pl1
end


lemma weak {Γ : ctx} {φ ψ : form} :
  prfK Γ φ → prfK (Γ ∪ ψ) φ :=
begin
  intro h, dsimp,
  induction h,
  { apply ax,
    exact (set.mem_insert_of_mem _ h_h) },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq },
    { exact h_ih_hp } },
  { exact nec h_ih }
end


lemma pr {Γ : ctx} {φ : form} :
  prfK (Γ ∪ φ) φ :=
begin
apply ax;
apply or.intro_left;
simp
end


lemma cut {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ) :=
begin
intros h1 h2,
exact mp (mp pl2 (mp pl1 h2)) h1
end


lemma conv_deduction {Γ : ctx} {φ ψ : form} :
  prfK Γ (φ ⊃ ψ) → prfK (Γ ∪ φ) ψ :=
begin
intro h, 
exact mp (weak h) pr 
end


lemma imp_if_imp_imp {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ χ) → prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 pl1)) h1
end


lemma cut1 {Γ : ctx} {φ ψ χ θ : form} :
  prfK Γ (θ ⊃ (φ ⊃ ψ)) → prfK Γ (ψ ⊃ χ) → prfK Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
have h3 : prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ), from cut,
have h4 : prfK Γ (θ ⊃ (φ ⊃ ψ)) → prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)) → prfK Γ (θ ⊃ (φ ⊃ χ)), from cut,
specialize h4 h1,
have h5 : prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)), from mp pl2 (mp pl1 h2),
specialize h4 h5,
exact h4
end


lemma imp_switch {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ (ψ ⊃ χ)) → prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
intro h1,
have h2 : prfK Γ (ψ ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))), from mp pl1 (mp pl2 h1),
have h3 : prfK Γ ((ψ ⊃ (φ ⊃ ψ)) ⊃ (ψ ⊃ (φ ⊃ χ))), from mp pl2 h2,
exact mp h3 pl1
end


lemma cut2 {Γ : ctx} {φ ψ χ θ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (θ ⊃ (ψ ⊃ χ)) → prfK Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {Γ : ctx} {φ ψ : form} :
  prfK Γ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) :=
begin
have h1 : prfK Γ ((φ ⊃ ((φ ⊃ ψ) ⊃ ψ)) ⊃ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ))), from pl2,
have h2 : prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ ψ)), from iden,
have h3 : prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ ψ)) → prfK Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)), from imp_switch,
specialize h3 h2,
exact mp h1 h3
end


lemma imp_imp_iff_imp {Γ : ctx} {θ φ ψ : form} : 
  prfK Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfK Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 pl1}
end


lemma imp_shift {Γ : ctx} {θ φ ψ χ : form} : 
  prfK Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfK Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 pl1 pl2)}
end


lemma left_and_imp {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (ψ ⊃ ((φ & ψ) ⊃ χ)) → prfK Γ ((φ & ψ) ⊃ χ) :=
begin
intro h1,
exact mp double_imp (cut pl6 h1)
end


lemma and_right_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, 
{intro h1,
exact mp (cut2 pl1 pl2) (cut1 pl4 h1)},
intro h1,
exact left_and_imp (cut2 pl5 h1)
end




--TODOs:
lemma prove_not_imp_not_prove {Γ : ctx} {φ : form} : prfK Γ (¬φ) ↔ ¬prfK Γ φ := sorry

lemma not_contra1 {Γ : ctx} {φ : form} : 
  ¬ prfK Γ (φ & ¬φ) := sorry

lemma not_contra2 {Γ : ctx} {φ : form} : 
  prfK Γ ¬(φ & ¬φ) := sorry