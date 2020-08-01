-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL ..syntax.syntaxDEL ..syntax.soundnessDEL data.set.basic

open prfPA
local attribute [instance] classical.prop_decidable
variables {agents : Type}


---------------------- Helper Lemmas ----------------------


lemma iden {Γ : ctx agents} {φ : formPA agents} :
  prfPA Γ (φ ⊃ φ) :=
begin
exact mp (mp (@pl2 _ _ φ (φ ⊃ φ) φ) pl1) pl1
end


lemma weak {Γ : ctx agents} {φ ψ : formPA agents} :
  prfPA Γ φ → prfPA (Γ ∪ ψ) φ :=
begin
  intro h, dsimp,
  induction h,
  { apply ax,
    exact (set.mem_insert_of_mem _ h_h) },
  { exact pl1 },
  { exact pl2 },
  { exact pl3},
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact kdist },
  {exact truth},
  {exact posintro},
  {exact negintro},
  { apply mp,
    { exact h_ih_hpq },
    { exact h_ih_hp } },
  { exact nec h_ih },
  { exact atomicperm },
  { exact announceneg },
  { exact announceconj },
  { exact announceknow },
  { exact announcecomp }
end


lemma pr {Γ : ctx agents} {φ : formPA agents} :
  prfPA (Γ ∪ φ) φ :=
begin
apply ax;
apply or.intro_left;
simp
end


lemma cut {Γ : ctx agents} {φ ψ χ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA Γ (ψ ⊃ χ) → prfPA Γ (φ ⊃ χ) :=
begin
intros h1 h2,
exact mp (mp pl2 (mp pl1 h2)) h1
end


lemma conv_deduction {Γ : ctx agents} {φ ψ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA (Γ ∪ φ) ψ :=
begin
intro h, 
exact mp (weak h) pr 
end


lemma imp_if_imp_imp {Γ : ctx agents} {φ ψ χ : formPA agents} : prfPA Γ (φ ⊃ χ) → prfPA Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 pl1)) h1
end


lemma cut1 {Γ : ctx agents} {φ ψ χ θ : formPA agents} :
  prfPA Γ (θ ⊃ (φ ⊃ ψ)) → prfPA Γ (ψ ⊃ χ) → prfPA Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
have h3 : prfPA Γ (φ ⊃ ψ) → prfPA Γ (ψ ⊃ χ) → prfPA Γ (φ ⊃ χ), from cut,
have h4 : prfPA Γ (θ ⊃ (φ ⊃ ψ)) → prfPA Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)) → prfPA Γ (θ ⊃ (φ ⊃ χ)), from cut,
specialize h4 h1,
have h5 : prfPA Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)), from mp pl2 (mp pl1 h2),
specialize h4 h5,
exact h4
end


lemma imp_switch {Γ : ctx agents} {φ ψ χ : formPA agents} : prfPA Γ (φ ⊃ (ψ ⊃ χ)) → prfPA Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
intro h1,
have h2 : prfPA Γ (ψ ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))), from mp pl1 (mp pl2 h1),
have h3 : prfPA Γ ((ψ ⊃ (φ ⊃ ψ)) ⊃ (ψ ⊃ (φ ⊃ χ))), from mp pl2 h2,
exact mp h3 pl1
end


lemma cut2 {Γ : ctx agents} {φ ψ χ θ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA Γ (θ ⊃ (ψ ⊃ χ)) → prfPA Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {Γ : ctx agents} {φ ψ : formPA agents} :
  prfPA Γ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) :=
begin
have h1 : prfPA Γ ((φ ⊃ ((φ ⊃ ψ) ⊃ ψ)) ⊃ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ))), from pl2,
have h2 : prfPA Γ ((φ ⊃ ψ) ⊃ (φ ⊃ ψ)), from iden,
have h3 : prfPA Γ ((φ ⊃ ψ) ⊃ (φ ⊃ ψ)) → prfPA Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)), from imp_switch,
specialize h3 h2,
exact mp h1 h3
end


lemma imp_imp_iff_imp {Γ : ctx agents} {θ φ ψ : formPA agents} : 
  prfPA Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfPA Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 pl1}
end


lemma imp_shift {Γ : ctx agents} {θ φ ψ χ : formPA agents} : 
  prfPA Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfPA Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 pl1 pl2)}
end


lemma left_and_imp {Γ : ctx agents} {φ ψ χ : formPA agents} :
  prfPA Γ (ψ ⊃ ((φ & ψ) ⊃ χ)) → prfPA Γ ((φ & ψ) ⊃ χ) :=
begin
intro h1,
exact mp double_imp (cut pl5 h1)
end


lemma and_right_imp {Γ : ctx agents} {φ ψ χ : formPA agents} : 
  prfPA Γ ((φ & ψ) ⊃ χ) ↔ prfPA Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, 
{intro h1,
exact mp (cut2 pl1 pl2) (cut1 pl3 h1)},
intro h1,
exact left_and_imp (cut2 pl4 h1)
end




--TODOs:
lemma prove_not_imp_not_prove {Γ : ctx agents} {φ : formPA agents} : prfPA Γ (~φ) ↔ ¬prfPA Γ φ := sorry

lemma not_contra1 {Γ : ctx agents} {φ : formPA agents} : 
  ¬ prfPA Γ (φ & ~φ) := sorry

lemma not_contra2 {Γ : ctx agents} {φ : formPA agents} : 
  prfPA Γ ~(φ & ~φ) := sorry