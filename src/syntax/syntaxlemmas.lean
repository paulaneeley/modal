-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import language syntax.syntax data.set.basic syntax.soundness

open prfK


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
lemma not_contra1 {Γ : ctx} {φ : form} : 
  ¬ prfK Γ (φ & ¬φ) :=
begin
simp, by_contradiction h1,
have h2 : prfK Γ ((φ & ¬φ) ⊃ φ), from pl5,
have h3 : prfK Γ ((φ & ¬φ) ⊃ ¬φ), from pl6,
have h4 : prfK (Γ ∪ (φ & ¬φ)) φ, from conv_deduction h2,
have h5 : prfK (Γ ∪ (φ & ¬φ)) ¬φ, from conv_deduction h3,
have h6 : sem_csq (Γ ∪ (φ & ¬φ)) φ, from soundness (Γ ∪ (φ & ¬φ)) φ h4,
have h7 : sem_csq (Γ ∪ (φ & ¬φ)) ¬φ, from soundness (Γ ∪ (φ & ¬φ)) (¬φ) h5,
rw sem_csq at *, dsimp at h6, dsimp at h7, sorry
end


lemma not_contra {Γ : ctx} {φ : form} : 
  prfK Γ ¬(φ & ¬φ) :=
begin
simp, sorry
end











-- DEPRECATED:
/-
-- structural lemmas
lemma sub_weak {Γ Δ : ctx} {φ : form} :
  (prfK Δ φ) → (Δ ⊆ Γ) → (prfK Γ φ) :=
begin
  intros h s,
  induction h,
  { apply ax, exact s h_h },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq s },
    {exact h_ih_hp s} },
  { exact nec (h_ih s) }
end


lemma sub_weak {Γ Δ : ctx} {φ : form} :
  (prfK Δ φ) → (Δ ⊆ Γ) → (prfK Γ φ) :=
begin
  intros h s,
  induction h,
  { apply ax, exact s h_h },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq s },
    {exact h_ih_hp s} },
  { exact nec (h_ih s) }
end


lemma contr {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ φ) ψ → prfK (Γ ∪ φ) ψ :=
begin
  generalize eq : (Γ ∪ φ ∪ φ) = Γ',
  dsimp at *,
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert},
    { exact h } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl)}
end


lemma exg {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ ψ) χ → prfK (Γ ∪ ψ ∪ φ) χ :=
  begin
  generalize eq : (Γ ∪ φ ∪ ψ) = Γ',
  dsimp at *,
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert_of_mem _ _,
      apply set.mem_insert _ _ },
      { cases set.eq_or_mem_of_mem_insert h with h' h',
        { rw h', apply set.mem_insert _ _ },
        { apply set.mem_insert_of_mem _ _,
          apply set.mem_insert_of_mem _ _, 
          exact h' } } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
    { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl)}
end


-- subcontext lemmas
lemma subctx_ax {Γ Δ : ctx} {φ : form} :
   Δ ⊆ Γ → prfK Δ φ → prfK Γ φ :=
begin
  intros s h,
  induction h,
  { apply ax (s h_h) },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq s },
    { exact h_ih_hp s } },
  { exact nec (h_ih s) }
end


lemma subctx_contr {Γ Δ : ctx} {φ : form}:
   Δ ⊆ Γ → prfK (Γ ∪ Δ) φ → prfK Γ φ :=
begin
  generalize eq : Γ ∪ Δ = Γ',
  intros s h,
  induction h; subst eq,
  { cases h_h,
    { exact ax h_h },
    { exact ax (s h_h) } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl) }
end


lemma pr1 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ ψ) φ :=
by apply ax; apply or.intro_right; apply or.intro_left; simp


lemma pr2 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ ψ) ψ :=
by apply ax; apply or.intro_left; simp


lemma by_mp1 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) ψ :=
mp pr2 pr1


lemma by_mp2 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ (φ ⊃ ψ) ∪ φ) ψ :=
mp pr1 pr2


-- left-hand side rules of inference
lemma mp_in_ctx_left {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ ψ) χ → prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) χ :=
begin
  generalize eq : (Γ ∪ φ ∪ ψ) = Γ',
  dsimp at *,
  intros h,
  induction h; subst eq,
  { cases h_h,
    { rw h_h,
      exact by_mp1 },
    { cases h_h,
      { rw h_h,
        exact pr1 },
      { apply ax,
        apply set.mem_insert_of_mem _ _,
        apply set.mem_insert_of_mem _ _, exact h_h } } },
    { exact pl1 },
    { exact pl2 },
    --{ exact pl3 },
    { exact pl4 },
    { exact pl5 },
    { exact pl6 },
    { exact pl7 },
    { exact kdist },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact nec (h_ih rfl) }
end

lemma mp_in_ctx_right {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) χ → prfK (Γ ∪ φ ∪ ψ) χ :=
begin
  generalize eq : (Γ ∪ φ ∪ (φ ⊃ ψ)) = Γ',
  dsimp at *,
  intros h,
  induction h; subst eq,
  { cases h_h, 
    { subst h_h,
      exact mp pl1 pr },
    { cases h_h,
      { subst h_h, 
        exact pr1 },
      { exact weak (weak (ax h_h)) } } },    
    { exact pl1 },
    { exact pl2 },
    --{ exact pl3 },
    { exact pl4 },
    { exact pl5 },
    { exact pl6 },
    { exact pl7 },
    { exact kdist },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact nec (h_ih rfl) }
end


lemma iden_imp_imp {Γ : ctx} {φ ψ : form} : prfK Γ (((φ ⊃ φ) ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) :=
begin
exact cut pl2 weak_imp
end


lemma not_id {Γ : ctx} {φ : form} :
  prfK Γ ((¬φ) ⊃ (φ ⊃ φ)) :=
begin
exact mp pl1 iden
end


-/
