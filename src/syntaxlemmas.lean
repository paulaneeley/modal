-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import language syntax data.set.basic

open prfK


---------------------- Helper Lemmas ----------------------


lemma iden {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ φ) :=
  mp (mp (@pl2 _ φ (φ ⊃ φ) φ) pl1) pl1


/- structural lemmas -/
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


/- subcontext lemmas -/
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


/- right-hand side rules of inference -/
lemma pr {Γ : ctx} {φ : form} :
  prfK (Γ ∪ φ) φ :=
by apply ax; apply or.intro_left; simp

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

lemma cut {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ) :=
λ hpq hqr, mp (mp pl2 (mp pl1 hqr)) hpq

lemma conv_deduction {Γ : ctx} {φ ψ : form} :
  prfK Γ (φ ⊃ ψ) → prfK (Γ ∪ φ) ψ :=
λ h, mp (weak h) pr 

lemma not_pp {Γ : ctx} {φ : form} :
  prfK Γ ((¬φ) ⊃ (φ ⊃ φ)) :=
  begin
  have h1 : prfK Γ ((φ ⊃ φ) ⊃ ((¬φ) ⊃ (φ ⊃ φ))), from pl1,
  have h2 : prfK Γ (φ ⊃ φ), from iden,
  have h3 : prfK Γ ((¬φ) ⊃ (φ ⊃ φ)), from mp h1 h2,
  exact h3
  end


/- left-hand side rules of inference -/
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


lemma dni {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ (¬¬φ)) := sorry


--TODOs:
lemma not_contra {Γ : ctx} {φ : form} : 
  prfK Γ ¬(φ & ¬φ) :=
begin
simp, 
have h1 : prfK Γ ((φ & ¬φ) ⊃ φ), from pl5,
have h2: prfK Γ ((φ & ¬φ) ⊃ ¬φ), from pl6,
sorry
end


lemma and_left_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
split,
{intro h, sorry}, 
sorry
end


lemma and_right_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, intro h1, sorry, sorry
end


lemma imp_if_imp_imp {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ χ) → prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
have h2 : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))), from pl2,
sorry
end


lemma imp_imp_if_imp {Γ : ctx} {θ φ ψ : form} : 
 prfK Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfK Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
sorry
end


lemma imp_shift {Γ : ctx} {θ φ ψ χ : form} : 
 prfK Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfK Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
sorry
end