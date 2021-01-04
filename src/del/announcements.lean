/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.languageDEL del.semantics.semanticsDEL 
import data.set.basic data.equiv.basic
local attribute [instance] classical.prop_decidable

variable {agents : Type}


---------------------- Facts about Announcements ----------------------


-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : formPA agents) : 
  F_validPA ((¬(U φ (¬ψ))) ⊃ (U φ ψ)) equiv_class :=
begin
intros f h v x h1,
rw forces_update_dual at h1,
cases h1 with Ph1 h1, intro h, exact h1
end


-- Proposition 4.11, pg. 77
lemma partial_announce (φ ψ : formPA agents) : 
  ¬ (F_validPA ¬(U φ ¬⊥)) equiv_class :=
begin
rw F_validPA, 
push_neg,
let f : frame agents := 
{ states := nat,
  h := ⟨0⟩,
  rel := λ a, λ x y : nat, x = y 
}, 
use f, split, intro a,
split, intro x, 
exact eq.refl x,
split, intros x y h,
exact eq.symm h,
intros x y z h1 h2, 
exact eq.trans h1 h2,
let v : nat → f.states → Prop := λ n x, false,
use v,
let x : f.states := 42,
use x, rw forcesPA, rw not_imp,
split, intro h, intro h1, exact h1,
rw forcesPA, trivial
end


--Proposition 4.22
lemma public_annouce_var (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
  forcesPA f v x (U φ p n) ↔ forcesPA f v x (φ ⊃ (p n)) :=
begin
split, repeat {intros h1 h2, exact h1 h2},
end


lemma public_annouce_conj (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) :
  forcesPA f v x (U φ (ψ & χ)) ↔ forcesPA f v x ((U φ ψ) & (U φ χ)) :=
begin
split,
intro h1,
split,
intro h2,
exact (h1 h2).left,
intro h2,
exact (h1 h2).right, 
intros h1 h2,
split,
exact h1.left h2,
exact h1.right h2,
end


-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) : 
  forcesPA f v x (U φ (¬ψ)) ↔ forcesPA f v x (φ ⊃ ¬(U φ ψ))  :=
begin
split,
intros h1 h2 h3, specialize h1 h2,
rw ←not_forces_impPA at h1,
exact absurd (h3 h2) h1,
intros h1, rw forcesPA at h1, rw imp_iff_not_or at h1,
cases h1,
intro h2, exact absurd h2 h1,
intros h h2, apply h1, intro h3, exact h2
end


-- Proposition 4.18, pg. 79
lemma public_announce_know (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) (a : agents) :
  forcesPA f v s (U φ (K a ψ)) ↔ forcesPA f v s (φ ⊃ (K a (U φ ψ))) :=
begin
split,
intros h1 h2 t hrel h3,
exact h1 h2 ⟨t, h3⟩ hrel,
rintros h1 h2 ⟨t, h3⟩ hrel,
exact h1 h2 t hrel h3,
end


namespace compositionPA

variables A A' : Prop
variable  B    : A → Prop
variable  A''  : A' → Prop
variable  B'   : ∀ h : A', A'' h → Prop


lemma comp_helper1 (h : A ↔ ∃ h : A', A'' h) 
  (h' : ∀ (h1 : A) (h2 : A') (h3 : A'' h2), B h1 ↔ B' h2 h3) : 
  (∀ h1 : A, B h1) ↔ (∀ h2 h3, B' h2 h3) :=
begin
  split,
  { intros hh h2 h3, 
    have h1 : A := h.mpr ⟨h2, h3⟩,
    exact (h' h1 h2 h3).mp (hh h1) },
  intros hh h1,
  cases h.mp h1 with h2 h3,
  exact (h' h1 h2 h3).mpr (hh h2 h3)
end


lemma comp_helper2 (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) :
  forcesPA f v s (φ & U φ ψ) ↔ 
  (∃ h : forcesPA f v s φ, forcesPA (f.restrict 
  (λ y, forcesPA f v y φ) s h) (λ n u, v n u.val) ⟨s, h⟩ ψ) :=
begin
split,
intro h1,
cases h1 with h1 h2,
use h1, 
apply h2,
intro h1,
cases h1 with h1 h2,
split,
exact h1,
intro h3,
exact h2,
end


def is_frame_iso (f1 f2 : frame agents) (F : f1.states ≃ f2.states) := 
  ∀ x x' : f1.states, ∀ a : agents, (f1.rel a x x' ↔ f2.rel a (F x) (F x'))


def is_model_iso (f1 f2 : frame agents) (v1 : nat → f1.states → Prop)
  (v2 : nat → f2.states → Prop) (F : f1.states ≃ f2.states) := 
  is_frame_iso f1 f2 F ∧ ∀ n, ∀ x : f1.states, v1 n x = v2 n (F x)


lemma model_iso_symm {f1 f2 : frame agents} {v1 : nat → f1.states → Prop}
  {v2 : nat → f2.states → Prop} {F : f1.states ≃ f2.states} :
  is_model_iso f1 f2 v1 v2 F → is_model_iso f2 f1 v2 v1 (F.symm) :=
begin
intro h1,
cases h1 with h1 h2,
split,
intros x x' a,
specialize h1 (F.inv_fun x) (F.inv_fun x') a, 
simp at h1,
exact h1.symm,
intros n x,
specialize h2 n (F.inv_fun x), simp at *,
exact h2.symm
end


def restrict_F {f1 f2 : frame agents} {v1 : nat → f1.states → Prop}
  {v2 : nat → f2.states → Prop} (F : f1.states ≃ f2.states) 
  (φ : formPA agents) (x : f1.states) (h : ∀ y : f1.states,
  (forcesPA f1 v1 y φ ↔ forcesPA f2 v2 (F y) φ)) (h' : forcesPA f1 v1 x φ)
  (h'' : forcesPA f2 v2 (F x) φ) : 
  (f1.restrict (λ y, forcesPA f1 v1 y φ) x h').states 
  ≃ (f2.restrict (λ y, forcesPA f2 v2 y φ) (F x) h'').states :=
{ to_fun := λ ⟨y, hy⟩, ⟨(F y), (h y).mp hy⟩,
  inv_fun := λ ⟨y, hy⟩, ⟨(F.inv_fun y), (h (F.inv_fun y)).mpr 
  begin
    convert hy,
    apply F.right_inv,
  end ⟩,
  left_inv := 
  begin
    intro y,
    cases y with y hy,
    ext,
    apply F.left_inv,
  end,
  right_inv := 
  begin
  intro y,
    cases y with y hy,
    ext,
    apply F.right_inv,
  end }


lemma update_iso {f1 f2 : frame agents} {v1 : nat → f1.states → Prop}
  {v2 : nat → f2.states → Prop} (F : f1.states ≃ f2.states) :
  is_model_iso f1 f2 v1 v2 F → ∀ φ : formPA agents,
  ∀ h : (∀ x : f1.states, forcesPA f1 v1 x φ ↔ forcesPA f2 v2 (F x) φ), 
  ∀ x, ∀ h' : forcesPA f1 v1 x φ, 
  ∀ h'' : forcesPA f2 v2 (F x) φ, 
  is_model_iso (f1.restrict (λ y, forcesPA f1 v1 y φ) x h') 
  (f2.restrict (λ y, forcesPA f2 v2 y φ) (F x) h'') (λ n u, v1 n u.val) 
  (λ n u, v2 n u.val) (restrict_F F φ x h h' h'') :=
begin
intros h1 φ h2 x h3 h4,
cases h1 with h1 h6,
split,
rintros ⟨x1, hx1⟩ ⟨y1, hy1⟩ a,
apply h1 x1 y1 a,
rintros n ⟨x1, hx1⟩,
apply h6 n x1,
end


lemma comp_helper3 (f1 f2 : frame agents) (v1 : nat → f1.states → Prop)
  (v2 : nat → f2.states → Prop) (F : f1.states ≃ f2.states) :
  is_model_iso f1 f2 v1 v2 F → ∀ s1 : f1.states, ∀ φ : formPA agents, 
  forcesPA f1 v1 s1 φ ↔ forcesPA f2 v2 (F s1) φ :=
begin
intro h1,
intros x1 φ, induction φ generalizing f1 v1 f2 v2 F h1 x1,
split,
repeat {intro h3, exact h3},
split,
repeat {intro h3,
rename φ n,
cases h1 with h1 h2,
specialize h2 n x1,
rw forcesPA at *,
convert h3},
exact eq.symm h2,
repeat {rename φ_φ φ}, 
repeat {rename φ_ψ ψ},
repeat {rename φ_ih_φ φ_ih},
repeat {rename φ_ih_ψ ψ_ih},
repeat {rename φ_a a},
split,
repeat {intro h3,
cases h3 with h3 h4,
split},
exact (φ_ih f1 v1 f2 v2 F h1 x1).mp h3,
exact (ψ_ih f1 v1 f2 v2 F h1 x1).mp h4,
exact (φ_ih f1 v1 f2 v2 F h1 x1).mpr h3,
exact (ψ_ih f1 v1 f2 v2 F h1 x1).mpr h4,
split,
repeat {intros h3 h4},
exact (ψ_ih f1 v1 f2 v2 F h1 x1).mp (h3 ((φ_ih f1 v1 f2 v2 F h1 x1).mpr h4)),
exact (ψ_ih f1 v1 f2 v2 F h1 x1).mpr (h3 ((φ_ih f1 v1 f2 v2 F h1 x1).mp h4)),
split,
intros h3 y1 h4,
specialize φ_ih f1 v1 f2 v2 F h1 (F.inv_fun y1),
cases h1 with h1 h5,
specialize h1 x1 (F.inv_fun y1) a,
simp at *,
exact φ_ih.mp (h3 (F.inv_fun y1) (h1.mpr h4)),
intros h3 x2 h4,
specialize φ_ih f1 v1 f2 v2 F h1 x2,
cases h1 with h1 h5,
exact φ_ih.mpr (h3 (F.to_fun x2) ((h1 x1 x2 a).mp h4)),
split,
intro h2,
specialize φ_ih f1 v1 f2 v2 F h1,
intro h3,
have h4 := ((φ_ih x1).mpr h3),
have h5 := update_iso F h1 φ φ_ih x1 h4 h3,
specialize ψ_ih (f1.restrict (λ (y : f1.states), forcesPA f1 v1 y φ) x1 h4)
  (λ (n : ℕ) (u : (f1.restrict (λ (y : f1.states), forcesPA f1 v1 y φ) x1 h4).states), v1 n u.val)
  (f2.restrict (λ (y : f2.states), forcesPA f2 v2 y φ) (F x1) h3)
  (λ (n : ℕ) (u : (f2.restrict (λ (y : f2.states), forcesPA f2 v2 y φ) (F x1) h3).states), 
  v2 n u.val) (restrict_F F φ x1 φ_ih h4 h3) h5 ⟨x1, h4⟩,
have h6 := ψ_ih.mp (h2 h4),
convert h6,
intro h2,
specialize φ_ih f1 v1 f2 v2 F h1,
intro h3,
have h4 := (φ_ih x1).mp h3,
have h5 := update_iso F h1 φ φ_ih x1 h3 h4,
specialize ψ_ih (f2.restrict (λ (y : f2.states), forcesPA f2 v2 y φ) (F x1) h4)
  (λ (n : ℕ) (u : (f2.restrict (λ (y : f2.states), forcesPA f2 v2 y φ) (F x1) h4).states), v2 n u.val)
  (f1.restrict (λ (y : f1.states), forcesPA f1 v1 y φ) x1 h3)
  (λ (n : ℕ) (u : (f1.restrict (λ (y : f1.states), forcesPA f1 v1 y φ) x1 h3).states), v1 n u.val) 
  (_) (model_iso_symm h5) ⟨F x1, h4⟩,
have h6 := ψ_ih.mp (h2 h4),
convert h6,
{exact (equiv.eq_symm_apply F).mpr rfl},
end


-- Proposition 4.17, pg. 78
lemma public_announce_comp (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) :
  forcesPA f v s (U (φ & U φ ψ) χ) ↔ forcesPA f v s (U φ (U ψ χ)) :=
begin
apply comp_helper1,
apply comp_helper2,
intros h1 h2 h3,
let F : (f.restrict (λ (y : f.states), forcesPA f v y (φ&φ.update ψ)) s h1).states ≃ ((f.restrict 
  (λ (y : f.states), forcesPA f v y φ) s h2).restrict (λ (y : (f.restrict (λ (y : f.states), 
  forcesPA f v y φ) s h2).states), forcesPA (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2) 
  (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), v n u.val) y ψ) 
  ⟨s, h2⟩ h3).states :=
  {to_fun :=
  begin
    rintro ⟨x, h⟩,
    use x,
    apply h.left,
    apply h.right,
  end,
  inv_fun := 
  begin
    rintro ⟨⟨x, h4⟩, h5⟩,
    exact ⟨x, ⟨h4, λ _, h5⟩⟩, 
  end,
  left_inv := 
  begin
    rintro ⟨x, h⟩,
    ext,
    refl,
  end,
  right_inv :=
  begin
    rintro ⟨⟨x, h4⟩, h5⟩,
    refl,
  end},
have h4 := comp_helper3 (f.restrict (λ (y : f.states), forcesPA f v y (φ&φ.update ψ)) s h1)
  ((f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).restrict (λ (y : (f.restrict (λ (y : f.states), 
  forcesPA f v y φ) s h2).states), forcesPA (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2) 
  (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), v n u.val) y ψ) ⟨s, h2⟩ h3)
  (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y (φ&φ.update ψ)) s h1).states), v n u.val)
  (λ (n : ℕ) (u : ((f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).restrict (λ (y : (f.restrict 
  (λ (y : f.states), forcesPA f v y φ) s h2).states), forcesPA (f.restrict (λ (y : f.states), forcesPA f v y φ)
  s h2) (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), v n u.val) y ψ) 
  ⟨s, h2⟩ h3).states), (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), 
  v n u.val) n u.val),
specialize h4 F,
have h5 : is_model_iso (f.restrict (λ (y : f.states), forcesPA f v y (φ&φ.update ψ)) s h1) 
  ((f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).restrict (λ (y : (f.restrict (λ (y : f.states), 
  forcesPA f v y φ) s h2).states), forcesPA (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2) 
  (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), v n u.val) y ψ) 
  ⟨s, h2⟩ h3) (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), forcesPA f v y (φ&φ.update ψ)) s h1).states), 
  v n u.val) (λ (n : ℕ) (u : ((f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).restrict 
  (λ (y : (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), forcesPA (f.restrict 
  (λ (y : f.states), forcesPA f v y φ) s h2) (λ (n : ℕ) (u : (f.restrict (λ (y : f.states), 
  forcesPA f v y φ) s h2).states), v n u.val) y ψ) ⟨s, h2⟩ h3).states), (λ (n : ℕ) (u : 
  (f.restrict (λ (y : f.states), forcesPA f v y φ) s h2).states), v n u.val) n u.val) F,
{
  split,
  rintros ⟨x1, hx1⟩ ⟨y1, hy1⟩ a,
  refl,
  rintros n ⟨x, hx⟩,
  refl
},
convert h4 h5 ⟨s, h1⟩ χ
end


end compositionPA

