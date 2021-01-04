/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import basicmodal.language basicmodal.syntax.syntax 
import basicmodal.semantics.semantics data.set.basic basicmodal.paths 
import basicmodal.semantics.definability
local attribute [instance] classical.prop_decidable

open form


---------------------- Frame Undefinability ----------------------


-- F (a class of frames) is undefinable
def undefinable (F : set (frame)) :=
  ∀ φ, ¬ defines φ F


-- The theory of x in m
def theory_at (f : frame) (v : nat → f.states → Prop) (x : f.states) : 
  set (form) := { φ : form | forces f v x φ}


-- Invariance under disjoint union
variables {α β : Type}
def frame.rel.dunion (r1 : α → α → Prop) (r2 : β → β → Prop) : 
  (sum α β) → (sum α β) → Prop
  | (sum.inl a1) (sum.inl a2) := r1 a1 a2
  | (sum.inr b1) (sum.inr b2) := r2 b1 b2
  | _ _                       := false


def val_dunion {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) : nat → (sum f1.states f2.states) → Prop
  | n (sum.inl x1) := v1 n x1
  | n (sum.inr x2) := v2 n x2


def frame.dunion (f1 f2 : frame) : frame :=
{
  states := sum f1.states f2.states,
  h := ⟨sum.inl f1.h.default⟩, 
  rel := frame.rel.dunion (f1.rel) (f2.rel)
}


theorem invariance_dunion (f1 f2 : frame) (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (x1 : f1.states) : 
  theory_at f1 v1 x1 = theory_at (f1.dunion f2) (val_dunion v1 v2) (sum.inl x1) :=
begin
ext φ, revert x1, induction φ,
repeat {rename φ_ih_φ ih_φ},
repeat {rename φ_ih_ψ ih_ψ},
repeat {rename φ_φ φ},
repeat {rename φ_ψ ψ},
repeat {intro x1},
repeat {split},
repeat {intro h, exact h},
{intro h, split, exact (ih_φ x1).mp h.left, exact (ih_ψ x1).mp h.right},
{intro h, split, exact (ih_φ x1).mpr h.left, exact (ih_ψ x1).mpr h.right},
{intros h h1, exact (ih_ψ x1).mp (h ((ih_φ x1).mpr h1))}, 
{intros h h1, exact (ih_ψ x1).mpr (h ((ih_φ x1).mp h1))},
{intros h s h1, cases s, exact (φ_ih s).mp ((h s) h1), exact false.elim h1},
{intros h s h1, exact (φ_ih s).mpr ((h (sum.inl s)) h1)}
end


-- Invariance under generated submodels
def frame.gen_subframe (f : frame) (x : f.states) : frame :=
{
  states := { y // reachable (f.rel) x y},
  h := ⟨⟨x, ref_close x (f.rel)⟩⟩,
  rel := λ x1 x2, (f.rel) x1.val x2.val
}


def val_gen_subframe (f : frame) (x : f.states)
  (v : nat → f.states → Prop) : nat → (frame.gen_subframe f x).states → Prop :=
  λ n, λ y, v n y.val


theorem invariance_gen_submodel (f : frame) (v : ℕ → f.states → Prop) 
  (x : f.states) (y : (frame.gen_subframe f x).states) :
  theory_at f v y.val = theory_at (f.gen_subframe x) (val_gen_subframe f x v) y :=
begin
ext φ, revert y, induction φ,
repeat {rename φ_ih_φ ih_φ},
repeat {rename φ_ih_ψ ih_ψ},
repeat {rename φ_φ φ},
repeat {rename φ_ψ ψ},
repeat {intro y},
repeat {split},
repeat {intro h1, exact h1}, 
{intro h1, split, exact (ih_φ y).mp h1.left, exact (ih_ψ y).mp h1.right}, 
{intro h1, split, exact (ih_φ y).mpr h1.left, exact (ih_ψ y).mpr h1.right}, 
{intros h1 h2, exact (ih_ψ y).mp (h1 ((ih_φ y).mpr h2))}, 
{intros h1 h2, exact (ih_ψ y).mpr (h1 ((ih_φ y).mp h2))},
{intros h1 z h2, exact (φ_ih z).mp ((h1 z.val) h2)}, 
{intros h1 z h2, 
have h3 := reach_right x y.1 z f.rel (and.intro y.2 h2),
exact (φ_ih ⟨z, h3⟩).mpr ((h1 ⟨z, h3⟩) h2)}
end


-- Invariance under bisimulation
def base {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (x1 : f1.states) (x2 : f2.states) := 
  ∀ n, v1 n x1 ↔ v2 n x2


def forth {f1 f2 : frame} (bisim : f1.states → f2.states → Prop) 
  (x1 : f1.states) (x2 : f2.states) := 
  ∀ y1, f1.rel x1 y1 → (∃ y2 : f2.states, f2.rel x2 y2 ∧ bisim y1 y2)


def back {f1 f2 : frame} (bisim : f1.states → f2.states → Prop) 
  (x1 : f1.states) (x2 : f2.states) := 
  ∀ y2, f2.rel x2 y2 → (∃ y1 : f1.states, f1.rel x1 y1 ∧ bisim y1 y2)


-- Bisimulation between M1 = (f1,v1) and M2 = (f2,v2)
def is_bisimulation {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) := ∀ x1 x2,
  bisim x1 x2 → (base v1 v2 x1 x2 ∧ forth bisim x1 x2 ∧ back bisim x1 x2)


theorem invariance_bisim {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) 
  (h : is_bisimulation v1 v2 bisim) (x1 : f1.states) (x2 : f2.states) : 
  bisim x1 x2 → theory_at f1 v1 x1 = theory_at f2 v2 x2 :=
begin
intro h1, ext φ, revert x1 x2, induction φ,
repeat {rename φ_ih_φ ih_φ},
repeat {rename φ_ih_ψ ih_ψ},
repeat {rename φ_φ φ},
repeat {rename φ_ψ ψ},
repeat {intros x1 x2 h1},
{split, repeat {intro h2, exact h2}}, 
{split, 
intro h2, exact ((h x1 x2 h1).left φ).mp h2, 
intro h2, exact ((h x1 x2 h1).left φ).mpr h2}, 
{split, 
intro h2, split, exact (ih_φ x1 x2 h1).mp h2.left, exact (ih_ψ x1 x2 h1).mp h2.right, 
intro h2, split, exact (ih_φ x1 x2 h1).mpr h2.left, exact (ih_ψ x1 x2 h1).mpr h2.right}, 
{split, 
intros h2 h3, exact (ih_ψ x1 x2 h1).mp (h2 ((ih_φ x1 x2 h1).mpr h3)), 
intros h2 h3, exact (ih_ψ x1 x2 h1).mpr (h2 ((ih_φ x1 x2 h1).mp h3))},
{cases h x1 x2 h1 with h4 h5,
cases h5 with h5 h6, split,
{intros h2 y2 h3, cases h6 y2 h3 with y1 h6, 
cases h6 with h6 h7, exact (φ_ih y1 y2 h7).mp (h2 y1 h6)},
{intros h2 y1 h3, cases h5 y1 h3 with y2 h5, 
cases h5 with h5 h7, exact (φ_ih y1 y2 h7).mpr (h2 y2 h5)}}
end


-- Invariance using surjective bounded morphisms
open function


def is_bddmorphism {f1 f2 : frame} (g : f1.states → f2.states) := 
  ∀ x1 : f1.states, forth (λ x1 x2, (g x1) = x2) x1 (g x1) ∧ back (λ x1 x2, (g x1) = x2) x1 (g x1)


def is_surjbddmorphism {f1 f2 : frame} (g : f1.states → f2.states) 
  := surjective g ∧ is_bddmorphism g


theorem pull_back {f1 f2 : frame} (g : f1.states → f2.states) (h : is_surjbddmorphism g) :
  ∀ φ, ¬ f_valid φ f2 → ¬ f_valid φ f1 :=
begin
intros φ h1, rw f_valid at *, 
push_neg at h1, push_neg,
cases h1 with v2 h1,
cases h1 with y h1,
let v1 := (λ n x, v2 n (g x)), use v1,
cases h with hl hr, cases hl y with x hl, 
existsi (x : f1.states), have h3 := invariance_bisim v1 v2 (λ x y, g x = y),
have h4 : is_bisimulation v1 v2 (λ (x : f1.states) (y : f2.states), g x = y), 
{intros x1 x2 h2, split,
{intro n, split, intro h, subst h2, apply h, intro h, subst h2, apply h},
split,
have h5 : forth (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2, 
from eq.subst h2 (hr x1).left, exact h5, 
have h5 : back (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2,
from eq.subst h2 (hr x1).right, exact h5},
specialize h3 h4 x y hl, intro h2, apply h1,
rw set.subset.antisymm_iff at h3, cases h3, 
rw set.subset_def at h3_left,
exact h3_left φ h2
end


lemma invariance_pull_back (F : set (frame)) {f1 f2 : frame} 
  (h1 : f1 ∈ F) (h2 : f2 ∉ F) : 
  (∃ g : f1.states → f2.states, is_surjbddmorphism g) → undefinable F :=
begin
intro h, cases h with g h,
intro φ, by_contradiction h3, 
have h4 := h3 f1, specialize h3 f2, 
rw ←not_iff_not at h3,
exact (pull_back g h φ (h3.mp h2)) (h4.mp h1)
end