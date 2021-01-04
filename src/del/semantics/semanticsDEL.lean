/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/


import del.languageDEL del.syntax.syntaxDEL data.set.basic
import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

variable {agents : Type}
open formPA 
open form
open set


---------------------- Semantics ----------------------

structure frame (agents : Type) :=
(states : Type)
(h : nonempty states)
(rel : agents → states → states → Prop)


def frame.restrict (f : frame agents) (P : f.states → Prop) (s : f.states) (Ps : P s) : frame agents :=
{
  states := { s' : f.states // P s' },
  h := ⟨⟨s, Ps⟩⟩,
  rel := λ a : agents, λ u v, f.rel a u.val v.val
}


variables {α : Type} 
variables (r : α → α → Prop)

def euclidean    := ∀ ⦃x y z⦄, r x y → r x z → r y z 
def euclid_class : set (frame agents ) := { f : frame agents | ∀ a : agents, euclidean   (f.rel a) }
def ref_class    : set (frame agents)  := { f : frame agents | ∀ a : agents, reflexive   (f.rel a) }
def equiv_class  : set (frame agents)  := { f : frame agents | ∀ a : agents, equivalence (f.rel a) }


-- Definition of forces for public announcement logic
def forcesPA : ∀ f : frame agents, 
  (nat → f.states → Prop) → f.states → formPA agents → Prop
  | f v x bot          := false
  | f v x (var n)      := v n x
  | f v x (and φ ψ)    := (forcesPA f v x φ) ∧ (forcesPA f v x ψ)
  | f v x (impl φ ψ)   := (forcesPA f v x φ) → (forcesPA f v x ψ)
  | f v x (box a φ)    := ∀ y, f.rel a x y → forcesPA f v y φ
  | f v x (update φ ψ) := ∀ h : forcesPA f v x φ, 
      forcesPA (f.restrict (λ y, forcesPA f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ


-- φ is valid in a model M = (f,v)
def m_validPA (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) := 
  ∀ x, forcesPA f v x φ


-- Valid in a frame f
def f_validPA (φ : formPA agents) (f : frame agents) := 
  ∀ v x, forcesPA f v x φ


-- φ is valid in a class of frames F
def F_validPA (φ : formPA agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ v x, forcesPA f v x φ


-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctxPA (f : frame agents) (v : nat → f.states → Prop) 
  (Γ : ctxPA agents) := ∀ φ, ∀ x, φ ∈ Γ → forcesPA f v x φ


-- Global semantic consequence
def global_sem_csqPA (Γ : ctxPA agents) (F : set (frame agents)) (φ : formPA agents) :=
  ∀ f ∈ F, ∀ v, forces_ctxPA f v Γ → ∀ x, forcesPA f v x φ


lemma not_forces_impPA (f : frame agents) : ∀ v x φ, 
  (¬(forcesPA f v x φ)) ↔ (forcesPA f v x (¬φ)) :=
begin
intros v x φ, split, 
repeat {intros h1 h2, exact h1 h2},
end


lemma forces_existsPA {a : agents} {f : frame agents} {v : nat → f.states → Prop} 
  {x : f.states} {φ : formPA agents} :
  forcesPA f v x (¬K a ¬φ) ↔ ∃ y : f.states, (f.rel a x y ∧ forcesPA f v y φ) :=
begin
split,
intro h1,
repeat {rw forcesPA at h1},
have h2 := not_or_of_imp h1,
clear h1, cases h2, push_neg at h2,
cases h2 with y h2, cases h2 with h2 h3,
existsi (y : f.states), split, exact h2,
have h4 := (not_forces_impPA f v y (¬φ)).mp h3,
repeat {rw forcesPA at h4}, repeat {rw imp_false at h4},
rw not_not at h4, exact h4,
exact false.elim h2,
intro h1, cases h1 with y h1,
cases h1 with h1 h2,
intro h3,
specialize h3 y h1,
rw ←not_forces_impPA at h3, 
exact absurd h2 h3
end


lemma forces_update_dual (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) :
  forcesPA f v x ¬(U φ (¬ψ)) ↔ ∃ h : forcesPA f v x φ, 
  forcesPA (f.restrict (λ y, forcesPA f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ :=
begin
split,
{intro h1, repeat {rw forcesPA at h1},
rw imp_false at h1,
push_neg at h1,
cases h1 with Ph1 h1, 
existsi (Ph1 : forcesPA f v x φ), 
rw not_forces_impPA at h1, 
repeat {rw forcesPA at h1}, 
rw imp_false at h1, 
push_neg at h1,
cases h1 with Ph2 h2, exact Ph2},
{intro h1, cases h1 with Ph1 h1, 
intro h2, apply h2, exact h1}
end


-- Definition of forces for epistemic logic...used for typeclass inference between systems
def forces : ∀ f : frame agents, 
  (nat → f.states → Prop) → f.states → form agents → Prop
  | f v x form.bot          := false
  | f v x (form.var n)      := v n x
  | f v x (form.and φ ψ)    := (forces f v x φ) ∧ (forces f v x ψ)
  | f v x (form.impl φ ψ)   := (forces f v x φ) → (forces f v x ψ)
  | f v x (form.box a φ)    := ∀ y, f.rel a x y → forces f v y φ


def F_valid (φ : form agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ


-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctx (f : frame agents) (v : nat → f.states → Prop) 
  (Γ : ctx agents) := ∀ φ : form agents, ∀ x, φ ∈ Γ → forces f v x φ


-- Global semantic consequence
def global_sem_csq (Γ : ctx agents) (F : set (frame agents)) (φ : form agents) :=
  ∀ f ∈ F, ∀ v, forces_ctx f v Γ → ∀ x, forces f v x φ


lemma forcesPA_iff_forces (φ : form agents) (f : frame agents) : 
  ∀ v x, forcesPA f v x (to_PA φ) ↔ forces f v x φ :=
begin
intros v x, induction φ generalizing x,
split,
repeat {intro h1, apply h1},
split,
repeat {intro h1, apply h1},
repeat {rename φ_ih_φ ih_φ},
repeat {rename φ_ih_ψ ih_ψ},
split,
intro h1,
cases h1 with h1 h2,
split,
exact (ih_φ x).mp h1,
exact (ih_ψ x).mp h2,
intro h1,
cases h1 with h1 h2,
split,
exact (ih_φ x).mpr h1,
exact (ih_ψ x).mpr h2,
split,
intros h1 h2,
exact (ih_ψ x).mp (h1 ((ih_φ x).mpr h2)),
intros h1 h2,
exact (ih_ψ x).mpr (h1 ((ih_φ x).mp h2)),
split,
intros h1 y h3,
exact (φ_ih y).mp (h1 y h3),
intros h1 y h3,
exact (φ_ih y).mpr (h1 y h3)
end


lemma not_forces_imp (f : frame agents) : ∀ v x φ, 
  (¬(forces f v x φ)) ↔ (forces f v x (¬φ)) :=
begin
intros v x φ, split, 
repeat {intros h1 h2, exact h1 h2},
end


lemma forces_exists {a : agents} {f : frame agents} {v : nat → f.states → Prop} 
  {x : f.states} {φ : form agents} :
  forces f v x (¬K a ¬φ) ↔ ∃ y : f.states, (f.rel a x y ∧ forces f v y φ) :=
begin
split,
intro h1,
repeat {rw forces at h1},
have h2 := not_or_of_imp h1,
clear h1, cases h2, push_neg at h2,
cases h2 with y h2, cases h2 with h2 h3,
existsi (y : f.states), split, exact h2,
have h4 := (not_forces_imp f v y (¬φ)).mp h3,
repeat {rw forces at h4}, repeat {rw imp_false at h4},
rw not_not at h4, exact h4,
exact false.elim h2,
intro h1, cases h1 with y h1,
cases h1 with h1 h2,
intro h3,
exact absurd h2 (h3 y h1)
end


lemma equiv_ref_euclid (f : frame agents) : 
  f ∈ (equiv_class : set (frame agents)) ↔ 
  f ∈ ((ref_class : set (frame agents)) ∩ (euclid_class : set (frame agents))) :=
begin
split,
intro h1,
split,
intro a,
cases h1 a with h1 h2, cases h2 with h2 h3,
exact h1,
intro a, intros x y z h4 h5,
cases h1 a with h1 h2, cases h2 with h2 h3,
exact h3 (h2 h4) h5,
intros h1 a, split,
exact h1.left a,
split, cases h1 with h1 h2,
intros x y h3,
exact (h2 a) h3 (h1 a x),
intros x y z h2 h3, cases h1 with h1 h4,
exact h4 a (h4 a h2 (h1 a x)) h3
end