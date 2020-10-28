-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.syntax.syntaxDEL data.set.basic
variable {agents : Type}
open formPA 
local attribute [instance] classical.prop_decidable


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

-- definition of forces
def forces : ∀ f : frame agents, 
  (nat → f.states → Prop) → f.states → formPA agents → Prop
  | f v x bot          := false
  | f v x (var n)      := v n x
  | f v x (and φ ψ)    := (forces f v x φ) ∧ (forces f v x ψ)
  | f v x (impl φ ψ)   := (forces f v x φ) → (forces f v x ψ)
  | f v x (box a φ)    := ∀ y, f.rel a x y → forces f v y φ
  | f v x (update φ ψ) := ∀ h : forces f v x φ, 
      forces (f.restrict (λ y, forces f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ

-- φ is valid in a model M = (f,v)
def m_valid (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) := 
  ∀ x, forces f v x φ

-- valid in a frame f
def f_valid (φ : formPA agents) (f : frame agents) := 
  ∀ v x, forces f v x φ

-- φ is valid in a class of frames F = set f
def F_valid (φ : formPA agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ

-- -- φ is universally valid (valid in all frames)
-- def u_valid (φ : formPA agents) := 
--   ∀ f v x, forces f v x φ

-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctx (f : frame agents) (v : nat → f.states → Prop) 
  (Γ : ctx agents) := ∀ φ, ∀ x, φ ∈ Γ → forces f v x φ

-- Local semantic consequence
def local_sem_csq (Γ : ctx agents) (φ : formPA agents) :=
  ∀ f v x, forces_ctx f v Γ → forces f v x φ

-- Global semantic consequence
def global_sem_csq (Γ : ctx agents) (φ : formPA agents) :=
  ∀ f v x, forces_ctx f v Γ → forces f v x φ


open set
variables (f : frame agents) {α : Type} (a : agents) (r : α → α → Prop)

def euclidean := ∀ ⦃x y z⦄, r x y → r x z → r y z 

--def ref_class : set (frame agents) := { f : frame agents | ∀ a : agents, reflexive (f.rel a) }
--def symm_class : set (frame agents) := { f : frame agents | ∀ a : agents, symmetric (f.rel a) }
--def trans_class : set (frame agents ) := { f : frame agents | ∀ a : agents, transitive (f.rel a) }
def euclid_class : set (frame agents ) := { f : frame agents | ∀ a : agents, euclidean (f.rel a) }
--def ref_trans_class : set (frame agents) := ref_class ∩ trans_class
def equiv_class : set (frame agents) := { f : frame agents | ∀ a : agents, equivalence (f.rel a) }


lemma not_forces_imp (f : frame agents) : ∀ v x φ, 
  (¬(forces f v x φ)) ↔ (forces f v x (~φ)) :=
begin
intros v x φ, split, 
{intros h1 h2, exact h1 h2},
{intros h1 h2, specialize h1 h2, exact h1}
end

lemma forces_exists {a : agents} {f : frame agents} {v : nat → f.states → Prop} {x : f.states} {φ : formPA agents} :
  forces f v x (~K a ~φ) ↔ ∃ y : f.states, (f.rel a x y ∧ forces f v y φ) :=
begin
split,
intro h1,
rw forces at h1, rw forces at h1,
have h2 := not_or_of_imp h1,
clear h1, cases h2, push_neg at h2,
cases h2 with y h2, cases h2 with h2 h3,
existsi (y : f.states), split, exact h2,
have h4 := (not_forces_imp f v y (~φ)).mp h3,
repeat {rw forces at h4}, repeat {rw imp_false at h4},
rw not_not at h4, exact h4,
rw forces at h2, exact false.elim h2,
intro h1, cases h1 with y h1,
cases h1 with h1 h2,
rw forces,
intro h3,
rw forces at h3, specialize h3 y h1,
rw ←not_forces_imp at h3, 
exact absurd h2 h3
end

lemma forces_update_dual (φ ψ : formPA agents) (f : frame agents) (v : nat → f.states → Prop) (x : f.states) : 
forces f v x ~(U φ (~ψ)) ↔ ∃ h : forces f v x φ, 
      forces (f.restrict (λ y, forces f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ :=
begin
split,
{intro h1, rw forces at h1, rw forces at h1,
rw forces at h1, rw imp_false at h1,
push_neg at h1,
cases h1 with Ph1 h1, 
existsi (Ph1 : forces f v x φ), rw not_forces_imp at h1, 
rw forces at h1, rw forces at h1,
rw forces at h1, rw imp_false at h1, 
push_neg at h1,
cases h1 with Ph2 h2, exact Ph2},
{intro h1, cases h1 with Ph1 h1, 
intro h2, apply h2, exact h1}
end
