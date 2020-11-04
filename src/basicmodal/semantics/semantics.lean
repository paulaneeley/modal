import basicmodal.language basicmodal.syntax.syntax
import logic.basic data.set.basic
local attribute [instance] classical.prop_decidable


open form

---------------------- Semantics ----------------------

-- definition of relational frame
structure frame :=
(states : Type)
(h : inhabited states)
(rel : states → states → Prop)

-- definition of forces
def forces (f : frame) (v : nat → f.states → Prop) : f.states → form → Prop
  | x (bot)    := false
  | x (var n)  := v n x
  | x (and φ ψ)  := (forces x φ) ∧ (forces x ψ)
  | x (impl φ ψ) := (forces x φ) → (forces x ψ)
  | x (box φ)  := ∀ y, f.rel x y → forces y φ

-- φ is valid in a model M = (f,v)
def m_valid (φ : form) (f : frame) 
  (v : nat → f.states → Prop) := 
  ∀ x, forces f v x φ

-- φ is valid in a frame f
def f_valid (φ : form) (f : frame) := 
  ∀ v x, forces f v x φ

-- φ is valid in a class of frames F
def F_valid (φ : form) (F : set (frame)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ

-- φ is universally valid (valid in all frames)
def u_valid (φ : form) := 
  ∀ f v x, forces f v x φ

-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctx (f : frame) (v : nat → f.states → Prop) 
  (Γ : ctx) := ∀ φ, ∀ x, φ ∈ Γ → forces f v x φ

-- Global semantic consequence
def global_sem_csq (Γ : ctx) (φ : form) :=
  ∀ f v, forces_ctx f v Γ → ∀ x, forces f v x φ

lemma not_forces_imp :  ∀ f v x φ, 
  (¬(forces f v x φ)) ↔ (forces f v x (¬φ)) :=
begin
intros f v x φ, split, 
{intros h1 h2, exact h1 h2},
{intros h1 h2, specialize h1 h2, exact h1}
end

lemma forces_exists {f : frame} {v : nat → f.states → Prop} {x : f.states} {φ : form} :
  forces f v x (◇φ) ↔ ∃ y : f.states, (f.rel x y ∧ forces f v y φ) :=
begin
simp at *,
split,
intro h1,
rw forces at h1, rw forces at h1,
have h2 := not_or_of_imp h1,
clear h1, cases h2, push_neg at h2,
cases h2 with y h2, cases h2 with h2 h3,
existsi (y : f.states), split, exact h2,
have h4 := (not_forces_imp f v y (¬φ)).mp h3,
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