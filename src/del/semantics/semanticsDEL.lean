-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL ..syntax.syntaxDEL
variable {agents : Type}
open formPA

---------------------- Semantics ----------------------

structure frame (agents : Type) :=
(states : Type)
(h : inhabited states)
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
  | f v x (dual φ ψ)   := ∃ h : forces f v x φ, 
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

-- φ is universally valid (valid in all frames)
def u_valid (φ : formPA agents) := 
  ∀ f v x, forces f v x φ
