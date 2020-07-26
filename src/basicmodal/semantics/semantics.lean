
import language syntax.syntax

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

-- φ is valid in a class of frames F = set f
def F_valid (φ : form) (F : set (frame)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ

-- φ is universally valid (valid in all frames)
def u_valid (φ : form) := 
  ∀ f v x, forces f v x φ

-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctx (f : frame) (v : nat → f.states → Prop) 
  (x : f.states) (Γ : ctx) := ∀ φ, (φ ∈ Γ → forces f v x φ)

-- φ is a global semantic consequence of Γ
def sem_csq (Γ : ctx) (φ : form) :=
  ∀ f v x, (∀ ψ ∈ Γ, m_valid ψ f v) → forces f v x φ

-- I'm not sure which definition to use...
def sem_csq2 (Γ : ctx) (φ : form) :=
  ∀ f v x, (∀ y, forces_ctx f v y Γ) → forces f v x φ
