import data.set.basic

---------------------- Syntax ----------------------

-- Def 2.1, pg 12
inductive form (agents : Type) (B : list agents) : Type
  | bot  : form
  | var  (n : nat) : form 
  | and  (φ ψ : form) : form
  | impl (φ ψ : form) : form
  | box  (a : agents) (φ : form) : form
  | every (B : list agents) (φ : form) : form
  | comm (B : list agents) (φ : form)  : form

open form

-- Notation
local notation `⊥`:80   := form.bot
local prefix `p`:80     := form.var _
infix `&`:80      := form.and
infix `⊃`         := form.impl
notation `¬`:80 φ := form.impl φ (form.bot _)
notation `⊤`:80   := ¬ ⊥
notation ψ `∨` φ  := ¬(¬ψ & ¬φ)
notation `K`:80   := form.box -- "x knows that φ"
notation `C`:80   := λ φ, ¬(K (¬φ)) -- "φ is consistent with x's knowledge"


variables {agents : Type} {B : list agents} {states : Type}

-- Proof system, pg. 26
inductive prfS5C (a : agents) : form agents B → Prop 
-- axioms:
| pl1 (φ ψ)     : prfS5C (φ ⊃ (ψ ⊃ φ))
| pl2 (φ ψ χ)   : prfS5C ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 (φ ψ)     : prfS5C (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| k_dist (φ ψ)  : prfS5C ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| t (φ)         : prfS5C ((K a φ) ⊃ φ)
| pos_int (φ)   : prfS5C ((K a φ) ⊃ (K a (K a φ)))
| neg_int (φ)   : prfS5C ((¬ K a φ) ⊃ (K a (¬ K a φ)))
| cb_dist (φ ψ) : prfS5C ((comm B (φ ⊃ ψ)) ⊃ ((comm B φ) ⊃ (comm B ψ)))
| mix (φ)       : prfS5C ((comm B φ) ⊃ (φ & (every B (comm B φ))))
| ind (φ)       : prfS5C ((comm B (φ ⊃ (every B φ))) ⊃ (φ ⊃ (comm B φ)))
-- rules of inference:
| mp (φ ψ) (hpq: prfS5C (φ ⊃ ψ)) (hp : prfS5C φ) : prfS5C ψ
| nec (φ) (hp: prfS5C φ) : prfS5C (K a φ)
| nec_cb (φ) (hp : prfS5C φ) : prfS5C (comm B φ)
    
#print prfS5C



---------------------- Semantics ----------------------

structure frame (agents : Type) :=
(states : Type)
(h : inhabited states)
(rel : agents → states → states → Prop)
#print inhabited

-- group semantics


-- definition of forces
def forces (f : frame agents) (a : agents) (B : list agents) (v : nat → f.states → Prop) : 
  f.states → form agents B → Prop
  | s (bot a)    := false
  | s (var a n)  := v n s
  | s (and φ ψ)  := (forces s φ) ∧ (forces s ψ)
  | s (impl φ ψ) := (forces s φ) → (forces s ψ)
  | s (form.box a φ)   := ∀ s', f.rel a s s' → forces s' φ
  --| s (form.every B φ) := ∀ s', f.rel a s s' → forces s' φ
  --| s (form.comm B φ)  := sorry

-- valid in a model m
def m_valid (φ : form agents B) (a : agents)
  (f : frame agents) (v : nat → f.states → Prop) := 
  ∀ x : f.states, forces f a v x φ

-- valid in a frame f
def f_valid (φ : form agents B) (a : agents) (f: frame agents) := 
  ∀ x v, forces f a v x φ

-- valid in a class of frames F
def F_valid (φ : form agents B) (a : agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ x, ∀ v, forces f a v x φ

-- universally valid (valid in all frames)
def u_valid (φ : form agents B) (a : agents) := 
  ∀ f : frame agents, ∀ x, ∀ v, forces f a v x φ


















---------------------- Come Back to this Stuff Later ----------------------

/-
notation (F, v) `⊨` φ := m_valid φ a F v
notation F `⊨` φ := f_valid φ a F
notation F' `⊨` φ := f_valid φ a F'
notation `⊨` φ := u_valid φ a
-/

-- Def 2.6, pg 17
/-
structure model (agents : Type) (states : Type) extends frame agents states :=
(val : nat → set states)


-- Def 2.7, pg 18
def forces (M : model agents states) (a : agents) : states → form agents → Prop
  | s (bot a)    := false
  | s (var a n)  := M.val n s
  | s (and φ ψ)  := (forces s φ) ∧ (forces s ψ)
  | s (impl φ ψ) := ¬(forces s φ) ∨ (forces s ψ)
  | s (box a φ)  := ∀ s', M.rel a s s' → forces s' φ
  | s (dia a φ)  := ∃ s', M.rel a s s' → forces s' φ

#check @forces
-/


-- General knowledge, pg 12, "Everybody in B knows φ" 
/-def EB : form agents → list agents → form agents
  | φ [] := φ ∨ ¬φ
  | φ (b::bs) := form.and (K b φ) (EB φ bs)

#check EB
-/

  --| C (B : set agents) (φ : form) : form

/-
-- Define a context
def gamma (agents: Type) : Type := set (form agents)
notation `Γ` := gamma
notation Γ `∪` φ :=set.insert φ Γ
-/
