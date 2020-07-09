import data.set.basic

---------------------- Basic Language ----------------------

-- Def 2.1, pg 12
inductive form (agents : Type) : Type
  | bot  : form
  | var  (n : nat) : form 
  | and  (φ ψ : form) : form
  | impl (φ ψ : form) : form
  | box  (a : agents) (φ : form) : form

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


variables {agents : Type} {states : Type}


---------------------- Syntax ----------------------

-- Define a context
@[reducible] def ctx (agents: Type) : Type := set (form agents)
notation Γ `∪` φ := set.insert φ Γ

-- Proof system, pg. 26
inductive prfK (a : agents) : ctx agents → form agents → Prop 
| ax (Γ) (φ) (h : φ ∈ Γ) : prfK Γ φ
| pl1 (Γ) (φ ψ)          : prfK Γ (φ ⊃ (ψ ⊃ φ))
--| pl' (Γ) (φ ψ)        : prfK (Γ) ((φ & ψ) ⊃ φ)
| pl2 (Γ) (φ ψ χ)        : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 (Γ) (φ ψ)          : prfK Γ (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| kdist (Γ) (φ ψ)        : prfK Γ ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| mp (Γ) (φ ψ) 
  (hpq: prfK (Γ) (φ ⊃ ψ)) 
  (hp : prfK (Γ) φ)      : prfK Γ ψ
| nec (Γ) (φ) 
  (hp: prfK (Γ) φ)       : prfK Γ (K a φ)
    
#check @prfK

-- A basic object language proof (using pl', from class)

/-example (Γ : ctx agents) : ∀ a : agents, prfK a Γ (K a (p 0 & p 1) ⊃ (K a p 0)) :=
begin
intro a, 
have h1 : prfK a Γ (K a ((p 0 & p 1) ⊃ (p 0))), 
apply prfK.nec, {apply prfK.pl'}, 
have h2 : prfK a Γ ((K a ((p 0 & p 1) ⊃ (p 0))) ⊃ (K a (p 0 & p 1) ⊃ K a (p 0))),
apply prfK.kdist, 
have h3 : prfK a Γ (K a (p 0 & p 1) ⊃ K a (p 0)), 
{apply prfK.mp _ _ _ h2 h1,}, exact h3
end-/


-- Deduction theorem does not hold using current necessitation rule
/-theorem deduction (a : agents) (Γ : ctx agents) (φ ψ : form agents) : 
  prfK a (Γ ∪ φ) ψ → prfK a Γ (φ ⊃ ψ) :=
begin
sorry
end-/

---------------------- Semantics ----------------------


structure frame (agents : Type) :=
(states : Type)
(h : inhabited states)
(rel : agents → states → states → Prop)
#print inhabited

-- definition of forces
def forces (f : frame agents) (a : agents) (v : nat → f.states → Prop) : 
  f.states → form agents → Prop
  | s (bot a)    := false
  | s (var a n)  := v n s
  | s (and φ ψ)  := (forces s φ) ∧ (forces s ψ)
  | s (impl φ ψ) := (forces s φ) → (forces s ψ)
  | s (box a φ)  := ∀ s', f.rel a s s' → forces s' φ

-- φ is valid in a model M = (f,v)
def m_valid (φ : form agents) (f : frame agents) 
  (a : agents) (v : nat → f.states → Prop) := 
  ∀ x, forces f a v x φ

-- φ is valid in a frame f
def f_valid (φ : form agents) (f: frame agents) (a : agents)
  (v : nat → f.states → Prop) :=  ∀ x, forces f a v x φ

-- φ is valid in a class of frames F = set f
def F_valid (φ : form agents) (F : set (frame agents)) 
  (a : agents) := ∀ f ∈ F, ∀ x, ∀ v, forces f a v x φ

-- φ is universally valid (valid in all frames)
def u_valid (φ : form agents) (a : agents) := 
  ∀ f : frame agents, ∀ x, ∀ v, forces f a v x φ

-- φ is a global semantic consequence of Γ
def sem_csq (Γ : ctx agents) (φ : form agents) (a : agents) :=
  ∀ f, ∀ x, ∀ v, (∀ ψ ∈ Γ, m_valid ψ f a v) → forces f a v x φ


---------------------- Soundness Theorem ----------------------

open classical
local attribute [instance] prop_decidable


lemma not_forces_imp : ∀ a : agents, ∀ f v x φ, 
  (¬(forces f a v x φ)) ↔ (forces f a v x (¬φ)) :=
begin
intros a f v x φ, split, 
{intros h1 h2, exact h1 h2},
{intros h1 h2, specialize h1 h2, exact h1}
end


theorem soundness (a : agents) (Γ : ctx agents) 
  (φ : form agents) : prfK a Γ φ → sem_csq Γ φ a :=
begin
intro h,
induction h,

{intros f x v h, specialize h h_φ, have h1 := h h_h, 
rw m_valid at h1, specialize h1 x, exact h1},

{intros f x v h2 h3 h4, exact h3}, 

-- case for pl'
/-{intros f x v h2 h3,
simp [forces] at h3, 
exact h3.left},-/

{intros f x v h2 h3 h4 h5, apply h3, 
exact h5, apply h4, exact h5}, 

{intros f x v h1 h2 h3,
by_contradiction h4,
specialize h2 h4, specialize h3 h4, 
rw ← not_forces_imp at h2, exact h2 h3},

{intros f x v h1 h2 h3, simp [forces] at *, 
intros x' h4, specialize h3 x', specialize h2 x', specialize h3 h4,
specialize h2 h4, specialize h2 h3, exact h2}, 

{intros f x v h, 
specialize h_ih_hpq f x v,
specialize h_ih_hp f x v,
specialize h_ih_hp h,
specialize h_ih_hpq h,
exact h_ih_hpq h_ih_hp}, 

{intros f x v h1 y h2,
rw sem_csq at h_ih,
specialize h_ih f y v h1, 
exact h_ih},
end



variables (agents states)
variable a : agents
def tAxioms : ctx agents := { φ : form agents | ∃ ψ, φ = (K a ψ ⊃ ψ)}
def refl_class : set (frame agents) := { f : frame agents | reflexive (f.rel a) }

theorem Tsoundness (a : agents)
  (φ : form agents) : prfK a (tAxioms agents a) φ → F_valid φ (refl_class agents a) a :=
begin
intro h, have h1 := soundness _ _ _ h, intros f h2 x v,
apply h1, intros ψ, rintros ⟨θ, h3⟩, rw h3,  sorry
end


