import data.set.basic

---------------------- Syntax ----------------------

-- Def 2.1, pg 12


inductive form (agents : Type) : Type
  | bot                 : form
  | var  (n : nat)      : form 
  | and  (φ ψ : form)   : form
  | impl (φ ψ : form)   : form
  | box  (a : agents) 
         (φ : form)     : form
  | update (φ ψ : form) : form
  | dual (φ ψ : form)   : form


open form

-- Notation
local notation `⊥`:80   := form.bot
local prefix `p`:80     := form.var _
infix `&`:80            := form.and
infix `⊃`               := form.impl
notation `~`:80 φ       := φ ⊃ (form.bot _)
notation `⊤`:80         := ~ (form.bot _)
notation ψ `∨` φ        := ~(~ψ & ~φ)
notation φ ↔ ψ          := (φ ⊃ ψ) & (ψ ⊃ φ)
notation `K`:80         := form.box -- "a knows that φ"
notation `C`:80         := λ φ a, ~(K a (~φ)) -- "φ is consistent with a's knowledge"
notation `U`:80         := form.update
notation `D`:80         := form.dual


variables {agents : Type} {states : Type}



---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx (agents: Type) : Type := set (form agents)
notation Γ `∪` φ := set.insert φ Γ

-- Proof system, pg. 26
inductive prfK : ctx agents → form agents → Prop 
| ax {Γ} {φ} 
 (h : φ ∈ Γ)             : prfK Γ φ
| pl1 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl4 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ φ)
| pl5 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ ψ)
| pl6 {Γ} {φ}            : prfK Γ (⊥ _ ⊃ φ)
| kdist {Γ} {φ ψ} {a}    : prfK Γ ((K a (φ ⊃ ψ)) ⊃ ((K a φ) ⊃ (K a ψ)))
| truth {Γ} {φ} {a}      : prfK Γ ((K a φ) ⊃ φ)
| posintro {Γ} {φ} {a}   : prfK Γ ((K a φ) ⊃ (K a (K a φ)))
| negintro {Γ} {φ} {a}   : prfK Γ (~(K a φ) ⊃ (K a ~(K a φ)))
| mp {Γ} {φ ψ} 
  (hpq: prfK Γ (φ ⊃ ψ)) 
  (hp : prfK Γ φ)        : prfK Γ ψ
| nec {Γ} {φ} {a}
  (hp: prfK Γ φ)         : prfK Γ φ → prfK Γ (K a φ)
| atomicperm {Γ} {φ} 
  {n}                    : prfK Γ ((U φ (p n)) ↔ (φ ⊃ (p n)))
| announceneg {Γ} {φ ψ}  : prfK Γ ((U φ (~ψ)) ↔ (φ ⊃ ~(U φ ψ)))
| announceconj {Γ} 
  {φ ψ χ}                : prfK Γ ((U φ (ψ & χ)) ↔ ((U φ ψ) & (U φ χ)))
| announceknow {Γ} 
  {φ ψ} {a}              : prfK Γ ((U φ (K a ψ)) ↔ (φ ⊃ (K a (U φ ψ))))
| announcecomp {Γ} 
  {φ ψ χ}                : prfK Γ ((U φ (U ψ χ)) ↔ (U (φ & (U φ ψ)) χ))




---------------------- Semantics ----------------------

structure frame (agents : Type) :=
(states : Type)
(h : inhabited states)
(rel : agents → states → states → Prop)
#print inhabited

def frame.restrict (f : frame agents) (P : f.states → Prop) (s : f.states) (Ps : P s) : frame agents :=
{
  states := { s' : f.states // P s' },
  h := ⟨⟨s, Ps⟩⟩,
  rel := λ a : agents, λ u v, f.rel a u.val v.val
}

-- definition of forces

def forces : ∀ f : frame agents, 
  (nat → f.states → Prop) → f.states → form agents → Prop
  | f v x (bot a)      := false
  | f v x (var a n)    := v n x
  | f v x (and φ ψ)    := (forces f v x φ) ∧ (forces f v x ψ)
  | f v x (impl φ ψ)   := (forces f v x φ) → (forces f v x ψ)
  | f v x (box a φ)    := ∀ y, f.rel a x y → forces f v y φ
  | f v x (update φ ψ) := ∀ h : forces f v x φ, 
      forces (f.restrict (λ y, forces f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ
  | f v x (dual φ ψ)   := ∃ h : forces f v x φ, 
      forces (f.restrict (λ y, forces f v y φ) x h) (λ n u, v n u.val) ⟨x, h⟩ ψ



-- φ is valid in a model M = (f,v)
def m_valid (φ : form agents) (f : frame agents) 
  (v : nat → f.states → Prop) := 
  ∀ x, forces f v x φ

-- valid in a frame f
def f_valid (φ : form agents) (f : frame agents) := 
  ∀ v x, forces f v x φ

-- φ is valid in a class of frames F = set f
def F_valid (φ : form agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ

-- φ is universally valid (valid in all frames)
def u_valid (φ : form agents) := 
  ∀ f v x, forces f v x φ


---------------------- Facts about Announcements ----------------------


-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : form agents) : 
  u_valid (form.dual φ ψ ⊃ U φ ψ) :=
begin
intros f v x h1, rw forces at *, 
cases h1 with Ph1 h1, intro h, exact h1
end

-- Proposition 4.11, pg. 77
/-
lemma partial_announce (φ ψ : form agents) : 
  ~ (u_valid (form.dual φ ⊤)) :=
begin
by_contradiction h, rw u_valid at h, sorry
end
-/

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : form agents) : 
  u_valid ((form.dual φ ~ψ ⊃ (φ ⊃ form.dual (~φ) ψ)) & ((φ ⊃ form.dual (~φ) ψ) ⊃ form.dual φ ~ψ)) :=
begin
intros f v x, split, rw forces, sorry, sorry
end



---------------------- Completeness by Translation ----------------------

-- Def 7.20, pg. 186, Translation function t

def translate : form agents → form agents
  | (⊥ _)          := ⊥ _
  | (p n)          := p n
  | (φ & ψ)        := (translate φ) & (translate ψ)
  | (~ φ)          := ~ (translate φ)
  | (K a φ)        := K a (translate φ)
  | (U φ (p n))    := translate ~(~φ & ~(p n))
  | (U φ (~ψ))     := translate (φ ⊃ ~ (U φ ψ))
  | (U φ (ψ & χ))  := translate ((U φ ψ) & (U φ χ))
  | (U φ (K a ψ))  := translate (φ ⊃ (K a (U φ ψ)))
  | (U φ (U ψ χ))  := translate (U (φ & (U φ ψ)) χ)










-- Def 7.21, pg. 187, Complexity function c

def complexity : form agents → ℕ
  | (⊥ _)     := 1
  | (p n)     := 1
  | (φ & ψ)   := 1 + max((complexity φ), (complexity ψ))
  | (φ ⊃ ψ)   := 1 + max((complexity φ), (complexity ψ))
  --| (~ φ)     := 1 + (complexity φ)
  | (K a φ)   := 1 + (complexity φ)
  --| (U φ ψ)   := (4 + (complexity φ)) * (complexity ψ)
  --| (D φ ψ)   := (4 + (complexity φ)) * (complexity ψ)

decidable_linear_order


-- Subformulas
def subformulas : form agents → set (form agents)
  | (⊥ a)    := {(⊥ a)}
  | (p n)    := {(p n)}
  | (~ φ)    := {(~φ)} ∪ (subformulas φ)
  | (φ & ψ)  := {(φ & ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (φ ⊃ ψ)  := {(φ ⊃ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (K a φ)  := {(K a φ)} ∪ (subformulas φ)
  | (U φ ψ)  := {(update φ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
  | (D φ ψ)  := {(dual φ ψ)} ∪ (subformulas φ) ∪ (subformulas ψ)
















