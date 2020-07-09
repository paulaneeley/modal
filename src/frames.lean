import data.set.basic ..my_new_lean_stuff.paths


---------------------- Syntax ----------------------


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


---------------------- Semantics ----------------------


structure frame (agents : Type) :=
(states : Type)
(h : inhabited states)
(rel : agents → states → states → Prop)

variables {agents : Type} {states : Type}

-- definition of forces
def forces (f : frame agents) (a : agents) (v : nat → f.states → Prop) : 
  f.states → form agents → Prop
  | s (bot a)    := false
  | s (var a n)  := v n s
  | s (and φ ψ)  := (forces s φ) ∧ (forces s ψ)
  | s (impl φ ψ) := (forces s φ) → (forces s ψ)
  | s (form.box _ φ)  := ∀ s', f.rel a s s' → forces s' φ

-- valid in a model m
def m_valid (φ : form agents) (a : agents)
  (f : frame agents) (v : nat → f.states → Prop) := 
  ∀ x, forces f a v x φ

-- valid in a frame f
def f_valid (φ : form agents) (a : agents) (f: frame agents) := 
  ∀ x v, forces f a v x φ

-- valid in a class of frames F
def F_valid (φ : form agents) (a : agents) (F : set (frame agents)) := 
  ∀ f ∈ F, ∀ x, ∀ v, forces f a v x φ

-- universally valid (valid in all frames)
def u_valid (φ : form agents) (a : agents) := 
  ∀ f : frame agents, ∀ x, ∀ v, forces f a v x φ


---------------------- Frame Definability ----------------------


-- φ defines F (a class of frames)
def defines (φ : form agents) (a : agents) (F : set (frame agents)) := 
  ∀ f, f ∈ F ↔ f_valid φ a f


---------------------- Definability Proofs (To do this summer) ----------------------

section
open classical
open set
local attribute [instance] prop_decidable

variable f : frame agents
variable a : agents

--def is_rfl {α : Type*} (R : α → α → Prop) := ∀ x, R x x
--#check is_rfl (F.rel a)
--#print reflexive

variables (agents states)
def refl_class : set (frame agents) := { f : frame agents | reflexive (f.rel a) }
def symm_class : set (frame agents) := { f : frame agents | symmetric (f.rel a) }
def trans_class : set (frame agents) := { f : frame agents | transitive (f.rel a) }
def equiv_class : set (frame agents) := { f : frame agents | equivalence (f.rel a) }
variables {agents states}


theorem ref_def : ∀ a : agents, 
  defines ((K a (p 0)) ⊃ (p 0)) a (refl_class agents a) :=
begin
intros a f,
split,
{intros h x v h1, 
apply h1 x, apply h x},
{intros h x, let v := λ n y, n = 0 ∧ f.rel a x y,
specialize h x v,
simp [forces, v] at h, exact h}
end

-- to do
theorem symm_def : ∀ a : agents, 
  defines ((p 0) ⊃ (K a (K a (p 0)))) a (symm_class agents a) :=
begin
sorry
end

end


---------------------- Frame Undefinability ----------------------


-- F (a class of frames) is undefinable
def undefinable (φ : form agents) (a : agents) (F : set (frame agents)) :=
  ∀ φ, ¬ defines φ a F

-- The theory of x in m
def theory_at (f : frame agents) (v : nat → f.states → Prop) (x : f.states) (a : agents) : 
  set (form agents) := { φ : form agents | forces f a v x φ}




-- Invariance under disjoint union
variables {α β : Type}
def frame.rel.dunion (r1 : α → α → Prop) (r2 : β → β → Prop) : 
  (sum α β) → (sum α β) → Prop
  | (sum.inl a1) (sum.inl a2) := r1 a1 a2
  | (sum.inr b1) (sum.inr b2) := r2 b1 b2
  | _ _                       := false

def val_dunion {f1 f2 : frame agents} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) : nat → (sum f1.states f2.states) → Prop
  | n (sum.inl x1) := v1 n x1
  | n (sum.inr x2) := v2 n x2

def frame.dunion (f1 : frame agents) (f2 : frame agents) : frame agents :=
{
  states := sum f1.states f2.states,
  h := ⟨sum.inl f1.h.default⟩, 
  rel := λ a : agents, frame.rel.dunion (f1.rel a) (f2.rel a)
}

theorem invariance_dunion : ∀ a : agents, ∀ f1 f2 x1 v1 v2, 
  theory_at f1 v1 x1 a = theory_at (f1.dunion f2) (val_dunion v1 v2) (sum.inl x1) a :=
begin
intros a f1 f2 x1 v1 v2, ext φ, revert x1, induction φ,
{intro x1, split, repeat {intro h, rw theory_at at *, exact h}},
{intro x1, split, repeat {intro h, rw theory_at at *, exact h}},
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, 
intro x1, split, intro h, split, specialize ih_φ x1, 
cases ih_φ, cases h, exact ih_φ_mp h_left,
specialize ih_ψ x1, cases ih_ψ, cases h, exact ih_ψ_mp h_right,
intro h, split, specialize ih_φ x1, cases ih_φ, cases h, exact ih_φ_mpr h_left,
specialize ih_ψ x1, cases ih_ψ, cases h, exact ih_ψ_mpr h_right},
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ,
intro x1, split, intro h, specialize ih_φ x1, cases ih_φ, specialize ih_ψ x1,
cases ih_ψ, intro h1, have h2 := ih_φ_mpr h1, have h3 := h h2, exact ih_ψ_mp h3, 
intro h, specialize ih_φ x1, specialize ih_ψ x1, cases ih_φ, cases ih_ψ, 
intro h1, have h2 := ih_φ_mp h1, have h3 := h h2, exact ih_ψ_mpr h3},
{rename φ_φ φ, intro x1, split, intros h s h1, cases s, specialize φ_ih s, 
cases φ_ih, specialize h s, have h2 := h h1, exact φ_ih_mp h2,
apply false.elim h1, intros h s h1, specialize φ_ih s, cases φ_ih,
specialize h (sum.inl s), have h2 := h h1, exact φ_ih_mpr h2}
end

#print subtype




-- Invariance under generated submodels
def frame.gen_subframe (a : agents) (f : frame agents) (x : f.states) : frame agents :=
{
  states := { y // reachable (f.rel a) x y},
  h := ⟨⟨x, ref_close x (f.rel a)⟩⟩,
  rel := λ a : agents, λ x1 x2, (f.rel a) x1.val x2.val
}

def val_gen_subframe (a : agents) (f : frame agents) (x : f.states)
  (v : nat → f.states → Prop) : nat → (frame.gen_subframe a f x).states → Prop :=
  λ n, λ y, v n y.val

theorem invariance_gen_submodel (f : frame agents) (x : f.states)
  (a : agents) (v : ℕ → f.states → Prop) (y : (frame.gen_subframe a f x).states) : 
  theory_at f v y.val a = theory_at (f.gen_subframe a x) (val_gen_subframe a f x v) y a :=
begin
ext φ, revert y, induction φ,
{intros y, split, repeat {intro h1, exact h1}}, 
{intros y, split, repeat {intro h1, exact h1}}, 
{rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, rename φ_φ φ, rename φ_ψ ψ,
intros y, specialize ih_φ y, specialize ih_ψ y, cases ih_φ, 
cases ih_ψ, split, intro h1, cases h1, split, exact ih_φ_mp h1_left, 
exact ih_ψ_mp h1_right, intro h1, cases h1, split, exact ih_φ_mpr h1_left, 
exact ih_ψ_mpr h1_right}, 
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ,
intros y, specialize ih_φ y, specialize ih_ψ y, 
cases ih_φ, cases ih_ψ, split, intros h1 h2, 
have h3 := ih_φ_mpr h2, have h4 := h1 h3, exact ih_ψ_mp h4, intros h1 h2, 
have h3 := ih_φ_mp h2, have h4 := h1 h3, exact ih_ψ_mpr h4},
{rename φ_φ φ, intros y, split, intro h1, repeat {rw theory_at at *},
repeat {rw set.mem_set_of_eq at *}, repeat {rw forces at *},
intros z h2, specialize h1 z.val,
specialize φ_ih z, have h3 := h1 h2, repeat {rw theory_at at *},
repeat {rw set.mem_set_of_eq at *}, repeat {rw forces at *},
--specialize h φ_a, 
have h3 := reach_right x y.val z.val (f.rel φ_a) (and.intro h h2), 
have h4 := h1 h2, sorry}
end



-- Invariance under bisimulation
def base {f1 f2 : frame agents} (x1 : f1.states) (v1 : nat → f1.states → Prop) 
  (x2 : f2.states) (v2 : nat → f2.states → Prop) := ∀ n, v1 n x1 ↔ v2 n x2

def forth {f1 f2 : frame agents} (a : agents) 
  (bisim : f1.states → f2.states → Prop) (x1 : f1.states) (x2 : f2.states)  := 
  ∀ y1, f1.rel a x1 y1 → (∃ y2 : f2.states, f2.rel a x2 y2 ∧ bisim y1 y2)

def back {f1 f2 : frame agents} (a : agents) 
  (bisim : f1.states → f2.states → Prop) (x1 : f1.states) (x2 : f2.states)  := 
  ∀ y2, f2.rel a x2 y2 → (∃ y1 : f1.states, f1.rel a x1 y1 ∧ bisim y1 y2)

-- Bisimulation between M1 = (f1,v1) and M2 = (f2,v2)
def is_bisimulation {f1 f2 : frame agents} (a : agents) 
  (v1 : nat → f1.states → Prop) (v2 : nat → f2.states → Prop) 
  (bisim : f1.states → f2.states → Prop) := ∀ x1 x2,
  bisim x1 x2 → (base x1 v1 x2 v2 ∧ forth a bisim x1 x2 ∧ back a bisim x1 x2)

theorem invariance_bisim {f1 f2 : frame agents} (a : agents) 
  (v1 : nat → f1.states → Prop) (v2 : nat → f2.states → Prop) 
  (bisim : f1.states → f2.states → Prop) (h : is_bisimulation a v1 v2 bisim) 
  (x1 : f1.states) (x2 : f2.states) : 
  bisim x1 x2 → theory_at f1 v1 x1 a = theory_at f2 v2 x2 a :=
begin
intro h1, ext φ, revert x1 x2, induction φ,
{sorry}, {sorry}, {sorry}, {sorry},
{rename φ_φ φ, intros x1 x2 h, split, intro h1, repeat {rw theory_at at *}, 
repeat {rw set.mem_set_of_eq at *}, repeat {rw forces at *}, intros y2' h3,
specialize h1 y1, rw bisimilar at h, cases h, have h2 := h_left h_right,
cases h2, cases h2_right, clear h_left, rw back at h2_right_right, sorry}
end













/-{intros x1 x2 h, repeat {rw [theory_at, set.mem_set_of_eq, forces] at *}},
{intros x1 x2 h, cases h, have h2 := h_left h_right, cases h2, specialize h2_left φ, exact h2_left},
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, intros x1 x2 h, cases ih_φ, cases ih_ψ,
split, intro h, cases h, split, exact ih_φ_mp h_left, exact ih_ψ_mp h_right,
intro h, cases h, split, exact ih_φ_mpr h_left, exact ih_ψ_mpr h_right}, 
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, cases ih_φ, cases ih_ψ,
split, intros h h2, have h3 := ih_φ_mpr h2, have h4 := h h3, exact ih_ψ_mp h4,
intros h h2, have h3 := ih_φ_mp h2, have h4 := h h3, exact ih_ψ_mpr h4}, 
-/