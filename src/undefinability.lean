-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import language syntax semantics data.set.basic paths definability

open form
local attribute [instance] classical.prop_decidable



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
{intro y, split, repeat {intro h1, exact h1}}, 
{intro y, split, repeat {intro h1, exact h1}},
{rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, rename φ_φ φ, 
rename φ_ψ ψ, intro y, specialize ih_φ y, specialize ih_ψ y, 
cases ih_φ, cases ih_ψ, split, intro h1, cases h1, split, 
exact ih_φ_mp h1_left, exact ih_ψ_mp h1_right, intro h1, 
cases h1, split, exact ih_φ_mpr h1_left, exact ih_ψ_mpr h1_right}, 
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, 
rename φ_ih_ψ ih_ψ, intro y, specialize ih_φ y, specialize ih_ψ y, 
cases ih_φ, cases ih_ψ, split, intros h1 h2, have h3 := ih_φ_mpr h2, 
have h4 := h1 h3, exact ih_ψ_mp h4, intros h1 h2, 
have h3 := ih_φ_mp h2, have h4 := h1 h3, exact ih_ψ_mpr h4},
{rename φ_φ φ, intro y, split, {intros h1 z h2, specialize φ_ih z,
cases φ_ih, specialize h1 z.val, have h3 := h1 h2, exact φ_ih_mp h3}, 
{intro h1, intros z h2, 
have h3 := reach_right x y.val z f.rel (and.intro y.property h2),
specialize φ_ih ⟨z, h3⟩, cases φ_ih, specialize h1 ⟨z, h3⟩, 
have h4 := h1 h2, exact φ_ih_mpr h4}}
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
{intros x1 x2 h1, split, intro h2, exact h2, intro h2, exact h2}, 
{intros x1 x2 h1, specialize h x1 x2 h1, cases h, 
specialize h_left φ, cases h_left, split, intro h2, 
exact h_left_mp h2, intro h2, exact h_left_mpr h2}, 
{intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1, 
cases φ_ih_φ, cases φ_ih_ψ, split, intro h2, cases h2, split, 
exact φ_ih_φ_mp h2_left, exact φ_ih_ψ_mp h2_right, intro h2, 
cases h2, split, exact φ_ih_φ_mpr h2_left, exact φ_ih_ψ_mpr h2_right}, 
{intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1,
cases φ_ih_φ, cases φ_ih_ψ, split, intros h2 h3, have h4 := φ_ih_φ_mpr h3,
have h5 := h2 h4, exact φ_ih_ψ_mp h5, intros h2 h3, have h4 := φ_ih_φ_mp h3,
have h5 := h2 h4, exact φ_ih_ψ_mpr h5},
{rename φ_φ φ, intros x1 x2 h1, specialize h x1 x2 h1, cases h with h4 h5,
cases h5 with h5 h6, split,
{intros h2 y2 h3, specialize h6 y2 h3, cases h6 with y1 h6, 
cases h6 with h6 h7, specialize h2 y1 h6, specialize φ_ih y1 y2 h7, 
cases φ_ih, exact φ_ih_mp h2},
{intros h2 y1 h3, specialize h5 y1 h3, cases h5 with y2 h5, 
cases h5 with h5 h7, specialize h2 y2 h5, specialize φ_ih y1 y2 h7, 
cases φ_ih, exact φ_ih_mpr h2}}
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
intros φ h1, rw f_valid at *, rw not_forall at *, cases h1 with v2 h1,
rw not_forall at h1, cases h1 with y h1,
let v1 := (λ n x, v2 n (g x)), use v1, rw not_forall,
cases h with hl hr, specialize hl y, cases hl with x hl, 
existsi (x : f1.states), have h3 := invariance_bisim v1 v2 (λ x y, g x = y),
have h4 : is_bisimulation v1 v2 (λ (x : f1.states) (y : f2.states), g x = y), 
{intros x1 x2 h2, split,
{intro n, split, intro h, subst h2, apply h, intro h, subst h2, apply h},
specialize hr x1, cases hr, split,
have h5 : forth (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2, 
from eq.subst h2 hr_left, exact h5, 
have h5 : back (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2,
from eq.subst h2 hr_right, exact h5},
specialize h3 h4 x y hl, intro h2, apply h1,
rw set.subset.antisymm_iff at h3, cases h3, 
rw set.subset_def at h3_left,
specialize h3_left φ h2, exact h3_left,
end

lemma invariance_pull_back (F : set (frame)) {f1 f2 : frame} 
  (h1 : f1 ∈ F) (h2 : f2 ∉ F) : 
  (∃ g : f1.states → f2.states, is_surjbddmorphism g) → undefinable F :=
begin
intro h, cases h with g h,
intro φ, by_contradiction h3, 
have h4 := h3 f1, specialize h3 f2, 
rw ←not_iff_not at h3, cases h3,
have h5 := h3_mp h2, 
cases h4, have h7 := h4_mp h1, 
have h8 := pull_back g h φ h5, 
exact h8 h7
end