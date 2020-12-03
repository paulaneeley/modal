-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.semantics.semanticsDEL 
import data.set.basic data.equiv.basic
variable {agents : Type}
local attribute [instance] classical.prop_decidable


---------------------- Facts about Announcements ----------------------

-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : formPA agents) : 
  F_validPA ((¬(U φ (¬ψ))) ⊃ (U φ ψ)) equiv_class :=
begin
rw F_validPA, intros f h v x,
rw forcesPA, intro h1,
rw forces_update_dual at h1,
cases h1 with Ph1 h1, intro h, exact h1
end

-- Proposition 4.11, pg. 77
lemma partial_announce (φ ψ : formPA agents) : 
  ¬ (F_validPA ¬(U φ ¬⊥)) equiv_class :=
begin
rw F_validPA, 
push_neg,
let f : frame agents := { states := nat,
  h := ⟨0⟩,
  rel := λ a, λ x y : nat, x = y }, 
use f, split, intro a,
split, intro x, 
exact eq.refl x,
split, intros x y h,
exact eq.symm h,
intros x y z h1 h2, 
exact eq.trans h1 h2,
let v : nat → f.states → Prop := λ n x, false,
use v,
let x : f.states := 42,
use x, rw forcesPA, rw not_imp,
split, intro h, intro h1, exact h1,
rw forcesPA, trivial
end

--prop 4.22
lemma public_annouce_var (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
  forcesPA f v x (U φ p n) ↔ forcesPA f v x (φ ⊃ (p n)) :=
begin
split, repeat {intros h1 h2, exact h1 h2},
end

lemma public_annouce_conj (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) :
  forcesPA f v x (U φ (ψ & χ)) ↔ forcesPA f v x ((U φ ψ) & (U φ χ)) :=
begin
split,
intro h1,
split,
intro h2, specialize h1 h2,
exact h1.left,
intro h2, specialize h1 h2,
exact h1.right, 
intros h1 h2,
split,
exact h1.left h2,
exact h1.right h2,
end

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) : 
  forcesPA f v x (U φ (¬ψ)) ↔ forcesPA f v x (φ ⊃ ¬(U φ ψ))  :=
begin
split,
intros h1 h2 h3, specialize h1 h2,
specialize h3 h2, rw ←not_forces_impPA at h1,
exact absurd h3 h1,
intros h1, rw forcesPA at h1, rw imp_iff_not_or at h1,
cases h1,
intro h2, exact absurd h2 h1,
intros h h2, apply h1, intro h3, exact h2
end

-- Proposition 4.18, pg. 79
lemma public_announce_know (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) (a : agents) :
  forcesPA f v s (U φ (K a ψ)) ↔ forcesPA f v s (φ ⊃ (K a (U φ ψ))) :=
begin
split,
intros h1 h2 t hrel h3,
rw forcesPA at h1,
specialize h1 h2,
rw forcesPA at h1,
specialize h1 ⟨t, h3⟩,
specialize h1 hrel,
exact h1,
intro h1,
intro h2,
rw forcesPA,
rintro ⟨t, h3⟩,
intro hrel,
exact h1 h2 t hrel h3,
end

namespace compositionPA

-- -- The theory of x in m
-- def theory_at (f : frame agents) (v : nat → f.states → Prop) (x : f.states) : 
--   set (formPA agents) := { φ : formPA agents | forcesPA f v x φ}

-- -- Invariance under bisimulation
-- def base {f1 f2 : frame agents} (v1 : nat → f1.states → Prop) 
--   (v2 : nat → f2.states → Prop) (x1 : f1.states) (x2 : f2.states) := 
--   ∀ n, v1 n x1 ↔ v2 n x2

-- def forth {f1 f2 : frame agents} (bisim : f1.states → f2.states → Prop) 
--   (x1 : f1.states) (x2 : f2.states) := 
--   ∀ a, ∀ y1, f1.rel a x1 y1 → (∃ y2 : f2.states, f2.rel a x2 y2 ∧ bisim y1 y2)

-- def back {f1 f2 : frame agents} (bisim : f1.states → f2.states → Prop) 
--   (x1 : f1.states) (x2 : f2.states) := 
--   ∀ a, ∀ y2, f2.rel a x2 y2 → (∃ y1 : f1.states, f1.rel a x1 y1 ∧ bisim y1 y2)

-- -- Bisimulation between M1 = (f1,v1) and M2 = (f2,v2)
-- def is_bisimulation {f1 f2 : frame agents} (v1 : nat → f1.states → Prop) 
--   (v2 : nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) := ∀ x1 x2,
--   bisim x1 x2 → (base v1 v2 x1 x2 ∧ forth bisim x1 x2 ∧ back bisim x1 x2)

-- theorem invariance_bisim {f1 f2 : frame agents} {v1 : nat → f1.states → Prop}
--   {v2 : nat → f2.states → Prop} (bisim : f1.states → f2.states → Prop) 
--   (h : is_bisimulation v1 v2 bisim) (x1 : f1.states) (x2 : f2.states) : 
--   bisim x1 x2 → theory_at f1 v1 x1 = theory_at f2 v2 x2 :=
-- begin
-- intros h1, ext φ, revert x1 x2, induction φ,
-- {intros x1 x2 h1, split, intro h2, exact h2, intro h2, exact h2}, 
-- {intros x1 x2 h1, specialize h x1 x2 h1, cases h, 
-- specialize h_left φ, cases h_left, split, intro h2, 
-- exact h_left_mp h2, intro h2, exact h_left_mpr h2}, 
-- {intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1, 
-- cases φ_ih_φ, cases φ_ih_ψ, split, intro h2, cases h2, split, 
-- exact φ_ih_φ_mp h2_left, exact φ_ih_ψ_mp h2_right, intro h2, 
-- cases h2, split, exact φ_ih_φ_mpr h2_left, exact φ_ih_ψ_mpr h2_right}, 
-- {intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1,
-- cases φ_ih_φ, cases φ_ih_ψ, split, intros h2 h3, have h4 := φ_ih_φ_mpr h3,
-- have h5 := h2 h4, exact φ_ih_ψ_mp h5, intros h2 h3, have h4 := φ_ih_φ_mp h3,
-- have h5 := h2 h4, exact φ_ih_ψ_mpr h5},
-- {rename φ_φ φ, intros x1 x2 h1, specialize h x1 x2 h1, cases h with h4 h5,
-- cases h5 with h5 h6, split,
-- {intros h2 y2 h3, specialize h6 φ_a y2 h3, cases h6 with y1 h6, 
-- cases h6 with h6 h7, specialize h2 y1 h6, specialize φ_ih y1 y2 h7, 
-- cases φ_ih, exact φ_ih_mp h2},
-- {intros h2 y1 h3, specialize h5 φ_a y1 h3, cases h5 with y2 h5, 
-- cases h5 with h5 h7, specialize h2 y2 h5, specialize φ_ih y1 y2 h7, 
-- cases φ_ih, exact φ_ih_mpr h2}},
-- {rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ,
-- intros x1 x2 h1, specialize h x1 x2 h1, cases h with h2 h3,
-- cases h3 with h3 h4, split,
-- {
--   intro h5,
--   intro h6,
--   rw theory_at at h5,
--   rw set.mem_set_of_eq at h5,
--   rw forcesPA at h5,
--   specialize ih_φ x1 x2 h1,
--   repeat {rw theory_at at ih_φ},
--   repeat {rw set.mem_set_of_eq at ih_φ},
--   have h7 := ih_φ.mpr h6,
--   specialize h5 h7,
--   specialize ih_ψ x1 x2 h1,
--   repeat {rw theory_at at ih_ψ},
--   repeat {rw set.mem_set_of_eq at ih_ψ},
--   have h8 : forcesPA f1 v1 x1 ψ, 
--   sorry,
--   have h9 := ih_ψ.mp h8,
--   sorry,
-- }, 
-- {
--   intro h5,
--   intro h6,
--   rw theory_at at h5,
--   rw set.mem_set_of_eq at h5,
--   rw forcesPA at h5,
--   specialize ih_φ x1 x2 h1,
--   repeat {rw theory_at at ih_φ},
--   repeat {rw set.mem_set_of_eq at ih_φ},
--   have h7 := ih_φ.mp h6,
--   specialize h5 h7,
--   specialize ih_ψ x1 x2 h1,
--   repeat {rw theory_at at ih_ψ},
--   repeat {rw set.mem_set_of_eq at ih_ψ},
--   have h8 : forcesPA f2 v2 x2 ψ, 
--   sorry,
--   have h9 := ih_ψ.mpr h8,
--   sorry,
-- }}
-- end

-- lemma comp_helper3 {f1 f2 : frame agents} {v1 : nat → f1.states → Prop} 
--   {v2 : nat → f2.states → Prop} {x1 : f1.states} {x2 : f2.states} {φ : formPA agents} :
--   forcesPA f1 v1 x1 φ → theory_at f1 v1 x1 = theory_at f2 v2 x2 → forcesPA f2 v2 x2 φ :=
-- begin
-- intros h1 h2,
-- repeat {rw theory_at at h2},
-- simp at *,
-- repeat {rw set_of at h2},
-- exact eq.subst h2 h1,
-- end

variables A A'     : Prop
variable  B        : A → Prop
variable  A''      : A' → Prop
variable  B'       : ∀ h : A', A'' h → Prop

lemma comp_helper1 (h : A ↔ ∃ h : A', A'' h) 
  (h' : ∀ (h1 : A) (h2 : A') (h3 : A'' h2), B h1 ↔ B' h2 h3) : 
  (∀ h1 : A, B h1) ↔ (∀ h2 h3, B' h2 h3) :=
begin
  split,
  { intros hh h2 h3, 
    have h1 : A := h.mpr ⟨h2, h3⟩,
    exact (h' h1 h2 h3).mp (hh h1) },
  intros hh h1,
  cases h.mp h1 with h2 h3,
  exact (h' h1 h2 h3).mpr (hh h2 h3)
end

lemma comp_helper2 (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) :
  forcesPA f v s (φ & U φ ψ) ↔ 
  (∃ h : forcesPA f v s φ, forcesPA (f.restrict 
  (λ y, forcesPA f v y φ) s h) (λ n u, v n u.val) ⟨s, h⟩ ψ) :=
begin
split,
intro h1,
cases h1 with h1 h2,
use h1, 
apply h2,
intro h1,
cases h1 with h1 h2,
split,
exact h1,
intro h3,
exact h2,
end

-- lemmas from 12/02/2020 meeting start here --

def is_modal_iso (f1 f2 : frame agents) (v1 : nat → f1.states → Prop)
  (v2 : nat → f2.states → Prop) (F : f1.states ≃ f2.states) := 
  ∀ x x' : f1.states, ∀ a : agents, (f1.rel a x x' ↔ f2.rel a (F x) (F x'))

lemma update_iso {f1 f2 : frame agents} {v1 : nat → f1.states → Prop}
  {v2 : nat → f2.states → Prop} (F : f1.states ≃ f2.states) :
  is_modal_iso f1 f2 v1 v2 F → ∀ φ : formPA agents, ∀ x : f1.states,
  ∀ h : forcesPA f1 v1 x φ, ∀ h' : forcesPA f2 v2 (F x) φ, 
  ∃ F' : (f1.restrict (λ y, forcesPA f1 v1 y φ) x h).states
  ≃ (f2.restrict (λ y, forcesPA f2 v2 y φ) (F x) h').states,
  is_modal_iso (f1.restrict (λ y, forcesPA f1 v1 y φ) x h) 
  (f2.restrict (λ y, forcesPA f2 v2 y φ) (F x) h') (λ n u, v1 n u.val) (λ n u, v2 n u.val) F' :=
begin
sorry
end

lemma comp_helper4 {f1 f2 : frame agents} {v1 : nat → f1.states → Prop} 
  {v2 : nat → f2.states → Prop} (F : f1.states ≃ f2.states) :
  (is_modal_iso f1 f2 v1 v2 F ∧ ∀ n : nat, ∀ x : f1.states, v1 n x = v2 n (F x)) → ∀ s1 : f1.states, 
  ∀ φ : formPA agents, forcesPA f1 v1 s1 φ ↔ forcesPA f2 v2 (F s1) φ :=
begin
intro h1,
cases h1 with h1 h2,
intros x1 φ, induction φ generalizing x1,
split,
repeat {intro h3,
exact h3},
split,
repeat {intro h3,
rename φ n,
specialize h2 n x1,
rw forcesPA at *,
convert h3},
exact eq.symm h2,
repeat {rename φ_φ φ}, 
repeat {rename φ_ψ ψ},
repeat {rename φ_ih_φ φ_ih},
repeat {rename φ_ih_ψ ψ_ih},
repeat {rename φ_a a},
split,
repeat {intro h3,
rw forcesPA at *,
cases h3 with h3 h4,
split},
exact (φ_ih x1).mp h3,
exact (ψ_ih x1).mp h4,
exact (φ_ih x1).mpr h3,
exact (ψ_ih x1).mpr h4,
split,
repeat {intros h3 h4},
exact (ψ_ih x1).mp (h3 ((φ_ih x1).mpr h4)),
exact (ψ_ih x1).mpr (h3 ((φ_ih x1).mp h4)),
split,
intros h3 y1 h4,
rw is_modal_iso at h1,
specialize h3 (F.inv_fun y1),
specialize φ_ih (F.inv_fun y1),
specialize h1 x1 (F.inv_fun y1) a,
simp at *,
exact φ_ih.mp (h3 (h1.mpr h4)),
intros h3 x2 h4,
rw is_modal_iso at h1,
specialize h1 x1 x2 a,
specialize φ_ih x2,
rw forcesPA at h3,
specialize h3 (F.to_fun x2),
simp at *,
exact φ_ih.mpr (h3 (h1.mp h4)),
split,
intros h3 h4,
specialize φ_ih x1,
have h5 := update_iso F h1 φ x1 (φ_ih.mpr h4) h4,
cases h5 with F' h5,
rw forcesPA at h3,
specialize h3 (φ_ih.mpr h4),
repeat {sorry}
end


-- Proposition 4.17, pg. 78
lemma public_announce_comp (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) :
  forcesPA f v s (U (φ & U φ ψ) χ) ↔ forcesPA f v s (U φ (U ψ χ)) :=
begin
apply comp_helper1,
apply comp_helper2,
intros h1 h2 h3,
split,
intro h4,
--have h5 := comp_helper4,
repeat {sorry}
end

end compositionPA

