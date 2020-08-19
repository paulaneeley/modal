-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import languageDEL semantics.semanticsDEL data.set.basic
variable {agents : Type}
local attribute [instance] classical.prop_decidable


---------------------- Facts about Announcements ----------------------

-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : formPA agents) : 
  F_valid ((~(U φ (~ψ))) ⊃ (U φ ψ)) equiv_class :=
begin
rw F_valid, intros f h v x,
rw forces, intro h1,
rw forces_exists at h1,
cases h1 with Ph1 h1, intro h, exact h1
end

-- Proposition 4.11, pg. 77
lemma partial_announce (φ ψ : formPA agents) : 
  ¬ (F_valid ~(U φ ~⊥)) equiv_class :=
begin
rw F_valid, rw not_forall, 
let f : frame agents := { states := nat,
  h := inhabited.mk 0,
  rel := λ a, λ x y : nat, x = y }, 
use f, rw not_imp, split, intro a,
split, intro x, 
exact eq.refl x,
split, intros x y h,
exact eq.symm h,
intros x y z h1 h2, 
exact eq.trans h1 h2,
rw not_forall,
let v : nat → f.states → Prop := λ n x, false,
use v, rw not_forall,
let x : f.states := 42,
use x, rw forces, rw not_imp,
split, intro h, intro h1, exact h1,
rw forces, trivial
end

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) : 
  F_valid (U φ (~ψ) ↔ (φ ⊃ ~(U φ ψ))) equiv_class :=
begin
rw F_valid, intros f h1 v x,
split,
intros h1 h2 h3, specialize h1 h2,
specialize h3 h2, rw ←not_forces_imp at h1,
exact absurd h3 h1,
intros h1, rw forces at h1, rw imp_iff_not_or at h1,
cases h1,
rw forces, intro h2, exact absurd h2 h1_1,
rw forces at h1_1, rw forces, intro h, rw forces at h1_1,
rw forces, intro h1, apply h1_1, intro h2, exact h1
end

-- Proposition 4.17, pg. 78
lemma public_announce_comp (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) :
  forces f v x (U (φ & U φ ψ) χ) ↔ forces f v x (U φ (U ψ χ)) :=
begin
sorry
end


lemma khelper (φ ψ : formPA agents) (f : frame agents) (v : nat → f.states → Prop) 
  (x : f.states) (a : agents) : (∀ (y : f.states), f.rel a x y → forces f v x φ → forces f v x (U φ ψ)) 
  ↔ (∀ (y : f.states), forces f v x φ ∧ f.rel a x y → forces f v x (U φ ψ)) :=
begin
split,
intros h1 y h2, specialize h1 y h2.right h2.left, exact h1,
intros h1 y h2 h3, specialize h1 y (and.intro h3 h2), exact h1,
end


-- Proposition 4.18, pg. 79
lemma public_announce_know (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) (a : agents) :
  forces f v s (U φ (K a ψ)) ↔ forces f v s (φ ⊃ (K a (U φ ψ))) :=
begin
split,
intro h1,
rw forces at h1,
rw forces, intro h2,
--specialize h1 h2, 
--rw forces at h1,
rw forces, intros t h3, rw forces, intro h4, 
specialize h1 h2,
rw forces at h1,
specialize h1 ⟨t, h4⟩, dsimp at *,
convert h1,
sorry, 
intro h1, rw forces at h1,
rw forces, intro h,
rw forces, specialize h1 h,
rw forces at h1, sorry,
end

--prop 4.22
lemma rwVar (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
  forces f v x (U φ p n) ↔ forces f v x (φ ⊃ (p n)) :=
begin
split, repeat {intros h1 h2, exact h1 h2},
end

lemma rwAnd (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
  forces f v x (U φ (ψ & χ)) ↔ forces f v x ((U φ ψ) & (U φ χ)) :=
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
