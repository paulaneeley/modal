-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.semantics.semanticsDEL data.set.basic
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

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) : 
  F_validPA (U φ (¬ψ) ↔ (φ ⊃ ¬(U φ ψ))) equiv_class :=
begin
rw F_validPA, intros f h1 v x, split,
intros h1 h2 h3, specialize h1 h2,
specialize h3 h2, rw ←not_forces_impPA at h1,
exact absurd h3 h1,
intros h1, rw forcesPA at h1, rw imp_iff_not_or at h1,
cases h1,
intro h2, exact absurd h2 h1_1,
intros h h1, apply h1_1, intro h2, exact h1
end

-- Proposition 4.17, pg. 78
lemma public_announce_comp (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (s : f.states) :
  forcesPA f v s (U (φ & U φ ψ) χ) ↔ forcesPA f v s (U φ (U ψ χ)) :=
begin
split,
intro h1,
intro h2, 
sorry,
intro h1,
intro h2, 
sorry
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

--prop 4.22
lemma rwVar (φ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
  forcesPA f v x (U φ p n) ↔ forcesPA f v x (φ ⊃ (p n)) :=
begin
split, repeat {intros h1 h2, exact h1 h2},
end

lemma rwAnd (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (n : ℕ) :
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
