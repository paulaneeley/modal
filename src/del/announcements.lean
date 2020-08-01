-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import languageDEL semantics.semanticsDEL data.set.basic
variable {agents : Type}
local attribute [instance] classical.prop_decidable


---------------------- Facts about Announcements ----------------------

example : ∃ n : ℕ, 2 + 2 = n :=
begin
  existsi 4,
  -- goal now 2 + 2 = 4
refl
end

-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : formPA agents) : 
  F_valid ((~(U φ (~ψ))) ⊃ (U φ ψ)) euclid_class :=
begin
rw F_valid, intros f h v x,
rw forces, intro h1,
rw forces_exists at h1,
cases h1 with Ph1 h1, intro h, exact h1
end

-- Proposition 4.11, pg. 77
lemma partial_announce (φ ψ : formPA agents) : 
  ¬ (F_valid ~(U φ ~⊥)) euclid_class :=
begin
sorry
end

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) : 
  F_valid ((~U φ ~(~ψ) ⊃ (φ ⊃ ~U (~φ) ~ψ)) & 
  ((φ ⊃ ~U (~φ) ~ψ) ⊃ (~U φ (~ψ)))) euclid_class :=
begin
sorry
end

-- Proposition 4.17, pg. 78
lemma public_announce_comp (φ ψ χ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) :
  forces f v x (U (φ & U φ ψ) χ) ↔ forces f v x (U φ (U ψ χ)) :=
begin
sorry
end

-- Proposition 4.18, pg. 79
lemma public_announce_know (φ ψ : formPA agents) (f : frame agents) 
  (v : nat → f.states → Prop) (x : f.states) (a : agents) :
  forces f v x (U φ (K a ψ)) ↔ forces f v x (φ ⊃ (K a (U φ ψ))) :=
begin
sorry
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
