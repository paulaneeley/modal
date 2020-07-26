-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import languageDEL import semantics.semanticsDEL
variable {agents : Type}


---------------------- Facts about Announcements ----------------------

-- Proposition 4.10, pg. 77
lemma functional_announce (φ ψ : formPA agents) : 
  u_valid (formPA.dual φ ψ ⊃ U φ ψ) :=
begin
intros f v x h1, rw forces at *, 
cases h1 with Ph1 h1, intro h, exact h1
end

-- Proposition 4.11, pg. 77
lemma partial_announce (φ ψ : formPA agents) : 
  ¬ (u_valid (D φ (~⊥))) :=
begin
by_contradiction h, rw u_valid at h, sorry
end

-- Proposition 4.12, pg. 77
lemma public_announce_neg (φ ψ : formPA agents) : 
  u_valid ((D φ (~ψ) ⊃ (φ ⊃ D (~φ) ψ)) & 
  ((φ ⊃ D (~φ) ψ) ⊃ D φ (~ψ))) :=
begin
intros f v x, split, rw forces, sorry, sorry
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
