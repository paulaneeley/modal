-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import ..languageDEL data.set.basic ..semantics.semanticsDEL
variables {agents : Type}



---------------------- Soundness ----------------------


theorem soundnessPA {Γ : ctx agents} {φ : formPA agents} : 
  prfPA Γ φ → (∀ ψ ∈ Γ, F_valid ψ equiv_class) → F_valid φ equiv_class :=
begin
intros h1 h2 f h3 v, induction h1,
{intro x, specialize h2 h1_φ h1_h, rw F_valid at h2, specialize h2 f h3 v x, exact h2},
{intros x h4 h5, exact h4},
{intros x h4 h5 h6, exact (h4 h6) (h5 h6)},
{intros x h4 h5, exact and.intro h4 h5}, 
{intros x h4, exact h4.left}, 
{intros x h4, exact h4.right}, 
{intros x h4, apply h4, intro h5, exact h5},
{intros x h3 h4, simp [forces] at *, intros x' h5, 
exact (h3 x' h5) (h4 x' h5)},
{intros x h1, apply h1, specialize h3 h1_a, exact h3.left x}, 
{intros x h1 y h4 z h5, specialize h1 z, apply h1,
specialize h3 h1_a, cases h3 with h3l h3r, cases h3r with h3r h3rr,
specialize h3rr h4 h5, exact h3rr}, 
{intros x h1 y h6 h4, apply h1, intros z h5, specialize h4 z, apply h4, 
specialize h3 h1_a, cases h3 with h3l h3r, cases h3r with h3r h3rr, 
exact h3rr (h3r h6) h5},
{intro x, specialize h1_ih_hp h2 x, specialize h1_ih_hpq h2 x h1_ih_hp, 
exact h1_ih_hpq},
{intros x y h1, exact h1_ih_hp h2 y}, 
{intros x, split, repeat {intros h1 h4, apply h1 h4}}, 
{intros x, split, intros h1 h4 h5, exact (h1 h4) (h5 h4),
intros h1 h4 h5, apply h1 h4, intro h6, exact h5}, 
{intros x, split, intro h1, split, intro h4,
specialize h1 h4, exact h1.left,
intro h4, specialize h1 h4, exact h1.right, 
intros h1 h4, split, exact h1.left h4, exact h1.right h4}, 
{rename h1_a a, rename h1_ψ ψ, rename h1_φ φ,
intros s, rw forces, split,
intro h1, intro h4, specialize h1 h4,
rw forces at h1,
rw forces,
intro y,
intro h5,
rw forces,
intro h6,
sorry,
sorry,
}, 
{intros x, rw forces, split, rw forces, intro h1,
rw forces, intro h4, rw forces at h1, rw forces at h4,
cases h4, specialize h1 h4_left, rw forces at h4_right,
specialize h4_right h4_left, sorry, sorry}
end
