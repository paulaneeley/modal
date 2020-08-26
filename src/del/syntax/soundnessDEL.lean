-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL data.set.basic del.semantics.semanticsDEL del.announcements
variables {agents : Type}
local attribute [instance] classical.prop_decidable



---------------------- Soundness ----------------------


theorem soundnessPA {Γ : ctx agents} {φ : formPA agents} : 
  prfPA Γ φ → (∀ ψ ∈ Γ, F_valid ψ equiv_class) → F_valid φ equiv_class :=
begin
intros h1 h2 f h3 v, induction h1 with Γ φ h1 Γ φ ψ Γ φ ψ χ Γ φ ψ Γ φ ψ Γ φ ψ Γ φ ψ 
Γ φ Γ φ ψ Γ φ ψ a Γ φ a Γ φ a Γ φ a Γ φ ψ hpq hp ih_hpq ih_hp Γ φ a hp ih Γ φ Γ φ n
Γ φ ψ Γ φ ψ χ Γ φ ψ χ Γ φ ψ a Γ φ ψ χ,
{intro x, specialize h2 φ h1, rw F_valid at h2, specialize h2 f h3 v x, exact h2},
{intros x h4 h5, exact h4},
{intros x h4 h5 h6, exact (h4 h6) (h5 h6)},
{intros x h1 h2,
by_contradiction h3,
specialize h2 h3, specialize h1 h3, 
rw ← not_forces_imp at h1, exact h1 h2},
{intros x h4 h5, exact and.intro h4 h5}, 
{intros x h4, exact h4.left}, 
{intros x h4, exact h4.right}, 
{intros x h4, rw forces at h4, rw forces at h4,
rw forces at h4, rw imp_false at h4, rw imp_false at h4,
rw not_not at h4, exact h4},
{intros x h1 h2, rw forces at h1,
rw forces at h1, rw forces at h1, rw forces at h1,
rw imp_false at h1, rw imp_false at h1, rw not_imp_not at h1,
exact h1 h2}, 
{intros x h3 h4, simp [forces] at *, intros x' h5, 
exact (h3 x' h5) (h4 x' h5)},
{intros x h1, apply h1, specialize h3 a, exact h3.left x}, 
{intros x h1 y h4 z h5, specialize h1 z, apply h1,
specialize h3 a, cases h3 with h3l h3r, cases h3r with h3r h3rr,
specialize h3rr h4 h5, exact h3rr}, 
{intros x h1 y h6 h4, apply h1, intros z h5, specialize h4 z, apply h4, 
specialize h3 a, cases h3 with h3l h3r, cases h3r with h3r h3rr, 
exact h3rr (h3r h6) h5},
{intro x, specialize ih_hp h2 x, specialize ih_hpq h2 x ih_hp, 
exact ih_hpq},
{intros x y h1, exact ih h2 y}, 
{intros x, split, repeat {intros h1 h4, apply h1 h4}}, 
{intros x, split, repeat {intros h1 h4, apply h1 h4}}, 
{intros x, split, intros h1 h4 h5, exact (h1 h4) (h5 h4),
intros h1 h4 h5, apply h1 h4, intro h6, exact h5}, 
{intros x, split, intro h1, split, intro h4,
specialize h1 h4, exact h1.left,
intro h4, specialize h1 h4, exact h1.right, 
intros h1 h4, split, exact h1.left h4, exact h1.right h4}, 
{intros x, split, intros h1 h4 h5,
specialize h4 h5, specialize h1 h5, apply h1, exact h4,
intros h1 h4 h5, rw forces at h1, rw forces at h1,
specialize h1 (λ h4, h5), rw forces at h1, specialize h1 h4,
exact h1},
{intro x, split, rw forces, rw public_announce_know, intro h1, exact h1,
intro h1, rw public_announce_know, exact h1}, 
{intro x, split, intro h1, rw public_announce_comp,
exact h1, intro h1, rw public_announce_comp at h1, exact h1}
end
