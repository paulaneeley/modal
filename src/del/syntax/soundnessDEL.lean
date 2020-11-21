-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL data.set.basic del.semantics.semanticsDEL del.announcements
variables {agents : Type}
local attribute [instance] classical.prop_decidable



---------------------- Soundness ----------------------

theorem soundnessS5 {Γ : ctx agents} {φ : form agents} : 
  prfS5 Γ φ → global_sem_csq Γ equiv_class φ :=
begin
intros h1 f h2 v h3 x, 
induction h1 generalizing x,
repeat {rename h1_Γ Γ}, 
repeat {rename h1_φ φ}, 
repeat {rename h1_h h1},
repeat {rename h1_ψ ψ},
repeat {rename h1_χ χ},
repeat {rename h1_a a},
repeat {rename h1_hp hp},
repeat {rename h1_hpq hpq},
repeat {rename h1_ih ih},
repeat {rename h1_ih_hp ih_hp},
repeat {rename h1_ih_hpq ih_hpq},
{specialize h3 φ x h1, exact h3},
{intros h4 h5, exact h4},
{intros h4 h5 h6, exact (h4 h6) (h5 h6)},
{intros h1 h4,
by_contradiction h5,
specialize h4 h5, specialize h1 h5, 
rw ← not_forces_imp at h1, exact h1 h4},
{intros h4 h5, exact and.intro h4 h5}, 
{intros h4, exact h4.left}, 
{intros h4, exact h4.right}, 
{intros h4, repeat {rw forces at h4}, 
repeat {rw imp_false at h4},
rw not_not at h4, exact h4},
{intros h1 h4,
repeat {rw forces at h1},
repeat {rw imp_false at h1},
rw not_imp_not at h1,
exact h1 h4}, 
{intros h3 h4, simp [forces] at *, intros x' h5, 
exact (h3 x' h5) (h4 x' h5)},
{intros h1, apply h1, specialize h2 a, exact h2.left x}, 
{intros h1 y h4 z h5, specialize h1 z, apply h1,
specialize h2 a, cases h2 with h2l h2r, cases h2r with h2r h2rr,
specialize h2rr h4 h5, exact h2rr}, 
{intros h1 y h5 h4, apply h1, intros z h6, specialize h4 z, apply h4, 
specialize h2 a, cases h2 with h2l h2r, cases h2r with h2r h2rr, 
exact h2rr (h2r h5) h6},
{specialize ih_hp h3 x, specialize ih_hpq h3 x ih_hp, 
exact ih_hpq},
{intros y h1, exact ih h3 y} 
end


theorem soundnessPA {Γ : ctxPA agents} {φ : formPA agents} : 
  prfPA Γ φ → global_sem_csqPA Γ equiv_class φ :=
begin
intros h1 f h2 v h3 x, 
induction h1 generalizing x,
repeat {rename h1_Γ Γ}, 
repeat {rename h1_φ φ}, 
repeat {rename h1_h h1},
repeat {rename h1_ψ ψ},
repeat {rename h1_χ χ},
repeat {rename h1_a a},
repeat {rename h1_hp hp},
repeat {rename h1_hpq hpq},
repeat {rename h1_ih ih},
repeat {rename h1_ih_hp ih_hp},
repeat {rename h1_ih_hpq ih_hpq},
{specialize h3 φ x h1, exact h3},
{intros h4 h5, exact h4},
{intros h4 h5 h6, exact (h4 h6) (h5 h6)},
{intros h1 h4,
by_contradiction h5,
specialize h4 h5, specialize h1 h5, 
rw ← not_forces_impPA at h1, exact h1 h4},
{intros h4 h5, exact and.intro h4 h5}, 
{intros h4, exact h4.left}, 
{intros h4, exact h4.right}, 
{intros h4, repeat {rw forcesPA at h4}, 
repeat {rw imp_false at h4},
rw not_not at h4, exact h4},
{intros h1 h4,
repeat {rw forcesPA at h1},
repeat {rw imp_false at h1},
rw not_imp_not at h1,
exact h1 h4}, 
{intros h3 h4, simp [forcesPA] at *, intros x' h5, 
exact (h3 x' h5) (h4 x' h5)},
{intros h1, apply h1, specialize h2 a, exact h2.left x}, 
{intros h1 y h4 z h5, specialize h1 z, apply h1,
specialize h2 a, cases h2 with h2l h2r, cases h2r with h2r h2rr,
specialize h2rr h4 h5, exact h2rr}, 
{intros h1 y h5 h4, apply h1, intros z h6, specialize h4 z, apply h4, 
specialize h2 a, cases h2 with h2l h2r, cases h2r with h2r h2rr, 
exact h2rr (h2r h5) h6},
{specialize ih_hp h3 x, specialize ih_hpq h3 x ih_hp, 
exact ih_hpq},
{intros y h1, exact ih h3 y},
{split, repeat {intros h1 h4, apply h1 h4}}, 
{split, repeat {intros h1 h4, apply h1 h4}}, 
{split, intros h1 h4 h5, exact (h1 h4) (h5 h4),
intros h1 h4 h5, apply h1 h4, intro h6, exact h5}, 
{split, intro h1, split, intro h4,
specialize h1 h4, exact h1.left,
intro h4, specialize h1 h4, exact h1.right, 
intros h1 h4, split, exact h1.left h4, exact h1.right h4}, 
{split, intros h1 h4 h5,
specialize h4 h5, specialize h1 h5, apply h1, exact h4,
intros h1 h4 h5, rw forcesPA at h1, rw forcesPA at h1,
specialize h1 (λ h4, h5), rw forcesPA at h1, specialize h1 h4,
exact h1},
{split, rw forcesPA, rw public_announce_know, intro h1, exact h1,
intro h1, rw public_announce_know, exact h1}, 
{split, intro h1, rw public_announce_comp,
exact h1, intro h1, rw public_announce_comp at h1, exact h1}
end

