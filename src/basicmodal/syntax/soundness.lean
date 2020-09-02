-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import basicmodal.language data.set.basic basicmodal.semantics.semantics 
import basicmodal.semantics.definability basicmodal.syntax.syntaxlemmas
local attribute [instance] classical.prop_decidable



---------------------- Soundness ----------------------


lemma not_forces_imp :  ∀ f v x φ, 
  (¬(forces f v x φ)) ↔ (forces f v x (¬φ)) :=
begin
intros f v x φ, split, 
{intros h1 h2, exact h1 h2},
{intros h1 h2, specialize h1 h2, exact h1}
end

theorem soundness (Γ : ctx) (φ : form) : prfK Γ φ → sem_csq Γ φ :=
begin
intro h,
induction h,
{intros f v x h, specialize h x, rw forces_ctx at h,
specialize h h_φ, have h1 := h h_h, 
exact h1},
{intros f v x h2 h3 h4, exact h3}, 
{intros f v x h2 h3 h4 h5, apply h3, 
exact h5, apply h4, exact h5}, 
{intros f x v h1 h2 h3,
by_contradiction h4,
specialize h2 h4, specialize h3 h4, 
rw ← not_forces_imp at h2, exact h2 h3},
{intros f v x h1 h2 h3, simp [forces] at *, 
exact and.intro h2 h3},
{intros f v x h1 h2, exact h2.left},
{intros f v x h1 h2, exact h2.right},
{intros f v x h1 h2 h3, rw forces at h2,
rw forces at h2, rw forces at h2, rw forces at h2,
rw imp_false at h2, rw imp_false at h2, rw not_imp_not at h2,
exact h2 h3}, 
{intros f v x h1 h2 h3, simp [forces] at *, 
intros x' h4, specialize h3 x' h4,
specialize h2 x' h4 h3, exact h2}, 
{intros f v x h, 
specialize h_ih_hpq f v x h,
specialize h_ih_hp f v x h,
exact h_ih_hpq h_ih_hp}, 
{intros f v x h1 y h2,
rw sem_csq at h_ih,
specialize h_ih f v y h1, 
exact h_ih},
end

theorem soundness2 (Γ : ctx) (φ : form) : ¬ sem_csq Γ φ → ¬ prfK Γ φ :=
begin
rw not_imp_not, exact soundness Γ φ
end


lemma hi {Γ : ctx} {φ : form} {C : set (frame)} : prfK Γ φ → (∀ ψ ∈ Γ, F_valid ψ C) → F_valid φ C :=
begin
intros h1 h2 f h3 v, induction h1,
{intro x, specialize h2 h1_φ h1_h, rw F_valid at h2, specialize h2 f h3 v x, exact h2},
{intros x h4 h5, exact h4},
{intros x h4 h5 h6, have h7 := h4 h6, have h8 := h5 h6, exact h7 h8},
{intros x h3 h4, by_contradiction h5, specialize h3 h5, specialize h4 h5, 
rw ← not_forces_imp at h3, exact h3 h4},
{intros x h4 h5, exact and.intro h4 h5}, 
{intros x h4, exact h4.left}, 
{intros x h4, exact h4.right}, 
{intros x h4 h5, rw forces at h4, rw forces at h4,
rw forces at h4, rw forces at h4, rw imp_false at h4,
rw imp_false at h4, rw not_imp_not at h4, exact h4 h5},
{intros x h3 h4, simp [forces] at *, intros x' h5, specialize h3 x' h5,
specialize h4 x' h5, exact h3 h4},
{intro x, specialize h1_ih_hp h2 x, specialize h1_ih_hpq h2 x h1_ih_hp, 
exact h1_ih_hpq},
{intros x y h3, apply h1_ih, exact h2}
end


lemma inclusion_valid {C C' : set (frame)} : ∀ ψ, C ⊆ C' → F_valid ψ C' → F_valid ψ C :=
begin
intros φ h1 h2 f h3 v x, 
have h4 := set.mem_of_subset_of_mem h1 h3,
specialize h2 f h4 v x, exact h2
end


def T_axioms : ctx := {φ : form | ∃ ψ, φ = (□ ψ ⊃ ψ)}
def S4_axioms : ctx := T_axioms ∪ {φ : form | ∃ ψ, φ = (□ ψ ⊃ □ (□ ψ))}
def S5_axioms : ctx := S4_axioms ∪ {φ : form | ∃ ψ, φ = (◇ ψ ⊃ □ (◇ ψ))}


lemma T_helper : ∀ φ ∈ T_axioms, F_valid φ ref_class :=
begin
intros φ h1 f h2 v x,
cases h1 with ψ h1, subst h1, 
apply ref_helper, exact h2
end

theorem T_soundness (φ : form) : prfK T_axioms φ → F_valid φ ref_class :=
begin
intro h, apply hi, apply h, apply T_helper 
end

lemma S4_helper : ∀ φ ∈ S4_axioms, F_valid φ ref_trans_class :=
begin
intros φ h1 f h2 v x,
cases h2 with h2l h2r, 
cases h1 with h1 h3, 
{apply T_helper, exact h1, exact h2l},
{cases h3 with ψ h3, subst h3, 
apply trans_helper, exact h2r}
end

theorem S4_soundness (φ : form) : prfK S4_axioms φ → F_valid φ ref_trans_class :=
begin
intro h, apply hi, apply h, apply S4_helper
end

lemma S5_helper : ∀ φ ∈ S5_axioms, F_valid φ equiv_class :=
begin
intros φ h1 f h2 v x,
cases h2 with h2l h2r, 
cases h2r with h2r h2rr,
cases h1 with h1 h3, 
{cases h1, apply T_helper, exact h1, 
exact h2l, cases h1 with ψ h1, subst h1, 
apply trans_helper, exact h2rr},
{cases h3 with ψ h3, dsimp at h3,
subst h3, apply euclid_helper, rw euclid_class,
rw set.mem_set_of_eq, rw euclidean,
intros x y z h1 h2,
rw symmetric at h2r,
specialize h2r h1, exact h2rr h2r h2}
end

theorem S5_soundness (φ : form) : prfK (S5_axioms) φ → F_valid φ (equiv_class) :=
begin
intro h, apply hi, apply h, apply S5_helper
end