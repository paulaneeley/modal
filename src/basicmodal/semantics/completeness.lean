import basicmodal.semantics.consistency basicmodal.syntax.soundness
local attribute [instance] classical.prop_decidable

open prfK
namespace canonical


def canonical (AX : ctx) [hax : sem_cons AX] : frame := 
{ 
  states := {xΓ : ctx // max_ax_consist AX xΓ},
  h := begin have h1 := max_ax_exists AX hax, choose Γ h1 using h1, exact ⟨⟨Γ, h1⟩⟩ end,
  rel := λ xΓ yΔ, ∀ φ : form, □φ ∈ xΓ.val → φ ∈ yΔ.val
}

def val_canonical (AX : ctx) [hax : sem_cons AX] : nat → (canonical AX).states → Prop :=
  λ n, λ xΓ : (canonical AX).states, (p n) ∈ xΓ.val

lemma existence (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) :
  ∀ φ, ◇φ ∈ xΓ.val → ∃ yΔ : (canonical AX).states, φ ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ :=
begin
intros φ h1,
let Γbox : ctx := {ψ : form | □ψ ∈ xΓ.val},
have h1 : ax_consist AX (Γbox ∪ {φ}), 
{by_contradiction h2, simp at h2,
have h3 := five AX Γbox φ h2,
cases h3 with L h3, cases h3 with h3 h4,
have h5 := cut fin_conj_boxn (mp kdist (nec h4)),
have h6 := exercise1,
specialize h6 xΓ.2,
have h7 : ∀ ψ ∈ (list.map □ L), ψ ∈ xΓ.1, 
intros ψ h8, simp at *, cases h8 with a h8,
cases h8 with h8l h8r, specialize h3 a h8l, 
subst h8r, exact h3,
specialize h6 h7 h5,
have h8 := (six AX xΓ.1 (max_imp_ax xΓ.2)).mp xΓ.2 (¬φ).box,
cases h8 with h8l h8r, simp at *, specialize h8r h6, 
exact absurd h1 h8r
},
have h2 := lindenbaum AX (Γbox ∪ {φ}) h1,
cases h2 with Δ h2, cases h2 with h2 h3,
let xΔ : (canonical AX).states := ⟨Δ, h2⟩,
existsi (xΔ : (canonical AX).states),
have h5 := set.union_subset_iff.mp h3,
cases h5, split, simp at h5_right, exact h5_right,
have h3 : ∀ φ : form, □φ ∈ xΓ.val → φ ∈ xΔ.val,
intros ψ h4, apply h5_left, exact h4,
exact h3
end

lemma truth (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) : 
  ∀ φ, forces (canonical AX) (val_canonical AX) xΓ φ ↔ (φ ∈ xΓ.val) :=
begin
intro φ, induction φ with n φ ψ ih_φ ih_ψ 
φ ψ ih_φ ih_ψ φ ih_φ generalizing xΓ,
split, intro h1, exact false.elim h1,
intro h1, rw forces, 
have h2 := xΓ.2,
rw max_ax_consist at h2, cases h2,
rw ax_consist at h2_left, specialize h2_left [⊥],
simp at *, specialize h2_left h1, 
rw fin_ax_consist at h2_left,
repeat {rw fin_conj at h2_left},
exact absurd not_contra h2_left,
repeat {rw forces, rw val_canonical},
split, intro h1, cases h1 with h1 h2,
specialize ih_φ xΓ, cases ih_φ,
specialize ih_ψ xΓ,
specialize ih_φ_mp h1, cases ih_ψ,
specialize ih_ψ_mp h2, 
exact max_conj_1 xΓ.2 (and.intro ih_φ_mp ih_ψ_mp), 
intro h1, split,
specialize ih_φ xΓ, cases ih_φ, 
apply ih_φ_mpr, exact max_conj_2 xΓ.2 h1,
specialize ih_ψ xΓ, cases ih_ψ, 
apply ih_ψ_mpr, exact max_conj_3 xΓ.2 h1,
split, 
intro h1, specialize ih_φ xΓ,
specialize ih_ψ xΓ, cases ih_φ, cases ih_ψ,
apply max_imp_1 xΓ.2,
intro h2, specialize ih_φ_mpr h2,
specialize h1 ih_φ_mpr, exact ih_ψ_mp h1,
intros h1 h2,
specialize ih_φ xΓ, cases ih_φ,
specialize ih_ψ xΓ, cases ih_ψ,
apply ih_ψ_mpr, specialize ih_φ_mp h2,
exact max_imp_2 xΓ.2 h1 ih_φ_mp,
split, intros h1, 
by_contradiction h2,
have h4 : ◇(¬φ) ∈ xΓ.val → ∃ yΔ : (canonical AX).states, 
  (¬φ) ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ,
from existence AX hax xΓ (¬φ),
have h5 := max_boxdn AX xΓ.1 xΓ.2 φ ((max_notiff AX xΓ.1 xΓ.2 φ.box).mp h2),
simp at *,
specialize h4 h5, cases h4 with xΔ h4, cases h4 with h4 h6,
have h7 := max_notiff AX xΔ.1 xΔ.2 φ,
cases h7 with h7l h7r,
specialize h7r h4, clear h7l h4 h5 h2,
specialize ih_φ xΔ, specialize h1 xΔ h6,
cases ih_φ, specialize ih_φ_mp h1,
exact absurd ih_φ_mp h7r,
intros h1 xΔ h2,
have h3 := h2 φ h1,
specialize ih_φ xΔ, cases ih_φ, 
apply ih_φ_mpr, exact h3,
end

lemma comphelper (AX : ctx) (φ : form) (hax : sem_cons AX) : 
  ¬ prfK AX φ → ax_consist AX {¬φ} :=
begin
intro h1, rw ax_consist, intros L h2,
rw fin_ax_consist, induction L, rw fin_conj, 
by_contradiction h3,
exact absurd (mp dne h3) (nprfalse AX hax), 
have h4 : (∀ ψ ∈ L_hd::L_tl, ψ = ¬φ) → prfK AX (¬fin_conj (L_hd::L_tl)) → prfK AX φ, 
from fin_conj_repeat hax,
simp at *, 
cases h2 with h2 h3,
specialize h4 h2, intro h6, apply h1, apply h4, 
exact h3,
exact h6
end 


theorem completeness (AX : ctx) (hax : sem_cons AX) (φ : form) : 
  global_sem_csq AX φ → prfK AX φ :=
begin
rw ←not_imp_not, intro h1,
have h2 : ax_consist AX {¬φ}, from comphelper AX φ hax h1,
have h3 : ∃ Γ', max_ax_consist AX Γ' ∧ {¬φ} ⊆ Γ', from lindenbaum AX {¬φ} h2,
cases h3 with Γ' h3, cases h3 with h3 h4, simp at *,
rw global_sem_csq, 
push_neg,
let f := canonical, use f AX,
let v := val_canonical, use v AX,
let xΓ' : (f AX).states := ⟨Γ', h3⟩, use xΓ',
split, rw forces_ctx,
intros ψ y h5, 
sorry,
have h5 : forces (f AX) (v AX) xΓ' (¬φ) ↔ ((¬φ) ∈ xΓ'.val), 
  from truth AX hax xΓ' ¬φ,
cases h5 with h5 h6,
have h7 : ¬forces (f AX) (v AX) xΓ' φ ↔ forces (f AX) (v AX) xΓ' ¬φ, 
  from not_forces_imp (f AX) (v AX) xΓ' φ,
cases h7 with h7 h8, apply h8, apply h6, simp at *, exact h4
end


theorem T_completeness (φ : form) : F_valid φ ref_class → prfK T_axioms φ :=
begin
intros h1,
have h2 : global_sem_csq T_axioms φ → prfK T_axioms φ, 
  from completeness T_axioms sem_consT φ,
apply h2, clear h2,
rw global_sem_csq, intros f v x h3,
rw F_valid at h1,
apply h1, 
sorry
end


theorem S4_completeness (φ : form) : F_valid φ ref_trans_class → prfK S4_axioms φ := sorry

theorem S5_completeness (φ : form) : F_valid φ equiv_class → prfK S5_axioms φ := sorry

end canonical











-- lemma completenesshelper {AX : ctx} {φ : form} {C : set (frame)} (hax : sem_cons AX) : 
--   F_valid φ C → (∀ ψ ∈ AX, F_valid ψ C) → prfK AX φ :=
-- begin
-- intros h1 h2,
-- have h3 : global_sem_csq AX φ → prfK AX φ, from completeness AX hax φ,
-- apply h3, clear h3,
-- end

-- intros h1,
-- have h2 : (∀ ψ ∈ T_axioms, F_valid ψ ref_class) → prfK T_axioms φ,
-- from completenesshelper sem_consT h1,
-- apply h2, clear h2,
-- intros ψ h2,
-- apply T_helper,
-- exact h2,
