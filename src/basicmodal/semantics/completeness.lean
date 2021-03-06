/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import basicmodal.semantics.consistency basicmodal.syntax.soundness
local attribute [instance] classical.prop_decidable

open prfK

---------------------- Canonical Model Construction ----------------------

namespace canonical


def canonical (AX : ctx) [hax : sem_cons AX] : frame := 
{ 
  states := {xΓ : ctx // max_ax_consist AX xΓ},
  h := 
  begin 
    have h1 := max_ax_exists AX hax, 
    choose Γ h1 using h1, 
    exact ⟨⟨Γ, h1⟩⟩ 
  end,
  rel := λ xΓ yΔ, ∀ φ : form, □φ ∈ xΓ.val → φ ∈ yΔ.val
}


def T_canonical  : frame := @canonical T_axioms sem_consT
def S4_canonical : frame := @canonical S4_axioms sem_consS4
def S5_canonical : frame := @canonical S5_axioms sem_consS5


def val_canonical (AX : ctx) [hax : sem_cons AX] : nat → (canonical AX).states → Prop :=
  λ n, λ xΓ : (canonical AX).states, (p n) ∈ xΓ.val


lemma existence (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) :
  ∀ φ, ◇φ ∈ xΓ.val ↔ ∃ yΔ : (canonical AX).states, φ ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ :=
begin
intro φ, split,
intro h1,
let Γbox : ctx := {ψ : form | □ψ ∈ xΓ.val},
have h1 : ax_consist AX (Γbox ∪ {φ}), 
{by_contradiction h2, simp at h2,
have h3 := five AX Γbox φ h2,
cases h3 with L h3, cases h3 with h3 h4,
have h5 := cut fin_conj_boxn (mp kdist (nec h4)),
have h6 := exercise1,
have h7 : ∀ ψ ∈ (list.map □ L), ψ ∈ xΓ.1, 
intros ψ h8, simp at *, cases h8 with a h8,
cases h8 with h8l h8r,
subst h8r, exact h3 a h8l,
specialize h6 xΓ.2 h7 h5,
have h8 := (six AX xΓ.1 (max_imp_ax xΓ.2)).mp xΓ.2 (¬φ).box,
cases h8 with h8l h8r, simp at *,
exact absurd h1 (h8r h6)
},
have h2 := lindenbaum AX (Γbox ∪ {φ}) h1,
cases h2 with Δ h2, cases h2 with h2 h3,
let xΔ : (canonical AX).states := ⟨Δ, h2⟩,
existsi (xΔ : (canonical AX).states),
have h5 := set.union_subset_iff.mp h3,
cases h5, split, simp at h5_right, exact h5_right,
have h3 : ∀ φ : form, □φ ∈ xΓ.val → φ ∈ xΔ.val,
intros ψ h4, apply h5_left, exact h4,
exact h3,
simp at *,
intros yΔ h1 h2,
by_contradiction h3,
have h4 := (max_notiff AX xΓ.1 xΓ.2 (◇φ)).mp h3,
have h5 := (max_dn AX xΓ.1 xΓ.2 (□¬φ)).mpr h4,
have h6 := (max_notiff AX yΔ.1 yΔ.2 φ).mpr (h2 (¬φ) h5),
exact absurd h1 h6
end


lemma truth (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) : 
  ∀ φ, forces (canonical AX) (val_canonical AX) xΓ φ ↔ (φ ∈ xΓ.val) :=
begin
intro φ, induction φ with n φ ψ ih_φ ih_ψ 
φ ψ ih_φ ih_ψ φ ih_φ generalizing xΓ,
split, intro h1, exact false.elim h1,
intro h1,
have h2 := xΓ.2,
cases h2,
specialize h2_left [⊥],
simp at *,
exact absurd not_contra (h2_left h1),
repeat {rw forces, rw val_canonical},
split, intro h1, cases h1 with h1 h2,
exact max_conj_1 xΓ.2 (and.intro ((ih_φ xΓ).mp h1) ((ih_ψ xΓ).mp h2)), 
intro h1, split,
apply (ih_φ xΓ).mpr, exact max_conj_2 xΓ.2 h1,
apply (ih_ψ xΓ).mpr, exact max_conj_3 xΓ.2 h1,
split, 
intro h1,
apply max_imp_1 xΓ.2,
intro h2,
exact (ih_ψ xΓ).mp (h1 ((ih_φ xΓ).mpr h2)),
intros h1 h2,
apply (ih_ψ xΓ).mpr,
exact max_imp_2 xΓ.2 h1 ((ih_φ xΓ).mp h2),
split, intros h1, 
by_contradiction h2,
have h4 := (existence AX hax xΓ (¬φ)).mp,
have h5 := max_boxdn AX xΓ.1 xΓ.2 φ ((max_notiff AX xΓ.1 xΓ.2 φ.box).mp h2),
cases h4 h5 with xΔ h4, cases h4 with h4 h6,
have h7 := max_notiff AX xΔ.1 xΔ.2 φ,
cases h7 with h7l h7r,
exact absurd ((ih_φ xΔ).mp (h1 xΔ h6)) (h7r h4),
intros h1 xΔ h2,
apply (ih_φ xΔ).mpr, exact h2 φ h1,
end


lemma comphelper (AX : ctx) (φ : form) (hax : sem_cons AX) : 
  ¬ prfK AX φ → ax_consist AX {¬φ} :=
begin
intro h1, intros L h2,
rw fin_ax_consist, induction L,
by_contradiction h3,
exact absurd (mp dne h3) (nprfalse AX hax), 
have h4 : (∀ ψ ∈ L_hd::L_tl, ψ = ¬φ) → prfK AX (¬fin_conj (L_hd::L_tl)) → prfK AX φ, 
from fin_conj_repeat hax,
simp at *, 
cases h2 with h2 h3,
intro h6, apply h1, apply h4 h2, 
exact h3,
exact h6
end 


theorem forcesAX (AX : ctx) (hax : sem_cons AX) : 
  forces_ctx (canonical AX) (val_canonical AX) AX :=
begin
intros φ xΓ h1,
have h2 : ∀ ψ ∈ list.nil, ψ ∈ xΓ.val, 
{intros ψ h3, have h4 := list.ne_nil_of_length_pos (list.length_pos_of_mem h3),
simp at *, exact false.elim h4},
exact (truth AX hax xΓ φ).mpr (exercise1 xΓ.2 h2 (mp pl1 (ax h1)))
end


theorem completeness (AX : ctx) (hax : sem_cons AX) (φ : form) : 
  global_sem_csq AX φ → prfK AX φ :=
begin
rw ←not_imp_not, intro h1,
have h2 := comphelper AX φ hax h1,
have h3 := lindenbaum AX {¬φ} h2,
simp at *,
cases h3 with Γ' h3, cases h3 with h3 h4, 
rw global_sem_csq, 
push_neg,
let f := canonical, use f AX,
let v := val_canonical, use v AX,
let xΓ' : (f AX).states := ⟨Γ', h3⟩,
split, 
exact forcesAX AX hax,
use xΓ',
have h5 := truth AX hax xΓ' ¬φ,
cases h5 with h5 h6,
have h7 := not_forces_imp (f AX) (v AX) xΓ' φ,
cases h7 with h7 h8, apply h8, apply h6, exact h4
end


lemma T_reflexive : T_canonical ∈ ref_class :=
begin
intros x φ h1,
have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK T_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
  from exercise1 x.2, simp at *,
have h3 : prfK T_axioms (fin_conj [φ.box] ⊃ φ), 
{repeat {rw fin_conj},
have h4 : prfK T_axioms (φ.box ⊃ φ), 
{refine ax _, rw T_axioms, simp},
exact cut (mp pl5 phi_and_true) h4},
exact h2 h1 h3
end


theorem T_completeness (φ : form) : F_valid φ ref_class → prfK T_axioms φ :=
begin
rw ←not_imp_not, 
intro h1,
have h2 := completeness T_axioms sem_consT φ,
rw ←not_imp_not at h2,
specialize h2 h1,
rw F_valid, 
push_neg,
let f := T_canonical, use f,
split,
exact T_reflexive,
let v := val_canonical, use (@v T_axioms sem_consT),
have h4 := lindenbaum T_axioms {¬φ} (comphelper T_axioms φ sem_consT h1),
simp at *,
cases h4 with Γ' h4, cases h4 with h4 h5,
let xΓ : f.states := ⟨Γ', h4⟩,
use xΓ,
have h6 := truth T_axioms sem_consT xΓ ¬φ,
cases h6 with h6 h7,
have h8 := not_forces_imp f (@v T_axioms sem_consT) xΓ φ,
cases h8 with h8 h9, apply h9, apply h7, exact h5
end


lemma S4_reftrans : S4_canonical ∈ ref_trans_class :=
begin
split,
intros x φ h1,
have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S4_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
  from exercise1 x.2, simp at *,
have h3 : prfK S4_axioms (fin_conj [φ.box] ⊃ φ), 
{repeat {rw fin_conj},
have h4 : prfK S4_axioms (φ.box ⊃ φ), 
{refine ax _, rw S4_axioms, simp, rw T_axioms, simp},
exact cut (mp pl5 phi_and_true) h4},
exact h2 h1 h3,
intros x y z h1 h2 φ h3, apply h2 φ,
apply h1 (□φ),
have h4 : prfK S4_axioms (fin_conj [φ.box] ⊃ φ.box.box), 
{repeat {rw fin_conj},
have h5 : prfK S4_axioms (φ.box ⊃ φ.box.box), 
{refine ax _, rw S4_axioms, simp},
exact cut (mp pl5 phi_and_true) h5},
have h6 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S4_axioms (fin_conj [□φ] ⊃ φ.box.box) → φ.box.box ∈ x.1, 
  from exercise1 x.2, simp at *,
exact h6 h3 h4
end


theorem S4_completeness (φ : form) : F_valid φ ref_trans_class → prfK S4_axioms φ :=
begin
rw ←not_imp_not, 
intro h1,
have h2 := completeness S4_axioms sem_consS4 φ,
rw ←not_imp_not at h2,
specialize h2 h1,
rw F_valid, 
push_neg,
let f := S4_canonical, use f,
split,
exact S4_reftrans,
let v := val_canonical, use (@v S4_axioms sem_consS4),
have h4 := lindenbaum S4_axioms {¬φ} (comphelper S4_axioms φ sem_consS4 h1),
simp at *,
cases h4 with Γ' h4, cases h4 with h4 h5,
let xΓ : f.states := ⟨Γ', h4⟩,
use xΓ,
have h6 := truth S4_axioms sem_consS4 xΓ ¬φ,
cases h6 with h6 h7,
have h8 := not_forces_imp f (@v S4_axioms sem_consS4) xΓ φ,
cases h8 with h8 h9, apply h9, apply h7, exact h5
end


lemma euclid_dual {φ : form} : prfK S5_axioms ((◇(¬φ) ⊃ □(◇(¬φ))) ⊃ (◇(□φ) ⊃ □φ)) :=
begin
simp,
have h1 : prfK S5_axioms (◇(¬φ) ⊃ □(◇¬φ)),
refine ax _, rw S5_axioms, simp, simp at *,
have h2 := contrapos.mpr h1,
have h3 := cut h2 (mp pl6 dual_equiv1),
have h4 : prfK S5_axioms ((¬□(◇¬φ)) ↔ (¬¬◇(¬(◇¬φ)))),
  from (mp (mp pl4 (contrapos.mpr (mp pl6 dual_equiv1))) (contrapos.mpr (mp pl5 dual_equiv1))),
have h5 := cut dni (cut (mp pl6 h4) h3),
have h6 := (contrapos.mpr (mp kdist (nec (contrapos.mpr (mp pl5 dual_equiv1))))),
exact (mp pl1 (cut h6 h5))
end


lemma S5_equiv : S5_canonical ∈ equiv_class :=
begin
rw equiv_ref_euclid,
split,
intros x φ h1,
have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S5_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
  from exercise1 x.2, simp at *,
have h3 : prfK S5_axioms (fin_conj [φ.box] ⊃ φ), 
{repeat {rw fin_conj},
have h4 : prfK S5_axioms (φ.box ⊃ φ), 
{refine ax _, rw S5_axioms, simp, rw T_axioms, simp},
exact cut (mp pl5 phi_and_true) h4},
exact h2 h1 h3,
intros x y z h1 h2 φ h3,
apply h2 φ, clear h2,
have h2 : prfK S5_axioms (◇(¬φ) ⊃ □(◇¬φ)), 
{refine ax _, rw S5_axioms, simp},
have h4 : prfK S5_axioms (◇(□φ) ⊃ □φ), 
  from mp euclid_dual h2,
have h5 : (∀ ψ ∈ [◇(□φ)], ψ ∈ x.1) → 
  prfK S5_axioms (fin_conj [◇(□φ)] ⊃ □φ) → □φ ∈ x.1, 
  from exercise1 x.2, simp at *,
apply h5,
by_contradiction h6,
have h7 := (max_notiff S5_axioms x.1 x.2 (¬(¬φ.box).box)).mp h6,
have h8 := (max_dn S5_axioms x.1 x.2 ((¬φ.box).box)).mpr h7,
have h9 := (max_notiff S5_axioms y.1 y.2 (φ.box)).mpr (h1 (¬φ.box) h8),
exact absurd h3 h9,
exact (cut (mp pl5 phi_and_true) h4)
end


theorem S5_completeness (φ : form) : F_valid φ equiv_class → prfK S5_axioms φ :=
begin
rw ←not_imp_not, 
intro h1,
have h2 := completeness S5_axioms sem_consS5 φ,
rw ←not_imp_not at h2,
specialize h2 h1,
rw F_valid, 
push_neg,
let f := S5_canonical, use f,
split,
exact S5_equiv,
let v := val_canonical, use (@v S5_axioms sem_consS5),
have h4 := lindenbaum S5_axioms {¬φ} (comphelper S5_axioms φ sem_consS5 h1),
simp at *,
cases h4 with Γ' h4, cases h4 with h4 h5,
let xΓ : f.states := ⟨Γ', h4⟩,
use xΓ,
have h6 := truth S5_axioms sem_consS5 xΓ ¬φ,
cases h6 with h6 h7,
have h8 := not_forces_imp f (@v S5_axioms sem_consS5) xΓ φ,
cases h8 with h8 h9, apply h9, apply h7, exact h5
end

end canonical

