/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.semantics.consistencyDEL del.syntax.soundnessDEL
import data.list.basic
local attribute [instance] classical.prop_decidable

variables {agents : Type}
open prfS5
open S5lemma


---------------------- Canonical Model Construction ----------------------


namespace canonical

def canonical [hax : sem_cons (∅ : ctx agents) equiv_class] : frame agents := 
{ 
  states := {xΓ : ctx agents // max_ax_consist xΓ},
  h := begin have h1 := max_ax_exists hax, choose Γ h1 using h1, exact ⟨⟨Γ, h1⟩⟩ end,
  rel := λ a, λ xΓ yΔ, ∀ φ : form agents, K a φ ∈ xΓ.val → φ ∈ yΔ.val
}


def val_canonical [hax : sem_cons (∅ : ctx agents) equiv_class] : 
  nat → canonical.states → Prop := λ n, λ xΓ : canonical.states, (form.var n) ∈ (xΓ.val : ctx agents)


lemma existence (hax : sem_cons (∅ : ctx agents) equiv_class) (xΓ : canonical.states) :
  ∀ a, ∀ φ : form agents, (¬ K a (¬φ)) ∈ xΓ.val ↔ ∃ yΔ : canonical.states, φ ∈ yΔ.val ∧ canonical.rel a xΓ yΔ :=
begin
intros a φ, split,
intro h1,
let Γbox : ctx agents := {ψ : form agents | K a ψ ∈ xΓ.val},
have h1 : ax_consist (Γbox ∪ {φ}), 
{by_contradiction h2, simp at h2,
have h3 := five Γbox φ h2,
cases h3 with L h3, cases h3 with h3 h4,
have h5 := cut fin_conj_boxn (mp kdist (nec h4)),
have h6 := exercise1,
have h7 : ∀ ψ ∈ (list.map (form.box a) L), ψ ∈ xΓ.1, 
intros ψ h8, simp at *, cases h8 with a h8,
cases h8 with h8l h8r,
subst h8r, exact h3 a h8l,
specialize h6 xΓ.2 h7 h5,
have h8 := (six xΓ.1 (max_imp_ax xΓ.2)).mp xΓ.2 (K a (¬φ)),
cases h8 with h8l h8r, simp at *, 
exact absurd h1 (h8r h6),
},
have h2 := lindenbaum (Γbox ∪ {φ}) h1,
cases h2 with Δ h2, cases h2 with h2 h3,
let xΔ : canonical.states := ⟨Δ, h2⟩,
existsi (xΔ : canonical.states),
have h5 := set.union_subset_iff.mp h3,
cases h5, split, simp at h5_right, exact h5_right,
have h3 : ∀ φ : form agents, K a φ ∈ xΓ.val → φ ∈ xΔ.val,
intros ψ h4, apply h5_left, exact h4,
exact h3,
simp at *,
intros yΔ h1 h2,
by_contradiction h4,
have h5 := (max_notiff xΓ.1 xΓ.2 (C a φ)).mp h4,
have h6 := (max_dn xΓ.1 xΓ.2 (K a ¬φ)).mpr h5,
exact absurd h1 ((max_notiff yΔ.1 yΔ.2 φ).mpr ((h2 (¬φ)) h6))
end


lemma truth (hax : sem_cons (∅ : ctx agents) equiv_class) (xΓ : canonical.states) : 
  ∀ φ : form agents, forces canonical val_canonical xΓ φ ↔ (φ ∈ xΓ.val) :=
begin
intro φ, induction φ with n φ ψ ih_φ ih_ψ 
φ ψ ih_φ ih_ψ φ ih_φ generalizing xΓ,
split, intro h1, exact false.elim h1,
intro h1, rw forces, 
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
rename φ a, rename ih_φ φ,
split, 
intros h1, by_contradiction h2,
have h4 := (existence hax xΓ a (¬φ)).mp,
have h5 := max_boxdn xΓ.1 xΓ.2 φ a ((max_notiff xΓ.1 xΓ.2 (K a φ)).mp h2),
cases h4 h5 with xΔ h4, cases h4 with h4 h6,
have h7 := max_notiff xΔ.1 xΔ.2 φ,
cases h7 with h7l h7r,
exact absurd ((φ_ih xΔ).mp (h1 xΔ h6)) (h7r h4),
intros h1 xΔ h2,
apply (φ_ih xΔ).mpr, exact (h2 φ h1),
end


lemma comphelper (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  ¬ prfS5 ∅ φ → ax_consist ({¬φ} : ctx agents) :=
begin
intros h1 L h2,
rw fin_ax_consist, induction L,
by_contradiction h3,
exact absurd (mp dne h3) (nprfalse hax), 
have h4 : (∀ ψ ∈ L_hd::L_tl, ψ = ¬φ) → prfS5 ∅ (¬fin_conj (L_hd::L_tl)) → prfS5 ∅ φ, 
from fin_conj_repeat hax,
simp at *, 
cases h2 with h2 h3,
intro h6, apply h1, apply h4 h2, 
exact h3,
exact h6
end 


theorem forcesAX (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  forces_ctx canonical val_canonical (∅ : ctx agents) :=
begin
intros φ xΓ h1,
have h2 := mp prfS5.pl1 (ax h1),
have h3 : ∀ ψ ∈ list.nil, ψ ∈ xΓ.val, 
{intros ψ h3, have h5 := list.ne_nil_of_length_pos (list.length_pos_of_mem h3),
simp at *, exact false.elim h5},
have h4 := exercise1 xΓ.2 h3 h2,
exact (truth hax xΓ φ).mpr h4
end


lemma euclid_dual {a : agents} {φ : form agents} : 
  prfS5 ∅ ((C a (¬φ) ⊃ K a (C a (¬φ))) ⊃ (C a (K a φ) ⊃ K a φ)) :=
begin
have h1 := contrapos.mpr negintro,
have h2 := cut h1 (mp pl6 dual_equiv1),
have h3 : prfS5 ∅ ((¬K a (C a ¬φ)) ↔ (¬¬C a (¬(C a ¬φ)))),
  from (mp (mp pl4 (contrapos.mpr (mp pl6 dual_equiv1))) 
  (contrapos.mpr (mp pl5 dual_equiv1))),
have h4 := cut dni (cut (mp pl6 h3) h2),
have h5 := (contrapos.mpr (mp kdist (nec (contrapos.mpr (mp pl5 dual_equiv1))))),
exact (mp pl1 (cut h5 h4))
end


lemma S5_equiv (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  canonical ∈ (equiv_class : set (frame agents)) :=
begin
rw equiv_ref_euclid,
split,
intros a x φ h1,
have h2 : ∀ a, (∀ ψ ∈ [(K a φ)], ψ ∈ x.1) → prfS5 ∅ (fin_conj [(K a φ)] ⊃ φ) → φ ∈ x.1, 
  from λ a, exercise1 x.2,
have h3 : prfS5 ∅ (fin_conj [(K a φ)] ⊃ φ), 
{exact cut (mp pl5 phi_and_true) prfS5.truth},
specialize h2 a, simp at *,
exact h2 h1 h3,
intros a x y z h1 h2 φ h3,
apply h2 φ,
have h4 := mp euclid_dual negintro,
have h5 : ∀ a, (∀ ψ ∈ [(C a (K a φ))], ψ ∈ x.1) → 
  prfS5 ∅ (fin_conj [(C a (K a φ))] ⊃ K a φ) → K a φ ∈ x.1,
  from λ a, exercise1 x.2, 
simp at *,
apply h5,
by_contradiction h6,
have h7 := max_notiff x.1 x.2 (¬K a (¬K a φ)),
have h8 := max_dn x.1 x.2 (K a (¬K a φ)),
have h9 := (max_notiff y.1 y.2 (K a φ)).mpr (h1 (¬K a φ) (h8.mpr (h7.mp h6))),
exact absurd h3 h9,
exact (cut (mp pl5 phi_and_true) h4)
end


theorem completeness (hax : sem_cons (∅ : ctx agents) equiv_class) (φ : form agents) : 
  global_sem_csq ∅ equiv_class φ → prfS5 ∅ φ :=
begin
rw ←not_imp_not, intro h1,
have h2 := comphelper φ hax h1,
have h3 := lindenbaum {¬φ} h2,
simp at *,
cases h3 with Γ' h3, cases h3 with h3 h4, 
rw global_sem_csq, 
push_neg,
let f := canonical, 
use f,
let v := val_canonical, 
split,
exact S5_equiv hax, 
use v,
let xΓ' : f.states := ⟨Γ', h3⟩,
split, 
exact forcesAX hax,
use xΓ',
have h5 : forces f v xΓ' (¬φ) ↔ ((¬φ) ∈ xΓ'.val), 
  from truth hax xΓ' ¬φ,
cases h5 with h5 h6,
have h7 : ¬forces f v xΓ' φ ↔ forces f v xΓ' ¬φ, 
  from not_forces_imp f v xΓ' φ,
cases h7 with h7 h8, apply h8, apply h6, exact h4
end


end canonical