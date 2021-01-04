/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.languageDEL del.syntax.syntaxDEL 
import del.semantics.semanticsDEL del.syntax.syntaxlemmasDEL
import del.syntax.soundnessDEL order.zorn data.set.basic data.list.basic
local attribute [instance] classical.prop_decidable

variables {agents : Type}
open prfS5
open S5lemma


---------------------- Consistency ----------------------


def sem_cons (AX : ctx agents) (F : set (frame agents)) := ¬ global_sem_csq AX F form.bot 
attribute [class] sem_cons


lemma sem_consS5 : sem_cons (∅ : ctx agents) equiv_class :=
begin
rw sem_cons,
rw global_sem_csq,
push_neg,
let f : frame agents := 
{ states := ℕ,
  h := ⟨0⟩,
  rel := λ a x y, x = y},
use f, let v := λ n x, true,
split,
intro a,
split,
intro x,
exact rfl,
split,
intros x y h1,
exact eq.symm h1,
intros x y z h1 h2,
exact (rfl.congr h2).mp h1,
use v,
split,
intros φ x h1,
exact false.elim h1, 
let x := 42,
use x,
rw forces, 
trivial
end


-- The S5 axiom system does not prove false
lemma nprfalse (hax : sem_cons (∅ : ctx agents) equiv_class) : ¬ prfS5 (∅ : ctx agents) form.bot :=
begin
have h1 : ¬ global_sem_csq (∅ : ctx agents) equiv_class form.bot → ¬ prfS5 ∅ form.bot,
{have h2 := soundnessS5,
rw ←not_imp_not at h2, exact h2},
apply h1, exact hax
end


lemma prnot_to_notpr (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  prfS5 ∅ (¬φ) → ¬ prfS5 ∅ φ :=
begin
intro h1, by_contradiction h2,
exact absurd (mp (mp pl5 contra_equiv_false) (mp (mp pl4 h2) h1)) (nprfalse hax)
end 


lemma pr_to_notprnot (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  prfS5 ∅ φ → ¬ prfS5 ∅ (¬φ) :=
begin
have h1 := prnot_to_notpr φ hax,
rw ←not_imp_not at h1, intro h2, apply h1, rw not_not, exact h2,
end 


-- finite conjunction of formulas
def fin_conj : list (form agents) → form agents
  | []      := ¬form.bot
  | (φ::φs) := φ & (fin_conj φs)


-- a few helper lemmas about finite conjunctions
lemma fin_conj_simp {Γ : ctx agents} : ∀ ψ : form agents, prfS5 Γ (¬fin_conj [ψ, ¬ψ]) :=
begin
intro ψ, exact (not_and_subst phi_and_true).mpr not_contra
end


lemma imp_conj_imp_imp {Γ : ctx agents} {φ ψ χ : form agents} {L : list (form agents)} : 
  prfS5 Γ ((fin_conj (φ::L)) ⊃ ψ) ↔ prfS5 Γ (fin_conj L ⊃ (φ ⊃ ψ)) :=
begin
split, 
intro h, dsimp [fin_conj] at h, rw and_right_imp at h, exact h,
intro h, dsimp [fin_conj], rw and_right_imp, exact h
end


lemma fin_conj_cons_imp {Γ : ctx agents} {φ b : form agents} {L : list (form agents)} : 
 prfS5 Γ (fin_conj (φ::L) ⊃ (φ ⊃ b)) → prfS5 Γ (fin_conj L ⊃ (φ ⊃ b)) :=
begin
intro h, rw imp_conj_imp_imp at h, rw imp_imp_iff_imp at h, exact h, exact φ,
end


lemma fin_conj_append {Γ : ctx agents} {L L' : list (form agents)} :
  prfS5 Γ ((fin_conj L' & fin_conj L) ↔ (fin_conj (L' ++ L))) :=
begin
induction L', rw fin_conj,
exact (mp (mp pl4 (cut (mp pl6 and_switch) (mp pl5 phi_and_true))) 
  (cut (mp pl6 phi_and_true) (mp pl5 and_switch))),
exact mp (mp pl4 (cut (mp pl5 and_commute) (imp_and_imp (mp pl5 L'_ih)))) 
  (cut iden (cut (imp_and_imp (mp pl6 L'_ih)) (mp pl6 and_commute)))
end 


lemma fin_conj_empty {L : list (form agents)} 
  (hax : sem_cons (∅ : ctx agents) equiv_class) :
  L = [] → ¬ prfS5 ∅ (fin_conj L ⊃ ⊥) :=
begin
intro h1, subst h1,
by_contradiction h2,
exact absurd (mp h2 iden) (nprfalse hax)
end 


lemma fin_conj_repeat_helper {θ : form agents} {L : list (form agents)} 
  (hax : sem_cons (∅ : ctx agents) equiv_class) :
  (∀ ψ ∈ L, ψ = θ) → prfS5 ∅ (θ ⊃ fin_conj L) :=
begin
intros h1, induction L,
exact mp pl1 iden,
rw fin_conj, simp at *,
cases h1 with h1 h2,
subst h1,
exact cut (mp double_imp pl4) (imp_and_and_imp (mp (mp pl4 iden) (L_ih h2))),
end


lemma fin_conj_repeat {φ : form agents} {L : list (form agents)}
  (hax : sem_cons (∅ : ctx agents) equiv_class) :
  (∀ ψ ∈ L, ψ = ¬φ) → prfS5 ∅ (¬fin_conj L) → prfS5 ∅ φ :=
begin
intros h1 h2, induction L,
exact absurd (mp dne h2) (nprfalse hax),
repeat {rw fin_conj at *}, simp at *,
cases h1 with h1 h3, 
have h5 := contrapos.mpr (fin_conj_repeat_helper hax h3),
subst h1,
exact (mp (mp pl3 (contrapos.mpr (cut h5 dne))) 
  (contrapos.mpr (cut ((demorgans.mp) (mp (mp pl6 (iff_not and_switch)) h2)) dne)))
end


lemma fin_conj_box2 {φ ψ : form agents} {a : agents} : 
  prfS5 ∅ (((K a φ) & K a ψ) ⊃ K a (φ & ψ)) :=
begin
exact (mp double_imp (cut2 pl6 (cut pl5 (cut (mp kdist (nec pl4)) kdist))))
end


lemma fin_conj_boxn {L : list (form agents)} {a : agents} : 
  prfS5 ∅ ((fin_conj (list.map (K a) L)) ⊃ (K a (fin_conj L))) :=
begin
induction L,
exact (mp pl1 (nec prtrue)),
exact (cut (imp_and_imp L_ih) fin_conj_box2)
end


lemma listempty {Γ : ctx agents} {L : list (form agents)} :
  (∀ φ ∈ L, φ ∈ Γ) → Γ = ∅ → L = [] := 
begin
intros h1 h2,
by_contradiction h3,
have h4 := list.length_pos_of_ne_nil,
have h5 := list.exists_mem_of_length_pos,
cases h5 (h4 h3) with φ h5,
exact absurd (h1 φ h5) (set.eq_empty_iff_forall_not_mem.mp h2 φ)
end


-- Consistency for a finite set of formulas L
def fin_ax_consist (L : list (form agents)) := ¬ prfS5 ∅ (fin_conj L ⊃ ⊥)


-- Consistency for an arbitrary set of formulas Γ
def ax_consist (Γ : ctx agents) :=
  ∀ L : list (form agents), (∀ ψ ∈ L, ψ ∈ Γ) → fin_ax_consist L


-- Γ is maximally ax-consistent
def max_ax_consist (Γ : ctx agents) := 
  ax_consist Γ ∧ (∀ Γ', Γ ⊂ Γ' → ¬ ax_consist Γ')


lemma max_imp_ax {Γ : ctx agents} : max_ax_consist Γ → ax_consist Γ :=
begin
intro h1, exact h1.left
end


-- Lemma 5 from class notes
lemma five_helper : 
  ∀ Γ : ctx agents, ∀ φ : form agents, ∀ L : list (form agents), ∀ b : form agents, 
  (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfS5 ∅ (fin_conj L ⊃ b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L' ⊃ (φ ⊃ b)) :=
begin
intros Γ φ L b h1 h2, 
revert b, 
induction L,
{intros b h2, existsi ([] : list (form agents)), split, 
intros ψ h3, exfalso, apply list.not_mem_nil ψ h3, 
exact imp_if_imp_imp h2},
{intros b h2,
have h1a : ∀ (ψ : form agents), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
  {intros ψ h2, apply h1 ψ (list.mem_cons_of_mem L_hd h2)},
have h1b: L_hd ∈ Γ ∨ L_hd = φ, 
  {apply h1 L_hd, left, refl},
cases h1b, 
have h3 := and_right_imp.mp h2,
cases L_ih h1a (L_hd ⊃ b) h3 with L' ih, existsi (L_hd::L' : list (form agents)),
cases ih, split, intros ψ h4, cases h4, 
subst h4, exact h1b, 
apply ih_left ψ h4, rw imp_shift at ih_right,
rw ←imp_conj_imp_imp at ih_right, exact ih_right,
have h3 : prfS5 ∅ (fin_conj (L_hd::L_tl) ⊃ b), 
exact h2, exact b,
have h4 : prfS5 ∅ (fin_conj L_tl ⊃ (φ ⊃ b)), 
  from eq.subst h1b (and_right_imp.mp) h2,
cases L_ih h1a (φ ⊃ b) h4 with L' ih, 
cases ih, existsi (L' : list (form agents)), split, 
exact ih_left, exact imp_imp_iff_imp.mp ih_right}
end

lemma five : 
  ∀ Γ : ctx agents, ∀ φ : form agents, ¬ ax_consist (Γ ∪ φ) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L' ⊃ ¬φ) :=
begin
intro Γ, intro φ, intro h1, rw ax_consist at h1, 
push_neg at h1,
cases h1 with L h1,
have h2 : (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfS5 ∅ (fin_conj L ⊃ ⊥) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L' ⊃ (φ ⊃ ⊥)), from five_helper Γ φ L ⊥,
cases h1,
have h3 : (∀ (ψ : form agents), ψ ∈ L → ψ ∈ Γ ∨ ψ = φ), 
{intros ψ this, exact or.swap (h1_left ψ this)},
apply h2 h3, rw fin_ax_consist at h1_right, rw not_not at h1_right,
exact h1_right,
end


-- Lemma 6 from class notes
lemma six_helper (Γ : ctx agents) (h : ax_consist Γ) :
max_ax_consist Γ → ∀ φ : form agents, φ ∈ Γ ∨ (¬φ) ∈ Γ :=
begin
intros h1 φ, rw or_iff_not_and_not, by_contradiction h2,
cases h2 with h2l h2r,
cases h1 with h1l h1r, clear h, 
have h2 := h1r (Γ ∪ φ),
have h3 : ¬ax_consist (Γ ∪ ¬φ), 
{apply h1r (Γ ∪ ¬φ), from set.ssubset_insert h2r},
have h5 : ¬ax_consist (Γ ∪ φ), 
{apply h2, from set.ssubset_insert h2l}, 
have h6 := five Γ φ _, have h7 := five Γ (¬φ) _, 
cases h6 with L' h6, cases h7 with L h7, cases h6 with h6l h6r,
cases h7 with h7l h7r,
have h8 := imp_and_and_imp (mp (mp pl4 h6r) h7r),
have h12 := cut (mp pl6 fin_conj_append) (cut h8 (mp pl5 contra_equiv_false)),
have h13 : (∀ (ψ : form agents), ψ ∈ L' ++ L → ψ ∈ Γ), 
intro ψ, intro h13,
rw list.mem_append at h13, cases h13, exact h6l ψ h13, exact h7l ψ h13,
exact absurd h12 (h1l (L' ++ L) h13),
exact h3,
exact h5,
end


lemma six (Γ : ctx agents) (h : ax_consist Γ) :
max_ax_consist Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬φ) ∈ Γ) :=
begin 
simp, split, 
intro h1, intro φ, 
split, exact six_helper Γ h h1 φ,
{rw ←not_and, by_contradiction h2,
cases h2 with h2 h3,
specialize h ([φ, ¬φ]), simp at *,
have h4 : (∀ (ψ : form agents), ψ = φ ∨ ψ = ¬φ → ψ ∈ Γ), 
{intros ψ h4, cases h4, subst h4, exact h2, subst h4, exact h3},
have h5 : prfS5 ∅ (¬fin_conj [φ, ¬φ]), from fin_conj_simp φ, 
exact absurd h5 (h h4)},
intro h1, split, exact h,
intros Γ' h2,
have h3 : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ, from h2,
cases h3,
rw set.not_subset at h3_right,
apply (exists.elim h3_right), simp, intros ψ h4 h5,
specialize h1 ψ, cases h1,
cases h1_left,
apply absurd h1_left h5,
have h6 : (¬ψ) ∈ Γ', from set.mem_of_subset_of_mem h3_left h1_left,
rw ax_consist, 
push_neg,
existsi ([ψ,¬ψ] : list (form agents)),
simp, split, intros φ h7, cases h7, subst h7, exact h4, 
subst h7, exact h6, rw fin_ax_consist, rw not_not,
exact fin_conj_simp ψ
end


-- Exercise 1 from class notes
lemma ex1help {Γ : ctx agents} {φ : form agents} {L L' : list (form agents)} :
  (∀ ψ ∈ L, ψ ∈ Γ) → prfS5 ∅ (fin_conj L ⊃ φ) → (∀ ψ ∈ L', ψ ∈ (insert φ Γ)) 
  → ∃ L'' : list (form agents), (∀ ψ ∈ L'', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L'' ⊃ fin_conj L') :=
begin
intros h1 h2 h3, induction L',
existsi ([] : list (form agents)),
split,
intros ψ h4, exact false.elim h4,
exact iden,
simp at *, cases h3 with h3 h4,
cases L'_ih h4 with L'' L'_ih,
cases L'_ih with ih1 ih2,
cases h3, 
existsi (L''++L : list (form agents)),
split,
simp at *, intros ψ h2,
cases h2 with h2 h5,
exact ih1 ψ h2,
exact h1 ψ h5,
subst h3, 
exact (cut (mp pl6 fin_conj_append) (cut (mp pl5 and_switch) (imp_and_and_imp (mp (mp pl4 h2) ih2)))),
existsi (L'_hd::L'' : list (form agents)),
split, simp at *, split, exact h3, exact ih1,
exact imp_and_imp ih2
end


lemma exercise1 {Γ : ctx agents} {φ : form agents} {L : list (form agents)} :
  max_ax_consist Γ → (∀ ψ ∈ L, ψ ∈ Γ) → prfS5 ∅ (fin_conj L ⊃ φ) → φ ∈ Γ :=
begin
intros h1 h2 h3, 
by_contradiction h4, 
cases h1 with h1 h5, 
specialize h5 (Γ ∪ {φ}), 
simp at h5,
specialize h5 (set.ssubset_insert h4), 
rw ax_consist at h5,
push_neg at h5,
cases h5 with L' h5,
cases h5 with h5 h6,
rw fin_ax_consist at h6, 
rw not_not at h6,
have h7 := ex1help h2 h3 h5,
cases h7 with L'' h7,
cases h7 with h7 h8,
apply h1 L'' h7,
exact cut h8 h6
end


lemma max_dn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) :
  φ ∈ Γ ↔ (¬¬φ) ∈ Γ :=
begin
split, intro h1, 
have h2 : (∀ ψ ∈ [φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (¬¬φ)) → (¬¬φ) ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
exact (cut (mp pl5 phi_and_true) dni), 
intro h1,
have h2 : (∀ ψ ∈ [¬¬φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬¬φ] ⊃ φ) → φ ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
exact (cut (mp pl5 phi_and_true) dne), 
end


lemma max_boxdn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) (a : agents) :
  (¬K a φ) ∈ Γ → (¬ (K a (¬¬φ))) ∈ Γ :=
begin
intro h1,
have h2 : ∀ a, (∀ ψ ∈ [¬ K a φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬ K a φ] ⊃ (¬ (K a (¬¬φ)))) → (¬ (K a (¬¬φ))) ∈ Γ,
  from λ a, exercise1 h,
simp at *, 
apply h2 a, exact h1, clear h2,
exact (cut (mp pl5 phi_and_true) (mp pl5 box_dn)), 
end


lemma max_notiff (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) :
  φ ∉ Γ ↔ (¬φ) ∈ Γ :=
begin
split, intro h1,
have h2 := max_imp_ax h, 
have h3 := six_helper Γ h2 h,
specialize h3 φ, cases h3, exact absurd h3 h1, exact h3,
intro h1,
have h2 := max_imp_ax h, 
have h3 := six Γ h2,
cases h3, specialize h3_mp h (¬φ), simp at *,
cases h3_mp with mp1 mp2,
have h4 := max_dn Γ h φ,
rw ←not_iff_not at h4, apply h4.mpr, exact mp2 h1
end


lemma max_imp_1 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ ∈ Γ → ψ ∈ Γ) → (φ ⊃ ψ) ∈ Γ :=
begin
intros h1 h2, rw imp_iff_not_or at h2,
cases h2,
have h3 : (∀ χ ∈ [¬φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [¬φ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
simp at *, apply h3, 
exact (max_notiff Γ h1 φ).mp h2,
exact cut (mp pl5 phi_and_true) (and_right_imp.mp exfalso),
have h3 : (∀ χ ∈ [ψ], χ ∈ Γ) → prfS5 ∅ (fin_conj [ψ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
simp at *, 
apply h3, exact h2, exact (cut (mp pl5 phi_and_true) pl1),
end


lemma max_imp_2 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ ⊃ ψ) ∈ Γ → φ ∈ Γ → ψ ∈ Γ :=
begin
intros h1 h2 h3,
have h4 : (∀ χ ∈ [φ, (φ ⊃ ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [φ, (φ ⊃ ψ)] ⊃ ψ) → ψ ∈ Γ, from exercise1 h1,
simp at *, apply h4, intros χ h5, cases h5, subst h5, exact h3, subst h5, exact h2,
exact and_right_imp.mpr (mp pl5 phi_and_true)
end


lemma max_conj_1 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ ∈ Γ ∧ ψ ∈ Γ) → (φ & ψ) ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (ψ ⊃ (φ & ψ))) → (ψ ⊃ (φ & ψ)) ∈ Γ, 
  from exercise1 h1,
simp at *,
apply max_imp_2 h1, 
exact (h3 h2.left) (cut (mp pl5 phi_and_true) pl4), exact h2.right
end


lemma max_conj_2 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → φ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ φ) → φ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2,
exact (cut (mp pl5 phi_and_true) pl5)
end


lemma max_conj_3 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → ψ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ ψ) → ψ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2,
exact (cut (mp pl5 phi_and_true) pl6)
end


-- Γ is maximally AX-consistent iff it is AX-consistent and for 
-- every AX-consistent set Γ', if Γ ⊆ Γ', then Γ = Γ'
lemma max_equiv (Γ : ctx agents) : max_ax_consist Γ ↔ ax_consist Γ ∧ 
  ∀ Γ', ax_consist Γ' → Γ ⊆ Γ' → Γ = Γ' :=
begin
split, 
{intro h1, split, exact h1.left, 
intros Γ' h2 h3, rw set.subset.antisymm_iff, split, exact h3,
by_contradiction h4, exact h1.right Γ' (and.intro h3 h4) h2}, 
intro h1, split, exact h1.left,
intros Γ' h2, by_contradiction h3,
rw set.ssubset_def at h2, apply h2.right, 
rw (h1.right Γ' h3) h2.left
end


open zorn
-- Lemma: if c is a chain of sets, L is a list of elements such that 
-- every element in L is in Union(c), then there is an element m in c such that every 
-- element of L is in m.
lemma lindenhelper (c : set (ctx agents)) (h : c.nonempty) (h1 : chain (⊆) c) (L : list (form agents)) :
(∀ φ ∈ L, φ ∈ ⋃₀(c)) → ∃ m ∈ c, (∀ ψ ∈ L, ψ ∈ m) :=
begin
intro h2,
induction L, simp,
rw ←set.nonempty_def, exact h,
have h2b : ∀ φ, φ ∈ L_tl → φ ∈ ⋃₀(c), 
{intros φ h3, apply h2, exact set.mem_union_right (eq φ) h3},
cases L_ih h2b with m ih,
cases ih with h3 ih,
specialize h2 L_hd, 
simp at h2,
cases h2 with m' h2,
cases h2 with h2 h4,
existsi (m' ∪ m : ctx agents), 
have h5 : m' ∪ m ∈ c, 
{have h6 := chain.total_of_refl h1 h3 h2,
cases h6,
exact (eq.substr (set.union_eq_self_of_subset_right h6) h2), 
exact (eq.substr (set.union_eq_self_of_subset_left h6) h3)},
existsi (h5 : m' ∪ m ∈ c),
intros ψ h6, cases h6,
subst h6, exact set.mem_union_left m h4,
exact set.mem_union_right m' (ih ψ h6)
end


lemma lindenbaum (Γ : ctx agents) (hax : ax_consist Γ) : 
  ∃ Γ', max_ax_consist Γ' ∧ Γ ⊆ Γ' :=
begin
let P := { Γ'' | Γ'' ⊇ Γ ∧ ax_consist Γ''},
have h : ∀ c ⊆ P, chain (⊆) c → c.nonempty → ∃ub ∈ P, ∀ s ∈ c, s ⊆ ub, 
{intros c h2 h3 h4, use ⋃₀(c), 
have h5 := lindenhelper c h4 h3,
repeat {split}, 
cases h4 with Γ'' h4,
have h6 := set.mem_of_mem_of_subset h4 h2,
cases h6 with h6 h7,
apply set.subset_sUnion_of_subset c Γ'' h6 h4,
intros L h6,
cases h5 L h6 with m h5,
cases h5 with h7 h5,
cases (set.mem_of_mem_of_subset h7 h2) with h8 h9,
apply h9, exact h5,
intros s h7, exact set.subset_sUnion_of_mem h7},
have h1 : Γ ∈ P,
split,
exact set.subset.rfl,
exact hax,
cases zorn_subset₀ P h Γ h1 with Γ' h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
use Γ', split, rw max_equiv, split, apply h2.2, 
intros m h5 h6, symmetry, apply h4 m, split, 
apply set.subset.trans h2.1 h6,
exact h5, exact h6, apply h2.1
end


-- Corollary 8 from class notes
lemma max_ax_exists (hax : sem_cons (∅ : ctx agents) equiv_class) : ∃ Γ : ctx agents, max_ax_consist Γ :=
begin
have h1 : ax_consist ∅,
{intro L, intro h2, rw fin_ax_consist, 
have h3 := listempty h2, have this : ∅ = ∅, refl, 
specialize h3 this, subst h3, by_contradiction h4, 
apply nprfalse hax, exact mp dne h4},
have h2 := lindenbaum ∅ h1, 
cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : ctx agents), apply h2
end