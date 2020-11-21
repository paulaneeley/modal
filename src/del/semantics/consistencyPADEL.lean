-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.syntax.syntaxDEL 
import del.semantics.semanticsDEL del.syntax.syntaxlemmasPADEL
import del.syntax.soundnessDEL order.zorn data.set.basic data.list.basic
local attribute [instance] classical.prop_decidable

open prfPA
open PAlemma
variables {agents : Type}


---------------------- Consistency ----------------------

namespace consistPA

-- finite conjunction of formulas
def fin_conj : list (formPA agents) → formPA agents
  | []  := ¬formPA.bot
  | (φ::φs) := φ & (fin_conj φs)

-- a few helper lemmas about finite conjunctions
lemma fin_conj_simp {Γ : ctxPA agents} : ∀ ψ : formPA agents, prfPA Γ (¬fin_conj [ψ, ¬ψ]) :=
begin
intro ψ, rw fin_conj, rw fin_conj, rw fin_conj,
have h2 : (prfPA Γ (((¬ψ)&(¬⊥)) ↔ (¬ψ)) → 
  (prfPA Γ (¬(ψ & ((¬ψ)&(¬⊥)))) ↔ prfPA Γ (¬(ψ & (¬ψ))))), 
  from not_and_subst,
simp at h2,
specialize h2 phi_and_true, cases h2,
exact h2_mpr not_contra
end

lemma fin_conj_append {Γ : ctxPA agents} {L L' : list (formPA agents)} :
  prfPA Γ ((fin_conj L' & fin_conj L) ↔ (fin_conj (L' ++ L))) :=
begin
induction L', rw fin_conj,
exact (mp (mp pl4 (cut (mp pl6 and_switch) (mp pl5 phi_and_true))) 
  (cut (mp pl6 phi_and_true) (mp pl5 and_switch))),
exact mp (mp pl4 (cut (mp pl5 and_commute) (imp_and_imp (mp pl5 L'_ih)))) 
  (cut iden (cut (imp_and_imp (mp pl6 L'_ih)) (mp pl6 and_commute)))
end 

lemma imp_conj_imp_imp {Γ : ctxPA agents} {φ ψ χ : formPA agents} {L : list (formPA agents)} : 
  prfPA Γ ((fin_conj (φ::L)) ⊃ ψ) ↔ prfPA Γ (fin_conj L ⊃ (φ ⊃ ψ)) :=
begin
split, 
intro h, dsimp [fin_conj] at h, rw and_right_imp at h, exact h,
intro h, dsimp [fin_conj], rw and_right_imp, exact h
end

-- consistency for a finite set of formulas L
def fin_ax_consist (L : list (formPA agents)) := ¬ prfPA ∅ (fin_conj L ⊃ ⊥)

-- consistency for an arbitrary set of formulas Γ
def ax_consist (Γ : ctxPA agents) :=
  ∀ L : list (formPA agents), (∀ ψ ∈ L, ψ ∈ Γ) → fin_ax_consist L

-- Γ is maximally ax-consistent
def max_ax_consist (Γ : ctxPA agents) := 
  ax_consist Γ ∧ (∀ Γ', Γ ⊂ Γ' → ¬ ax_consist Γ')

lemma max_imp_ax {Γ : ctxPA agents} : max_ax_consist Γ → ax_consist Γ :=
begin
intro h1, rw max_ax_consist at h1, cases h1, exact h1_left
end

lemma five_helper : 
  ∀ Γ : ctxPA agents, ∀ φ : formPA agents, ∀ L : list (formPA agents), ∀ b : formPA agents, 
  (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfPA ∅ (fin_conj L ⊃ b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfPA ∅ (fin_conj L' ⊃ (φ ⊃ b)) :=
begin
intros Γ φ L b h1 h2, 
revert b, 
induction L,
{intros b h2, existsi ([] : list (formPA agents)), split, 
intros ψ h3, exfalso, apply list.not_mem_nil ψ h3, 
dsimp [fin_conj] at *, exact imp_if_imp_imp h2},
{intros b h2,
have h1a : ∀ (ψ : formPA agents), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
  {intros ψ h2, specialize h1 ψ, 
  have h3 := list.subset_cons L_hd L_tl,
  have h4 := list.mem_cons_of_mem L_hd h2, 
  apply h1 h4},
specialize L_ih h1a,
have h1b: L_hd ∈ Γ ∨ L_hd = φ, 
  {apply h1 L_hd, left, refl},
cases h1b, 
have h3 : prfPA ∅ (fin_conj L_tl ⊃ (L_hd ⊃ b)), 
  from and_right_imp.mp h2,
specialize L_ih (L_hd ⊃ b) h3,
cases L_ih with L' ih, existsi (L_hd::L' : list (formPA agents)),
cases ih, split, intros ψ h4, cases h4, 
subst h4, exact h1b, 
apply ih_left ψ h4, rw imp_shift at ih_right,
rw ←imp_conj_imp_imp at ih_right, exact ih_right,
have h3 : prfPA ∅ (fin_conj (L_hd::L_tl) ⊃ b), 
exact h2, exact b,
specialize L_ih (φ ⊃ b),
have h5 : prfPA ∅ (fin_conj (L_hd :: L_tl) ⊃ b) → 
  prfPA ∅ (fin_conj L_tl ⊃ (L_hd ⊃ b)), 
  from and_right_imp.mp,
specialize h5 h2,
have h6 : prfPA ∅ (fin_conj L_tl ⊃ (φ ⊃ b)), 
  from eq.subst h1b h5,
specialize L_ih h6, cases L_ih with L' ih, 
cases ih, existsi (L' : list (formPA agents)), split, 
exact ih_left, exact imp_imp_iff_imp.mp ih_right}
end

-- Lemma 5 from class notes
lemma five : 
  ∀ Γ : ctxPA agents, ∀ φ : formPA agents, ¬ ax_consist (Γ ∪ φ) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfPA ∅ (fin_conj L' ⊃ ¬φ) :=
begin
intro Γ, intro φ, intro h1, simp at *, rw ax_consist at h1, 
push_neg at h1,
cases h1 with L h1,
have h2 : (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfPA ∅ (fin_conj L ⊃ ⊥) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfPA ∅ (fin_conj L' ⊃ (φ ⊃ ⊥)), from five_helper Γ φ L ⊥,
cases h1,
have h3 : (∀ (ψ : formPA agents), ψ ∈ L → ψ ∈ Γ ∨ ψ = φ), 
{intros ψ this, specialize h1_left ψ this, exact or.swap h1_left},
specialize h2 h3, apply h2, rw fin_ax_consist at h1_right, rw not_not at h1_right,
exact h1_right,
end


lemma six_helper (Γ : ctxPA agents) (h : ax_consist Γ) :
max_ax_consist Γ → ∀ φ : formPA agents, φ ∈ Γ ∨ (¬φ) ∈ Γ :=
begin
intros h1 φ, rw or_iff_not_and_not, by_contradiction h2,
cases h2 with h2l h2r, rw max_ax_consist at h1,
cases h1 with h1l h1r, clear h, 
have h2 := h1r (Γ ∪ φ), have h3 := h1r (Γ ∪ ¬φ),
simp at h3, have h4 : ¬ax_consist (Γ ∪ ¬φ), 
{apply h3, from set.ssubset_insert h2r},
have h5 : ¬ax_consist (Γ ∪ φ), 
{simp at *, apply h2, from set.ssubset_insert h2l}, 
clear h2 h3, simp at *, have h6 := five Γ φ _, have h7 := five Γ (¬φ) _, 
cases h6 with L' h6, cases h7 with L h7, cases h6 with h6l h6r,
cases h7 with h7l h7r,
have h8 : prfPA ∅ ((fin_conj L' & fin_conj L) ⊃ ((¬φ) & ¬¬φ)), 
from imp_and_and_imp (mp (mp pl4 h6r) h7r),
rw ax_consist at h1l,
have h12: prfPA ∅ ((fin_conj (L' ++ L)) ⊃ ⊥), 
from cut (mp pl6 fin_conj_append) (cut h8 (mp pl5 contra_equiv_false)),
specialize h1l (L' ++ L), rw fin_ax_consist at h1l,
have h13: (∀ (ψ : formPA agents), ψ ∈ L' ++ L → ψ ∈ Γ), 
intro ψ, specialize h6l ψ, specialize h7l ψ, intro h13,
rw list.mem_append at h13, cases h13, exact h6l h13, exact h7l h13,
specialize h1l h13, exact absurd h12 h1l,
exact h4,
exact h5,
end

-- lemma 6 from class notes
lemma six (Γ : ctxPA agents) (h : ax_consist Γ) :
max_ax_consist Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬φ) ∈ Γ) :=
begin 
simp, split, 
intro h1, intro φ, 
split, exact six_helper Γ h h1 φ,
{rw ←not_and, by_contradiction h2,
cases h2 with h2 h3,
rw ax_consist at h,
specialize h ([φ, ¬φ]), simp at *,
have h4 : (∀ (ψ : formPA agents), ψ = φ ∨ ψ = ¬φ → ψ ∈ Γ), 
{intros ψ h4, cases h4, subst h4, exact h2, subst h4, exact h3},
specialize h h4, rw fin_ax_consist at h, 
have h5 : prfPA ∅ (¬fin_conj [φ, ¬φ]), from fin_conj_simp φ, 
exact absurd h5 h},
intro h1, rw max_ax_consist, split, exact h,
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
existsi ([ψ,¬ψ] : list (formPA agents)),
simp, split, intros φ h7, cases h7, subst h7, exact h4, 
subst h7, exact h6, rw fin_ax_consist, rw not_not,
exact fin_conj_simp ψ
end

lemma ex1help {Γ : ctxPA agents} {φ : formPA agents} {L L' : list (formPA agents)} :
  (∀ ψ ∈ L, ψ ∈ Γ) → prfPA ∅ (fin_conj L ⊃ φ) → (∀ ψ ∈ L', ψ ∈ (insert φ Γ)) 
  → ∃ L'' : list (formPA agents), (∀ ψ ∈ L'', ψ ∈ Γ) ∧ prfPA ∅ (fin_conj L'' ⊃ fin_conj L') :=
begin
intros h1 h2 h3, induction L',
existsi ([] : list (formPA agents)),
split,
intros ψ h4, exact false.elim h4,
exact iden,
simp at *, cases h3 with h3 h4,
specialize L'_ih h4,
cases L'_ih with L'' L'_ih,
cases L'_ih with ih1 ih2,
cases h3, 
existsi (L''++L : list (formPA agents)),
split,
simp at *, intros ψ h2,
cases h2 with h2 h5,
exact ih1 ψ h2,
exact h1 ψ h5,
subst h3, 
exact (cut (mp pl6 fin_conj_append) (cut (mp pl5 and_switch) (imp_and_and_imp (mp (mp pl4 h2) ih2)))),
existsi (L'_hd::L'' : list (formPA agents)),
split, simp at *, split, exact h3, exact ih1,
exact imp_and_imp ih2
end

lemma exercise1 {Γ : ctxPA agents} {φ : formPA agents} {L : list (formPA agents)} :
  max_ax_consist Γ → (∀ ψ ∈ L, ψ ∈ Γ) → prfPA ∅ (fin_conj L ⊃ φ) → φ ∈ Γ :=
begin
intros h1 h2 h3, 
by_contradiction h4, 
rw max_ax_consist at h1,
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
rw ax_consist at h1, 
have h7 := ex1help h2 h3 h5,
cases h7 with L'' h7,
cases h7 with h7 h8,
specialize h1 L'' h7, apply h1,
exact cut h8 h6
end

lemma max_dn (Γ : ctxPA agents) (h : max_ax_consist Γ) (φ : formPA agents) :
  φ ∈ Γ ↔ (¬¬φ) ∈ Γ :=
begin
split, intro h1, 
have h2 : (∀ ψ ∈ [φ], ψ ∈ Γ) → prfPA ∅ (fin_conj [φ] ⊃ (¬¬φ)) → (¬¬φ) ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) dni), 
intro h1,
have h2 : (∀ ψ ∈ [¬¬φ], ψ ∈ Γ) → prfPA ∅ (fin_conj [¬¬φ] ⊃ φ) → φ ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) dne), 
end

lemma max_notiff (Γ : ctxPA agents) (h : max_ax_consist Γ) (φ : formPA agents) :
  φ ∉ Γ ↔ (¬φ) ∈ Γ :=
begin
split, intro h1,
have h2 : ax_consist Γ, from max_imp_ax h, 
have h3 : ∀ φ : formPA agents, φ ∈ Γ ∨ (¬φ) ∈ Γ, from six_helper Γ h2 h,
specialize h3 φ, cases h3, exact absurd h3 h1, exact h3,
intro h1,
have h2 : ax_consist Γ, from max_imp_ax h, 
have h3 : max_ax_consist Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬φ) ∈ Γ), 
  from six Γ h2,
cases h3, specialize h3_mp h (¬φ), simp at *,
cases h3_mp with mp1 mp2, specialize mp2 h1,
have h4 : φ ∈ Γ ↔ (¬¬φ) ∈ Γ, from max_dn Γ h φ,
rw ←not_iff_not at h4, cases h4, apply h4_mpr, exact mp2
end

lemma max_imp_1 {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  max_ax_consist Γ → (φ ∈ Γ → ψ ∈ Γ) → (φ ⊃ ψ) ∈ Γ :=
begin
intros h1 h2, rw imp_iff_not_or at h2,
cases h2,
have h3 : (∀ χ ∈ [¬φ], χ ∈ Γ) → prfPA ∅ (fin_conj [¬φ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
simp at *, apply h3, 
exact (max_notiff Γ h1 φ).mp h2,
repeat {rw fin_conj at *},
have h4 : prfPA ∅ ((¬φ) ⊃ (φ ⊃ ψ)), from and_right_imp.mp exfalso,
exact cut (mp pl5 phi_and_true) h4,
have h3 : (∀ χ ∈ [ψ], χ ∈ Γ) → prfPA ∅ (fin_conj [ψ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
simp at *, 
apply h3, exact h2, exact (cut (mp pl5 phi_and_true) pl1),
end

lemma max_imp_2 {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  max_ax_consist Γ → (φ ⊃ ψ) ∈ Γ → φ ∈ Γ → ψ ∈ Γ :=
begin
intros h1 h2 h3,
have h4 : (∀ χ ∈ [φ, (φ ⊃ ψ)], χ ∈ Γ) → prfPA ∅ (fin_conj [φ, (φ ⊃ ψ)] ⊃ ψ) → ψ ∈ Γ, from exercise1 h1,
simp at *, apply h4, intros χ h5, cases h5, subst h5, exact h3, subst h5, exact h2,
repeat {rw fin_conj},
exact and_right_imp.mpr (mp pl5 phi_and_true)
end

lemma max_conj_1 {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  max_ax_consist Γ → (φ ∈ Γ ∧ ψ ∈ Γ) → (φ & ψ) ∈ Γ :=
begin
intros h1 h2, cases h2,
have h3 : (∀ χ ∈ [φ], χ ∈ Γ) → prfPA ∅ (fin_conj [φ] ⊃ (ψ ⊃ (φ & ψ))) → (ψ ⊃ (φ & ψ)) ∈ Γ, 
  from exercise1 h1,
simp at *, specialize h3 h2_left,
repeat {rw fin_conj at *},
have h5 : prfPA ∅ ((φ&¬⊥)⊃(ψ⊃φ&ψ)),
exact (cut (mp pl5 phi_and_true) pl4), 
specialize h3 h5,
have h6 : (ψ ⊃ (φ & ψ)) ∈ Γ → ψ ∈ Γ → (φ & ψ) ∈ Γ, from max_imp_2 h1,
apply h6, exact h3, exact h2_right
end

lemma max_conj_2 {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → φ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfPA ∅ (fin_conj [(φ & ψ)] ⊃ φ) → φ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2, repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) pl5)
end

lemma max_conj_3 {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → ψ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfPA ∅ (fin_conj [(φ & ψ)] ⊃ ψ) → ψ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2, repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) pl6)
end


lemma max_translate {Γ : ctxPA agents} {φ : formPA agents} : 
  max_ax_consist Γ → (φ ∈ Γ ↔ (to_PA (translate φ)) ∈ Γ) :=
begin
intro h1,
induction φ,
repeat 
{split,
repeat
{intro h2,
exact h2}},
repeat {rename φ_φ φ, rename φ_ψ ψ,
rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ},
intro h2, 
cases ih_φ,

repeat {sorry},
-- need exercise 1
end

end consistPA