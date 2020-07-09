-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import language syntax.syntax semantics.semantics syntax.syntaxlemmas order.zorn data.set.basic
local attribute [instance] classical.prop_decidable

open prfK

---------------------- Consistency ----------------------



-- finite conjunction of formulas
def fin_conj : list form → form
  | [] := ⊤
  | (φ::φs) := (φ) & (fin_conj φs)

-- consistency for a finite set of formulas L
def fin_ax_consist (AX : ctx) (L : list form) := ¬ prfK AX (fin_conj L ⊃ ⊥)

-- consistency for an arbitrary set of formulas Γ
def ax_consist (AX Γ : ctx) := 
  ∀ L : list form, (∀ ψ ∈ L, ψ ∈ Γ) → fin_ax_consist AX L



lemma imp_conj_imp_imp {Γ : ctx} {φ ψ χ : form} {L : list form} : 
  prfK Γ ((fin_conj (φ::L)) ⊃ ψ) ↔ prfK Γ (fin_conj L ⊃ (φ ⊃ ψ)) :=
begin
split, 
intro h, dsimp [fin_conj] at h, rw and_right_imp at h, exact h,
intro h, dsimp [fin_conj], rw and_right_imp, exact h
end

lemma fin_conj_cons_imp {Γ : ctx} {φ b : form} {L : list form} : 
 prfK Γ (fin_conj (φ::L) ⊃ (φ ⊃ b)) → prfK Γ (fin_conj L ⊃ (φ ⊃ b)) :=
begin
intro h, dsimp [fin_conj] at h, rw and_right_imp at h,
rw imp_imp_if_imp at h, exact h
end


/-Lemma: for every Gamma, phi, for every list L, for every formula b, 
if everything in L is in Gamma or equal to phi, and you can prove conj L ⊃ b, 
then there is a list L', such that everything in L' is in Gamma, and you can 
prove conj L' ⊃ (phi ⊃ b)
-/
lemma five_helper (AX : ctx) : 
  ∀ Γ : ctx, ∀ φ : form, ∀ L : list form, ∀ b : form, 
  (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfK AX (fin_conj L ⊃ b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfK AX (fin_conj L' ⊃ (φ ⊃ b)) :=
begin
intros Γ φ L b h1 h2, revert b, induction L,
{intros b h2, existsi ([] : list form), split, intros ψ h3, exfalso, 
apply list.not_mem_nil ψ h3, dsimp [fin_conj] at *,
have h3 := imp_if_imp_imp h2, exact h3},
{have h1a : ∀ (ψ : form), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
{intros ψ h2, specialize h1 ψ, 
have h3 := list.subset_cons L_hd L_tl,
have h4 := list.mem_cons_of_mem L_hd h2, 
apply h1 h4},
intros b h2, 
have h1b: L_hd ∈ Γ ∨ L_hd = φ, 
{apply h1 L_hd, left, refl},
specialize L_ih h1a, cases h1b, 
{have h3 : prfK AX (fin_conj L_tl ⊃(L_hd ⊃ b)),
rw imp_conj_imp_imp at h2, exact h2, exact b,
specialize L_ih (L_hd ⊃ b) h3,
cases L_ih with L' ih, existsi (L_hd::L' : list form),
cases ih, split, intros ψ h4, cases h4, 
subst h4, exact h1b, 
apply ih_left ψ h4, rw imp_shift at ih_right,
rw ←imp_conj_imp_imp at ih_right, exact ih_right,
have h3 : prfK AX (fin_conj (L_hd::L_tl) ⊃ b), 
exact h2, exact b},
{have h4 : prfK AX (fin_conj L_tl ⊃ b), {sorry},
specialize L_ih b h4, cases L_ih with L' ih, 
existsi (L' : list form), exact ih}}
end


-- Lemma 5 from class notes
lemma five (AX : ctx) : 
  ∀ Γ : ctx, ∀ φ : form, ¬ ax_consist AX (Γ ∪ φ) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfK AX (fin_conj L' ⊃ ¬φ) :=
begin
intros Γ φ h1, rw ax_consist at h1, dsimp at h1, rw not_forall at h1,
cases h1 with L h1, rw not_imp at h1, cases h1, dsimp at *, 
rw fin_ax_consist at h1_right, rw not_not at h1_right,
existsi (L : list form), split,
intros ψ h, sorry, sorry 
end


-- Γ is maximally ax-consistent
def max_ax_consist (AX Γ : ctx) := 
  ax_consist AX Γ ∧ ∀ Γ' : ctx, Γ ⊂ Γ' → ¬ ax_consist AX Γ' 


-- lemma 6 from class notes
lemma six (AX Γ : ctx) (h : ax_consist AX Γ) : 
  max_ax_consist AX Γ ↔ (∀ φ : form, φ ∈ Γ ∨ (¬φ) ∈ Γ) :=
begin
split,
{intros h1 φ, rw or_iff_not_and_not, by_contradiction h2, 
cases h2 with h2l h2r, rw max_ax_consist at h1, cases h1 with h1l h1r,
clear h, have h2 := h1r (Γ ∪ φ), have h3 := h1r (Γ ∪ ¬φ),
have h4 : ¬ax_consist AX (Γ ∪ ¬φ), {sorry}, have h5 : ¬ax_consist AX (Γ ∪ φ), 
{sorry}, clear h2 h3, have h6 := five AX Γ φ _, have h7 := five AX Γ (¬φ) _, 
cases h6 with L' h6, cases h7 with L h7, dsimp at *, cases h6 with h6l h6r,
cases h7 with h7l h7r, clear h6l h7l, sorry, sorry, sorry},
{intro h1, dsimp at h1, rw max_ax_consist, split, exact h, 
intros Γ' h2, by_contradiction h6, have h3 : ∃ψ ∈ Γ', ψ ∉ Γ, 
from set.exists_of_ssubset h2, cases h3 with ψ h3, cases h3 with h4 h3, 
specialize h1 ψ, cases h1, exfalso, exact h3 h1, 
rw set.ssubset_def at h2, have h5 := set.mem_of_subset_of_mem h2.left h1, 
sorry}
end


-- Γ is maximally AX-consistent iff it is AX-consistent and for 
-- every AX-consistent set Γ', if Γ ⊆ Γ', then Γ = Γ'
lemma max_equiv (AX Γ : ctx) : max_ax_consist AX Γ ↔ ax_consist AX Γ ∧ 
  ∀ Γ', ax_consist AX Γ' → Γ ⊆ Γ' → Γ = Γ' :=
begin
split, 
{intro h1, split, rw max_ax_consist at h1, exact h1.left, 
intros Γ' h2 h3, rw set.subset.antisymm_iff, split, exact h3,
by_contradiction h4, rw max_ax_consist at h1, cases h1, 
have h5 := and.intro h3 h4, rw ←set.ssubset_iff_subset_not_subset at h5,
specialize h1_right Γ' h5, exact h1_right h2}, 
intro h1, cases h1, rw max_ax_consist, split, exact h1_left,
intros Γ' h2, by_contradiction h3, specialize h1_right Γ' h3,
rw set.ssubset_def at h2, cases h2, exact h2_right (h1_right h2_left)
end

#check zorn.zorn_subset
open zorn
lemma lindenbaum (AX Γ : ctx) (hax : ax_consist AX Γ) : ∃ Γ', max_ax_consist AX Γ' ∧ Γ ⊆ Γ' :=
begin
let S := { Γ'' | Γ'' ⊇ Γ ∧ ax_consist AX Γ''},
have h : ∀c ⊆ S, chain (⊆) c → ∃ub ∈ S, ∀ s ∈ c, s ⊆ ub, {sorry},
cases zorn_subset S h with Γ' h1, cases h1 with h1 h2,
use Γ', split, rw max_equiv, split, apply h1.2, 
intros m h3 h4, symmetry, apply h2 m, split, apply set.subset.trans h1.1 h4,
exact h3, exact h4, apply h1.1
end

--Lemma: if c is a chain of sets, L is a list of elements such that 
--every element in L is in Union(c), then there is an element S in C such that every element of L is in S.
-- by induction on L.
-- S := collection of max cons sets
-- m := Γ'