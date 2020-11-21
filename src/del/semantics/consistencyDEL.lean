-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.syntax.syntaxDEL 
import del.semantics.semanticsDEL del.syntax.syntaxlemmasDEL
import del.syntax.soundnessDEL order.zorn data.set.basic data.list.basic
local attribute [instance] classical.prop_decidable

open prfS5
open S5lemma
variables {agents : Type}


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
rw forces_ctx,
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
intro h1, simp at *, by_contradiction h2,
have h3 : prfS5 ∅ form.bot, from mp (mp pl5 contra_equiv_false) (mp (mp pl4 h2) h1),
have h4 : ¬ prfS5 ∅ form.bot, from nprfalse hax,
exact absurd h3 h4
end 

lemma pr_to_notprnot (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
  prfS5 ∅ φ → ¬ prfS5 ∅ (¬φ) :=
begin
have h1 : prfS5 ∅ (¬φ) → ¬ prfS5 ∅ φ, from prnot_to_notpr φ hax,
rw ←not_imp_not at h1, intro h2, apply h1, rw not_not, exact h2,
end 

-- finite conjunction of formulas
def fin_conj : list (form agents) → form agents
  | []  := ¬form.bot
  | (φ::φs) := φ & (fin_conj φs)

-- a few helper lemmas about finite conjunctions
lemma fin_conj_simp {Γ : ctx agents} : ∀ ψ : form agents, prfS5 Γ (¬fin_conj [ψ, ¬ψ]) :=
begin
intro ψ, rw fin_conj, rw fin_conj, rw fin_conj,
have h2 : (prfS5 Γ (((¬ψ)&(¬⊥)) ↔ (¬ψ)) → 
  (prfS5 Γ (¬(ψ & ((¬ψ)&(¬⊥)))) ↔ prfS5 Γ (¬(ψ & (¬ψ))))), 
  from not_and_subst,
simp at h2,
specialize h2 phi_and_true, cases h2,
exact h2_mpr not_contra
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
intro h1, subst h1, rw fin_conj,
have h1 : prfS5 (∅ : ctx agents) (¬(form.bot)), simp at *, exact iden,
by_contradiction h2,
have h3 : prfS5 ∅ form.bot, from mp h2 h1,
have h4 : ¬ prfS5 ∅ form.bot, from nprfalse hax,
exact absurd h3 h4
end 

lemma fin_conj_repeat_helper {θ : form agents} {L : list (form agents)} 
  (hax : sem_cons (∅ : ctx agents) equiv_class) :
  (∀ ψ ∈ L, ψ = θ) → prfS5 ∅ (θ ⊃ fin_conj L) :=
begin
intros h1, induction L,
exact mp pl1 iden,
rw fin_conj, simp at *,
cases h1 with h1 h2,
specialize L_ih h2, subst h1,
exact cut (mp double_imp pl4) (imp_and_and_imp (mp (mp pl4 iden) L_ih)),
end

lemma fin_conj_repeat {φ : form agents} {L : list (form agents)}
  (hax : sem_cons (∅ : ctx agents) equiv_class) :
  (∀ ψ ∈ L, ψ = ¬φ) → prfS5 ∅ (¬fin_conj L) → prfS5 ∅ φ :=
begin
intros h1 h2, induction L,
rw fin_conj at h2,
have h3 := mp dne h2,
have h4 := nprfalse hax,
exact absurd h3 h4,
repeat {rw fin_conj at *}, simp at *,
cases h1 with h1 h3, 
have h5 : prfS5 ∅ ((¬fin_conj L_tl) ⊃ ¬(¬φ)), from contrapos.mpr (fin_conj_repeat_helper hax h3),
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
rw fin_conj, simp at *, rw fin_conj,
exact (mp pl1 (nec prtrue)),
rw list.map, repeat {rw fin_conj},
have h1 := imp_and_imp,
specialize h1 L_ih,
exact (cut h1 fin_conj_box2)
end


lemma listempty {Γ : ctx agents} {L : list (form agents)} :
  (∀ φ ∈ L, φ ∈ Γ) → Γ = ∅ → L = [] := 
begin
intros h1 h2,
by_contradiction h3,
have h4 : L ≠ [] → 0 < L.length, from list.length_pos_of_ne_nil,
specialize h4 h3,
have h5 : 0 < L.length → ∃ a, a ∈ L, from list.exists_mem_of_length_pos,
specialize h5 h4,
cases h5 with φ h5, specialize h1 φ h5,
have h6 : Γ = ∅ → ∀ φ, φ ∉ Γ, from set.eq_empty_iff_forall_not_mem.mp,
specialize h6 h2, specialize h6 φ, exact absurd h1 h6
end


-- consistency for a finite set of formulas L
def fin_ax_consist (L : list (form agents)) := ¬ prfS5 ∅ (fin_conj L ⊃ ⊥)


-- consistency for an arbitrary set of formulas Γ
def ax_consist (Γ : ctx agents) :=
  ∀ L : list (form agents), (∀ ψ ∈ L, ψ ∈ Γ) → fin_ax_consist L


-- Γ is maximally ax-consistent
def max_ax_consist (Γ : ctx agents) := 
  ax_consist Γ ∧ (∀ Γ', Γ ⊂ Γ' → ¬ ax_consist Γ')


lemma max_imp_ax {Γ : ctx agents} : max_ax_consist Γ → ax_consist Γ :=
begin
intro h1, rw max_ax_consist at h1, cases h1, exact h1_left
end


/-Lemma: for every Gamma, phi, for every list L, for every formula b, 
if everything in L is in Gamma or equal to phi, and you can prove conj L ⊃ b, 
then there is a list L', such that everything in L' is in Gamma, and you can 
prove conj L' ⊃ (phi ⊃ b)
-/
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
dsimp [fin_conj] at *, exact imp_if_imp_imp h2},
{intros b h2,
have h1a : ∀ (ψ : form agents), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
  {intros ψ h2, specialize h1 ψ, 
  have h3 := list.subset_cons L_hd L_tl,
  have h4 := list.mem_cons_of_mem L_hd h2, 
  apply h1 h4},
specialize L_ih h1a,
have h1b: L_hd ∈ Γ ∨ L_hd = φ, 
  {apply h1 L_hd, left, refl},
cases h1b, 
have h3 : prfS5 ∅ (fin_conj L_tl ⊃ (L_hd ⊃ b)), 
  from and_right_imp.mp h2,
specialize L_ih (L_hd ⊃ b) h3,
cases L_ih with L' ih, existsi (L_hd::L' : list (form agents)),
cases ih, split, intros ψ h4, cases h4, 
subst h4, exact h1b, 
apply ih_left ψ h4, rw imp_shift at ih_right,
rw ←imp_conj_imp_imp at ih_right, exact ih_right,
have h3 : prfS5 ∅ (fin_conj (L_hd::L_tl) ⊃ b), 
exact h2, exact b,
specialize L_ih (φ ⊃ b),
have h5 : prfS5 ∅ (fin_conj (L_hd :: L_tl) ⊃ b) → 
  prfS5 ∅ (fin_conj L_tl ⊃ (L_hd ⊃ b)), 
  from and_right_imp.mp,
specialize h5 h2,
have h6 : prfS5 ∅ (fin_conj L_tl ⊃ (φ ⊃ b)), 
  from eq.subst h1b h5,
specialize L_ih h6, cases L_ih with L' ih, 
cases ih, existsi (L' : list (form agents)), split, 
exact ih_left, exact imp_imp_iff_imp.mp ih_right}
end

-- Lemma 5 from class notes
lemma five : 
  ∀ Γ : ctx agents, ∀ φ : form agents, ¬ ax_consist (Γ ∪ φ) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L' ⊃ ¬φ) :=
begin
intro Γ, intro φ, intro h1, simp at *, rw ax_consist at h1, 
push_neg at h1,
cases h1 with L h1,
have h2 : (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → prfS5 ∅ (fin_conj L ⊃ ⊥) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L' ⊃ (φ ⊃ ⊥)), from five_helper Γ φ L ⊥,
cases h1,
have h3 : (∀ (ψ : form agents), ψ ∈ L → ψ ∈ Γ ∨ ψ = φ), 
{intros ψ this, specialize h1_left ψ this, exact or.swap h1_left},
specialize h2 h3, apply h2, rw fin_ax_consist at h1_right, rw not_not at h1_right,
exact h1_right,
end


lemma six_helper (Γ : ctx agents) (h : ax_consist Γ) :
max_ax_consist Γ → ∀ φ : form agents, φ ∈ Γ ∨ (¬φ) ∈ Γ :=
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
have h8 : prfS5 ∅ ((fin_conj L' & fin_conj L) ⊃ ((¬φ) & ¬¬φ)), 
from imp_and_and_imp (mp (mp pl4 h6r) h7r),
rw ax_consist at h1l,
have h12: prfS5 ∅ ((fin_conj (L' ++ L)) ⊃ ⊥), 
from cut (mp pl6 fin_conj_append) (cut h8 (mp pl5 contra_equiv_false)),
specialize h1l (L' ++ L), rw fin_ax_consist at h1l,
have h13: (∀ (ψ : form agents), ψ ∈ L' ++ L → ψ ∈ Γ), 
intro ψ, specialize h6l ψ, specialize h7l ψ, intro h13,
rw list.mem_append at h13, cases h13, exact h6l h13, exact h7l h13,
specialize h1l h13, exact absurd h12 h1l,
exact h4,
exact h5,
end

-- lemma 6 from class notes
lemma six (Γ : ctx agents) (h : ax_consist Γ) :
max_ax_consist Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬φ) ∈ Γ) :=
begin 
simp, split, 
intro h1, intro φ, 
split, exact six_helper Γ h h1 φ,
{rw ←not_and, by_contradiction h2,
cases h2 with h2 h3,
rw ax_consist at h,
specialize h ([φ, ¬φ]), simp at *,
have h4 : (∀ (ψ : form agents), ψ = φ ∨ ψ = ¬φ → ψ ∈ Γ), 
{intros ψ h4, cases h4, subst h4, exact h2, subst h4, exact h3},
specialize h h4, rw fin_ax_consist at h, 
have h5 : prfS5 ∅ (¬fin_conj [φ, ¬φ]), from fin_conj_simp φ, 
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
existsi ([ψ,¬ψ] : list (form agents)),
simp, split, intros φ h7, cases h7, subst h7, exact h4, 
subst h7, exact h6, rw fin_ax_consist, rw not_not,
exact fin_conj_simp ψ
end

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
specialize L'_ih h4,
cases L'_ih with L'' L'_ih,
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

lemma max_dn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) :
  φ ∈ Γ ↔ (¬¬φ) ∈ Γ :=
begin
split, intro h1, 
have h2 : (∀ ψ ∈ [φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (¬¬φ)) → (¬¬φ) ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) dni), 
intro h1,
have h2 : (∀ ψ ∈ [¬¬φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬¬φ] ⊃ φ) → φ ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) dne), 
end

lemma max_boxdn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) (a : agents) :
  (¬K a φ) ∈ Γ → (¬ (K a (¬¬φ))) ∈ Γ :=
begin
intro h1,
have h2 : ∀ a, (∀ ψ ∈ [¬ K a φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬ K a φ] ⊃ (¬ (K a (¬¬φ)))) → (¬ (K a (¬¬φ))) ∈ Γ,
  from λ a, exercise1 h,
simp at *, 
specialize h2 a,
apply h2, exact h1, clear h2,
repeat {rw fin_conj at *},
exact (cut (mp pl5 phi_and_true) (mp pl5 box_dn)), 
end

lemma max_notiff (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) :
  φ ∉ Γ ↔ (¬φ) ∈ Γ :=
begin
split, intro h1,
have h2 : ax_consist Γ, from max_imp_ax h, 
have h3 : ∀ φ : form agents, φ ∈ Γ ∨ (¬φ) ∈ Γ, from six_helper Γ h2 h,
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

lemma max_imp_1 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ ∈ Γ → ψ ∈ Γ) → (φ ⊃ ψ) ∈ Γ :=
begin
intros h1 h2, rw imp_iff_not_or at h2,
cases h2,
have h3 : (∀ χ ∈ [¬φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [¬φ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
simp at *, apply h3, 
exact (max_notiff Γ h1 φ).mp h2,
repeat {rw fin_conj at *},
have h4 : prfS5 ∅ ((¬φ) ⊃ (φ ⊃ ψ)), from and_right_imp.mp exfalso,
exact cut (mp pl5 phi_and_true) h4,
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
repeat {rw fin_conj},
exact and_right_imp.mpr (mp pl5 phi_and_true)
end

lemma max_conj_1 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ ∈ Γ ∧ ψ ∈ Γ) → (φ & ψ) ∈ Γ :=
begin
intros h1 h2, cases h2,
have h3 : (∀ χ ∈ [φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (ψ ⊃ (φ & ψ))) → (ψ ⊃ (φ & ψ)) ∈ Γ, 
  from exercise1 h1,
simp at *, specialize h3 h2_left,
repeat {rw fin_conj at *},
have h5 : prfS5 ∅ ((φ&¬⊥)⊃(ψ⊃φ&ψ)),
exact (cut (mp pl5 phi_and_true) pl4), 
specialize h3 h5,
have h6 : (ψ ⊃ (φ & ψ)) ∈ Γ → ψ ∈ Γ → (φ & ψ) ∈ Γ, from max_imp_2 h1,
apply h6, exact h3, exact h2_right
end

lemma max_conj_2 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → φ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ φ) → φ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2, repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) pl5)
end

lemma max_conj_3 {Γ : ctx agents} {φ ψ : form agents} : 
  max_ax_consist Γ → (φ & ψ) ∈ Γ → ψ ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ ψ) → ψ ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2, repeat {rw fin_conj},
exact (cut (mp pl5 phi_and_true) pl6)
end

-- Γ is maximally AX-consistent iff it is AX-consistent and for 
-- every AX-consistent set Γ', if Γ ⊆ Γ', then Γ = Γ'
lemma max_equiv (Γ : ctx agents) : max_ax_consist Γ ↔ ax_consist Γ ∧ 
  ∀ Γ', ax_consist Γ' → Γ ⊆ Γ' → Γ = Γ' :=
begin
split, 
{intro h1, split, rw max_ax_consist at h1, exact h1.left, 
intros Γ' h2 h3, rw set.subset.antisymm_iff, split, exact h3,
by_contradiction h4, rw max_ax_consist at h1, cases h1, 
have h5 := and.intro h3 h4, 
have h6 : Γ ⊂ Γ', from h5,
specialize h1_right Γ' h6, exact h1_right h2}, 
intro h1, cases h1, rw max_ax_consist, split, exact h1_left,
intros Γ' h2, by_contradiction h3, specialize h1_right Γ' h3,
rw set.ssubset_def at h2, cases h2, apply h2_right, rw h1_right h2_left
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
specialize L_ih h2b,
cases L_ih with m ih,
cases ih with h3 ih,
specialize h2 L_hd, 
simp at h2,
cases h2 with m' h2,
cases h2 with h2 h4,
existsi (m' ∪ m : ctx agents), 
have h5 : m' ∪ m ∈ c, 
{have h6 := chain.total_of_refl h1 h3 h2,
cases h6,
have h7 := set.union_eq_self_of_subset_right h6,
exact (eq.substr h7 h2), 
have h7 := set.union_eq_self_of_subset_left h6,
exact (eq.substr h7 h3)},
existsi (h5 : m' ∪ m ∈ c),
intros ψ h6, cases h6,
subst h6, exact set.mem_union_left m h4,
specialize ih ψ h6, exact set.mem_union_right m' ih
end


lemma lindenbaum (Γ : ctx agents) (hax : ax_consist Γ) : 
  ∃ Γ', max_ax_consist Γ' ∧ Γ ⊆ Γ' :=
begin
let P := { Γ'' | Γ'' ⊇ Γ ∧ ax_consist Γ''},
have h : ∀ c ⊆ P, chain (⊆) c → c.nonempty → ∃ub ∈ P, ∀ s ∈ c, s ⊆ ub, 
{intros c h2 h3 h4, use ⋃₀(c), 
have h5 := lindenhelper c h4 h3,
split, 
split,
rw superset,
rw set.nonempty_def at h4,
cases h4 with Γ'' h4,
have h6 := set.mem_of_mem_of_subset h4 h2,
cases h6 with h6 h7,
rw superset at h6,
apply set.subset_sUnion_of_subset c Γ'' h6 h4,
rw ax_consist,
intros L h6,
specialize h5 L h6,
cases h5 with m h5,
cases h5 with h7 h5,
have h8 := set.mem_of_mem_of_subset h7 h2,
cases h8 with h8 h9,
rw ax_consist at h9, apply h9, exact h5,
intros s h7, exact set.subset_sUnion_of_mem h7},
have h1 : Γ ∈ P,
split,
exact set.subset.rfl,
exact hax,
cases zorn_subset₀ P h Γ h1 with Γ' h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
use Γ', split, rw max_equiv, split, apply h2.2, 
intros m h5 h6, symmetry, apply h4 m, split, apply set.subset.trans h2.1 h6,
exact h5, exact h6, apply h2.1
end

-- Corollary 8
lemma max_ax_exists (hax : sem_cons (∅ : ctx agents) equiv_class) : ∃ Γ : ctx agents, max_ax_consist Γ :=
begin
have h1 : ax_consist ∅,
{rw ax_consist, intro L, intro h2, rw fin_ax_consist, 
have h3 := listempty h2, have this : ∅ = ∅, refl, 
specialize h3 this, subst h3, by_contradiction h4, 
have h5 := mp dne, apply nprfalse hax, exact h5 h4},
have h2 : ∃ Γ, max_ax_consist Γ ∧ ∅ ⊆ Γ, from lindenbaum ∅ h1, 
cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : ctx agents), apply h2
end