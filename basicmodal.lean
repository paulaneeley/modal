import data.set.basic ..my_new_lean_stuff.paths order.zorn
local attribute [instance] classical.prop_decidable

---------------------- Basic Language ----------------------

-- Def 2.1, pg 12


inductive form : Type
  | bot  : form
  | var  (n : nat) : form 
  | and  (φ ψ : form) : form
  | impl (φ ψ : form) : form
  | box  (φ : form) : form


open form

-- Notation
local notation `⊥`:80   := form.bot
local prefix `p`:80     := form.var
infix `&`:79      := form.and
infix `⊃`         := form.impl
notation `¬` φ    := form.impl φ form.bot
notation `⊤`:80   := ¬ form.bot
notation φ `∨` ψ  := (¬φ ⊃ ψ)
notation `□`:80   := form.box 
notation `◇`:80   := λ φ, ¬(□(¬φ))


variables {states : Type}


---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx : Type := set (form)
notation Γ `∪` φ := set.insert φ Γ

-- Proof system, pg. 26
inductive prfK : ctx → form → Prop 
| ax {Γ} {φ} (h : φ ∈ Γ) : prfK Γ φ
| pl1 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
--| pl3 {Γ} {φ ψ}          : prfK Γ (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ φ)
| pl6 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ ψ)
| pl7 {Γ} {φ}            : prfK Γ (¬¬φ ⊃ φ)
| kdist {Γ} {φ ψ}        : prfK Γ ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
| mp {Γ} {φ ψ} 
  (hpq: prfK Γ (φ ⊃ ψ)) 
  (hp : prfK Γ φ)      : prfK Γ ψ
| nec {Γ} {φ} 
  (hp: prfK Γ φ)       : prfK Γ (□ φ)
    
open prfK


-- Some helper lemmas for the proof system:
lemma iden {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ φ) :=
  mp (mp (@pl2 _ φ (φ ⊃ φ) φ) pl1) pl1
--begin
--have h1 : prfK Γ (φ ⊃ ((φ ⊃ φ) ⊃ φ)), from pl1, 
--have h2 : prfK Γ ((φ ⊃ ((φ ⊃ φ) ⊃ φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ))), from pl2,
--have h3 : prfK Γ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ)), from mp h2 h1,
--have h4 : prfK Γ (φ ⊃ (φ ⊃ φ)), from pl1,
--have h5 : prfK Γ (φ ⊃ φ), from mp h3 h4,
--exact h5
--end



/- structural lemmas -/
lemma sub_weak {Γ Δ : ctx} {φ : form} :
  (prfK Δ φ) → (Δ ⊆ Γ) → (prfK Γ φ) :=
begin
  intros h s,
  induction h,
  { apply ax, exact s h_h },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq s },
    {exact h_ih_hp s} },
  { exact nec (h_ih s) }
end

lemma weak {Γ : ctx} {φ ψ : form} :
  prfK Γ φ → prfK (Γ ∪ ψ) φ :=
begin
  intro h, dsimp,
  induction h,
  { apply ax,
    exact (set.mem_insert_of_mem _ h_h) },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq },
    { exact h_ih_hp } },
  { exact nec h_ih }
end

lemma contr {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ φ) ψ → prfK (Γ ∪ φ) ψ :=
begin
  generalize eq : (Γ ∪ φ ∪ φ) = Γ',
  dsimp at *,
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert},
    { exact h } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl)}
end

lemma exg {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ ψ) χ → prfK (Γ ∪ ψ ∪ φ) χ :=
  begin
  generalize eq : (Γ ∪ φ ∪ ψ) = Γ',
  dsimp at *,
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert_of_mem _ _,
      apply set.mem_insert _ _ },
      { cases set.eq_or_mem_of_mem_insert h with h' h',
        { rw h', apply set.mem_insert _ _ },
        { apply set.mem_insert_of_mem _ _,
          apply set.mem_insert_of_mem _ _, 
          exact h' } } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
    { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl)}
end


/- subcontext lemmas -/
lemma subctx_ax {Γ Δ : ctx} {φ : form} :
   Δ ⊆ Γ → prfK Δ φ → prfK Γ φ :=
begin
  intros s h,
  induction h,
  { apply ax (s h_h) },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq s },
    { exact h_ih_hp s } },
  { exact nec (h_ih s) }
end

lemma subctx_contr {Γ Δ : ctx} {φ : form}:
   Δ ⊆ Γ → prfK (Γ ∪ Δ) φ → prfK Γ φ :=
begin
  generalize eq : Γ ∪ Δ = Γ',
  intros s h,
  induction h; subst eq,
  { cases h_h,
    { exact ax h_h },
    { exact ax (s h_h) } },
  { exact pl1 },
  { exact pl2 },
  --{ exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl7 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact nec (h_ih rfl) }
end


/- right-hand side rules of inference -/
lemma pr {Γ : ctx} {φ : form} :
  prfK (Γ ∪ φ) φ :=
by apply ax; apply or.intro_left; simp

lemma pr1 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ ψ) φ :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

lemma pr2 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ ψ) ψ :=
by apply ax; apply or.intro_left; simp

lemma by_mp1 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) ψ :=
mp pr2 pr1

lemma by_mp2 {Γ : ctx} {φ ψ : form} :
  prfK (Γ ∪ (φ ⊃ ψ) ∪ φ) ψ :=
mp pr1 pr2

lemma cut {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ) :=
λ hpq hqr, mp (mp pl2 (mp pl1 hqr)) hpq

lemma conv_deduction {Γ : ctx} {φ ψ : form} :
  prfK Γ (φ ⊃ ψ) → prfK (Γ ∪ φ) ψ :=
λ h, mp (weak h) pr 

lemma not_pp {Γ : ctx} {φ : form} :
  prfK Γ ((¬φ) ⊃ (φ ⊃ φ)) :=
  begin
  have h1 : prfK Γ ((φ ⊃ φ) ⊃ ((¬φ) ⊃ (φ ⊃ φ))), from pl1,
  have h2 : prfK Γ (φ ⊃ φ), from iden,
  have h3 : prfK Γ ((¬φ) ⊃ (φ ⊃ φ)), from mp h1 h2,
  exact h3
  end


/- left-hand side rules of inference -/
lemma mp_in_ctx_left {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ ψ) χ → prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) χ :=
begin
  generalize eq : (Γ ∪ φ ∪ ψ) = Γ',
  dsimp at *,
  intros h,
  induction h; subst eq,
  { cases h_h,
    { rw h_h,
      exact by_mp1 },
    { cases h_h,
      { rw h_h,
        exact pr1 },
      { apply ax,
        apply set.mem_insert_of_mem _ _,
        apply set.mem_insert_of_mem _ _, exact h_h } } },
    { exact pl1 },
    { exact pl2 },
    --{ exact pl3 },
    { exact pl4 },
    { exact pl5 },
    { exact pl6 },
    { exact pl7 },
    { exact kdist },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact nec (h_ih rfl) }
end

lemma mp_in_ctx_right {Γ : ctx} {φ ψ χ : form} :
  prfK (Γ ∪ φ ∪ (φ ⊃ ψ)) χ → prfK (Γ ∪ φ ∪ ψ) χ :=
begin
  generalize eq : (Γ ∪ φ ∪ (φ ⊃ ψ)) = Γ',
  dsimp at *,
  intros h,
  induction h; subst eq,
  { cases h_h, 
    { subst h_h,
      exact mp pl1 pr },
    { cases h_h,
      { subst h_h, 
        exact pr1 },
      { exact weak (weak (ax h_h)) } } },    
    { exact pl1 },
    { exact pl2 },
    --{ exact pl3 },
    { exact pl4 },
    { exact pl5 },
    { exact pl6 },
    { exact pl7 },
    { exact kdist },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact nec (h_ih rfl) }
end

/-lemma dne {Γ : ctx} {φ : form} :
  prfK Γ ((¬¬φ) ⊃ φ) := 
  begin
  have h1 : prfK Γ (((¬φ) ⊃ (¬¬φ)) ⊃ (((¬φ) ⊃ (¬φ) ⊃ φ))), from pl3,
  have h2 : prfK Γ ((¬¬φ) ⊃ ((¬φ) ⊃ (¬¬φ))), from pl1,
  have h3 : prfK Γ ((¬¬φ) ⊃ (((¬φ) ⊃ (¬φ) ⊃ φ))), from cut h2 h1,
  have h4 : prfK Γ ((¬¬φ) ⊃ ((¬φ) ⊃ (¬φ))), from not_pp,
  have h5 : prfK Γ (((¬¬φ) ⊃ (((¬φ) ⊃ (¬φ)) ⊃ φ)) ⊃ (((¬¬φ) ⊃ ((¬φ) ⊃ (¬φ))) ⊃ ((¬¬φ) ⊃ φ))), from pl2,
  have h6 : prfK Γ (((¬¬φ) ⊃ ((¬φ) ⊃ (¬φ))) ⊃ ((¬¬φ) ⊃ φ)), from mp h5 h3,
  have h7 : prfK Γ ((¬¬φ) ⊃ φ), from mp h6 h4,
  exact h7
  end-/

lemma dni {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ (¬¬φ)) := sorry



---------------------- Semantics ----------------------

-- definition of relational frame
structure frame :=
(states : Type)
(h : inhabited states)
(rel : states → states → Prop)

-- definition of forces
def forces (f : frame) (v : nat → f.states → Prop) : f.states → form → Prop
  | x (bot)    := false
  | x (var n)  := v n x
  | x (and φ ψ)  := (forces x φ) ∧ (forces x ψ)
  | x (impl φ ψ) := (forces x φ) → (forces x ψ)
  | x (box φ)  := ∀ y, f.rel x y → forces y φ

-- φ is valid in a model M = (f,v)
def m_valid (φ : form) (f : frame) 
  (v : nat → f.states → Prop) := 
  ∀ x, forces f v x φ

-- φ is valid in a frame f
def f_valid (φ : form) (f : frame) := 
  ∀ v x, forces f v x φ

-- φ is valid in a class of frames F = set f
def F_valid (φ : form) (F : set (frame)) := 
  ∀ f ∈ F, ∀ v x, forces f v x φ

-- φ is universally valid (valid in all frames)
def u_valid (φ : form) := 
  ∀ f v x, forces f v x φ

-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def forces_ctx (f : frame) (v : nat → f.states → Prop) 
  (Γ : ctx) : f.states → Prop := λ x, ∀ φ, φ ∈ Γ → forces f v x φ

inductive sem_csq2 (Γ : ctx) (φ :form) : Prop
| is_true (f : ∀ (F : frame) (v : nat → F.states → Prop) (x : F.states),
forces_ctx F v Γ x → forces F v x φ) : sem_csq2

-- φ is a global semantic consequence of Γ
def sem_csq (Γ : ctx) (φ : form) :=
  ∀ f v x, (∀ ψ ∈ Γ, m_valid ψ f v) → forces f v x φ



---------------------- Frame Definability ----------------------


-- φ defines F (a class of frames)
def defines (φ : form) (F : set (frame)) := 
  ∀ f, f ∈ F ↔ f_valid φ f


---------------------- Definability Proofs ----------------------

section
open classical
open set

variable f : frame
variables {α : Type} (r : α → α → Prop)
variables {states}


def euclidean := ∀ ⦃x y z⦄, r x y → r x z → r y z 

def ref_class : set (frame) := { f : frame | reflexive (f.rel) }
def symm_class : set (frame) := { f : frame | symmetric (f.rel) }
def trans_class : set (frame) := { f : frame | transitive (f.rel) }
def euclid_class : set (frame) := { f : frame | euclidean (f.rel) }
def equiv_class : set (frame) := { f : frame | equivalence (f.rel) }
def ref_trans_class : set (frame) := ref_class ∩ trans_class
def ref_trans__euc_class : set (frame) := ref_class ∩ trans_class ∩ euclid_class


lemma ref_helper : ∀ φ f, f ∈ ref_class → f_valid ((box φ) ⊃ φ) f :=
begin
intros φ f h v x h1, 
apply h1 x, apply h x
end

theorem ref_def : defines ((□ (p 0)) ⊃ (p 0)) (ref_class) :=
begin
intro f,
split,
{exact ref_helper (p 0) f},
{intros h x, let v := λ n y, n = 0 ∧ f.rel x y,
specialize h v x,
simp [forces, v] at h, exact h}
end


lemma symm_helper : ∀ φ f, f ∈ symm_class → f_valid (φ ⊃ (□ (◇φ))) f :=
begin
dsimp, intros φ f h v x h1 y h2 h3,
by_contradiction h4,
specialize h3 x, have h4 := h h2, 
have h5 := h3 h4, exact h5 h1
end

-- TODO:
theorem symm_def : defines ((p 0) ⊃ (□ (◇ (p 0)))) (symm_class) :=
begin
-- direct:
/-intro f,
split,
{exact symm_helper (p 0) f},
{intros h1 x y h2, let v := λ n y, n = 0 ∧ f.rel x y, 
dsimp at h1, specialize h1 v y,
simp [forces, v] at h1, specialize h1 h2 x, sorry}
-/
-- by contradiction:
simp, rw defines, intro f, split,
{exact symm_helper (p 0) f},
{intro h1, by_contradiction h2, rw symm_class at h2,
rw set.nmem_set_of_eq at h2, rw symmetric at h2,
rw not_forall at h2, cases h2 with x h2, rw not_forall at h2,
cases h2 with y h2, rw not_imp at h2, cases h2,
let v := λ n x, n = 0 ∧ ¬ f.rel y x, specialize h1 v x,
have h3 : v 0 x,
{sorry}, 
specialize h1 h3 y h2_left, rw forces at h1, rw forces at h1,
have h4 : (∀ (y_1 : f.states), f.rel y y_1 → forces f v y_1 (¬p 0)),
{intros w h4 h5, have h6 : ¬f.rel y w, 
{sorry},
 exact absurd h4 h6}, 
specialize h1 h4, exact h1}
end


lemma trans_helper : ∀ φ f, f ∈ trans_class → f_valid (□ φ ⊃ □ (□ φ)) f :=
begin
intros φ f h v x h1 y h3 z h4, 
have h5 := h h3, have h6 := h5 h4,
specialize h1 z, apply h1 h6
end


lemma euclid_helper : ∀ φ f, f ∈ euclid_class → f_valid (◇ φ ⊃ □ (◇ φ)) f :=
begin
dsimp, intros φ f h v x h1 y h2 h3,
apply h1, intros z h4,
have h6 := h h2, specialize h6 h4,
clear h, specialize h3 z h6, exact h3
end

end


---------------------- Frame Undefinability ----------------------


-- F (a class of frames) is undefinable
def undefinable (F : set (frame)) :=
  ∀ φ, ¬ defines φ F


-- The theory of x in m
def theory_at (f : frame) (v : nat → f.states → Prop) (x : f.states) : 
  set (form) := { φ : form | forces f v x φ}


-- Invariance under disjoint union
variables {α β : Type}
def frame.rel.dunion (r1 : α → α → Prop) (r2 : β → β → Prop) : 
  (sum α β) → (sum α β) → Prop
  | (sum.inl a1) (sum.inl a2) := r1 a1 a2
  | (sum.inr b1) (sum.inr b2) := r2 b1 b2
  | _ _                       := false

def val_dunion {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) : nat → (sum f1.states f2.states) → Prop
  | n (sum.inl x1) := v1 n x1
  | n (sum.inr x2) := v2 n x2

def frame.dunion (f1 f2 : frame) : frame :=
{
  states := sum f1.states f2.states,
  h := ⟨sum.inl f1.h.default⟩, 
  rel := frame.rel.dunion (f1.rel) (f2.rel)
}

theorem invariance_dunion (f1 f2 : frame) (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (x1 : f1.states) : 
  theory_at f1 v1 x1 = theory_at (f1.dunion f2) (val_dunion v1 v2) (sum.inl x1) :=
begin
ext φ, revert x1, induction φ,
{intro x1, split, repeat {intro h, rw theory_at at *, exact h}},
{intro x1, split, repeat {intro h, rw theory_at at *, exact h}},
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, 
intro x1, split, intro h, split, specialize ih_φ x1, 
cases ih_φ, cases h, exact ih_φ_mp h_left,
specialize ih_ψ x1, cases ih_ψ, cases h, exact ih_ψ_mp h_right,
intro h, split, specialize ih_φ x1, cases ih_φ, cases h, exact ih_φ_mpr h_left,
specialize ih_ψ x1, cases ih_ψ, cases h, exact ih_ψ_mpr h_right},
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ,
intro x1, split, intro h, specialize ih_φ x1, cases ih_φ, specialize ih_ψ x1,
cases ih_ψ, intro h1, have h2 := ih_φ_mpr h1, have h3 := h h2, exact ih_ψ_mp h3, 
intro h, specialize ih_φ x1, specialize ih_ψ x1, cases ih_φ, cases ih_ψ, 
intro h1, have h2 := ih_φ_mp h1, have h3 := h h2, exact ih_ψ_mpr h3},
{rename φ_φ φ, intro x1, split, intros h s h1, cases s, specialize φ_ih s, 
cases φ_ih, specialize h s, have h2 := h h1, exact φ_ih_mp h2,
apply false.elim h1, intros h s h1, specialize φ_ih s, cases φ_ih,
specialize h (sum.inl s), have h2 := h h1, exact φ_ih_mpr h2}
end



-- Invariance under generated submodels
def frame.gen_subframe (f : frame) (x : f.states) : frame :=
{
  states := { y // reachable (f.rel) x y},
  h := ⟨⟨x, ref_close x (f.rel)⟩⟩,
  rel := λ x1 x2, (f.rel) x1.val x2.val
}

def val_gen_subframe (f : frame) (x : f.states)
  (v : nat → f.states → Prop) : nat → (frame.gen_subframe f x).states → Prop :=
  λ n, λ y, v n y.val

theorem invariance_gen_submodel (f : frame) (v : ℕ → f.states → Prop) 
  (x : f.states) (y : (frame.gen_subframe f x).states) :
  theory_at f v y.val = theory_at (f.gen_subframe x) (val_gen_subframe f x v) y :=
begin
ext φ, revert y, induction φ,
{intro y, split, repeat {intro h1, exact h1}}, 
{intro y, split, repeat {intro h1, exact h1}},
{rename φ_ih_φ ih_φ, rename φ_ih_ψ ih_ψ, rename φ_φ φ, 
rename φ_ψ ψ, intro y, specialize ih_φ y, specialize ih_ψ y, 
cases ih_φ, cases ih_ψ, split, intro h1, cases h1, split, 
exact ih_φ_mp h1_left, exact ih_ψ_mp h1_right, intro h1, 
cases h1, split, exact ih_φ_mpr h1_left, exact ih_ψ_mpr h1_right}, 
{rename φ_φ φ, rename φ_ψ ψ, rename φ_ih_φ ih_φ, 
rename φ_ih_ψ ih_ψ, intro y, specialize ih_φ y, specialize ih_ψ y, 
cases ih_φ, cases ih_ψ, split, intros h1 h2, have h3 := ih_φ_mpr h2, 
have h4 := h1 h3, exact ih_ψ_mp h4, intros h1 h2, 
have h3 := ih_φ_mp h2, have h4 := h1 h3, exact ih_ψ_mpr h4},
{rename φ_φ φ, intro y, split, {intros h1 z h2, specialize φ_ih z,
cases φ_ih, specialize h1 z.val, have h3 := h1 h2, exact φ_ih_mp h3}, 
{intro h1, intros z h2, 
have h3 := reach_right x y.val z f.rel (and.intro y.property h2),
specialize φ_ih ⟨z, h3⟩, cases φ_ih, specialize h1 ⟨z, h3⟩, 
have h4 := h1 h2, exact φ_ih_mpr h4}}
end




-- Invariance under bisimulation
def base {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (x1 : f1.states) (x2 : f2.states) := 
  ∀ n, v1 n x1 ↔ v2 n x2

def forth {f1 f2 : frame} (bisim : f1.states → f2.states → Prop) 
  (x1 : f1.states) (x2 : f2.states) := 
  ∀ y1, f1.rel x1 y1 → (∃ y2 : f2.states, f2.rel x2 y2 ∧ bisim y1 y2)

def back {f1 f2 : frame} (bisim : f1.states → f2.states → Prop) 
  (x1 : f1.states) (x2 : f2.states) := 
  ∀ y2, f2.rel x2 y2 → (∃ y1 : f1.states, f1.rel x1 y1 ∧ bisim y1 y2)

-- Bisimulation between M1 = (f1,v1) and M2 = (f2,v2)
def is_bisimulation {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) := ∀ x1 x2,
  bisim x1 x2 → (base v1 v2 x1 x2 ∧ forth bisim x1 x2 ∧ back bisim x1 x2)

theorem invariance_bisim {f1 f2 : frame} (v1 : nat → f1.states → Prop) 
  (v2 : nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) 
  (h : is_bisimulation v1 v2 bisim) (x1 : f1.states) (x2 : f2.states) : 
  bisim x1 x2 → theory_at f1 v1 x1 = theory_at f2 v2 x2 :=
begin
intro h1, ext φ, revert x1 x2, induction φ,
{intros x1 x2 h1, split, intro h2, exact h2, intro h2, exact h2}, 
{intros x1 x2 h1, specialize h x1 x2 h1, cases h, 
specialize h_left φ, cases h_left, split, intro h2, 
exact h_left_mp h2, intro h2, exact h_left_mpr h2}, 
{intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1, 
cases φ_ih_φ, cases φ_ih_ψ, split, intro h2, cases h2, split, 
exact φ_ih_φ_mp h2_left, exact φ_ih_ψ_mp h2_right, intro h2, 
cases h2, split, exact φ_ih_φ_mpr h2_left, exact φ_ih_ψ_mpr h2_right}, 
{intros x1 x2 h1, specialize φ_ih_φ x1 x2 h1, specialize φ_ih_ψ x1 x2 h1,
cases φ_ih_φ, cases φ_ih_ψ, split, intros h2 h3, have h4 := φ_ih_φ_mpr h3,
have h5 := h2 h4, exact φ_ih_ψ_mp h5, intros h2 h3, have h4 := φ_ih_φ_mp h3,
have h5 := h2 h4, exact φ_ih_ψ_mpr h5},
{rename φ_φ φ, intros x1 x2 h1, specialize h x1 x2 h1, cases h with h4 h5,
cases h5 with h5 h6, split,
{intros h2 y2 h3, specialize h6 y2 h3, cases h6 with y1 h6, 
cases h6 with h6 h7, specialize h2 y1 h6, specialize φ_ih y1 y2 h7, 
cases φ_ih, exact φ_ih_mp h2},
{intros h2 y1 h3, specialize h5 y1 h3, cases h5 with y2 h5, 
cases h5 with h5 h7, specialize h2 y2 h5, specialize φ_ih y1 y2 h7, 
cases φ_ih, exact φ_ih_mpr h2}}
end



-- Invariance using surjective bounded morphisms
open function

def is_bddmorphism {f1 f2 : frame} (g : f1.states → f2.states) := 
  ∀ x1 : f1.states, forth (λ x1 x2, (g x1) = x2) x1 (g x1) ∧ back (λ x1 x2, (g x1) = x2) x1 (g x1)

def is_surjbddmorphism {f1 f2 : frame} (g : f1.states → f2.states) 
  := surjective g ∧ is_bddmorphism g


theorem pull_back {f1 f2 : frame} (g : f1.states → f2.states) (h : is_surjbddmorphism g) :
  ∀ φ, ¬ f_valid φ f2 → ¬ f_valid φ f1 :=
begin
intros φ h1, rw f_valid at *, rw not_forall at *, cases h1 with v2 h1,
rw not_forall at h1, cases h1 with y h1,
let v1 := (λ n x, v2 n (g x)), use v1, rw not_forall,
cases h with hl hr, specialize hl y, cases hl with x hl, 
existsi (x : f1.states), have h3 := invariance_bisim v1 v2 (λ x y, g x = y),
have h4 : is_bisimulation v1 v2 (λ (x : f1.states) (y : f2.states), g x = y), 
{intros x1 x2 h2, split,
{intro n, split, intro h, subst h2, apply h, intro h, subst h2, apply h},
specialize hr x1, cases hr, split,
have h5 : forth (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2, 
from eq.subst h2 hr_left, exact h5, 
have h5 : back (λ (x1 : f1.states) (x2 : f2.states), g x1 = x2) x1 x2,
from eq.subst h2 hr_right, exact h5},
specialize h3 h4 x y hl, intro h2, apply h1,
rw set.subset.antisymm_iff at h3, cases h3, 
rw set.subset_def at h3_left,
specialize h3_left φ h2, exact h3_left,
end

lemma invariance_pull_back (F : set (frame)) {f1 f2 : frame} 
  (h1 : f1 ∈ F) (h2 : f2 ∉ F) : 
  (∃ g : f1.states → f2.states, is_surjbddmorphism g) → undefinable F :=
begin
intro h, cases h with g h,
intro φ, by_contradiction h3, 
have h4 := h3 f1, specialize h3 f2, 
rw ←not_iff_not at h3, cases h3,
have h5 := h3_mp h2, 
cases h4, have h7 := h4_mp h1, 
have h8 := pull_back g h φ h5, 
exact h8 h7
end




---------------------- Expressivity ---------------------------


--def expressible (θ : form) := ∃ ψ : form, u_valid ((ψ ⊃ θ) & (θ ⊃ ψ)) 


---------------------- Soundness ----------------------


lemma not_forces_imp :  ∀ f v x φ, 
  (¬(forces f v x φ)) ↔ (forces f v x (¬φ)) :=
begin
intros f v x φ, split, 
{intros h1 h2, exact h1 h2},
{intros h1 h2, specialize h1 h2, exact h1}
end

theorem soundness (Γ : ctx) 
  (φ : form) : prfK Γ φ → sem_csq Γ φ :=
begin
intro h,
induction h,
{intros f v x h, specialize h h_φ, have h1 := h h_h, 
rw m_valid at h1, specialize h1 x, exact h1},
{intros f v x h2 h3 h4, exact h3}, 
{intros f v x h2 h3 h4 h5, apply h3, 
exact h5, apply h4, exact h5}, 
/-{intros f x v h1 h2 h3,
by_contradiction h4,
specialize h2 h4, specialize h3 h4, 
rw ← not_forces_imp at h2, exact h2 h3},-/
{intros f v x h1 h2 h3, simp [forces] at *, 
exact and.intro h2 h3},
{intros f v x h1 h2, exact h2.left},
{intros f v x h1 h2, exact h2.right},
{intros f v x h1 h2, apply h2, intro h3, exact h3},
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



lemma hi {Γ : ctx} {φ : form} {C : set (frame)} : prfK Γ φ → (∀ ψ ∈ Γ, F_valid ψ C) → F_valid φ C :=
begin
intros h1 h2 f h3 v, induction h1,
{intro x, specialize h2 h1_φ h1_h, rw F_valid at h2, specialize h2 f h3 v x, exact h2},
{intros x h4 h5, exact h4},
{intros x h4 h5 h6, have h7 := h4 h6, have h8 := h5 h6, exact h7 h8},
/-{intros x h3 h4, by_contradiction h5, specialize h3 h5, specialize h4 h5, 
rw ← not_forces_imp at h3, exact h3 h4},-/
{intros x h4 h5, exact and.intro h4 h5}, 
{intros x h4, exact h4.left}, 
{intros x h4, exact h4.right}, 
--{intros x h4, exact false.elim h4},
{intros x h4, apply h4, intro h5, exact h5},
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

lemma S5_helper : ∀ φ ∈ S5_axioms, F_valid φ ref_trans__euc_class :=
begin
intros φ h1 f h2 v x,
cases h2 with h2l h2r, 
cases h2l with h2l h2lr,
cases h1 with h1 h3, 
{cases h1, apply T_helper, exact h1, 
exact h2l, cases h1 with ψ h1, subst h1, 
apply trans_helper, exact h2lr},
{cases h3 with ψ h3, dsimp at h3,
subst h3, apply euclid_helper, exact h2r}
end

theorem S5_soundness (φ : form) : prfK (S5_axioms) φ → F_valid φ (ref_trans__euc_class) :=
begin
intro h, apply hi, apply h, apply S5_helper
end



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



-- TODO:
example {Γ : ctx} {φ : form} : 
  prfK Γ ¬(φ & ¬φ) :=
begin
simp, 
have h1 : prfK Γ ((φ & ¬φ) ⊃ φ), from pl5,
have h2: prfK Γ ((φ & ¬φ) ⊃ ¬φ), from pl6,
sorry
end

lemma and_left_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
split,
{intro h, sorry}, 
sorry
end

lemma and_right_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, intro h1, sorry
end

--prfK ... (A > B > C) -> prfK ... (A > C)
lemma imp_if_imp_imp {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ χ) → prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
have h2 : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))), from pl2,
sorry
end

/-
| pl1 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ φ))
| pl2 {Γ} {φ ψ χ}        : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl4 {Γ} {φ ψ}          : prfK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ φ)
| pl6 {Γ} {φ ψ}          : prfK Γ ((φ & ψ) ⊃ ψ)
| pl7 {Γ} {φ}            : prfK Γ (¬¬φ ⊃ φ)
-/

lemma imp_imp_if_imp {Γ : ctx} {θ φ ψ : form} : 
 prfK Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfK Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
sorry
end

lemma imp_shift {Γ : ctx} {θ φ ψ χ : form} : 
 prfK Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfK Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
sorry
end


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