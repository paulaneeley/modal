-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import basicmodal.language basicmodal.syntax.syntax 
import basicmodal.semantics.semantics basicmodal.paths
import data.set.basic

open form
local attribute [instance] classical.prop_decidable


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


def euclidean := ∀ ⦃x y z⦄, r x y → r x z → r y z 

def ref_class : set (frame) := { f : frame | reflexive (f.rel) }
def symm_class : set (frame) := { f : frame | symmetric (f.rel) }
def trans_class : set (frame) := { f : frame | transitive (f.rel) }
def euclid_class : set (frame) := { f : frame | euclidean (f.rel) }
def equiv_class : set (frame) := { f : frame | equivalence (f.rel) }
def ref_trans_class : set (frame) := ref_class ∩ trans_class


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


theorem symm_def : defines ((p 0) ⊃ (□ (◇ (p 0)))) (symm_class) :=
begin
simp, rw defines, intro f, split,
{exact symm_helper (p 0) f},
{intro h1, by_contradiction h2, rw symm_class at h2,
rw set.nmem_set_of_eq at h2, rw symmetric at h2,
rw not_forall at h2, cases h2 with x h2, rw not_forall at h2,
cases h2 with y h2, rw not_imp at h2,
let v := λ n x, n = 0 ∧ ¬ f.rel y x,
specialize h1 v x,
simp [forces, v] at h1,
specialize h1 h2.right y h2.left, 
apply h1,
intros y1 h3 h4, exact absurd h3 h4}
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


