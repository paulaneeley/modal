/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.languageDEL del.syntax.syntaxDEL data.set.basic
local attribute [instance] classical.prop_decidable

variables {agents : Type}
open prfPA


---------------------- Helper Lemmas ----------------------

namespace PAlemma


lemma iden {Γ : ctxPA agents} {φ : formPA agents} :
  prfPA Γ (φ ⊃ φ) :=
begin
exact mp (mp (@pl2 _ _ φ (φ ⊃ φ) φ) pl1) pl1
end


lemma prtrue {Γ : ctxPA agents} : prfPA Γ ¬⊥ :=
begin
exact iden
end


lemma weak {Γ : ctxPA agents} {φ ψ : formPA agents} :
  prfPA Γ φ → prfPA (Γ ∪ ψ) φ :=
begin
intro h,
induction h,
{apply ax, exact (set.mem_insert_of_mem _ h_h)},
{exact pl1},
{exact pl2},
{exact pl3},
{exact pl4},
{exact pl5},
{exact pl6},
{exact pl7},
{exact kdist},
{exact truth},
{exact posintro},
{exact negintro},
{apply mp,
  {exact h_ih_hpq},
  {exact h_ih_hp}},
{exact nec h_ih},
{exact atomicbot},
{exact atomicperm},
{exact announceneg},
{exact announceconj},
{exact announceimp},
{exact announceknow},
{exact announcecomp}
end


lemma pr {Γ : ctxPA agents} {φ : formPA agents} :
  prfPA (Γ ∪ φ) φ :=
begin
apply ax;
apply or.intro_left;
simp
end


lemma cut {Γ : ctxPA agents} {φ ψ χ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA Γ (ψ ⊃ χ) → prfPA Γ (φ ⊃ χ) :=
begin
intros h1 h2,
exact mp (mp pl2 (mp pl1 h2)) h1
end


lemma conv_deduction {Γ : ctxPA agents} {φ ψ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA (Γ ∪ φ) ψ :=
begin
intro h, 
exact mp (weak h) pr 
end


lemma hs1 {Γ : ctxPA agents} {φ ψ χ : formPA agents} :
  prfPA Γ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) :=
begin
exact (mp (mp pl2 (mp pl1 pl2)) pl1)
end


lemma likemp {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  prfPA Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)) :=
begin
exact (mp (mp hs1 (mp pl2 iden)) pl1)
end


lemma dne {Γ : ctxPA agents} {φ : formPA agents} :
prfPA Γ ((¬¬φ) ⊃ φ) :=
begin
have h1 : prfPA Γ (φ ⊃ (φ ⊃ φ)), from pl1,
exact (cut (cut pl1 (cut pl7 pl7)) (mp likemp h1))
end


lemma dni {Γ : ctxPA agents} {φ : formPA agents} : prfPA Γ (φ ⊃ ¬¬φ) :=
begin
exact mp pl7 dne
end


lemma imp_if_imp_imp {Γ : ctxPA agents} {φ ψ χ : formPA agents} : prfPA Γ (φ ⊃ χ) → prfPA Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 pl1)) h1
end


lemma cut1 {Γ : ctxPA agents} {φ ψ χ θ : formPA agents} :
  prfPA Γ (θ ⊃ (φ ⊃ ψ)) → prfPA Γ (ψ ⊃ χ) → prfPA Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
exact (cut h1) (mp pl2 (mp pl1 h2))
end


lemma imp_switch {Γ : ctxPA agents} {φ ψ χ : formPA agents} : prfPA Γ (φ ⊃ (ψ ⊃ χ)) → prfPA Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 (mp pl2 h1))) pl1
end


lemma l2 {Γ : ctxPA agents} {φ ψ χ : formPA agents} : prfPA Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
exact (mp (mp pl2 (cut pl2 hs1)) (mp pl1 pl1))
end


lemma hs2 {Γ : ctxPA agents} {φ ψ χ : formPA agents} :
  prfPA Γ ((φ ⊃ ψ) ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ χ))) :=
begin
exact (mp l2 hs1)
end


lemma cut2 {Γ : ctxPA agents} {φ ψ χ θ : formPA agents} :
  prfPA Γ (φ ⊃ ψ) → prfPA Γ (θ ⊃ (ψ ⊃ χ)) → prfPA Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {Γ : ctxPA agents} {φ ψ : formPA agents} :
  prfPA Γ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) :=
begin
exact mp pl2 (imp_switch iden)
end


lemma imp_imp_iff_imp {Γ : ctxPA agents} {θ φ ψ : formPA agents} : 
  prfPA Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfPA Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 pl1}
end


lemma imp_shift {Γ : ctxPA agents} {θ φ ψ χ : formPA agents} : 
  prfPA Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfPA Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 pl1 pl2)}
end


lemma left_and_imp {Γ : ctxPA agents} {φ ψ χ : formPA agents} :
  prfPA Γ (ψ ⊃ ((φ & ψ) ⊃ χ)) → prfPA Γ ((φ & ψ) ⊃ χ) :=
begin
intro h1,
exact mp double_imp (cut pl6 h1)
end


lemma and_right_imp {Γ : ctxPA agents} {φ ψ χ : formPA agents} : 
  prfPA Γ ((φ & ψ) ⊃ χ) ↔ prfPA Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, 
{intro h1,
exact mp (cut2 pl1 pl2) (cut1 pl4 h1)},
intro h1,
exact left_and_imp (cut2 pl5 h1)
end


lemma not_and_subst {φ ψ χ : formPA agents} {Γ : ctxPA agents} : prfPA Γ (φ ↔ ψ) → (prfPA Γ ¬(χ & φ) ↔ prfPA Γ ¬(χ & ψ)) :=
begin
intro h1, split, 
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl6 h1)) (cut pl5 pl4))))},
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl5 h1)) (cut pl5 pl4))))},
end


lemma not_contra {Γ : ctxPA agents} {φ : formPA agents} : 
  prfPA Γ ¬(φ & ¬φ) :=
begin
exact mp (mp pl3 (cut dne pl6)) (cut dne pl5)
end


lemma phi_and_true {Γ : ctxPA agents} {φ : formPA agents} : prfPA Γ ((φ&(¬⊥)) ↔ φ) :=
begin
exact (mp (mp pl4 pl5) (mp (imp_switch pl4) prtrue))
end


lemma imp_and_and_imp {Γ : ctxPA agents} {φ ψ χ θ : formPA agents} : 
  prfPA Γ (((φ ⊃ ψ) & (χ ⊃ θ))) → prfPA Γ (((φ & χ) ⊃ (ψ & θ))) :=
begin
intro h,
exact (mp double_imp (cut (cut pl5 (mp pl5 h)) (cut2 (cut pl6 (mp pl6 h)) pl4)))
end


lemma not_contra_equiv_true {Γ : ctxPA agents} {φ : formPA agents} : 
  prfPA Γ (¬(φ & ¬φ) ↔ ¬⊥) :=
begin
exact (mp (mp pl4 (mp pl1 prtrue)) (mp pl1 not_contra))
end


lemma contrapos {Γ : ctxPA agents} {φ ψ : formPA agents} :
  prfPA Γ ((¬ψ) ⊃ (¬φ)) ↔ prfPA Γ (φ ⊃ ψ) :=
begin
split,
intro h1,
exact mp pl7 h1,
intro h1,
exact mp (cut (cut (mp hs1 dni) (mp hs2 dne)) pl7) h1,
end


lemma iff_not {Γ : ctxPA agents} {φ ψ : formPA agents} :
  prfPA Γ (φ ↔ ψ) → prfPA Γ (¬ψ ↔ ¬φ) :=
begin
intro h1,
have h2 : prfPA Γ (φ ⊃ ψ), from mp pl5 h1,
have h3 : prfPA Γ (ψ ⊃ φ), from mp pl6 h1,
rw ←contrapos at h2,
rw ←contrapos at h3,
exact (mp (mp pl4 h2) h3)
end


lemma contra_equiv_false {Γ : ctxPA agents} {φ : formPA agents} : 
  prfPA Γ ((φ & ¬φ) ↔ ⊥) :=
begin
have h1 := iff_not not_contra_equiv_true,
exact (mp (mp pl4 (cut dni (cut (mp pl6 h1) dne))) (cut dni (cut (mp pl5 h1) dne)))
end


lemma and_switch {Γ : ctxPA agents} {φ ψ : formPA agents} : prfPA Γ ((φ & ψ) ↔ (ψ & φ)) :=
begin
exact (mp (mp pl4 (mp double_imp (cut pl5 (imp_switch (cut pl6 pl4))))) 
(mp double_imp (cut pl5 (imp_switch (cut pl6 pl4)))))
end


lemma imp_and_imp {Γ : ctxPA agents} {φ ψ χ : formPA agents} : 
  prfPA Γ (φ ⊃ ψ) → prfPA Γ  ((χ & φ) ⊃ (χ & ψ)) :=
begin
intros h1,
exact imp_and_and_imp (mp (mp pl4 iden) h1)
end


lemma iff_iff_and_iff {Γ : ctxPA agents} {φ ψ χ θ : formPA agents} : 
  prfPA Γ (φ ↔ χ) → prfPA Γ (ψ ↔ θ) → prfPA Γ ((φ & ψ) ↔ (χ & θ)) := 
begin
intros h1 h2,
exact mp (mp pl4 (imp_and_and_imp (mp (mp pl4 (mp pl5 h1)) (mp pl5 h2)))) 
  (imp_and_and_imp (mp (mp pl4 (mp pl6 h1)) (mp pl6 h2)))
end


lemma and_commute {Γ : ctxPA agents} {φ ψ χ : formPA agents} : prfPA Γ (((φ & ψ) & χ) ↔ (φ & (ψ & χ))) :=
begin
exact mp (mp pl4 (mp double_imp (imp_imp_iff_imp.mp 
  (cut (cut pl5 pl6) (cut2 pl6 (cut1 pl4 (imp_switch (cut (cut pl5 pl5) pl4)))))))) 
  (mp double_imp (imp_imp_iff_imp.mp (cut (cut pl6 pl5) 
  (imp_switch (cut pl5 (cut1 pl4 (cut2 (cut pl6 pl6) pl4)))))))
end


lemma demorgans {Γ : ctxPA agents} {φ ψ : formPA agents} : 
  prfPA Γ (¬(φ & ψ)) ↔ prfPA Γ (φ ⊃ ¬ψ) :=
begin
split,
intro h1,
exact (and_right_imp.mp (mp (contrapos.mpr (mp pl5 and_switch)) h1)),
intro h1,
exact (mp (contrapos.mpr (mp pl5 and_switch)) (and_right_imp.mpr h1))
end


lemma explosion {Γ : ctxPA agents} {ψ : formPA agents} : prfPA Γ (⊥ ⊃ ψ) :=
begin
apply contrapos.mp, exact (mp pl1 iden)
end


lemma exfalso {Γ : ctxPA agents} {φ ψ : formPA agents} : prfPA Γ ((φ & ¬φ) ⊃ ψ) :=
begin
exact cut not_contra explosion
end


lemma box_dn {Γ : ctxPA agents} {φ : formPA agents} {a : agents}  : prfPA Γ ((¬K a φ) ↔ ¬(K a (¬¬φ))) :=
begin
exact mp (mp pl4 (contrapos.mpr (mp kdist (nec dne)))) (contrapos.mpr (mp kdist (nec dni)))
end


lemma dual_equiv1 {Γ : ctxPA agents} {φ : formPA agents} {a : agents} : prfPA Γ ((K a φ) ↔ (¬(¬K a ¬(¬φ)))) :=
begin
exact mp (mp pl4 (cut (contrapos.mp (mp pl6 box_dn)) dni)) 
  (cut dne (contrapos.mp (mp pl5 box_dn)))
end


end PAlemma