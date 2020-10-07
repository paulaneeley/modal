-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import basicmodal.language basicmodal.syntax.syntax data.set.basic

open prfK
local attribute [instance] classical.prop_decidable


---------------------- Helper Lemmas ----------------------


lemma iden {Γ : ctx} {φ : form} :
  prfK Γ (φ ⊃ φ) :=
begin
exact mp (mp (@pl2 _ φ (φ ⊃ φ) φ) pl1) pl1
end

lemma prtrue {Γ : ctx} : prfK Γ ⊤ :=
begin
exact iden
end


lemma weak {Γ : ctx} {φ ψ : form} :
  prfK Γ φ → prfK (Γ un ψ) φ :=
begin
  intro h,
  induction h,
  { apply ax,
    exact (set.mem_insert_of_mem _ h_h) },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { exact pl4 },
  { exact pl5 },
  { exact pl6 },
  { exact pl8 },
  { exact kdist },
  { apply mp,
    { exact h_ih_hpq },
    { exact h_ih_hp } },
  { exact nec h_ih }
end


lemma pr {Γ : ctx} {φ : form} :
  prfK (Γ un φ) φ :=
begin
apply ax;
apply or.intro_left;
simp
end


lemma cut {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ) :=
begin
intros h1 h2,
exact mp (mp pl2 (mp pl1 h2)) h1
end


lemma conv_deduction {Γ : ctx} {φ ψ : form} :
  prfK Γ (φ ⊃ ψ) → prfK (Γ un φ) ψ :=
begin
intro h, 
exact mp (weak h) pr 
end


lemma hs1 {Γ : ctx} {φ ψ χ : form} :
  prfK Γ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) :=
begin
exact (mp (mp pl2 (mp pl1 pl2)) pl1)
end


lemma likemp {Γ : ctx} {φ ψ : form} : 
  prfK Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)) :=
begin
exact (mp (mp hs1 (mp pl2 iden)) pl1)
end


lemma dne {Γ : ctx} {φ : form} :
prfK Γ ((¬¬φ) ⊃ φ) :=
begin
have h1 : prfK Γ (φ ⊃ (φ ⊃ φ)), from pl1,
have h2 : prfK Γ (((¬¬(φ ⊃ (φ ⊃ φ))) ⊃ (¬¬φ)) ⊃ ((¬φ) ⊃ ¬(φ ⊃ (φ ⊃ φ)))), from pl8,
have h3 : prfK Γ (((¬φ) ⊃ ¬(φ ⊃ (φ ⊃ φ))) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ φ)), from pl8,
have h4 : prfK Γ (((¬¬(φ ⊃ (φ ⊃ φ))) ⊃ (¬¬φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ φ)), from cut h2 h3,
have h5 : prfK Γ ((¬¬φ) ⊃ ((¬¬(φ ⊃ (φ ⊃ φ))) ⊃ (¬¬φ))), from pl1,
have h6 : prfK Γ ((¬¬φ) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ φ)), from cut h5 h4,
have h7 : prfK Γ ((φ ⊃ (φ ⊃ φ)) ⊃ (((φ ⊃ (φ ⊃ φ)) ⊃ φ) ⊃ φ)), from likemp,
have h8 : prfK Γ (((φ ⊃ (φ ⊃ φ)) ⊃ φ) ⊃ φ), from mp h7 h1,
have h9 : prfK Γ ((¬¬φ) ⊃ φ), from cut h6 h8,
exact h9
end


lemma dni {Γ : ctx} {φ : form} : prfK Γ (φ ⊃ ¬¬φ) :=
begin
have h1 : prfK Γ ((¬¬(¬φ)) ⊃ (¬φ)), from dne,
exact mp pl8 h1
end


lemma imp_if_imp_imp {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ χ) → prfK Γ (φ ⊃ (ψ ⊃ χ)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 pl1)) h1
end


lemma cut1 {Γ : ctx} {φ ψ χ θ : form} :
  prfK Γ (θ ⊃ (φ ⊃ ψ)) → prfK Γ (ψ ⊃ χ) → prfK Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
have h3 : prfK Γ (φ ⊃ ψ) → prfK Γ (ψ ⊃ χ) → prfK Γ (φ ⊃ χ), from cut,
have h4 : prfK Γ (θ ⊃ (φ ⊃ ψ)) → prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)) → prfK Γ (θ ⊃ (φ ⊃ χ)), from cut,
specialize h4 h1,
have h5 : prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)), from mp pl2 (mp pl1 h2),
specialize h4 h5,
exact h4
end


lemma imp_switch {Γ : ctx} {φ ψ χ : form} : prfK Γ (φ ⊃ (ψ ⊃ χ)) → prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
intro h1,
have h2 : prfK Γ (ψ ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))), from mp pl1 (mp pl2 h1),
have h3 : prfK Γ ((ψ ⊃ (φ ⊃ ψ)) ⊃ (ψ ⊃ (φ ⊃ χ))), from mp pl2 h2,
exact mp h3 pl1
end


lemma l2 {Γ : ctx} {φ ψ χ : form} : prfK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
exact (mp (mp pl2 (cut pl2 hs1)) (mp pl1 pl1))
end


lemma hs2 {Γ : ctx} {φ ψ χ : form} :
  prfK Γ ((φ ⊃ ψ) ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ χ))) :=
begin
exact (mp l2 hs1)
end


lemma cut2 {Γ : ctx} {φ ψ χ θ : form} :
  prfK Γ (φ ⊃ ψ) → prfK Γ (θ ⊃ (ψ ⊃ χ)) → prfK Γ (θ ⊃ (φ ⊃ χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {Γ : ctx} {φ ψ : form} :
  prfK Γ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) :=
begin
have h1 : prfK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ ψ)) → prfK Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)), from imp_switch,
specialize h1 iden,
exact mp pl2 h1
end


lemma imp_imp_iff_imp {Γ : ctx} {θ φ ψ : form} : 
  prfK Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ prfK Γ (θ ⊃ (φ ⊃ ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 pl1}
end


lemma imp_shift {Γ : ctx} {θ φ ψ χ : form} : 
  prfK Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ prfK Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 pl1 pl2)}
end


lemma left_and_imp {Γ : ctx} {φ ψ χ : form} :
  prfK Γ (ψ ⊃ ((φ & ψ) ⊃ χ)) → prfK Γ ((φ & ψ) ⊃ χ) :=
begin
intro h1,
exact mp double_imp (cut pl6 h1)
end


lemma and_right_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ ((φ & ψ) ⊃ χ) ↔ prfK Γ (ψ ⊃ (φ ⊃ χ)) :=
begin
split, 
{intro h1,
exact mp (cut2 pl1 pl2) (cut1 pl4 h1)},
intro h1,
exact left_and_imp (cut2 pl5 h1)
end


lemma not_and_subst {φ ψ χ : form} {Γ : ctx} : 
  prfK Γ (φ ↔ ψ) → (prfK Γ ¬(χ & φ) ↔ prfK Γ ¬(χ & ψ)) :=
begin
intro h1, split, 
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl6 h1)) 
  (cut pl5 pl4))))},
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl5 h1)) 
  (cut pl5 pl4))))},
end


lemma not_contra {Γ : ctx} {φ : form} : 
  prfK Γ ¬(φ & ¬φ) :=
begin
exact mp (mp pl3 (cut dne pl6)) (cut dne pl5)
end


lemma phi_and_true {Γ : ctx} {φ : form} : prfK Γ ((φ&¬⊥) ↔ φ) :=
begin
exact (mp (mp pl4 pl5) (mp (imp_switch pl4) prtrue))
end


lemma imp_and_and_imp {Γ : ctx} {φ ψ χ θ : form} : 
  prfK Γ (((φ ⊃ ψ) & (χ ⊃ θ))) → prfK Γ (((φ & χ) ⊃ (ψ & θ))) :=
begin
intro h,
exact (mp double_imp (cut (cut pl5 (mp pl5 h)) (cut2 (cut pl6 (mp pl6 h)) pl4)))
end


lemma not_contra_equiv_true {Γ : ctx} {φ : form} : 
  prfK Γ (¬(φ & ¬φ) ↔ ⊤) :=
begin
exact (mp (mp pl4 (mp pl1 prtrue)) (mp pl1 not_contra))
end


lemma contrapos {Γ : ctx} {φ ψ : form} :
  prfK Γ ((¬ψ) ⊃ (¬φ)) ↔ prfK Γ (φ ⊃ ψ) :=
begin
split,
intro h1,
exact mp pl8 h1,
intro h1,
exact mp (cut (cut (mp hs1 dni) (mp hs2 dne)) pl8) h1,
end


lemma iff_not {Γ : ctx} {φ ψ : form} :
  prfK Γ (φ ↔ ψ) → prfK Γ (¬ψ ↔ ¬φ) :=
begin
intro h1,
have h2 : prfK Γ (φ ⊃ ψ), from mp pl5 h1,
have h3 : prfK Γ (ψ ⊃ φ), from mp pl6 h1,
rw ←contrapos at h2,
rw ←contrapos at h3,
exact (mp (mp pl4 h2) h3)
end


lemma contra_equiv_false {Γ : ctx} {φ : form} : 
  prfK Γ ((φ & ¬φ) ↔ ⊥) :=
begin
have h1 : prfK Γ (¬⊤ ↔ ¬¬(φ & ¬φ)), from iff_not not_contra_equiv_true,
exact (mp (mp pl4 (cut dni (cut (mp pl6 h1) dne))) (cut dni (cut (mp pl5 h1) dne)))
end


lemma and_switch {Γ : ctx} {φ ψ : form} : prfK Γ ((φ & ψ) ↔ (ψ & φ)) :=
begin
exact (mp (mp pl4 (mp double_imp (cut pl5 (imp_switch (cut pl6 pl4))))) 
(mp double_imp (cut pl5 (imp_switch (cut pl6 pl4)))))
end


lemma and_commute {Γ : ctx} {φ ψ χ : form} : prfK Γ (((φ & ψ) & χ) ↔ (φ & (ψ & χ))) :=
begin
exact mp (mp pl4 (mp double_imp (imp_imp_iff_imp.mp 
  (cut (cut pl5 pl6) (cut2 pl6 (cut1 pl4 (imp_switch (cut (cut pl5 pl5) pl4)))))))) 
  (mp double_imp (imp_imp_iff_imp.mp (cut (cut pl6 pl5) 
  (imp_switch (cut pl5 (cut1 pl4 (cut2 (cut pl6 pl6) pl4)))))))
end


lemma imp_and_imp {Γ : ctx} {φ ψ χ : form} : 
  prfK Γ (φ ⊃ ψ) → prfK Γ ((χ & φ) ⊃ (χ & ψ)) :=
begin
intros h1,
have h2 := imp_and_and_imp,
specialize h2 (mp (mp pl4 iden) h1), exact h2
end

lemma not_nphi_imp_phi {Γ : ctx} {φ : form} : prfK Γ (¬((¬φ) ⊃ φ)) := sorry

lemma demorgans {Γ : ctx} {φ ψ : form} : prfK Γ ((¬(φ & ψ)) ↔ (φ ⊃ ¬ψ)) := sorry

-- lemma imp_and {Γ : ctx} {φ ψ : form} : prfK Γ ((¬(φ ⊃ ψ)) ↔ (φ & ¬ψ)) := sorry

lemma explosion {Γ : ctx} {ψ : form} : prfK Γ (⊥ ⊃ ψ) :=
begin
apply contrapos.mp, exact (mp pl1 iden)
end

lemma exfalso {Γ : ctx} {φ ψ : form} : prfK Γ ((φ & ¬φ) ⊃ ψ) :=
begin
exact cut not_contra explosion
end

lemma box_dne {Γ : ctx} {φ : form} : prfK Γ ((¬□φ) ⊃ ¬(□(¬¬φ))) :=
begin
exact (contrapos.mpr (mp kdist (nec dne)))
end

