import basicmodal.semantics.consistency basicmodal.syntax.soundness
local attribute [instance] classical.prop_decidable

open prfK
namespace canonical


def canonical (AX : ctx) [hax : sem_cons AX] : frame := 
{ 
  states := {xΓ : ctx // max_ax_consist AX xΓ},
  h := begin have h1 := max_ax_exists AX hax, choose Γ h1 using h1, exact ⟨⟨Γ, h1⟩⟩ end,
  rel := λ xΓ yΔ, ∀ φ : form, □φ ∈ xΓ.val → φ ∈ yΔ.val
}


def val_canonical (AX : ctx) [hax : sem_cons AX] : nat → (canonical AX).states → Prop :=
  λ n, λ xΓ : (canonical AX).states, (p n) ∈ xΓ.val


lemma existence (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) :
  ∀ φ, ◇φ ∈ xΓ.val → ∃ yΔ : (canonical AX).states, φ ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ :=
begin
simp, intros φ h1,
let Γbox : ctx := {ψ : form | □ψ ∈ xΓ.val},
have h1 : ax_consist AX (Γbox ∪ φ), by_contradiction h2,
have h3 : ∃ L', (∀ ψ ∈ L', ψ ∈ Γbox) ∧ prfK AX (fin_conj L' ⊃ ¬φ), 
  from five AX Γbox φ h2,
cases h3 with L h3, cases h3 with h3 h4,
have h5 : prfK AX (□(fin_conj L ⊃ ¬φ)), from nec h4,
have h6 : prfK AX (□(fin_conj L) ⊃ □(¬φ)), from mp kdist h5,
simp at *, sorry, simp at *, sorry
end


lemma truth (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) : 
  ∀ φ, forces (canonical AX) (val_canonical AX) xΓ φ ↔ (φ ∈ xΓ.val) :=
begin
intro φ, induction φ with n φ ψ ih_φ ih_ψ φ ψ ih_φ ih_ψ φ ih_φ,
split, intro h1, exact false.elim h1,
intro h1, 
rw forces, 
sorry,
repeat {rw forces, rw val_canonical}, 
split, intro h1, cases h1 with h1 h2, cases ih_φ,
specialize ih_φ_mp h1, cases ih_ψ,
specialize ih_ψ_mp h2, 
sorry,
intro h1, split, repeat {sorry}
end



lemma comphelper (AX : ctx) (φ : form) (hax : sem_cons AX) : 
  ¬ prfK AX φ → ax_consist AX {¬φ} :=
begin
intro h1, rw ax_consist, intros L h2,
rw fin_ax_consist, simp at *,
induction L, rw fin_conj, simp, by_contradiction h3,
have h4 : prfK AX ⊥, from mp dne h3,
have h5 : ¬prfK AX ⊥, from nprfalse AX hax,
exact absurd h4 h5, 
simp at *, 
cases h2 with h2 h3, subst h2,
specialize L_ih h3, rw fin_conj,
sorry
end 

theorem completeness (hax : sem_cons ∅) (φ : form) : 
  global_sem_csq ∅ φ → prfK ∅ φ :=
begin
rw ←not_imp_not, intro h1,
have h2 : ax_consist ∅ {¬φ}, from comphelper ∅ φ hax h1,
have h3 : ∃ Γ', max_ax_consist ∅ Γ' ∧ {¬φ} ⊆ Γ', from lindenbaum ∅ {¬φ} h2,
simp at *, cases h3 with Γ' h3, cases h3 with h3 h4, 
rw global_sem_csq, rw not_forall, let f := canonical, use f ∅,
rw not_forall, let v := val_canonical, use v ∅, rw not_forall,
let xΓ' : (f ∅).states := ⟨Γ', h3⟩, use xΓ', 
rw not_imp, split,
intros y ψ h5, 
have h6 : ψ ∉ ∅, {exact set.not_mem_empty ψ},
exact absurd h5 h6,
have h5 : forces (f ∅) (v ∅) xΓ' (¬φ) ↔ ((¬φ) ∈ xΓ'.val), 
  from truth ∅ hax xΓ' ¬φ,
simp at *,
cases h5 with h5 h6,
have h7 : ¬forces (f ∅) (v ∅) xΓ' φ ↔ forces (f ∅) (v ∅) xΓ' ¬φ, 
  from not_forces_imp (f ∅) (v ∅) xΓ' φ,
simp at *, cases h7 with h7 h8, apply h8, apply h6, exact h4,
end

end canonical

theorem T_completeness (φ : form) : F_valid φ ref_class → prfK T_axioms φ := sorry

theorem S4_completeness (φ : form) : F_valid φ ref_trans_class → prfK S4_axioms φ := sorry

theorem S5_completeness (φ : form) : F_valid φ equiv_class → prfK S5_axioms φ := sorry