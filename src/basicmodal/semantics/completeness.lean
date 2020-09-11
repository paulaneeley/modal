import basicmodal.semantics.consistency
local attribute [instance] classical.prop_decidable

open prfK

namespace canonical

def canonical (AX : ctx) [hax : sem_cons AX] : frame := 
{ 
  states := {xΓ : ctx // max_ax_consist AX xΓ},
  h := begin have h1 := max_ax_exists AX hax, choose Γ h1 using h1, exact ⟨⟨Γ, h1⟩⟩ end,
  rel := λ xΓ yΔ, ∀ φ : form, □φ ∈ xΓ.val → φ ∈ yΔ.val
}
#check canonical

def val_canonical (AX : ctx) [hax : sem_cons AX] : nat → (canonical AX).states → Prop :=
  λ n, λ xΓ : (canonical AX).states, (p n) ∈ xΓ.val

lemma existence (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) :
  ∀ φ, ◇φ ∈ xΓ.val → ∃ yΔ : (canonical AX).states, φ ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ := sorry

lemma truth (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) : 
  ∀ φ, forces (canonical AX) (val_canonical AX) xΓ φ ↔ (φ ∈ xΓ.val) :=
begin
intro φ, induction φ with n φ ψ ih_φ ih_ψ φ ψ ih_φ ih_ψ φ ih_φ,
split, intro h1, exact false.elim h1,
intro h1, 
have h2 : (¬form.bot) ∉ xΓ.val, 
sorry,
repeat {rw forces, rw val_canonical}, sorry,
split, intro h1, cases h1 with h1 h2, cases ih_φ,
specialize ih_φ_mp h1, cases ih_ψ,
specialize ih_ψ_mp h2, sorry,
intro h1, split, repeat {sorry}
end

theorem completeness (K : ctx) (φ : form) : sem_csq K φ → prfK K φ :=
begin
rw ←not_imp_not, intro h1,
have h2 : ax_consist K {¬φ}, 
{simp at *, rw ax_consist, intros L h2, rw fin_ax_consist,
have h3 : L = [¬φ], simp at *, sorry,
subst h3, simp at *, rw fin_conj, rw fin_conj, simp at *, 
have h4 : prfK K ((¬(¬φ)) ⊃ (¬(¬φ)&¬⊥)), sorry,
have h6 : prfK K (φ ⊃ (¬(¬φ)&¬⊥)), simp at *,
sorry, sorry},
have h3 : ∃ Γ', max_ax_consist K Γ' ∧ {¬φ} ⊆ Γ', from lindenbaum K {¬φ} h2,
simp at *,
cases h3 with Γ' h3, cases h3 with h3 h4, sorry
end


end canonical