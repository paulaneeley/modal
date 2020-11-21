import del.languageDEL del.semantics.complexitylemmas
variables {agents : Type}

-- Def 7.20, pg. 186, Translation function t
@[simp] def translate : formPA agents → form agents
  | (formPA.bot)     := form.bot
  | (p n)            := form.var n
  | (φ & ψ)          := have _, from tr1 φ ψ, have _, from tr2 φ ψ, form.and (translate φ) (translate ψ)
  | (φ ⊃ ψ)          := have _, from tr1 φ ψ, have _, from tr2 φ ψ, form.impl (translate φ) (translate ψ)
  | (K a φ)          := form.box a (translate φ)
  | (U φ formPA.bot) := have _, from tr3 φ,     translate (φ ⊃ ⊥)
  | (U φ (p n))      := have _, from tr3 φ,     translate (φ ⊃ (p n))
  | (U φ (ψ & χ))    := have _, from tr5 φ ψ χ, translate ((U φ ψ) & (U φ χ))
  | (U φ (ψ ⊃ χ))    := have _, from tr5 φ ψ χ, translate ((U φ ψ) ⊃ (U φ χ))
  | (U φ (K a ψ))    := have _, from tr6 φ ψ,   translate (φ ⊃ (K a (U φ ψ)))
  | (U φ (U ψ χ))    := have _, from tr7 φ ψ χ, translate (U (φ & (U φ ψ)) χ)
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf complexity⟩] }