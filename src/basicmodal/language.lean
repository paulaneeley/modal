
inductive form : Type
  | bot  : form
  | var  (n : nat) : form 
  | and  (φ ψ : form) : form
  | impl (φ ψ : form) : form
  | box  (φ : form) : form


-- Notation
--local notation `⊥`:80   := form.bot
--local prefix `p`:80     := form.var
notation `⊥`:80   := form.bot
prefix `p`:80     := form.var
infix `&`:79      := form.and
infix `⊃`         := form.impl
notation `¬` φ    := form.impl φ form.bot
notation `⊤`:80   := ¬ form.bot
notation φ `∨` ψ  := (¬φ ⊃ ψ)
notation φ `↔` ψ  := (φ ⊃ ψ) & (ψ ⊃ φ)
notation `□`:80   := form.box 
notation `◇`:80   := λ φ, ¬(□(¬φ))