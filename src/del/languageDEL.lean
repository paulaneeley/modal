-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

-- Def 2.1, pg 12
inductive form (agents : Type) : Type
  | bot                 : form
  | var  (n : nat)      : form
  | and  (φ ψ : form)   : form
  | impl (φ ψ : form)   : form
  | box  (a : agents)
         (φ : form)     : form


inductive formPA (agents : Type) : Type
  | bot  {}                  : formPA
  | var  {} (n : nat)        : formPA
  | and  {} (φ ψ : formPA)   : formPA
  | impl {} (φ ψ : formPA)   : formPA
  | box  {} (a : agents) 
            (φ : formPA)     : formPA
  | update {} (φ ψ : formPA) : formPA


-- Notation
--local notation `⊥`:80   := formPA.bot
--local prefix `p`:80     := formPA.var
notation `⊥`:80         := formPA.bot
prefix `p`:80           := formPA.var
infix `&`:80            := formPA.and
infix `⊃`               := formPA.impl
notation `~`:80 φ       := φ ⊃ formPA.bot
notation `⊤`:80         := ~ (formPA.bot _)
notation φ `∨` ψ        := ((~φ) ⊃ ψ)
notation φ ↔ ψ          := (φ ⊃ ψ) & (ψ ⊃ φ)
notation `K`:80         := formPA.box -- "a knows that φ"
notation `C`:80         := λ φ a, ~(K a (~φ)) -- "φ is consistent with a's knowledge"
notation `U`:80         := formPA.update
notation `D`:80         := λ φ ψ, ~(U φ (~ψ))