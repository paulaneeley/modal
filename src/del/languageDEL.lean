/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

-- Def 2.1, pg 12
inductive form (agents : Type) : Type
  | bot                : form
  | var  (n : nat)     : form
  | and  (φ ψ : form)  : form
  | impl (φ ψ : form)  : form
  | box  (a : agents)
         (φ : form)    : form


-- form notation
notation `⊥`:80   := form.bot
prefix `p`:80     := form.var
infix `&`:80      := form.and
infix `⊃`         := form.impl
notation `¬`:80 φ := form.impl φ form.bot
notation `⊤`:80   := ¬ (form.bot _)
notation φ `∨` ψ  := form.impl (¬φ) ψ
notation φ ↔ ψ    := form.and (form.impl φ ψ) (form.impl ψ φ)
notation `K`:80   := form.box -- "a knows that φ"
notation `C`:80   := λ a φ, ¬(form.box a (¬φ)) -- "φ is consistent with a's knowledge"


inductive formPA (agents : Type) : Type
  | bot  {}                  : formPA
  | var  {} (n : nat)        : formPA
  | and  {} (φ ψ : formPA)   : formPA
  | impl {} (φ ψ : formPA)   : formPA
  | box  {} (a : agents) 
            (φ : formPA)     : formPA
  | update {} (φ ψ : formPA) : formPA


-- formPA notation
notation `⊥`:80   := formPA.bot
prefix `p`:80     := formPA.var
infix `&`:80      := formPA.and
infix `⊃`         := formPA.impl
notation `¬`:80 φ := formPA.impl φ formPA.bot
notation `⊤`:80   := ¬ (formPA.bot _)
notation φ `∨` ψ  := formPA.impl (¬φ) ψ
notation φ ↔ ψ    := formPA.and (formPA.impl φ ψ) (formPA.impl ψ φ)
notation `K`:80   := formPA.box -- "a knows that φ"
notation `C`:80   := λ φ a, ¬(formPA.box a (¬φ)) -- "φ is consistent with a's knowledge"
notation `U`:80   := formPA.update
notation `D`:80   := λ φ ψ, ¬(formPA.update φ (¬ψ))


variable {agents : Type}

def to_PA : form agents → formPA agents
  | (form.bot)      := formPA.bot
  | (form.var n)    := formPA.var n
  | (form.and φ ψ)  := formPA.and (to_PA φ) (to_PA ψ)
  | (form.impl φ ψ) := formPA.impl (to_PA φ) (to_PA ψ)
  | (form.box a φ)  := formPA.box a (to_PA φ)