/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import del.semantics.translationlemmas
import del.semantics.completenessDEL del.syntax.syntaxlemmasPADEL
import tactic.linarith

variables {agents : Type}
open prfPA
open PAlemma

---------------------- Completeness by Translation ----------------------


theorem equiv_translation_aux' {Γ : ctxPA agents} (n : nat) (φ : formPA agents) (h : complexity φ ≤ n) : 
  prfPA Γ (φ ↔ to_PA (translate φ)) :=
begin
  simp at *,
  induction n with n ih generalizing φ,
  { have h1 : complexity φ > 0, from comp_gt_zero, linarith},
  cases φ,
  case formPA.bot 
    { exact mp (mp pl4 iden) iden },
  case formPA.var : m 
    { exact mp (mp pl4 iden) iden },
  case formPA.and : φ ψ 
    { rw translate,
      exact iff_iff_and_iff (ih φ (compand1 h)) (ih ψ (compand2 h))
    },
  case formPA.impl : φ ψ 
    { rw translate,
      repeat {rw to_PA},
      exact iff_iff_imp_iff (ih φ (compimp1 h)) (ih ψ (compimp2 h))
    },
  case formPA.box : a φ 
    { simp at *,
      have h1 : complexity φ ≤ n, from nat.lt_succ_iff.mp (nat.one_add_le_iff.mp h),
      exact iff_k_dist (ih φ h1), 
    },
  case formPA.update : φ ψ 
    { cases ψ,
      case formPA.bot 
        { repeat {rw translate},
          repeat {rw complexity at h},
          have h1 : complexity φ ≤ n, 
            {have : complexity φ + 1 ≤ nat.succ n, linarith,
             exact nat.lt_succ_iff.mp this},
          have h2 := atomicbot, 
          exact update_iff1 (ih φ h1) h2
        },
      case formPA.var : m 
        { repeat {rw translate},
          repeat {rw complexity at h},
          have h1 : complexity φ ≤ n, 
            {have : complexity φ + 1 ≤ nat.succ n, linarith,
             exact nat.lt_succ_iff.mp this},
          have h2 := atomicperm, 
          exact update_iff1 (ih φ h1) h2
        },
      case formPA.and : ψ χ 
        { repeat {rw translate},
          exact update_iff2 (ih (U φ ψ) (updatecompand1 h)) (ih (U φ χ) (updatecompand2 h)) announceconj,
        },
      case formPA.impl : ψ χ
        { repeat {rw translate},
          exact update_iff3 (ih (U φ ψ) (updatecompimp1 h)) (ih (U φ χ) (updatecompimp2 h)) announceimp,
        },
      case formPA.box : a ψ
        { repeat {rw translate}, 
          exact update_iff4 announceknow (ih (φ ⊃ K a (U φ ψ)) (updatecompknow2 h))
        },
      case formPA.update : ψ χ
        { rw translate, 
          exact update_iff5 announcecomp (ih (U (φ & (U φ ψ)) χ) (updatecompupdate h))
        } 
    }
end


theorem equiv_translation (Γ : ctxPA agents) : ∀ φ : formPA agents, prfPA Γ (φ ↔ to_PA (translate φ)) :=
begin
intro φ,
have h : complexity φ ≤ complexity φ + 1, linarith,
simp,
exact equiv_translation_aux' (complexity φ + 1) φ h
end


lemma forces_ctxPA_iff_forces_ctx (f : frame agents) 
  (v : nat → f.states → Prop) : 
  forces_ctxPA f v ∅ ↔ forces_ctx f v ∅ :=
begin
split,
repeat {intros h1 φ x h2,
exact false.elim h2},
end


lemma global_sem_csqPA_iff_global_sem_csq (F : set (frame agents)) (φ : form agents) : 
  global_sem_csqPA ∅ F (to_PA φ) ↔ global_sem_csq ∅ F φ :=
begin
split,
intros h1 f h2 v h3 x,
have h4 := (forces_ctxPA_iff_forces_ctx f v).mpr h3,
exact (forcesPA_iff_forces φ f v x).mp (h1 f h2 v h4 x),
intros h1 f h2 v h3 x,
have h4 := (forces_ctxPA_iff_forces_ctx f v).mp h3,
exact (forcesPA_iff_forces φ f v x).mpr (h1 f h2 v h4 x)
end


theorem completenessPA {φ : formPA agents} (Γ : ctxPA agents) : 
  global_sem_csqPA ∅ equiv_class φ → prfPA ∅ φ :=
begin
intros h1,
have h2 := mp pl5 (equiv_translation ∅ φ),
have h3 := soundnessPA,
have h4 : global_sem_csqPA ∅ equiv_class (to_PA (translate φ)), 
{intros f h4 v h5 x,
exact h3 h2 f h4 v h5 x (h1 f h4 v h5 x)},
have h5 := (global_sem_csqPA_iff_global_sem_csq equiv_class (translate φ) ).mp h4,
have h6 := canonical.completeness sem_consS5 (translate φ),
have h7 := to_prfPA (h6 h5),
simp at *,
exact mp (mp pl6 (equiv_translation ∅ φ)) h7
end