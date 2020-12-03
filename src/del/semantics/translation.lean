-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

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
      have h1 := ih φ (compand1 h),
      have h2 := ih ψ (compand2 h),
      exact iff_iff_and_iff h1 h2
    },
  case formPA.impl : φ ψ 
    { rw translate,
      repeat {rw to_PA},
      have h1 := ih φ (compimp1 h),
      have h2 := ih ψ (compimp2 h),
      exact iff_iff_imp_iff h1 h2
    },
  case formPA.box : a φ 
    { simp at *,
      have h1 : complexity φ ≤ n, from nat.lt_succ_iff.mp (nat.one_add_le_iff.mp h),
      have h2 := ih φ h1,
      exact iff_k_dist h2, 
    },
  case formPA.update : φ ψ 
    { cases ψ,
      case formPA.bot 
        { repeat {rw translate},
          repeat {rw complexity at h},
          have h1 : complexity φ ≤ n, 
            {have : complexity φ + 1 ≤ nat.succ n, linarith,
             exact nat.lt_succ_iff.mp this},
          have h2 := ih φ h1,
          have h3 : prfPA Γ ((U φ ⊥) ↔ (φ ⊃ ⊥)), from atomicbot, 
          exact update_iff1 h2 h3 
        },
      case formPA.var : m 
        { repeat {rw translate},
          repeat {rw complexity at h},
          have h1 : complexity φ ≤ n, 
            {have : complexity φ + 1 ≤ nat.succ n, linarith,
             exact nat.lt_succ_iff.mp this},
          have h2 := ih φ h1,
          have h3 : prfPA Γ ((U φ (p m)) ↔ (φ ⊃ (p m))), from atomicperm, 
          exact update_iff1 h2 h3 
        },
      case formPA.and : ψ χ 
        { repeat {rw translate},
          have h1 : prfPA Γ ((U φ (ψ & χ)) ↔ ((U φ ψ) & (U φ χ))), from announceconj,
          have h2 := ih (U φ ψ) (updatecompand1 h),
          have h3 := ih (U φ χ) (updatecompand2 h),
          simp at *,
          exact update_iff2 h2 h3 h1,
        },
      case formPA.impl : ψ χ
        { repeat {rw translate},
          have h1 : prfPA Γ ((U φ (ψ ⊃ χ)) ↔ ((U φ ψ) ⊃ (U φ χ))), from announceimp,
          have h2 := ih (U φ ψ) (updatecompimp1 h),
          have h3 := ih (U φ χ) (updatecompimp2 h),
          simp at *,
          exact update_iff3 h2 h3 h1,
        },
      case formPA.box : a ψ
        { repeat {rw translate}, 
          have h1 : prfPA Γ ((U φ (K a ψ)) ↔ (φ ⊃ (K a (U φ ψ)))), from announceknow,
          have h2 := ih (φ ⊃ K a (U φ ψ)) (updatecompknow2 h),
          exact update_iff4 h1 h2
        },
      case formPA.update : ψ χ
        { rw translate,
          have h1 : prfPA Γ ((U φ (U ψ χ)) ↔ (U (φ & (U φ ψ)) χ)), from announcecomp,
          have h2 := ih (U (φ & (U φ ψ)) χ) (updatecompupdate h),
          exact update_iff5 h1 h2,
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
rw global_sem_csqPA at h1,
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
have h2 : prfPA ∅ (φ ⊃ to_PA (translate φ)), 
  from mp pl5 (equiv_translation ∅ φ),
have h3 : prfPA ∅ (φ ⊃ to_PA (translate φ)) → 
  global_sem_csqPA ∅ equiv_class (φ ⊃ to_PA (translate φ)), 
  from soundnessPA,
specialize h3 h2,
have h4 : global_sem_csqPA ∅ equiv_class (to_PA (translate φ)), 
{rw global_sem_csqPA, intros f h4 v h5 x,
specialize h1 f h4 v h5 x, specialize h3 f h4 v h5 x, exact h3 h1},
have h5 : global_sem_csq (∅ : ctx agents) equiv_class (translate φ), 
  from (global_sem_csqPA_iff_global_sem_csq equiv_class (translate φ) ).mp h4,
have h6 : global_sem_csq ∅ equiv_class (translate φ) → prfS5 ∅ (translate φ), 
  from canonical.completeness sem_consS5 (translate φ),
specialize h6 h5,
have h7 : prfPA (to_PA '' ∅) (to_PA (translate φ)), from to_prfPA h6,
have h8 : prfPA ∅ (φ ↔ to_PA (translate φ)), from equiv_translation ∅ φ,
simp at *,
have h9 : prfPA ∅ ((to_PA (translate φ)) ⊃ φ), from mp pl6 h8,
have h10 : prfPA ∅ φ, from mp h9 h7,
exact h10
end