-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.languageDEL del.syntax.syntaxDEL del.syntax.syntaxlemmasDEL del.syntax.soundnessDEL
import del.semantics.translationdefs  del.semantics.semanticsDEL
import del.semantics.translationfunction del.semantics.complexitylemmas del.semantics.translationlemmas 
import tactic.linarith

variables {agents : Type}

open prfPA

---------------------- Completeness by Translation ----------------------

theorem equiv_translation_aux' {Γ : ctx agents} (n : nat) (φ : formPA agents) (h : complexity φ ≤ n) : 
  prfPA Γ (φ ↔ (translate φ)) :=
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
      have h1 := ih φ (compimp1 h),
      have h2 := ih ψ (compimp2 h),
      exact iff_iff_imp_iff h1 h2
    },
  case formPA.box : a φ 
    { simp at *,
      have h1 : complexity φ ≤ n, sorry, --exact nat.lt_succ_iff.mp h,
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
          have h3 := atomicbot, exact update_iff1 h2 h3 
        },
      case formPA.var : m 
        { repeat {rw translate},
          repeat {rw complexity at h},
          have h1 : complexity φ ≤ n, 
            {have : complexity φ + 1 ≤ nat.succ n, linarith,
             exact nat.lt_succ_iff.mp this},
          have h2 := ih φ h1,
          have h3 := atomicperm, exact update_iff1 h2 h3 
        },
      case formPA.and : ψ χ 
        { repeat {rw translate},
          have h1 := announceconj,
          have h2 := ih (U φ ψ) (updatecompand1 h),
          have h3 := ih (U φ χ) (updatecompand2 h),
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
          have h1 := announceknow,
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


theorem equiv_translation (Γ : ctx agents) : ∀ φ : formPA agents, prfPA Γ (φ ↔ (translate φ)) :=
begin
intro φ,
have h : complexity φ ≤ complexity φ + 1, linarith,
simp,
exact equiv_translation_aux' (complexity φ + 1) φ h
end


theorem completenessPA {Γ : ctx agents} {φ : formPA agents} : 
   (∀ ψ ∈ Γ, F_valid ψ equiv_class) → F_valid φ equiv_class → prfPA Γ φ :=
begin
intros h1 h2,
have h3 : prfPA Γ (φ ⊃ translate φ), from mp pl5 (equiv_translation Γ φ),
have h4 : prfPA Γ (φ ⊃ translate φ) → (∀ ψ ∈ Γ, F_valid ψ equiv_class) → 
  F_valid (φ ⊃ translate φ) equiv_class, from soundnessPA,
specialize h4 h3 h1,
have h5 : F_valid (translate φ) equiv_class, {rw F_valid, intros f h v x,
specialize h2 f h v x, specialize h4 f h v x h2, exact h4},
sorry,
end