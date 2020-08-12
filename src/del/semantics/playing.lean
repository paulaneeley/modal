import tactic.linarith

/-
Good tactics to use:
  library_search
  suggest
  linarith

Find documentation here:

  https://leanprover-community.github.io/mathlib_docs/tactics.html

Documentation on well-founded recursion:

  https://leanprover-community.github.io/extras/well_founded_recursion.html

-/

inductive form : Type
| var : form
| bot : form
| and : form → form → form

def complexity : form → nat
| form.var := 0
| form.bot := 0
| (form.and phi psi) := max (complexity phi) (complexity psi) + 1

def complexity_lt_left (phi psi : form) : complexity phi < complexity (phi.and psi) :=
begin
  simp [complexity],
  linarith [le_max_left (complexity phi) (complexity psi)]
end

def complexity_lt_right (phi psi : form) : complexity psi < complexity (phi.and psi) :=
begin
  simp [complexity],
  linarith [le_max_right (complexity phi) (complexity psi)]
end

def f : form → nat
| form.var := 3
| form.bot := 7
| (form.and phi psi) :=
  have _ := complexity_lt_left phi psi,
  have _ := complexity_lt_right phi psi,
  9 * f phi * f psi
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf complexity⟩] }

theorem f_var : f form.var = 3 := rfl

theorem f_bot : f form.bot = 7 := rfl

theorem f_and (phi psi : form) : f (phi.and psi) = 9 * f phi * f psi := rfl

/-
induction on complexity: show that the theorem holds for all formulas
of complexity at most n, using ordinary induction on nat.
-/
theorem f_pos_aux : ∀ n phi, complexity phi < n → f phi > 0
| 0     _                  _ := by linarith
| (n+1) form.var           _ := dec_trivial
| (n+1) form.bot           _ := dec_trivial
| (n+1) (form.and phi psi) h :=
  begin
    -- `h` is the assumption `complexity (phi.and psi) < n + 1`
    -- we know that the complexity of `phi` is smaller
    have h1 : complexity phi < n,
      linarith [complexity_lt_left phi psi],
    -- we know that the complexity of `psi` is smaller
    have h2 : complexity psi < n,
      linarith [complexity_lt_right phi psi],
    -- so we have the inductive hypothesis for `phi`, justified by `h1`
    have h3 : f phi > 0,
      from f_pos_aux n phi h1,
    -- and we have the inductive hypothesis for `psi`, justified by `h2`
    have h4 : f psi > 0,
      from f_pos_aux n psi h2,
    -- now unfold the definition of `f`, and use the inductive hypotheses
    have h5 : f (phi.and psi) = 9 * f phi * f psi,
      by refl,
    rw h5,
    exact mul_pos (mul_pos (by norm_num) h3) h4
  end

theorem f_pos_aux' {psi : form} : ∀ n phi, complexity phi < n → f phi > 0 :=
  begin
    intros n phi h,
    induction n with n ih,
    linarith,
    induction phi,
    sorry,
    sorry,
    rename phi_a phi, rename phi_a_1 psi, rename phi_ih_a ih_phi, rename phi_ih_a_1 ih_psi,
    have h1 : complexity phi < n, linarith [complexity_lt_left phi psi],
  end

theorem f_pos (phi : form) : f phi > 0 :=
have h : complexity phi < complexity phi + 1,
  from nat.lt_succ_self _,
f_pos_aux _ _ h
