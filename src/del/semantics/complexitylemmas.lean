-- Following the textbook "Dynamic Epistemic Logic" by 
-- Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

import del.semantics.translationdefs tactic.linarith
variables {agents : Type}

---------------------- Generic helper lemmas ----------------------
lemma comp_gt_zero {φ : formPA agents} : complexity φ > 0 :=
begin
induction φ,
repeat { rw complexity }, repeat { linarith },
have h1 : 4 > 0, linarith,
exact (mul_pos (add_lt_add h1 φ_ih_φ) φ_ih_ψ)
end

lemma comp_ge_zero {φ : formPA agents} : complexity φ ≥ 0 := le_of_lt comp_gt_zero

lemma comp_ge_one {φ : formPA agents} : complexity φ ≥ 1 :=
begin
have h1 : complexity φ > 0, from comp_gt_zero,
linarith
end

lemma maxhelper {n1 n2 n3 n4 : nat} : n1 + n2 < n4 → n1 + n3 < n4 → n1 + max n2 n3 < n4 :=
begin
intros h1 h2,
exact nat.add_lt_of_lt_sub_left (max_lt (nat.lt_sub_left_of_add_lt h1) (nat.lt_sub_left_of_add_lt h2))
end

lemma le_maxhelper {n1 n2 n3 n4 : nat} : n1 + n2 ≤ n4 → n1 + n3 ≤ n4 → n1 + max n2 n3 ≤ n4 :=
begin
intros h1 h2,
have h3 := max_le (nat.le_sub_left_of_add_le h1) (nat.le_sub_left_of_add_le h2),
rw nat.le_sub_right_iff_add_le at h3,
have h4 : max n2 n3 + n1 = n1 + max n2 n3, linarith,
have h5 : n1 + max n2 n3 ≤ n4, from eq.subst h4 h3,
exact h5, linarith
end

-------------- Helper lemmas for translation function --------------

lemma tr1 : ∀ φ ψ : formPA agents, complexity φ < 1 + max (complexity φ) (complexity ψ) := 
begin
intros φ ψ,
have h1 := lt_add_one _, 
have h2 := add_comm _ _,
exact (eq.subst h2 (lt_of_le_of_lt (le_max_left (complexity φ) (complexity ψ)) h1))
end

lemma tr2 : ∀ φ ψ : formPA agents, complexity ψ < 1 + max (complexity φ) (complexity ψ) :=
begin
intros φ ψ, 
have h1 := lt_add_one _, 
have h2 := add_comm _ _,
exact (eq.subst h2 (lt_of_le_of_lt (le_max_right (complexity φ) (complexity ψ)) h1))
end

lemma tr3 : ∀ φ : formPA agents, 1 + max (complexity φ) 1 < 4 + complexity φ :=
begin
intro φ,
rw add_comm 4,
have h1 : complexity φ < complexity φ + 1, from lt_add_one _,
have h2 : 0 < 2 ↔ 2 ≠ 0, from zero_lt_iff_ne_zero,
cases h2, 
specialize h2_mpr (nat.add_one_ne_zero 1),
have h3 : 3 + (complexity φ + 1) = complexity φ + 4, from add_comm _ _,
exact (eq.subst h3 (add_lt_add (lt_add_of_pos_right 1 h2_mpr) (max_lt h1 (lt_add_of_pos_left 1 comp_gt_zero))))
end

lemma tr4helper {φ ψ : formPA agents} : (complexity φ + 4) * (1 + max (complexity ψ) 1) > 9 :=
begin
have h1 : complexity φ ≥ 1, from comp_ge_one,
have h2 : (complexity φ + 4) ≥ 5, linarith,
have h3 : complexity ψ ≥ 1, from comp_ge_one,
have h4 := max_eq_left h3,
have h5 : 1 + max (complexity ψ) 1 ≥ 1 + 1, linarith,
have h6 : 0 ≤ 2, linarith,
have h7 : 0 ≤ complexity φ + 4, linarith,
have h8 := mul_le_mul h2 h5 h6 h7,
exact h8,
end

lemma tr4helper1 {n m : nat} : n ≥ 4 → m ≥ 1 → 2 + n * m < n * (1 + m) :=
begin
  intros h1 h2,
  have h3 := mul_add n 1 m,
  linarith,
end

lemma tr4helper2 {φ ψ : formPA agents} : 1 + 1 + (complexity φ + 4) * complexity ψ < (complexity φ + 4) * (1 + complexity ψ) :=
begin
have h1 : complexity φ + 4 ≥ 4, linarith,
exact (tr4helper1 h1 (comp_ge_one))
end

lemma tr4helper3 {φ ψ : formPA agents} : 1 + 1 + ((complexity φ + 4) * complexity ψ) < (complexity φ + 4) * (1 + max (complexity ψ) 1) :=
begin
have h1 : complexity ψ ≥ 1, from comp_ge_one,
have h2 := max_eq_left h1,
have h3 : (complexity φ + 4) * (1 + complexity ψ) = (complexity φ + 4) * (1 + max (complexity ψ) 1), 
from congr_arg (has_mul.mul (complexity φ + 4)) (congr_arg (has_add.add 1) (eq.symm (max_eq_left comp_ge_one))),
exact (eq.subst h3 tr4helper2)
end

lemma tr4 : ∀ φ ψ : formPA agents, 1 + max (complexity φ) (1 + max ((4 + complexity φ) 
  * complexity ψ) 1) < (4 + complexity φ) * (1 + max (complexity ψ) 1) :=
begin
intros φ ψ,
rw add_comm 4,
have h1 : 1 ≤ 1 + max (complexity ψ) 1, linarith,
have h2 : 1 + complexity φ < (complexity φ + 4), linarith, 
have h3 : 1 > 0, linarith,
have h4 : 4 ≥ 0, linarith,
have h5 : complexity ψ ≥ 1, from comp_ge_one,
have h6 : 1 ≥ 1, linarith,
have h7 : max (complexity ψ) 1 ≥ 1, exact le_max_right (complexity ψ) 1,
have h8 : 3 < 9, linarith,
have h9 : 1 + 1 + max ((complexity φ + 4) * complexity ψ) 1 = 1 + (1 + max ((complexity φ + 4) * complexity ψ) 1), linarith,
exact (maxhelper (eq.subst (mul_one (1 + complexity φ)) 
  (mul_lt_mul h2 h1 h3 (add_nonneg comp_ge_zero h4))) (eq.subst h9 (maxhelper tr4helper3 (lt_trans h8 tr4helper))))
end

lemma tr5helper {φ ψ : formPA agents} : 1 + ((complexity φ + 4) * complexity ψ) < (complexity φ + 4) * (1 + (complexity ψ)) :=
begin
have h1 : 1 + 1 + (complexity φ + 4) * complexity ψ < (complexity φ + 4) * (1 + complexity ψ), from tr4helper2,
linarith,
end

lemma tr5helper1 {ψ χ : formPA agents} : complexity χ ≤ max (complexity χ) (complexity ψ) :=
begin
cases max_choice (complexity ψ) (complexity χ),
repeat {have h : complexity χ ≤ complexity χ, linarith, exact (le_max_left_of_le h)}
end

lemma tr5helper2 {ψ χ : formPA agents} : max (complexity ψ) (complexity χ) = complexity ψ → complexity χ ≤ complexity ψ :=
begin
intro h1, 
have h2 : max (complexity χ) (complexity ψ) = complexity ψ, 
  from eq.substr (max_comm (complexity χ) (complexity ψ)) h1,
exact (eq.subst h2 tr5helper1)
end

lemma tr5helper3 {φ ψ χ : formPA agents} : complexity χ ≤ complexity ψ → 
  1 + ((complexity φ + 4) * complexity χ) < (complexity φ + 4) * (1 + (complexity ψ)) :=
begin
intro h1,
have h2 : complexity φ + 4 > 0, linarith,
have h3 : complexity φ + 4 ≤ complexity φ + 4, linarith,
have h4 := nat.mul_le_mul_left (complexity φ + 4) h1,
have h5 : 1 + (complexity φ + 4) * complexity χ ≤ 1 + (complexity φ + 4) * complexity ψ, linarith,
exact (lt_of_le_of_lt h5 tr5helper)
end

lemma tr5 : ∀ φ ψ χ : formPA agents, 1 + max ((4 + complexity φ) * complexity ψ) 
  ((4 + complexity φ) * complexity χ) < (4 + complexity φ) * (1 + max (complexity ψ) (complexity χ)) :=
begin
intros φ ψ χ,
rw add_comm 4,
cases max_choice (complexity ψ) (complexity χ),
cases max_choice ((complexity φ + 4) * complexity ψ) ((complexity φ + 4) * complexity χ),
exact (eq.substr h_1 (eq.substr h (tr5helper))),
exact (eq.substr h_1 (eq.substr h (tr5helper3 (tr5helper2 h)))),
cases max_choice ((complexity φ + 4) * complexity ψ) ((complexity φ + 4) * complexity χ),
exact (eq.substr h_1 (eq.substr h (tr5helper3 (tr5helper2 (eq.subst (max_comm (complexity ψ) (complexity χ)) h))))),
exact (eq.substr h_1 (eq.substr h tr5helper)),
end

lemma tr6 : ∀ φ ψ : formPA agents, 1 + max (complexity φ) (1 + (complexity φ + 4) 
  * complexity ψ) < (complexity φ + 4) * (complexity ψ + 1) :=
begin
intros φ ψ,
have h1 : 1 + complexity φ < complexity φ + 4, linarith,
have h2 : complexity ψ + 1 ≥ 1, linarith, 
have h3 : 0 < 1, linarith,
have h4 : 0 ≤ complexity φ + 4, linarith,
have h5 := mul_lt_mul h1 h2 h3 h4,
have h6 : 1 + complexity φ < (complexity φ + 4) * (complexity ψ + 1), linarith,
have h7 : 1 + 1 + (complexity φ + 4) * complexity ψ = 1 + (1 + (complexity φ + 4) * complexity ψ), linarith,
have h8 : 1 + complexity ψ = complexity ψ + 1, linarith,
exact (maxhelper h6 (eq.subst h8 (eq.subst h7 tr4helper2)))
end

lemma tr6' : ∀ φ ψ : formPA agents, 1 + max (complexity φ) (1 + (4 + complexity φ) 
  * complexity ψ) < (4 + complexity φ) * (1 + complexity ψ) :=
begin
  intros φ ψ,
  rw add_comm 4, rw add_comm 1 (complexity ψ),
  apply tr6
end

lemma tr7helper1 {φ ψ : formPA agents} : (complexity φ + 4) * (complexity ψ + 4) 
  = (complexity φ) * (complexity ψ) + 4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4 :=
begin
have h1 := mul_add (complexity φ + 4) (complexity ψ) 4,
have h2 := add_mul (complexity φ) 4 (complexity ψ),
have h3 := add_mul (complexity φ) 4 4,
linarith
end

lemma tr7helper2 {φ ψ : formPA agents} : 5 + (complexity φ) < (complexity φ) * (complexity ψ) + 4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4 :=
begin
have h1 : complexity φ ≥ 1, from comp_ge_one,
have h2 : complexity ψ ≥ 1, from comp_ge_one,
have : complexity φ * complexity ψ ≥ 0, apply nat.zero_le,
linarith 
end

lemma tr7helper3 {φ ψ : formPA agents} : 5 + (complexity φ) < (complexity φ + 4) * (complexity ψ + 4) :=
begin
have h1 := tr7helper1,
exact (eq.substr h1 tr7helper2)
end

lemma tr7helper4 {φ ψ : formPA agents} : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) < 
  (complexity φ) * (complexity ψ) + 4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4 :=
begin
have h1 : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) = 
  (complexity φ) * (complexity ψ) + (5 + 4 * (complexity ψ)), linarith,
have h2 : 5 + 4 * (complexity ψ) < 4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4, linarith,
have h3 := add_lt_add_left h2 ((complexity φ) * (complexity ψ)),
have h4 : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) < 
  (complexity φ) * (complexity ψ) + (4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4), from eq.substr h1 h3,
have h5 : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) < 
  (complexity φ) * (complexity ψ) + 4 * (complexity ψ) + 4 * (complexity φ) + 4 * 4, linarith,
exact h5
end

lemma tr7helper5 {φ ψ : formPA agents} : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) =
  (5 + ((complexity φ + 4) * complexity ψ)) :=
begin
have h1 := add_mul (complexity φ) 4 (complexity ψ),
have h2 : 5 + (complexity φ) * (complexity ψ) + 4 * (complexity ψ) 
  = 5 + ((complexity φ + 4) * complexity ψ), linarith,
exact h2
end

lemma tr7helper6 {φ ψ : formPA agents} : (5 + ((complexity φ + 4) * complexity ψ)) 
  < (complexity φ + 4) * (complexity ψ + 4) :=
begin
have h1 := tr7helper5,
have h2 := tr7helper1,
exact (eq.substr h2 (eq.subst h1 tr7helper4))
end

lemma tr7 : ∀ φ ψ χ : formPA agents, (1 + (4 + max (complexity φ) ((complexity φ + 4) 
  * complexity ψ))) * complexity χ < (complexity φ + 4) * ((complexity ψ + 4) * complexity χ) :=
begin
intros φ ψ χ,
have h1 := mul_assoc (complexity φ + 4) (complexity ψ + 4) (complexity χ),
have h2 : (5 + max (complexity φ) ((complexity φ + 4) * complexity ψ)) 
  = (1 + 4 + max (complexity φ) ((complexity φ + 4) * complexity ψ)), linarith,
have h3 : (1 + 4 + max (complexity φ) ((complexity φ + 4) * complexity ψ)) 
  = (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))), linarith,
exact (eq.subst h1 (mul_lt_mul_of_pos_right (eq.subst h3 (maxhelper tr7helper3 tr7helper6)) comp_gt_zero))
end

lemma tr7' : ∀ φ ψ χ : formPA agents, (4 + (1 + max (complexity φ) ((4 + complexity φ) 
  * complexity ψ))) * complexity χ < (4 + complexity φ) * ((4 + complexity ψ) * complexity χ) :=
begin
  intros φ ψ χ,
  rw [add_left_comm 4, add_comm 4 (complexity φ), add_comm 4 (complexity ψ)],
  apply tr7
end

/-

  (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))) * complexity χ <
    (complexity φ + 4) * ((complexity ψ + 4) * complexity χ)
⊢ (4 + (1 + max (complexity φ) ((4 + complexity φ) * complexity ψ))) * complexity χ <
    (4 + complexity φ) * ((4 + complexity ψ) * complexity χ)

-/

-------------- Helper lemmas for equiv_translation_aux --------------


lemma compand1 {φ ψ : formPA agents} {n : nat} : complexity (φ & ψ) ≤ n + 1 → complexity φ ≤ n :=
begin
  intro h,
  rw complexity at *,
  have h1 := le_max_left (complexity φ) (complexity ψ),
  linarith
end

lemma compand2 {φ ψ : formPA agents} {n : nat} : complexity (φ & ψ) ≤ n + 1 → complexity ψ ≤ n :=
begin
  intro h,
  rw complexity at *,
  have h1 := le_max_right (complexity φ) (complexity ψ),
  linarith
end

lemma compimp1 {φ ψ : formPA agents} {n : nat} : complexity (φ ⊃ ψ) ≤ n + 1 → complexity φ ≤ n :=
begin
  intro h,
  rw complexity at *,
  have h1 := le_max_left (complexity φ) (complexity ψ),
  linarith
end

lemma compimp2 {φ ψ : formPA agents} {n : nat} : complexity (φ ⊃ ψ) ≤ n + 1 → complexity ψ ≤ n :=
begin
  intro h,
  rw complexity at *,
  have h1 := le_max_right (complexity φ) (complexity ψ),
  linarith
end

lemma updatecomphelper {φ ψ : formPA agents} : 
  complexity (U φ ψ) = (complexity φ + 4) * complexity ψ :=
begin
rw complexity,
have h1 := add_comm 4 (complexity φ),
have h2 : (4 + complexity φ) * complexity ψ = (4 + complexity φ) * complexity ψ, refl,
exact (eq.subst h1 h2),
end


lemma updatecompand1 {φ ψ χ : formPA agents} {n : nat} : 
  complexity (U φ (ψ & χ)) ≤ n + 1 → complexity (U φ ψ) ≤ n :=
begin
intro h1,
simp only [complexity] at *,
have h2 := add_le_add_left (le_max_left (complexity ψ) (complexity χ)) 1,
have h3 := comp_ge_one,
have h4 : complexity φ + 4 ≥ 1, from le_add_right h3,
have h5 := le_trans (nat.mul_le_mul_left ((4 + complexity φ)) h2) h1,
have h6 := mul_add (4 + complexity φ) 1 (complexity ψ),
have h7 : (4 + complexity φ) * (complexity ψ) < 
  (4 + complexity φ) + (4 + complexity φ) * (complexity ψ), linarith,
linarith
end

lemma updatecompand2 {φ ψ χ : formPA agents} {n : nat} : 
  complexity (U φ (ψ & χ)) ≤ n + 1 → complexity (U φ χ) ≤ n :=
begin
intro h1,
simp only [complexity] at *,
have h2 := add_le_add_left (le_max_right (complexity ψ) (complexity χ)) 1,
have h3 := comp_ge_one,
have h4 : complexity φ + 4 ≥ 1, from le_add_right h3,
have h5 := le_trans (nat.mul_le_mul_left ((4 + complexity φ)) h2) h1,
have h6 := mul_add (4 + complexity φ) 1 (complexity χ),
have h7 : (4 + complexity φ) * (complexity ψ) < 
  (4 + complexity φ) + (4 + complexity φ) * (complexity ψ), linarith,
linarith
end

lemma updatecompimp1 {φ ψ χ : formPA agents} {n : nat} : 
  complexity (U φ (ψ ⊃ χ)) ≤ n + 1 → complexity (U φ ψ) ≤ n :=
begin
intro h1,
rw complexity at *,
have h2 := add_le_add_left (le_max_left (complexity ψ) (complexity χ)) 1,
have h3 := comp_ge_one,
have h4 : complexity φ + 4 ≥ 1, from le_add_right h3,
have h5 := le_trans (nat.mul_le_mul_left ((4 + complexity φ)) h2) h1,
have h6 := mul_add (4 + complexity φ) 1 (complexity ψ),
have h7 : (4 + complexity φ) * (complexity ψ) < 
  (4 + complexity φ) + (4 + complexity φ) * (complexity ψ), linarith,
linarith
end

lemma updatecompimp2 {φ ψ χ : formPA agents} {n : nat} : 
  complexity (U φ (ψ ⊃ χ)) ≤ n + 1 → complexity (U φ χ) ≤ n :=
begin
intro h1,
simp only [complexity] at *,
have h2 := add_le_add_left (le_max_right (complexity ψ) (complexity χ)) 1,
have h3 := comp_ge_one,
have h4 : complexity φ + 4 ≥ 1, from le_add_right h3,
have h5 := le_trans (nat.mul_le_mul_left ((4 + complexity φ)) h2) h1,
have h6 := mul_add (4 + complexity φ) 1 (complexity χ),
have h7 : (4 + complexity φ) * (complexity ψ) < 
  (4 + complexity φ) + (4 + complexity φ) * (complexity ψ), linarith,
linarith
end

lemma updatecompknow1' (φ ψ : formPA agents) {n : nat} {a : agents} : complexity (U φ (K a ψ)) ≤ n + 1 
  → 1 + complexity φ ≤ n :=
begin
intro h1,
simp only [complexity] at h1,
have h2 : complexity φ > 0, from comp_gt_zero,
have h3 : complexity ψ ≥ 1, from comp_ge_one,
have h4 := add_mul 4 (complexity φ) (1 + complexity ψ),
have h5 := mul_add (complexity φ) 1 (complexity ψ),
have h6 := mul_add 4 1 (complexity ψ),
have h7 : 4 * (1 + complexity ψ) + complexity φ * (1 + complexity ψ) = 
  4 * (1 + complexity ψ) + complexity φ * 1 + complexity φ * complexity ψ, linarith,
have h8 : (4 + complexity φ) * (1 + complexity ψ) = 
  4 * 1 + 4 * complexity ψ + complexity φ * 1 + complexity φ * complexity ψ, linarith,
have h9 : complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 4 * 1 ≤ n + 1, linarith,
have h10 : complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ ≤ n, linarith,
have : complexity φ * complexity ψ ≥ 0, apply nat.zero_le,
have h11 : 1 + complexity φ ≤ 
  complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ, linarith,
exact le_trans h11 h10
end 

lemma updatecompknow2' {φ ψ : formPA agents} {n : nat} : (4 + complexity φ) * (1 + complexity ψ) ≤ n + 1 
  → 1 + (1 + (4 + complexity φ) * complexity ψ) ≤ n :=
begin
intro h1,
have h2 : complexity φ ≥ 1, from comp_ge_one,
have h3 : complexity ψ ≥ 1, from comp_ge_one,
have h4 := add_mul 4 (complexity φ) (1 + complexity ψ),
have h5 := mul_add (complexity φ) 1 (complexity ψ),
have h6 := mul_add 4 (complexity ψ) 1,
have h7 : (4 + complexity φ) * (1 + complexity ψ) = 
  4 * (1 + complexity ψ) + complexity φ * 1 + complexity φ * complexity ψ, linarith, 
have h8 : (4 + complexity φ) * (1 + complexity ψ) = 
  complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 4 * 1, linarith,
have h9 : complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 4 ≤ n + 1, 
  from eq.subst h8 h1,
have h10 : complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 3 ≤ n, linarith,
have h11 : (4 + complexity φ) * complexity ψ = 4 * complexity ψ + complexity φ * complexity ψ, 
  from add_mul 4 (complexity φ) (complexity ψ),
have h12 : 1 + (4 + complexity φ) * complexity ψ = 
  1 + (4 * complexity ψ + complexity φ * complexity ψ), linarith,
have h13 : 1 + (1 + (4 + complexity φ) * complexity ψ) = 
  1 + (1 + (4 * complexity ψ + complexity φ * complexity ψ)), linarith,
have h14 : 1 + (1 + (4 * complexity ψ + complexity φ * complexity ψ)) = 
  2 + 4 * complexity ψ + complexity φ * complexity ψ, linarith,
have h15 : 2 + 4 * complexity ψ + complexity φ * complexity ψ ≤ 
  complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 3, linarith,
have h16 : 1 + (1 + (4 * complexity ψ + complexity φ * complexity ψ)) ≤ 
  complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 3, from eq.substr h14 h15,
have h17 : 1 + (1 + (4 + complexity φ) * complexity ψ) ≤ 
  complexity φ * complexity ψ + complexity φ * 1 + 4 * complexity ψ + 3, from eq.substr h12 h16,
exact le_trans h17 h10
end

lemma updatecompknow1 {a : agents} {φ ψ : formPA agents} {n : nat} : 
  complexity (U φ (K a ψ)) ≤ n + 1 → complexity φ ≤ n :=
begin
intro h1,
have h2 : 1 + complexity φ ≤ n, from updatecompknow1' φ ψ h1,
linarith
end

lemma updatecompknow2 {a : agents} {φ ψ : formPA agents} {n : nat} : 
  complexity (U φ (K a ψ)) ≤ n + 1 → complexity (φ ⊃ K a (U φ ψ)) ≤ n :=
begin
intro h1,
have h2 : 1 + complexity φ ≤ n, from updatecompknow1' φ ψ h1,
have h3 : 1 + (1 + (4 + complexity φ) * complexity ψ) ≤ n, from updatecompknow2' h1,
have h4 : 1 + max (complexity φ) (1 + (4 + complexity φ) * complexity ψ) ≤ n, from le_maxhelper h2 h3,
exact h4
end
 
lemma updatecompupdate {φ ψ χ : formPA agents} {n : nat} : 
  complexity (U φ (U ψ χ)) ≤ n + 1 → complexity (U (φ & U φ ψ) χ) ≤ n :=
begin
intro h1, repeat {rw complexity at *},
have h2 := tr7 φ ψ χ,
have h3 := add_left_comm 1 4 (max (complexity φ) ((complexity φ + 4) * complexity ψ)),
have h5 : (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))) = 
  (4 + (1 + max (complexity φ) ((4 + complexity φ) * complexity ψ))), 
  from eq.subst (add_comm (complexity φ) 4) h3,
have h6 : (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))) * complexity χ = 
  (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))) * complexity χ, refl,
have h7 : (1 + (4 + max (complexity φ) ((complexity φ + 4) * complexity ψ))) * complexity χ =
  (4 + (1 + max (complexity φ) ((4 + complexity φ) * complexity ψ))) * complexity χ, 
  from eq.subst h5 h6,
have h8 := add_comm 4 (complexity φ),
have h9 := updatecomphelper,
have h11 : (4 + complexity φ) * ((4 + complexity ψ) * complexity χ) = 
  (complexity φ + 4) * ((complexity ψ + 4) * complexity χ), 
  from eq.subst h8 (congr_arg (has_mul.mul (4 + complexity φ)) h9),
have h13 : (4 + (1 + max (complexity φ) ((4 + complexity φ) * complexity ψ))) * complexity χ <
    (4 + complexity φ) * ((4 + complexity ψ) * complexity χ), from eq.subst h7 (eq.substr h11 h2),
have h14 := lt_of_lt_of_le h13 h1,
linarith,
end