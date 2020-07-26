import data.list data.set.basic
section
variable {α : Type*}

def path (R : α → α → Prop) : α → list α → Prop
| x [] := true
| x (y::ys) := R x y ∧ path y ys

def last (R : α → α → Prop) : α → list α → α
| x [] := x
| x (y::ys) := last y ys

def reachable (R : α → α → Prop) (x y : α) : Prop := ∃ l : list α, path R x l ∧ last R x l = y


---------------------- Lemmas about R* ----------------------

lemma reach_right : ∀ x y z : α, ∀ R : α → α → Prop, 
  reachable R x y ∧ R y z →  reachable R x z :=
begin
intros x y z R h1, cases h1 with h1 h2,
rw reachable at *, cases h1 with l h1,
revert x, induction l, 
{intros x h, cases h
with h1 h3, rw last at h3, existsi ([z] : list α),
split, rw path, split, apply eq.subst h3.symm, exact h2,
rw path, trivial, rw last, rw last}, 
{intros x h1, cases h1 with h1 h3, specialize l_ih l_hd,
rw path at h1, cases h1 with h1 h4, rw last at h3, 
have h5 := l_ih (and.intro h4 h3), cases h5 with l h5,
existsi (l_hd::l : list α), split, rw path, exact and.intro h1 h5.left,
rw last, exact h5.right} 
end


lemma ref_close : ∀ x : α, ∀ R : α → α → Prop, reachable R x x :=
begin
intros x R,
existsi ([] : list α),
split,
trivial, 
rw last
end

lemma trans_close : ∀ x y z : α, ∀ R : α → α → Prop, 
  reachable R x y ∧ reachable R y z → reachable R x z :=
begin
intros x y z R h,
cases h with h1 h2,
rw reachable at *,
cases h1 with l1 h1,
cases h2 with l2 h2,
revert x y z,
induction l1, 
{intros x y z h1 h2, cases h1 with h1 h3, cases h2 with h2 h4,
rw last at h3, existsi (l2 : list α), split, apply eq.subst h3.symm,
exact h2, apply eq.subst h3.symm, exact h4},
{intros x y z h1 h2, cases h1 with h1 h3, cases h2 with h2 h4,
cases h1 with h1 h5, specialize l1_ih l1_hd, specialize l1_ih y, 
specialize l1_ih z, have h6: (∃ (l : list α), path R l1_hd l ∧ last R l1_hd l = z),
from l1_ih (and.intro h5 h3) (and.intro h2 h4), cases h6 with l h6,
existsi (l1_hd::l : list α), split, split, exact h1, exact h6.left, exact h6.right}
end

lemma containsR : ∀ x y : α, ∀ R : α → α → Prop, R x y → reachable R x y :=
begin
intros x y R h,
rw reachable,
existsi ([y] : list α),
split, split,
exact h, trivial,
rw last, rw last
end

open set

lemma smallest (R S : α → α → Prop) (reflS : reflexive S) (transS : transitive S) : 
  (∀ x y : α, R x y → S x y) → (∀ x y : α, reachable R x y → S x y) :=
begin
intros h1 x z h2, rw reachable at h2, 
cases h2 with l h2, cases h2 with h2 h3, 
revert x z, induction l, 
{intros x z h2 h3, rw last at h3, specialize reflS x, 
apply eq.subst h3, exact reflS},
{intros x z h2 h3, rw path at h2, cases h2 with h2 h4, 
rw last at h3, specialize l_ih l_hd, specialize l_ih z,
have h5: S l_hd z, from l_ih h4 h3, specialize h1 x,
specialize h1 l_hd, have h6 : S x l_hd, from h1 h2,
rw transitive at transS, have h7 := transS h6, 
have h8 := h7 h5, exact h8}
end

end





