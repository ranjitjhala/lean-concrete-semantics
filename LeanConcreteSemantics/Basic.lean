def hello := "world"

-- #eval hello
-- #eval 1+2


-- theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=

theorem and_commutative (p q : Prop) : p ∧ q -> q ∧ p :=
  fun ⟨ hp, hq ⟩ => And.intro hq hp

theorem de_morgan ( p q r : Prop) : p ∧ (q ∨ r) -> ((p ∧ q) ∨ (p ∧ r)) :=
  fun ⟨ hp , hqr ⟩ => match hqr with
    | Or.inl hq => Or.inl (And.intro hp hq)
    | Or.inr hr => Or.inr (And.intro hp hr)

namespace chapter3

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro lr rl
  where
    lr := λ ⟨ hp, hq ⟩ => ⟨ hq, hp ⟩
    rl := λ ⟨ hq, hp ⟩ => ⟨ hp, hq ⟩

example : p ∨ q ↔ q ∨ p := Iff.intro lr rl
  where
    lr := λ pq => match pq with
            | Or.inl p => Or.inr p
            | Or.inr q => Or.inl q
    rl := λ qp => match qp with
            | Or.inl q => Or.inr q
            | Or.inr p => Or.inl p


-- -- associativity of ∧ and ∨
-- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- -- distributivity
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- -- other properties
-- example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
-- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
-- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
-- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
-- example : ¬(p ∧ ¬p) := sorry
-- example : p ∧ ¬q → ¬(p → q) := sorry
-- example : ¬p → (p → q) := sorry
-- example : (¬p ∨ q) → (p → q) := sorry
-- example : p ∨ False ↔ p := sorry
-- example : p ∧ False ↔ False := sorry
-- example : (p → q) → (¬q → ¬p) := λ p_imp_q not_q p => not_q (p_imp_q p)

end chapter3


namespace mylist

inductive list (α : Type) where
  | nil  : list α
  | cons : α -> list α -> list α
  deriving Repr

def length {α : Type} : list α -> Nat
  | list.nil => 0
  | list.cons _ xs => 1 + length xs

def append {α : Type} : list α -> list α -> list α
  | list.nil, ys => ys
  | list.cons x xs, ys => list.cons x (append xs ys)

theorem append_nil {α : Type} : (xs: list α) -> append xs list.nil = xs
  | list.nil => rfl
  | list.cons y ys => by rw [ append, append_nil ]

theorem append_nil_t {α : Type} (xs: list α) : append xs list.nil = xs := by
  cases xs
  . rfl
  . rw [append, append_nil_t]

theorem bob (a b : Nat) : (1 + (a + b)) = (1 + a ) + b := by
  rw [Nat.add_assoc]

theorem length_append {α : Type} (xs ys : list α) : length (append xs ys) = length xs + length ys :=
  match xs with
  | list.nil => by simp [append, length]
  | list.cons _ xs' => by simp [append, length, length_append, Nat.add_assoc]

def single {α : Type} (x : α) : list α :=
  list.cons x list.nil

def reverse {α : Type} : list α -> list α
  | list.nil => list.nil
  | list.cons x xs => append (reverse xs) (single x)

def it_reverse {α : Type} : list α -> list α -> list α
  | acc, list.nil => acc
  | acc, list.cons x xs => it_reverse (list.cons x acc) xs

def reverse' {α : Type} : list α -> list α :=
  it_reverse list.nil

#eval reverse' (list.cons 1 (list.cons 2 (list.cons 3 list.nil)))

theorem reverse_length {α : Type} (xs : list α) : length (reverse xs) = length xs :=
  match xs with
  | list.nil => rfl
  | list.cons x xs => by simp [reverse, length, length_append, single, reverse_length, Nat.add_comm]

theorem app_assoc {α : Type} (xs ys zs : list α) : append (append xs ys) zs = append xs (append ys zs) :=
  match xs with
  | list.nil => rfl
  | list.cons x xs' => by simp [append, app_assoc]

theorem app_nil {α : Type} (xs : list α) : append xs list.nil = xs :=
  match xs with
  | list.nil => rfl
  | list.cons x xs => by simp [append, app_nil]

theorem rev_app {α : Type} (xs ys : list α) : reverse (append xs ys) = append (reverse ys) (reverse xs) :=
  match xs with
  | list.nil => by rw [append, reverse, app_nil]
  | list.cons x xs => by simp [append, reverse, rev_app, app_assoc]

theorem rev_rev {α : Type} (xs : list α) : reverse (reverse xs) = xs :=
  match xs with
  | list.nil => rfl
  | list.cons x xs => by simp [reverse, rev_app, append, rev_rev]

theorem it_rev {α : Type} (acc xs : list α) : it_reverse acc xs = append (reverse xs) acc :=
  match xs with
  | list.nil => rfl
  | list.cons x xs => by simp [it_reverse, reverse, single, app_assoc, append, it_rev]

theorem rev_rev' {α : Type} (xs : list α) : reverse xs = reverse' xs :=
  by simp [reverse', it_rev, app_nil]

end mylist

namespace tree

inductive tree (α : Type) where
  | tip  : α -> tree α
  | node : tree α -> α -> tree α -> tree α

def mirror {α : Type} : tree α -> tree α
  | tree.tip x      => tree.tip x
  | tree.node l x r => tree.node (mirror r) x (mirror l)

theorem mirror_mirror {α : Type} (t : tree α) : mirror (mirror t) = t :=
  match t with
  | tree.tip x => rfl
  | tree.node l x r => by simp [mirror, mirror_mirror]

open mylist

def contents {α : Type} : tree α -> list α
  | tree.tip x => single x
  | tree.node l x r => append (append (contents l) (single x)) (contents r)

def sum_tree : tree Nat -> Nat
  | tree.tip x => x
  | tree.node l x r => x + sum_tree l + sum_tree r

def sum_list : list Nat -> Nat
  | list.nil => 0
  | list.cons x xs => x + sum_list xs

theorem sum_append (xs ys : list Nat) : sum_list (append xs ys) = sum_list xs + sum_list ys :=
  match xs with
  | list.nil        => by simp [append, sum_list]
  | list.cons x xs' => by simp [append, sum_list, sum_append, Nat.add_assoc]

-- ex 2.6
theorem sum_contents (t : tree Nat) : sum_tree t = sum_list (contents t) :=
  match t with
  | tree.tip x => rfl
  | tree.node l x r => by simp [sum_tree, contents, sum_append, sum_contents, single, sum_list, Nat.add_comm]

end tree


namespace basics

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

open Weekday

def next_weekday(d: Weekday) : Weekday :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | _         => monday

example : next_weekday (next_weekday friday) = tuesday := rfl

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl

-- #eval next (next tuesday)      -- Weekday.thursday
-- #eval next (previous tuesday)  -- Weekday.tuesday

-- example : next (previous tuesday) = tuesday :=
--   rfl

inductive Bool where
  | tt
  | ff
  deriving Repr

open Bool

def negb (b:Bool) : Bool :=
  match b with
  | tt => ff
  | ff => tt

def andb (b1 b2 : Bool)  : Bool :=
  match b1 with
  | tt => b2
  | ff => ff

def orb (b1 b2 : Bool) : Bool :=
  match b1 with
  | tt => tt
  | ff => b2


example : (orb tt ff) = tt := by rfl
example : (orb ff ff) = ff := by rfl
example : (orb ff tt) = tt := by rfl
example : (orb tt tt) = tt := by rfl

inductive Peano where
  | Z
  | S : Peano -> Peano
  deriving Repr

open Peano



def plus (n m : Peano) : Peano :=
  match n with
  | Z => m
  | S n' => S (plus n' m)

def mult (n m : Peano) : Peano :=
  match n with
  | Z => Z
  | S n' => plus m (mult n' m)

def sub (n m : Peano) : Peano :=
  match n, m with
  | _   , Z    => n
  | Z   , _    => Z
  | S n', S m' => sub n' m'

def eq (n m : Peano) : Bool :=
  match n, m with
  | Z, Z       => tt
  | S n', S m' => eq n' m'
  | _, _       => ff

def le (n m : Peano) : Bool :=
  match n, m with
  | Z   , _    => tt
  | S _ , Z    => ff
  | S n', S m' => le n' m'

def even (n: Peano) : Bool :=
  match n with
  | Z => tt
  | S Z => ff
  | S (S n) => even n

def zero  := Z
def one   := S Z
def two   := S (S Z)
def three := S (S (S Z))
def four  := S (S (S (S Z)))

#eval eq (plus two two) four

theorem plus_Z_n : ∀ (n: Peano), plus Z n = n := by
  intros
  rfl

theorem plus_n_Z : ∀ (n: Peano), plus n Z = n := by
  intros n
  induction n
  . rfl
  . simp [plus]
    assumption

theorem mult_Z_n (n : Peano) : mult Z n = Z := rfl

theorem mult_n_Z (n : Peano) : mult n Z = Z := by
  cases n
  . rfl
  . simp [mult, mult_n_Z, plus]

theorem plus_n_Z' (n: Peano): plus n Z = n :=
  match n with
  | Z => rfl
  | S n' => by simp [plus, plus_n_Z']

theorem plus_id_exercise (n m o : Peano) : n = m -> m = o -> plus n m = plus m o := by
  intros nm mo
  simp [nm, mo]

theorem mult_n_Z_m_Z (n m : Peano) : plus (mult n Z) (mult m Z) = Z := by
  simp [mult_n_Z, plus]

theorem mult_n_one (n : Peano) : mult n one = n :=
  match n with
  | Z => rfl
  | S n' => by simp [mult, mult_n_one]; rfl


theorem plus_1_neq_0 (n : Peano) : eq (plus n one) Z = ff := by
  cases n
  . rfl
  . rfl

theorem negb_involutive (b : Bool) : negb (negb b) = b := by
  cases b
  . rfl
  . rfl

theorem andb_commutative (b c : Bool) : andb b c = andb c b := match b, c with
  | ff, ff => rfl
  | ff, tt => rfl
  | tt, ff => rfl
  | tt, tt => rfl

theorem andb_commutative' (b c : Bool) : andb b c = andb c b := by
  cases b <;> (cases c <;> rfl)

theorem andb3_exchange (b c d : Bool) : andb (andb b c) d = andb (andb b d) c := by
  cases b <;> (cases c <;> (cases d <;> rfl))


theorem andb_true_elim2 (b c : Bool) : andb b c = tt -> c = tt := by
  cases b <;> simp [andb]

theorem zero_nbeq_plus_1 (n : Peano) : eq Z (plus n one) = ff := by
  cases n <;> simp [plus, eq]


theorem rewrite_comm (b c : Bool): b = c -> c = b := by
  intros bc; simp [bc]


theorem andb_eq_orb (b c : Bool): (andb b c = orb b c) -> b = c := by
  cases b
  . simp [andb, orb]
    intros ctt
    simp [ctt]
  . simp [andb, orb]

inductive Bin where
  | BZ
  | B0 : Bin -> Bin
  | B1 : Bin -> Bin
  deriving Repr

open Bin

def incr (m: Bin) : Bin :=
  match m with
  | BZ    => B1 BZ
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')

def b0 := BZ
def b1 := B1 BZ
def b2 := B0 (B1 BZ)
def b3 := B1 (B1 BZ)
def b4 := B0 (B0 (B1 BZ))

example : incr b0 = b1 := rfl
example : incr b1 = b2 := rfl
example : incr b2 = b3 := rfl
example : incr b3 = b4 := rfl

def bin_to_nat (m: Bin) : Peano :=
  match m with
  | BZ    => Z
  | B0 m' => let pm' := (bin_to_nat m')
             plus pm' pm'
  | B1 m' => let pm' := (bin_to_nat m')
             S (plus pm' pm')

example : bin_to_nat b0 = zero  := rfl
example : bin_to_nat b1 = one   := rfl
example : bin_to_nat b2 = two   := rfl
example : bin_to_nat b3 = three := rfl


-- 0  (BZ)             ==> B1 BZ
-- 1  (B1 BZ)          ==> B0 (B1 BZ)
-- 2  (B0 (B1 BZ))     ==> B1 (B1 BZ)
-- 3  (B1 (B1 BZ))     ==> B0 (B0 (B1 Z))
-- 4  (B0 (B0 (B1 Z))  ==>

end basics
