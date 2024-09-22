namespace MyBool

inductive Bool where
  | tt
  | ff
  deriving Repr

open Bool

def and(b1 b2: Bool) : Bool :=
  match b1, b2 with
  | tt, tt => tt
  | _, _   => ff

def or (b1 b2: Bool) : Bool :=
  match b1, b2 with
  | ff, ff => ff
  | _, _   => tt

-- exercise
theorem conj_comm : ∀ (b1 b2 : Bool), and b1 b2 = and b2 b1 := by
  intros b1 b2
  cases b1 <;> cases b2 <;> rfl

-- exercise
theorem or_comm : ∀ (b1 b2 : Bool), or b1 b2 = or b2 b1 := by
  intros b1 b2
  cases b1 <;> cases b2 <;> rfl


end MyBool


namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

open Nat

def n0 : Nat := zero
def n1 : Nat := succ zero
def n2 : Nat := succ (succ zero)
def n3 : Nat := succ (succ (succ zero))

def add (n m: Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)

example : add n1 n2 = n3 := by rfl

theorem add_zero (n: Nat) : add n zero = n := by
  induction n with
  | zero => rfl
  | succ => simp [add, *]


end MyNat

namespace MyList

inductive List (α : Type) where
  | nil : List α
  | cons : α -> List α -> List α
  deriving Repr

open List

def list0123 := cons 0 (cons 1 (cons 2 (cons 3 nil)))
def list3210 := cons 3 (cons 2 (cons 1 (cons 0 nil)))

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (app xs' ys)

example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = list0123 := by
  simp [app, list0123]

def singleton {α : Type} (x: α) : List α := cons x nil

def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | nil => nil
  | cons x xs' => app (rev xs') (singleton x)

example : rev list0123 = list3210 := rfl

example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = cons 0 (cons 1 (cons 2 (cons 3 nil))) := rfl

theorem app_nil : ∀ {α : Type} (xs: List α), app xs nil = xs := by
  intro α xs
  induction xs
  case nil => rfl
  case cons => simp [app, *]

theorem app_assoc : ∀ {α : Type} (xs ys zs: List α), app (app xs ys) zs = app xs (app ys zs) := by
  intros  α xs ys zs
  induction xs
  case nil => rfl
  case cons => simp [app, *]

theorem rev_app : ∀ {α : Type} (xs ys: List α), rev (app xs ys) = app (rev ys) (rev xs) := by
  intro α xs ys
  induction xs
  case nil => simp [app, rev, app_nil]
  case cons x xs' ih => simp [app, rev, ih, app_assoc]

theorem rev_rev : ∀ {α : Type} (xs: List α), rev (rev xs) = xs := by
  intro α xs
  induction xs
  case nil  => rfl
  case cons => simp [rev, rev_app, app, *]


def length {α : Type} (xs: List α) : Nat :=
  match xs with
  | nil => 0
  | cons _ xs' => 1 + length xs'

def pos_length (xs: List Nat) : Nat :=
  match xs with
  | nil => 0
  | cons x xs' => if x = 1 then length xs' + x else length xs'

theorem pos_len: ∀ (xs : List Nat), pos_length xs <= length xs := by
  intros xs
  induction xs
  case nil  => simp [pos_length]
  case cons x xs' _ =>
    simp [pos_length, length]
    split
    . simp [*, Nat.add_comm]
    . simp []


def count (k : Nat) (xs: List Nat) : Nat :=
  match xs with
  | nil => 0
  | cons x xs => if x = k then 1 + count k xs else count k xs

theorem count_length : ∀ (k : Nat) (xs : List Nat), count k xs <= length xs := by
  intros k xs
  induction xs
  case nil => simp [count]
  case cons x xs' ih =>
    simp [count, length]
    split
    . simp [*]
    . calc
        count k xs' <= length xs'     := by simp [*]
        _           <= length xs' + 1 := by simp []
        _           = 1 + length xs'  := by simp [Nat.add_comm]


def snoc {α : Type} (xs: List α) (y: α) : List α :=
  match xs with
  | nil => singleton y
  | cons x xs => cons x (snoc xs y)

def rev' {α : Type} (xs: List α) : List α :=
  match xs with
  | nil => nil
  | cons x xs => snoc (rev' xs) x

example : rev' (cons 1 (cons 2 (cons 3 nil))) = cons 3 (cons 2 (cons 1 nil)) := rfl

theorem rev_snoc_snoc : ∀ {α : Type} (xs: List α) (y: α), rev' (snoc xs y) = cons y (rev' xs) := by
  intros α xs y
  induction xs
  case nil => rfl
  case cons x xs ih => simp [snoc, rev', ih]

theorem rev_rev_snoc : ∀ {α : Type} (xs: List α), rev' (rev' xs) = xs := by
  intros α xs
  induction xs
  case nil => rfl
  case cons x xs ih => simp [rev', rev_snoc_snoc, ih]


def sum_to (n: Nat) : Nat :=
  match n with
  | 0           => 0
  | Nat.succ n' => n + sum_to n'

theorem sum_to_eq : ∀ (n : Nat), 2 * sum_to n = n * (n + 1) := by
  intros n
  induction n
  case zero => rfl
  case succ => simp_arith [*, sum_to, Nat.mul_add, Nat.mul_comm]

end MyList

section Tree

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α -> α -> Tree α -> Tree α
  deriving Repr

open Tree

def mirror {α : Type} (t: Tree α) : Tree α :=
  match t with
  | leaf => leaf
  | node l x r => node (mirror r) x (mirror l)

theorem mirror_mirror : ∀ {α : Type} (t: Tree α), mirror (mirror t) = t := by
  intros α t
  induction t
  case leaf => rfl
  case node => simp [mirror, *]

end Tree

open Nat
open List

def div2 (n: Nat) : Nat :=
  match n with
  | zero => zero
  | succ zero => zero
  | succ (succ n') => succ (div2 n')

theorem div2_thm : ∀ (n: Nat), div2 (n + n) = n := by
  intros n
  induction n
  case zero => rfl
  case succ n' ih =>
    calc
      div2 (n' + 1 + (n' + 1)) = div2 (((n' + n') + 1) + 1) := by simp_arith []
      _                        = div2 (n' + n') + 1         := by simp [div2]
      _                        = n' + 1                     := by simp [ih]


--- NEXT: 2.6

-- literals
example : [1,2,3] = cons 1 (cons 2 (cons 3 nil)) := by rfl

-- nil
example : ([] : List Nat) = (nil : List Nat) := by rfl

-- cons
example : 1 :: [2,3] = cons 1 (cons 2 (cons 3 nil)) := by rfl

-- append
example : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6] := by rfl

#eval 1 - 10
