
import LeanConcreteSemantics.Basic

#eval hello
#check mylist.reverse
#check mylist.length_append

open basics
open Peano
open Bool

theorem plus_Z_r (n:Peano) : plus n Peano.Z = n := by
  cases n
  . rfl
  . simp [plus, plus_Z_r]

theorem plus_Z_r' (n:Peano) : plus n Peano.Z = n := by
  induction n with
  | Z => rfl
  | S n' ih => simp [plus, ih]

theorem plus_Z_r'' : ∀ (n:Peano),  plus n Peano.Z = n := by
  intros n
  induction n with
  | Z => rfl
  | S n' => simp [plus, *]

theorem minus_n_n : ∀ (n: Peano), sub n n = Z := by
  intros n
  induction n
  case Z => rfl
  case S => simp [sub, *]

theorem minus_n_n' (n: Peano):  sub n n = Z := by
  induction n with
  | Z => rfl
  | S => simp [sub, *]

theorem mult_Z_r : ∀ (n: Peano), mult n Z = Z := by
  intros n
  induction n
  case Z => rfl
  case S => simp [mult, plus, *]

theorem plus_S_r : ∀ (n m : Peano), plus n (S m) = S (plus n m) := by
  intros n m
  induction n <;> simp [plus, *]
  -- case Z => simp [plus]
  -- case S => simp [plus, *]


theorem plus_comm : ∀ (n m : Peano), plus n m = plus m n := by
  intros n m
  induction n
  case Z => simp [plus, plus_Z_r]
  case S => simp [plus, plus_S_r, *]

theorem plus_assoc : ∀ (a b c : Peano), plus (plus a b) c = plus a (plus b c) := by
  intros a b c
  induction a
  case Z => simp [plus]
  case S => simp [plus, *]

def double (n: Peano) : Peano :=
  match n with
  | Z => Z
  | S n' => S (S (double n'))

theorem double_plus : ∀ (n: Peano), double n = plus n n := by
  intros n
  induction n
  case Z => rfl
  case S => simp [double, plus, plus_S_r, *]

theorem eqb_refl : ∀ (n : Peano), eq n n = tt := by
  intros n; induction n
  case Z => rfl
  case S => simp [eq, *]

theorem even_S : ∀ (n : Peano), even (S n) = negb (even n) := by
  intros n; induction n
  case Z => rfl
  case S => simp [even, *, negb_involutive]

theorem mult_0_plus' : ∀ (n m : Peano), mult (plus (plus n Z) Z) m = mult n m := by
  intros n m
  simp [plus_n_Z]

theorem plus_rearrange_firsttry : ∀ (n m p q : Peano),
  plus (plus n m) (plus p q) = plus (plus m n) (plus p q) := by
  intros n m p q
  simp [plus_comm]


theorem add_shuffle3 : ∀ n m p : Peano, plus n (plus m p) = plus m (plus n p) := by
  intros m n p
  calc
    plus m (plus n p) = plus (plus m n) p := by simp [plus_assoc]
    _                 = plus (plus n m) p := by simp [plus_comm]
    _                 = plus n (plus m p) := by simp [plus_assoc]

theorem add_shuffle3' : ∀ n m p : Peano, plus n (plus m p) = plus m (plus n p) := by
  intros m n p
  have h1 :plus m (plus n p) = plus (plus m n) p  := by simp [plus_assoc]
  have h2 :plus (plus m n) p = plus (plus n m) p  := by simp [plus_comm]
  have h3 :plus (plus n m) p = plus n (plus m p)  := by simp [plus_assoc]
  simp [*]

theorem mult_S_r : ∀ n m : Peano, mult n (S m) = plus n (mult n m) := by
  intros n m
  induction n
  case Z => simp [mult, plus]
  case S => simp [mult, plus, *, add_shuffle3]

theorem mult_comm : ∀ n m : Peano, mult n m = mult m n := by
  intros n m
  induction n
  case Z => simp [mult, mult_Z_r]
  case S => simp [mult, mult_S_r, *]


theorem plus_leb_compat_l : ∀ n m p : Peano, le n m = tt -> le (plus p n) (plus p m) = tt := by
  intros n m p
  intro le_mn
  induction p
  case Z => simp [plus, *]
  case S => simp [plus, le, *]

theorem leb_refl : ∀ n : Peano, le n n = tt := by
  intros n; induction n <;> simp [le, *]

theorem zero_neqb_S : ∀ n:Peano, eq Z (S n) = ff := by
  intros n
  rfl

theorem andb_false_r : ∀ (b : basics.Bool), andb b ff = ff := by
  intros b
  cases b <;> simp [andb]

theorem S_neqb_zero: ∀ n:Peano, eq (S n) Z = ff := by
  intros n
  rfl

theorem mult_1_l : ∀ n:Peano, mult one n = n := by
  intros n
  simp [mult, plus_n_Z]

-- Proof.
--   (* FILL IN HERE *) Admitted.
-- Theorem all3_spec : ∀ b c : bool,
--   orb
--     (andb b c)
--     (orb (negb b)
--          (negb c))
--   = true.
-- Proof.
--   (* FILL IN HERE *) Admitted.
-- Theorem mult_plus_distr_r : ∀ n m p : nat,
--   (n + m) × p = (n × p) + (m × p).
-- Proof.
--   (* FILL IN HERE *) Admitted.
-- Theorem mult_assoc : ∀ n m p : nat,
--   n × (m × p) = (n × m) × p.
-- Proof.
--   (* FILL IN HERE *) Admitted.
-- ☐
