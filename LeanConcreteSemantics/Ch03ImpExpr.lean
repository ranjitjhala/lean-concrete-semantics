set_option pp.fieldNotation false

namespace section_3_1

abbrev Val := Nat
abbrev Vname := String

inductive Aexp where
  | Num : Val -> Aexp
  | Var : Vname -> Aexp
  | Add : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

def aexp_5 := Num 5
def aexp_x := Var "x"
def aexp_x_plus_y := Add (Var "x") (Var "y")
def aexp_2_plus_z_plus_3 := Add (Num 2) (Add (Var "z") (Num 3))

abbrev State := Vname -> Val

-- #asknico get rid of `.Add`
def aval (a: Aexp) (s: State) : Val :=
  match a with
  | .Num n => n
  | .Var x => s x
  | .Add a1 a2 => aval a1 s + aval a2 s

-- initial state
def st0 : State := λ _ => 0

example : aval aexp_5 st0 = 5 := rfl
example : aval aexp_x st0 = 0 := rfl

-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

def st1 := st0 ["x" := 2] [ "y" := 10 ] [ "z" := 100 ]

example : aval aexp_x_plus_y st1 = 12 := rfl
example : aval aexp_2_plus_z_plus_3 st1 = 105 := rfl

def asimp_const (a: Aexp) : Aexp :=
  match a with
  | .Num n => Num n
  | .Var x => Var x
  | .Add a1 a2 => match asimp_const a1, asimp_const a2 with
    | Num n1, Num n2 => Num (n1 + n2)
    | a1', a2' => Add a1' a2'

theorem aval_asimp_const : ∀ {a: Aexp} {s: State}, aval a s = aval (asimp_const a) s  := by
  intros a s
  induction a using asimp_const.induct <;> simp [asimp_const, aval, *]
  -- case case1 => rfl
  -- case case2 => rfl
  -- case case3 a1 a2 n1 n2 _ _ _ _ => simp [asimp_const, aval, *]
  -- case case4 => simp [asimp_const, aval, *]

theorem aval_asimp_const' : ∀ {a: Aexp} {s: State}, aval (asimp_const a) s  = aval a s := by
  intros a s
  induction a using asimp_const.induct <;> simp_all [asimp_const, aval]

def plus (a1: Aexp) (a2: Aexp) : Aexp :=
  match a1, a2 with
  | Num n1, Num n2 => Num (n1 + n2)
  | Num n , a      => if n = 0 then a else Add (Num n) a
  | a, Num n       => if n = 0 then a else Add a (Num n)
  | _, _           => Add a1 a2

theorem aval_plus: ∀ {a1 a2 : Aexp}, aval (plus a1 a2) s = aval a1 s + aval a2 s := by
  intros a1 a2
  cases a1 <;> cases a2 <;> simp_arith [plus, aval] <;> split <;> simp [aval, *]


def asimp (a: Aexp) : Aexp :=
  match a with
  | .Num n => Num n
  | .Var x => Var x
  | .Add a1 a2 => plus (asimp a1) (asimp a2)

theorem aval_asimp : ∀ {a: Aexp} {s: State}, aval a s = aval (asimp a) s := by
  intros a s
  induction a using asimp.induct <;> simp [asimp, aval, aval_plus, *]


-- ex 3.1
def optimal (a: Aexp) : Bool :=
  match a with
  | .Num _ => true
  | .Var _ => true
  | .Add (Num _) (Num _) => false
  | .Add a1 a2 => optimal a1 && optimal a2

theorem optimal_asimp_const : ∀ {a: Aexp}, optimal (asimp_const a) = true := by
  intros a
  induction a using asimp_const.induct <;> simp_all [asimp_const, optimal]

-- ex 3.2
inductive AexpOpt where
  | AONum : Val -> AexpOpt
  | AOVar : Vname -> AexpOpt -> AexpOpt

open AexpOpt

def unopt (ao: AexpOpt) : Aexp :=
  match ao with
  | AONum n => Num n
  | AOVar x ao' => Add (Var x) (unopt ao')

def aval_opt (ao: AexpOpt) (s: State) : Val :=
  aval (unopt ao) s

def aoplusn (n : Val) (ao: AexpOpt) : AexpOpt :=
  match ao with
  | AONum m => AONum (n + m)
  | AOVar x ao' => AOVar x (aoplusn n ao')

-- #asknico
theorem add_silly : ∀ {x y z : Val}, x + (y + z) = y + (x + z) := by
  intros x y z
  calc
    x + (y + z) = (x + y) + z := by simp [Nat.add_assoc]
    _           = (y + x) + z := by simp [Nat.add_comm]
    _           = y + (x + z) := by simp [Nat.add_assoc]

theorem aoplusn_aval : ∀ {n: Val} {ao: AexpOpt} {s: State}, aval (unopt (aoplusn n ao)) s = n + aval (unopt ao) s := by
  intros n ao s
  induction ao
  case AONum m => simp_arith [aoplusn, aval_opt, aval, unopt]
  case AOVar x ao ih => simp [aval_opt] at ih
                        simp [aoplusn, aval_opt, aval, ih, add_silly]

def aoplus (ao other: AexpOpt) : AexpOpt :=
  match ao with
  | AONum n => aoplusn n other
  | AOVar x ao' => AOVar x (aoplus ao' other)

theorem aoplus_aval : ∀ {ao1 ao2: AexpOpt} {s: State}, aval (unopt (aoplus ao1 ao2)) s = aval (unopt ao1) s + aval (unopt ao2) s := by
  intros ao1 ao2 s
  induction ao1
  case AONum n => simp [aoplus,aval_opt, aval, unopt, aoplusn_aval]
  case AOVar x ao ih => simp [aoplus, aval_opt, unopt, ih, aval, Nat.add_assoc]

def asimp_opt (a: Aexp) : AexpOpt :=
  match a with
  | .Num n => AONum n
  | .Var x => AOVar x (AONum 0)
  | .Add a1 a2 => aoplus (asimp_opt a1) (asimp_opt a2)

theorem asimp_opt_aval : ∀ {a : Aexp} {s: State}, aval (unopt (asimp_opt a)) s = aval a s := by
  intros a s
  induction a using asimp.induct <;> simp [asimp_opt, unopt, aoplus_aval, aval, aval_opt, *]

def asimp_full (a:Aexp) : Aexp := unopt (asimp_opt a)

theorem asimp_full_aval : ∀ {a : Aexp} {s: State}, aval (asimp_full a) s = aval a s := by
  intros a s
  simp [asimp_full, asimp_opt_aval]

-- ex 3.3

def subst (x : Vname) (xa : Aexp) (a : Aexp) : Aexp :=
  match a with
  | .Num n => Num n
  | .Var y => if x = y then xa else Var y
  | .Add a1 a2 => Add (subst x xa a1) (subst x xa a2)

example : subst "x" (Num 3) (Add (Var "x") (Var "y")) = Add (Num 3) (Var "y") := rfl

theorem subst_aval : ∀ {x : Vname} {xa a : Aexp} {s: State}, aval (subst x xa a) s = aval a (s [x := aval xa s]) := by
  intros x xa a s
  induction a
  case Num n => simp [subst, aval]
  case Var y => simp [subst, aval]
                split
                case isTrue => simp [upd, *]
                case isFalse => simp [upd, *]; split <;> simp_all [aval]
  case Add a1 a2 ih1 ih2 => simp [subst, aval, *]

end section_3_1

namespace section_3_2

open section_3_1

-- inductive Bexp where
--   | Bcon : Bool -> Bexp
--   | Bnot : Bexp -> Bexp
--   | Band : Bexp -> Bexp -> Bexp
--   | BLeq : Aexp -> Aexp -> Bexp
--   deriving Repr

-- open Bexp

-- def bval (b: Bexp) (s: State) : Bool :=
--   match b with
--   | Bcon v => v
--   | Bnot b' => !bval b' s
--   | Band b1 b2 => bval b1 s && bval b2 s
--   | BLeq a1 a2 => aval a1 s <= aval a2 s

inductive Bexp where
  | Bvar : Vname -> Bexp
  | Bnot : Bexp  -> Bexp
  | Band : Bexp  -> Bexp -> Bexp
  | Bor  : Bexp  -> Bexp -> Bexp
  deriving Repr

open Bexp

abbrev BState := Vname -> Bool

def bval (b: Bexp) (s: BState) : Bool :=
  match b with
  | Bvar v => s v
  | Bnot b' => !bval b' s
  | Band b1 b2 => bval b1 s && bval b2 s
  | Bor  b1 b2 => bval b1 s || bval b2 s

def is_var (b : Bexp) : Bool :=
  match b with
  | Bvar _ => true
  | _ => false

def is_nnf (b : Bexp) : Bool :=
  match b with
  | Bvar _ => true
  | Bnot b' => is_var b'
  | Band b1 b2 => is_nnf b1 && is_nnf b2
  | Bor b1 b2 => is_nnf b1 && is_nnf b2

def nnf_helper (b: Bexp) (top: Bool) :=
  match top, b with
  | true, Bvar v      => Bvar v
  | false, Bvar v     => Bnot (Bvar v)
  | true, Bnot b'     => nnf_helper b' false
  | false, Bnot b'     => nnf_helper b' true
  | true, Band b1 b2  => Band (nnf_helper b1 true)   (nnf_helper b2 true)
  | false, Band b1 b2 => Bor  (nnf_helper b1 false)  (nnf_helper b2 false)
  | true, Bor b1 b2   => Bor  (nnf_helper b1 true)   (nnf_helper b2 true)
  | false, Bor b1 b2  => Band (nnf_helper b1 false)  (nnf_helper b2 false)

def nnf (b : Bexp) : Bexp := nnf_helper b true

-- #asknico apply same tactic to all remaining cases?
theorem nnf_helper_is_nnf : ∀ {b : Bexp} {top : Bool}, is_nnf (nnf_helper b top) = true := by
  intros b top
  induction b, top using nnf_helper.induct <;> simp_all [nnf_helper, is_nnf, is_var]

theorem nnf_is_nnf : ∀ {b : Bexp}, is_nnf (nnf b) = true := by
  simp [nnf, nnf_helper_is_nnf]

def flip (b1 b2: Bool) : Bool := if b1 then b2 else not b2

theorem nnf_helper_bval : ∀ {b : Bexp} {top : Bool}, bval (nnf_helper b top) s = flip (bval b s) top := by
  intros b top
  induction b, top using nnf_helper.induct <;> simp_all [nnf_helper, bval, flip]

theorem nnf_bval : ∀ {b : Bexp} {s: BState}, bval (nnf b) s = bval b s := by
  intros b s
  simp [nnf, nnf_helper_bval, flip]

def is_cube (b : Bexp) : Bool :=
  match b with
  | Bor _ _    => false
  | Band b1 b2 => is_cube b1 && is_cube b2
  | _          => is_nnf b

def is_dnf (b : Bexp) : Bool :=
  match b with
  | Bor b1 b2  => is_dnf b1 && is_dnf b2
  | Band b1 b2 => is_cube b1 && is_cube b2
  | _          => is_nnf b

theorem is_cube_is_nnf : ∀ { b : Bexp}, is_cube b = true -> is_nnf b = true := by
  intros b
  induction b using is_cube.induct
  case case1 => simp [is_cube]
  case case2 => simp_all [is_cube,is_nnf]
  case case3 b _ _ => cases b <;> simp_all [is_cube, is_nnf]

theorem is_dnf_is_nnf : ∀ { b : Bexp}, is_dnf b = true -> is_nnf b = true := by
  intros b
  induction b
  case Bvar _ => simp [is_dnf, is_nnf]
  case Bnot b' _ => simp [is_dnf, is_nnf]
  case Band b1 b2 _ _ => simp_all [is_dnf, is_nnf, is_cube_is_nnf]
  case Bor b1 b2 ih1 ih2 => simp_all [is_dnf, is_nnf]

def cube_and (a b : Bexp) : Bexp :=
  match b with
  | Bor b1 b2 => Bor (cube_and a b1) (cube_and a b2)
  | Band _ _  => Band a b
  | Bvar _  => Band a b
  | Bnot _  => Band a b

theorem cube_and_is_dnf : ∀ {a b : Bexp}, is_cube a = true -> is_dnf b = true -> is_dnf (cube_and a b) = true := by
  intros a b
  induction b generalizing a <;> simp_all [cube_and, is_dnf, is_cube]

def dnf_and (a b : Bexp) : Bexp :=
  match a with
  | Bor a1 a2 => Bor (dnf_and a1 b) (dnf_and a2 b)
  | Band _ _  => cube_and a b
  | Bvar  _   => cube_and a b
  | Bnot _    => cube_and a b

theorem dnf_and_is_dnf : ∀ {a b : Bexp}, is_dnf a = true -> is_dnf b = true -> is_dnf (dnf_and a b) = true := by
  intros a b
  induction a generalizing b
  case Bor  => simp_all [is_dnf]
  case Band a1 a2 _ _ => simp_all [is_dnf,dnf_and]
                         intros
                         apply cube_and_is_dnf
                         simp_all [is_cube]
                         assumption
  case Bvar a => simp_all [dnf_and]
                 intros
                 have h : is_cube (Bvar a) = true := by rfl
                 apply cube_and_is_dnf <;> assumption

  case Bnot a _  => simp_all [dnf_and]
                    intros
                    have h : is_cube (Bnot a) = true := by simp_all [is_dnf, is_nnf, is_cube]
                    apply cube_and_is_dnf <;> assumption

def dnf_of_nnf (b : Bexp) : Bexp :=
  match b with
  | Band b1 b2 => dnf_and (dnf_of_nnf b1) (dnf_of_nnf b2)
  | Bor  b1 b2 => Bor (dnf_of_nnf b1) (dnf_of_nnf b2)
  | Bvar _     => b
  | Bnot _     => b

theorem dnf_of_nnf_is_dnf : ∀ {b : Bexp}, is_nnf b -> is_dnf (dnf_of_nnf b) = true := by
  intros b
  induction b <;> simp_all [dnf_of_nnf, is_nnf, is_dnf, dnf_and_is_dnf]

theorem cube_and_bval : ∀ {a b : Bexp} {s: BState}, bval (cube_and a b) s = (bval a s && bval b s) := by
  intros a b s
  induction b generalizing a
  case Bor b1 b2 => simp_all [cube_and, bval, Bool.and_or_distrib_left]
  case Band b1 b2 ih1 ih2 => simp_all [cube_and, bval, ih1, ih2]
  case Bvar _ => simp [cube_and, bval]
  case Bnot _ => simp [cube_and, bval]

theorem dnf_and_bval : ∀ {a b : Bexp} {s: BState}, bval (dnf_and a b) s = (bval a s && bval b s) := by
  intros a b s
  induction a
  case Bor    => simp_all [dnf_and, bval, Bool.and_or_distrib_right]
  case Band   => simp_all [dnf_and, bval, cube_and_bval]
  case Bvar _ => simp_all [dnf_and, bval, cube_and_bval]
  case Bnot _ => simp_all [dnf_and, bval, cube_and_bval]

theorem dnf_bval : ∀ {b : Bexp} {s: BState}, bval (dnf_of_nnf b) s = bval b s := by
  intros b s
  induction b
  case Bvar _ => rfl
  case Bnot b' ih => simp [dnf_of_nnf, bval, ih]
  case Bor b1 b2 ih1 ih2 => simp [dnf_of_nnf, bval, ih1, ih2]
  case Band b1 b2 ih1 ih2 => simp_all [dnf_and_bval, bval, dnf_of_nnf, dnf_and_bval]

end section_3_2
