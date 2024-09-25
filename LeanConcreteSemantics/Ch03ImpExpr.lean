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

-- nico's version
theorem dnf_and_is_dnf' : ∀ {a b : Bexp}, is_dnf a -> is_dnf b -> is_dnf (dnf_and a b) := by
  intros a b a_dnf b_dnf
  induction a generalizing b <;> simp_all [is_dnf] <;> apply cube_and_is_dnf <;> try trivial
  simp_all [is_cube]

-- nico's version
theorem dnf_and_is_dnf'' : ∀ {a b : Bexp}, is_dnf a -> is_dnf b -> is_dnf (dnf_and a b) := by
  intros a b a_dnf b_dnf
  induction a generalizing b -- <;> simp_all [is_dnf] <;> apply cube_and_is_dnf <;> try trivial
  case Band a1 a2 _ _ => simp_all [is_dnf]; apply cube_and_is_dnf; simp_all [is_cube]; assumption
  case Bor a1 a2 _ _ => simp_all [is_dnf]
  case Bvar _ => apply simp_all

  -- simp_all [is_cube]



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

namespace section_3_3

open section_3_1

inductive Instr where
  | LOADI : Val -> Instr
  | LOAD  : Vname -> Instr
  | ADD   : Instr
  deriving Repr

open Instr

abbrev Stack := List Val


-- def exec1 (i:Instr) (s:State) (stk:Stack) : Option Stack :=
--   match i with
--   | LOADI n => some (n :: stk)
--   | LOAD  x => some (s x :: stk)
--   | ADD     => match stk with
--                 | n1::n2::stk' => some ((n2 + n1) :: stk')
--                 | _ => none

def exec1 (s:State) (i:Instr) (stk:Stack) : Stack :=
  match i, stk with
  | LOADI n, _         => (n :: stk)
  | LOAD  x, _         => (s x :: stk)
  | ADD    , n::m::stk => (m + n) :: stk
  | ADD    , _         => []

def exec (s:State) (is: List Instr) (stk:Stack) : Stack :=
  match is with
  | []     => stk
  | i::is' => exec s is' (exec1 s i stk)

def comp (a: Aexp) : List Instr :=
  match a with
  | .Num n => [LOADI n]
  | .Var x => [LOAD  x]
  | .Add a1 a2 => comp a1 ++ comp a2 ++ [ADD]

theorem exec_append : ∀ {s : State} {is1 is2 : List Instr} {stk : Stack},
  exec s (is1 ++ is2) stk = exec s is2 (exec s is1 stk) := by
  intros s is1 is2 stk
  induction is1 generalizing stk
  case nil => rfl
  case cons i is1' ih => simp [exec, ih]

theorem comp_exec : ∀ {s : State} {a : Aexp} { stk : Stack },
  exec s (comp a) stk = aval a s :: stk := by
  intro s a stk
  induction a generalizing s stk
  case Num n => rfl
  case Var x => rfl
  case Add a1 a2 ih1 ih2 => simp_all [comp, aval, exec_append, exec, exec1]

-- TODO: 3.10 "option" / skip

abbrev Reg := Nat
abbrev RState := Reg -> Val

inductive RInst where
  | RLDI : Val -> Reg -> RInst
  | RLD  : Vname -> Reg -> RInst
  | RADD : Reg -> Reg -> RInst
  deriving Repr

open RInst

def rupd (rs: RState) (r: Reg) (n: Val) : RState :=
  λ r' => if r = r' then n else rs r'

def rexec1 (s: State) (i: RInst) (rs: RState) : RState :=
  match i with
  | RLDI n r  => rupd rs r  n
  | RLD  x r  => rupd rs r  (s x)
  | RADD r r' => rupd rs r (rs r + rs r')

def rexec (s: State) (is: List RInst) (rs: RState) : RState :=
  match is with
  | []     => rs
  | i::is' => rexec s is' (rexec1 s i rs)

def rcomp (a: Aexp) (r: Reg) : List RInst :=
  match a with
  | .Num n => [RLDI n r]
  | .Var x => [RLD  x r]
  | .Add a1 a2 => rcomp a1 r ++ (rcomp a2 (r+1) ++ [RADD r (r+1)])

theorem rexec_append : ∀ {s : State} {is1 is2 : List RInst} {rs: RState},
  rexec s (is1 ++ is2) rs = rexec s is2 (rexec s is1 rs) := by
  intros s is1 is2 rs
  induction is1 generalizing rs
  case nil => rfl
  case cons i is1' ih => simp [rexec, ih]

theorem succ_contra : forall {n : Nat}, n+1 = n -> False := by
  intros n h; induction n <;> simp_all

theorem lt_succ : ∀ {n m : Nat}, n < m -> n < m + 1 := by
  intros n m h
  omega

theorem rexec1_sep : ∀ {s: State} { r r' r'': Reg} {rs: RState},
  r < r' -> rexec1 s (RADD r' r'') rs r = rs r := by
  intros s r r' r'' rs lt
  simp_all [rexec1, rupd]
  intros
  simp_all

theorem rcomp_sep : ∀ {s: State} {a: Aexp} { r r': Reg}  {rs: RState},
  r < r' -> rexec s (rcomp a r') rs r = rs r := by
  intros s a r r' rs lt
  induction a generalizing r' rs
  case Num n =>
    simp_all [rexec, rexec1, rupd]; intros heq; simp_all [heq]
  case Var x =>
    simp_all [rexec, rexec1, rupd]; intros heq; simp_all [heq]
  case Add a1 a2 ih1 ih2 =>
    simp_all [rcomp, rexec_append, rexec, rexec1_sep]
    calc
      rexec s (rcomp a2 (r' + 1)) (rexec s (rcomp a1 r') rs) r
        = rexec s (rcomp a1 r') rs r := by apply ih2; apply lt_succ; assumption
      _ = rs r := by simp_all [ih1]

theorem rexec_rcomp : ∀ {a : Aexp} {r: Reg} {s: State} {rs: RState},
   rexec s (rcomp a r) rs r = aval a s := by
  intros a r s rs
  induction a generalizing r s rs
  case Num n => simp_all [rexec, rcomp, rexec1, aval, rupd]
  case Var x => simp_all [rexec, rcomp, rexec1, aval, rupd]
  case Add a1 a2 ih1 ih2 => simp_all [rexec, rcomp, rexec1, aval, rupd, rexec_append, ih1, ih2, rcomp_sep]

-- TODO: 3.12
inductive instr0 where
  | LDI0 : Val -> instr0
  | LD0  : Vname -> instr0
  | MV0  : Reg -> instr0
  | ADD0 : Reg -> instr0

open instr0

def r0exec1 (s: State) (i: instr0) (rs: RState) : RState :=
  match i with
  | LDI0 n => rupd rs 0 n
  | LD0  x => rupd rs 0 (s x)
  | MV0  r => rupd rs r (rs 0)
  | ADD0 r => rupd rs 0 (rs 0 + rs r)

def r0exec (s: State) (is: List instr0) (rs: RState) : RState :=
  match is with
  | []     => rs
  | i::is' => r0exec s is' (r0exec1 s i rs)

def r0comp (a: Aexp) (r: Reg) : List instr0 :=
  match a with
  | .Num n => [LDI0 n]
  | .Var x => [LD0  x]
  | .Add a1 a2 => (r0comp a2 r ++ [MV0 r]) ++ (r0comp a1 (r+1) ++ [ADD0 r])

theorem r0exec_append : ∀ {s : State} {is1 is2 : List instr0} {rs: RState},
  r0exec s (is1 ++ is2) rs = r0exec s is2 (r0exec s is1 rs) := by
  intros s is1 is2 rs
  induction is1 generalizing rs
  case nil => rfl
  case cons i is1' ih => simp [r0exec, ih]

theorem r0exec1_sep : ∀ {s: State} { r : Reg} {rs: RState},
  0 < r -> r0exec1 s (ADD0 r) rs r = rs r := by
  intros s r  rs lt
  simp_all [r0exec1, rupd]
  intros
  simp_all

-- #asknico
theorem r0comp_sep : ∀ {s: State} {a: Aexp} { r r': Reg}  {rs: RState},
  0 < r -> r < r' -> r0exec s (r0comp a r') rs r = rs r := by
  intros s a r r' rs pos lt
  induction a generalizing r' rs
  case Num n => simp_all [r0exec, r0exec1, rupd]; intros heq; simp_all [heq]
  case Var x => simp_all [r0exec, r0exec1, rupd]; intros heq; simp_all [heq]
  case Add a1 a2 ih1 ih2 =>
    simp_all [r0comp, r0exec_append]
    simp_all [r0exec, r0exec1, r0exec_append, rupd, ih1, ih2]
    split
    . case isTrue => simp_all []
    . case isFalse => calc
        r0exec s (r0comp a1 (r' + 1)) (rupd (r0exec s (r0comp a2 r') rs) r' (r0exec s (r0comp a2 r') rs 0)) r
          = rupd (r0exec s (r0comp a2 r') rs) r' (r0exec s (r0comp a2 r') rs 0) r := by apply ih1; apply lt_succ; assumption
        _ = r0exec s (r0comp a2 r') rs r := by simp_all [rupd]; intros; simp_all
        _ = rs r := by apply ih2; assumption

theorem r0exec_rcomp : ∀ {a : Aexp} {r: Reg} {s: State} {rs: RState},
   0 < r -> r0exec s (r0comp a r) rs 0 = aval a s := by
  intros a r s rs pos
  induction a generalizing r s rs
  case Num n => simp_all [r0exec, r0comp, r0exec1, aval, rupd]
  case Var x => simp_all [r0exec, r0comp, r0exec1, aval, rupd]
  case Add a1 a2 ih1 ih2 =>
    simp_all [r0comp, aval, r0exec_append, r0exec, r0exec1]
    let v2   := aval a2 s
    let rs2  := r0exec s (r0comp a2 r) rs
    let rs2' := rupd rs2 r v2
    let is1  := r0comp a1 (r + 1)
    calc
      rupd (r0exec s is1 rs2') 0 (aval a1 s + r0exec s is1 rs2' r) 0
        = aval a1 s + r0exec s (r0comp a1 (r + 1)) rs2' r := by simp [rupd, is1]
      _ = aval a1 s + rs2' r                              := by simp [r0comp_sep pos]
      _ = aval a1 s + rupd rs2 r v2 r                     := by simp [r0comp_sep pos]
      _ = aval a1 s + v2                                  := by simp [rupd]
      _ = aval a1 s + aval a2 s                           := by simp [v2]

end section_3_3
