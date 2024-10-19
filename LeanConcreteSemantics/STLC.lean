
/- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html -/
set_option pp.fieldNotation false

inductive Ty where
  | TInt  : Ty
  | TBool : Ty
  | TFun  : Ty -> Ty -> Ty
  deriving Repr
open Ty

abbrev Vname := String

inductive Op where
  | Add   : Op
  | Equal : Op
  deriving Repr

open Op

inductive Exp where
  | ENum   : Int -> Exp
  | EBool  : Bool -> Exp
  | EVar   : Vname -> Exp
  | EOp    : Op -> Exp -> Exp -> Exp
  | ELam   : Vname -> Ty -> Exp -> Exp
  | EApp   : Exp -> Exp -> Exp
  deriving Repr

open Exp

inductive Result (α : Type) : Type where
  | Ok      : α -> Result α
  | Stuck   : Result α
  | Timeout : Result α
  deriving Repr

open Result

inductive Val where
  | VInt  : Int -> Val
  | VBool : Bool -> Val
  | VClos : Vname -> Ty -> Exp -> (Vname -> Val) -> Val

open Val

abbrev State := Vname -> Val
abbrev TEnv  := Vname -> Ty

@[simp]
def upd (s: Vname -> α ) (x: Vname) (v: α ) : Vname -> α :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

-- --------------------------------------------------------------------------------------------

def combine (r1 : Result Val) (r2 : Result Val) (k : Val -> Val -> Result Val) : Result Val :=
  match r1 with
  | Ok v1 =>
    match r2 with
    | Ok v2 => k v1 v2
    | _ => r2
  | _ => r1

def op_add (v1 : Val) (v2 : Val) : Result Val :=
  match v1, v2 with
  | VInt n1, VInt n2 => Ok (VInt (n1 + n2))
  | _, _ => Stuck

def op_equal (v1 : Val) (v2 : Val) : Result Val :=
  match v1, v2 with
  | VInt n1, VInt n2 => Ok (VBool (n1 == n2))
  | VBool b1, VBool b2 => Ok (VBool (b1 == b2))
  | _, _ => Stuck

def eval_op (o : Op) : Val -> Val -> Result Val :=
  match o with
  | Op.Add => op_add
  | Op.Equal => op_equal

def eval (k : Nat) (ρ : State) (e : Exp) : Result Val :=
  match k with
  | 0 => Timeout
  | k + 1 =>
    match e with
      | ENum n       => Ok (VInt n)
      | EBool b      => Ok (VBool b)
      | EVar x       => Ok (ρ x)
      | EOp o e1 e2  => combine (eval k ρ e1) (eval k ρ e2) (eval_op o)
      | ELam x τ e   => Ok (VClos x τ e ρ)
      | EApp e1 e2   => combine  (eval k ρ e1) (eval k ρ e2) (fun v1 v2 =>
                          match v1 with
                          | VClos x _ e ρ' => eval k (ρ' [ x := v2 ]) e
                          | _ => Stuck
                        )

-- --------------------------------------------------------------------------------------------

def one_plus_two := EOp Add (ENum 1) (ENum 2)
def inc := ELam "x" TInt (EOp Add (EVar "x") (ENum 1))
def st0 : State := λ _ => VInt 0
example : eval 100 st0 (EApp inc one_plus_two) = Ok (VInt 4) := rfl

-- --------------------------------------------------------------------------------------------

def ty_op (o: Op) (τ1 τ2: Ty) : Option Ty :=
  match (o, τ1, τ2) with
  | (Op.Add, TInt, TInt)     => some TInt
  | (Op.Equal, TInt, TInt)   => some TBool
  | (Op.Equal, TBool, TBool) => some TBool
  | _                        => none

inductive WT : TEnv -> Exp -> Ty -> Prop where
  | TNum   : WT Γ (ENum n) TInt
  | TBool  : WT Γ (EBool b) TBool
  | TVar   : WT Γ (EVar x) (Γ x)
  | TOp    : WT Γ e1 τ1 -> WT Γ e2 τ2 -> ty_op o τ1 τ2 = some τ -> WT Γ (EOp o e1 e2) τ
  | TLam   : WT (Γ[ x := τ ]) e τ' -> WT Γ (ELam x τ e) (TFun τ τ')
  | TApp   : WT Γ e1 (TFun τ τ') -> WT Γ e2 τ -> WT Γ (EApp e1 e2) τ'

inductive WV : Val -> Ty -> Prop where
  | TVInt  : WV (VInt _) TInt
  | TVBool : WV (VBool _) TBool
  | TVClos : (∀ x, WV (ρ x) (Γ x)) -> WT (Γ [ x := τ ]) e τ' -> WV (VClos x τ e ρ) (TFun τ τ')

inductive WR : Result Val -> Ty -> Prop where
  | TOk      : WV v τ -> WR (Ok v) τ
  | TTimeout : WR Timeout τ

abbrev WS (Γ : TEnv) (ρ : State) := ∀ x, WV (ρ x) (Γ x)

-- ------------------------------------------------------------------------------------------
@[simp]
theorem int_val : WV v TInt <-> ∃ i, v = VInt i := by
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

@[simp]
theorem bool_val : WV v TBool <-> ∃ b, v = VBool b := by
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

-- lemma 1
theorem op_safe :  WV v1 τ1 -> WV v2 τ2 -> some τ = ty_op o τ1 τ2 -> ∃ v, eval_op o v1 v2 = Ok v ∧ WV v τ
  := by
  intros v1t1 v2t2 tyop
  cases o
  . case Add   =>
    cases τ1 <;> cases τ2 <;> repeat trivial
    . case TInt.TInt =>
        simp_all [op_add, ty_op];
        cases v1t1; cases v2t2; simp_all [];
        rename_i i1 _ i2 _
        apply Exists.intro (VInt (i1 + i2))
        simp_all [eval_op, op_add]
  . case Equal =>
    cases τ1 <;> cases τ2 <;> repeat trivial
    repeat
        (simp_all [op_equal, ty_op];
         cases v1t1; cases v2t2; simp_all [];
         rename_i i1 _ i2 _
         apply Exists.intro (VBool (i1 == i2))
         simp_all [eval_op, op_equal])

theorem op_safe_r : WR r1 τ1 -> WR r2 τ2 -> some τ = ty_op o τ1 τ2 -> WR (combine r1 r2 (eval_op o)) τ
  := by
  intros wr1 wr2 t_op
  cases wr1 <;> cases wr2 <;> simp_all [combine]
  . case TOk.TOk =>
    rename_i v1 vt1 v2 vt2
    cases (op_safe vt1 vt2 t_op)
    rename_i w hw
    cases hw
    simp_all []
    constructor
    assumption
  repeat constructor

-- lemma 2
theorem lookup_safe : WS Γ ρ -> WV (ρ x) (Γ x)  := by
  intro h_ws
  apply h_ws x

theorem ws_upd : WS Γ ρ -> WV v τ -> WS (Γ [ x := τ ]) (ρ [ x := v ]) := by
  intros ws wv
  intro y
  by_cases (y = x) <;> simp_all [upd]

theorem wr_val : ¬ (r = Timeout) -> WR r τ ->  ∃ v, r = Ok v /\ WV v τ := by
  intro not_timeout wr
  cases wr
  . case TOk => apply Exists.intro; trivial
  . case TTimeout => trivial

theorem eval_safe:
  WT Γ e τ -> WS Γ ρ -> WR (eval k ρ e) τ := by
  intros wt ws
  induction k, ρ, e using eval.induct generalizing τ Γ  <;> simp_all [eval]
  -- case k = 0
  . case case1 =>
    constructor
  -- case num n
  . case case2 =>
    cases wt; repeat constructor
  -- case bool b
  . case case3 =>
    cases wt; repeat constructor
  -- case var x
  . case case4 =>
    constructor; rename_i ρ _ x ; cases wt ; apply ws x
  -- case op o e1 e2
  . case case5 =>
    cases wt; rename_i ρ k o e1 e2 ih1 ih2 t1 t2 et1 et2 op_ty
    apply op_safe_r
    apply ih1; repeat trivial
    apply ih2; repeat trivial
    simp_all []
  -- case lam
  . case case6 =>
    cases wt; rename_i ρ _ x τx e τ' te; repeat constructor
    apply ws
    trivial
  -- case app
  . case case7 =>
    cases wt
    rename_i ρ k e1 e2 ih1 ih2 ih3 τ2 et2 et1
    generalize h1 : (eval k ρ e1) = r1 at ih1   --- this is ANF / Nico's tip
    generalize h2 : (eval k ρ e2) = r2 at ih2   --- this is ANF / Nico's tip
    have hv1 : ¬ (r1 = Timeout) -> ∃ v1, r1 = Ok v1 ∧ WV v1 (TFun τ2 τ)
      := by intros r1_not_timeout; apply wr_val; trivial; apply ih1; repeat trivial
    have hv2 : ¬ (r2 = Timeout) -> ∃ v2, r2 = Ok v2 ∧ WV v2 τ2
      := by intros r1_not_timeout; apply wr_val; trivial; apply ih2; repeat trivial
    cases r1
    . case TApp.Ok =>
      cases r2
      . case Ok =>
        simp_all [combine]
        rename_i v1 v2
        cases hv1
        rename_i ρ' Γ' x body ws' tbody
        simp_all []
        apply ih3
        apply tbody
        apply ws_upd
        repeat trivial
      . case Stuck =>
        simp_all []
      . case Timeout =>
        simp_all [combine]; constructor
    . case TApp.Stuck =>
      simp_all []
    . case TApp.Timeout =>
      simp_all [combine]; constructor
