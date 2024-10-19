
/- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html -/
set_option pp.fieldNotation false

example : 1 + 1 = 2 := rfl

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

-- def lookup {v} (key: Vname) (kvs : List (Vname × v)) : Result v :=
--   match kvs with
--   | [] => Stuck
--   | (k', v) :: kvs => if key == k' then Ok v else lookup key kvs

-- example : lookup "dog" [("cat", 1), ("dog", 2), ("rat", 3)] = Ok 2 := rfl
-- example : lookup "dog" [("cat", 1), ("hog", 2), ("rat", 3)] = Stuck := rfl

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

-- def eval (k : Nat) (ρ : State) (e : Exp) : Result Val :=
--   match (k, e) with
--   | (0,   _          ) => Timeout
--   | (_,   ENum n     ) => Ok (VInt n)
--   | (_,   EBool b    ) => Ok (VBool b)
--   | (_,   EVar x     ) => Ok (ρ x)
--   | (_,   ELam x τ e ) => Ok (VClos x τ e ρ)
--   | (k+1, EOp o e1 e2) => combine (eval k ρ e1) (eval k ρ e2) (eval_op o)
--   | (k+1, EApp  e1 e2) => combine  (eval k ρ e1) (eval k ρ e2) (fun v1 v2 =>
--                             match v1 with
--                             | VClos x _ e ρ' => eval k (ρ' [ x := v2 ]) e
--                             | _ => Stuck
--                           )

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
theorem op_safe : some τ = ty_op o τ1 τ2  -> WV v1 τ1 -> WV v2 τ2 -> ∃ v, eval_op o v1 v2 = Ok v ∧ WV v τ
  := by
  intros tyop v1t1 v2t2
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


-- lemma 2
theorem lookup_safe : WS Γ ρ -> WV (ρ x) (Γ x)  := by
  intro h_ws
  apply h_ws x


theorem eval_safe:
  WT Γ e τ -> WS Γ ρ -> WR (eval k ρ e) τ := by
  intros wt ws
  induction k, ρ, e using eval.induct <;> simp_all [eval]
  -- case k = 0
  constructor
  -- case num n
  cases wt; repeat constructor
  -- case bool b
  cases wt; repeat constructor
  -- case var x
  rename_i ρ _ x ; cases wt ; apply ws x
  -- case op o e1 e2
  sorry
  -- case lam
  cases wt; rename_i ρ _ x τx e τ' te; repeat constructor; apply ws; assumption
  -- case app
  sorry
