-- import LeanConcreteSemantics.Ch03ImpExpr
-- import LeanConcreteSemantics.Ch02Proving
import Aesop
import LeanConcreteSemantics.Ch02Proving
import LeanConcreteSemantics.Ch03ImpExpr

set_option pp.fieldNotation false
set_option pp.proofs true

@[aesop safe [constructors]]
inductive Val where
  | Iv : Int -> Val
  | Fv : Float -> Val

open Val

abbrev Vname := String

abbrev State := Vname -> Val

@[aesop safe [constructors]]
inductive Aexp where
  | Ic : Int -> Aexp
  | Fc : Float -> Aexp
  | V  : Vname -> Aexp
  | Plus : Aexp -> Aexp -> Aexp
  deriving Repr


open Aexp

@[aesop safe [constructors]]
inductive Taval : Aexp -> State -> Val -> Prop where
  | T_Ic {i s} : Taval (Ic i) s (Iv i)
  | T_Rc {f s} : Taval (Fc f) s (Fv f)
  | T_V  {x s} : Taval (V x) s (s x)
  | T_PlusI {a1 a2 s i1 i2} : Taval a1 s (Iv i1) -> Taval a2 s (Iv i2) -> Taval (Plus a1 a2) s (Iv (i1 + i2))
  | T_PlusR {a1 a2 s r1 r2} : Taval a1 s (Fv r1) -> Taval a2 s (Fv r2) -> Taval (Plus a1 a2) s (Fv (r1 + r2))

open Taval

def st0 : State := fun x => match x with
  | "x" => Iv 3
  | "y" => Iv 4
  | _   => Iv 0


inductive Bexp where
  | Bc : Bool -> Bexp
  | Not : Bexp -> Bexp
  | And : Bexp -> Bexp -> Bexp
  | Less : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp

inductive Tbval : Bexp -> State -> Bool -> Prop where
  | T_Bc  {v s}   : Tbval (Bc v) s v
  | T_Not {b v s} : Tbval b s v -> Tbval (Not b) s (!v)
  | T_And {b1 b2 v1 v2 s} : Tbval b1 s v1 -> Tbval b2 s v2 -> Tbval (And b1 b2) s (v1 && v2)
  | T_LessI {a1 a2 i1 i2 s} : Taval a1 s (Iv i1) -> Taval a2 s (Iv i2) -> Tbval (Less a1 a2) s (i1 < i2)
  | T_LessF {a1 a2 r1 r2 s} : Taval a1 s (Fv r1) -> Taval a2 s (Fv r2) -> Tbval (Less a1 a2) s (r1 < r2)

open Tbval



inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

infix:10 "<<"  => fun x y => Less x y
infix:10 "<~"  => Com.Assign
infixr:8 ";;" => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

@[simp]
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v


inductive Step : (Com × State) -> (Com × State) -> Prop where
   | Assign : ∀ {x a s v},
                Taval a s v ->
                Step (x <~ a, s) (Skip, s [x := v])
   | Seq1   : ∀ {c s},
                Step ((Skip ;; c), s) (c, s)
   | Seq2   : ∀ {c1 c1' c2 s s'},
                Step (c1, s) (c1', s') ->
                Step ((c1 ;; c2) , s) ((c1' ;; c2), s')
   | IfTrue : ∀ {b c1 c2 s},
                Tbval b s true ->
                Step (IF b THEN c1 ELSE c2, s) (c1, s)
   | IfFalse : ∀ {b c1 c2 s},
                Tbval b s false ->
                Step (IF b THEN c1 ELSE c2, s) (c2, s)
   | While   : ∀ { b c s },
                Step (Com.While b c, s) (Com.If b (c ;; (Com.While b c)) Skip, s)


inductive Ty where
  | Ity : Ty
  | Fty : Ty
  deriving Repr

open Ty

abbrev Env := Vname -> Ty

inductive HasTyA : Env -> Aexp -> Ty -> Prop where
  | Ty_Ic {Γ i} : HasTyA Γ (Ic i) Ity
  | Ty_Fc {Γ r} : HasTyA Γ (Fc r) Fty
  | Ty_V  {Γ x} : HasTyA Γ (V x) (Γ x)
  | Ty_PlusI {Γ a1 a2} : HasTyA Γ a1 Ity -> HasTyA Γ a2 Ity -> HasTyA Γ (Plus a1 a2) Ity
  | Ty_PlusR {Γ a1 a2} : HasTyA Γ a1 Fty -> HasTyA Γ a2 Fty -> HasTyA Γ (Plus a1 a2) Fty

inductive HasTyB : Env -> Bexp -> Prop where
  | Ty_Bc   {Γ v}       : HasTyB Γ (Bc v)
  | Ty_Not  {Γ b}       : HasTyB Γ b    -> HasTyB Γ (Not b)
  | Ty_And  {Γ b1 b2}   : HasTyB Γ b1   -> HasTyB Γ b2  -> HasTyB Γ (And b1 b2)
  | Ty_Less {Γ a1 a2 t} : HasTyA  Γ a1 t -> HasTyA Γ a2 t -> HasTyB Γ (Less a1 a2)

inductive HasTyC : Env -> Com -> Prop where
  | Ty_Skip   {Γ}         : HasTyC Γ Skip
  | Ty_Assign {Γ x a}     : HasTyA Γ a (Γ x) -> HasTyC Γ (x <~ a)
  | Ty_Seq    {Γ c1 c2}   : HasTyC  Γ c1 -> HasTyC Γ c2 -> HasTyC Γ (c1 ;; c2)
  | Ty_If     {Γ b c1 c2} : HasTyB Γ b -> HasTyC Γ c1 -> HasTyC Γ c2 -> HasTyC Γ (IF b THEN c1 ELSE c2)
  | Ty_While  {Γ b c}     : HasTyB Γ b -> HasTyC Γ c  -> HasTyC Γ (WHILE b DO c END)

@[simp]
def com_x_y : Com := "x" <~ Ic 3 ;; "y" <~ Plus (V "x") (Ic 4)

-- ⟨ x ← 3 ;; y ← x + 4, st0 ⟩ ==> st0 [x := 3][y := 7]
@[simp]
def env_int : Env := fun _ => Ity

-- Yay for syntax directed!
example : HasTyC env_int com_x_y := by
  repeat constructor

@[simp]
def type(v: Val) : Ty := match v with
  | Iv _ => Ity
  | Fv _ => Fty

@[simp]
def Wf (Γ: Env) (s: State) : Prop :=
  ∀ x, Γ x = type (s x)


theorem arith_preservation : ∀ { Γ a τ s v },
  HasTyA Γ a τ -> Wf Γ s -> Taval a s v -> type v = τ := by
  intros Γ a τ s v G_a_t G_s a_s_v
  induction G_a_t generalizing v
  . case Ty_Ic i =>
    cases a_s_v
    simp_all
  . case Ty_Fc f =>
    cases a_s_v
    simp_all
  . case Ty_V x =>
    cases a_s_v
    simp_all
  . case Ty_PlusI a1 a2 _ _ ih1 _ =>
    cases a_s_v
    simp_all
    rename_i _ _ av1 _; apply (ih1 av1)
  . case Ty_PlusR a1 a2 _ _ ih1 _ =>
    cases a_s_v
    rename_i _ _ av1 _; apply (ih1 av1)
    simp_all







theorem arith_progress: ∀ { Γ a τ s },
  HasTyA Γ a τ -> Wf Γ s -> ∃ v, Taval a s v  := by
  intros Γ a τ s G_a_t G_s
  induction G_a_t
  . case Ty_Ic i =>
    apply Exists.intro (Iv i)
    constructor
  . case Ty_Fc f =>
    apply Exists.intro (Fv f)
    constructor
  . case Ty_V x =>
    apply Exists.intro (s x)
    constructor
  . case Ty_PlusI a1 a2 _ _ ih1  ih2 =>
    cases ih1
    cases ih2
    rename_i a1ty a2ty v1 a1v1 v2 a2v2
    cases v1
    -- i1
    cases v2
    -- i1, i2
    rename_i i1 i2
    apply Exists.intro (Iv (i1 + i2))
    constructor
    assumption
    assumption
    -- i1, f2
    rename_i _ f2
    have contra : type (Fv f2) = Ity := by apply (arith_preservation a2ty G_s a2v2)
    simp_all
    -- f1, _
    rename_i f1
    have contra : type (Fv f1) = Ity := by apply (arith_preservation a1ty G_s a1v1)
    simp_all
  . case Ty_PlusR a1 a2 _ _ ih1 ih2 =>
    cases ih1
    cases ih2
    rename_i a1ty a2ty v1 a1v1 v2 a2v2
    cases v1
    -- i1
    rename_i i1
    have contra : type (Iv i1) = Fty := by apply (arith_preservation a1ty G_s a1v1)
    simp_all
    -- f1
    cases v2
    -- i2
    rename_i i2
    have contra : type (Iv i2) = Fty := by apply (arith_preservation a2ty G_s a2v2)
    simp_all
    -- f1, f2
    rename_i f1 f2
    apply Exists.intro (Fv (f1 + f2))
    constructor; assumption; assumption

theorem arith_preservation_I : ∀ { Γ a s }, HasTyA Γ a Ity -> Wf Γ s -> ∃ i, Taval a s (Iv i) := by
  intros Γ a s G_a_t G_s
  cases (arith_progress G_a_t G_s)    -- FUNKY MOVE!
  rename_i v a_v
  cases v
  -- i
  rename_i i
  apply Exists.intro i; assumption
  -- f
  rename_i f
  have contra : type (Fv f) = Ity := by apply (arith_preservation G_a_t G_s a_v)
  simp_all

theorem arith_preservation_F : ∀ { Γ a s }, HasTyA Γ a Fty -> Wf Γ s -> ∃ f, Taval a s (Fv f) := by
  intros Γ a s G_a_t G_s
  cases (arith_progress G_a_t G_s)    -- FUNKY MOVE!
  rename_i v a_v
  cases v
  -- i
  rename_i i
  have contra : type (Iv i) = Fty := by apply (arith_preservation G_a_t G_s a_v)
  simp_all
  -- f
  rename_i f
  apply Exists.intro; assumption

theorem bool_progress: ∀ { Γ b s },
  HasTyB Γ b -> Wf Γ s -> ∃ v, (Tbval b s v)  := by
  intros Γ b s Gb Gs
  induction Gb
  . case Ty_Bc v =>
    apply Exists.intro v
    constructor
  . case Ty_Not b' Gb' ih' =>
    cases ih'
    rename_i v ihv
    apply Exists.intro (!v); constructor; assumption
  . case Ty_And b1 b2 Gb1 Gb2 ih1 ih2 =>
    cases ih1
    cases ih2
    rename_i v1 ihv1 v2 ihv2
    apply Exists.intro (v1 && v2)
    constructor; assumption; assumption
  . case Ty_Less a1 a2 t Ga1 Ga2 =>
    cases t
    . case Ity =>
      cases (arith_preservation_I Ga1 Gs) <;> cases (arith_preservation_I Ga2 Gs)
      rename_i i1 a1i1 i2 a2i2
      apply Exists.intro
      apply T_LessI ; assumption ; assumption
    . case Fty =>
      cases (arith_preservation_F Ga1 Gs) <;> cases (arith_preservation_F Ga2 Gs)
      rename_i i1 a1i1 i2 a2i2
      apply Exists.intro
      apply T_LessF ; assumption ; assumption


theorem update_ty : ∀ { Γ s x v },  Wf Γ s -> type v = Γ x -> Wf Γ (s [x := v]) := by
  intros Γ s x v v_ty_x wf_s y
  by_cases (y = x) <;> simp_all         --


theorem state_preservation : ∀ { Γ c c' s s' },
  HasTyC Γ c -> Wf Γ s -> Step (c, s) (c', s') -> Wf Γ s'
  := by
  intros Γ c c' s s' ty_c wf_s step_c_c'
  induction ty_c generalizing c' s <;> cases step_c_c' <;> repeat trivial
  . case Ty_Assign.Assign => apply update_ty; trivial; apply arith_preservation; repeat trivial
  . case Ty_Seq.Seq2      => rename_i ih1 _ _ _; apply ih1; repeat trivial

theorem com_preservation : ∀ { Γ c c' s s' },
  HasTyC Γ c -> Wf Γ s -> Step (c, s) (c', s') -> HasTyC Γ c'
  := by
  intros Γ c c' s s' ty_c wf_s step
  induction ty_c generalizing c' s s' <;> cases step <;> repeat trivial
  . case Ty_Assign.Assign => constructor
  . case Ty_Seq.Seq2      => rename_i ih _ _ _; constructor; apply ih; repeat trivial
  . case Ty_While         => repeat (constructor <;> repeat trivial)

theorem assign_progress: ∀ { Γ x a s }, HasTyA Γ a (Γ x) -> Wf Γ s -> ∃ c' s', Step (x <~ a, s) (c', s') := by
  intros Γ x a s a_ty wf_s
  cases (arith_progress a_ty wf_s)
  rename_i v a_v
  apply Exists.intro
  apply Exists.intro
  constructor
  assumption

theorem com_progress : ∀ { Γ s c },
   HasTyC Γ c -> Wf Γ s -> ¬ (c = Skip) -> ∃ c' s', Step (c, s) (c', s')
  := by
  intros Γ s c ty_c wf_s not_skip
  induction ty_c <;> repeat trivial
  . case Ty_Assign x a a_ty =>
    cases (arith_progress a_ty wf_s)
    apply Exists.intro
    apply Exists.intro
    constructor
    assumption
  . case Ty_Seq    =>
    rename_i c1 c2 c1_ty c2_ty ih1 ih2
    by_cases (c1 = Skip)
    . case pos =>
      apply Exists.intro
      apply Exists.intro
      simp_all
      apply Step.Seq1
    . case neg c1_notskip =>
      cases (ih1 c1_notskip)
      rename_i c1' step1'
      cases step1'
      apply Exists.intro; apply Exists.intro;
      apply Step.Seq2
      repeat trivial
  . case Ty_If     =>
    rename_i b c1 c2 b_ty _ _ _ _
    cases (bool_progress b_ty wf_s)
    rename_i bv hbv
    cases bv
    . case intro.false =>
      apply Exists.intro; apply Exists.intro;
      apply Step.IfFalse; assumption
    . case intro.true =>
      apply Exists.intro; apply Exists.intro;
      apply Step.IfTrue; assumption
  . case Ty_While =>
    apply Exists.intro; apply Exists.intro;
    apply Step.While

open section_4_5 (star)

abbrev Steps := star Step

theorem soundness : ∀ { Γ c c' s s' },
  HasTyC Γ c -> Wf Γ s -> Steps (c, s) (c', s') -> ¬ (c' = Skip) -> ∃ c'' s'', Step (c', s') (c'', s'')
  := by
  intros Γ c c' s s' ty_c wf_s steps not_skip
  generalize h : (c, s)   = cs at steps --- this is ANF / Nico's tip
  generalize h : (c', s') = cs' at steps --- this is ANF / Nico's tip
  induction steps generalizing Γ c s c' s'
  . case refl =>
    rename_i h1
    cases h1
    cases h
    apply (com_progress ty_c wf_s not_skip)
  . case step =>
    rename_i cs1 cs2 cs3 step1 step_rest ih hh
    cases cs2
    rename_i c2 s2
    cases h
    cases hh
    have ty_c2 : HasTyC Γ c2 := by apply (com_preservation ty_c wf_s step1)
    have wf_s2 : Wf Γ s2     := by apply (state_preservation ty_c wf_s step1)
    apply (ih ty_c2 wf_s2 not_skip)
    repeat trivial
