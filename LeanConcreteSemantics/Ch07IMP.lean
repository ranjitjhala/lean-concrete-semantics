import LeanConcreteSemantics.Ch03ImpExpr
import LeanConcreteSemantics.Ch02Proving

set_option pp.fieldNotation false
set_option pp.proofs true

open section_3_1
open section_3_1.Aexp

class ToAexp (a : Type) where
  toAexp : a -> Aexp

instance : ToAexp Nat where
  toAexp := Num

instance : ToAexp String where
  toAexp := Var

instance : OfNat Aexp (n: Nat) where
  ofNat := Num n

instance : Add Aexp where
  add := fun a1 a2 => Add a1 a2

instance : HAdd String Aexp Aexp where
  hAdd := fun s a => Add (Var s) a

instance : HAdd String Nat Aexp where
  hAdd := fun s a => Add (Var s) (Num a)

def mkVar (s: String) (i : Nat) : Aexp := Var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

def x := "x"
def y := "y"
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

def st100 : State := λ _ => 100

#eval (aval 12 st100)

#eval (aval aexp0 st100)


inductive Bexp where
  | Bc    : Bool -> Bexp
  | Bnot  : Bexp -> Bexp
  | Band  : Bexp -> Bexp -> Bexp
  | BLess : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp

def bval (b: Bexp) (st: State) : Bool :=
  match b with
  | Bexp.Bc v        => v
  | Bexp.Bnot b1     => ! bval b1 st
  | Bexp.Band b1 b2  => bval b1 st && bval b2 st
  | Bexp.BLess a1 a2 => aval a1 st < aval a2 st

inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

def bLess (a1 a2 : Aexp) : Bexp := BLess a1 a2

infix:10 "<<"  => fun x y => BLess (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;" => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

def com0 := x <~ y + 1
def com1 := y <~ 2
def com2 := com0 ;; com1
def com3 := x <~ y + 1 ;; y <~ x + 2
def com4 := Skip ;; Skip ;; Skip ;; Skip
def com5 := IF 10 << x THEN x <~ 1 ELSE y <~ 2
def com6 := WHILE x << 5 DO x <~ x + 1 END

def st_x_10_y_20 := st0 [x := 10 ] [ y := 20]

#eval com3
#eval com4

inductive BigStep : Com -> State -> State -> Prop where
  | Skip {st} :  BigStep Skip st st
  | Assign {st a n} : BigStep (Assign a n) st (st [a := aval n st])
  | Seq {c1 c2 st1 st2 st3} : BigStep c1 st1 st2 -> BigStep c2 st2 st3 -> BigStep (Seq c1 c2) st1 st3
  | IfTrue {b c1 c2 st st'} : bval b st = true -> BigStep c1 st st' -> BigStep (If b c1 c2) st st'
  | IfFalse {b c1 c2 st st'} : bval b st = false -> BigStep c2 st st' -> BigStep (If b c1 c2) st st'
  | WhileFalse {b c st} : bval b st = false -> BigStep (While b c) st st
  | WhileTrue {b c st st' st''} : bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' -> BigStep (While b c) st st''

notation:12 "⟨" c "," s "⟩ ==> " t  => BigStep c s t

example : ⟨ (x <~ 5 ;; y <~ x + 1) , st0 ⟩ ==> st0 [x := 5] [y := 6] := by
  apply BigStep.Seq
  apply BigStep.Assign
  apply BigStep.Assign

theorem seq_assoc : ∀ {c1 c2 c3 : Com} { st st' : State },
   ( ⟨ c1 ;; (c2 ;; c3), st ⟩ ==> st' ) <-> ( ⟨ (c1 ;; c2) ;; c3, st ⟩ ==> st' ) := by
   intros c1 c2 c3 st st'
   apply Iff.intro
   . case mp =>
     intro h1_h23
     cases h1_h23
     . case Seq h1 h23 =>
        cases h23
        . case Seq h2 h3 =>
          apply BigStep.Seq
          apply BigStep.Seq
          assumption
          assumption
          assumption
   . case mpr =>
     intro h12_h3
     cases h12_h3
     . case Seq h12 h3 =>
        cases h12
        . case Seq h1 h2 =>
          apply BigStep.Seq
          assumption
          apply BigStep.Seq
          assumption
          assumption

def equiv_com (c1 c2 : Com) := ∀ {st st' : State}, ( ⟨ c1, st ⟩ ==> st') ↔ ( ⟨ c2, st ⟩ ==> st' )

infix:50 "≃"  => equiv_com

theorem skip_skip : ∀ {c: Com}, (Skip ;; c) ≃ c := by
  intros c st st'
  apply Iff.intro
  case mp =>
    intro skip_c
    cases skip_c
    case Seq h1 h2 =>
      cases h1
      assumption
  case mpr =>
    intro c
    apply BigStep.Seq
    apply BigStep.Skip
    assumption

theorem unfold_while : ∀ {b c}, (WHILE b DO c END) ≃ ((IF b THEN c ELSE Skip) ;; (WHILE b DO c END)) := by
  intros b c st st'
  apply Iff.intro
  case mp =>
   intros hw
   cases hw
   . case WhileFalse bf =>
     apply BigStep.Seq
     apply BigStep.IfFalse
     assumption
     apply BigStep.Skip
     apply BigStep.WhileFalse
     assumption
   . case WhileTrue hb hc hw =>
      apply BigStep.Seq
      apply BigStep.IfTrue ; assumption
      assumption
      assumption
  case mpr =>
    intros hiw
    cases hiw
    . case Seq hi hw =>
      cases hi
      . case IfTrue hb hc =>
        apply BigStep.WhileTrue
        assumption
        assumption
        assumption
      . case IfFalse hb hc =>
        cases hc
        assumption

theorem seq_assoc_kyle : ∀ {c1 c2 c3 : Com}, (c1 ;; (c2 ;; c3)) ≃ ((c1 ;; c2) ;; c3) := by
   intros c1 c2 c3 st st'
   constructor <;> intro H
   . rcases H
     case mp.Seq h1 h23 =>
       cases h23
       apply BigStep.Seq
       . case Seq h1 h2 => apply BigStep.Seq <;> assumption
       . case Seq h12 h3 => assumption
   . rcases H
     case mpr.Seq h12 h3 =>
       cases h12
       apply BigStep.Seq
       . case Seq => assumption
       . case Seq => apply BigStep.Seq <;> assumption

theorem if_c_c : ∀ { b c }, (IF b THEN c ELSE c) ≃ c := by
   intros b c st st'
   apply Iff.intro
   case mp =>
     intro hif
     cases hif <;> assumption
   case mpr =>
     intro hc
     cases hb : bval b st
     .case false => apply BigStep.IfFalse <;> assumption
     .case true  => apply BigStep.IfTrue  <;> assumption

theorem lem_7_6 : ∀ {b c c' s t},
  (⟨ WHILE b DO c END , s ⟩ ==> t) ->
  c ≃ c' ->
  (⟨ WHILE b DO c' END, s ⟩ ==> t) := by
   intros b c c' s t cst c_eq_c'
   generalize h : (WHILE b DO c END) = x at cst   --- this is ANF / Nico's tip
   induction cst <;> simp_all []
   . case WhileFalse =>
      constructor
      assumption
   . case WhileTrue =>
      constructor <;> try assumption
      simp_all [equiv_com]    --- this is a bit of magic

theorem equiv_symm : ∀ {c c'}, c ≃ c' -> c' ≃ c := by
  simp_all [equiv_com]

theorem equiv_refl : ∀ {c}, c ≃ c := by
  simp_all [equiv_com]

theorem equiv_trans : ∀ {c1 c2 c3}, c1 ≃ c2 -> c2 ≃ c3 -> c1 ≃ c3 := by
  simp_all [equiv_com]

theorem lem_7_5 : ∀ {b c c'},
  c ≃ c' ->
  (WHILE b DO c END) ≃ (WHILE b DO c' END) := by
  intros b c c' c_eq_c'
  simp_all [equiv_com]
  intros st st'
  apply Iff.intro
  . case mp =>
      intros wc
      apply lem_7_6
      assumption
      assumption
  . case mpr =>
      intros wc
      apply lem_7_6
      assumption
      apply equiv_symm
      assumption

theorem bigstep_deterministic : ∀ {c s t1 t2}, (⟨ c, s ⟩ ==> t1) -> (⟨ c, s ⟩ ==> t2) -> t1 = t2 := by
  intros c s t1 t2 s_to_t1 s_to_t2
  induction s_to_t1 generalizing t2 <;> cases s_to_t2 <;> try simp_all []
  case Seq.Seq =>
    rename_i c1 c2 st1 st2 st3 _ _ ih1 ih2 _ bob _
    apply ih2
    have fact := ih1 bob
    simp_all []
  case WhileTrue.WhileTrue =>
    rename_i b c st st' st'' _ _ ih1 ih2 _ _ bob _
    apply ih2
    have fact := ih1 bob
    simp_all []
  case IfTrue.IfTrue =>
    rename_i b c1 c2 _ _ _ ih _ _
    apply ih
    simp_all []
  case IfFalse.IfFalse =>
    rename_i b c1 c2 _ _ _ ih _ _
    apply ih
    simp_all []

inductive Step : (Com × State) -> (Com × State) -> Prop where
   | Assign : ∀ {x a s},
                Step (x <~ a, s) (Skip, s [x := aval a s])
   | Seq1   : ∀ {c s},
                Step ((Skip ;; c), s) (c, s)
   | Seq2   : ∀ {c1 c1' c2 s s'},
                Step (c1, s) (c1', s') ->
                Step ((c1 ;; c2) , s) ((c1' ;; c2), s')
   | IfTrue : ∀ {b c1 c2 s},
                bval b s == true ->
                Step (IF b THEN c1 ELSE c2, s) (c1, s)
   | IfFalse : ∀ {b c1 c2 s},
                bval b s == false ->
                Step (IF b THEN c1 ELSE c2, s) (c2, s)
   | While   : ∀ { b c s },
                Step (Com.While b c, s) (Com.If b (c ;; (Com.While b c)) Skip, s)

open section_4_5 (star)

abbrev Steps := star Step

def com_xz_yx := x <~ Var z ;; y <~ Var x

def st := st0 ["x" := 3] [ "y" := 7 ] [ "z" := 5 ]

theorem smallstep_deterministic : ∀ {cs cs1 cs2}, (Step cs cs1) -> (Step cs cs2) -> cs1 = cs2 := by
  intros cs cs1 cs2 step1 step2
  induction step1 generalizing cs2 <;> cases step2 <;> simp_all []
  case Seq2.Seq1  _ _ _ _ b _ => cases b
  case Seq1.Seq2  _ _ _ _  b  => cases b
  case Seq2.Seq2 =>
    rename_i c11 c11' _ _ _ _ ih _ _ step_c11
    have fact := ih step_c11
    simp_all []

theorem steps_skip : ∀ {st cs}, Steps (Skip, st) cs -> cs = (Skip, st) := by
  intros st cs steps
  cases steps
  . case refl => simp_all []
  . case step _ ih _ => cases ih

theorem seq_steps : ∀ {c1 c1' c2 s s'},
  Steps (c1, s) (c1', s') ->
  Steps (c1;;c2, s) (c1';;c2, s')
  := by
  intros c1 c1' c2 s s' steps_c1_c1'
  generalize h1 : (c1, s)   = c1s  at steps_c1_c1'
  generalize h2 : (c1', s') = c1s' at steps_c1_c1'
  induction steps_c1_c1' generalizing c1 c1' c2 s s'
  case refl =>
    rename_i a
    cases h1
    simp_all []
    apply star.refl
  case step  =>
    cases h1
    cases h2
    rename_i c1s'' step_c1_hd _ ih
    apply star.step
    constructor
    apply step_c1_hd
    apply ih
    simp_all []
    simp_all []


theorem skip_steps : ∀ {c st1 st2},
  star Step (c, st1) (Skip, st2) ->
  star Step (Skip;;c , st1) (Skip, st2) := by
  intros
  apply star.step
  constructor
  assumption

---------------------------------------------------------------------------------
@[simp] theorem BigStep_skip_Iff : ∀ {s t}, (⟨ Skip, s ⟩ ==> t) <-> (s = t) := by
  intros s t
  apply Iff.intro
  . case mp =>
      intro h
      cases h
      simp_all []
  . case mpr =>
      intro s_eq_t
      simp_all []
      constructor

@[simp] theorem BigStep_assign_Iff: ∀ {x a s t}, (⟨ x <~ a, s ⟩ ==> t) <-> (t = (s[x := aval a s])) := by
  intros x a s t
  apply Iff.intro
  . case mp =>
      intro h
      cases h
      simp_all []
  . case mpr =>
      intro h
      simp_all []
      constructor

@[simp] theorem BigStep_seq_Iff: ∀ {c1 c2 s t}, (⟨ c1 ;; c2, s ⟩ ==> t) <-> (∃ s', (⟨ c1, s ⟩ ==> s') ∧ (⟨ c2, s' ⟩ ==> t)) := by
  intros c1 c2 s t
  apply Iff.intro
  . case mp =>
    intros h
    cases h
    apply Exists.intro
    apply And.intro
    assumption
    assumption
  . case mpr =>
    intros h
    cases h
    rename_i s' h12
    cases h12
    constructor
    assumption
    assumption

@[simp] theorem BigStep_if_Iff: ∀ {b c1 c2 s t}, (⟨ IF b THEN c1 ELSE c2 , s ⟩ ==> t) <-> ((bval b s = true ∧ (⟨ c1, s ⟩ ==> t)) ∨ (bval b s = false ∧ (⟨ c2, s ⟩ ==> t))) := by
  intros b c1 c2 s t
  apply Iff.intro
  . case mp =>
    intro h
    cases h
    . case IfTrue =>
      apply Or.inl
      apply And.intro
      assumption
      assumption
    . case IfFalse =>
      apply Or.inr
      apply And.intro
      assumption
      assumption
  . case mpr =>
    intro h
    cases h
    . case inl h =>
      cases h
      apply BigStep.IfTrue
      assumption
      assumption
    . case inr h =>
      cases h
      apply BigStep.IfFalse
      assumption
      assumption

#check BigStep.WhileTrue

theorem bigstep_implies_smallstep : ∀ {c s t}, (⟨ c, s ⟩ ==> t) -> Steps (c, s) (Skip, t) := by
  intros c s t bs
  induction bs
  . case Skip => constructor
  . case Assign s x a => apply star.step
                         constructor
                         apply star.refl
  . case Seq c1 c2 st1 st2 st3 _ _ sc1 sc2 =>
      apply section_4_5.star_trans
      apply seq_steps
      apply sc1
      apply star.step
      apply Step.Seq1
      apply sc2
  . case IfTrue =>
      apply star.step
      apply Step.IfTrue
      simp_all []
      assumption
  . case IfFalse =>
      apply star.step
      apply Step.IfFalse
      simp_all []
      assumption
  . case WhileFalse b c st b_false =>
      apply star.step
      constructor
      apply section_4_5.star_one
      constructor
      simp_all []
  . case WhileTrue =>
      rename_i b c st st1 st2 _ _ _ c_steps ih
      apply star.step
      constructor
      apply star.step
      constructor <;> simp_all []
      apply section_4_5.star_trans
      apply seq_steps c_steps
      apply skip_steps
      assumption

theorem step_case : ∀ {c c' s s' t},  Step (c, s) (c', s') -> (⟨ c', s' ⟩ ==> t) -> (⟨ c, s ⟩ ==> t) := by
  intros c c' s s' t step1 bigstep
  generalize h : (c, s) = cs at step1 --- this is ANF / Nico's tip
  generalize h : (c', s') = cs' at step1 --- this is ANF / Nico's tip
  induction step1 generalizing c c' s s' t
  . case Assign x a s hyp  =>
      cases h
      cases hyp
      simp_all []
  . case Seq1 c s hyp =>
      cases h
      cases hyp
      constructor
      constructor
      assumption
  . case Seq2 c1 c1' c2 s s' _hyp step_c1 ih =>
      cases ih
      cases h
      cases bigstep
      rename_i st2 c1'_s'_st2' c2_st2
      constructor
      apply step_c1
      apply c1'_s'_st2'
      simp_all []
      simp_all []
      assumption
  . case IfTrue b c1 c2 s hyp hh  =>
      cases h
      cases hh
      constructor
      simp_all []
      assumption
  . case IfFalse b c1 c2 s hyp hh =>
      cases h
      cases hh
      apply BigStep.IfFalse
      simp_all []
      assumption
  . case While b c s hh =>
      cases h
      cases hh
      generalize hyp : bval b s = bv
      cases bv
      -- bv = false
      cases bigstep
      simp_all []
      simp_all []
      apply BigStep.WhileFalse
      assumption
      -- bv = true
      cases bigstep
      simp_all []
      rename_i h_bv h_c_w
      cases h_c_w
      rename_i s' hh
      cases hh
      apply BigStep.WhileTrue
      assumption
      assumption
      assumption
      simp_all []




theorem smallstep_implies_bigstep : ∀ {c s t}, Steps (c, s) (Skip, t) -> (⟨ c, s ⟩ ==> t)  := by
  intros c s t steps
  generalize h : (c, s)    = x at steps --- this is ANF / Nico's tip
  generalize h : (Skip, t) = y at steps --- this is ANF / Nico's tip
  induction steps generalizing c s t
  . case refl h1 h2 =>
      cases h2
      cases h
      constructor
  . case step cs cs1 skip_t step_head step_tail ih h7 =>
      cases h7
      cases h
      apply step_case
      apply step_head
      apply ih
      simp_all []
      simp_all []
