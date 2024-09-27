
import LeanConcreteSemantics.Ch03ImpExpr

set_option pp.fieldNotation false

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

theorem boo : ∀ {b c c' s t},
  (⟨ WHILE b DO c END , s ⟩ ==> t) ->
  c ≃ c' ->
  (⟨ WHILE b DO c' END, s ⟩ ==> t) := by
  intros b c c' s t cst cc
  induction cst -- nasty error: index in target's type is not a variable (consider using the `cases` tactic instead)

  -- cases hb : bval b s
  -- . case false =>
  --   cases cst
  --   . case WhileFalse => apply BigStep.WhileFalse <;> assumption
  --   . case WhileTrue  => simp_all []
  -- . case true =>
  --   cases cst
  --   . case WhileFalse => simp_all []
  --   . case WhileTrue s1 _ c_s_s1 w_c_s1_t => sorry
