
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

notation:12 "⟨" c "," st "⟩ ==> " st'  => BigStep c st st'

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
