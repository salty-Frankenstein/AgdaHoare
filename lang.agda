open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ)
open import Data.String using (String; _≟_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Integer.Base using (ℤ; _+_; _-_; +_)

Id : Set
Id = String

data IExp : Set where
  N : ℤ → IExp
  Var : Id → IExp
  _`+_ : IExp → IExp → IExp
  _`-_ : IExp → IExp → IExp

data BExp : Set where 
  BV : Bool → BExp
  _`<_ : IExp → IExp → BExp
  _`=_ : IExp → IExp → BExp
  _`>_ : IExp → IExp → BExp
  `¬_ : BExp → BExp
  _`∧_ : BExp → BExp → BExp
  _`∨_ : BExp → BExp → BExp

data Comm : Set where
  skip : Comm
  _:=_ : Id → IExp → Comm
  _;_ : Comm → Comm → Comm
  `if_`then_`else_ : BExp → Comm → Comm → Comm
  `while_`do_ : BExp → Comm → Comm

data Stmt : Set where
  E : IExp → Stmt
  B : BExp → Stmt
  C : Comm → Stmt
infixr 5 _;_
infix 15 _:=_

_X = Var "X"
_Y = Var "Y"
_Z = Var "Z"
X = "X"
Y = "Y"
Z = "Z"
pN : ℕ → IExp
pN n = N (+ n)