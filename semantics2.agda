open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; recompute)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Integer.Base using (ℤ; _+_; _-_; +_)
open import Data.Integer.Properties using (_<?_)

open import lang

State : Set 
State = Id → ℤ


σ₀ : State
σ₀ = λ _ → + 0

data Value : IExp → Set where
  V-n : ∀ {n} → Value (N n)
getVal : ∀ (n : IExp) → Value n → ℤ
getVal (N n) V-n = n 

data IsVar : IExp → Set where
  Var-v : ∀ {v}
    → IsVar (Var v)
getId : ∀ (x : IExp) → IsVar x → Id
getId (Var x) Var-v = x

-- lookup with all var-value zero-default
lookup : ∀ (σ : State) → (x : Id) → ℤ
lookup s x = s x

-- eval with all var-value zero-default
eval : (s : State) → (x : IExp) → ℤ 
eval s (N x) = x
eval s (Var x)  = lookup s x
eval s (x₁ `+ x₂) = eval s x₁ + eval s x₂
eval s (x₁ `- x₂) = eval s x₁ - eval s x₂

modify : State → Id → ℤ → State
modify s x n x' with x ≟ x' 
... | yes _ = n
... | no _ = s x'
-- modify s x n = modify' s x (x in? s) n
--   where
--     modify' : ∀ (σ : State) → (x : Id) → Dec (x ∈ σ) → ℤ → State
--     modify' (state []) x c n with c
--     ... | yes ()
--     ... | no _ = state (⟨ x , n ⟩ ∷ [])
--     modify' (state (_ ∷ xs)) x c n with c 
--     ... | yes (Z _) = state (⟨ x , n ⟩ ∷ xs)
--     ... | yes (S c') = modify' (state xs) x (yes c') n
--     ... | no _ = state (⟨ x , n ⟩ ∷ [])

_ : eval (modify σ₀ "x" (+ 1)) (N (+ 1) `+ Var "x") ≡ + 2
_ = refl

data _-→_ : Stmt × State → Stmt × State → Set where
  `<-eval : ∀ {n₁ n₂ σ}
    -------------------------------------------------------------
    → ⟨ B (n₁ `< n₂) , σ ⟩ -→ ⟨ B (BV ⌊ eval σ n₁ <? eval σ n₂ ⌋) , σ ⟩

  :=-exec : ∀ {x n σ}
    --------------------------------------------------------
    → ⟨ C (x := n) , σ ⟩ -→ ⟨ C skip , modify σ x (eval σ n) ⟩ 

  ;-left : ∀ {c₀ c₀′ σ σ′ c₁}
    → ⟨ C c₀ , σ ⟩ -→ ⟨ C c₀′ , σ′ ⟩ 
    -------------------------------------
    → ⟨ C (c₀ ; c₁) , σ ⟩ -→ ⟨ C (c₀′ ; c₁) , σ′ ⟩ 

  ;-exec : ∀ {c₁ σ}
    ---------------------------------
    → ⟨ C (skip ; c₁) , σ ⟩ -→ ⟨ C c₁ , σ ⟩ 

  `if-cond : ∀ {b b′ σ σ′ c₀ c₁}
    → ⟨ B b , σ ⟩ -→ ⟨ B b′ , σ′ ⟩ 
    ---------------------------------------------------------------
    → ⟨ C (`if b `then c₀ `else c₁) , σ ⟩ -→ ⟨ C (`if b′ `then c₀ `else c₁) , σ′ ⟩ 

  `if-true : ∀ {c₀ c₁ σ}
    ------------------------------------------------------
    → ⟨ C (`if (BV true) `then c₀ `else c₁) , σ ⟩ -→ ⟨ C c₀ , σ ⟩ 

  `if-false : ∀ {c₀ c₁ σ}
    -------------------------------------------------------
    → ⟨ C (`if (BV false) `then c₀ `else c₁) , σ ⟩ -→ ⟨ C c₁ , σ ⟩ 

  `while-exec : ∀ {b c σ}
    -------------------------------------------------------------------------------
    → ⟨ C (`while b `do c) , σ ⟩ -→ ⟨ C (`if b `then (c ; `while b `do c) `else skip) , σ ⟩ 

infix  2 _-→*_
infix  1 `begin_
infixr 2 _-→⟨_⟩_
infix  3 _`∎

infixr  2 _-→S_
data _>-_-→_ : Stmt × State → ℕ → Stmt × State → Set where
  -→Z : ∀ {M}
    → M >- 0 -→  M
  
  _-→S_ : ∀ {L M N n}
    → L -→ M 
    → M >- n -→ N 
    → L >- (suc n) -→ N


_-→*_ : Stmt × State → Stmt × State → Set 
M' -→* N' = ∃[ n ] (M' >- n -→ N')
  

-- data _-→*_ : Stmt × State → Stmt × State → Set where
--   form : ∀ {M N n}
--     → (x : M >- n -→ N)
--     → M -→* N 

_`∎ : ∀ M
  ---------
  → M -→* M
x `∎ = ⟨ 0 , -→Z ⟩

_-→⟨_⟩_ : ∀ L {M N}
  → L -→ M
  → M -→* N 
  ----------
  → L -→* N
x -→⟨ x-→y ⟩ ⟨ .0 , -→Z ⟩ = ⟨ 1 , x-→y -→S -→Z ⟩
x -→⟨ x-→y ⟩ ⟨ (suc n) , x₁ -→S x₂ ⟩ = ⟨ suc (suc n) , x-→y -→S x₁ -→S x₂ ⟩
-- x -→⟨ x-→y ⟩ -→Z = (x-→y -→S -→Z)
-- x -→⟨ x-→y ⟩ (x₁ -→S x₂) = (x-→y -→S x₁ -→S x₂)

`begin_ : ∀ {M N}
  → M -→* N
  ----------
  → M -→* N 
`begin M-→*N = M-→*N 

