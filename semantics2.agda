open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<?_; _≤?_; _<ᵇ_; _≡ᵇ_) renaming (_≟_ to _=?_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; recompute)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import lang

State : Set 
State = Id → ℕ


σ₀ : State
σ₀ = λ _ → 0

data Value : IExp → Set where
  V-n : ∀ {n} → Value (N n)
getVal : ∀ (n : IExp) → Value n → ℕ
getVal (N n) V-n = n 

data IsVar : IExp → Set where
  Var-v : ∀ {v}
    → IsVar (Var v)
getId : ∀ (x : IExp) → IsVar x → Id
getId (Var x) Var-v = x

-- lookup with all var-value zero-default
lookup : ∀ (σ : State) → (x : Id) → ℕ
lookup s x = s x

-- eval with all var-value zero-default
evalI : State → IExp → ℕ 
evalI s (N x) = x
evalI s (Var x)  = lookup s x
evalI s (x₁ `+ x₂) = evalI s x₁ + evalI s x₂
evalI s (x₁ `- x₂) = evalI s x₁ ∸ evalI s x₂

evalB : State → BExp → Bool
evalB s (BV x) = x
evalB s (x₁ `< x₂) = evalI s x₁ <ᵇ evalI s x₂
evalB s (x₁ `≤ x₂) = let l = evalI s x₁; r = evalI s x₂ in (l <ᵇ r) ∨ (l ≡ᵇ r)
evalB s (x₁ `= x₂) = evalI s x₁ ≡ᵇ evalI s x₂
evalB s (x₁ `> x₂) = let l = evalI s x₁; r = evalI s x₂ in not ((l <ᵇ r) ∨ (l ≡ᵇ r))
evalB s (`¬ x) = not (evalB s x)
evalB s (x₁ `∧ x₂) = evalB s x₁ ∧ evalB s x₂
evalB s (x₁ `∨ x₂) = evalB s x₁ ∨ evalB s x₂

modify : State → Id → ℕ → State
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

_ : evalI (modify σ₀ "x" 1) (N 1 `+ Var "x") ≡ 2
_ = refl

{- small step -}
data _-→_ : Stmt × State → Stmt × State → Set where
  :=-exec : ∀ {x n σ}
    --------------------------------------------------------
    → ⟨ C (x := n) , σ ⟩ -→ ⟨ C skip , modify σ x (evalI σ n) ⟩ 

  ;-left : ∀ {c₀ c₀′ σ σ′ c₁}
    → ⟨ C c₀ , σ ⟩ -→ ⟨ C c₀′ , σ′ ⟩ 
    -------------------------------------
    → ⟨ C (c₀ ; c₁) , σ ⟩ -→ ⟨ C (c₀′ ; c₁) , σ′ ⟩ 

  ;-exec : ∀ {c₁ σ}
    ---------------------------------
    → ⟨ C (skip ; c₁) , σ ⟩ -→ ⟨ C c₁ , σ ⟩ 

  `if-true : ∀ {b c₀ c₁ σ}
    → T (evalB σ b)
    ------------------------------------------------------
    → ⟨ C (`if b `then c₀ `else c₁) , σ ⟩ -→ ⟨ C c₀ , σ ⟩ 

  `if-false : ∀ {b c₀ c₁ σ}
    → T (not (evalB σ b))
    -------------------------------------------------------
    → ⟨ C (`if b `then c₀ `else c₁) , σ ⟩ -→ ⟨ C c₁ , σ ⟩ 

  `while-true : ∀ {b c σ}
    → T (evalB σ b)
    --------------------------------------------------------------
    → ⟨ C (`while b `do c) , σ ⟩ -→ ⟨ C (c ; `while b `do c) , σ ⟩ 

  `while-false : ∀ {b c σ}
    → T (not (evalB σ b))
    ----------------------------------------------
    → ⟨ C (`while b `do c) , σ ⟩ -→ ⟨ C skip , σ ⟩ 

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
  
form-→* : ∀ {M N n} 
  → M >- n -→ N 
  → M -→* N
form-→* -→Z = ⟨ 0 , -→Z ⟩
form-→* s@(_-→S_ {n = n} _ _) = ⟨ suc n , s ⟩

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

{- big step -}
data _⇓_ : Stmt × State → State → Set where
  :=-exec : ∀ {x n σ}
  ----------------------------------------------
    → ⟨ C (x := n) , σ ⟩ ⇓ modify σ x (evalI σ n) 

  ;-exec : ∀ {c₀ c₁ σ σ' σ''}
    → ⟨ C c₀ , σ ⟩ ⇓ σ'
    → ⟨ C c₁ , σ' ⟩ ⇓ σ''
    ---------------------------------
    → ⟨ C (c₀ ; c₁) , σ ⟩ ⇓ σ''

  `if-true : ∀ {b c₀ c₁ σ σ'}
    → T (evalB σ b)
    → ⟨ C c₀ , σ ⟩ ⇓ σ'
    -------------------------------------------
    → ⟨ C (`if b `then c₀ `else c₁) , σ ⟩ ⇓ σ'

  `if-false : ∀ {b c₀ c₁ σ σ'}
    → T (not (evalB σ b))
    → ⟨ C c₁ , σ ⟩ ⇓ σ'
    -------------------------------------------
    → ⟨ C (`if b `then c₀ `else c₁) , σ ⟩ ⇓ σ'

  `while-true : ∀ {b c σ σ' σ''}
    → T (evalB σ b)
    → ⟨ C c , σ ⟩ ⇓ σ'
    → ⟨ C (`while b `do c) , σ' ⟩ ⇓ σ''
    --------------------------------------------------------------
    → ⟨ C (`while b `do c) , σ ⟩ ⇓ σ''

  `while-false : ∀ {b c σ}
    → T (not (evalB σ b))
    ----------------------------------
    → ⟨ C (`while b `do c) , σ ⟩ ⇓ σ 
