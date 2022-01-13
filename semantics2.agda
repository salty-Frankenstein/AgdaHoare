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
data _-→_ : Comm × State → Comm × State → Set where
  :=-exec : ∀ {x n σ}
    --------------------------------------------------------
    → ⟨ x := n , σ ⟩ -→ ⟨ skip , modify σ x (evalI σ n) ⟩ 

  ;-left : ∀ {c₀ c₀′ σ σ′ c₁}
    → ⟨ c₀ , σ ⟩ -→ ⟨ c₀′ , σ′ ⟩ 
    -------------------------------------
    → ⟨ c₀ ; c₁ , σ ⟩ -→ ⟨ c₀′ ; c₁ , σ′ ⟩ 

  ;-exec : ∀ {c₁ σ}
    ---------------------------------
    → ⟨ skip ; c₁ , σ ⟩ -→ ⟨ c₁ , σ ⟩ 

  `if-true : ∀ {b c₀ c₁ σ}
    → T (evalB σ b)
    ------------------------------------------------------
    → ⟨ `if b `then c₀ `else c₁ , σ ⟩ -→ ⟨ c₀ , σ ⟩ 

  `if-false : ∀ {b c₀ c₁ σ}
    → T (not (evalB σ b))
    -------------------------------------------------------
    → ⟨ `if b `then c₀ `else c₁ , σ ⟩ -→ ⟨ c₁ , σ ⟩ 

  `while-true : ∀ {b c σ}
    → T (evalB σ b)
    --------------------------------------------------------------
    → ⟨ `while b `do c , σ ⟩ -→ ⟨ c ; `while b `do c , σ ⟩ 

  `while-false : ∀ {b c σ}
    → T (not (evalB σ b))
    ----------------------------------------------
    → ⟨ `while b `do c , σ ⟩ -→ ⟨ skip , σ ⟩ 

infix  2 _-→*_
infix  1 `begin_
infixr 2 _-→⟨_⟩_
infixr 2 _-→*⟨_⟩_
infix  3 _`∎

infixr  2 _-→S_
data _>-_-→_ : Comm × State → ℕ → Comm × State → Set where
  -→Z : ∀ {M}
    → M >- 0 -→  M
  
  _-→S_ : ∀ {L M N n}
    → L -→ M 
    → M >- n -→ N 
    → L >- (suc n) -→ N


_-→*_ : Comm × State → Comm × State → Set 
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

-→*-refl : ∀ {M}
  ---------
  → M -→* M
-→*-refl = ⟨ 0 , -→Z ⟩

-→*-trans : ∀ {L M N}
  → L -→* M
  → M -→* N 
  ----------
  → L -→* N 
-→*-trans ⟨ .0 , -→Z ⟩ x₁ = x₁
-→*-trans ⟨ (suc n) , x -→S snd ⟩ x₁ with -→*-trans ⟨ n , snd ⟩ x₁
... | ⟨ fst , snd₁ ⟩ = ⟨ suc fst , (x -→S snd₁) ⟩

-→trans-→* : ∀ {L M N}
  → L -→ M
  → M -→* N
  ----------
  → L -→* N
-→trans-→* x ⟨ .0 , -→Z ⟩ = ⟨ 1 , x -→S -→Z ⟩
-→trans-→* x ⟨ suc n , x₁ -→S x₂ ⟩ = ⟨ suc (suc n) , x -→S x₁ -→S x₂ ⟩

_`∎ : ∀ M
  ---------
  → M -→* M
x `∎ = -→*-refl

_-→⟨_⟩_ : ∀ L {M N}
  → L -→ M
  → M -→* N 
  ----------
  → L -→* N
x -→⟨ x-→y ⟩ z = -→trans-→* x-→y z

_-→*⟨_⟩_ : ∀ L {M N}
  → L -→* M
  → M -→* N 
  ----------
  → L -→* N 
x -→*⟨ x-→*y ⟩ z = -→*-trans x-→*y z

-- x -→⟨ x-→y ⟩ -→Z = (x-→y -→S -→Z)
-- x -→⟨ x-→y ⟩ (x₁ -→S x₂) = (x-→y -→S x₁ -→S x₂)

`begin_ : ∀ {M N}
  → M -→* N
  ----------
  → M -→* N 
`begin M-→*N = M-→*N 

{- big step -}
data _⇓_ : Comm × State → State → Set where
  skip-exec : ∀ {σ}
    -------------------
    → ⟨ skip , σ ⟩ ⇓ σ 

  :=-exec : ∀ {x n σ}
  ----------------------------------------------
    → ⟨ x := n , σ ⟩ ⇓ modify σ x (evalI σ n) 

  ;-exec : ∀ {c₀ c₁ σ σ' σ''}
    → ⟨ c₀ , σ ⟩ ⇓ σ'
    → ⟨ c₁ , σ' ⟩ ⇓ σ''
    ---------------------------------
    → ⟨ c₀ ; c₁ , σ ⟩ ⇓ σ''

  `if-true : ∀ {b c₀ c₁ σ σ'}
    → T (evalB σ b)
    → ⟨ c₀ , σ ⟩ ⇓ σ'
    -------------------------------------------
    → ⟨ `if b `then c₀ `else c₁ , σ ⟩ ⇓ σ'

  `if-false : ∀ {b c₀ c₁ σ σ'}
    → T (not (evalB σ b))
    → ⟨ c₁ , σ ⟩ ⇓ σ'
    -------------------------------------------
    → ⟨ `if b `then c₀ `else c₁ , σ ⟩ ⇓ σ'

  `while-true : ∀ {b c σ σ' σ''}
    → T (evalB σ b)
    → ⟨ c , σ ⟩ ⇓ σ'
    → ⟨ `while b `do c , σ' ⟩ ⇓ σ''
    --------------------------------------------------------------
    → ⟨ `while b `do c , σ ⟩ ⇓ σ''

  `while-false : ∀ {b c σ}
    → T (not (evalB σ b))
    ----------------------------------
    → ⟨ `while b `do c , σ ⟩ ⇓ σ 

;-local : ∀ {c₁ s s' c'} 
  → ⟨ c₁ , s ⟩ -→* ⟨ c' , s' ⟩ 
  → (c₂ : Comm)
  --------------------------------------
  → ⟨ c₁ ; c₂ , s ⟩ -→* ⟨ c' ; c₂ , s' ⟩ 
;-local ⟨ .0 , -→Z ⟩ c₂ = -→*-refl
;-local ⟨ suc m , x -→S snd ⟩ c₂ with ;-local ⟨ m , snd ⟩ c₂
... | ⟨ _ , snd₁ ⟩ = form-→* (;-left x -→S snd₁)

sc-mg : ∀ {c₁ c₂ s s' s₂ t} 
  → ⟨ c₁ , s ⟩ -→* ⟨ skip , s₂ ⟩ → ⟨ c₂ , s₂ ⟩ -→* ⟨ t , s' ⟩
  → ⟨ c₁ ; c₂ , s ⟩ -→* ⟨ t , s' ⟩ 
sc-mg {c₁} {c₂} {s} {s'} {s₂} {t} x x₁ = 
  `begin 
    ⟨ c₁ ; c₂ , s ⟩
  -→*⟨ ;-local x c₂ ⟩  
    ⟨ skip ; c₂ , s₂ ⟩
  -→⟨ ;-exec ⟩ 
    ⟨ c₂ , s₂ ⟩
  -→*⟨ x₁ ⟩
    ⟨ t , s' ⟩
  `∎

sc-mg' : ∀ {c₁ c₂ s s' s₂} 
  → ⟨ c₁ , s ⟩ -→* ⟨ skip , s₂ ⟩ → ⟨ c₂ , s₂ ⟩ -→* ⟨ skip , s' ⟩
  → ⟨ c₁ ; c₂ , s ⟩ -→* ⟨ skip , s' ⟩ 
sc-mg' = sc-mg

sc-sp : ∀ {c₁ c₂ s s' n} 
  → ⟨ c₁ ; c₂ , s ⟩ >- n -→ ⟨ skip , s' ⟩ 
  -------------------------------------------------------------------------------------
  → ∃[ s₂ ] ∃[ a ] ∃[ b ] ((⟨ c₁ , s ⟩ >- a -→ ⟨ skip , s₂ ⟩) 
                            × (⟨ c₂ , s₂ ⟩ >- b -→ ⟨ skip , s' ⟩) 
                            × suc (a + b) ≡ n)
sc-sp {.skip} {c₂} {s} {s'} {suc n} (;-exec -→S x₁) = ⟨ s , ⟨ 0 , ⟨ n , ⟨ -→Z , ⟨ x₁ , refl ⟩ ⟩ ⟩ ⟩ ⟩
sc-sp {c₁} {c₂} {s} {s'} {suc n} (;-left x -→S x₁) with sc-sp x₁
... | ⟨ s₂ , ⟨ a , ⟨ b , ⟨ fst , ⟨ snd , sab≡n ⟩ ⟩ ⟩ ⟩ ⟩ = 
  ⟨ s₂ , ⟨ (suc a) , ⟨ b , ⟨ (x -→S fst) , ⟨ snd , cong suc sab≡n ⟩ ⟩ ⟩ ⟩ ⟩


-- sc-sp {.skip} {c₂} {s} {s'} {(suc n)} (;-exec -→S x₁) = ⟨ s , ⟨ ⟨ 0 , -→Z ⟩ , ⟨ n , x₁ ⟩ ⟩ ⟩
-- sc-sp {c₁} {c₂} {s} {s'} {(suc n)} (;-left x -→S x₁) with sc-sp x₁
-- ... | ⟨ s₂ , ⟨ ⟨ fst , snd ⟩ , t ⟩ ⟩ = ⟨ s₂ , ⟨ ⟨ suc fst , x -→S snd ⟩ , t ⟩ ⟩

big→small : ∀ {c σ σ'}
  → ⟨ c , σ ⟩ ⇓ σ'
  → ⟨ c , σ ⟩ -→* ⟨ skip , σ' ⟩ 
big→small skip-exec = -→*-refl
big→small :=-exec = -→trans-→* :=-exec -→*-refl
big→small (;-exec x x₁) = sc-mg (big→small x) (big→small x₁)
big→small (`if-true x x₁) = -→trans-→* (`if-true x) (big→small x₁)
big→small (`if-false x x₁) = -→trans-→* (`if-false x) (big→small x₁)
big→small (`while-true x x₁ x₂) = -→trans-→* (`while-true x) (sc-mg (big→small x₁) (big→small x₂))
big→small (`while-false x) = -→trans-→* (`while-false x) -→*-refl

-- small→big : ∀ {c σ σ'}
--   → ⟨ c , σ ⟩ -→* ⟨ skip , σ' ⟩ 
--   → ⟨ c , σ ⟩ ⇓ σ'
-- small→big ⟨ .0 , -→Z ⟩ = skip-exec
-- small→big ⟨ .1 , :=-exec -→S -→Z ⟩ = :=-exec
-- small→big ⟨ .(suc _) , ;-left x -→S snd ⟩ = {!   !}
-- small→big ⟨ .(suc _) , ;-exec -→S snd ⟩ = {!   !}
-- small→big ⟨ .(suc _) , `if-true x -→S snd ⟩ = {!   !}
-- small→big ⟨ .(suc _) , `if-false x -→S snd ⟩ = {!   !}
-- small→big ⟨ .(suc _) , `while-true x -→S snd ⟩ = {!   !}
-- small→big ⟨ .(suc _) , `while-false x -→S snd ⟩ = {!   !}