open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; recompute)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
-- import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Integer.Base using (ℤ; _+_; _-_; +_; _<_; _≤_)
open import Data.Integer.Properties using (_<?_; ≤-step; ≤-<-trans)

open import lang
open import semantics2


Assertion : Set₁ 
Assertion = State → Set
  
_!<_ : IExp → IExp → Assertion
a !< b = λ st → eval st a < eval st b
_<=_ : IExp → IExp → Assertion
a <= b = λ st → eval st a ≤ eval st b
TRUE : Assertion
TRUE = λ st → ⊤
FALSE : Assertion
FALSE = λ st → ⊥

infixr 0 _⇒_ 
_⇒_ : Assertion → Assertion → Set 
p ⇒ q = {st : State} → p st → q st

-- data ⦃|_|⦄_⦃|_|⦄ : Assertion → Stmt → Assertion → Set where
--   form : ∀ {P c Q c' st st'}
--     → (⟨ c , st ⟩ -→* ⟨ c' , st' ⟩ → P st → Q st')
--     → ⦃| P |⦄ c ⦃| Q |⦄
⦃|_|⦄_⦃|_|⦄ : Assertion → Stmt → Assertion → Set 
⦃| P |⦄ c ⦃| Q |⦄ = ∀ {st st'} 
    → ⟨ c , st ⟩ -→* ⟨ C skip , st' ⟩ → P st → Q st'

infix 1 ⦃|_|⦄_⦃|_|⦄
infix 2 _[_↦_]
_[_↦_] : Assertion → Id → IExp → Assertion
p [ x ↦ a ] = λ st → p (modify st x (eval st a))


h-sp : ∀ {P P' Q c} 
    → (P ⇒ P')
    → ⦃| P' |⦄ c ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ c ⦃| Q |⦄
h-sp p⇒p' p'||q c p = p'||q  c (p⇒p' p)

h-wc : ∀ {P Q Q' c} 
    → (Q ⇒ Q')
    → ⦃| P |⦄ c ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ c ⦃| Q' |⦄
h-wc q⇒q' p||q c p = q⇒q' (p||q c p)

h-:= : ∀ {Q X a} → ⦃| Q [ X ↦ a ] |⦄ C (X := a) ⦃| Q |⦄
h-:= ⟨ .1 , :=-exec -→S -→Z ⟩ y = y
-- h-:= {Q} {X} {a} {st} {.(modify st X (eval st a))} ⟨ .1 , :=-exec -→S -→Z ⟩ y = y

t : Assertion
t = _X !< pN 1
a : Assertion
a = t [ X ↦ pN 3 ]

_ : ⦃| TRUE |⦄ C (X := pN 0) ⦃| _X !< pN 5 |⦄
_ = h-sp (λ x → _<_.+<+ (s≤s z≤n)) (h-:= {_X !< pN 5})

lmm : _X !< pN 4 ⇒ _X !< pN 5 [ X ↦ _X `+ pN 1 ]
lmm = λ x → {! λ st → eval (modify st X (eval st (_X `+ pN 1))) _X !} 
  where
    lll : ∀ {x y : ℤ} → x ≤ Data.Integer.Base.suc y → x < y + + 1
    lll {x} {y} x₁ = ≤-<-trans x₁ {!   !}
    ll : ∀ {x y : ℤ} → x < y → x < y + + 1
    ll {x} {y} x₁ = {!   !}
    l : {st : State} → st "X" < + 4 → st "X" + + 1 < + 5
    l {st} x with st "X" 
    ... | +_ zero = _<_.+<+ (s≤s (s≤s z≤n))
    ... | +_ (suc n) = _<_.+<+ (s≤s (s≤s {!   !}))
    ... | ℤ.negsuc n = {!   !}

lmm2 : _X !< pN 4 ⇒ _X !< pN 5 [ X ↦ _X `+ pN 1 ]
lmm2 = {!   !}

_ : ⦃| _X !< pN 4 |⦄ C (X := _X `+ pN 1) ⦃| _X !< pN 5 |⦄
_ = h-sp {_} {_} {_X !< pN 5} (lmm2 {{!   !}}) {!   !}
-- _ = h-sp lmm ((h-:= {_X !< pN 5}))

_ : ⦃| _X !< pN 5 [ X ↦ _X `+ pN 1 ] |⦄ C (X := _X `+ pN 1) ⦃| _X !< pN 5 |⦄
_ = h-:= {_X !< pN 5} 

_ : ∃[ P ] ⦃| P |⦄ C (X := _X `+ pN 2) ⦃| _X <= pN 10 |⦄
_ = ⟨ _X <= pN 10 [ X ↦ _X `+ pN 2 ] , h-:= {_X <= pN 10} ⟩

