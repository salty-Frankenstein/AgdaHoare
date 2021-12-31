open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; recompute)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Integer.Base using (ℤ; _+_; _-_; +_; _<_; _≤_)
open import Data.Integer.Properties using (_<?_; ≤-step; ≤-<-trans; +-monoˡ-<)

open import lang
open import semantics2


Assertion : Set₁ 
Assertion = State → Set

infixl 5 _&&_
infixl 10 _==_ 
_&&_ : Assertion → Assertion → Assertion
P && Q = λ st → P st × Q st

_!<_ : IExp → IExp → Assertion
a !< b = λ st → eval st a < eval st b
_<=_ : IExp → IExp → Assertion
a <= b = λ st → eval st a ≤ eval st b
_==_ : IExp → IExp → Assertion
a == b = λ st → eval st a ≡ eval st b 

TRUE : Assertion
TRUE = λ st → ⊤
FALSE : Assertion
FALSE = λ st → ⊥

infixr 0 _⇒_ 
data _⇒_ : Assertion → Assertion → Set where
  form : ∀ {p q} → (∀ {st} → p st → q st) → p ⇒ q

data ⦃|_|⦄_⦃|_|⦄ : Assertion → Stmt → Assertion → Set where
  form : ∀ {P c Q}
    → (∀ {st st'} → ⟨ c , st ⟩ -→* ⟨ C skip , st' ⟩ → P st → Q st')
    → ⦃| P |⦄ c ⦃| Q |⦄

infix 1 ⦃|_|⦄_⦃|_|⦄
infix 2 _[_↦_]
_[_↦_] : Assertion → Id → IExp → Assertion
p [ x ↦ a ] = λ st → p (modify st x (eval st a))


h-sp : ∀ {P P' Q c} 
    → (P ⇒ P')
    → ⦃| P' |⦄ c ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ c ⦃| Q |⦄
h-sp (form p⇒p') (form p'||q) = form (λ c p → p'||q c (p⇒p' p))

h-wc : ∀ {P Q Q' c} 
    → (Q ⇒ Q')
    → ⦃| P |⦄ c ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ c ⦃| Q' |⦄
h-wc (form q⇒q') (form p||q) = form (λ c p → q⇒q' (p||q c p))

h-:= : ∀ {Q X a} → ⦃| Q [ X ↦ a ] |⦄ C (X := a) ⦃| Q |⦄
h-:= = form λ {⟨ suc .0 , :=-exec -→S -→Z ⟩ x₁ → x₁}

h-sk : ∀ {P} → ⦃| P |⦄ C skip ⦃| P |⦄
h-sk = form (λ {⟨ .0 , -→Z ⟩ x₁ → x₁})

sc-sp : ∀ {c₁ c₂ s s' n} 
    → ⟨ C (c₁ ; c₂) , s ⟩ >- n -→ ⟨ C skip , s' ⟩ 
    -------------------------------------------------------------------------------------
    → ∃[ s₂ ] ((⟨ C c₁ , s ⟩ -→* ⟨ C skip , s₂ ⟩) × (⟨ C c₂ , s₂ ⟩ -→* ⟨ C skip , s' ⟩))
sc-sp {.skip} {c₂} {s} {s'} {(suc n)} (;-exec -→S x₁) = ⟨ s , ⟨ ⟨ 0 , -→Z ⟩ , ⟨ n , x₁ ⟩ ⟩ ⟩
sc-sp {c₁} {c₂} {s} {s'} {(suc n)} (;-left x -→S x₁) with sc-sp x₁
... | ⟨ s₂ , ⟨ ⟨ fst , snd ⟩ , t ⟩ ⟩ = ⟨ s₂ , ⟨ ⟨ suc fst , x -→S snd ⟩ , t ⟩ ⟩

h-sc : ∀ {P R Q c₁ c₂} 
    → ⦃| P |⦄ C c₁ ⦃| R |⦄
    → ⦃| R |⦄ C c₂ ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ C (c₁ ; c₂) ⦃| Q |⦄
h-sc (form c₁-→skip→P→R) (form c₂-→skip→R→Q) = form λ {⟨ fst , snd ⟩ P → 
    let ⟨ σ , ⟨ c₁-→skip , c₂-→skip ⟩ ⟩ = sc-sp snd 
        P→R = c₁-→skip→P→R c₁-→skip
        R→Q = c₂-→skip→R→Q c₂-→skip
     in R→Q (P→R P)}

t : Assertion
t = _X !< pN 1
a : Assertion
a = t [ X ↦ pN 3 ]

_ : ⦃| TRUE |⦄ C (X := pN 0) ⦃| _X !< pN 5 |⦄
_ = h-sp (form λ x → _<_.+<+ (s≤s z≤n)) h-:=

_ : ⦃| _X !< pN 4 |⦄ C (X := _X `+ pN 1) ⦃| _X !< pN 5 |⦄
_ = h-sp (form (λ pst → +-monoˡ-< (+ 1) pst)) h-:=

_ : ⦃| _X !< pN 5 [ X ↦ _X `+ pN 1 ] |⦄ C (X := _X `+ pN 1) ⦃| _X !< pN 5 |⦄
_ = h-:=

_ : ∃[ P ] ⦃| P |⦄ C (X := _X `+ pN 2) ⦃| _X <= pN 10 |⦄
_ = ⟨ _X <= pN 10 [ X ↦ _X `+ pN 2 ] , h-:= ⟩

_ : ⦃| TRUE |⦄ C (X := pN 1 ; Y := pN 2) ⦃| _X == pN 1 && _Y == pN 2 |⦄
_ = h-sp (form (λ x → tt)) 
      (h-sc (h-sp (form (λ x → refl)) h-:=) (h-sp (form (λ x → ⟨ x , refl ⟩)) h-:=))
