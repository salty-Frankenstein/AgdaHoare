open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _<_; _≤_; _≡ᵇ_; _+_) renaming (_≟_ to _=?_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-monoˡ-<; ≡ᵇ⇒≡)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; recompute)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import lang
open import semantics2


Assertion : Set₁ 
Assertion = State → Set


infixl 5 _&&_
infixl 4 _||_
infixl 10 _==_ 
_&&_ : Assertion → Assertion → Assertion
P && Q = λ st → P st × Q st
_||_ : Assertion → Assertion → Assertion
P || Q = λ st → P st ⊎ Q st
!_ : Assertion → Assertion
! P = λ st → ¬ P st

_!<_ : IExp → IExp → Assertion
a !< b = λ st → evalI st a < evalI st b
_<=_ : IExp → IExp → Assertion
a <= b = λ st → evalI st a ≤ evalI st b
_==_ : IExp → IExp → Assertion
a == b = λ st → evalI st a ≡ evalI st b 

TRUE : Assertion
TRUE = λ st → ⊤
FALSE : Assertion
FALSE = λ st → ⊥

A : BExp → Assertion
A b = λ st → T (evalB st b)

notTrue : ∀ {x} → T (not x) → ¬ T x
notTrue {false} tt ()
notTrue {true} () x₁


infixr 0 _⇒_ 
data _⇒_ : Assertion → Assertion → Set where
  form : ∀ {p q} → (∀ {st} → p st → q st) → p ⇒ q

⇒-trans : ∀ {P Q R} → P ⇒ Q → Q ⇒ R → P ⇒ R 
⇒-trans (form x) (form x₁) = form (λ x₂ → x₁ (x x₂))

&&-elim : ∀ {P : Assertion} → TRUE && P ⇒ P
&&-elim = form (λ {⟨ _ , x ⟩ → x})

data ⦃|_|⦄_⦃|_|⦄ : Assertion → Comm → Assertion → Set where
  form : ∀ {P c Q}
    → (∀ {st st'} → ⟨ C c , st ⟩ -→* ⟨ C skip , st' ⟩ → P st → Q st')
    → ⦃| P |⦄ c ⦃| Q |⦄

infix 1 ⦃|_|⦄_⦃|_|⦄
infix 2 _[_↦_]
_[_↦_] : Assertion → Id → IExp → Assertion
p [ x ↦ a ] = λ st → p (modify st x (evalI st a))


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

h-:= : ∀ {Q X a} → ⦃| Q [ X ↦ a ] |⦄ (X := a) ⦃| Q |⦄
h-:= = form λ {⟨ suc .0 , :=-exec -→S -→Z ⟩ x₁ → x₁}

h-sk : ∀ {P} → ⦃| P |⦄ skip ⦃| P |⦄
h-sk = form (λ {⟨ .0 , -→Z ⟩ x₁ → x₁})

sc-sp : ∀ {c₁ c₂ s s' n} 
    → ⟨ C (c₁ ; c₂) , s ⟩ >- n -→ ⟨ C skip , s' ⟩ 
    -------------------------------------------------------------------------------------
    → ∃[ s₂ ] ((⟨ C c₁ , s ⟩ -→* ⟨ C skip , s₂ ⟩) × (⟨ C c₂ , s₂ ⟩ -→* ⟨ C skip , s' ⟩))
sc-sp {.skip} {c₂} {s} {s'} {(suc n)} (;-exec -→S x₁) = ⟨ s , ⟨ ⟨ 0 , -→Z ⟩ , ⟨ n , x₁ ⟩ ⟩ ⟩
sc-sp {c₁} {c₂} {s} {s'} {(suc n)} (;-left x -→S x₁) with sc-sp x₁
... | ⟨ s₂ , ⟨ ⟨ fst , snd ⟩ , t ⟩ ⟩ = ⟨ s₂ , ⟨ ⟨ suc fst , x -→S snd ⟩ , t ⟩ ⟩

h-sc : ∀ {P R Q c₁ c₂} 
    → ⦃| P |⦄ c₁ ⦃| R |⦄
    → ⦃| R |⦄ c₂ ⦃| Q |⦄
    ---------------------
    → ⦃| P |⦄ c₁ ; c₂ ⦃| Q |⦄
h-sc (form c₁-→skip→P→R) (form c₂-→skip→R→Q) = form λ {⟨ fst , snd ⟩ P → 
    let ⟨ σ , ⟨ c₁-→skip , c₂-→skip ⟩ ⟩ = sc-sp snd 
        P→R = c₁-→skip→P→R c₁-→skip
        R→Q = c₂-→skip→R→Q c₂-→skip
     in R→Q (P→R P)}

h-cd : ∀ {b P Q c₁ c₂}
    → ⦃| P && A b |⦄ c₁ ⦃| Q |⦄
    → ⦃| P && ! A b |⦄ c₂ ⦃| Q |⦄
    ----------------------------
    → ⦃| P |⦄ `if b `then c₁ `else c₂ ⦃| Q |⦄
h-cd (form caseT) (form caseF) =
    form λ {⟨ suc _ , `if-true x -→S snd ⟩ Pst → caseT (form-→* snd) ⟨ Pst , x ⟩
          ; ⟨ suc _ , `if-false x -→S snd ⟩ Pst → caseF (form-→* snd) ⟨ Pst , notTrue x ⟩}

_ : ⦃| TRUE |⦄ X := N 0 ⦃| _X !< N 5 |⦄
_ = h-sp (form λ x → s≤s z≤n) h-:=

_ : ⦃| _X !< N 4 |⦄ X := _X `+ N 1 ⦃| _X !< N 5 |⦄
_ = h-sp (form (λ pst → +-monoˡ-< 1 pst)) h-:=

_ : ∃[ P ] ⦃| P |⦄ X := _X `+ N 2 ⦃| _X <= N 10 |⦄
_ = ⟨ _X <= N 10 [ X ↦ _X `+ N 2 ] , h-:= ⟩

_ : ⦃| TRUE |⦄ X := N 1 ; Y := N 2 ⦃| _X == N 1 && _Y == N 2 |⦄
_ = h-sp (form (λ x → tt)) 
      (h-sc (h-sp (form (λ x → refl)) h-:=) (h-sp (form (λ x → ⟨ x , refl ⟩)) h-:=))


_ : ⦃| TRUE |⦄ 
    `if _X `= N 0 
    `then Y := N 2 
    `else (Y := _X `+ N 1) 
    ⦃| _X <= _Y |⦄
_ = h-cd (h-sp l (h-sp f h-:= )) (h-sp l (h-sp (form λ x → k) h-:=))
    where 
        l : ∀ {P} → TRUE && P ⇒ P
        l = form proj₂

        g : ∀ {a b : ℕ} → T (a ≡ᵇ b) → a ≡ b
        g {a} {b} = ≡ᵇ⇒≡ a b

        f : A (_X `= N 0) ⇒ (_X <= _Y) [ Y ↦ N 2 ]
        f = form λ x → ≤-trans (≤-reflexive (g x)) z≤n
        
        k : ∀ {x} → x ≤ x + 1
        k {zero} = z≤n
        k {suc x} = s≤s k
