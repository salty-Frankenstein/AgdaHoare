open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _<_; _≤_; _≡ᵇ_; _<ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ≤-antisym; +-monoˡ-<; +-monoˡ-≤; ≡ᵇ⇒≡; m+[n∸m]≡n; n≤1+n; +-comm)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; uncurry) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_∘_; id; const)
open import lang
open import semantics
open import hoare 

⊎-ex : ∀ {A B : Set} → ¬ A → A ⊎ B → B
⊎-ex x (inj₁ x₁) = ⊥-elim (x x₁)
⊎-ex x (inj₂ y) = y

<→+1≤ : ∀ {x y} → T (x <ᵇ y) → x + 1 ≤ y
<→+1≤ {zero} {suc y} x₁ = s≤s z≤n
<→+1≤ {suc x} {suc y} x₁ = s≤s (<→+1≤ x₁)

suc≤→< : ∀ {x y} → suc x ≤ y → T (x <ᵇ y)
suc≤→< (s≤s z≤n) = tt
suc≤→< (s≤s (s≤s x₁)) = suc≤→<  (s≤s x₁)

¬>→≤ : ∀ {x y} → ¬ (suc x ≤ y) → y ≤ x 
¬>→≤ {_} {zero} x₁ = z≤n
¬>→≤ {zero} {suc zero} x₁ = ⊥-elim (x₁ (s≤s (¬>→≤ (λ ()))))
¬>→≤ {zero} {suc (suc y)} x₁ = ⊥-elim (x₁ (s≤s (¬>→≤ (λ ()))))
¬>→≤ {suc x} {suc y} x₁ = s≤s (¬>→≤ (λ z → x₁ (s≤s z)))

_ : ⦃| _X == N 0 |⦄ 
    `while (_X `< N 100) `do 
      (X := _X `+ N 1 ; Y := _X)
    ⦃| _X == N 100 && _Y == N 100 |⦄ 
_ = h-wc l10 l11
  where
    l1 : (_X !< N 100 || _X == _Y) && _X <= N 100 && A (_X `< N 100)
      ⇒ (_X `+ N 1) <= N 100
    l1 = ⇒-trans &&-elimʳ (form <→+1≤)

    l2 : ⦃| (_X `+ N 1) <= N 100 |⦄ X := (_X `+ N 1) ⦃| _X <= N 100 |⦄
    l2 = h-:=

    l3 : ⦃| (_X !< N 100 || _X == _Y) && _X <= N 100 && A (_X `< N 100) |⦄
          X := _X `+ N 1
         ⦃| _X <= N 100 |⦄
    l3 = h-sp l1 l2

    l4 : _X <= N 100 ⇒ (_X !< N 100 || (_X == _X)) && _X <= N 100
    l4 = &&-form (⇒-trans (form (const refl)) ||-formʳ) (form id)

    l5 : ⦃| (_X !< N 100 || _X == _X) && _X <= N 100 |⦄ 
          Y := _X 
         ⦃| (_X !< N 100 || _X == _Y) && _X <= N 100 |⦄
    l5 = h-:=

    l6 : ⦃| _X <= N 100 |⦄ 
          Y := _X 
         ⦃| (_X !< N 100 || _X == _Y) && (_X <= N 100) |⦄
    l6 = h-sp l4 l5

    l7 : ⦃| (_X !< N 100 || _X == _Y) && _X <= N 100 && A (_X `< N 100) |⦄
          X := _X `+ N 1 ; Y := _X 
         ⦃| (_X !< N 100 || _X == _Y) && _X <= N 100 |⦄
    l7 = h-sc l3 l6

    l8 : ⦃| (_X !< N 100 || _X == _Y) && _X <= N 100 |⦄
           `while _X `< N 100 `do 
             (X := _X `+ N 1 ; Y := _X) 
         ⦃| (_X !< N 100 || _Y == _X) && _X <= N 100 && ! (_X !< N 100) |⦄
    l8 = h-wc l8' (h-wh l7)
      where 
        l8' : (_X !< N 100 || _X == _Y) && _X <= N 100 && ! A (_X `< N 100) 
          ⇒ (_X !< N 100 || _Y == _X) && _X <= N 100 && ! (_X !< N 100)
        l8' = &&-form (&&-form (⇒-trans &&-elimˡ (⇒-trans &&-elimˡ (||-injʳ (form sym)))) 
                              (⇒-trans &&-elimˡ &&-elimʳ)) 
              (⇒-trans &&-elimʳ (form (λ {st} x x₁ → x (suc≤→< x₁))))  

    l9 : _X == N 0 ⇒ (_X !< N 100 || (_X == _Y)) && _X <= N 100
    l9 = &&-form (⇒-trans (form t1) ||-formˡ) (form t2)
      where
        t1 : ∀ {x} → x ≡ 0 → x < 100
        t1 refl = s≤s z≤n
        t2 : ∀ {x} → x ≡ 0 → x ≤ 100
        t2 refl = z≤n

    l10 : (_X !< N 100 || (_Y == _X)) && (_X <= N 100) && (! (_X !< N 100))
        ⇒ _X == N 100 && _Y == N 100
    l10 = &&-form l21 (⇒-trans (&&-form l21 ⇒-refl) 
                      (⇒-trans (&&-form &&-elimˡ (⇒-trans &&-elimʳ 
                                                          (⇒-trans (&&-form &&-elimʳ (⇒-trans &&-elimˡ &&-elimˡ)) 
                                                                   (form (uncurry ⊎-ex))))) 
                                (form (λ {⟨ fst , snd ⟩ → trans snd fst}))))
      where 
        l3' : (_X <= N 100) && (! (_X !< N 100)) ⇒ _X == N 100
        l3' = ⇒-trans (&&-form &&-elimˡ (⇒-trans &&-elimʳ (form ¬>→≤))) (form (uncurry ≤-antisym))

        l21 : (_X !< N 100 || (_Y == _X)) && (_X <= N 100) && (! (_X !< N 100)) ⇒ _X == N 100
        l21 = ⇒-trans (&&-form &&-elimʳ (⇒-trans &&-elimˡ &&-elimʳ)) (⇒-trans &&-comm l3')
    
    l11 : ⦃| _X == N 0 |⦄
           `while _X `< N 100 `do 
             (X := _X `+ N 1 ; Y := _X) 
         ⦃| (_X !< N 100 || (_Y == _X)) && _X <= N 100 && !(_X !< N 100 ) |⦄
    l11 = h-sp l9 l8