-- A tiny fragment of HoTT, with ua postulated, and some definitions.

{-# OPTIONS --without-K --type-in-type #-}
module _ where

open import MiniHoTT1
open import Data.Product public

isSet : Set → Set
isSet A = (x y : A) → ∀ (p q : x ≡ y) → p ≡ q

isInj : {A B : Set} (f : A → B) → Set _
isInj f = ∀ x x′ → f x ≡ f x′ → x ≡ x′

isSurj : {A B : Set} (f : A → B) → Set _
isSurj f = ∀ y → ∃ λ x → f x ≡ y

isEquiv : {A B : Set} (f : A → B) → Set _
isEquiv f = isInj f × isSurj f

infix 4 _≃_
_≃_ : (A B : Set) → Set _
A ≃ B = Σ (A → B) isEquiv

id : {A : Set} → A → A
id b = b

idIsEquiv : {A : Set} → isEquiv (id {A})
idIsEquiv = (λ x x′ p → p) , (λ x → (x , refl))

idEquiv : {A : Set} → A ≃ A
idEquiv = id , idIsEquiv

postulate
  ua : {A B : Set} → (A ≃ B) → (A ≡ B)
  ua-inj : {A B : Set} → isInj (ua {A} {B})
