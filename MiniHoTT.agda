-- A tiny fragment of HoTT, with paths and ua postulated, and some definitions.

{-# OPTIONS --without-K --type-in-type #-}
module _ where

infix 4 _≡_
infixl 4 _◾_
postulate
  _≡_ : {A : Set} → A → A → Set
  refl : {A : Set} {x : A} → x ≡ x
  _◾_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x

  subst
    : {A : Set} (B : A → Set) {x y : A}
    → (p : x ≡ y) → (B x → B y)

  cong
    : {A B : Set} → (f : A → B)
    → ∀ {x y} → (p : x ≡ y) → f x ≡ f y

-------------------------------------------------------------------------

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
