-- A tiny fragment of HoTT, postulated

{-# OPTIONS --without-K --type-in-type #-}
module _ where

infix 4 _≡_
infixl 4 _◾_
postulate
  _≡_ : {A : Set} → A → A → Set
  refl : {A : Set} {x : A} → x ≡ x
  _◾_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x

  cong
    : {A B : Set} → (f : A → B)
    → ∀ {x y} → (p : x ≡ y) → f x ≡ f y

  coe : {A B : Set} → A ≡ B → A → B
