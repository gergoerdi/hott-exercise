{-# OPTIONS --without-K --type-in-type #-}
module _ where

data Bool : Set where
  true false : Bool

Bool-elim
  : ∀ (P : Bool → Set)
  → P true → P false
  → ∀ b → P b
Bool-elim P Pt Pf true = Pt
Bool-elim P Pt Pf false = Pf

data Unit : Set where
  it : Unit

data Void : Set where

¬_ : Set → Set
¬ A = A → Void

-- A tiny fragment of HoTT, postulated
module _ where
  infix 4 _≡_
  postulate
    _≡_ : ∀ {A : Set} → A → A → Set
    refl : ∀ {A : Set} {x : A} → x ≡ x
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x

    subst
      : ∀ {A : Set} (B : A → Set) {x y : A}
      → (p : x ≡ y) → (B x → B y)

    cong
      : ∀ {A B : Set} → (f : A → B)
      → ∀ {x y} → (p : x ≡ y) → f x ≡ f y


module BoolIsNotContractible where
  F : Bool → Set
  F = Bool-elim (λ _ → Set) Unit Void

  true≢false : ¬ (true ≡ false)
  true≢false p = subst F p it

-------------------------------------------------------------------------

U : Set _
U = Set

open import Data.Product

-- More fragments of HoTT
module _ where
  isSet : Set → Set
  isSet A = (x y : A) → ∀ (p q : x ≡ y) → p ≡ q

  isEquiv : ∀ {A B : Set} (f : A → B) → Set _
  isEquiv {B = B} f = ∀ (y : B) → ∃ λ x → (f x ≡ y) × (∀ x′ → x ≡ x′ → f x′ ≡ y)

  infix 4 _≃_
  _≃_ : ∀ (A B : Set) → Set _
  A ≃ B = Σ (A → B) isEquiv

  id : ∀ {A : Set} → A → A
  id b = b

  idIsEquiv : ∀ {A : Set} → isEquiv (id {A})
  idIsEquiv x = x , refl , λ x′ p → sym p

  idEquiv : ∀ {A : Set} → A ≃ A
  idEquiv = id , idIsEquiv

  postulate
    ua : ∀ {A B : Set} → (A ≃ B) → (A ≡ B)
    ua-inj : ∀ {A B : Set} (equiv equiv′ : A ≃ B) →
      ua equiv ≡ ua equiv′ → equiv ≡ equiv′

module UniverseIsNotSet where
  not : Bool → Bool
  not = Bool-elim (λ _ → Bool) false true

  notNot : ∀ b → not (not b) ≡ b
  notNot = Bool-elim (λ b → not (not b) ≡ b) refl refl

  notIsEquiv : isEquiv not
  notIsEquiv = Bool-elim _
    (false , refl , Bool-elim _ (λ p → p)    (λ p → refl))
    (true ,  refl , Bool-elim _ (λ p → refl) (λ p → p))

  notEquiv : Bool ≃ Bool
  notEquiv = not , notIsEquiv

  notEquiv≢idEquiv : ¬ (ua notEquiv ≡ ua idEquiv)
  notEquiv≢idEquiv pEquiv = BoolIsNotContractible.true≢false eq
    where
      pFun : proj₁ notEquiv ≡ proj₁ idEquiv
      pFun = cong proj₁ (ua-inj notEquiv idEquiv pEquiv)

      eq : true ≡ false
      eq = cong (λ f → f false) pFun

  UIsNotSet : ¬ (isSet U)
  UIsNotSet prf = notEquiv≢idEquiv pEquiv
    where
      pEquiv : ua notEquiv ≡ ua idEquiv
      pEquiv = prf Bool Bool (ua notEquiv) (ua idEquiv)
