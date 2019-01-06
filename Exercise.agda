{-# OPTIONS --without-K --type-in-type #-}
module _ where

data Bool : Set where
  true false : Bool

Bool-elim
  : (P : Bool → Set)
  → P true → P false
  → ∀ (b : Bool) → P b
Bool-elim P Pt Pf true  = Pt
Bool-elim P Pt Pf false = Pf

data Unit : Set where
  it : Unit

data Void : Set where

¬_ : Set → Set
¬ A = A → Void

open import MiniHoTT1

module BoolIsNotContractible where
  F : Bool → Set
  F = Bool-elim (λ _ → Set) Unit Void

  true≢false : ¬ (true ≡ false)
  true≢false p = coe (cong F p) it

-------------------------------------------------------------------------

U : Set _
U = Set

open import MiniHoTT2

module UniverseIsNotSet where
  not : Bool → Bool
  not = Bool-elim (λ _ → Bool) false true

  notNot : ∀ b → not (not b) ≡ b
  notNot = Bool-elim (λ b → not (not b) ≡ b) refl refl

  notIsInj : isInj not
  notIsInj b b′ p =    -- b
    sym (notNot b) ◾   -- not (not b)
    cong not p     ◾   -- not (not b′)
    notNot b′          -- b′

  notIsSurj : isSurj not
  notIsSurj b = not b , notNot b

  notIsEquiv : isEquiv not
  notIsEquiv = notIsInj , notIsSurj

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
