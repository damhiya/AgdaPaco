{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Record.Indexed.M where

open import Data.Container.Indexed
open import Data.Product
open import Data.Sum
open import Function.Base
open import Level
open import Relation.Unary

private
  variable
    a i c r : Level

record M {I : Set i} (C : Container I I c r) (i : I) : Set (c ⊔ r) where
  coinductive
  constructor inf
  field
    unfold : ⟦ C ⟧ (M C) i

ana : ∀ {I : Set i} {C : Container I I c r} {P : Pred I a} → P ⊆ ⟦ C ⟧ P → P ⊆ M C
M.unfold (ana coalg x) = record
  { fst = proj₁ (coalg x)
  ; snd = λ r → ana coalg (proj₂ (coalg x) r)
  }
