{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Paco.Indexed.Properties where

open import Level
open import Relation.Unary

open import Data.Empty
open import Data.Product
open import Data.Sum as Sum
open import Function.Base
open import Data.Container.Indexed as Container
open import Codata.Paco.Indexed.Base as Paco

private
  variable
    a b : Level

module _ {i c r} {I : Set i} {C : Container I I c r} where

  accumulate : ∀ {Γ : Pred I a} {Δ : Pred I b} → Δ ⊆ Paco C (Γ ∪ Δ) → Δ ⊆ Paco C Γ
  accumulate {Γ = Γ} {Δ = Δ} H HΔ = Paco.ana coalg (H HΔ)
    where
      aux : (Γ ∪ Δ) ∪ Paco C (Γ ∪ Δ) ⊆ Γ ∪ Paco C (Γ ∪ Δ)
      aux (inj₁ (inj₁ x)) = inj₁ x
      aux (inj₁ (inj₂ x)) = inj₂ (H x)
      aux (inj₂ x)        = inj₂ x
  
      coalg : Paco C (Γ ∪ Δ) ⊆ ⟦ C ⟧ (Γ ∪ Paco C (Γ ∪ Δ))
      coalg = Container.map C (λ {i} → aux {x = i}) ∘ Paco.unfold
