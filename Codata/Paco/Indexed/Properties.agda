{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Paco.Indexed.Properties where

open import Codata.Paco.Indexed.Base as Paco
open import Data.Container.Indexed as Container
open import Data.Product
open import Data.Sum
open import Function.Base
open import Level
open import Relation.Unary

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
      coalg = Container.map C (λ {i} → aux {i}) ∘ Paco.unfold

  mult : ∀ {Γ : Pred I a} → Paco C (Γ ∪ Paco C Γ) ⊆ Paco C Γ
  Paco.unfold (mult {Γ = Γ} paco) = record
    { fst = proj₁ unfold
    ; snd = λ r → case (proj₂ unfold r) of λ
      { (inj₁ x) → x
      ; (inj₂ x) → inj₂ (mult x)
      }
    }
    where open Paco.Paco paco

  multiplication : ∀ {Γ : Pred I a} → Paco C (Paco C Γ) ⊆ Paco C Γ
  multiplication {Γ = Γ} H = mult (Paco.map inj₂ H)
