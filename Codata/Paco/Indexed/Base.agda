{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Paco.Indexed.Base where

open import Codata.Record.Indexed.M using (M)
import Data.Container.Indexed as Container
open import Data.Empty
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Function.Base
open import Level
open import Relation.Unary

open Container hiding (map)

private
  variable
    i c r a b : Level

record Paco {I : Set i} (C : Container I I c r) (Γ : Pred I a) (i : I) : Set (c ⊔ r ⊔ a) where
  coinductive
  constructor fold
  field
    unfold : ⟦ C ⟧ (Γ ∪ Paco C Γ) i

module _ {I : Set i} {C : Container I I c r} where

  Paco⇒M : Paco C ∅ ⊆ M C
  M.unfold (Paco⇒M paco) = record
    { fst = proj₁ unfolded
    ; snd = λ r → Paco⇒M (proj₂ unfolded r)
    }
    where
      unfolded : ⟦ C ⟧ (Paco C (const ⊥)) _
      unfolded = Container.map C
        {X = ∅ ∪ Paco C ∅}
        {Y = Paco C ∅}
        [ ⊥-elim , id ] (Paco.unfold paco)
  
  M⇒Paco : M C ⊆ Paco C ∅
  Paco.unfold (M⇒Paco m) = record
    { fst = proj₁ unfold
    ; snd = λ p → inj₂ (M⇒Paco (proj₂ unfold p))
    }
    where open M m
  
  map : ∀ {Γ : Pred I a} {Δ : Pred I b} → Γ ⊆ Δ → Paco C Γ ⊆ Paco C Δ
  Paco.unfold (map f paco) = record
    { fst = proj₁ unfold
    ; snd = λ p → case (proj₂ unfold p) of λ
      { (inj₁ x) → inj₁ (f x)
      ; (inj₂ x) → inj₂ (map f x)
      }
    }
    where open Paco paco
  
  ana : ∀ {P : Pred I a} {Γ : Pred I b} → P ⊆ ⟦ C ⟧ (Γ ∪ P) → P ⊆ Paco C Γ
  Paco.unfold (ana coalg x) = record
    { fst = proj₁ (coalg x)
    ; snd = λ p → case (proj₂ (coalg x) p) of λ
      { (inj₁ x) → inj₁ x
      ; (inj₂ x) → inj₂ (ana coalg x)
      }
    }
