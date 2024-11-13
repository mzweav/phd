{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Kan

module Nat where

  data Nat {l : Level} : Set l where
    Z : Nat
    S : Nat{l} → Nat

  tpred : ∀ {l : Level} → Nat{l} → Nat{l}
  tpred Z = Z
  tpred (S x) = x

  decNat : {l : Level} (x y : Nat{l}) → (x == y) ∨ ((x == y) → ⊥{l})
  decNat Z Z = inl id
  decNat Z (S y) = inr (\ ())
  decNat (S x) Z = inr (\ ())
  decNat (S x) (S y) = case (\ p → inl (ap S p)) (λ q → inr (\ p → q (ap tpred p))) (\ _ _ → trunc) (decNat x y)

  
  
