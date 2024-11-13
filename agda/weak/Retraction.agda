{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import weak.Cofibs
open import Prop
open import weak.Path
open import weak.Kan

module weak.Retraction where

  record Retraction {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
    constructor retract
    field 
      f   : A → B
      g   : B → A
      inv : (b : B) → Path B (f (g b)) b

  Contractible-Retract : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2}
                       → hasHFill B
                       → ContractibleFill A
                       → Retraction A B
                       → ContractibleFill B
  Contractible-Retract hcomB cA (retract f g inv) α t = fst c' , (\ pα → (fst (snd c') pα) ∘ ! (snd (snd (inv _)))) where
    c = cA α (λ pα → g (t pα))
    c' = hcomB `0 `1 (inl id) α (\ z pα → fst (inv (t pα)) z) (f (fst c) , (\ pα → ap (f) ((snd c) pα) ∘ (fst (snd (inv _)))))
    
  compose-retracts : ∀ {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
              → hasHFill C
              → Retraction A B
              → Retraction B C
              → Retraction A C
  compose-retracts hcomC (retract f g inv) (retract f' g' inv') = retract (f' o f) (g o g') (\ c → ∘Path hcomC (inv' c) (apPath f' (inv (g' c))))
