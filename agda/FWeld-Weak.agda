{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Kan
open import FibWeld

module FWeld-Weak where 


  module WRec-Weak {l l' : Level} {α : Set}
                   {{cα : Cofib α}}
                   {T : α → Set l}
                   {B : Set l}
                   {f : (pα : α) → B → T pα}
                   (C : Set l')
                   (hcomC : hasHCom C)
                   (m : (b : B) → C)
                   (n : (pα : α) → (t : T pα) → C)
                   (p : (b : B) → (pα : α) → Path C (m b) (n pα (f pα b))) where

    adjust : (z : I) (b : B) → _
    adjust z b = hcomC `0 z α (\ z pα → fst (p b pα) z) (m b , (\ pα → fst (snd (p b pα)))) 

    module E = WElim (\ _ → C)
                     (relCom-constant C hcomC)
                     (\ a → fst (adjust `1 a))
                     (\ pα b → n pα b)
                     (\ a pα → ! (ap= (transport-constant (win-α! _ _ _ _ _ pα))) ∘ snd (snd (p a pα)) ∘ ! (fst (snd (adjust `1 a)) pα) )

    wrec-weak : (w : Weld α T B f) → C
    wrec-weak = E.welim


    wrec-weak-α : (pα : α) (t : T pα)
                → wrec-weak (coe (! (Weld-α α T B f pα)) t) == (n pα t)
    wrec-weak-α pα t = E.welim-α pα t

    wrec-weak-win : (b : B) → Path C (m b) (wrec-weak (win _ _ _ _ b)) [ α ↦ (\ pα → (\ z → fst (p b pα) z) , fst (snd (p b pα)) , ((fst (snd (adjust `1 b)) pα) ∘ ! (snd (snd (p b pα))) ) ∘ snd (snd (p b pα))) ]
    wrec-weak-win b = ((\ z → fst (adjust z b)) ,  ! (snd (snd (adjust `0 b)) id)  , id) , (\ pα → pair= (λ= \ z → (fst (snd (adjust z b)) pα)) (pair= uip uip))

    wrec-weak-α' : (pα : α) (b : Weld α T B f)
                → wrec-weak b == (n pα (coe (Weld-α α T B f pα) b))
    wrec-weak-α' pα b = ap= (transport-constant (ap= (transport-inv (λ X → X) (Weld-α _ _ _ _ pα)))) ∘ E.welim-α' pα b  



  module WElim-Weak {l l' : Level} {α : Set}
                   {{_ : Cofib α}}
                   {T : α → Set l}
                   {B : Set l}
                   {f : (pα : α) → B → T pα}
                   (C : Weld α T B f → Set l')
                   (comC : relCom C)
                   (m : (a : B) → C (win _ _ _ _ a))
                   (n : (pα : α) → (b : T pα) → C (coe (!(Weld-α α T B f pα)) b))
                   (p : (a : B) → (pα : α) → Path _ (m a) (transport C (win-α! _ _ _ _ _ pα) (n pα (f pα a)))) where

    adjust : (z : I) (b : B) → _
    adjust z b = relCom-hasHCom C comC (win _ _ _ _ b) `0 z α (\ z pα → fst (p b pα) z) (m b , (\ pα → fst (snd (p b pα)))) 

    module E = WElim C
                     comC
                     (\ a → fst (adjust `1 a))
                     (\ pα b → n pα b)
                     (\ a pα → snd (snd (p a pα)) ∘ ! (fst (snd (adjust `1 a)) pα)  )

