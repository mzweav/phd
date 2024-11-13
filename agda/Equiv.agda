{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Path
open import Contractible
import ComInternal

module Equiv where

  -- normal definition

  isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (l1 ⊔ l2)
  isEquiv A B f = (b : B) → Contractible (HFiber f b)

  Equiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  Equiv A B = Σ \ (f : A → B) → isEquiv A B f

  id-Equiv : ∀ {l} {A : Set l} → hasHCom A → isEquiv A A (\ x → x)
  id-Equiv hcomA = λ a → (a , (\ _ → a) , id , id) , (s a) where
    abstract
      s = \ a → (\ hf → snd (scontr hcomA a) hf )

  QEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  QEquiv A B = Σ \ (f : A → B) → Σ \ (g : B → A) → ((x : A) → Path A ((g o f) x) x) × ((y : B) → Path B ((f o g) y) y)

  Equiv-to-QEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Equiv A B → QEquiv A B
  Equiv-to-QEquiv A B (f , eq) = f , g , eq1 , eq2 where
  
    g : B → A
    g b = fst (fst (eq b))

    h1 : (a : A) → _
    h1 a = snd (eq (f a)) (a , eq-to-Path _ _ id)

    eq1 : (a : A) → _
    eq1 a =  (λ i → fst (fst (h1 a) i))
             , ap fst (fst (snd (h1 a)))
             , ap fst (snd (snd (h1 a)))

    eq2 : (b : B) → _
    eq2 b = snd (fst (eq b))

  -- TODO: finish proof
  postulate
    QEquiv-to-Equiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → hasHCom A → hasHCom B → QEquiv A B → Equiv A B
    QEquiv-to-isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → hasHCom A → hasHCom B → (qeq : QEquiv A B) → isEquiv A B (fst qeq)
{-
  QEquiv-toEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → hasHCom A → QEquiv A B → Equiv A B
  QEquiv-toEquiv A B comA (f , g , eq1 , eq2) = f , (λ b → (g b , eq2 b) , h b) where

    h' : ∀ a b → Path B (f a) b → Path A (g b) a 
    h' a b p = ∘Path comA (eq1 a) (!Path comA ((λ i → g ((fst p) i)) , ap g (fst (snd p)) , ap g (snd (snd p))))

    h : ∀ b x → _
    h b (a , p) = (λ i → fst (h' a b p) i , {!!})
                , pair= (fst (snd (h' a b p))) {!!}
                , pair= (snd (snd (h' a b p))) {!!}
-}

  isEquiv-comp : ∀ {l1 l2 l3}
                 {A : Set l1}
                 {B : Set l2}
                 {C : Set l3}
                 (_ : hasHCom A)
                 (_ : hasHCom B)
                 (_ : hasHCom C)
                 (g : B → C)
                 (f : A → B)
                 →
                 isEquiv B C g → isEquiv A B f → isEquiv A C (g o f)
  isEquiv-comp {A = A} {B} {C} hcomA hcomB hcomC g f gEq fEq = QEquiv-to-isEquiv A C hcomA hcomC eqAC where

    eqAB = Equiv-to-QEquiv A B (f , fEq)
    eqBC = Equiv-to-QEquiv B C (g , gEq)

    f' = fst (snd eqAB)
    g' = fst (snd eqBC)

    eqAC : QEquiv A C
    eqAC = g o f , f' o g'
         , (λ a → ∘Path hcomA (fst (snd (snd eqAB)) a) (apPath f' (fst (snd (snd eqBC)) (f a))))
         , (λ c → ∘Path hcomC (snd (snd (snd eqBC)) c) (apPath g (snd (snd (snd eqAB)) (g' c))))

  Iso-Equiv : {l1 l2 : Level} {A : Set l1} {B : Set l2} → hasHCom A → hasHCom B → Iso A B → Equiv A B
  Iso-Equiv {A = A} {B} hcomA hcomB (iso f g Aeq Beq) = f , QEquiv-to-isEquiv A B hcomA hcomB
                                                                              (f , g , (λ a → eq-to-Path _ _ (Aeq a))
                                                                                     , (λ b → eq-to-Path _ _ (Beq b)))


  -- ----------------------------------------------------------------------
  -- other definitions of equivalence

  -- flip orientation of path

  isEquiv' : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (l1 ⊔ l2)
  isEquiv' A B f = (b : B) → Contractible (HFiber' f b)


  -- filling instead of normal def of contractibility

  isEquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (ℓ₁ ⊔ l1 ⊔ l2)
  isEquivFill A B f = (b : B) → ContractibleFill (HFiber f b)

  isEquiv-isEquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → isEquiv A B f → ((b : B) → hasHCom (HFiber f b)) → isEquivFill A B f
  isEquiv-isEquivFill A B f e hcomHFB b = contr-extend-partial (hcomHFB b) (e b)

  EquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set _
  EquivFill A B = Σ \ (f : A → B) → isEquivFill A B f

  transport-IsEquivFill : ∀ {l1 l2 : Level} {A A' : Set l1} {B : Set l2}
                            {f : A' → B} → isEquivFill A' B f
                            → (p : A == A')
                            → isEquivFill A B (f o coe p)
  transport-IsEquivFill e id = e

  -- ----------------------------------------------------------------------

  isEquivFill-hprop : {l1 l2 : Level} → (A : Set l1) (B : Set l2) (f : A → B) 
                → (e1 e2 : isEquivFill A B f)
                → Path (isEquivFill A B f) e1 e2
  isEquivFill-hprop A B f e1 e2 = (\ z → \ b → fst (ContractibleFill-hprop _ (e1 b) (e2 b)) z) ,
                                  (λ= \ b → fst (snd (ContractibleFill-hprop (HFiber f b) (e1 b) (e2 b)))) ,
                                  (λ= \ b → snd (snd (ContractibleFill-hprop (HFiber f b) (e1 b) (e2 b))))

  fix-isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) 
              → (isEquivFill A B f)
              → ContractibleFill (isEquivFill A B f)
  fix-isEquiv A B f b = inhabited-hprop-contractible _ (ComInternal.hcomΠ _ _ (\ x → hcomContractibleFill _)) b (isEquivFill-hprop A B f)

  abstract
    idEquiv-from-= : ∀ {l}{A B : Set l}(comA : hasHCom A)(f : A → B)(eq : A == B) → f == coe (ap (λ X → (A → X)) eq) (λ x → x) → isEquiv A B f
    idEquiv-from-= comA f id id a = scontr comA a


  
