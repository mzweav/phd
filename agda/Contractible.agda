
{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Kan
open import Path

module Contractible where

  contr-extend-partial : {l : Level} {A : Set l} 
         → hasHCom A
         → Contractible A
         → ContractibleFill A
  contr-extend-partial hcomA cA α t = fst c , (\ pα → fst (snd c) pα ∘ ! (snd (snd (snd cA (t pα))))) where
    c = hcomA `0 `1 α (\ z pα → fst (snd cA (t pα)) z) (fst cA , (λ pα → fst (snd (snd cA (t pα)))))

  contr-implies-hprop : {l : Level} {A : Set l} 
                      → hasHCom A
                      → Contractible A
                      → (x y : A) → Path A x y
  contr-implies-hprop hcomA cA x y = (\ z → fst (p z) ) , (! ((snd (p `0)) (inl id))) , (! ((snd (p `1)) (inr id))) where
    p : ∀ z → _
    p z = contr-extend-partial hcomA cA ((z == `0) ∨ (z == `1)) (case01 (\ _ → x) (\ _ → y)) 

  contr-extend-partial-path : {l : Level} {A : Set l} 
                             → (hcomA : hasHCom A)
                             → (cA : Contractible A)
                             → (α : Set) {{cα : Cofib α}} (t : α → A)
                             → Path A (fst (contr-extend-partial hcomA cA α t)) (fst cA)
  contr-extend-partial-path hcomA cA α t = contr-implies-hprop hcomA cA _ _

  HProp : {l : Level} → Set l → Set l
  HProp A = (x y : A) → Path A x y

  HSet : {l : Level} → Set l → Set l
  HSet A = (x y : A) → HProp (Path A x y)

  subtype-path : {l1 l2 : Level} → {A : Set l1} (B : A → Set l2) → relCom B → ((a : A) → HProp (B a)) → (x y : Σ B) → Path A (fst x) (fst y) → Path _ x y
  subtype-path B comB propB (a1 , b1) (a2 , b2) p = (λ i → fst p i , fst pB i)
                                                    , pair= (fst (snd p)) (move-transport-left B (fst (snd p)) (fst (snd pB))) 
                                                    , pair= (snd (snd p)) (move-transport-left B (snd (snd p)) (snd (snd pB))) where

    coeB : ∀ i → _
    coeB i = comB (fst p) `0 i ⊥ (λ _ → abort) (transport! B (fst (snd p)) b1 , (λ ff → abort ff))

    fixB-path : Path _ (fst (coeB `1)) (transport! B (snd (snd p)) b2)
    fixB-path = propB (fst p `1) (fst (coeB `1)) (transport! B (snd (snd p)) b2)

    fixB : ∀ i → _
    fixB i = comB (λ _ → (fst p) i) `0 `1 ((i == `0) ∨ (i == `1))
                  (λ j → case01 (λ i=0 → transport! (B o fst p) i=0 (transport! B (fst (snd p)) b1))
                                (λ i=1 → transport! (B o fst p) i=1 (fst fixB-path j)))
                  (fst (coeB i)
                  , ∨-elim01 _ (λ i=0 → ! (apd! (λ i → fst (coeB i)) i=0)
                                        ∘ ap (transport! (B o fst p) i=0) (snd (snd (coeB `0)) id))
                               (λ i=1 → ! (apd! (λ i → fst (coeB i)) i=1)
                                        ∘ ap (transport! (B o fst p) i=1) (fst (snd (fixB-path)))))

    pB : PathO (B o fst p) (transport! B (fst (snd p)) b1) (transport! B (snd (snd p)) b2)
    pB = (λ i → fst (fixB i))
         , ! (fst (snd (fixB `0)) (inl id))
         , snd (snd fixB-path) ∘ ! (fst (snd (fixB `1)) (inr id))

  Σ-hprop : {l : Level}(A : Set l) (B : A → Set l) (_ : relCom B) → HProp A → ((a : A) → HProp (B a)) → HProp (Σ B)
  Σ-hprop A B comB propA propB (a1 , b1) (a2 , b2) = (λ i → fst pA i , fst pB i)
                                                           , pair= (fst (snd pA)) (move-transport-left B (fst (snd pA)) (fst (snd pB)))
                                                           , pair= (snd (snd pA)) (move-transport-left B (snd (snd pA)) (snd (snd pB))) where

    pA = propA a1 a2

    fillB : ∀ i → _
    fillB i = comB (fst pA) `0 i ⊥ (λ _ → abort)
                   (transport! B (fst (snd pA)) b1 , (λ ff → abort ff))

    fixB-path : Path _ (fst (fillB `1)) (transport! B (snd (snd pA)) b2)
    fixB-path = propB (fst pA `1) (fst (fillB `1)) (transport! B (snd (snd pA)) b2)

    fixB : ∀ i → _
    fixB i = comB (λ _ → (fst pA) i) `0 `1 ((i == `0) ∨ (i == `1))
                  (λ j → case01 (λ i=0 → transport! (B o fst pA) i=0 (transport! B (fst (snd pA)) b1))
                                (λ i=1 → transport! (B o fst pA) i=1 (fst fixB-path j)))
                  (fst (fillB i)
                  , ∨-elim01 _ (λ i=0 → ! (apd! (λ i → fst (fillB i)) i=0)
                                        ∘ ap (transport! (B o fst pA) i=0) (snd (snd (fillB `0)) id))
                               (λ i=1 → ! (apd! (λ i → fst (fillB i)) i=1)
                                        ∘ ap (transport! (B o fst pA) i=1) (fst (snd (fixB-path)))))

    pB : PathO (B o fst pA) (transport! B (fst (snd pA)) b1) (transport! B (snd (snd pA)) b2)
    pB = (λ i → fst (fixB i))
         , ! (fst (snd (fixB `0)) (inl id))
         , snd (snd fixB-path) ∘ ! (fst (snd (fixB `1)) (inr id))

  
  HProp-to-HSet : {l : Level}(A : Set l) (_ : hasHCom A) → HProp A → HSet A
  HProp-to-HSet A hcomA propA = setA where

    fillA : ∀ i j → (x y : A) (q1 q2 : Path A x y) → _
    fillA i j x y q1 q2 = hcomA `0 `1 (((i == `0) ∨ (i == `1)) ∨ ((j == `0) ∨ (j == `1)))
                                (λ k → case (case01 (λ _ → fst (propA x (fst q1 j)) k)
                                                    (λ _ → fst (propA x (fst q2 j)) k))
                                            (case01 (λ _ → fst (propA x (fst q1 j)) k)
                                                    (λ _ → fst (propA x (fst q1 j)) k))
                                            (∨-elim01 _ (λ i=0 → ∨-elim01 _ (λ j=0 → id)
                                                                            (λ j=1 → id))
                                                        (λ i=1 → ∨-elim01 _ (λ j=0 → ap (λ z → fst (propA x z) k)
                                                                                        (ap! (fst q1) j=0
                                                                                        ∘ ! (fst (snd q1))
                                                                                        ∘ fst (snd q2)
                                                                                        ∘ ap (fst q2) j=0))
                                                                            (λ j=1 → ap (λ z → fst (propA x z) k)
                                                                                        (ap! (fst q1) j=1
                                                                                        ∘ ! (snd (snd q1))
                                                                                        ∘ snd (snd q2)
                                                                                        ∘ ap (fst q2) j=1)))))
                                (x
                                , ∨-elim _ (∨-elim01 _ (λ _ → fst (snd (propA x (fst q1 j))))
                                                       (λ _ → fst (snd (propA x (fst q2 j)))))
                                           (∨-elim01 _ (λ _ → fst (snd (propA x (fst q1 j))))
                                                       (λ _ → fst (snd (propA x (fst q1 j)))))
                                           (λ _ _ → uip))

    setA : HSet A
    setA x y q1 q2 = (λ i → (λ j → fst (fillA i j x y q1 q2))
                                , (fst (snd q1) ∘ snd (snd (propA x (fst q1 `0))))
                                  ∘ ! (fst (snd (fillA i `0 x y q1 q2)) (inr (inl id)))
                                , (snd (snd q1) ∘ snd (snd (propA x (fst q1 `1))))
                                  ∘ ! (fst (snd (fillA i `1 x y q1 q2)) (inr (inr id))))
                         , pair= (λ= λ j → (snd (snd (propA x (fst q1 j))))
                                 ∘ ! (fst (snd (fillA `0 j x y q1 q2)) (inl (inl id))))
                                 (×= uip uip)
                         , pair= (λ= λ j → (snd (snd (propA x (fst q2 j))))
                                 ∘ ! (fst (snd (fillA `1 j x y q1 q2)) (inl (inr id))))
                                 (×= uip uip)
                                 
{-
  Contractible-hprop : {l : Level}(A : Set l) (_ : hasHCom A) (_ : relCom (λ a → (a' : A) → Path A a a')) → HProp (Contractible A)
  Contractible-hprop A hcomA comPathA c = Σ-hprop A (λ a → (a' : A) → Path A a a') comPathA propA propPathA c where

    propA : HProp A
    propA = contr-implies-hprop hcomA c

    setA : HSet A
    setA = HProp-to-HSet A hcomA propA
    
    propPathA : ∀ a q1 q2 → _
    propPathA a q1 q2 = (λ i a' → fst (setA a a' (q1 a') (q2 a')) i)
                        , (λ= λ a' → fst (snd (setA a a' (q1 a') (q2 a'))))
                        , (λ= λ a' → snd (snd (setA a a' (q1 a') (q2 a'))))
-}

  ContractibleFill-hprop : {l : Level} (A : Set l) → (c1 c2 : ContractibleFill A) → Path (ContractibleFill A) c1 c2
  ContractibleFill-hprop A c1 c2 = (\ z → λ α t → fst (c z α t) , (\ pα → snd (c z α t) (inl pα))) , (λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (c `0 α {{cα}} t) (inr (inl id))) ) (λ= \ _ → uip)) , (λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (c `1 α {{cα}} t) (inr (inr id))) ) (λ= \ _ → uip)) where
    c : ∀ z α {{cα : Cofib α}} t → _
    c z α t = c1 (α ∨ ((z == `0) ∨ (z == `1)))
              (case (\ pα → t pα)
                    (case01 (\ z=0 → fst (c1 α t)) (\ z=1 → fst (c2 α t)))
                    (\ pα → ∨-elim01 _
                            (\ z=0 → snd (c1 α t) pα)
                            ((\ z=1 → snd (c2 α t) pα))))

  inhabited-hprop-contractible : {l : Level} (A : Set l) 
                               → hasHCom A
                               → A
                               → ((x y : A) → Path A x y)
                               → ContractibleFill A
  inhabited-hprop-contractible A hcomA a p = contr-extend-partial hcomA (a , (\ b → p a b))


  hcomContractibleFill : {l : Level} (A : Set l) → hasHCom (ContractibleFill A)
  hcomContractibleFill A r r' α t b = (λ β s → fst (c β s) , (\ pβ → snd (c β s) (inl (inl pβ)))) , ((\ pα → λ= (\ β → λ=inf \ cβ → λ= \ s → pair= (snd (c β {{cβ}} s) (inl (inr pα))) (λ= \ _ → uip)))) , (\ r=r' → λ= (\ β → λ=inf \ cβ → λ= \ s → pair= (snd (c β {{cβ}} s) (inr r=r')) (λ= \ _ → uip))) where
    c : ∀ β {{cβ : Cofib β}} s → _
    c β s = (fst b ((β ∨ α) ∨ (r == r'))
                 (∨-elim _ (case s (\ pα → fst ((t r' pα) β s)) (\ pβ pα → snd ((t r' pα) β s) pβ))
                 (\ r=r' → fst (fst b β s))
                 (∨-elim _ (\ pβ r=r' → snd (fst b β s) pβ ∘ ap= (transport-constant trunc)) (\ pα r=r' → ((ap (\ h → fst (h β s))) (snd b pα) ∘ ap (\ h → fst (t h pα β s)) (! r=r')) ∘ ap= (transport-constant trunc) ) (\ _ _ → λ= \ _ → uip))))


