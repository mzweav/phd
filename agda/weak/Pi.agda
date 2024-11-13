{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import weak.Kan
open import weak.Cofibs

module weak.Pi where
  
  hcomΠ : ∀ {l1 l2 : Level} (A : Set l1) (B : A → Set l2)
           → ((x : A) → hasHFill (B x) )
           → hasHFill ( (x : A) → B x)
  hcomΠ A B hcomB r r' r01 α t b = ((\ a → fst (c a))) , (\ pα → λ= \ a → fst (snd (c a)) pα ) , (\ r=r' → λ= \ z → snd (snd (c z)) r=r') where
    c : (x : A) → _
    c x = hcomB x r r' r01 α (\ z pα → t z pα x) (fst b x , (\ pα → ap= (snd b pα))) 

  comΠrange :  ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Set l2} (B : Γ × A → Set l3) → relFill B → relFill (λ γ → (a : A) → B (γ , a))
  comΠrange B comB γ r r' r01 α t b = (λ a → fst (fillb a)) , (λ pα → λ= λ a → fst (snd (fillb a)) pα) , (λ {id → λ= (λ a → snd (snd (fillb a)) id)}) where
    fillb : ∀ a → _
    fillb a = comB (\ x → γ x , a) r r' r01 α (λ z pα → (t z pα) a) ((fst b) a , (λ pα → ap (λ f → f a) (snd b pα)))

  wcomΠ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3}
       → relWCom A
       → relWCom B
       → relWCom (\ γ → (x : A γ) → B (γ , x))
  wcomΠ {A = A} {B = B} wcomA wcomB p r b α t =
    ((\ r' a' → transport (\ H → B (p r' , H)) (snd (snd (snd (relWCom-relWCoe A wcomA p r' a'))))
                          (fst (fix r' a' `1 (useuse r' a')))) ,
      {!!}) ,
      (\ pα → =HFiber (λ= \ r' → λ= \ a → ap (transport (λ H → B (p r' , H)) (snd (snd (snd (relWCom-relWCoe A wcomA p r' a))))) (fst (snd (fix r' a `1 (useuse r' a))) pα) ∘ ! (apd (fst (t pα) r') (snd (snd (snd (relWCom-relWCoe A wcomA p r' a))))) )
                      {!!}) where
  
    coeA : (r : I) (r' : I) → (a : A (p r)) → A (p r')
    coeA r r' a =  fst (relWCom-relWCoe A wcomA p r a) r'

    use : (r' : I) (a : A (p r')) → _
    use r' a = wcomB (\ y → p y , coeA r' y a)
                    r
                    ( (b (coeA r' r a)) ) 
                     α 
                    (\ pα → ((\ z → fst (t pα) z (coeA r' z a))) ,
                            (\ z → fst (snd (t pα)) z (coeA r' r a) ) ,
                            ap (\ H → H (coeA r' r a)) (fst (snd (snd (t pα)))) ,
                            ap (\ H → H (coeA r' r a)) (snd (snd (snd (t pα)))) )

    fix : (r' : I) (a' : A (p r')) (k : I) → _
    fix r' a' k = relWCom-relCom (\ x → B (p r' , x)) (wcomPre (\ x → (p r' , x)) B wcomB)
                                 (fst (snd (relWCom-relWCoe A wcomA p r' a')))
                                 `0 k
                                 α
                                 (\ z pα → fst (t pα) r' (fst (snd (relWCom-relWCoe A wcomA p r' a')) z)) 

    useuse : (r' : I) (a' : A (p r')) → _
    useuse r' a' = (transport (\ H → B (p r' , H)) (! (fst (snd (snd (relWCom-relWCoe A wcomA p r' a')))))
                                             (fst (fst (use r' a')) r') ,
                                   (\ pα → (ap (transport (\ H → B (p r' , H)) (! (fst (snd (snd (relWCom-relWCoe A wcomA p r' a')))))) (ap (\ z → fst z r') (snd (use r' a') pα))) ∘ ! (apd (fst (t pα) r') (! (fst (snd (snd (relWCom-relWCoe A wcomA p r' a'))))))))


  Πcommute : ∀ {l2 l3 : Level}
               (A : I → Set l2) → relWCom A
             → (B : Σ A → Set l3) → relWCom B
           → Equiv ((x : I) → (a : A x) → B (x , a))
                   ((f : (x : I) → A x) → (x : I) → B (x , f x) )
  Πcommute A comA B comB = (\ f a x → f x (a x)) ,
                           (λ b α t → ((λ x a → {! b (\ y → fst (fst ((comA (\ x → x) x a) ⊥ (\ x → abort x))) y) x !}) , {!!}) , {!!})

{-

  fillΠstrict : ∀ {l} → (A : I → Set l) → hasWCom A
                → (B : Σ A → Set l) → relFill B
                → hasWCom (\ x → (a : A x) → B (x , a))
  fillΠstrict A fillA B fillB r b α t = {!!} , {!!} where
    coexyA : (x : I) (y : I) → (a : A x) → A y
    coexyA x y a =  fst (fst (fillA x a ⊥ (\ x → abort x))) y  

    postulate
      coexyApath : (x : I) (a : A x) → Path (A x) (coexyA x x a) a

    use : (s : I) (a : A s) → _
    use s a = fillB (\ y → y , coexyA s y a)
                    r
                    ( (b (coexyA s r a)) )
                     α 
                    (\ pα z → fst (t pα z) (coexyA s z a) , (\ {id → ap (\ f → f _) (snd (t pα r) id)}) )

    -- TODO: this should be a strict composition instead
    fix : (s : I) (k : I) (a : A s) (b : B (s , fst (coexyApath s a) k ) [ α ↦ (\ pα → fst (t pα s) (fst (coexyApath s a) k)) ]) → B (s , a)
    fix s k a b =  coe (ap (\ h → B (s , h)) ( (snd (snd (coexyApath s a))) )) (  fst (fst f) `1   )  where
      f = fillB (\ z → s ,  fst (coexyApath s a) z  ) 
                k
                (fst b)
                α
                (\ pα → (\ z → fst (t pα s) (fst (coexyApath s a) z) ,
                        (\ {id → ! (snd b pα)})))


-}
