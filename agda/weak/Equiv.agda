{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import weak.Kan
open import weak.Cofibs
open import weak.Pi
open import weak.Path

module weak.Equiv where

  back : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} → Equiv A B → B → A
  back e b =  fst (fst ((snd e b) ⊥ (\ x → abort x))) 

  inv1 : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} → (e : Equiv A B) → (b : B) → Path B (fst e (back e b)) b
  inv1 e b =  snd (fst ((snd e b) ⊥ (\ x → abort x))) 

  isIso-isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B)
                → hasHFill A
                → hasHFill B
                → isIso A B f
                → isEquivFill A B f
  isIso-isEquiv A B f hcomA hcomB (iso g gf fg) b α t =
       (fst (mkA `0) , (\ z → fst (mkB z)) ,
         ! (fst (snd (mkB `0)) (inr (inl id)))  ,
         ! (snd (snd (mkB `1)) id)) ,
         (\ pα → pair= (fst (snd (mkA `0)) pα ∘ ap g (! (fst (snd (snd (t pα))))) ∘ ! (gf _))
                       (pair= (λ= \ x → {!fst (snd (mkB x)) (inl pα) !})
                              (pair= uip uip))) where
     mkA : (z : I) → _
     mkA z = hcomA `1 z (inr id) α
                 (\ z pα → g (fst (snd (t pα)) z))
                 (g b , (\ pα → ap g (snd (snd (snd (t pα))))))

     mkinnerB : (z : I) → _
     mkinnerB z = (hcomB `1 z (inr id) α (\ z pα → fst (snd (t pα)) z) (b , (\ pα → snd (snd (snd (t pα))))))
  
     mkB : (z : I) → _
     mkB z = hcomB `1 z (inr id)
                   (α ∨ ((z == `0) ∨ (z == `1)))
                   (\ y → case (\ pα → fst (snd (t pα)) y )
                               (case01 (\ z=0 → f (fst (mkA y)))
                                       (\ _ →  fst (mkinnerB y ) ))
                               (\ pα → ∨-elim01 _ (\ z=0 → ap f (fst (snd (mkA y)) pα) ∘ ! (fg _))
                                                  (\ z=1 → fst (snd (mkinnerB y)) pα )))
                   (b ,
                    ∨-elim _ (\ pα → snd (snd (snd (t pα))))
                             (∨-elim01 _
                                       (\ z=0 → fg _ ∘ ! (ap f (snd (snd (mkA `1)) id)))
                                       (\ z=1 → ! (snd (snd (mkinnerB `1)) id)))
                             (\ _ _ → uip))
  

  !equiv : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} 
         → hasHFill A
         → Equiv A B
         → Equiv B A
  !equiv hcomA e = (back e) , (λ b α t → {!fst (h b α t)!} , (\ pα → {!snd (h b α t) pα!})) where
    h : ∀ b α {{cα : Cofib α}} (t : α → HFiber (back e) b) → _
    h b α t =  (snd e (fst e b)) α (\ pα → back e (fst (t pα)) , apPath (fst e) (snd (t pα)))


  compose-equiv : ∀ {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
       → hasHFill C
       → Equiv A B
       → Equiv B C
       → Equiv A C
  compose-equiv hcomC e1 e2 = (\ a → fst e2 (fst e1 a)) ,
               (λ c α t → (fst (fst (use1 c α t)) ,
                           (\ z → fst (compose c α t z)) ,
                           ap (fst e2) (fst (snd (snd (fst (use1 c α t))))) ∘ ! (fst (snd (compose c α t `0)) (inl id))  ,
                           snd (snd (snd (fst (use2 c α t)))) ∘ ! (fst (snd (compose c α t `1)) (inr id)) ) ,
                          (\ pα → {!(snd (use1 c α t)) pα!})) where
       use2 : ∀ c α {{cα : Cofib α}} (t : α → HFiber (λ a → fst e2 (fst e1 a)) c) → _
       use2 c α t = snd e2 c α (\ pα → fst e1 (fst (t pα)) , snd (t pα))
       
       use1 : ∀ c α {{cα : Cofib α}} (t : α → HFiber (λ a → fst e2 (fst e1 a)) c) → _
       use1 c α t = snd e1 (fst (fst (use2 c α t)))
                        α
                        (\ pα → (fst (t pα)) , {!fst (use2 c α t)!})

       compose : ∀ c α {{cα : Cofib α}} t x → _
       compose c α t x = hcomC `0 `1 (inl id)
                               ((x == `0) ∨ (x == `1))
                               (\ z → case01 (\ x=0 → (fst e2 (fst (snd (fst (use1 c α t))) `0)))
                                             (\ x=1 →  fst (snd (fst (use2 c α t))) z) )
                               ((fst e2 (fst (snd (fst (use1 c α t))) x)) ,
                                ∨-elim01 _ (\ x=0 → ap (fst e2) (ap (fst (snd (fst (use1 c α t)))) (! x=0)))
                                           (\ x=1 → ap (fst e2) (! (ap (fst (snd (fst (use1 c α t)))) x=1) ∘ ! (snd (snd (snd (fst (use1 c α t)))))) ∘ fst (snd (snd (fst (use2 c α t))))))

       

  -- super easy proof!
  transportEquivLine : ∀ {l1 l2} {A : Set l1} (B : A → Set l2) (comB : relWCom B) 
                     → (p : I → A)
                     → Equiv (B (p `0)) (B (p `1))
  transportEquivLine B wcomB p = 
    (compose-equiv (relFill-hasHFill B (relWCom-relFill B wcomB) _)
                   (!equiv (hcomΠ _ _ (\ x → (relFill-hasHFill B (relWCom-relFill B wcomB) (p x))))
                           (_ , wcomB (p) `0))
                   (_ , wcomB (p) `1))

  transportEquiv : ∀ {l1 l2} {A : Set l1} (B : A → Set l2) (comB : relWCom B) {a1 a2 : A}
                → (p : Path A a1 a2)
                → Equiv (B a1) (B a2)
  transportEquiv {A = A} B wcomB p =
    (\ b → transport B (snd (snd p)) (fst (transportEquivLine B wcomB (fst p)) (transport B (! (fst (snd p))) b)) ) ,
           {!TODO!}
    -- writing out the transport for better definitional equality

    -- transport (\ (p : A × A) → Equiv (B (fst p)) (B (snd p)) ) (pair= (fst (snd p)) (snd (snd p) ∘ ap= (transport-constant  (fst (snd p)))))
    --                          (transportEquivLine B wcomB (fst p))

  equivExtension : ∀ {l1 l2} {A : Set l1} {B : Set l2} {α : Set} {{ca : Cofib α}}
                    (a : α → A) (b : α → B)
                → (e : Equiv A B)
                → ((pα : α) → fst e (a pα) == b pα)
                → Equiv (A [ α ↦ a ]) (B [ α ↦ b ])
  equivExtension a b e p = (\ x → fst e (fst x) , (\ pα → ap (fst e) (snd x pα) ∘ ! (p pα))) ,
                           {!!}

  PathOverPathEquiv : ∀ {l1} {A : I → Set l1} {a0 : A `0} {a1 : A `1}
                    → (wcomA : relWCom A)
                    → Equiv (PathO A a0 a1) (Path (A `1) (fst ((transportEquivLine A wcomA) (\ x → x)) a0) a1)
  PathOverPathEquiv {A = A} wcomA = {!equivExtension {A = (x : I) → A x} {I → A `1}_ _ ? ? !}


  Πequiv-constant : ∀ {l1 l2 : Level} (A : Set l1) (B B' : A → Set l2)
                  → ((x : A) → Equiv (B x) (B' x))
                  → Equiv ((x : A) → B x) ((x : A) → B' x)
  Πequiv-constant A B B' e = (\ f x → fst (e x) (f x)) , {!!}


  -- function comes out wrong.  
  -- would work if we already know that isEquiv is fibrant
  relWCom-equiv : ∀ {l : Level} (A B : I → Set l)
                → relWCom A
                → ((x : I) → Equiv (B x) (A x))
                → hasWCom B
  relWCom-equiv A B wcomA e r =  transport (isEquivFill ((r' : I) → B r') (B r)) {!!} (snd e') where
    e' = compose-equiv {!!} (Πequiv-constant I B A e) (compose-equiv {!!} (_ , wcomA (\ x → x) r) (!equiv {!!} (e r))) 

