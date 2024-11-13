{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;lzero;_⊔_)
open import Lib
open import Interval
open import weak.Cofibs
open import Prop
open import weak.Kan
open import weak.Path
open import weak.Equiv
open import weak.Retraction

module weak.Kan2 where 



  -- ----------------------------------------------------------------------
  -- still wonder if this suffices

  □ : Set
  □ = I × I

  U : □ → Set
  U (x , y) = ((x == `0) ∨ (x == `1)) ∨ (y == `0)

  hasUFillers : {l : Level} (A : Set l) → Set ((lsuc lzero) ⊔ l)
  hasUFillers A = (t : (x : □) → U x → A) → ContractibleFill ((x : □) → A [ U x ↦ t x ])

  Contractible : {l : Level} (A : Set l) → Set l
  Contractible A = Σ \ (a : A) → (b : A) → Path A a b

  -- define a type to be fibrant if hfiber is contractible and hasUfillers

  module _ {l : Level} (A : Set l) where
    q : hasHCom A → hasUFillers A
    q hcomA u α t = (λ xy → fst (h xy) ,
                    (∨-elim _ (\ side → fst (snd (h xy)) (inr side)) (\ bot → snd (snd (h xy)) (! bot) ∘ {!!}) (\ _ _ → uip))) ,
                    (\ pα → λ= \ xy → pair= (fst (snd (h xy)) (inl pα)) (λ= \ _ → uip)) where
      h : (xy : _) → _
      h (x , y) = hcomA `0 y (α ∨ ((x == `0) ∨ (x == `1)))
                             (\ z → case (\ pα → fst (t pα (x , z)))
                                         (\ side → u (x , z) (inl side))
                                         (\ pα side → ! (snd (t pα (x , z)) (inl side))))
                             (u (x , `0) (inr id)  ,
                              ∨-elim _ (\ pα → ! (snd (t pα (x , `0)) (inr id)))
                                       (\ side → ap (u (x , `0)) trunc)
                                       (\ _ _ → uip))

  top : {l : Level} {A : Set l} → (□ → A) → ((xy : □) → U xy → A)
  top f = \xy _ → f xy

  hasWeakUFillers : {l : Level} (A : Set l) → Set ((lsuc lzero) ⊔ l)
  hasWeakUFillers A = isEquivFill (□ → A) ((xy : □) → U xy → A) top

  
  
  derive-homog : {l : Level} {A : Set l} {B : A → Set l}
               → relCom B
               → (a1 : A)
               → (sq : (x y : I) → A [ (x == `1) ↦ (\ _ → a1) ] )
               → (b1 : B (fst (sq `1 `0)))
               → (p : (x : I) → B (fst (sq x `0)) [ (x == `1) ↦ (\ x=1 → transport (\ z → B (fst (sq z `0))) (! x=1) b1) ] )
               → (q : (x : I) → B (fst (sq x `1)) [ (x == `1) ↦ ((\ x=1 → transport (\ z → B (fst (sq z `1))) (! x=1) {!b1!})) ] )
               → (x y : I) → B (fst (sq x y)) 
  derive-homog {B = B} comB a1 sq b1 p q x y = {!c!} where
    c = 
        (comB (\ x → fst (sq x y)) `1 x
              {{Cofib=1r}}
              ((y == `0) ∨ (y == `1))
              (\ z → ∨-elim01 _ (\ y=0 → transport (\ H → B(fst (sq z H))) (! y=0) (fst (p z)))
                                ((\ y=1 → transport (\ H → B(fst (sq z H))) (! y=1) (fst (q z)))))
              (transport B {!!} b1 ,
               ∨-elim01 _ {!(snd (p `1))!} (\ y=1 → {!snd (q `1) id!}) ))
               
  

  hasCom0 : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasCom0 A = (r' : I) 
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A z) 
             (b : A `0 [ α ↦ t `0 ]) 
            → A r' [ α ↦ t r' , (`0 == r') ↦ ⇒ (fst b) ]
  -- SFiber (apply `0) : (I → A) -> A is contractible

  hasWCom0 :  ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasWCom0 A = (r : I) → isEquivFill ((r' : I) → A r') (A `0) (apply A `0)

  hasHFill0 : ∀ {l} → (Set l) → Set (lsuc lzero ⊔ l)
  hasHFill0 A = (r' : I) 
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A) 
             (b : A [ α ↦ t `0 ]) 
            → A [ α ↦ t r' , (`0 == r') ↦ ⇒ (fst b) ]

  hasHFill1 : ∀ {l} → (Set l) → Set (lsuc lzero ⊔ l)
  hasHFill1 A = (r' : I) 
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A) 
             (b : A [ α ↦ t `1 ]) 
            → A [ α ↦ t r' , (`1 == r') ↦ ⇒ (fst b) ]

  relCom0 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relCom0 {Γ = Γ} A = (p : I → Γ) → hasCom0 (A o p)

  hasCoe0 : {l : Level} → (I → Set l) → Set l
  hasCoe0 A = (r' : I) 
           → (b : A `0) 
           → A r' [ (`0 == r') ↦ ⇒ b ]

  relCoe0 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (l1 ⊔ l2)
  relCoe0 {_} {_} {Γ} A = (p : I → Γ) → hasCoe0 (A o p)

  hasCom-hasCoe0 : ∀ {l1 } (A : I → Set l1) -> 
                   hasCom0 A 
                 → hasCoe0 A
  hasCom-hasCoe0 A comA r' b = fst com , (\ r=r' → snd (snd com) r=r') where
    com = comA r' ⊥ (\ x → abort) (b , \ x → abort x)

  relCom-relCoe0 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom0 A 
                 → relCoe0 A
  relCom-relCoe0 A comA p r' b = fst com , (\ r=r' → snd (snd com) r=r') where
    com = comA p r' ⊥ (\ x → abort) (b , \ x → abort x)

  
  inv : ∀ {l} → (A : Set l) → hasCom0 (\ _ → A) → ∀ {a0 a1} → Path A a0 a1 → Path A a1 a0
  inv A hcomA {a0}{a1} p = (\ z → fst (i z)) , snd (snd p)  ∘ ! (fst (snd (i `0)) (inl id)) , ! (fst (snd (i `1)) (inr id)) where
    i : ∀ z → _
    i z = hcomA `1 ((z == `0) ∨ (z == `1))
                   (\ y → case01 (\ _ → fst p y)
                                 (\ _ → a0))
                   (a0 , (∨-elim01 _ (\ _ → fst (snd p)) (\ _ → id) )) 

  het-to-homPath : ∀ {l} → (A : I → Set l) → (com0 : relCom0 A) → ∀ {a0 a1}
                 → PathO A a0 a1
                 → Path (A `1) (fst (relCom-relCoe0 A com0 (\ x → x) `1 a0)) a1
  het-to-homPath A comA {a0} {a1} p = (\ z → (fst (h z))) , (! (fst (snd (h `0)) (inl id)) , snd (snd p) ∘ ! (fst (snd (h `1)) (inr id))) where
    h : ∀ z → _
    h z = comA ((\ x → x)) `1 ((z == `0) ∨ (z == `1))
               (\ y → case01 (\ z=0 → (fst (relCom-relCoe0 A comA (\ x → x) y a0)))
                             (\ z=1 → fst p y)  )
               (a0 , ∨-elim01 _ (\ z=0 → ! (snd (snd (comA (λ x → x) `0 ⊥ (λ x → abort) (a0 , (λ x → abort x)))) id))
                                (\ z=1 → fst (snd p)) )

  hasEquiv : ∀ {l} (A : I → Set l) → (comA : hasCom0 A) -> Set _
  hasEquiv A comA = (x : I) → isEquivFill (A `0) (A x) (\ p → fst (hasCom-hasCoe0 A comA x p))

  hasCom1 : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasCom1 A = (r' : I) 
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A z) 
             (b : A `1 [ α ↦ t `1 ]) 
            → A r' [ α ↦ t r' , (`1 == r') ↦ ⇒ (fst b) ]

  relCom1 : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  relCom1 A = (r' : I) 
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A z) 
             (b : A `1 [ α ↦ t `1 ]) 
            → A r' [ α ↦ t r' , (`1 == r') ↦ ⇒ (fst b) ]

  PathOverPathEquiv0 : ∀ {l1} {A : I → Set l1} {a0 : A `0} {a1 : A `1}
                    → (comA : hasCom0 A)
                    → Equiv (Path (A `1) (fst (hasCom-hasCoe0 A comA `1 a0)) a1) (PathO A a0 a1) 
  PathOverPathEquiv0 {A = A} wcomA = {!equivExtension {A = (x : I) → A x} {I → A `1}_ _ ? ? !}


  com1 : ∀ {l} (A : I → Set l) → (comA : relCom0 A) 
        → hasEquiv A (comA (\ x → x))
        → hasCom1 A
  com1 A comA e r' α t b = fst d , (\ pα →  fst (snd d) pα ∘ goal2r' pα ) , (\ r'=1 → {!snd (snd d)!}) where
    e' : (x : I) → Equiv _ _
    e' x = _ , (e x)
    
    b0 = back (e' _) (fst b)

    b0' =  e `1 (fst b)
              ⊥
              (\ x → abort x) 

    b0path =  fst (PathOverPathEquiv0 (comA (\ x → x)) ) (snd (fst b0')) 

    goal : ∀ pα → Path (A `0) (back (e' `1) (t `1 pα)) (back (e' `0) (t `0 pα))
    goal = {!!}

    fix =  comA (\ _ → `0) `1
                α (\ z pα → fst (goal pα) z)
                (back (e' _) (fst b) , (\ pα → ap (back (e' `1)) (snd b pα) ∘ fst (snd (goal pα)))) 

    c = comA (\ x → `0) r' α (\ z pα →  back (e' z) (t z pα) ) ( fst fix  , (\ pα →  fst (snd fix) pα ∘ ! (snd (snd (goal pα))) ))

    goal2 : (x : I) → α → A x
    goal2 = λ v v₁ → _

    goal2r' : ∀ pα → goal2 r' pα == t r' pα
    goal2r' = {!!}

    goal20 : ∀ pα → goal2 `0 pα == back (e' r') (t r' pα)
    goal20 = {!!}

    d = comA (\ x → x) r' α (\ z pα → goal2 z pα) (fst c , (\ pα → fst (snd c) pα ∘ goal20 pα ))

  -- ----------------------------------------------------------------------

  contr-extend-partial : {l : Level} {A : Set l} 
         → hasHFill0 A
         → Contractible A
         → ContractibleFill A
  contr-extend-partial hcomA cA α t = fst c , (\ pα → fst (snd c) pα ∘ ! (snd (snd (snd cA (t pα))))) where
    c = hcomA `1 α (\ z pα → fst (snd cA (t pα)) z) (fst cA , (λ pα → fst (snd (snd cA (t pα)))))


  hprop : {l : Level} (A : I → Set l)
        → ((x : I) → hasHFill0 (A x))
        → (r : I) (b : A r)
        → (a a' : HFiber (apply A r) b)
        → Path _ a a'
  hprop  A hcomA r b a a' = {!!} -- do you need 

  lemma : {l : Level} (A : I → Set l)
        → ((x : I) → hasHFill0 (A x))
        → hasWCoe A
        → {!!}
        → hasWCom A
  lemma A hcomA wcoeA e r b = contr-extend-partial {!OK!} ((wcoeA r b) , (\h → hprop A hcomA r b _ _))


  HFiber' : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  HFiber' f b = Σ \a → Path _ b (f a)

  isEquivFill' : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (ℓ₁ ⊔ l1 ⊔ l2)
  isEquivFill' A B f = (b : B) → ContractibleFill (HFiber' f b)

  hasWCom' :  ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasWCom' A = (r : I) → isEquivFill' ((r' : I) → A r') (A r) (apply A r)





{-
  com : ∀ {l} (A : I → Set l) → (comA : relCom0 A) 
        → (∀ r α {{cα : Cofib α}} t → isEquivFill ((A `0) [ α ↦ (t `0)]) (A r [ α ↦ t r ]) (\ b → fst (comA (\ x → x) r α t b), fst (snd (comA (\x → x)r α t b)) ))
        → hasWCom' A
  com A comA e r b α t = ((\ r' → fst (c r')) ,
                          (\ z →  fst (path z)) ,
                          {!(fst (snd (path `1)) (inr (inr id)))!} , {!! (fst (snd (path `0)) (inr (inl id)))!}) ,
                         (\ pα → pair= (λ= \ r' → fst (snd (c r')) pα) (pair= {!!} (pair= uip uip)) ) where

    fixb : ∀ z → _
    fixb z = comA (\ _ → r) z α (\ z pα → fst (snd (t pα)) z) (b , (\ pα → fst (snd (snd (t pα)))))

    fixbinv : ∀ z → _
    fixbinv z = comA (\ _ → r) `1
                     ((z == `0) ∨ (z == `1))
                     (\ w → ∨-elim01 _ (\ z=0 → fst (fixb w)) (\ z=1 → b ))
                     (fst (fixb `0) ,
                      ∨-elim01 _ (\ z=0 → id)
                                 (\ z=1 → snd (snd (fixb `0)) id))  

    center = (e r α (\ z pα → fst (t pα) z)) ((fst (fixb `1) , (\ pα → fst (snd (fixb `1)) pα ∘ ! (snd (snd (snd (t pα))))))) ⊥ (\ x → abort x)

    goback = fst (fst center)
    
    c : ∀ z → _
    c z =  comA (\ x → x) z α (\ z pα → fst (t pα) z ) goback

-- path : Path (apply A r (λ r' → fst (c r'))) (A r) b
-- have: fixb `1 to b
-- have: c r to fixb 1
    path : ∀ z → _
    path z = comA (\ _ → r) `1 (α ∨ ((z == `0) ∨ (z == `1)))
                  (\ z → case {!!}
                              (case01 (\ z=0 → fst (c r))
                                      (λ z=1 → fst (fixbinv z)))
                              {!!})
                  (fst (fst (snd (fst center)) z) , ∨-elim _
                                      {!!}
                                      (∨-elim01 _
                                                (\ z=0 → ap (\ H → fst (fst (snd (fst center)) H)) (! z=0) ∘ ! (ap fst (fst (snd (snd (fst center))))) )
                                                (\ z=1 → ap (\ H → fst (fst (snd (fst center)) H)) (! z=1) ∘ ap fst (! (snd (snd (snd (fst center))))) ∘ ! (fst (snd (fixbinv `0)) (inl id))   ))
                                      {!!}) 

    -- (\ z → fst (fst (snd (fst center)) z)) , {!!} ∘ ap fst (fst (snd (snd (fst center)))) , {!snd (fixb `1)!} ∘ ap fst (snd (snd (snd (fst center))))
-}

{-
  com : ∀ {l} (A : I → Set l)
        → (comA : relCom0 A)
          (comA1 : (r : I) → hasHFill1 (A r)) 
        → (∀ r α {{cα : Cofib α}} t → isEquivFill ((A `0) [ α ↦ (t `0)]) (A r [ α ↦ t r ]) (\ b → fst (comA (\ x → x) r α t b), fst (snd (comA (\x → x)r α t b)) ))
        → hasWCom' A
  com A comA hcomA1 e r b α t = ((\ r' → fst (c r')) ,
                          (\ z →  fst (path z)) ,
                          ! (snd (snd (fixb `0)) id)  ∘ ! (fst (snd (path `0)) (inr (inl id))) , ap fst (fst (snd (snd (fst center)))) ∘ ! (fst (snd (path `1)) (inr (inr id)))) ,
                         (\ pα → pair= (λ= \ r' → fst (snd (c r')) pα) (pair= (λ= \ z → fst (snd (path z)) (inl pα) ∘ {!!}) (pair= uip uip)) ) where

    fixb : ∀ z → _
    fixb z = comA (\ _ → r) z α (\ z pα → fst (snd (t pα)) z) (b , (\ pα → fst (snd (snd (t pα)))))

    center = (e r α (\ z pα → fst (t pα) z)) ((fst (fixb `1) , (\ pα → fst (snd (fixb `1)) pα ∘ ! (snd (snd (snd (t pα))))))) ⊥ (\ x → abort x)

    goback = fst (fst center)
    
    c : ∀ z → _
    c z =  comA (\ x → x) z α (\ z pα → fst (t pα) z ) goback

    path : ∀ z → _
    path z = hcomA1 r `0 (α ∨ ((z == `0) ∨ (z == `1)))
                  (\ w → case (λ pα →   fst (t pα) r )
                              (case01 (\ z=0 →  fst (fixb w) )
                                      (λ z=1 →  fst (fst (snd (fst center)) w) ))
                              (\ pα → ∨-elim01 _
                                               (\ z=0 →  {!fst (snd (fixb w)) pα!} )
                                               (\ z=1 → {!? ∘ ap (fst (snd (t pα))) (z=1)!})))
                  (fst (fixb `1) , ∨-elim _
                                      (\ pα → {! (fst (snd (fixb `1)) pα ∘ ! (snd (snd (snd (t pα))))) ∘ snd (snd (snd (t pα))) !})
                                      (∨-elim01 _
                                                (\ z=0 → id )
                                                (\ z=1 → ap fst (snd (snd (snd (fst center))))   ))
                                      (\ _ _ → uip)) 
-}

  hasWComRefl :  ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasWComRefl A = (r : I) 
                → (α : Set) {{_ : Cofib α}} 
                → (t : (z : I) → α → A z) 
                → (b : A r [ α ↦ t r ]) 
                → HFiber (apply A r) (fst b) [ α ↦ (\ pα → (\ z → t z pα) , ((\ _ → t r pα) , (id , snd b pα))) ]

  fst-transport-Path-left : {l1 l2 : Level} {A : Set l1} {B : Set l2} {a0 : A} {a1 : B → A}
                     {b b' : B} (p : b == b')
                     → (q : Path A (a1 b) a0)
                     → fst (transport (\ x → Path A (a1 x) a0) p q) == (fst q)
  fst-transport-Path-left id q = id

  wcom-from-com-retract : ∀ {l} (A : I → Set l)
        → (comA : relCom0 A)
        → (∀ r α {{cα : Cofib α}} t → (b : (A r [ α ↦ t r ]))
             → HFiber {A = ((A `0) [ α ↦ (t `0)])} {B = (A r [ α ↦ t r ])}
                       (\ b → fst (comA (\ x → x) r α t b), fst (snd (comA (\x → x)r α t b)) ) b)
        → hasWComRefl A
  wcom-from-com-retract A comA e r α t b = 
    ((\ r' → fst (c r')) ,
      (\ z → fst (fst (snd (center)) z)) , ap fst (fst (snd (snd (center)))) , ap fst (snd (snd (snd (center))))) ,
     (\ pα → pair= (λ= \ r' → fst (snd (c r')) pα) (pair= (λ= \ z → snd (fst (snd (center)) z) pα ∘ id ∘ ap= (fst-transport-Path-left {a1 = apply A r} (λ= (λ r' → fst (snd (c r')) pα)) ((λ _ → t r pα) , id , snd b pα))  ) (pair= uip uip)) ) where

    center = (e r α (\ z pα → (t z pα))) (b) 

    c : ∀ z → _
    c z =  comA (\ x → x) z α (\ z pα → (t z pα)) (fst center)


  coe-retract-equiv-strict : ∀ {l} (A : I → Set l)
        → (comA : relCom0 A)
        → (ret : (r : I) (b : A r) → A `0 [ r == `0 ↦ ⇒ b ])
        → (r : I) (b : A `0) → Path (A `0) (fst (ret r (fst (relCom-relCoe0 A comA (\ x → x) r b)))) b
  coe-retract-equiv-strict A comA ret r b = (\ z → fst (p z)) , ! (fst (snd (p `0)) (inl id)) , ! (fst (snd (p `1)) (inr id)) where
    p : ∀ z → _
    p z = comA (\ x → `0) r ((z == `0) ∨ (z == `1))
               (\ z → case01 (\ z=0 → fst (ret z (fst (relCom-relCoe0 A comA (\ x → x) z b))) ) (\ _ → b) )
               (b , ∨-elim01 _ (\ x=0 → ! (snd (relCom-relCoe0 A comA (λ x → x) `0 b) id) ∘ ! (snd (ret `0 _) id)) (\ _ → id))


  -- coe-retract-equiv-strict' : ∀ {l} (A : I → Set l)
  --       → (comA : relCom0 A)
  --       → (ret : (r : I) (b : A r) → A `0 [ r == `0 ↦ ⇒ b ])
  --       → (r : I) (b : A r) → Path (A r) (fst (relCom-relCoe0 A comA (\ x → x) r (fst (ret r b)))) b
  -- coe-retract-equiv-strict' A comA ret r b = (\ z → fst (p z)) , {! ! (fst (snd (p `0)) (inl id)) !} , {! ! (fst (snd (p `1)) (inr id)) !} where
  --   p : ∀ z → _
  --   p z = comA (\ x → r) `0 ((z == `0) ∨ (z == `1))
  --              (\ z → case01 {! (\ z=0 → (fst (relCom-relCoe0 A comA (\ x → x) r (fst (ret r b))))) !} 
  --                            (\ _ → b) )
  --              (b , {! ∨-elim01 _ (\ x=0 → ! (snd (relCom-relCoe0 A comA (λ x → x) `0 b) id) ∘ ! (snd (ret `0 _) id)) (\ _ → id) !})

  !Path : ∀ {l} {A : Set l} {a b : A} → hasHFill0 A → Path A a b → Path A b a
  !Path {a = a}{b} hA p = 
                (\ x → fst (c x)) , 
                 snd (snd p) ∘ ! (fst (snd (c `0)) (inl id))  , id ∘ ! (fst (snd (c `1)) (inr id))  where
    c : (x : I) → _
    c x = (hA `1 ((x == `0) ∨ (x == `1)) 
              (\ z → case (\ x=0 → fst p z) ((\ x=1 → a)) (\ p q → abort (iabort (q ∘ ! p))))
              (a , ∨-elim _ ( (\ x=0 → ((fst (snd p))) )) ( ((λ x=1 → id)) ) (\ _ _ → uip))) 

  ∘Path' : ∀ {l} {A : Set l} {a b c : A} → hasHFill0 A → Path A b c → Path A a b → Path A a c
  ∘Path' {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c `0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c `1)) (inr id))  where
    c : (x : I) → _
    c x = (hA `1 ((x == `0) ∨ (x == `1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (iabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip))) 

  inv-square : {l : Level} {A  : Set l} (hcomA : hasHFill0 A) 
               {a b c : A}
               (p : Path A a b)
               (q : Path A b c)
            → PathO (\ z → Path A (fst p z) c)
                    ( (\ z → fst (∘Path' hcomA q p) z) , ! (fst (snd p)) ∘ fst (snd (∘Path' hcomA q p))  , snd (snd (∘Path' hcomA q p)) )
                    ((\ z → fst q z) , ! (snd (snd p)) ∘ fst (snd q) , snd (snd q))
  inv-square = {!!}



  -- wcom-from-coe-equiv should be a corollary of this
  -- (though it doesn't need the whole thing)
  HFiber-equiv : {l1 l2 l3 : Level} {A : Set l1} {A' : Set l2} {B : Set l3}
               → hasHFill0 B
               → (f : A → B) (f' : A' → B) 
               → (e : Equiv A A')
               → ((a' : A') → Path B (f (back e a')) (f' a'))
               -- (a : A) → p (fst e a) : Path B (f (back e (fst e a))) (f' ((fst e) a))
               → ((b : B) → Equiv (HFiber f b) (HFiber f' b))
  HFiber-equiv hcomB f f' e c b = {! m , eqv !} where
  {-
    m : (HFiber f b) → (HFiber f' b)
    m h = fst e (fst h) , ∘Path' hcomB (snd h) (c (fst h))

    eqv : isEquivFill _ _ m
    eqv h α t = ((fst (fst u) , {!apPath f' (snd (fst u))!}) , (λ x → {!!} , {!!}) , {!!}) , {!!} where
      u =  snd e (fst h) α (\ pα → fst (fst (t pα)) , {!snd (fst (t pα))!}) 
  -}

  wcom-from-coe-equiv : ∀ {l} (A : I → Set l)
        → (comA : relCom0 A)
        → ((r : I) → isEquivFill (A `0) (A r) (\ z → fst (relCom-relCoe0 A comA (\ x → x) r z)))
        → hasWCom A
  wcom-from-coe-equiv A comA eq r b = Contractible-Retract {!really from 0 is enough!}
                                            (eq r b)
                                            ( (retract to from comp) ) where

       hcomA : (r : I) → hasHFill0 (A r)
       hcomA = {!!}

       -- A = A `0
       -- B = A r
       -- A' = (x : I) → A x
       -- f' = apply r
       -- f  = coe^0->r
       -- fst e : A → A' = \ x → coe^0 -> x
       -- back e : A' → A = apply to 0

       -- (a' : A') → Path B (f (back e a')) (f' a')
       path : (h : (r' : I) → A r')
            → (r' : I) → Path (A r') (fst (relCom-relCoe0 A comA (\ x → x) r' (h `0))) (h r') 
       path h r' = ((\ z → fst (c z) )) , ! (fst (snd (c `0)) (inl id)) ,  ! ((fst (snd (c `1))) (inr id)) where
         c : ∀ z → _
         c z = comA (\ x → x) r' ((z == `0) ∨ (z == `1))
                    (\ z → case01 (\ z=0 → fst (relCom-relCoe0 A comA (\ x → x) z (h `0)))
                                  (\ z=1 → h z))
                    (h `0 , ∨-elim01 _ (\ z=0 → ! (snd (relCom-relCoe0 A comA (\ x → x) `0 (h `0)) id))
                                       (\ _ → id))

       to : (HFiber {A = A `0} {B = A r} (λ z → fst (relCom-relCoe0 A comA (λ x → x) r z)) b)
          → (HFiber {A = (x : I) → A x} {B = A r} (apply A r) b)
       to h = (\ r' → fst (relCom-relCoe0 A comA (\ x → x) r' (fst h))) ,
              snd h

       from : (HFiber (apply A r) b) → (HFiber (λ z → fst (relCom-relCoe0 A comA (λ x → x) r z)) b)
       from h = fst h `0 , ∘Path' (hcomA r) (snd h) ((path (fst h) r))

       comp : (h : HFiber (apply A r) b) → Path (HFiber (apply A r) b) (to (from h)) h
       comp h = (\ z → (\ x → fst (path (fst h) x) z) , (\ y → fst (fst s z) y ) , fst (snd (fst s z)) , snd (snd (fst s z))) , 
                pair= (λ= \ r' →  fst (snd (path (fst h) r'))) ((pair= (λ= \ y → ap (\ q → fst q y) (fst (snd s)) ∘ {!OK!}) (pair= uip uip))) ,
                pair= (λ= \ z → snd (snd (path (fst h) z))) ((pair= (λ= \ y → ap (\ q → fst q y) (snd (snd s)) ∘ {!OK!}) (pair= uip uip)))  where
            s =  inv-square {A = A r} (hcomA r) (path (fst h) r) (snd h)   

       comp2 : (h : _) → Path _ (from (to h)) h
       comp2 h = ((\ z → fst h , {!snd h!})) , pair= (snd (relCom-relCoe0 A comA (\ x → x) `0 (fst h)) id) {!!} , pair= id {!!}

       -- ∘Path' (hcomA r) (snd h) (path (coe 0-> x (fst h)) r)
       -- snd h
       -- refl ((coe^0->r (fst h)))
       -- refl b
       

  -- need an hcom but seems OK
  com' : ∀ {l} (A : I → Set l)
          (comA : relCom A)
        → (∀ r α {{cα : Cofib α}} t → (b : (A r [ α ↦ t r ]))
             → HFiber {A = ((A `0) [ α ↦ (t `0)])} {B = (A r [ α ↦ t r ])}
                      (\ b → fst (comA (\ x → x) `0 r α t b), fst (snd (comA (\x → x) `0 r α t b)) ) b)
  com' A comA r α t b = (fst (comA (\ x → x) r `0 α t b) , fst (snd (comA (\ x → x) r `0 α t b)) ) ,
                        ((\ z → fst (comA (\ x → x) z r {{Cofib=}} α t (fst (comA (\ x → x) r z {{Cofib=}} α t b) , (\ pα → fst (snd (comA (λ x → x) r z {{Cofib=}} α t b)) pα))) , (\ pα → fst (snd (comA (λ x → x) z r {{Cofib=}} α t (fst (comA (λ x → x) r z {{Cofib=}} α t b) , (λ pα₁ → fst (snd (comA (λ x → x) r z {{Cofib=}} α t b)) pα₁)))) pα) ) ,
                         pair= {!!} (λ= \ _ → uip) , pair= {!!} (λ= \ _ → uip)) where
     postulate
       Cofib= : {z w : I} → Cofib (z == w)
