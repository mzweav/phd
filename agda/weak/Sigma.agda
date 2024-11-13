{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import weak.Kan
open import weak.Cofibs
open import weak.Equiv
open import weak.Pi
open import weak.Retraction
open import weak.Path

module weak.Sigma where

  hcomΣ : ∀ {l2 l3 : Level} {A : Set l2} {B : A → Set l3}
        → hasHFill A
        → relFill B
        → hasHFill (Σ B)
  hcomΣ {A = A} {B} hcomA comB r r' r01 α t b = (fst (fA r') , fst fB) , (\ pα → pair= (fst (snd (fA r')) pα) (fst (snd fB) pα)) , (\ {id → pair= (snd (snd (fA r)) id ) (snd (snd fB) id)}) where
    fA : (z : I) → _
    fA z = hcomA r z r01 α (\ z pα → fst (t z pα)) (fst (fst b) , (\ pα → ap fst (snd b pα)))

    fB = comB (\ x → (fst (fA x))) r r' r01 α
              (\ z pα → transport B (fst (snd (fA z)) pα) (snd (t z pα)))
              (transport B (snd (snd (fA r)) id) (snd (fst b)) ,
                (\ pα → het-to-hom {!apd snd ((snd b) pα)!}))
  
  Σtrivial : ∀ {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
           → ContractibleFill A
           → ((a : A) → ContractibleFill (B a))
           → ContractibleFill (Σ B)
  Σtrivial {B = B} cA cB α t = (fst a , fst b) , (\ pα → pair= (snd a pα) (snd b pα)) where
    a = cA α (\ pα → fst (t pα))
    b = cB (fst a) α ((\ pα → transport B (snd a pα) (snd (t pα))))

  Σcong : ∀ {l1 l2 : Level} {A A' : Set l1} {B : A → Set l2} {B' : A' → Set l2}
        → hasHFill A
        → hasHFill A'
        → relFill B
        → relWCom B'
        → (e : Equiv A A')
        → ((a : A) → Equiv (B a) (B' (fst e a))) 
        → Equiv (Σ \ (x : A) → B x) (Σ \ (x : A') → B' x)
  Σcong {A = A} {A' = A'} {B = B} {B' = B'} hcomA hcomA' comB wcomB' eA eB =
    map ,
    (\ ab' → Contractible-Retract (hcomHFiberMap ab')
                                  (Σtrivial (snd eA (fst ab')) (\ a → snd (extend (fst ab') a) (snd ab')))
                                  (ret (fst ab') (snd ab')) ) where

    comB' = relWCom-relFill B' wcomB'

    map : Σ B → Σ B'
    map = (\ p → fst eA (fst p) , fst (eB _) (snd p))

    hcomHFiberMap : (ab' : _) → hasHFill (HFiber map ab')
    hcomHFiberMap ab' = hcomΣ (hcomΣ hcomA comB) (comPath-endpoints map (\ _ → ab') (hcomΣ hcomA' comB'))

    extend : (a' : A') → (ha : HFiber (fst eA) a') → Equiv (B (fst ha)) (B' a')
    extend a' ha = compose-equiv (relFill-hasHFill B' comB' a')
                                 (eB (fst ha))
                                 (transportEquiv B' wcomB' (snd ha))

    ret : (a' : A') (b' : B' a')
         → Retraction (Σ \ (ha : HFiber (fst eA) a') →
                           HFiber {A = B (fst ha)} {B = B' a'} (fst (extend a' ha)) b'   )
                      (HFiber map (a' , b'))
    ret a' b' = retract (λ h → ((fst (fst h)) , (fst (snd h))) ,
                               (\ z → (fst (snd (fst h)) z) , fst (fromone h) z) ,  
                               pair= (fst (snd (snd (fst h)))) (ap= (transport-inv-2 B' (fst (snd (snd (fst h))))) ∘ ap (transport B' (fst (snd (snd (fst h))))) (fst (snd (fromone h)))) ,
                               pair= (snd (snd (snd (fst h)))) ((ap= (transport-inv-2 B' (snd (snd (snd (fst h))))) ∘ ap (transport B' (snd (snd (snd (fst h))))) (snd (snd (fromone h))))))
                        (\ q → (fst (fst q) , (\ z → fst ((fst (snd q)) z)) , ap fst (fst (snd (snd q))) , ap fst (snd (snd (snd q)))) ,
                               (snd (fst q)) , {! apdPath snd (snd q) !})
                               -- snd (fst (snd q) z)
                        {!!} where
        fromone : ∀ (h : Σ (λ ha → HFiber (fst (extend a' ha)) b')) → _
        fromone h = (back (PathOverPathEquiv {A = \z → B' (fst (snd (fst h)) z)} {transport B' (! (fst (snd (snd (fst h))))) (fst (eB _) (fst (snd h)))}{transport B' (! (snd (snd (snd (fst h))))) b'} (wcomPre (\ x → (fst (snd (fst h)) x)) B' wcomB'))
                          ((\ z → transport B' (! (snd (snd (snd (fst h))))) (fst (snd (snd h)) z)) ,
                          ({!nonsense!} ∘ ap= (transport-inv B' (snd (snd (snd (fst h)))))) ∘ ap (transport B' (! (snd (snd (snd (fst h)))))) (fst (snd (snd (snd h)))) ,
                           ap (transport B' (! (snd (snd (snd (fst h)))))) (snd (snd (snd (snd h))))))

  Σcommutei : ∀ {l2 l3 : Level}
               (A : I → Set l2)
               (B : Σ A → Set l3)
           → isIso ((x : I) → Σ \ (a : A x) → B (x , a))
                   (Σ \ (f : (x : I) → A x) →
                        (x : I) → B (x , f x) )
                   (\ f → (\ x → fst (f x)) , (\ x → snd (f x)))
  Σcommutei A B = iso (\ h x → fst h x , snd h x) (\ p → id) (\ q → id)

  Σcommutei' : ∀ {l2 l3 : Level}
               (A : I → Set l2)
               (B : Σ A → Set l3)
           → isIso (Σ \ (f : (x : I) → A x) →
                        (x : I) → B (x , f x) )
                   ((x : I) → Σ \ (a : A x) → B (x , a))
                   (\ h x → fst h x , snd h x)
  Σcommutei' A B = iso (\ f → (\ x → fst (f x)) , (\ x → snd (f x))) (\ p → id) (\ q → id)

  Σcommute : ∀ {l2 l3 : Level}
               (A : I → Set l2) → relFill A
             → (B : Σ A → Set l3) → relFill B
           → Equiv ((x : I) → Σ \ (a : A x) → B (x , a))
                   (Σ \ (f : (x : I) → A x) → (x : I) → B (x , f x) )
  Σcommute A comA B comB = (\ f → (\ x → fst (f x)) , (\ x → snd (f x))) , isIso-isEquiv _ _ _ (hcomΠ I _ (\ x → hcomΣ ( (relFill-hasHFill A comA x) ) ( (fillPre (\ a → x , a) B comB) )) ) (hcomΣ (hcomΠ _ _ (relFill-hasHFill A comA)) ( comΠrange (\ q → B (snd q , fst q (snd q))) ( (fillPre (\ q → snd q , fst q (snd q)) B comB) ) )) (Σcommutei A B)

  hascomΣ : ∀ {l1 l2 : Level} {A : I → Set l2} {B : Σ A → Set l1}
        → relWCom A
        → relWCom B
        → hasWCom (\ x → Σ \ (a : A x) → B (x , a))
  hascomΣ {A = A} {B = B} wcomA wcomB r = snd e where
      e = compose-equiv (hcomΣ (relCom-hasHFill A (relWCom-relCom A wcomA) r)
                                 ( (fillPre (\ x → (r , x)) B (relWCom-relFill B wcomB)) ))
         ( Σcommute A (relWCom-relFill A wcomA) B (relWCom-relFill B wcomB)  )
         (Σcong ((hcomΠ I (A) (relCom-hasHFill (A) ((relWCom-relCom A wcomA)))))
                (relCom-hasHFill (A) ((relWCom-relCom A wcomA)) r)
                (comΠrange {A = I} (\ q → B ((snd q) , fst q (snd q))) ( fillPre (λ q → ((snd q) , fst q (snd q))) B (relWCom-relFill B wcomB) ) )
                (  wcomPre (\ v → (r , v)) B wcomB  )
                (_ , wcomA (\x → x) r )
                ( (\ a → _ , wcomB (\ x → x , a x) r) ))


  hfiber-domain-strict : ∀ {l : Level} {A B C : Set l}
                       → (f : A → C) (g : B → C)
                       → (c : C)
                       → (h : A → B) → (g o h) == f
                       → HFiber f c
                       → HFiber g c
  hfiber-domain-strict f g c h X hf = h(fst hf) , {!snd hf!}

  hfiber-Σ : ∀ {l1 l2 l3 l4 : Level} {A : Set l1} {A' : Set l4} {B : A → Set l3} {B' : A' → Set l2}
           → (f : Equiv A A')
           → (g : (x : A) → B x → B' (fst f x))
           → (a' : A') (b' : B' a')
           → HFiber (fst f) a'
           → HFiber (g (back f a')) {!transportPath  !}
           → HFiber (\ (p : Σ B) → (fst f (fst p) , g (fst p) (snd p))) (a' , b')
  hfiber-Σ f g X a' b' = {!!}

  Iso' : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  Iso' A B = Σ \ f → isIso A B f
   
  hfiber-iso : ∀ {l : Level} {A B C : Set l}
              → (f : A → C) 
              → (h : Iso' B A)
              → (c : C)
              → Iso' (HFiber (f o fst h) c) (HFiber f c)
  hfiber-iso f g c = {!!}

  contr-iso : ∀ {l : Level} {A B : Set l} → ContractibleFill A → Iso' A B → ContractibleFill B
  contr-iso = {!!}

  whcomΣ : ∀ {l1 l2 l3 : Level} {A : Set l2} {B : A → Set l3}
        → hasWHCom A
        → relWCom B
        → hasWHCom (Σ B)
  whcomΣ {A = A} {B} hcomA comB r b = contr-iso {!!} (hfiber-iso _ (_ , Σcommutei' (\ _ → A) (\ x → B (snd x)) ) _ )   where
    hA = hcomA r (fst b)
    fixb = {!!}
    hB = comB (fst (fst (hA ⊥ (\ x → abort x)))) r (  fixb )

    foo : (HFiber (λ f → f r) b)
    foo = {!!}

  wcomΣ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3}
        → relWCom A
        → relWCom B
        → relWCoe (\ γ → Σ \ (x : A γ) → B (γ , x))
  wcomΣ {A = A} {B = B} wcomA wcomB p r (a , b) =
    hfiber-domain-strict {A = (Σ \ (f : (x : _) → A (p x)) → (x : _) → B (p x , f x) )}
                         (\ p → fst p r , snd p r) _ _
                         (\ p x → fst p x , snd p x)
                         id
                         (hfiber-Σ (_ , wcomA p r ) (\ f g → g r) _ _ hA hB ) where
    hA =  fst ((wcomA p r) (a) ⊥ (\ x → abort x))

    fixb = {!comB !} 

    hB =  fst (wcomB (\ x → p x , fst hA x) r fixb ⊥ (\ x → abort x))

  
    
