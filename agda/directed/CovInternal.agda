{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Proposition
open import Cofibs
open import Kan
open import Path
open import Interval
open import universe.Sigma
open import Glue
open import directed.Covariant
open import Glue-Weak

module Directed.CovInternal where

  -- an older version of relCov for funglue that is slightly sharper:
  -- to show that is covariant, 
  -- it is not necessary to assume that the funglue pieces are in UKan,
  -- nor is it necessary for the universe UCov to exist.
  --
  -- not used in the rest of the development

  private
  
    dua-α' : 𝟚 → Set
    dua-α' x = ((x == ``0) ∨ (x == ``1))

    module _ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) where
      dua-α = dua-α' x
    
      dua-T  : dua-α → Set l1
      dua-T = (cased01 (\ _ → A) (\ _ → B))
    
      dua-B = B
    
      dua-f : (p : dua-α) → dua-T p → dua-B 
      dua-f = (∨-elimd01 _ (\ _ → f) (\ _ x → x) )
    
    dua-α-constant : {l : Level} {Γ : Set l}
                     (θ : Γ → 𝟚) (p : I → Γ)
                   → Σ \ (α' : Set) → (x : I) → (dua-α' (θ (p x))) == α'
    dua-α-constant θ p = dua-α' (fst pick) , ((\ x → ap dua-α' (ap= (snd pick)))) where
      pick = (𝟚-Inull (θ o p))
    
    preduafun : ∀ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) → Set l1
    preduafun x A B f = Glue (dua-α x A B f) (dua-T x A B f) (dua-B x A B f) (dua-f x A B f)
    
    duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
             (x : Γ → 𝟚) (A : Γ → Set l2) (B : Γ → Set l2)
             (f : (θ : Γ) → A θ → B θ)
             → Γ → Set l2
    duaF {Γ = Γ} x A B f θ = preduafun (x θ) (A θ) (B θ) (f θ)
    
    -- this proof seems like it should generalize to
    -- x ⊢ Glue (α(x) ∨ β(x) ↦ f ∨ g) where
    --   (α ``1) → α y for all y
    --   g is an equivalence
    
    
    -- **********************************************************************
    -- main idea is here: covariance of function glueing
    
    relCov-duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
                 (x : Γ → 𝟚)
                 (A B : Γ → Set l2)
                 (f : (θ : Γ) → A θ → B θ)
                 → relCov A
                 → relCov B
                 → relCov1 (duaF x A B f)
    relCov-duaF x A B f dcomA dcomB p α t b =
      glue _ _ _ _
               (∨-elimd01 _ (\ xp1=0  → fst (tleft xp1=0))
                            (\ xp1=1  → fst (tright-fill ``1)))
               (fst b' ,
                ∨-elimd01 _ (\ xp1=0 → fst (snd b') (inl (inr xp1=0)))
                            (\ xp1=1 → fst (snd b') (inr xp1=1))) ,
               (\ pα → glue-cong _ _ _ _ _ _
                            (λ= (∨-elimd01 _
                                   (\ xp1=0 → ! (tleft-α pα xp1=0))
                                   (\ xp1=1 →  fst (snd (tright-fill ``1)) pα ∘ unglue-α (t ``1 pα) (inr xp1=1)  )))
                            (fst (snd b') (inl (inl pα))) ∘ Glueη (t ``1 pα)) where
      
      back-in-time : ((x o p) ``1 == ``0) → (y : _) → (x o p) y == ``0
      back-in-time eq y = transport (\ h → (x o p) y ≤ h) eq (dimonotonicity≤ (x o p) y ``1 id) 
    
      -- when the result in is in A, compose in A 
      tleft-fill : (y : 𝟚) (xp1=0 : x (p ``1) == ``0) → _
      tleft-fill y xp1=0 =
        dcomA p y α
               (\ z pα → coe (Glue-α _ _ _ _ (inl (back-in-time xp1=0 z))) (t z pα))
               (coe (Glue-α _ _ _ _ (inl (back-in-time xp1=0 ``0 ))) (fst b) ,
                   (λ pα → ((ap (coe (Glue-α _ _ _ _ (inl _))) (snd b pα)) ∘ ap (\ h → (coe (Glue-α _ _ _ _ (inl h)) (t ``0 pα))) uip)))
    
      tleft = tleft-fill ``1
    
      -- on α, the composite in A is just t 1
      tleft-α : (pα : α) → (xp1=0 : x(p ``1) == ``0) →
             fst (tleft xp1=0) == coe (Glue-α _ _ _ _ (inl xp1=0)) (t ``1 pα)
      tleft-α pα xp1 = (ap (\ h → coe (Glue-α _ _ _ _ (inl h)) (t ``1 pα)) uip) ∘ ! (fst (snd (tleft xp1)) pα)
    
      tright-fill : ∀ y → _
      tright-fill y = dcomB p y
                          (α)
                          (\ z pα → unglue (t z pα))
                          (unglue (fst b) ,
                                  (\ pα → ap unglue (snd b pα)))
    
      -- unglue everyone to B and compose there, agreeing with f (tleft-fill) on xp1 = 0
      b' : Σ \ (b' : B (p ``1)) → _
      b' = dcomB p ``1
                 ((α ∨ (x (p ``1) == ``0)) ∨ (x (p ``1) == ``1))
                 ((\ z → case (case (\ pα →  unglue (t z pα))
                                 (\ xp1=0 → f (p z) (fst (tleft-fill z xp1=0)))
                                 (\ pα xp1=0 → ap (f (p z)) (fst (snd (tleft-fill z xp1=0)) pα) ∘ ! (unglue-α (t z pα) (inl (back-in-time xp1=0 z)))  ))
                              (\ xp1=1 → fst (tright-fill z))
                              (∨-elim _ (\ pα xp1=1 → fst (snd (tright-fill z)) pα )
                                        (\ p q → abort (diabort (q ∘ ! p)) )
                                        (λ _ _ → λ= \ _ → uip))))
                 (unglue (fst b) ,
                   ∨-elim _ 
                   (∨-elim _ (\ pα → ap unglue (snd b pα))
                            (\ xp1=0 → unglue-α (fst b) (inl (back-in-time xp1=0 ``0 )) ∘ ! (ap (f (p ``0)) (snd (snd (tleft-fill ``0 xp1=0)) id)) )
                            (\ _ _ → uip) )
                   (\ xp1=1 → ! (snd (snd (tright-fill ``0)) id))
                   (\ _ _ → uip))
    
    dcom-dua-restricts-0 : ∀ {l1 l2 : Level} {Γ : Set l1}
                         (x : Γ → 𝟚)
                         (A B : Γ → Set l2)
                         (f : (θ : Γ) → A θ → B θ)
                         (dcomA : relCov A)
                         (dcomB : relCov B)
                         → (p : 𝟚 → Γ)
                         → (xpy=0 : (y : 𝟚) → x (p y) == ``0)
                         → ∀ α {{cα : Cofib α}} t b 
                         → coe (Glue-α _ _ _ _ (inl (xpy=0 ``1))) (fst (relCov-duaF x A B f dcomA dcomB p α t b)) ==
                               (fst (dcomA p ``1 α
                                           (\ z pα →  coe (Glue-α _ _ _ _ (inl (xpy=0 z))) (t z pα))
                                           (coe (Glue-α _ _ _ _ (inl (xpy=0 ``0))) (fst b) ,
                                            (\ pα → ap (\ x → coe (Glue-α _ _ _ _ (inl (xpy=0 ``0))) x) (snd b pα)))))    
    dcom-dua-restricts-0 x A B f dcomA dcomB p xpy=0 α t b =
      dcom= A dcomA p
            (λ= \ z → λ= \ pα → ap (\ H → (coe (Glue-α ((x (p z) == ``0) ∨ (x (p z) == ``1)) (dua-T (x (p z)) (A (p z)) (B (p z)) (f (p z))) (dua-B (x (p z)) (A (p z)) (B (p z)) (f (p z))) (dua-f (x (p z)) (A (p z)) (B (p z)) (f (p z))) (inl H)) (t z pα))) uip)
            (ap (\ H → coe (Glue-α (((x o p) ``0 == ``0) ∨ (x (p ``0) == ``1)) (dua-T (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (dua-B (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (dua-f (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (inl H)) (fst b)) uip) ∘
      (glue-α _ _ (inl (xpy=0 ``1)))
    
    dcom-dua-restricts-1 : ∀ {l1 l2 : Level} {Γ : Set l1}
                         (x : Γ → 𝟚)
                         (A B : Γ → Set l2)
                         (f : (θ : Γ) → A θ → B θ)
                         (dcomA : relCov A)
                         (dcomB : relCov B)
                         → (p : 𝟚 → Γ)
                         → (xpy=1 : (y : 𝟚) → x (p y) == ``1)
                         → ∀ α {{cα : Cofib α}} t b 
                         → coe (Glue-α _ _ _ _ (inr (xpy=1 ``1))) (fst (relCov-duaF x A B f dcomA dcomB p α t b)) ==
                               (fst (dcomB p ``1 α
                                          (\ z pα →  coe (Glue-α _ _ _ _ (inr (xpy=1 z))) (t z pα))
                                          (coe (Glue-α _ _ _ _ (inr (xpy=1 ``0))) (fst b) ,
                                               (\ pα → ap (\ x → coe (Glue-α _ _ _ _ (inr (xpy=1 ``0))) x) (snd b pα)))))    
    dcom-dua-restricts-1 x A B f dcomA dcomB p xpy=1 α t b =
      dcom= B dcomB p (λ= \ z → λ= \ pα → ! (unglue-α (t z pα) (inr (xpy=1 z))) )
                      (! (unglue-α (fst b) (inr (xpy=1 ``0))))
      ∘ (glue-α _ _ (inr (xpy=1 ``1)))
  

    -- ----------------------------------------------------------------------
    -- misc stuff, not really used
    dua-identity : ∀ {l : Level} {A : Set l} {x : 𝟚} → QEquiv (preduafun x A A (\ x → x)) A -- in fact this is an isomorphism
    dua-identity =
      unglue ,
      ((\ a → glue _ _ _ _ (∨-elimd01 _ (\ _ → a) (\ _ → a)) (a , (∨-elimd01 _ (\ _ → id) (\ _ → id)))) ,
       (\ g → (\ _ → g) , glue-cong _ _ _ _ _ _ (λ= (∨-elimd01 _ (\x → unglue-α g (inl x)) (\ y → unglue-α g (inr y)))) id ∘ Glueη g , id) ,
       (\ a → (\ _ → a) , ! (Glueβ _ _) , id))  
  
    -- argument for monotonicity being necessary:
    -- reversal + preduafun covariant is contradictory
    no-reverse : ({l1 : Level} (A : Set l1) (B : Set l1) (f : A → B)
           (p : 𝟚 → 𝟚) → (preduafun (p ``0) A B f) → preduafun (p ``1) A B f )
        → (1- : 𝟚 → 𝟚)
        → (1- ``0 == ``1)
        → (1- ``1 == ``0)
        → ⊥{lzero}
    no-reverse comdua 1- p q = coe (Glue-α _ _ _ _ (inl q)) (comdua' 1- (coe (! (Glue-α _ _ _ _ (inr p))) _))  where
      comdua' = comdua ⊥ (Unit) (\ _ → <>) 







