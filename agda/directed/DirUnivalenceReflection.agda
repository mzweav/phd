{-# OPTIONS --rewriting  #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import Cofibs
open import Kan
open import Path
open import Equiv
open import Interval
open import Glue
open import universe.Universe
open import universe.Path
open import universe.LibFlat
open import directed.DirInterval
open import directed.Covariant
open import directed.Segal
open import directed.Covariant-is-Fibrant
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import directed.universe.FunGlue
open import directed.universe.FunGlueKan
open import directed.universe.Hom

module directed.DirUnivalenceReflection where

  open Layered

  duahom :  {@♭ l : Level} (A B : UCov l) → (f : ElC A → ElC B) → Hom (UCov l) A B
  duahom A B f = (λ i → FunGlueUCov (fungluedata A B f i)) ,
                        FunGlueUCov0 (fungluedata A B f ``0) id , 
                        FunGlueUCov1 (fungluedata A B f ``1) id

  abstract
    -- FIXME: why didn't this need to change with aligning the Kan operation for funglue ?
    duaβ : {@♭ l : Level} (A B : UCov l) → (f : ElC A → ElC B) → Path _ f (dcoe A B (duahom A B f))
    duaβ {l} A B f = (λ i a → coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id)) (fst (path a i))) , patheq0 , patheq1 where
  
      p : 𝟚 → Set l
      p = ElC o (fst (duahom A B f))
  
      covp : relCov p
      covp = dcomEl' (fst (duahom A B f))
  
      patht : (a : ElC A) (j : I) (i : 𝟚)  → (j == `0) ∨ (j == `1) → (p i)
      patht a j i = ∨-elim01 _ (λ _ → glue ((i == ``0) ∨ (i == ``1)) _ _ _ (∨-elimd01 _ (λ _ → a) (λ _ → f a)) (f a , ∨-elimd01 _ (λ _ → id) (λ _ → id)))
                               (λ _ → (fst (dcoetoi (fst (duahom A B f)) i (coe (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) a))))
  
      path : (a : ElC A) (j : I) → _
      path a j = covp (λ x → x) ``1 ((j == `0) ∨ (j == `1)) (patht a j)
                      (glue _ _ _ _ (∨-elimd01 _ (λ _ → a) (λ _ → f a)) (f a , ∨-elimd01 _ (λ _ → id) (λ _ → id)) -- is just   coe (! (ap ElC (FunGlueUCov0 (fungluedata A B f ``0) id))) a
                      , ∨-elim01 _ (λ _ → id)
                                   (λ _ →  ! (move-transport-right (λ X → X) (Glue-α _ _ _ _ (inl id)) (glue-α _ _ (inl id)) )
                                           ∘ (het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (! (Glue-α _ _ _ _ (inl id))) {a}))
                                             (transport-=h (λ X → X) (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) {a})))
                                           ∘ ! (snd (snd (dcoetoi (fst (duahom A B f)) ``0 (coe (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) a))) id)))
  
      patheq0 : _
      patheq0 = λ= λ a → het-to-hom (_∘h_ (_∘h_ (transport-=h (λ X → X) (! (Glue-α _ _ _ _ (inr id))))
                                    (hom-to-het ((move-transport-right (λ X → X) (Glue-α _ _ _ _ (inr id)) (glue-α _ _ (inr id))))))
                                    (transport-=h (λ X → X) (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))))
                         ∘ ! (ap (coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))) (fst (snd (path a `0)) (inl id)))
  
      patheq1 : _
      patheq1 = λ= λ a → ! (ap (coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))) (fst (snd (path a `1)) (inr id)))

    duaηfun' : {@♭ l : Level} → (A : 𝟚 → UCov l) → (x : 𝟚) → ElC (A x) → ElC (fst (duahom (A ``0) (A ``1) (dcoe𝟚U A)) x)
    duaηfun' A x a = glue _ _ _ _ (∨-elimd01 _
                                            (\ x=0 → transport (ElC o A) x=0 a)
                                            (\ x=1 → transport (ElC o A) x=1 a))
                                            (fst useh ,
                                            ∨-elimd01 _ (\ x=0 → fst (snd (snd useh)) x=0 ∘ pf x a x=0) (snd (snd (snd useh)))) where
      -- FIXME: make homogEl : hasHomog El a lemma
      h = relCov-relHomog' (ElC o A) (dcomEl' A)
  
      useh = (h (\ x → x) x ⊥ (\ z x → abort x) (a , (\ x → abort x)))
  
      pf : (x : 𝟚) (a : ElC (A x)) → (x=0 : x == ``0) →
           dcoe𝟚U A (transport (λ x₁ → El (ElCov (A x₁))) x=0 a)  ==
           fst
             (dcomEl (A o (λ x₁ → x₁)) ``1 ⊥ (λ z x₁ → abort x₁)
              (transport
               (λ x₁ → ((ElC o A) o (λ x₂ → x₂)) x₁ [ ⊥ ↦ (λ x₂ → abort x₂) ]) x=0
               (a , (λ x₁ → abort x₁))))
      pf .``0 a id = id

    duaηfun-fix-type : {@♭ l : Level} → (A B : UCov l) → (p : Hom _ A B) → (i : 𝟚) →
                        Glue (dua-α (fungluedatakan (ElCov (fst p ``0)) (ElCov (fst p ``1)) (dcoe𝟚U (fst p)) i))
                             (dua-T (fungluedatakan (ElCov (fst p ``0)) (ElCov (fst p ``1)) (dcoe𝟚U (fst p)) i))
                             (dua-B (fungluedatakan (ElCov (fst p ``0)) (ElCov (fst p ``1)) (dcoe𝟚U (fst p)) i))
                             (dua-f (fungluedatakan (ElCov (fst p ``0)) (ElCov (fst p ``1)) (dcoe𝟚U (fst p)) i))
      == ElC (fst (duahom A B (dcoe A B p)) i)
    duaηfun-fix-type A B p i = ( ap (\ X → Glue ((i == ``0) ∨ (i == ``1)) (fst (fst X)) (snd (fst X)) (snd X))
                                                 (pair= (pair= eq1 eq2)
                                                        (het-to-hom (_∘h_ ( apdo (\ Z → dua-f Z)
                                                                                 (fungluedatakan=h (ap ElCov (fst (snd p))) ((ap ElCov (snd (snd p))))
                                                                                                   (λ=o (\ x x' x=hx' →
                                                                                                    _∘h_ (!h (transport-=h (\X → X) (ap (λ x₁ → El (ElCov x₁)) (snd (snd p))) ))
                                                                                                         ( dcomEl=h {A = fst p} id ``1 ⊥ {{Cofib⊥}} hid (
                                                                                                                    _∘h_ ( !h (transport-=h (\ X → X) (ap ElC (! (fst (snd p))))))
                                                                                                                          x=hx') ) ))
                                                                                                   id))
                                                                          (transport-=h (λ v → (u : (i == ``0) ∨ (i == ``1)) → fst v u → snd v) (pair= eq1 eq2))))) ) where
      eq1 = (ap (λ X → λ z → El (cased01 (λ _ → ElCov (fst X)) (λ _ → ElCov (snd X)) z)) (pair= ((fst (snd p))) ((snd (snd p)) ∘ (ap= (transport-constant (fst (snd p)))))))
      eq2 = (ap ElC (snd (snd p)) ∘ ap= (transport-constant eq1))

    duaηfun : {@♭ l : Level} → (A B : UCov l) → (p : Hom _ A B) → (i : 𝟚) → ElC ((fst p) i) → ElC (fst (duahom A B (dcoe A B p)) i)
    duaηfun {l} A B p i x = coe ( (duaηfun-fix-type A B p i) ) (duaηfun' (fst p) i x)
                                         
    ηeq0 : {@♭ l : Level} (A B : UCov l) → (p : Hom _ A B) →
          (duaηfun A B p ``0) == coe (ap (λ X → ((ElC (fst p ``0)) → X)) (! (Glue-α _ _ _ _ (inl id)) ∘ ap ElC (fst (snd p)))) (λ x → x) 
    ηeq0 {l} A B p = het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (ap (λ X → El (ElCov (fst p ``0)) → X)
                               (!
                                (Glue-α _ _ _ _ (inl id))
                                ∘ ap ElC (fst (snd p))))))
                           (λ=o λ a a' aeq → _∘h_ (_∘h_ aeq
                                                  (_∘h_ (hom-to-het (glue-α _ _ (inl id))) (!h (transport-=h (λ X → X) (Glue-α _ _ _ _ (inl id))))))
                                                  (transport-=h (λ X → X)
                                                                (duaηfun-fix-type A B p ``0))))
  
    ηeq1 : {@♭ l : Level} (A B : UCov l) → (p : Hom _ A B) →
          (duaηfun A B p ``1) == coe (ap (λ X → ((ElC (fst p ``1)) → X)) (! (Glue-α _ _ _ _ (inr id)) ∘ ap ElC (snd (snd p)))) (λ x → x)
    ηeq1 {l} A B p = het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (ap (λ X → El (ElCov (fst p ``1)) → X)
                               (!
                                (Glue-α _ _ _ _ (inr id))
                                ∘ ap ElC (snd (snd p))))))
                           (λ=o λ b b' beq → _∘h_ (_∘h_ beq
                                                  (_∘h_ (hom-to-het (glue-α _ _ (inr id))) (!h (transport-=h (λ X → X) (Glue-α _ _ _ _ (inr id))))))
                                                  ((transport-=h (λ X → X) ((duaηfun-fix-type A B p ``1))))))


    {- This is the interesting piece of duaη at dimension 1: in
       particular, as the glue type erases all of the data "in
       the middle" of the morphism (as it is shifted into the 
       function component of the glue type), this shows that
       nothing is actually lost by only retaining the starting
       point. -}
    ηeqCheck : {@♭ l : Level} → (p : 𝟚 → UCov l) →
               (q : (i : 𝟚) → ElC (p i)) →
               Path _ q (λ i → fst (dcoetoi p i (q ``0)))
    ηeqCheck p q = (λ j i → fst (fill i j))
                  , λ= (λ z → ! (fst (snd (fill z `0)) (inl id)))
                  , λ= (λ z → ! (fst (snd (fill z `1)) (inr id))) where 

      qfill : ∀ z → _
      qfill z = dcoetoi p z (q ``0)

      fill : ∀ i (j : I) → _
      fill i j = dcomEl p i ((j == `0) ∨ (j == `1))
                        (λ z → case01 (λ _ → q z)
                                      (λ _ → fst (qfill z)))
                        (q ``0
                        , ∨-elim01 _ (λ _ → id)
                                     (λ _ → ! (snd (snd (qfill ``0)) id))) 

    ηeqCheck2 : {@♭ l : Level} → (p : 𝟚 → UCov l) →
                (q : (j i : 𝟚) → ElC (p i)) →
                Path _ q (λ j i → fst (dcoetoi p i (q j ``0)))
    ηeqCheck2 p q = (λ x j → fst (ηeqCheck p (λ i → q j i)) x)
                  , (λ= λ j →  fst (snd (ηeqCheck p (λ i → q j i))))
                  , (λ= λ j →  snd (snd (ηeqCheck p (λ i → q j i))))

    {- IDEA: also fix so that everything is triangulated into simplices -}
    
    ηeqCheck2' : {@♭ l : Level} → (p : 𝟚 → UCov l) →
                 (q : (i j : 𝟚) → ElC (p (i ⊓ j))) →
                 Path _ q (λ i j → fst (dcoetoi p (i ⊓ j) (q ``0 j)))
    ηeqCheck2' p q = (λ x i j →  fst (fill i j x))
                   , (λ= λ i → λ= λ j → ! (fst (snd (fill i j `0)) (inl id)))
                   , (λ= λ i → λ= λ j → ! (fst (snd (fill i j `1)) (inr id))) where 

      qfill : ∀ i j → _
      qfill i j = dcoetoi p (i ⊓ j) (q ``0 j)

      fill : ∀ i j (x : I) → _
      fill i j x = dcomEl (λ z → p (z ⊓ j)) i ((x == `0) ∨ (x == `1))
                          (λ z → case01 (λ _ → q z j)
                                        (λ _ → fst (qfill z j)))
                          (q ``0 j
                          , ∨-elim01 _ (λ _ → id)
                                       (λ _ → ! (snd (snd (qfill ``0 j)) id))) 

    
{-
    ηeqInt : {l : Level} (A B : UCov l) → (p : Hom _ A B) →
           QEquiv ((i : 𝟚) → ElC (fst (duahom A B (dcoe A B p)) i)) ((i : 𝟚) → ElC (fst p i))
    ηeqInt A B p = η , ηinv , ηeq , ηinveq where

      ηfill : ∀ q i → _
      ηfill q i = dcoetoi (fst p) i (coe (! (ap El (ap ElCov (fst (snd p)))) ∘ Glue-α _ _ _ _ (inl id)) (q ``0))

      η : ∀ q i → _
      η q i =  fst (ηfill q i)

      ηinv : ∀ q i → _
      ηinv q i = duaηfun A B p i (q i)

      ηeq : ∀ q → _ 
      ηeq q = {!!} , {!!} , {!!}

      ηinveq : ∀ q → _ -- this is just ηeqCheck
      ηinveq q = {!!} , {!!} , {!!}
-}
