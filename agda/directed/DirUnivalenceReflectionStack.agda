{-# OPTIONS --rewriting  #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import Cofibs
open import Kan
open import Path
open import Equiv
open import Contractible
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
open import directed.universe.Hom
open import directed.DirUnivalenceReflection
open import directed.UCovStack

module directed.DirUnivalenceReflectionStack where

  open Layered

  subtype-hom : {@♭ l1 l2 : Level} → {A : U{l1}} (B : El A → U{l2}) → ((a : El A) → HProp (El (B a))) → (x y : Σ (El o B)) → Hom (El A) (fst x) (fst y) → Hom _ x y
  subtype-hom B propB (a1 , b1) (a2 , b2) p = (λ i → fst p i , {!!}) -- fst pB i)
                                              , pair= (fst (snd p)) {!!} -- (move-transport-left B (fst (snd p)) (fst (snd pB))) 
                                              , pair= (snd (snd p)) {!!} -- (move-transport-left B (snd (snd p)) (snd (snd pB)))
                                              where

{-
    coeB : ∀ i → _
    coeB i = (comEl' B) (fst p) i ⊥ (λ _ → abort) (transport! B (fst (snd p)) b1 , (λ ff → abort ff))

    fixB-path : Path _ (fst (coeB ``1)) (transport! B (snd (snd p)) b2)
    fixB-path = propB (fst p ``1) (fst (coeB ``1)) (transport! B (snd (snd p)) b2)

    fixB : ∀ i → _
    fixB i = (comEl' B) (λ _ → (fst p) i) ``1 ((i == ``0) ∨ (i == ``1))
                  (λ j → cased01 (λ i=0 → transport! (B o fst p) i=0 (transport! B (fst (snd p)) b1))
                                 (λ i=1 → transport! (B o fst p) i=1 (fst fixB-path j)))
                  (fst (coeB i)
                  , ∨-elim01 _ (λ i=0 → ! (apd! (λ i → fst (coeB i)) i=0)
                                        ∘ ap (transport! (B o fst p) i=0) (snd (snd (coeB `0)) id))
                               (λ i=1 → ! (apd! (λ i → fst (coeB i)) i=1)
                                        ∘ ap (transport! (B o fst p) i=1) (fst (snd (fixB-path)))))

    pB : HomO (B o fst p) (transport! B (fst (snd p)) b1) (transport! B (snd (snd p)) b2)
    pB = (λ i → fst (fixB i))
         , ! (fst (snd (fixB `0)) (inl id))
         , snd (snd fixB-path) ∘ ! (fst (snd (fixB ``1)) (inr id))
-}

{-
  duahomstack :  {@♭ l : Level} (A B : UCovStack l) → (f : ElCS A → ElCS B) → Hom (UCovStack l) A B
  duahomstack A B f = subtype-hom {A = {!!}} {!!} {!!} _ _ (duahom (fst A) (fst B) f)
-}

{- (λ i → fst (duahom (fst A) (fst B) f) i , {!!})
                      , pair= (fst (snd (duahom (fst A) (fst B) f))) {!!}
                      , pair= (snd (snd (duahom (fst A) (fst B) f))) {!!}
-}

{-
    duaβstack : {@♭ l : Level} (A B : UCovStack l) → (f : ElCS A → ElCS B) → Path _ f (dcoestack A B (duahomstack A B f))
    duaβstack {l} A B f =
-}
