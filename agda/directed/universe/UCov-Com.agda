{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import Cofibs
open import Kan
open import Path
open import Interval
open import directed.DirInterval
open import directed.Covariant
open import universe.Universe
open import directed.Covariant-is-Fibrant
open import universe.LibFlat
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import universe.U
open import universe.Path
open import Equiv

module directed.universe.UCov-Com where

  open Layered

  -- a composition problem in UCov

  record ComposableUCov (@♭ l : Level) : Set (lmax ℓ₂ (lsuc l)) where
    constructor HComCov
    field
      r r' : I 
      α : Set
      c : Cofib α
      T : I → α → UCov l
      B : _[_↦_] (UCov l) α {{c}} (T r)

  module _ {@♭ l : Level} where
    -- underlying composition problem in U
    forget-composable : ComposableUCov l → Composable l
    forget-composable (HComCov r r' α c T B) =
      HCom r r' α c (\ z pα → ElCov (T z pα)) (ElCov (fst B) , (\ pα → ap ElCov (snd B pα))) 

    -- have to copy and paste to prove they land in UCov
    GlueT-T-Cov : (c : ComposableUCov l) → (fst (GlueT-Cofib (forget-composable c))) → UCov l
    GlueT-T-Cov (HComCov r r' α c T B) = (case (\ pα → (T r' pα))
                                         (\ r=r' → (fst B)) 
                                         (\ pα r=r' → (snd B pα) ∘ ap (\ x → (T x pα)) (! r=r'))) 

    GlueT-B-Cov : (c : ComposableUCov l) → UCov l
    GlueT-B-Cov (HComCov r r' α c T B) = (fst B)

    Composable-to-data : ComposableUCov l → GlueDataUCov l
    Composable-to-data H = Gluedata-cov ((fst o GlueT-Cofib o forget-composable) H)
                                        (snd (((GlueT-Cofib o forget-composable) H)))
                                        ((GlueT-T-Cov H))
                                        (GlueT-B-Cov H)
                                        (\ pα →  (GlueT-f H' pα) o
                                                 -- ElCov/case commuting converstion
                                                    coe (eq pα)   )
                                        ((\ pα →  transport-IsEquivFill (isEquiv-isEquivFill _ _ _
                                                   (GlueT-f-isEquiv (forget-composable H) pα)
                                                     (relCom-hasHCom _ ( (comEl' (HFiber-code {A = (GlueT-T H' pα) } {B = ElCov (GlueT-B-Cov H)} (GlueT-f H' pα))) )))
                                                    ((eq pα)) )) where
      H' = forget-composable H
      eq : ∀ pα -> ElC (GlueT-T-Cov H pα) == El (GlueT-T H' pα)
      eq pα = (ap (\ Z → El (case (λ x → ElCov (ComposableUCov.T H (ComposableUCov.r' H) x)) (λ y → ElCov (fst (ComposableUCov.B H))) Z pα)) (λ= \ x → λ= \ y → ap (\ Z → ap ElCov (snd (ComposableUCov.B H) x) ∘ Z) (ap-o (λ x₁ → ComposableUCov.T H x₁ x) ElCov (! y) ) ∘ ap-∘ ElCov (ap (λ x₁ → ComposableUCov.T H x₁ x) (! y)) (snd (ComposableUCov.B H) x)  ) ∘
                                                      ap El (ElCov-case {{cα = ComposableUCov.c H}} {A = (ComposableUCov.T H (ComposableUCov.r' H))} {B = (λ r=r' → fst (ComposableUCov.B H))} {compat = (λ pα₁ r=r' → snd (ComposableUCov.B H) pα₁ ∘ ap (λ x → ComposableUCov.T H x pα₁) (! r=r'))}pα))
                             
    GlueComposable : ComposableUCov l → UCov l
    GlueComposable = \ C → GlueUCov (Composable-to-data C) 

    hcom-UCov : hasHCom (UCov l)
    hcom-UCov r r' α {{cα}} T B = GlueComposable (HComCov r r' α cα T B) ,
                                  (\ pα → ! (GlueUCov-α (Composable-to-data (HComCov r r' α cα T B)) (inl pα)) ) ,
                                  (\ r=r' → ! (GlueUCov-α (Composable-to-data (HComCov r r' α cα T B)) (inr r=r'))) 

  UCovU : (@♭ l : Level) → U {lmax ℓ₂ (lsuc l)}
  UCovU l = code (Unit{lzero})
                 ( \ _ → UCov l )
                 (relCom-constant _ hcom-UCov)
                 <>
