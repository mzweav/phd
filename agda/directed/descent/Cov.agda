{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import directed.DirInterval
open import Proposition
open import Cofibs
open import Equiv
open import Path
open import Kan
open import universe.Universe
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import directed.Covariant
open import directed.universe.Hom
open import directed.descent.Lex
open import directed.descent.Pi
open import directed.descent.Sigma
open import directed.descent.Path
open import directed.descent.Hom

module directed.descent.Cov where

  relCov-internal-code : ∀ {@♭ l : Level} {Γ : U{l}} (A : El Γ → U{l}) → U{l}
  relCov-internal-code {Γ = Γ} A = Πcode-universal (→code 𝟚 Γ
                                                   , λ p → Πcode-universal (A (p ``0)
                                                                           , λ a → Contractible-code (Σcode-universal (A (p ``1)
                                                                                                     , λ b → Hom-code-universal ((\ x → A (p x)) , a , b)))))


  -- TODO: add implicit args so this type checking terminates 
  relCov-isStack : ∀ {@♭ l : Level} {Γ : U{l}} (A : El Γ → U{l}) → ((x : El Γ) → El (isStack (A x))) → El (isStack (relCov-internal-code A))
  relCov-isStack {l} {Γ} A Astack = ΠisStack {A = →code 𝟚 Γ} (λ (p : 𝟚 → El Γ) → Πcode-universal (A (p ``0)
                                                                                          , λ a → Contractible-code (Σcode-universal (A (p ``1)
                                                                                                                    , λ b → Hom-code-universal ((\ x → A (p x)) , a , b))))) 
                                             (λ p → ΠisStack (λ a → Contractible-code (Σcode-universal (A (p ``1)
                                                                                      , λ b → Hom-code-universal ((\ x → A (p x)) , a , b))))
                                                    (λ a → Contractible-isStack (Σcode-universal (A (p ``1)
                                                                                , λ b → Hom-code-universal ((\ x → A (p x)) , a , b)))
                                                                                (ΣisStack (λ b → Hom-code-universal ((\ x → A (p x)) , a , b))
                                                                                          (Astack (p ``1))
                                                                                          (λ b → HomO-isStack (\ x → A (p x)) a b
                                                                                                              (λ i → Astack (p i))))))

