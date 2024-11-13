{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Equiv
open import Path
open import Kan
open import universe.Universe
open import universe.U
open import universe.Path
open import directed.DirInterval
open import directed.universe.Hom
open import universe.Univalence
open import directed.descent.Lex
open import directed.descent.Pi
open import directed.descent.Sigma

module directed.descent.Hom where

  postulate
    DHom-eq : ∀ {@♭ l : Level} (A : 𝟚 → U{l}) (a0 : El (A ``0)) (a1 : El (A ``1))
               → --------------------------------------------------
                 Iso (El (D (Hom-code-universal (A , a0 , a1)))) (El (Hom-code-universal ((λ i → D (A i)) , (η (A ``0) a0) , (η (A ``1) a1))))

  Hom-η : ∀ {@♭ l : Level} (A : 𝟚 → U{l}) (a0 : El (A ``0)) (a1 : El (A ``1))
           → --------------------------------------------------
           El (Hom-code-universal (A , a0 , a1)) → El (D (Hom-code-universal (A , a0 , a1)))
  Hom-η A a0 a1 =  (Iso.g (DHom-eq A a0 a1)) o (apHomO (λ i → η (A i)))

  postulate
    Hom-η-eq : ∀ {@♭ l : Level} (A : 𝟚 → U{l})  (a0 : El (A ``0)) (a1 : El (A ``1)) → η (Hom-code-universal (A , a0 , a1)) == Hom-η A a0 a1

  Hom-patch : ∀ {@♭ l : Level} {A : 𝟚 → U{l}} {a0 : El (A ``0)} {a1 : El (A ``1)} → ((x : 𝟚) → El (isStack (A x))) → El (D (Hom-code-universal (A , a0 , a1))) → El (Hom-code-universal (A , a0 , a1))
  Hom-patch {A = A} {a0} {a1} Astack p = (λ i → fst (p' p'' i))
                                      , ap (λ f → f a0) (snd (snd (Apatch-eq ``0))) ∘ ! (fst (snd (p' p'' ``0)) (inl id))
                                      , ap (λ f → f a1) (snd (snd (Apatch-eq ``1))) ∘ ! (fst (snd (p' p'' ``1)) (inr id)) where
    Apatch : (x : 𝟚) → El (D (A x)) → El (A x)
    Apatch x = fst (isStack-to-QisStack (Astack x))

    Apatch-eq : ∀ x → _
    Apatch-eq x = snd (isStack-to-QisStack (Astack x))

    p' : ∀ p i → _
    p' (p , eq0 , eq1) i = (hcomEl (A i)) `0 `1 ((i == ``0) ∨ (i == ``1))
                           (λ j → cased01 (λ i=0 → transport! (El o A) i=0 (fst (Apatch-eq ``0) j a0))
                                          (λ i=1 → transport! (El o A) i=1 (fst (Apatch-eq ``1) j a1)))
                           (Apatch i (p i)
                           , ∨-elimd01 _ (λ i=0 → ! (apd! (λ x → Apatch x (p x)) i=0)
                                                  ∘ ap (transport! (El o A) i=0)
                                                                   (ap! (Apatch ``0) eq0
                                                                   ∘ ap (λ f → f a0) (fst (snd (Apatch-eq ``0)))))
                                         (λ  i=1 → ! (apd! (λ x → Apatch x (p x)) i=1)
                                                  ∘ ap (transport! (El o A) i=1)
                                                                   (ap! (Apatch ``1) eq1
                                                                   ∘ ap (λ f → f a1) (fst (snd (Apatch-eq ``1))))))
    p'' : _
    p'' = Iso.f (DHom-eq A a0 a1) p

  Hom-η-Equiv : ∀ {@♭ l : Level} (A : 𝟚 → U{l})  (a0 : El (A ``0)) (a1 : El (A ``1)) → (∀ i → El (isStack (A i))) → isEquiv _ _ (Hom-η A a0 a1)
  Hom-η-Equiv A a0 a1 Astack = isEquiv-comp (hcomEl (Hom-code-universal (A , a0 , a1)))
                                            (hcomEl (Hom-code-universal ((λ i → D (A i)) , (η (A ``0) a0) , (η (A ``1) a1))))
                                            (hcomEl (D (Hom-code-universal (A , a0 , a1))))
                                            (Iso.g (DHom-eq A a0 a1)) (apHomO (λ i → η (A i)))
                                                   (snd (Iso-Equiv (hcomEl (Hom-code-universal ((λ i → D (A i)) , (η (A ``0) a0) , (η (A ``1) a1))))
                                                                   (hcomEl (D (Hom-code-universal (A , a0 , a1))))
                                                                   (iso-inv (DHom-eq A a0 a1)))) eq' where

    Apatch = λ i → fst (isStack-to-QisStack (Astack i))
    Apatch-eq = λ i → snd (isStack-to-QisStack (Astack i))

    tyPath : Path (Σ λ X → ((i : 𝟚) → El (A i) → El (X i))) (A , λ _ a → a) (D o A , λ i → η (A i))
    tyPath = ua-Σ-pathd 𝟚 A (λ i → (D (A i))) (λ i → η (A i) , Astack i)

    eq' : isEquiv _ _ (λ (p : El (Hom-code-universal (A , a0 , a1))) → (apHomO (λ i → η (A i))) p)
    eq' = transport (λ {(X , f) → isEquiv (El (Hom-code-universal (A , a0 , a1)))
                                          (El (Hom-code-universal (X , f ``0 a0 , f ``1 a1)))
                                          (apHomO f)}) (snd (snd tyPath))
                    (fst (comEl' (λ {(X , f) → isEquiv-code (Hom-code-universal (A , a0 , a1))
                                                            (Hom-code-universal (X , f ``0 a0 , f ``1 a1))
                                                            (apHomO f)})
                                 (fst tyPath) `0 `1 ⊥ (λ _ → abort)
                                 (transport! (λ {(X , f) → isEquiv (El (Hom-code-universal (A , a0 , a1)))
                                          (El (Hom-code-universal (X , f ``0 a0 , f ``1 a1)))
                                          (apHomO f)}) (fst (snd tyPath))
                                          (transport (λ f → isEquiv _ _ f)
                                                     (λ= (λ _ → HomO= _ _ (λ _ → id)))
                                                     (id-Equiv (hcomEl (Hom-code-universal (A , a0 , a1)))))
                                     , (λ ff → abort ff))))

  HomO-isStack : ∀ {@♭ l : Level} (A : 𝟚 → U{l}) (a0 : El (A ``0)) (a1 : El (A ``1)) → ((i : 𝟚) → El (isStack (A i))) → El (isStack (Hom-code-universal (A , a0 , a1)))
  HomO-isStack A a0 a1 Astack = transport! (λ f → isEquiv _ _ f) (Hom-η-eq A a0 a1) (Hom-η-Equiv A a0 a1 Astack)

  Hom-isStack : ∀ {@♭ l : Level} (A : U{l}) (a0 a1 : El A) → El (isStack A) → El (isStack (Hom-code-universal ((λ _ → A) , a0 , a1)))
  Hom-isStack  A a0 a1 Astack = HomO-isStack (λ _ → A) a0 a1 (λ _ → Astack)
