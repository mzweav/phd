{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Equiv
open import Path
open import Kan
open import Glue
open import universe.Universe
open import universe.U
open import universe.Path
open import universe.Univalence
open import universe.Glue
open import directed.descent.Lex
open import directed.descent.Pi
open import directed.descent.Sigma

module directed.descent.Path where

  apPathO :  ∀ {l1 l2} {A : I → Set l1} {B : I → Set l2} {a0 a1} → (f : (x : I) → A x → B x) → (p : PathO A a0 a1) → PathO B (f `0 a0) (f `1 a1)
  apPathO f (p , eq0 , eq1) = (λ i → f i (p i)) , ap (f `0) eq0 , ap (f `1) eq1

  postulate
    DPath-eq : ∀ {@♭ l : Level} (A : I → U{l}) (a0 : El (A `0)) (a1 : El (A `1))
               → --------------------------------------------------
                 Iso (El (D (Path-code-universal (A , a0 , a1)))) (El (Path-code-universal ((λ i → D (A i)) , (η (A `0) a0) , (η (A `1) a1))))

  Path-η : ∀ {@♭ l : Level} (A : I → U{l}) (a0 : El (A `0)) (a1 : El (A `1))
           → --------------------------------------------------
           El (Path-code-universal (A , a0 , a1)) → El (D (Path-code-universal (A , a0 , a1)))
  Path-η A a0 a1 =  (Iso.g (DPath-eq A a0 a1)) o (apPathO (λ i → η (A i)))

  postulate
    Path-η-eq : ∀ {@♭ l : Level} (A : I → U{l})  (a0 : El (A `0)) (a1 : El (A `1)) → η (Path-code-universal (A , a0 , a1)) == Path-η A a0 a1

  Path-patch : ∀ {@♭ l : Level} {A : I → U{l}} {a0 : El (A `0)} {a1 : El (A `1)} → ((x : I) → El (isStack (A x))) → El (D (Path-code-universal (A , a0 , a1))) → El (Path-code-universal (A , a0 , a1))
  Path-patch {A = A} {a0} {a1} Astack p = (λ i → fst (p' p'' i))
                                      , ap (λ f → f a0) (snd (snd (Apatch-eq `0))) ∘ ! (fst (snd (p' p'' `0)) (inl id))
                                      , ap (λ f → f a1) (snd (snd (Apatch-eq `1))) ∘ ! (fst (snd (p' p'' `1)) (inr id)) where
    Apatch : (x : I) → El (D (A x)) → El (A x)
    Apatch x = fst (isStack-to-QisStack (Astack x))

    Apatch-eq : ∀ x → _
    Apatch-eq x = snd (isStack-to-QisStack (Astack x))

    p' : ∀ p i → _
    p' (p , eq0 , eq1) i = (hcomEl (A i)) `0 `1 ((i == `0) ∨ (i == `1))
                           (λ j → case01 (λ i=0 → transport! (El o A) i=0 (fst (Apatch-eq `0) j a0))
                                          (λ i=1 → transport! (El o A) i=1 (fst (Apatch-eq `1) j a1)))
                           (Apatch i (p i)
                           , ∨-elim01 _ (λ i=0 → ! (apd! (λ x → Apatch x (p x)) i=0)
                                                  ∘ ap (transport! (El o A) i=0)
                                                                   (ap! (Apatch `0) eq0
                                                                   ∘ ap (λ f → f a0) (fst (snd (Apatch-eq `0)))))
                                         (λ  i=1 → ! (apd! (λ x → Apatch x (p x)) i=1)
                                                  ∘ ap (transport! (El o A) i=1)
                                                                   (ap! (Apatch `1) eq1
                                                                   ∘ ap (λ f → f a1) (fst (snd (Apatch-eq `1))))))
    p'' : _
    p'' = Iso.f (DPath-eq A a0 a1) p

  Path-η-Equiv : ∀ {@♭ l : Level} (A : I → U{l})  (a0 : El (A `0)) (a1 : El (A `1)) → (∀ i → El (isStack (A i))) → isEquiv _ _ (Path-η A a0 a1)
  Path-η-Equiv A a0 a1 Astack = isEquiv-comp (hcomEl (Path-code-universal (A , a0 , a1)))
                                            (hcomEl (Path-code-universal ((λ i → D (A i)) , (η (A `0) a0) , (η (A `1) a1))))
                                            (hcomEl (D (Path-code-universal (A , a0 , a1))))
                                            (Iso.g (DPath-eq A a0 a1)) (apPathO (λ i → η (A i)))
                                                   (snd (Iso-Equiv (hcomEl (Path-code-universal ((λ i → D (A i)) , (η (A `0) a0) , (η (A `1) a1))))
                                                                   (hcomEl (D (Path-code-universal (A , a0 , a1))))
                                                                   (iso-inv (DPath-eq A a0 a1)))) eq' where

    Apatch = λ i → fst (isStack-to-QisStack (Astack i))
    Apatch-eq = λ i → snd (isStack-to-QisStack (Astack i))

    tyPath : Path (Σ λ X → ((i : I) → El (A i) → El (X i))) (A , λ _ a → a) (D o A , λ i → η (A i))
    tyPath = ua-Σ-pathd I A (λ i → (D (A i))) (λ i → η (A i) , Astack i)

    eq' : isEquiv _ _ (λ (p : El (Path-code-universal (A , a0 , a1))) → (apPathO (λ i → η (A i))) p)
    eq' = transport (λ {(X , f) → isEquiv (El (Path-code-universal (A , a0 , a1)))
                                          (El (Path-code-universal (X , f `0 a0 , f `1 a1)))
                                          (apPathO f)}) (snd (snd tyPath))
                    (fst (comEl' (λ {(X , f) → isEquiv-code (Path-code-universal (A , a0 , a1))
                                                            (Path-code-universal (X , f `0 a0 , f `1 a1))
                                                            (apPathO f)})
                                 (fst tyPath) `0 `1 ⊥ (λ _ → abort)
                                 (transport! (λ {(X , f) → isEquiv (El (Path-code-universal (A , a0 , a1)))
                                          (El (Path-code-universal (X , f `0 a0 , f `1 a1)))
                                          (apPathO f)}) (fst (snd tyPath))
                                          (transport (λ f → isEquiv _ _ f)
                                                     (λ= (λ _ → PathO= _ _ (λ _ → id)))
                                                     (id-Equiv (hcomEl (Path-code-universal (A , a0 , a1)))))
                                     , (λ ff → abort ff))))

  PathO-isStack : ∀ {@♭ l : Level} (A : I → U{l}) (a0 : El (A `0)) (a1 : El (A `1)) → ((i : I) → El (isStack (A i))) → El (isStack (Path-code-universal (A , a0 , a1)))
  PathO-isStack A a0 a1 Astack = transport! (λ f → isEquiv _ _ f) (Path-η-eq A a0 a1) (Path-η-Equiv A a0 a1 Astack)

  Path-isStack : ∀ {@♭ l : Level} (A : U{l}) (a0 a1 : El A) → El (isStack A) → El (isStack (Path-code-universal ((λ _ → A) , a0 , a1)))
  Path-isStack  A a0 a1 Astack = PathO-isStack (λ _ → A) a0 a1 (λ _ → Astack)

  HFiber-isStack : {@♭ l : Level} {A B : U{l}} → El (isStack A) → El (isStack B) → (f : El A → El B) (b : El B) → El (isStack (HFiber-code {l} {A} {B} f b))
  HFiber-isStack {l} {A} {B} Astack Bstack f b = ΣisStack _ Astack (λ a → Path-isStack B (f a) b Bstack) 

  Contractible-isStack : ∀ {@♭ l : Level} (A : U{l}) → El (isStack A) → El (isStack (Contractible-code A))
  Contractible-isStack A Astack = ΣisStack _ Astack (λ a → ΠisStack _ (λ a' → Path-isStack _ _ _ Astack))

  isEquiv-isStack : {@♭ l : Level} {A B : U{l}} → El (isStack A) → El (isStack B) → (f : El A → El B) → El (isStack (isEquiv-code A B f))
  isEquiv-isStack Astack Bstack f = ΠisStack _ (λ b → Contractible-isStack _ (HFiber-isStack Astack Bstack f b))
