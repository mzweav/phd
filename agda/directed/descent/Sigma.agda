{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import Cofibs
open import Interval
open import Path
open import Equiv
open import Kan
open import universe.Universe
open import universe.U
open import universe.Univalence
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import directed.descent.Lex

module directed.descent.Sigma where

  Σ-η'' : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
          (B : El A → U{l2})
          → Σ {A = El A} (El o B) → Σ {A = El A} (El o dD B o η A)
  Σ-η'' {l1} {l2} {A} B ab = fst ab , transport (λ g → El (g (fst ab))) (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq) (η (B (fst ab)) (snd ab)) 

  ΣisStack'' : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : (a : El A) → El (isStack (B a)))
               →
               hasSection (Σ {A = El A} (El o B)) (Σ {A = El A} (El o dD B o η A)) (Σ-η'' B)
  ΣisStack'' {l1} {l2} {A} B stackB = patch , path where

    patchB : ∀ a → _
    patchB a = fst (isStack-to-QisStack (stackB a))

    patchB-eq : ∀ a b → _
    patchB-eq a b = apPath (λ f → f b) (snd (isStack-to-QisStack (stackB a)))

    patch : ∀ p → _
    patch (a , b) = a , patchB a (transport! (λ g → El (g a)) (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq) b)

    path : ∀ p → Path (Σ (El o B)) ((patch o Σ-η'' B) p) p
    path (a , b) = (λ i → a , fst (patchB-eq a b) i)
                   , ap (λ b' → a , b') (ap (patchB a)
                                            (move-transport-right (λ g → El (g a)) (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq) id)
                                            ∘ fst (snd (patchB-eq a b)))
                   , ap (λ b' → a , b') (snd (snd (patchB-eq a b))) 

  Σ-η' : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
         (B : El A → U{l2})
         → Σ {A = El A} (El o B) → Σ {A = ElD A} (El o dD {A = A} B)
  Σ-η' {l1} {l2} {A} B ab = η A (fst ab) , transport (λ g → El (g (fst ab))) (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq) (η (B (fst ab)) (snd ab))

  -- reformulate so just axiom about snd
  postulate
    Σ-η-eq : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
               (B : El A → U{l2})
               → (λ z → Σ-η' {A = A} B z) == (λ z → (DΣ-fun B o η (Σcode-universal (A , B))) z)

  ΣisStack' : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
              (B : El A → U{l2})
              (_ : El (isStack A))
              (_ : (a : El A) → El (isStack (B a)))
              →
              hasSection (Σ {A = El A} (El o B)) (Σ {A = ElD A} (El o dD {A = A} B)) (Σ-η' B)
  ΣisStack' {l1} {l2} {A} B stackA stackB = transport (El o fib1) (snd (snd η-abs1)) equiv where -- transport (El o fib1) (snd (snd η-abs1)) (fst equiv) where
  
    Σpath : Path (Σ λ X → Σ (λ (f' : (El A → El X) × (El X → ElD A)) → Path _ (snd f' o fst f') (η A)))
                     (A , ((λ a → a) , η A) , idPath (η A))
                     (D A , (η A , (λ a → a)) , idPath (η A))
    Σpath = ua-Σ-path' A (D A) (η A , stackA)

    η-abs-b : ∀ (X : U{l1})
             (f1 : El A → El X)
             (f2 : El X → ElD A)
             (ηPath : Path _ (f2 o f1) (η A))
             → (p : Σ (El o B)) → (i : I) → ((El o dD B o (fst ηPath i)) (fst p)) [ ⊥ ↦ abort , (`1 == i) ↦ _ ]
    η-abs-b X f1 f2 p ab i = comEl' (λ (g : El A → ElD A) → (dD B o g) (fst ab)) (fst p) `1 i ⊥ (λ _ → abort)
                                         (transport! (El o (λ g → (dD B o g) (fst ab))) (snd (snd p))
                                                     (transport (λ g → El (g (fst ab)))
                                                                (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq)
                                                                (η (B (fst ab)) (snd ab))) , λ ff → abort ff) 

    η-abs : ∀ (X : U{l1})
              (f1 : El A → El X)
              (f2 : El X → ElD A)
              (ηPath : Path _ (f2 o f1) (η A))
              →
              Σ (El o B) → Σ (El o dD {A = A} B o f2)
    η-abs X f1 f2 p ab = f1 (fst ab) , transport (El o (λ g → (dD B o g) (fst ab)))
                                               (fst (snd p))
                                               (fst (η-abs-b X f1 f2 p ab `0))

    η-abs0' : (p : Σ (El o B)) → Path (Σ (El o dD {A = A} B o η A)) (η-abs A (λ a → a) (η A) (idPath (η A)) p) (Σ-η'' B p)
    η-abs0' (a , b) = (λ i → a , fst (η-abs-b A (λ a → a) (η A) (idPath (η A)) (a , b) i))
                      , id
                      , ap (λ b' → a , b')
                           (! (snd (snd (η-abs-b A (λ a → a) (η A) (idPath (η A)) (a , b) `1)) id)) 

    η-abs0 : Path (Σ (El o B) → Σ (El o dD {A = A} B o η A)) (η-abs A (λ a → a) (η A) (idPath (η A))) (Σ-η'' B)
    η-abs0 = funext η-abs0'

    η-abs1' : (p : Σ (El o B)) → Path (Σ (El o dD {A = A} B)) (η-abs (D A) (η A) (λ a → a) (idPath (η A)) p) (Σ-η' B p)
    η-abs1' (a , b) = (λ i → η A a , fst (η-abs-b (D A) (η A) (λ a → a) (idPath (η A)) (a , b) i))
                      , id
                      , ap (λ b' → η A a , b')
                           (! (snd (snd (η-abs-b (D A) (η A) (λ a → a) (idPath (η A)) (a , b) `1)) id))

    η-abs1 : Path _ (η-abs (D A) (η A) (λ a → a) (idPath (η A))) (Σ-η' B)
    η-abs1 = funext η-abs1'
    
    fib : (X : (Σ λ X → Σ (λ (f' : (El A → El X) × (El X → ElD A)) → Path _ (snd f' o fst f') (η A)))) → _
    fib X = hasSection-code (Σcode-universal (A , B))
                            (Σcode-universal (fst X , dD {A = A} B o snd (fst (snd  X))))
                            (η-abs (fst X) (fst (fst (snd X))) (snd (fst (snd X))) (snd (snd X)))

    fib0 : ∀ f' → U
    fib0 f' = hasSection-code (Σcode-universal (A , B)) (Σcode-universal (A , dD {A = A} B o η A)) f'

    fib1 : ∀ f' → U
    fib1 f' = hasSection-code (Σcode-universal (A , B)) (Σcode-universal (D A , dD {A = A} B)) f'

    equiv0 : El (fib0 (fst η-abs0 `0))
    equiv0 = fst (comEl' fib0 (fst η-abs0) `1 `0 ⊥ (λ _ → abort)
                    (transport! (El o fib0) (snd (snd η-abs0)) (ΣisStack'' B stackB) , λ ff → abort ff))

    equiv1 : El (fib (fst Σpath `1))
    equiv1 = fst (comEl' fib
                   (fst Σpath) `0 `1 ⊥ (λ _ → abort)
                   (transport! (El o fib) {M = fst Σpath `0} {N = (A , ((λ a → a) , η A) , idPath (η A))}
                               (fst (snd Σpath))
                               (transport (El o fib0) (fst (snd η-abs0)) equiv0)
                   , λ ff → abort ff))

    equiv : El (fib1 (fst η-abs1 `1))
    equiv = fst (comEl' fib1 (fst η-abs1) `0 `1 ⊥ (λ _ → abort)
                   (transport! (El o fib1)
                               (fst (snd η-abs1))
                               (transport (El o fib) (snd (snd Σpath)) equiv1)
                   , λ ff → abort ff))


  ΣisStack : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : El (isStack A))
               (_ : (a : El A) → El (isStack (B a)))
               → ----------------------------
               El (isStack (Σcode-universal (A , B)))
  ΣisStack {l1} {l2} {A} B stackA stackB =  QisStack-to-isStack (fst sec , funext (snd sec)) where
  
    sec-path : ∀ p → _
    sec-path p = transport! (λ h → Path (Σ (El o B)) ((fst (ΣisStack' {A = A} B stackA stackB) o h o Σ-η' {A = A} B) p) p)
                            (λ= (isIso.fg (DΣ-eq {A = A} B)))
                            (snd (ΣisStack' {A = A} B stackA stackB) p)
                            
    sec' : hasSection _ _ (isIso.g (DΣ-eq {A = A} B) o Σ-η' B)
    sec' = fst (ΣisStack' {A = A} B stackA stackB) o (DΣ-fun {A = A} B) , sec-path

    Σ-η-eq' : (p : Σ (El o B)) → (isIso.g (DΣ-eq {A = A} B) o Σ-η' B) p == η (Σcode-universal (A , B)) p
    Σ-η-eq' p = isIso.gf (DΣ-eq B) (η (Σcode-universal (A , B)) p)
                     ∘ ap (isIso.g (DΣ-eq B)) (ap (λ f' → f' p) (Σ-η-eq {A = A} B))

    sec : hasSection _ _ (η (Σcode-universal (A , B)))
    sec = transport (hasSection _ _) (λ= Σ-η-eq') sec'

  Σpatch : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : El (isStack A))
               (_ : (a : El A) → El (isStack (B a)))
               → ----------------------------
               ElD (Σcode-universal (A , B)) → Σ (El o B)
  Σpatch B stackA stackB = getPatch (ΣisStack B stackA stackB)
