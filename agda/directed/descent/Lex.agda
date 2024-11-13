{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Path
open import Contractible
open import Equiv
open import Kan
open import universe.Universe
open import universe.U
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import universe.Univalence

module directed.descent.Lex where

{- 
  TODO:
    1. Finish this file [DONE]
    2. Finish Σ [DONE]
    2.5 Prove Σ-η-eq on paper
    3. Finish universe stuff
    4. Make top level file summarizing main thm in paper
    5. Clean up paper
    6. Try version where all isos are equivs
    7. (Maybe) reformulate Path and Hom axioms
    8. Compare our axioms to those listed in Thierry's new draft  
-}

  -- TODO : Move!
  hasSection : ∀ {l} (A : Set l) (B : Set l) → (A → B) → Set l
  hasSection A B f = Σ (λ (g : B → A) → (a : A) → Path A (g (f a)) a) 

  hasSection-code : ∀ {@♭ l : Level} (A B : U{l}) → (El A → El B) → U{l}
  hasSection-code A B f = Σcode-universal (Πcode-universal (B , λ _ → A) , (λ g → Πcode-universal (A , λ a → Path-code-universal ((λ _ → A) , g (f a) , a))))

  postulate
    D : ∀ {@♭ l : Level} → U{l} → U{l}

    η : {@♭ l : Level} (A : U{l}) → El A → El (D A)

    L : {@♭ l : Level} → El (D (U-code{l})) → U{l}

    D-func : ∀ {@♭ l1 l2 : Level}
               {A : U{l1}}
               {B : U{l2}}
               (f : El A → El B)
               → ------------
               El (D A) → El (D B)

    D-id : {@♭ l : Level} (A : U{l})
           → ---------------------------------
           D-func {l} {l} {A} {A} (λ (a : El A) → a) == (λ a → a)

    D-comp : ∀ {@♭ l1 l2 l3 : Level}
               {A : U{l1}}
               {B : U{l2}}
               {C : U{l3}}
               (g : El B → El C)
               (f : El A → El B)
               →
               D-func {l1} {l3} {A} {C} (g o f) == ((D-func {l2} {l3} {B} {C} g) o (D-func f))

    η-nat : ∀ {@♭ l1 l2 : Level} {A : U{l1}} {B : U{l2}}
             (f : El A → El B)
             →
             ((D-func f) o (η A)) == ((η B) o f)

    η-path : {@♭ l : Level} (A : U{l}) → Path _ (D-func (η A)) (η (D A))

    L-eq : {@♭ l : Level} → (L o η (U-code{l})) == D    -- maybe make weak 
    
  dD : ∀ {@♭ l1 l2 : Level} {A : U{l1}} → (El A → U{l2}) → El (D A) → U{l2}
  dD B = L o (D-func B)

  ElD : ∀ {@♭ l : Level} → U{l} → Set l
  ElD = El o D

  DΣ-fst : ∀ {@♭ l1 l2 : Level}
             {A : U{l1}}
             (B : El A → U{l2})
             →
             (El (D (Σcode-universal (A , B)))) → El (D A)
  DΣ-fst B p = D-func fst p

  postulate
    DΣ-snd : ∀ {@♭ l1 l2 : Level}
               {A : U{l1}}
               (B : El A → U{l2})
               →
               (p : El (D (Σcode-universal (A , B)))) → El (dD B (DΣ-fst B p))

{- use DΣ-snd to define, and can derive naturality
    dD-func : ∀ {@♭ l1 l2 : Level}
                {A : U{l1}}
                {B : El A → U{l2}}
                (f : (a : El A) → El (B a))
                → ------------------
                (a : El (D A)) → El (dD B a)
-}

  DΣ-fun : ∀ {@♭ l1 l2 : Level}
             {A : U{l1}}
             (B : El A → U{l2})
             →
             (El (D (Σcode-universal (A , B)))) → (El (Σcode-universal (D A , dD B)))
  DΣ-fun B p = DΣ-fst B p , DΣ-snd B p

  postulate
    DΣ-eq : ∀ {@♭ l1 l2 : Level} -- natural in A on pg 2 of sheaf6
              {A : U{l1}}
              (B : El A → U{l2})
              → -------------------
              isIso (El (D (Σcode-universal (A , B)))) (El (Σcode-universal (D A , dD B))) (DΣ-fun B)
  
  isStack : {@♭ l : Level} → U{l} → U{l}
  isStack A = isEquiv-code A (D A) (η A)
{-
  isStackEl : {@♭ l : Level} → U{l} → Set l
  isStackEl A = isEquiv (El A) (El (D A)) (η A)
-}

  isStack-is-HProp : ∀{@♭ l : Level}(A : U{l}) → HProp (El (isStack A))
  isStack-is-HProp A Astack Astack' = (λ i da → fst (prop da (Astack da) (Astack' da)) i)
                                      , (λ= λ da → fst (snd (prop da (Astack da) (Astack' da))))
                                      , (λ= λ da → snd (snd (prop da (Astack da) (Astack' da)))) where

    fib-prop : ∀ da c → _
    fib-prop da c = contr-implies-hprop (hcomEl (HFiber-code {A = A} {B = D A} (η A) da)) c

    fib-set : ∀ da c → _
    fib-set da c = HProp-to-HSet _ (hcomEl (HFiber-code {A = A} {B = D A} (η A) da)) (fib-prop da c)

    fib-path : ∀ da c a → HProp ((b : Σ (λ a₁ → Path (ElD A) (η A a₁) da)) → Path (Σ (λ a₁ → Path (ElD A) (η A a₁) da)) a b)
    fib-path da c a q1 q2 = (λ i a' → fst (fib-set da c a a' (q1 a') (q2 a')) i)
                            , (λ= λ a' → fst (snd (fib-set da c a a' (q1 a') (q2 a'))))
                            , (λ= λ a' → snd (snd (fib-set da c a a' (q1 a') (q2 a'))))

    prop : (da : ElD A) → HProp (Contractible (Σ λ (a : El A) → Path (ElD A) (η A a) da))
    prop da c = Σ-hprop _ _ (comEl' (λ fib → Πcode-universal (HFiber-code {A = A} {B = D A} (η A) da
                                                             , (λ fib' → Path-code-universal ((λ _ → HFiber-code {A = A} {B = D A} (η A) da)
                                                                                             , fib , fib')))))
                            (fib-prop da c) (fib-path da c) c



  QisStack : {@♭ l : Level} → U{l} → U{l}
  QisStack A = Σcode-universal (Πcode-universal (D A , λ _ → A) , λ p → (Path-code-universal ((λ _ → Πcode-universal (A , λ _ → A)) , (p o (η A)) , (λ a → a))))

  QisStack-to-isStack : {@♭ l : Level} {A : U{l}} → El (QisStack A) → El (isStack A)
  QisStack-to-isStack {A = A} (pA , eq) = QEquiv-to-isEquiv (El A) (El (D A)) (hcomEl A) (hcomEl (D A)) (η A , pA , eq0 , eq1) where

    eq0 : ∀ a → _
    eq0 a = apPath (λ f → f a) eq

    eq1h : Path _ (D-func {A = D A} {A} pA o D-func (η A)) (λ x → x)
    eq1h = D-func o (fst eq) , D-comp pA (η A) ∘ ap D-func (fst (snd eq)) , D-id _ ∘ ap D-func (snd (snd eq)) 

    eq2h' : Path _ (D-func pA o D-func (η A)) (D-func pA o η (D A))
    eq2h' = apPath (λ f → D-func pA o f) (η-path A)

    eq2h : Path _ (D-func pA o D-func (η A)) (η A o pA) 
    eq2h = η-nat {A = D A} {A} pA =∘ eq2h'

    eq1 : ∀ a → _
    eq1 a = ∘Path (hcomEl (D A)) (apPath (λ f → f a) eq1h) (!Path (hcomEl (D A)) (apPath (λ f → f a) eq2h))
    

  isStack-to-QisStack : {@♭ l : Level} {A : U{l}} → El (isStack A) → El (QisStack A)
  isStack-to-QisStack {A = A} Astack = fst (snd qeq) , funext (fst (snd (snd qeq))) where
    qeq = Equiv-to-QEquiv (El A) (El (D A)) (η A , Astack)

  getPatch : {@♭ l : Level} {A : U{l}} → El (isStack A) → El (D A) → El A
  getPatch Astack = fst (isStack-to-QisStack Astack)

  patch-nat : ∀  {@♭ l1 l2 : Level}
                 {A : U{l1}}
                 {B : U{l2}}
                 (Astack : El (isStack A))
                 (Bstack : El (isStack B))
                 (f : El A → El B)
                 →
                 (a : El (D A)) → Path (El B) (getPatch Bstack (D-func f a)) (f (getPatch Astack a))
  patch-nat {A = A} {B} Astack Bstack f a = transport (λ x → El (Path-code-universal ((λ _ → B)
                                                                , (patchB (D-func f x))
                                                                , (f (patchA x)))))
                                                      (snd (snd (eqA a))) (fst p) where

    patchA = getPatch Astack
    eqA = snd (snd (snd (Equiv-to-QEquiv _ _ (η A , Astack))))

    patchB = getPatch Bstack
    eqB = snd (isStack-to-QisStack Bstack)

    p' : Path (El B) (patchB (D-func f (η A (patchA a)))) (f (patchA (η A (patchA a))))
    p' = transport (λ g → Path (El B) (patchB (g (patchA a))) (f (patchA (η A (patchA a)))))
                   (! (η-nat f))
                   (∘Path (hcomEl B) (apPath (λ x → f (patchA x))
                                             (!Path (hcomEl (D A)) (eqA a)))
                                     (apPath (λ g → g (f (patchA a))) eqB))

    p : _
    p = comEl' (λ x → Path-code-universal ((λ _ → B) , (patchB (D-func f x)) , (f (patchA x))))
               (fst (eqA a)) `0 `1 ⊥ (λ _ → abort)
               (transport! (λ x → El (Path-code-universal ((λ _ → B)
                                     , (patchB (D-func f x))
                                     , (f (patchA x)))))
                           (fst (snd (eqA a))) p' , (λ ff → abort ff))

  DΣ-Path : ∀ {@♭ l1 l2 : Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : (a : El A) → El (isStack (B a)))
               → ----------------------------
               Path U (Σcode-universal (A , B)) (Σcode-universal (A , dD B o η A))
  DΣ-Path {l1} {l2} {A} B stackB = coe! (ap (λ x → Path U (Σcode-universal (A , B)) (Σcode-universal (A , x))) eq)
                                  (apPath (λ X → Σcode-universal (A , X)) (funext λ a → ua (η (B a) , stackB a))) where

    eq : (L o D-func B o η A) == (D o B)
    eq = ap (λ x → x o B) L-eq ∘ ap (λ x → L o x) (η-nat B)

  
{-
  postulate
    DUnit-eq : {@♭ l : Level} (x : D (Unit{l})) → η Unit <> == x

  DUnit-isIso : {@♭ l : Level} → isIso _ _ (η (Unit{l}))
  DUnit-isIso = iso (λ _ → <>) (λ {<> → id}) DUnit-eq

  Σty-eq : ∀ {l1 l2} {A A' : U{l}1} (B : A → U{l}2) (B' : A' → U{l}2) → (Aeq : A == A') → ((x : A) → B x == B' (coe Aeq x)) → Σ B == Σ B'
  Σty-eq B B' id Beq = ap Σ (λ= λ x → Beq x) 

  dD-const : ∀ {l1 l2} (A : U{l}1) (B : U{l}2) (x : D A) → dD (λ _ → B) x == D B
  dD-const A B x = {!!}

  Dpair-eq : ∀ {l1 l2} (A : U{l}1) (B : U{l}2) → (D (A × B)) == (D A × D B)
  Dpair-eq {l} A B =  Σty-eq _ _ id (dD-const _ _) ∘ DΣ-eq  _ where

  TotId : ∀{l} (A : U{l}) → U{l}
  TotId A = Σ λ (x : A × A) → fst x == snd x 

  DId-fun : ∀{l} (A : U{l}) → TotId (D A) → D (TotId A)
  DId-fun A (p , eq) = coe! (DΣ-eq _) (coe! (Dpair-eq _ _) p , {!dD (λ x → fst x == snd x) (coe! (Dpair-eq A A) p)!})

  DId-fun' : ∀{l} (A : U{l}) → D (TotId A) → TotId (D A)
  DId-fun' A p = {!!}
  -}
