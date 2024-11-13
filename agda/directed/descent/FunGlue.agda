{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import Interval
open import Path
open import directed.DirInterval
open import Proposition
open import Cofibs
open import Equiv
open import Kan
open import universe.Universe
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import universe.Univalence
open import Glue
open import directed.Covariant
open import directed.universe.FunGlueKan
open import directed.descent.Lex

module directed.descent.FunGlue where

  private
    dua : ∀ {@♭ l : Level} (x : 𝟚)
            (A : U{l})
            (B : U{l})
            (f : El A → El B)
            → -------------------------
            U{l}
    dua x A B f = FunGlueUKan (fungluedatakan A B f x)

  FunGlue= : ∀ {@♭ l : Level} {i : 𝟚}
            {A : U{l}}
            {B : U{l}}
            {f : El A → El B}
            (x y : El (dua i A B f))
            (_ : (i=0 : i == ``0) → coe (Glue-α _ _ _ _ (inl i=0)) x == coe (Glue-α _ _ _ _ (inl i=0)) y)
            (_ : unglue x == unglue y)
            →
            x == y
  FunGlue= {l} {i} {A} {B} {f} x y Aeq Beq  = ! (Glueη y)
                                              ∘ ap (λ x → glue _ _ _ _ (fst (fst x)) (snd (fst x) , snd x))
                                                   (pair= (×= (λ= (∨-elimd01 _ Aeq
                                                                               (λ i=1 → ! (unglue-α y (inr i=1)) ∘ Beq ∘ unglue-α x (inr i=1))))
                                                              Beq)
                                                          (λ= λ _ → uip))
                                              ∘ Glueη x

  dua-path : ∀ {@♭ l : Level} {i : 𝟚}
            {A : U{l}}
            {B : U{l}}
            {f : El A → El B}
            (x y : El (dua i A B f))
            (pa :  (i=0 : i == ``0) → Path (El A) (coe (Glue-α _ _ _ _ (inl i=0)) x) (coe (Glue-α _ _ _ _ (inl i=0)) y))
            (pb : Path (El B) (unglue x) (unglue y))
            (peq : ∀ j → (i=0 : i == ``0) → f (fst (pa i=0) j) == fst pb j)
            →
            Path (El (dua i A B f)) x y
  dua-path {i = i} {A} {B} {f} x y pa pb peq = (λ j → glue _ _ _ _
                                                           (∨-elimd01 _ (λ i=0 → fst (pa i=0) j)
                                                                        (λ _ → fst pb j))
                                                           (fst pb j , ∨-elimd01 _ (peq j) (λ _ → id)))
                                               , ! (Glueη x)
                                                 ∘ (FunGlue= _ _ (λ i=0 → ! (glue-α _ _ (inl i=0))
                                                                        ∘ fst (snd (pa i=0))
                                                                        ∘ glue-α _ _ (inl i=0))
                                                                 (! (Glueβ _ _)
                                                                 ∘ fst (snd pb)
                                                                 ∘ Glueβ _ _))
                                               , ! (Glueη y)
                                                 ∘ (FunGlue= _ _ (λ i=0 → ! (glue-α _ _ (inl i=0))
                                                                        ∘ snd (snd (pa i=0))
                                                                        ∘ glue-α _ _ (inl i=0))
                                                                 (! (Glueβ _ _)
                                                                 ∘ snd (snd pb)
                                                                 ∘ Glueβ _ _))

  DGlue-eq0 : ∀ {@♭ l : Level} (x : 𝟚)
                (A : U{l})
                (B : U{l})
                (f : El A → El B)
                (g : ElD (dua x A B f))
                (x=0 : x == ``0)
                →
                D-func {A = dua x A B f} {B = B} unglue g == (D-func f (transport ElD (FunGlueUKan0 _ x=0) g))
  DGlue-eq0 x A B f g x=0 = ap {M = (dua x A B f) , unglue , g} {N = A , f , (transport ElD (FunGlueUKan0 _ x=0) g)}
                       (λ (x : Σ (λ X → ((El X → El B) × El (D X)))) → D-func (fst (snd x)) (snd (snd x)))
                       (pair= (FunGlueUKan0 _ x=0)
                              (×= (het-to-hom (λ=o (λ g z eq → apdo f (het-to-hom (eq ∘h transport-=h (λ X → X) (Glue-α _ _ _ _ (inl x=0))))
                                                                      ∘h hom-to-het (! (unglue-α g (inl x=0))))
                                                                      ∘h transport-=h (λ X → El X → El B) (FunGlueUKan0 _ x=0))
                                              ∘ fst-transport-Σ' {A = λ X → El X → El B} {B = λ X (_ : El X → El B) → El (D X)}
                                                                 (FunGlueUKan0 _ x=0) (unglue , g))
                                  (snd-transport-×' {A = λ X → El X → El B} {B = λ X → El (D X)} (FunGlueUKan0 _ x=0) (unglue , g))))

  DGlue-fun : ∀ {@♭ l : Level} (x : 𝟚)
                (A : U{l})
                (B : U{l})
                (f : El A → El B)
                →
                El (D (dua x A B f)) → El (dua x (D A) (D B) (D-func f))
  DGlue-fun x A B f g = glue _ _ _ _ (∨-elimd01 _ (λ x=0 → transport ElD (FunGlueUKan0 _ x=0) g)
                                                  (λ _ → D-func unglue g))
                                     (D-func unglue g , ∨-elimd01 _ (λ x=0 → ! (DGlue-eq0 x A B f g x=0)) (λ _ → id))

  postulate
    DGlue-eq : ∀ {@♭ l : Level} (x : 𝟚)
                 (A : U{l})
                 (B : U{l})
                 (f : El A → El B)
                 →
                 isIso (El (D (dua x A B f))) (El (dua x (D A) (D B) (D-func f))) (DGlue-fun x A B f)

  DGlue-η'' : ∀ {@♭ l : Level} (x : 𝟚)
                 (A : U{l})
                 (B : U{l})
                 (f : El A → El B)
                 →
                 El (dua x A B f) → (El (dua x A (D B) ((D-func f) o (η A))))
  DGlue-η'' x A B f g = glue _ _ _ _ (∨-elimd01 _ (λ x=0 → (coe (Glue-α _ _ _ _ (inl x=0)) g))
                                                  (λ _ → η B (unglue g)))
                                    (η B (unglue g)
                                    , ∨-elimd01 _ (λ x=0 → ap (η B) (unglue-α g (inl x=0))
                                                           ∘ ap (λ f → f (coe (Glue-α _ _ _ _ (inl x=0)) g)) (η-nat f))
                                                  (λ _ → id))

  DGlue-η' : ∀ {@♭ l : Level} (x : 𝟚)
                 (A : U{l})
                 (B : U{l})
                 (f : El A → El B)
                 →
                 El (dua x A B f) → (El (dua x (D A) (D B) (D-func f)))
  DGlue-η' x A B f g = glue _ _ _ _ (∨-elimd01 _ (λ x=0 → η A (coe (Glue-α _ _ _ _ (inl x=0)) g))
                                                 (λ _ → η B (unglue g)))
                                    (η B (unglue g)
                                    , ∨-elimd01 _ (λ x=0 → ap (η B) (unglue-α g (inl x=0))
                                                           ∘ ap (λ f → f (coe (Glue-α _ _ _ _ (inl x=0)) g)) (η-nat f)) (λ _ → id))

  DGlue-ηeq : ∀ {@♭ l : Level} (x : 𝟚)
                 (A : U{l})
                 (B : U{l})
                 (f : El A → El B)
                 →
                 (isIso.g (DGlue-eq x A B f) o (DGlue-η' x A B f)) == η (dua x A B f)
  DGlue-ηeq x A B f = λ= λ g → isIso.gf (DGlue-eq x A B f) (η (dua x A B f) g)
                               ∘ ap (isIso.g (DGlue-eq x A B f))
                                    (FunGlue= _ _ (λ x=0 → ! (glue-α _ _ (inl x=0))
                                                           ∘ het-to-hom (!h (transport-=h ElD (FunGlueUKan0 _ x=0))
                                                           ∘h apdo2 (λ X x → η X x)
                                                                    (! (FunGlueUKan0 _ x=0))
                                                                    (transport-=h (λ X → X) (Glue-α _ _ _ _ (inl x=0))))
                                                           ∘ glue-α _ _ (inl x=0))
                                                  (! (Glueβ _ _)
                                                  ∘ ! (ap (λ f → f g) (η-nat {A = dua x A B f} {B = B} unglue))
                                                  ∘ Glueβ _ _))

  Glue-isStack'' : ∀ {@♭ l : Level} (x : 𝟚)
                   {A : U{l}}
                   {B : U{l}}
                   (f : El A → El B)
                   (_ : El (isStack A))
                   (_ : El (isStack B))
                   → -------------------------
                   hasSection _ _ (DGlue-η'' x A B f)
  Glue-isStack'' x {A} {B} f stackA stackB = patch , path1 where  

    patchB = fst (isStack-to-QisStack stackB)
    patchB-eq = snd (isStack-to-QisStack stackB)
    
    pathb : (g : El (dua x A (D B) ((D-func f) o (η A)))) (x=0 : x == ``0)
            → Path (El B) (patchB (unglue g)) (f (coe (Glue-α _ _ _ _ (inl x=0)) g))
    pathb g x=0 = transport (λ g' → Path (El B) (patchB g') (f (coe (Glue-α _ _ _ _ (inl x=0)) g)))
                            (unglue-α g (inl x=0)
                              ∘ ap! (λ h → h (coe (Glue-α _ _ _ _ (inl x=0)) g)) (η-nat f))
                            (apPath (λ h → h (f (coe (Glue-α _ _ _ _ (inl x=0)) g))) patchB-eq)

    pathb' : (g : El (dua x A B f)) → Path (El B) (patchB (unglue (DGlue-η'' x A B f g))) (unglue g)
    pathb' g = transport! (λ g' →  Path (El B) (patchB g') (unglue g)) (Glueβ _ _) (apPath (λ h → h (unglue g)) patchB-eq)

    pathb-eq' : (g : El (dua x A B f)) (x=0 : x == ``0) → pathb' g =h pathb (DGlue-η'' x A B f g) x=0
    pathb-eq' g x=0 = !h (transport-=h (λ g' → Path (El B) (patchB g') (f (coe (Glue-α _ _ _ _ (inl x=0)) (DGlue-η'' x A B f g))))
                                       (unglue-α (DGlue-η'' x A B f g) (inl x=0)
                                       ∘ ap! (λ h → h (coe (Glue-α _ _ _ _ (inl x=0)) (DGlue-η'' x A B f g))) (η-nat f)))
                      ∘h apdo (λ h → apPath h patchB-eq)
                              (λ= λ h → ap h (ap f (! (glue-α _ _ (inl x=0)))
                                        ∘ ! (unglue-α g (inl x=0))))
                      ∘h transport-=h (λ g' →  Path (El B) (patchB g') (unglue g)) (! (Glueβ _ _))

    pathb-eq : (g : El (dua x A B f)) (x=0 : x == ``0) (i : I) → fst (pathb' g) i == fst (pathb (DGlue-η'' x A B f g) x=0) i 
    pathb-eq g x=0 i = het-to-hom (ap=o1 id {i} (fst (pathb' g))
                                         (fst (pathb (DGlue-η'' x A B f g) x=0))
                                         (pair=h-fst (λ=o1 (λ p → hom-to-het (ap (λ g' → (p `0 == patchB (unglue (DGlue-η'' x A B f g)))
                                                                                         × (p `1 == g'))
                                                                                 (ap f (! (glue-α _ _ (inl x=0)))
                                                                                 ∘ ! (unglue-α g (inl x=0))))))
                                                     (pathb-eq' g x=0)) i)

    fixb' : ∀ i (g : El (dua x A (D B) ((D-func f) o (η A)))) → _
    fixb' i g = (hcomEl B) `0 i (x == ``0)
                        (λ i x=0 → fst (pathb g x=0) i)
                        (patchB (unglue g)
                        , (λ x=0 → fst (snd (pathb g x=0))))

    fixb : (g : El (dua x A (D B) ((D-func f) o (η A)))) → _
    fixb = fixb' `1

    patch : El (dua x A (D B) ((D-func f) o (η A))) → El (dua x A B f)
    patch g = glue _ _ _ _
                   (∨-elimd01 _ (λ x=0 → coe (Glue-α _ _ _ _ (inl x=0)) g)
                                (λ _ → fst (fixb g)))
                   (fst (fixb g)
                   , ∨-elimd01 _ (λ x=0 → fst (snd (fixb g)) x=0 ∘ ! (snd (snd (pathb g x=0)))) (λ _ → id))

    patch-path : (g : El (dua x A B f)) → _
    patch-path g = !Path (hcomEl B) (apPath (λ f → f (unglue g)) patchB-eq)

    path-x=0 : (g : El (dua x A B f)) → (i j : I) → _
    path-x=0 g i j = (hcomEl B) `1 i ((j == `0) ∨ (j == `1))
                                (λ i → case01 (λ _ → fst (patch-path g) i)
                                              (λ _ → unglue g))
                                (fst (pathb' g) j
                                , ∨-elim01 _ (λ j=0 → ap! (fst (pathb' g)) j=0
                                                      ∘ ! (fst (snd (pathb' g)))
                                                      ∘ ap patchB (! (Glueβ _ _))
                                                      ∘ snd (snd (patch-path g)))
                                             (λ j=1 → ap! (fst (pathb' g)) j=1
                                                      ∘ ! (snd (snd (pathb' g)))))

    path-fixb : (g : El (dua x A B f)) → (i : I) → _
    path-fixb g i = (hcomEl B) `0 `1 ((x == ``0) ∨ ((i == `0) ∨ (i == `1)))
                             (λ j → case (λ x=0 → fst (path-x=0 g i j))
                                         (case01 (λ i=0 → fst (path-x=0 g i j))
                                                 (λ i=1 → fst (fixb' j (DGlue-η'' x A B f g))))
                                          (λ x=0 → ∨-elim01 _ (λ i=0 → id)
                                                              (λ i=1 → fst (snd (fixb' j (DGlue-η'' x A B f g))) x=0
                                                                       ∘ pathb-eq g x=0 j
                                                                       ∘ ! ((snd (snd (path-x=0 g i j))) (! i=1)))))
                             (fst (patch-path g) i
                             , ∨-elim _ (λ _ → ! (fst (snd (path-x=0 g i `0)) (inl id)))
                                        (∨-elim01 _ (λ i=0 → ! (fst (snd (path-x=0 g i `0)) (inl id)))
                                                    (λ i=1 → ap! (fst (patch-path g)) i=1
                                                             ∘ ! (snd (snd (patch-path g)))
                                                             ∘  ap patchB (Glueβ _ _)
                                                             ∘ ! (snd (snd (fixb' `0 (DGlue-η'' x A B f g))) id)))
                                        (λ _ _ → uip))
  
    path-unglue' : ∀ g → Path (El B) (unglue g) (fst (fixb (DGlue-η'' x A B f g)))
    path-unglue' g = (λ i → fst (path-fixb g i))
                     , ! (fst (snd (path-x=0 g `0 `1)) (inr id))
                       ∘ ! (fst (snd (path-fixb g `0)) (inr (inl id)))
                     , ! (fst (snd (path-fixb g `1)) (inr (inr id)))

    path1' : ∀ g → _
    path1' g = dua-path _ _
                      (λ x=0 → (λ _ → coe (Glue-α _ _ _ _ (inl x=0)) g)
                                      , id
                                      , !(glue-α _ _ (inl x=0)) ∘ ! (glue-α _ _ (inl x=0)))
                      (! (Glueβ _ _) =∘ path-unglue' g)
                      (λ i x=0 → fst (snd (path-fixb g i)) (inl x=0)
                                 ∘ fst (snd (path-x=0 g i `1)) (inr id)
                                 ∘ unglue-α g (inl x=0))

    path-unglue : ∀ g → Path (El B) (fst (fixb (DGlue-η'' x A B f g))) (unglue g)
    path-unglue g = !Path (hcomEl B) (path-unglue' g)

    path1 : ∀ g → _
    path1 g = !Path (hcomEl (dua x A B f)) (path1' g)
    

  Glue-isStack' : ∀ {@♭ l : Level} (x : 𝟚)
                   {A : U{l}}
                   {B : U{l}}
                   (f : El A → El B)
                   (_ : El (isStack A))
                   (_ : El (isStack B))
                   → -------------------------
                   hasSection _ _ (DGlue-η' x A B f)
  Glue-isStack' {l} x {A} {B} f stackA stackB = transport (El o fib1) (snd (snd η-abs1)) equiv where

    GlueΣpath : Path (Σ λ X → Σ (λ (f' : (El A → El X) × (El X → ElD A)) → Path _ (snd f' o fst f') (η A)))
                     (A , ((λ a → a) , η A) , idPath (η A))
                     (D A , (η A , (λ a → a)) , idPath (η A))
    GlueΣpath = ua-Σ-path' A (D A) (η A , stackA)

    η-fixb' : ∀ (X : U{l})
              (f1 : El A → El X)
              (f2 : El X → ElD A)
              (ηPath : Path _ (f2 o f1) (η A))
              (g : El (dua x A B f)) → (i : I) → _
    η-fixb' X f1 f2 ηPath g i = (hcomEl (D B)) `1 i (x == ``0)
                                               (λ z x=0 → (D-func f o (fst ηPath z)) (coe (Glue-α _ _ _ _ (inl x=0)) g))
                                               (η B (unglue g)
                                               , λ x=0 → ap (η B) (unglue-α g (inl x=0))
                                                         ∘ ap (λ f' → f' (coe (Glue-α _ _ _ _ (inl x=0)) g)) (η-nat f)
                                                         ∘ ap (λ f' → (D-func f o f') (coe (Glue-α _ _ _ _ (inl x=0)) g)) (snd (snd ηPath)))

    η-fixb : ∀ (X : U{l})
              (f1 : El A → El X)
              (f2 : El X → ElD A)
              (ηPath : Path _ (f2 o f1) (η A))
              (g : El (dua x A B f)) → _
    η-fixb X f1 f2 ηPath g = η-fixb' X f1 f2 ηPath g `0

    η-abs : ∀ (X : U{l})
              (f1 : El A → El X)
              (f2 : El X → ElD A)
              (ηPath : Path _ (f2 o f1) (η A))
              →
              El (dua x A B f) → (El (dua x X (D B) ((D-func f) o f2)))
    η-abs X f1 f2 ηPath g = glue _ _ _ _ (∨-elimd01 _ (λ x=0 → f1 (coe (Glue-α _ _ _ _ (inl x=0)) g))
                                                         (λ _ → fst (η-fixb X f1 f2 ηPath g)))
                                    (fst (η-fixb X f1 f2 ηPath g)
                                    , ∨-elimd01 _ (λ x=0 → fst (snd (η-fixb X f1 f2 ηPath g)) x=0
                                                           ∘ ap! (λ f' → (D-func f o f') (coe (Glue-α _ _ _ _ (inl x=0)) g)) (fst (snd ηPath)))
                                                  (λ _ → id))

    η-abs0b : ∀ g → Path (El (D B)) (fst (η-fixb A (λ a → a) (η A) (idPath (η A)) g)) (η B (unglue g))
    η-abs0b g = (λ i → fst (η-fixb' A (λ a → a) (η A) (idPath (η A)) g i)) , id , ! (snd (snd (η-fixb' A (λ a → a) (η A) (idPath (η A)) g `1)) id)

    η-abs1b : ∀ g → Path (El (D B)) (fst (η-fixb (D A) (η A) (λ a → a) (idPath (η A)) g)) (η B (unglue g))
    η-abs1b g = (λ i → fst (η-fixb' (D A) (η A) (λ a → a) (idPath (η A)) g i)) , id , ! (snd (snd (η-fixb' (D A) (η A) (λ a → a) (idPath (η A)) g `1)) id)

    η-abs0 : Path _ (η-abs A (λ a → a) (η A) (idPath (η A))) (DGlue-η'' x A B f)
    η-abs0 = funext (λ g → dua-path _ _ (λ x=0 → ((! (glue-α _ _ (inl x=0))) =∘ idPath (coe (Glue-α _ _ _ _ (inl x=0)) g)) ∘= (glue-α _ _ (inl x=0)))
                                        (((! (Glueβ _ _)) =∘ η-abs0b g) ∘= Glueβ _ _)
                                        (λ i x=0 → fst (snd (η-fixb' A (λ a → a) (η A) (idPath (η A)) g i)) x=0)) 

    η-abs1 : Path _ (η-abs (D A) (η A) (λ a → a) (idPath (η A))) (DGlue-η' x A B f)
    η-abs1 = funext (λ g → dua-path _ _ (λ x=0 → ((! (glue-α _ _ (inl x=0))) =∘ idPath (η A (coe (Glue-α _ _ _ _ (inl x=0)) g))) ∘= (glue-α _ _ (inl x=0)))
                                        (((! (Glueβ _ _)) =∘ η-abs1b g) ∘= Glueβ _ _)
                                        (λ i x=0 → fst (snd (η-fixb' (D A) (η A) (λ a → a) (idPath (η A)) g i)) x=0))

    fib : (X : (Σ λ X → Σ (λ (f' : (El A → El X) × (El X → ElD A)) → Path _ (snd f' o fst f') (η A)))) → _
    fib X = hasSection-code (dua x A B f) (dua x (fst X) (D B) ((D-func f) o (snd (fst (snd X))))) (η-abs (fst X) (fst (fst (snd X))) (snd (fst (snd X))) (snd (snd X)))

    fib0 : ∀ f' → U
    fib0 f' = hasSection-code (dua x A B f) (dua x A (D B) ((D-func f) o (η A))) f'

    fib1 : ∀ f' → U
    fib1 f' = hasSection-code (dua x A B f) (dua x (D A) (D B) ((D-func f))) f'

    equiv0 : El (fib0 (fst η-abs0 `0))
    equiv0 = fst (comEl' fib0 (fst η-abs0) `1 `0 ⊥ (λ _ → abort)
                    (transport! (El o fib0) (snd (snd η-abs0)) (Glue-isStack'' x f stackA stackB) , λ ff → abort ff))

    equiv1 : El (fib (fst GlueΣpath `1))
    equiv1 = fst (comEl' fib
                         (fst GlueΣpath) `0 `1 ⊥ (λ _ → abort)
                         (transport! (El o fib) {M = fst GlueΣpath `0} {N = (A , ((λ a → a) , η A) , idPath (η A))}
                                     ((fst (snd GlueΣpath)))
                                     (transport (El o fib0) (fst (snd η-abs0)) equiv0)
                         , (λ ff → abort ff)))

    equiv : El (fib1 (fst η-abs1 `1))
    equiv = fst (comEl' fib1 (fst η-abs1) `0 `1 ⊥ (λ _ → abort)
                   (transport! (El o fib1)
                               (fst (snd η-abs1))
                               (transport (El o fib) (snd (snd GlueΣpath)) equiv1)
                   , λ ff → abort ff))

  Glue-isStack : ∀ {@♭ l : Level} (x : 𝟚)
                   {A : U{l}}
                   {B : U{l}}
                   (f : El A → El B)
                   (_ : El (isStack A))
                   (_ : El (isStack B))
                   → -------------------------
                   El (isStack (dua x A B f))
  Glue-isStack x {A} {B} f stackA stackB = QisStack-to-isStack (fst sec , funext (snd sec)) where

    sec' : hasSection _ _ (isIso.g (DGlue-eq x A B f) o DGlue-η' x A B f)
    sec' = fst (Glue-isStack' x f stackA stackB) o (DGlue-fun x A B f)
           , (λ g → transport! (λ h → Path _ ((fst (Glue-isStack' x f stackA stackB) o h o DGlue-η' x A B f) g) g)
                               (λ= (isIso.fg (DGlue-eq x A B f)))
                               (snd (Glue-isStack' x f stackA stackB) g))

    sec : hasSection _ _ (η (dua x A B f))
    sec = transport (hasSection _ _) (DGlue-ηeq x A B f) sec'
                         
  Glue-patch : ∀ {@♭ l : Level} (x : 𝟚)
                 {A : U{l}}
                 {B : U{l}}
                 (f : El A → El B)
                 (_ : El (isStack A))
                 (_ : El (isStack B))
                 → ---------------------------------------
                 ElD (dua x A B f) → El (dua x A B f)
  Glue-patch {l} x {A} {B} f stackA stackB = getPatch (Glue-isStack x f stackA stackB)

