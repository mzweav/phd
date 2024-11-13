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
open import universe.U
open import universe.Univalence
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import directed.Covariant
open import directed.UCov
open import directed.universe.UCov-Com
open import directed.descent.Lex
open import directed.descent.Pi
open import directed.descent.Sigma
open import directed.descent.Path

module directed.descent.Univ where

  open Layered

  postulate
    D-lex : ∀ {l1 l2 :{♭} Level} {A : U{l1}} -- is this alright to postulate?
              (B : El A → U{l2})
              (X : U{lmax l2 l1})
              →
              Path U X (Σcode-universal (A , B)) → Path U (D X) (Σcode-universal (D A , dD B))

  Stack-fam : ∀ {l1 l2 :{♭} Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : Path U (Σcode-universal (A , B)) (Σcode-universal (A , dD B o η A))) -- is equiv gap map
               → ----------------------------
               (a : El A) → El (isStack (B a))
  Stack-fam {l1} {l2} {A} B p a = QisStack-to-isStack (patch , {!!}) where

    path : Path U (Σcode-universal (A , B)) (Σcode-universal (A , D o B))
    path = transport! (λ F → Path U (Σcode-universal (A , B)) (Σcode-universal (A , F))) (ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq) p

    pA : Equiv (El A) (El A)
    pA = {!!} 

    f : Σ (El o B) → Σ (El o D o B)
    f (a , b) = (a , (η (B a) b))

    gcom : ∀ ab → _
    gcom ab = comEl (fst path) `1 `0 ⊥ (λ _ → abort) (transport! El (snd (snd path)) ab , λ ff → abort ff)

    g : Σ (El o D o B) → Σ (El o B)
    g ab = (transport El (fst (snd path)) (fst (gcom ab)))

    eqv : QEquiv (Σ (El o B)) (Σ (El o D o B))
    eqv = f , g , {!!} , {!!}

    patch : (b : ElD (B a)) → El (B a)
    patch b = {!(ap! (_o_ L) (η-nat {A = A} {U-code{l2}} B) ∘ ap! (λ f → f o B) L-eq)!}


  dDisStack : ∀ {l1 l2 :{♭} Level} {A : U{l1}}
               (B : El A → U{l2})
               (_ : (a : El A) → El (isStack (B a)))
               →
               (a : El (D A)) → El (isStack (dD B a))
  dDisStack {l1} {l2} {A} B stackB = Stack-fam {A = D A} (dD B) path where

    eq : (dD (dD B o η A)) == (dD (dD B) o D-func (η A))
    eq = ap (λ g → L o g) (D-comp {A = A} {B = D A} {C = U-code} (dD B) (η A))

    path1 : Path U (Σcode-universal (D A , dD B)) (D (Σcode-universal (A , B)))
    path1 = ua (Iso-Equiv (hcomEl (Σcode-universal (D A , dD B)))
                          (hcomEl (D (Σcode-universal (A , B))))
                          (iso (isIso.g (DΣ-eq B))
                               (DΣ-fun B)
                               (isIso.fg (DΣ-eq B))
                               (isIso.gf (DΣ-eq B))))

    path2 : Path U (D (Σcode-universal (A , B))) (Σcode-universal (D A , (dD (dD B) o D-func (η A))))
    path2 = ap (λ F → Σcode-universal (D A , F)) eq =∘ D-lex (dD B o η A) (Σcode-universal (A , B)) (DΣ-Path B stackB)

    path3 : Path U (Σcode-universal (D A , (dD (dD B) o D-func (η A)))) (Σcode-universal (D A , dD (dD B) o η (D A)))
    path3 = apPath (λ g → Σcode-universal (D A , (dD (dD B) o g))) (η-path A)

    path : Path U (Σcode-universal (D A , dD B)) (Σcode-universal (D A , dD (dD B) o η (D A)))
    path = ∘Path (hcomEl (U-code{lmax l2 l1})) path3 (∘Path (hcomEl (U-code{lmax l2 l1})) path2 path1)

  UStack : ∀ {l :{♭} Level} → U{_}
  UStack {l} = Σcode-universal (U-code{l} , λ X → isStack X)

  UStack-isStack : ∀ {l :{♭} Level} → El (isStack (UStack{l})) 
  UStack-isStack {l} = QisStack-to-isStack (patch , patch-path) where

    p : Path (El (UStack {l}) → U) (D o fst) fst
    p = funext (λ X → !Path (hcomEl (U-code{l})) (ua (η (fst X) , snd X)))

    patch : El (D (UStack{l})) → El (UStack{l})
    patch X = dD fst X , dDisStack fst snd X

    eq : (fst o patch o η (UStack{l})) == (D o fst)
    eq = λ= λ X → ap (λ f → (f o fst) X) (L-eq{l})
                  ∘ ap {M = (D-func fst) o (η UStack)} {N = (η (U-code{l})) o fst} (λ f → L (f X))
                       (η-nat {A = UStack{l}} {B = U-code} (fst {A = U} {λ X → El (isStack X)}))

    p' : Path (El (UStack {l}) → U) (fst o patch o η (UStack{l})) fst
    p' = (transport! (λ f → Path _ f fst) eq p)

    patch-path : Path _ (patch o η (UStack{l})) (λ X → X)
    patch-path = funext (λ X → hembedding-path {A = U-code{l}} {P = isStack}
                                               isStack-is-HProp
                                               (apPath (λ f → f X) p'))
