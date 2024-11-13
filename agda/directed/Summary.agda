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
open import universe.Univalence -- TODO: cleanup uaη
open import universe.Pi
open import universe.Sigma
open import universe.Path

open import directed.DirInterval

open import directed.Covariant
import directed.Covariant-is-Fibrant
open import directed.UCov 

open import directed.universe.Pi 
open import directed.universe.Sigma 
open import directed.universe.Path
open import directed.universe.Hom

-- UCov is Kan and path univalent
open import directed.universe.Glue-Equiv-Covariant
open import directed.universe.UCov-Com
open import directed.UCov-Univalence

-- directed univalence retraction for UCov
open import directed.universe.FunGlueKan
open import directed.universe.FunGlue   
open import directed.DirUnivalenceReflection 

open import directed.descent.Lex 
open import directed.descent.Pi
open import directed.descent.Sigma 
open import directed.descent.Path
open import directed.descent.Hom
open import directed.descent.FunGlue
import directed.UCovStack

-- directed univalence reflection for UCovStack
open import directed.DirUnivalenceReflectionStack -- FIXME 

-- other stuff that is mentioned at least a little in the paper:
-- filling problem reformulations, etc.
import directed.Segal
import directed.SegalDepCovariant
import directed.Sigma
import directed.Discrete             -- FIXME: could use a cleanup
                                     -- how much of the commented out stuff do we intended to finish? not sure what it is

-- not mentioned in the paper
import directed.universe.FunWeldCov
  -- Weld types are also covariant
  -- it seems like absent the stack refinement there might be initial and final ways
  -- of making a function into a morphism

{-
  todo: add paper specefic summary with names from paper
-}

module directed.Summary where
  open Layered

  UKan : (@♭ l : Level) → Set _
  UKan l = U{l}

  UKan-code : (@♭ l : Level) → UKan _
  UKan-code l = U-code{l}

  El-UKan-eq : (@♭ l : Level) → El (UKan-code l) == UKan l
  El-UKan-eq l = id
  

  UCovStack : (@♭ l : Level) → Set _
  UCovStack = directed.UCovStack.UCovStack

  ElCovStack : {@♭ l : Level} → UCovStack l → UKan l
  ElCovStack = directed.UCovStack.ElCovStack

  ElCS : {@♭ l : Level} → UCovStack l → Set l
  ElCS = directed.UCovStack.ElCS

  UCovStack-code : (@♭ l : Level) → UKan _
  UCovStack-code = directed.UCovStack.UCovStack-code

  El-UCovStack-eq : (@♭ l : Level) → El (UCovStack-code l) == UCovStack l
  El-UCovStack-eq l = id



  Π-Kan-code : {@♭ l : Level}
               (A : UKan l)
               (B : El A → UKan l)
               →
               UKan l
  Π-Kan-code A B = Πcode-universal (A , B)

  Π-Kan-eq : {@♭ l : Level}
               (A : UKan l)
               (B : El A → UKan l)
               →
               El (Π-Kan-code A B) == ((a : El A) → El (B a))
  Π-Kan-eq A B = id

  Π-CovStack-code : {@♭ l : Level}
                    (@♭ A : UKan l)
                    (B : El A → UCovStack l)
                    →
                    UCovStack l
  Π-CovStack-code A B = ΠUCov A (fst o B) , ΠisStack {A = A} (ElCovStack o B) (λ a → snd (B a))

  Π-CovStack-eq : {@♭ l : Level}
                    (@♭ A : UKan l)
                    (B : El A → UCovStack l)
                    →
                    ElCS (Π-CovStack-code A B) == ((a : El A) → ElCS (B a))
  Π-CovStack-eq A B = id


  Σ-Kan-code : {@♭ l : Level}
               (A : UKan l)
               (B : El A → UKan l)
               →
               UKan l
  Σ-Kan-code A B = Σcode-universal (A , B)

  Σ-Kan-eq : {@♭ l : Level}
               (A : UKan l)
               (B : El A → UKan l)
               →
               El (Σ-Kan-code A B) == (Σ λ (a : El A) → El (B a))
  Σ-Kan-eq A B = id

  Σ-CovStack-code : {@♭ l : Level}
                    (A : UCovStack l)
                    (B : ElCS A → UCovStack l)
                    →
                    UCovStack _
  Σ-CovStack-code A B = Σcode-cov-universal (fst A , fst o B) , ΣisStack {A = ElCovStack A} (ElCovStack o B) (snd A) (λ a → snd (B a))

  Σ-CovStack-eq : {@♭ l : Level}
                    (A : UCovStack l)
                    (B : ElCS A → UCovStack l)
                    →
                    ElCS (Σ-CovStack-code A B) == (Σ λ (a : ElCS A) → ElCS (B a))
  Σ-CovStack-eq A B = id


  Path-Kan-code : {@♭ l : Level}
                  (A : I → UKan l)
                  (a0 : El (A `0))
                  (a1 : El (A `1))
                  →
                  UKan l
  Path-Kan-code A a0 a1 = universe.Path.Path-code-universal (A , a0 , a1)
  
  Path-Kan-eq : {@♭ l : Level}
                (A : I → UKan l)
                (a0 : El (A `0))
                (a1 : El (A `1))
                →
                El (Path-Kan-code A a0 a1) == PathO (El o A) a0 a1
  Path-Kan-eq A a0 a1 = id
{-
  -- TODO: make dependent
  Path-CovStack-code : {@♭ l : Level}
                       (A : UCovStack l)
                       (a0 a1 : ElCS A)
                       →
                       UCovStack l
  Path-CovStack-code A a0 a1 = {!!}
-}

  Hom-Kan-code : {@♭ l : Level}
                 (A : 𝟚 → UKan l)
                 (a0 : El (A ``0))
                 (a1 : El (A ``1))
                 →
                 UKan l
  Hom-Kan-code A a0 a1 = Hom-code-universal (A , a0 , a1)

  Hom-Kan-eq : {@♭ l : Level}
               (A : 𝟚 → UKan l)
               (a0 : El (A ``0))
               (a1 : El (A ``1))
               →
               El (Hom-Kan-code A a0 a1) == HomO (El o A) a0 a1
  Hom-Kan-eq A a0 a1 = id

  Hom-CovStack-code : {@♭ l : Level}   -- TODO: make dependent 
                      (A : UCovStack l)
                      (a0 a1 : ElCS A)
                      →
                      UCovStack l
  Hom-CovStack-code A a0 a1 = Hom-code-cov-universal (fst A , a0 , a1) , Hom-isStack (ElCovStack A) a0 a1 (snd A)
  
  Hom-CovStack-eq : {@♭ l : Level}
                    (A : UCovStack l)
                    (a0 a1 : ElCS A)
                    →
                    ElCS (Hom-CovStack-code A a0 a1) == Hom (ElCS A) a0 a1
  Hom-CovStack-eq A a0 a1 = id


  FunGlue-CovStack-code : {@♭ l : Level}
                          (A B : UCovStack l)
                          (f : ElCS A → ElCS B)
                          (i : 𝟚)
                          →
                          UCovStack l
  FunGlue-CovStack-code A B f i = FunGlueUCov (fungluedata (fst A) (fst B) f i) , Glue-isStack i f (snd A) (snd B)
  
  FunGlue-CovStack-eq : {@♭ l : Level}
                          (A B : UCovStack l)
                          (f : ElCS A → ElCS B)
                          (i : 𝟚)
                          →
                          ElCS (FunGlue-CovStack-code A B f i) == duafun-cov (fungluedata (fst A) (fst B) f i)
  FunGlue-CovStack-eq A B f i = id


  ua-Kan : {@♭ l : Level}
                (A B : UKan l)
                →
                Equiv (Equiv (El A) (El B)) (Path (UKan l) A B)
  ua-Kan A B = {!!}

  -- define / include equiv-to-path  and path-to-equiv
  ua-CovStack : {@♭ l : Level}
                (A B : UCovStack l)
                →
                Equiv (Equiv (ElCS A) (ElCS B)) (Path (UCovStack l) A B)
  ua-CovStack A B = {!!}

  dua-CovStack : {@♭ l : Level}
                (A B : UCovStack l)
                →
                Equiv (ElCS A → ElCS B) (Hom (UCovStack l) A B)
  dua-CovStack A B = {!!}


