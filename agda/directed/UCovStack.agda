{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import universe.Universe
open import universe.U
open import universe.Sigma 
open import directed.DirInterval
open import directed.descent.Lex
open import directed.UCov
open import directed.universe.UCov-Com


module directed.UCovStack where

  open Layered

  UCovStack : (@♭ l : Level) → Set _
  UCovStack l = Σ λ (X : UCov l) → El (isStack (ElCov X))

  ElCovStack : {@♭ l : Level} → UCovStack l → U{l}
  ElCovStack = ElCov o fst

  ElCS : {@♭ l : Level} → UCovStack l → Set l
  ElCS = ElC o fst

  UCovStack-code : (@♭ l : Level) → U
  UCovStack-code l = Σcode-universal (UCovU l , λ X → isStack (ElCov X))

  dcoestack : {@♭ l : Level} (A B : UCovStack l) → (p : Hom _ A B) → ElCS A → ElCS B
  dcoestack A B p = dcoe (fst A) (fst B) (apHom fst p)


