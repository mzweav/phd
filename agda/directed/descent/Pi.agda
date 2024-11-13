{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import Path
open import Equiv
open import Kan
open import universe.Universe
open import universe.U
open import universe.Pi
open import directed.descent.Lex

module directed.descent.Pi where

  Πpatch : ∀ {@♭ l : Level} {A : U{l}}
               (B : El A → U{l})
               (_ : (a : El A) → El (D (B a)) → El (B a))
               → --------------------------------------
               El (D (Πcode-universal (A , λ a → B a))) → (a : El A) → El (B a)
  Πpatch B Bpatch f a = ((Bpatch a) o (D-func (λ f → f a))) f

  ΠisStack : ∀ {@♭ l : Level} {A : U{l}}
               (B : El A → U{l})
               (_ : (a : El A) → El (isStack (B a)))
               → --------------------------------------
               El (isStack (Πcode-universal (A , λ a → B a)))
  ΠisStack {l} {A} B Bstack = QisStack-to-isStack (Πp , funext (λ f → funext (eq f))) where

    pB : ∀ a → El (D (B a)) → El (B a)
    pB a = fst (isStack-to-QisStack (Bstack a))

    pBeq : ∀ a → _
    pBeq a = snd (isStack-to-QisStack (Bstack a))

    Πp : _
    Πp = Πpatch {l} {A} B (λ a → pB a)

    h1 : ∀ (f :  (a : El A) → El (B a)) a → ((Πp o (η _)) f) a == ((pB a o ((η (B a)) o (λ f → f a))) f)
    h1 f a = ap (λ x → (pB a o x) f) (η-nat (λ f → f a)) 

    eq : ∀ f a → Path (El (B a)) (Πp (η _ f) a) (f a)
    eq f a = apPath (λ x → (x o (λ f₁ → f₁ a)) f) (pBeq a) ∘= h1 f a

  
