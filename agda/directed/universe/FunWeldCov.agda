{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Proposition
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Cofibs
open import Kan
open import Path
open import Interval
open import universe.Sigma
open import Glue
open import directed.Covariant
open import Glue-Weak
import Glue-Com-NoCofib
open import universe.Universe
open import directed.UCov
open import FibWeld
open import FWeld-Weak

module directed.universe.FunWeldCov where

  open Layered

  dua-α' : 𝟚 → Set
  dua-α' = (\ x → ((x == ``0) ∨ (x == ``1)))

  module _ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) where
    dua-α = dua-α' x

    dua-T  : dua-α → Set l1
    dua-T = (cased01 (\ _ → A) (\ _ → B))

    dua-B = A

    dua-f : (p : dua-α) → dua-B → dua-T p 
    dua-f = (∨-elimd01 _ (\ _ x → x) (\ _ → f) )

  preduafun : ∀ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) → Set l1
  preduafun x A B f = Weld (dua-α x A B f) (dua-T x A B f) (dua-B x A B f) (dua-f x A B f)
  -- FIXME really need a Weld that has dhcom constructors as well...
  --       eliminator should require covariance

  duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
           (x : Γ → 𝟚) (A : Γ → Set l2) (B : Γ → Set l2)
           (f : (θ : Γ) → A θ → B θ)
           → Γ → Set l2
  duaF {Γ = Γ} x A B f θ = preduafun (x θ) (A θ) (B θ) (f θ)

  -- this proof seems like it should generalize to
  -- x ⊢ Glue (α(x) ∨ β(x) ↦ f ∨ g) where
  --   (α ``1) → α y for all y
  --   g is an equivalence


  -- **********************************************************************
  -- main idea is here: covariance of function welding

  -- copy and paste of Kan.f-natural and changed to 𝟚 instead of I and specialized to 0/1
  f-dnatural : ∀ {l} {A B : 𝟚 → Set l} (f : (x : 𝟚) → A x → B x)
            → (dcoeA : hasDCoe A)
            → (dcomB : relCov B)
            → (a : A ``0) 
            → Path (B ``1) (f ``1 (fst (dcoeA ``1 a))) (fst (relCov-relDCoe B dcomB (\ x → x) ``1 (f ``0 a))) 
  f-dnatural {B = B} f dcoeA dcomB a = 
    (((\ x → fst (usecom x)) , 
     (! (fst (snd (usecom `0)) (inl id))) , 
     ! (fst (snd (usecom `1)) (inr id)))) where
   usecom : (x : I) → _
   usecom x = dcomB (\ z → z) ``1
                    ((x == `0) ∨ (x == `1)) 
                     (\ z → case (\ x=0 → f z (fst (dcoeA z a)))
                                  (\ x=1 → fst (relCov-relDCoe B dcomB (\ x → x) z (f ``0 a)))
                                  (\ p q → abort (iabort (q ∘ ! p)))) 
                     (f ``0 a , ∨-elim _ (\ x=0 →  ap (f ``0) (! ((snd (dcoeA ``0 a)) id)))
                                         (\ x=1 → ! (snd (relCov-relDCoe B dcomB (\ x → x) ``0 (f ``0 a)) id)) (\ _ _ → uip))

  relDCoe-duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
               (x : Γ → 𝟚)
               (A B : Γ → Set l2)
               (f : (θ : Γ) → A θ → B θ)
               → relCov A
               → relCov B
               → relDCoe1 (duaF x A B f)
  relDCoe-duaF x A B f dcomA dcomB p = 
     WRec-Weak.wrec-weak _
                         {!really need dhcom B too!}
                         (\ a → win _ _ _ _ (fst (relCov-relDCoe A dcomA p ``1 a)))
                         (∨-elimd01 _ (\ xp0=0 → \ a → win _ _ _ _ (fst (relCov-relDCoe A dcomA p ``1 a)))
                                      (\ xp0=1 → \ b → coe (! (Weld-α _ _ _ _ (inr ((usemono xp0=1)))))
                                                           (fst (relCov-relDCoe B dcomB p ``1 b) )))
                         (\ a → ∨-elimd01 _ (\ xp0=0 →
                                               (\ _ → (win _ _ _ _ ((fst (relCov-relDCoe A dcomA p ``1 a))))) ,
                                                      id ,
                                                      id)
                                            (\ xp0=1 →
                                               (\ z → coe (! (Weld-α _ _ _ _ (inr ((usemono xp0=1)))))
                                                           (fst (nat a) z)) ,
                                                      (win-α! _ _ _ _ _ (inr (usemono xp0=1))) ∘
                                                      ap (coe (! (Weld-α _ _ _ _ _))) (fst (snd (nat a))) , 
                                                      ap (coe (! (Weld-α _ _ _ _ _))) (snd (snd (nat a))))) where

       -- FIXME: dcomPre is only for the universe apparently, so its inlined here 
       nat : ∀ a → _
       nat = f-dnatural {A = A o p} {B = B o p} (\ x → f (p x))
                        (relCov-relDCoe {Γ = 𝟚} (A o p) (\ q → dcomA (p o q)) (( \ x → x))) ((\ q → dcomB (p o q)))
  
       usemono : x (p ``0) == ``1 → x (p ``1) == ``1
       usemono eq = diantisym id (transport (\ H → H ≤ x (p ``1)) eq (dimonotonicity≤ (x o p) ``0 ``1 id))


