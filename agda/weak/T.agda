
{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;lzero;_⊔_)
open import Lib
open import Interval
open import weak.Cofibs
open import Prop
open import weak.Kan
open import weak.Retraction


module weak.T where

  -- T types suggested by Andrew Swan

  -- slice over r : I
  module _ (r : I) where
    postulate
      T : Set
      inlT : I → T
      inrT : I → T
      push : inlT `1 == inrT r
      caseT : ∀ {l} {A : Set l} → (f : I → A) → (g : I → A) → (f `1 == g r) → (T → A)
      caseT-inl : ∀ {l} {A : Set l} → {f : I → A} → {g : I → A} → {e : _} {x : I}
               → caseT f g e (inlT x) == f x
      caseT-inr : ∀ {l} {A : Set l} → {f : I → A} → {g : I → A} → {e : _} {x : I}
               → caseT f g e (inrT x) == g x
      {-# REWRITE caseT-inl #-}
      {-# REWRITE caseT-inr #-}
    -- FIXME generalize
      Telimprop : ∀ {l} (A : T → Set l) → (f : (x : I) → A (inlT x)) → (g : (y : I) → A (inrT y)) → ((x : T) (a b : A x) → a == b) → (x : T) → A x
{-
    ∨-elim-inl : ∀ {l} (A : α ∨ β → Set l) → (f : (x : α) → A (inl x)) → (g : (y : β) → A (inr y)) → (h : (x : α) (y : β) → transport A (trunc) (f x) == g y) 
               → (x : α) → ∨-elim A f g h (inl x) == f x
    ∨-elim-inr : ∀ {l} (A : α ∨ β → Set l) → (f : (x : α) → A (inl x)) → (g : (y : β) → A (inr y)) → (h : (x : α) (y : β) → transport A (trunc) (f x) == g y) 
               → (x : β) → ∨-elim A f g h (inr x) == g x 
    -- trunc-same : {x : α ∨ β} → trunc {x} {x} == id
    {-# REWRITE ∨-elim-inl #-}
    {-# REWRITE ∨-elim-inr #-}
    -- {-# REWRITE trunc-same #-}
-}

  -- the map 1 → T
  inrr : ∀ {r} → T r
  inrr {r} = inrT r r
  
  -- the map T → I
  unT : (r : I) → T r → I
  unT r = caseT r (\ _ → r) (\ y → y) id

  unT2 : (r : I) -> T r -> I
  unT2 r = caseT r (\x -> x) (\_ -> `1) id

  applyT : {l : Level} (r : I) → (A : T r → Set l) → ((x : T r) -> A x) -> A inrr
  applyT r A f = f inrr

  postulate
    isCofibT : (r : I) (y : T r) → isCofib (y == inrr)
    isCofibT2 : (r : I) (y : T r) → isCofib (unT2 r y == `1)

  hasComT : ∀ {l} → ((x : I) → T x → Set l) → Set (lsuc lzero ⊔ l)
  hasComT A = (r : I) (b : (A r inrr))
            → ContractibleFill( (t : T r) → A r t [ t == inrr  ↦ (\ r=x → transport (A r) (! r=x) b ) ])

  SFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  SFiber f b = Σ \a → (f a) == b

  hasComT2 : ∀ {l} → ((x : I) → T x → Set l) → Set (lsuc lzero ⊔ l)
  hasComT2 A = (r : I) (a : A r inrr) → ContractibleFill (SFiber (applyT r (A r)) a) 

  hasSCom : ∀ {l} → ((x : I) → Set l) → Set (lsuc lzero ⊔ l)
  hasSCom A = (r : I) (a : A r) → ContractibleFill (SFiber (apply A r) a) 

  test : ∀ {l : Level} {A : (x : I) → T x → Set l} → hasComT2 A == hasComT A
  test {A = A} = {!    !}

  test2 : ∀ {l : Level} (A : I → Set l) → hasComT2 (\ x t → A (unT2 x t)) → hasSCom A
  test2 A comt r a = {!unT2 r!} where
    c = {! (applyT r (λ t → A (unT r t))) !}

    d : (SFiber (applyT r (λ t → A (unT r t))) a) → (SFiber (apply A r) a)
    d t = (λ x → fst t (inrT r x)) , snd t

    e : (SFiber (apply A r) a) → (SFiber (applyT r (λ t → A (unT r t))) a) 
    e i = (\ x → fst i (unT r x)) , snd i

    ed : (x : _) → d (e x) == x
    ed x = id

    ret : Retraction (SFiber (applyT r (λ t → A (unT r t))) a) (SFiber (apply A r) a)
    ret = retract d e {!ed!}

    de : (x : (SFiber (applyT r (λ t → A (unT r t))) a)) → e (d x) == x
    de x = pair= {!inrT r o unT r!} uip

