{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (_⊔_;Level)
open import Lib 
open import Interval 
open import Proposition

module Cofibs where

  ⊤ = Unit
  _∧_ = _×_
  ∀i : (I → Set) → Set
  ∀i α = (x : I) → α x

  -- this way we can't do cofib-induction... 
  postulate 
    isCofib : Set → Set 
    isCofib⊥ : isCofib ⊥
    isCofib∨ : ∀ {α β} → isCofib α → isCofib β → isCofib (α ∨ β)
    isCofib= : ∀ {r r' : I} → isCofib (r == r')
    isCofib∀ : ∀ {α : I → Set} → ((x : I) → isCofib (α x)) → isCofib (∀i α)
    -- almost never needed this: so far only used in Glue-HCom-NoCofib
    -- which is only used for the directed stuff
    isCofib-prop : ∀ {A : Set} → (p q : isCofib A) → p == q

  record Cofib (α : Set) : Set where
    constructor cofib
    field 
      is : isCofib α
      eq : (x y : α) → x == y

  Cofib-prop : ∀ {α} {p q : Cofib α} → p == q
  Cofib-prop = ap2 cofib (isCofib-prop _ _) (λ= \ _ → λ= \ _ → uip)

  Cofibs : Set1
  Cofibs = Σ \ α → Cofib α

  instance
    Cofib⊥ : Cofib ⊥
    Cofib⊥ = cofib isCofib⊥ (\ ())

    Cofib∨ : ∀ {α β} → {{_ : Cofib α}} → {{_ : Cofib β}} → Cofib (α ∨ β)
    Cofib∨ {_} {_} {{cofib cα eqα}} {{cofib cβ eqβ}} = cofib (isCofib∨ cα cβ) (\ _ _ → trunc)

    Cofib= : ∀ {r r' : I} → Cofib (r == r')
    Cofib= = cofib (isCofib=) (\ _ _ → uip)
  
    Cofib∀ : ∀ {α : I → Set} → {_ : (x : I) → Cofib (α x)} → Cofib ((x : I) → α x)
    Cofib∀ {_} {cα} = cofib (isCofib∀ (\ x → Cofib.is (cα x))) (\ x y → λ= \ a → Cofib.eq (cα a) _ _ ) 

  extends : ∀ {l} (α : Set) {A : Set l} → {{_ : Cofib α}} → (t : α → A) (b : A) → Set l
  extends {_} α t b = (x : α) → t x == b

  _[_↦_] : ∀ {l} (A : Set l) (α : Set) → {{cα : Cofib α}} → (t : α → A) → Set l
  A [ α ↦ t ] = Σ \ b → extends _ t b

  _[_↦_]e : ∀ {l} (A : Set l) (α : Cofibs) → (t : fst α → A) → Set l
  A [ α ↦ t ]e = Σ \ b → extends _ {{snd α}} t b

  -- less annoying than using an or?  or maybe just saving the pain for later
  -- no compat necessary because they're both subobjects of the same thing
  _[_↦_,_↦_] : ∀ {l : Level} (A : Set l) (α : Set) {{_ : Cofib α}} (t : α → A) (β : Set) {{_ : Cofib β}} (s : β → A) → Set l
  A [ α ↦ t , β ↦ s ] = Σ \ b → (extends _ t b) × (extends _ s b)

  _[_↦_,_↦_,_↦_] : ∀ {l : Level} (A : Set l) (α : Set) {{_ : Cofib α}} (t : α → A) (β : Set) {{_ : Cofib β}} (s : β → A) (γ : Set) {{_ : Cofib γ}} (s : γ → A) → Set l
  A [ α ↦ t , β ↦ s , γ ↦ r ] = Σ \ b → (extends _ t b) × ((extends _ s b) × (extends _ r b))

  
