{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (_⊔_;Level)
open import Lib 
open import Interval 
open import Prop public

module weak.Cofibs where

  ⊤ = Unit
  _∧_ = _×_
  ∀i : (I → Set) → Set
  ∀i α = (x : I) → α x

  -- this way we can't do cofib-induction... 
  postulate 
    isCofib : Set → Set 
    isCofib⊥ : isCofib ⊥
    isCofib∨ : ∀ {α β} → isCofib α → isCofib β → isCofib (α ∨ β)
    isCofib=0 : ∀ {r : I} → isCofib (r == `0)
    isCofib=1 : ∀ {r : I} → isCofib (r == `1)
    isCofib=0r : ∀ {r : I} → isCofib (`0 == r)
    isCofib=1r : ∀ {r : I} → isCofib (`1 == r)
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

    Cofib∨ : ∀ {α β} → Cofib α → Cofib β → Cofib (α ∨ β)
    Cofib∨ (cofib cα eqα) (cofib cβ eqβ) = cofib (isCofib∨ cα cβ) (\ _ _ → trunc)

    Cofib=0 : ∀ {r : I} → Cofib (r == `0)
    Cofib=0 = cofib (isCofib=0) (\ _ _ → uip)

    Cofib=01 : Cofib (`0 == `1)
    Cofib=01 = cofib (isCofib=1) (\ _ _ → uip)

    Cofib=1 : ∀ {r : I} → Cofib (r == `1)
    Cofib=1 = cofib (isCofib=1) (\ _ _ → uip)

    Cofib=0r : ∀ {r : I} → Cofib (`0 == r)
    Cofib=0r = cofib (isCofib=0r) (\ _ _ → uip)

    Cofib=1r : ∀ {r : I} → Cofib (`1 == r)
    Cofib=1r = cofib (isCofib=1r) (\ _ _ → uip)
  
    Cofib∀ : ∀ {α : I → Set} → ((x : I) → Cofib (α x)) → Cofib ((x : I) → α x)
    Cofib∀ cα = cofib (isCofib∀ (\ x → Cofib.is (cα x))) (\ x y → λ= \ a → Cofib.eq (cα a) _ _ ) 

  extends : ∀ {l} (α : Set) {A : Set l} → (t : α → A) (b : A) → Set l
  extends {_} α t b = (x : α) → t x == b

  _[_↦_] : ∀ {l} (A : Set l) (α : Set) → (t : α → A) → Set l
  A [ α ↦ t ] = Σ \ b → extends _ t b

  _[_↦_]e : ∀ {l} (A : Set l) (α : Cofibs) → (t : fst α → A) → Set l
  A [ α ↦ t ]e = Σ \ b → extends _ t b

  -- less annoying than using an or?  or maybe just saving the pain for later
  -- no compat necessary because they're both subobjects of the same thing
  _[_↦_,_↦_] : ∀ {l : Level} (A : Set l) (α : Set) (t : α → A) (β : Set) (s : β → A) → Set l
  A [ α ↦ t , β ↦ s ] = Σ \ b → (extends _ t b) × (extends _ s b)

  _[_↦_,_↦_,_↦_] : ∀ {l : Level} (A : Set l) (α : Set) (t : α → A) (β : Set) (s : β → A) (γ : Set) {{_ : Cofib γ}} (s : γ → A) → Set l
  A [ α ↦ t , β ↦ s , γ ↦ r ] = Σ \ b → (extends _ t b) × ((extends _ s b) × (extends _ r b))

  Cofib0or1 : ∀ {r r'} → (r == `0) ∨ (r == `1) → Cofib (r == r')
  Cofib0or1 = case (\ r=0 → transport (\ x → Cofib (x == _)) (! r=0) Cofib=0r) ((\ r=1 → transport (\ x → Cofib (x == _)) (! r=1) Cofib=1r)) (\ _ _ → Cofib-prop)

