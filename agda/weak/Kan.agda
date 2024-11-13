{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;lzero;_⊔_)
open import Lib
open import Interval
open import weak.Cofibs
open import Prop

-- the lsuc lzero is avoidable, because we could define codes for cofibs in universe 0

module weak.Kan where 

  ⇐ : ∀ {l} {I : Set} (A : I → Set l) {r r' : I} → A r' → (p : r == r') → A r
  ⇐ A x id = x

  ⇒ : ∀ {l} {I : Set} {A : I → Set l} {r r' : I} → A r → (p : r == r') → A r'
  ⇒ {A = A} x p = transport A p x

  k : ∀ {l1 l2} {A : Set l1} {B : Set l2} → A → B → A
  k x y = x

  ContractibleFill : {l : Level} (A : Set l) → Set (ℓ₁ ⊔ l)
  ContractibleFill A = (α : Set) {{cα : Cofib α}} → (t : α → A) → A [ α ↦ t ]

  HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  HFiber f b = Σ \a → Path _ (f a) b

  =HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B}
            {v1 v2 : HFiber f b}
          → (p : fst v1 == fst v2)
          → fst (snd v1) == (fst (snd v2))
          → v1 == v2
  =HFiber {v2 = v2} id id = ap (\ x → (fst v2 , fst (snd v2) , x)) (ap2 _,_ uip uip)

  isEquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (ℓ₁ ⊔ l1 ⊔ l2)
  isEquivFill A B f = (b : B) → ContractibleFill (HFiber f b)

  Equiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) →  Set (ℓ₁ ⊔ l1 ⊔ l2)
  Equiv A B = Σ \ (f : A → B) → isEquivFill A B f 

  apply : {l : Level} (A : I → Set l) → (r : I) → ((x : I) → A x) → A r
  apply A r f = f r

  hasWCom :  ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasWCom A = (r : I) → isEquivFill ((r' : I) → A r') (A r) (apply A r)

  hasWHCom :  ∀ {l} → (Set l) → Set (lsuc lzero ⊔ l)
  hasWHCom A = (r : I) → isEquivFill (I → A) A (\ f → f r)

  relWCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relWCom {Γ = Γ} A = (p : I → Γ) → hasWCom (A o p)

  hasWCoeOld : {l : Level} → (I → Set l) → Set l
  hasWCoeOld A = (r r' : I) →  
    Σ \ (f : A r → A r') → 
        ((e : r == r') → (b : A r) → Σ \ (p : (x : I) → A r') → (p `0 == f b) × (p `1 == ⇒ b e))

  hasWCoe : {l : Level} → (I → Set l) → Set l
  hasWCoe A = (r : I) (a : A r) → HFiber (apply A r) a

  relWCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (l1 ⊔ l2)
  relWCoe {Γ = Γ} A = (p : I → Γ) → hasWCoe (A o p)

  module hasWCoe-same {l : Level} (A : I → Set l) where
    to : hasWCoe A → hasWCoeOld A
    to h = λ r r' → (\ a → fst (h r a) r') , (\ {id b → (\ z → fst (snd (h r b)) z ) , fst (snd (snd (h r b))) , snd (snd (snd (h r b)))})

    from : hasWCoeOld A → hasWCoe A 
    from h = λ r a → (\ r' → fst (h r r') a) , (\ z → fst (snd (h r r) id a) z) , fst (snd (snd (h r r) id a)) , snd (snd (snd (h r r) id a))

  relWCom-relWCoe : ∀ {l1 l2} {Γ : Set l1} → (A : Γ → Set l2) → relWCom A → (p : I → Γ) → hasWCoe (A o p)
  relWCom-relWCoe A comA p r a = fst (comA p r a ⊥ (\ x → abort x))

  wcomPre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relWCom A → relWCom (A o θ)
  wcomPre θ _ comA p = comA (θ o p)

  -- ----------------------------------------------------------------------

  hasCom : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasCom A = (r r' : I) {{_ : Cofib (r == r')}}
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A z) 
             (b : A r [ α ↦ t r ]) 
            → A r' [ α ↦ t r' , (r == r') ↦ ⇒ (fst b) ]

  relCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relCom {Γ = Γ} A = (p : I → Γ) → hasCom (A o p)

  hasFill : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasFill A = (r r' : I) (_ : (r == `0) ∨ (r == `1))
           → (α : Set) {{_ : Cofib α}} 
             (t : (z : I) → α → A z) 
             (b : A r [ α ↦ t r ]) 
            → A r' [ α ↦ t r' , (r == r') ↦ ⇒ (fst b) ]

  relFill : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relFill {Γ = Γ} A = (p : I → Γ) → hasFill (A o p)

  comPre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relCom A → relCom (A o θ)
  comPre θ _ comA p = comA (θ o p)

  fillPre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relFill A → relFill (A o θ)
  fillPre θ _ comA p = comA (θ o p)

  hasHCom : {l : Level} → Set l → Set (lsuc lzero ⊔ l)
  hasHCom A = (r r' : I) {{_ : Cofib (r == r') }} (α : Set) {{_ : Cofib α}} 
            → (t : (z : I) → α → A) 
            → (b : A [ α ↦ t r ]) 
            → A [ α ↦ t r' , (r == r') ↦ k (fst b) ]

  hasHFill : {l : Level} → Set l → Set (lsuc lzero ⊔ l)
  hasHFill A = (r r' : I) (_ : (r == `0) ∨ (r == `1)) (α : Set) {{_ : Cofib α}} 
            → (t : (z : I) → α → A) 
            → (b : A [ α ↦ t r ]) 
            → A [ α ↦ t r' , (r == r') ↦ k (fst b) ]

  hasCoe : {l : Level} → (I → Set l) → Set l
  hasCoe A = (r r' : I) {{_ : Cofib (r == r') }}
           → (b : A r) 
           → A r' [ (r == r') ↦ ⇒ b ]

  relCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (l1 ⊔ l2)
  relCoe {_} {_} {Γ} A = (p : I → Γ) → hasCoe (A o p)

  relCom-hasHCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom A 
                 → (x : Γ) → hasHCom (A x)
  relCom-hasHCom A rA x r r' α t b = fst user , fst (snd user) , (\ r=r' → snd (snd user) r=r' ∘ ! (ap= (transport-constant r=r'))) where
    user = rA (\ _ → x) r r' α t b

  relFill-hasHFill : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relFill A 
                 → (x : Γ) → hasHFill (A x)
  relFill-hasHFill A rA x r r' r01 α t b = fst user , fst (snd user) , (\ r=r' → snd (snd user) r=r' ∘ ! (ap= (transport-constant r=r'))) where
    user = rA (\ _ → x) r r' r01 α t b

  relCom-relFill : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relCom A → relFill A
  relCom-relFill A comA p r r' r01 = comA p r r' {{Cofib0or1 r01}}

  relCom-hasHFill : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom A 
                 → (x : Γ) → hasHFill (A x)
  relCom-hasHFill A rA = relFill-hasHFill A (relCom-relFill A rA)

  relCom-relCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom A 
                 → relCoe A
  relCom-relCoe A comA p r r' b = fst com , (\ r=r' → snd (snd com) r=r') where
    com = comA p r r' ⊥ (\ x → abort) (b , \ x → abort x)

  relWCom-relCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relWCom A → relCom A
  relWCom-relCom A wcomA p r r' α {{cα}} t b = fst (fst fix) `1 , (\ pα →  ap (\ H → fst H `1) (snd fix (inl pα)) ) , (\{id →  ap (\ H → fst H `1) (snd fix (inr id)) ∘ ! (snd (snd (snd (fst w)))) }) where
    w =  wcomA p r (fst b) α (\pα → (\ z → t z pα) , ((\ _ → t r pα) , id , snd b pα))
    fix = wcomA (\ _ → p r') `0
                (fst (fst w) r')
                (α ∨ (r == r'))
                (case (\ pα → ((\ _ → t r' pα)) , (\ _ → t r' pα) , id , ap (\ H → fst H r') (snd w pα) )
                      (\ r=r' → (\ z → transport (A o p) r=r' (fst (snd (fst w)) z)) ,
                                (\ _ → transport (A o p) r=r' (fst (snd (fst w)) `0)) ,
                                id ,
                                apd (fst (fst w)) r=r' ∘ ap (transport (A o p) r=r') (fst (snd (snd (fst w)))) )
                      (\ pα r=r' → =HFiber (λ= \ z → ap (transport (A o p) r=r') (ap (\ w → (fst (snd w) z)) (snd w pα)) ∘ ! (apd (\ z → t z pα) r=r'))
                                           (λ= \ _ → ap (transport (A o p) r=r') (ap (\ w → (fst (snd w) `0)) (snd w pα)) ∘ ! (apd (\ z → t z pα) r=r')) ))  

  relWCom-relFill : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relWCom A → relFill A
  relWCom-relFill A wcomA = relCom-relFill A (relWCom-relCom A wcomA)

  -- ----------------------------------------------------------------------

