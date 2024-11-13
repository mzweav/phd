{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import weak.Cofibs
open import Prop
open import weak.Kan
open import weak.Pi

-- the lsuc lzero is avoidable, because we could define codes for cofibs in universe 0

module weak.Path where 

  PathO : {l : Level} (A : I → Set l) (a0 : A `0) (a1 : A `1) → Set l
  PathO A a0 a1 = Σ (\ (p : (x : I) → A x) → (p `0 == a0) × (p `1 == a1))

  PathO= : {l : Level} {A : I → Set l} {a0 : A `0} {a1 : A `1}
         → (p q : PathO A a0 a1) 
         → ((x : I) → fst p x == fst q x) → p == q
  PathO= p q h = pair= (λ= h) (pair= uip uip)

  ⇒fst : {l : Level} {A : I → I → Set l} {a0 : (y : I) → A y `0} {a1 : (y : I) → A y `1} {r r' : I} (eq : r == r')
         → (p : PathO (A r) (a0 r) (a1 r))
         → (x : I) → fst (⇒ { A = \ r → PathO (A r) (a0 r) (a1 r)} p eq) x == ⇒ (fst p x) eq
  ⇒fst id _ _ = id

  ∘Path : ∀ {l} {A : Set l} {a b c : A} → hasHFill A → Path A b c → Path A a b → Path A a c
  ∘Path {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c `0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c `1)) (inr id))  where
    c : (x : I) → _
    c x = (hA `0 `1 (inl id) ((x == `0) ∨ (x == `1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (iabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip))) 

  apPath : ∀ {l1 l2} {A : Set l1} {B : Set l2} {a1 a2 : A} (f : A → B) → Path A a1 a2 → Path B (f a1) (f a2)
  apPath f p = (\ x → f (fst p x)) , (ap f (fst (snd p)) , ap f (snd (snd p)))

  apdPath : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} {a1 a2 : A} (f : (x : A) → B x)
          → (p : Path A a1 a2)
          → PathO (\ x → B (fst p x)) (transport B (! (fst (snd p))) (f a1)) (transport B ((! (snd (snd p)))) (f a2))
  apdPath f p = (\ x → f (fst p x)) , ( ! (apd f (! (fst (snd p))))  ,  ! (apd f (! (snd (snd p)))) )

  ⇒fst-nd : {l : Level} {A : Set l} {a0 : (y : I) → A} {a1 : (y : I) → A} {r r' : I} (eq : r == r')
         → (p : Path A (a0 r) (a1 r))
         → (x : I) → fst (⇒ { A = \ r → Path A (a0 r) (a1 r)} p eq) x == (fst p x)
  ⇒fst-nd id _ _ = id

  fst-transport-Path : {l : Level} {A : I → Set l} {a0 : (γ : I) → A γ} {a1 : (γ : I) → A γ}
                     {r r' : I} (p : r == r')
                     → (q : Path (A r) (a0 r) (a1 r))
                     → fst (transport (\ x → Path (A x) (a0 x) (a1 x)) p q) == (\ x → transport A p (fst q x))
  fst-transport-Path id q = id

  fst-transport-Path-right : {l1 l2 : Level} {A : Set l1} {B : Set l2} {a0 : A} {a1 : B → A}
                     {b b' : B} (p : b == b')
                     → (q : Path A a0 (a1 b))
                     → fst (transport (\ x → Path A a0 (a1 x)) p q) == (fst q)
  fst-transport-Path-right id q = id

  comPath-endpoints : ∀ {l1 l : Level} {Γ : Set l1} {A : Set l} (a0 : (γ : Γ) → A) (a1 : (γ : Γ) → A) 
          → hasHFill A 
          → relFill (\γ → Path A (a0 γ) (a1 γ))
  comPath-endpoints {A = A} a0 a1 hcomA p r r' r01 α t b = 
          ((\ x → fst (hcoma x)) , (! (fst (snd (hcoma `0)) (inr (inl id))) ) , (! (fst (snd (hcoma `1)) (inr (inr id))) )) , 
          (\ pα → PathO= _ _ (\ x → fst (snd (hcoma x)) (inl pα) )) , 
          (\ r=r' → PathO= _ _ (\ x → snd (snd (hcoma x)) r=r' ∘ ⇒fst-nd {A = A} {a0 = λ z → a0 (p z)} {a1 = λ z → a1 (p z)} r=r' (fst b) x)) where 
    hcoma : (x : I) → _
    hcoma x = hcomA r r' r01
                  (α ∨ ((x == `0) ∨ (x == `1))) 
                  (\ z → case (\ pα → fst (t z pα) x ) 
                         (case (\ x=0 → transport _ (! x=0) (a0 (p z)) )
                               (\ x=1 → transport _ (! x=1) (a1 (p z)) ) 
                               (\ p q → abort (iabort (q ∘ ! p))))
                         (\ pα → ∨-elim _ (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) (\ _ _ → uip))) 
                  (fst (fst b) x , 
                   ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα)) (∨-elim _ (\ x=0 → ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b))))) ((\ x=1 → ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))))) ((\ _ _ → uip))) (((\ _ _ → uip))))


  
