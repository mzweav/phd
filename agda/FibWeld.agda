{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Kan

module FibWeld where 

  postulate

    Weld : ∀ {l} (α : Set)
           {{_ : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (pα : α) → B → T pα) → Set l

    Weld-α : ∀ {l} (α : Set)
           {{cα : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (pα : α) → B → T pα)
           → ---------------------------
           (pα : α) → Weld α T B f == T pα

    win : ∀ {l} (α : Set)
           {{cα : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (pα : α) → B → T pα)
           → ---------------------------
           B → Weld α T B f

    win-α : ∀ {l} (α : Set)
           {{cα : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (pα : α) → B → T pα)
           (a : B) (pα : α)
           → ---------------------------
           transport (λ X → X) (Weld-α α T B f pα) (win α T B f a) == f pα a
    -- {-# REWRITE win-α #-}

  win-α! : ∀ {l} (α : Set)
           {{cα : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (pα : α) → B → T pα)
           (a : B) (pα : α)
           → ---------------------------
           coe (! (Weld-α α T B f pα)) (f pα a) == (win α T B f a) 
  win-α! α A B f a pα = (move-transport-left! (λ X → X) (Weld-α α A B f pα) (! (win-α _ _ _ _ _ pα)))

  hcomWeldα :  ∀ {l} {α : Set}
           {{cα : Cofib α}}
           {T : α → Set l}
           {B : Set l}
           (hcomB : (pα : α) → hasHCom (T pα))
           {f : (pα : α) → B → T pα}
           (pα : α) → hasHCom (Weld α T B f) 
  hcomWeldα {α = α}{T = T}{B} hcomB {f} pα r r' β d c =
    coe (!(Weld-α α T B f pα)) (fst h) ,
    (\ pβ → ap (coe (! (Weld-α α T B f pα))) (fst (snd h) pβ) ∘ ! (ap= (transport-inv (\ x → x) (Weld-α α T B f pα))) ) ,
    ((\ r=r' → ap (coe (! (Weld-α α T B f pα))) (snd (snd h) r=r') ∘ ! (ap= (transport-inv (\ x → x) (Weld-α α T B f pα))) )) where
    h = ((hcomB pα) r r' β (λ i pβ → coe (Weld-α α T B f pα) (d i pβ))
             (coe (Weld-α α T B f pα) (fst c) ,
                  (λ pβ → ap (coe (Weld-α α T B f pα)) (snd c pβ))))
  postulate

    whcom : ∀ {l} {α : Set}
           {{cα : Cofib α}}
           {T : α → Set l}
           {B : Set l}
           {f : (pα : α) → B → T pα}
           (hcomB : (pα : α) → hasHCom (T pα))
           (r r' : I)
           (β : Set)
           {{cβ : Cofib β}}
           (d : I → β → Weld α T B f)
           (c : (Weld α T B f)[ β ↦ d r ])
           → ------------------------------------------------------------------------
           (Weld α T B f)[ β ↦ d r'
                         , r == r' ↦ (λ _ → (fst c))
                         , α ↦ (\ pα → fst (hcomWeldα hcomB pα r r' β d c)) ]

  module WElim {l l' : Level} {α : Set}
               {{cα : Cofib α}}
               {T : α → Set l}
               {B : Set l}
               {f : (pα : α) → B → T pα}
               (C : Weld α T B f → Set l')
               (comC : relCom C)
               (m : (a : B) → C (win _ _ _ _ a))
               (n : (pα : α) → (b : T pα) → C (coe (!(Weld-α α T B f pα)) b))
               (eq : (b : B) → (pα : α) → m b == transport C (win-α! _ _ _ _ _ pα) (n pα (f pα b))) where

    postulate
      welim : (w : Weld α T B f) → C w

      welim-win : (a : B) → welim (win α T B f a) == m a
      {-# REWRITE welim-win #-}

      welim-α : (pα : α) (t : T pα) → welim (coe (!(Weld-α α T B f pα)) t) == (n pα t)
              
    welim-α' : (pα : α) (b : Weld α T B f)
              → welim b == transport C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα))) (n pα (coe (Weld-α α T B f pα) b))
    welim-α' pα b = ap (transport C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα)))) (welim-α pα (coe (Weld-α α T B f pα) b)) ∘ ! (apd welim (ap= (transport-inv (λ X → X) (Weld-α α T B f pα)) {b}))

    postulate
      welim-whcom : (hcomB : (pα : α) → hasHCom (T pα))
                    (r r' : I)
                    (β : Set)
                    {{_ : Cofib β}}
                    (d : I → β → Weld α T B f)
                    (c : (Weld α T B f)[ β ↦ d r ])
                    → 
             welim (fst (whcom hcomB r r' β d c))
               ==
             fst (comC (λ i → fst (whcom hcomB r i β d c))
                       r r' (α ∨ β)
                       (λ i → case (λ pα → transport C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα)))
                                                            (n pα (coe (Weld-α α T B f pα) (fst (whcom hcomB r i β d c)))))
                                   (λ pβ → transport C (fst ((snd (whcom hcomB r i β d c))) pβ) (welim (d i pβ)))
                                   (λ pα pβ → het-to-hom (!h (transport-=h C (fst ((snd (whcom hcomB r i β d c))) pβ))
                                                          ∘h !h (hom-to-het (welim-α' pα (d i pβ)))
                                                          ∘h !h (transport-=h C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα))))
                                                          ∘h apdo (λ x → n pα (coe (Weld-α α T B f pα) x))
                                                                  (! (fst ((snd (whcom hcomB r i β d c))) pβ))
                                                          ∘h transport-=h C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα))))))
                       (transport C (fst (snd (snd (whcom hcomB r r β d c))) id) (welim (fst c))
                       , ∨-elim _ (λ pα → het-to-hom (!h (transport-=h C (fst (snd (snd (whcom hcomB r r β d c))) id))
                                                          ∘h !h (hom-to-het (welim-α' pα (fst c)))
                                                          ∘h !h (transport-=h C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα))))
                                                          ∘h apdo (λ x → n pα (coe (Weld-α α T B f pα) x))
                                                                  (! (fst (snd (snd (whcom hcomB r r β d c))) id))
                                                          ∘h transport-=h C (ap= (transport-inv (λ X → X) (Weld-α α T B f pα)))))
                                  (λ pβ → het-to-hom (!h (transport-=h C (fst (snd (snd (whcom hcomB r r β d c))) id))
                                                          ∘h apdo (welim) (snd c pβ)
                                                          ∘h transport-=h C (fst (snd (whcom hcomB r r β d c)) pβ)))
                                  (λ _ _ → uip)))




