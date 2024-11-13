{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Proposition
open import Cofibs
open import Kan
open import Path
open import Interval
open import directed.Segal
open import directed.Covariant

module directed.SegalDepCovariant where

  hasDCom₂ : ∀ {l2} (A : Δ₂ → Set l2) → Set (lmax (lsuc lzero) l2)
  hasDCom₂ A = (xy : Δ₂)
             → (h : (xy : Δ₂) → Λ₂ xy → A xy)
             → (α : Set) {{ cα  : Cofib α }}
             → (t : (xy : Δ₂) → α → A xy [ Λ₂ xy ↦ h xy ])
             → A xy [ Λ₂ xy ↦ h xy , α ↦ fst o t xy ]

  -- inner fibration
  relDCom₂ : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lmax (lsuc lzero) (lmax l1 l2))
  relDCom₂ {Γ = Γ} A = (p : Δ₂ → Γ) → hasDCom₂ (A o p)

  open CovSrcTgt

  relDCom₂-relCovSrcTgt : ∀ {l1 l2 : Level} {Γ : Set l1} (A : Γ → Set l2)
                        → relCovSrcTgt-better A
                        → relDCom₂ A
  relDCom₂-relCovSrcTgt A dcomA p (x , y , y≤x) h α t =
    transport (\ H → A (p (x , y , H))) uip  (fst fill) ,
    (∨-elim _ (\ {id → ap (transport (λ H → A (p (x , ``0 , H))) uip) (snd (snd fill) id) ∘   ap= (transport-∘ (λ H → A (p (x , ``0 , H))) ((uip {_} {_} {_} {_} {≤trans x id y≤x} {y≤x})) (uip {_} {_} {_} {_} {id} {≤trans x id y≤x}))  ∘  ! (apd (\ H → h (x , ``0 , H) (inl id)) (_∘_ ((uip {_} {_} {_} {_} {≤trans x id y≤x} {y≤x})) (uip {_} {_} {_} {_} {id} {≤trans x id y≤x})))   })
              (\ {id → ap (transport (λ H → A (p (``1 , y , H))) uip) (fst (snd fill) (inr id)) ∘ ! (apd (\ H → h (``1 , y , H) (inr id)) uip)})
              \ _ _ → uip) ,
    (\ pα → ap (transport (λ H → A (p (x , y , H))) uip) (fst (snd fill) (inl pα)) ∘ ! (apd (\ H → fst (t (x , y , H) pα)) uip)) where
    fill = dcomA ``0 y id (\ z _ z≤y → (p (x , z , (≤trans x z≤y y≤x))))
                 ((α ∨ (x == ``1)))
                 (\ z 0≤z z≤y → case (\ pα →  fst (t (x , z , (≤trans x z≤y y≤x)) pα)  )
                                     (\ x=1 → h (x , z , (≤trans x z≤y y≤x)) (inr x=1) )
                                     \ pα → \{id →  ! (snd (t (``1 , z , ≤trans ``1 z≤y y≤x) pα) (inr id))})
                 (transport (\ H → A (p (x , ``0 , H))) uip (h (x , ``0 , id) (inl id)) ,
                   ∨-elim _ (\ pα →  ! (apd (\ H → (h (x , ``0 , H) (inl id))) uip) ∘ ! (snd (t (x , ``0 , ≤trans x id y≤x) pα) (inl id)) )
                            (\ {id → ! (apd (λ H → h (``1 , ``0 , H) (inl id)) uip) ∘ ap (h (``1 , ``0 , ≤trans ``1 id y≤x)) trunc })
                            \ _ _ → uip )
  
  
  decompose-relDCom₂ : ∀ {l1 l2 : Level} {Γ : Set l1} (A : Γ → Set l2)
                     → relCov A
                     → relDCom₂ A
  decompose-relDCom₂ A dcomA p xy h α t =
                     triangle-from-square (A o p) (λ x y → fst (fill x y)) xy ,
                     ∨-elim _ 
                            (\ y=0 → !(triangle-from-square-boundary (A o p) (λ x y → fst (fill x y)) xy _
                                         ((snd (snd (fill (fst xy) (fst (snd xy)))) (! y=0))))
                                     ∘ coh1 (fst xy) (fst (snd xy)) y=0 (snd (snd xy)))
                            (\ x=1 → !(triangle-from-square-boundary (A o p) (λ x y → fst (fill x y)) xy _
                                         ((fst (snd (fill (fst xy) (fst (snd xy)))) (inl (inr x=1))))) ∘
                                     coh2 (fst xy) (fst (snd xy)) x=1 (snd (snd xy)))
                            (\ _ _ → uip) ,
                     (\pα → ! (triangle-from-square-boundary (A o p) (λ x y → fst (fill x y)) xy _
                                   ((fst (snd (fill (fst xy) (fst (snd xy)))) (inl (inl pα))))) ∘
                            ! (apd (\ H → fst (t H pα)) (lower-triangle-ret xy))  )
                     
   where
    fill : (x : 𝟚) (y : 𝟚) → A (p (lower-triangle x y)) [ (α ∨ (x == ``1)) ∨ (x == ``0) ↦ _ ,
                                                          ``0 == y ↦ _ ]
    fill x y' = dcomA (\ y → p (lower-triangle x y))
                     y'
                     ((α ∨ (x == ``1)) ∨ (x == ``0))
                     (\ y → case
                            (case (\ pα →  fst (t (lower-triangle x y) pα) )
                                  (\ x=1 →  h (lower-triangle x y) (inr x=1) )
                                  (\ pα x=1 →  ! (snd (t (lower-triangle x y) pα) (inr x=1)) ))
                            (\ x=0 → h (lower-triangle x y) ( (inl (ap (\ x → x ⊓ y) x=0)) ) ) -- really h (``0 , ``0 , id) (inl id) but fewer transports this way
                            (∨-elim _ (\ pα x=0 → ! (snd (t (lower-triangle x y) pα) (inl (ap (\ x → x ⊓ y) x=0))) )
                                      (\ p q → abort (diabort (p ∘ ! q)))
                                      (\ _ _ → λ= \ _ → uip)))
                     (h (x , ``0 , id) (inl id)  ,
                         ∨-elim _
                              (∨-elim _ (\ pα → ! (snd ((t (x , ``0 , id)) pα) (inl id)))
                                (\ x=1 → ap (h (x , ``0 , id)) trunc)
                                (\ _ _ → uip))
                              (\ x=0 → ap (h (x , ``0 , id)) trunc)
                              (\ _ _ → uip)
                              )

    -- easier to do this by ==-induction that to compose lemmas
    coh1 : ∀ x y (y=0 : y == ``0) (y≤x : y ≤ x) →
           h (x , y , y≤x) (inl y=0) ==
           transport (A o p) (lower-triangle-ret (x , y , y≤x))
             (transport (A o (λ y → p (lower-triangle x y))) (! y=0)
               (h (x , ``0 , id) (inl id)))
    coh1 x y id id =  ap (\ H → transport (A o p) H (h (x , ``0 , id) (inl id))) (uip {p = id} {q = (lower-triangle-ret (x , ``0 , id))}) 

    coh2 : ∀ x y (x=1 : x == ``1) y≤x →
         h (x , y , y≤x) (inr x=1) ==
         transport (A o p) (lower-triangle-ret (x , y , y≤x))
         (h (lower-triangle x y) (inr x=1))
    coh2 x y id id = ! (ap (\ H → transport (A o p) H (h (``1 , y , id) (inr id))) (uip {p = (pair= id (pair= (id ∘ ⊓comm ``1 y) uip))} {q = id}))
