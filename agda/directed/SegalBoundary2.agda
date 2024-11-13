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
open import directed.SegalDepCovariant

module directed.SegalBoundary2 where

  Faces : Set
  Faces = Σ \ (xbound : Δ₂) → Σ \ (ybound : Δ₂) → fst ybound ≤ fst (snd xbound)

  Δb : Faces  → Set
  Δb ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) =
     Σ \ (x : 𝟚) → Σ \ (y : 𝟚) → (ymin ≤ y) × ((y ≤ ymax) × ((xmin ≤ x) × (x ≤ xmax)))

  Λb : (f : Faces) → Δb f → Set
  Λb ((xmax , xmin , _) , (ymax , ymin , _) , yx≤) (x , y , _ ) = (y == ymin) ∨ (x == xmax)

  -- FIXME TODO
  postulate
    ≤inl : ∀ x y → x ≤ (x ⊔ y)
    ≤inr : ∀ x y → y ≤ (x ⊔ y)
    ≤case : ∀ x y z → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
    ≤fst : ∀ x y → (x ⊓ y) ≤ x
    ≤snd : ∀ x y → (x ⊓ y) ≤ y
    ≤pair : ∀ z x y → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
    distrib : ∀ x y z → ((x ⊔ y) ⊓ z) == ((x ⊓ z) ⊔ (y ⊓ z))
    distrib2 : ∀ x y z → ((x ⊓ y) ⊔ z) == ((x ⊔ z) ⊓ (y ⊔ z))

  other≤ : ∀ {x y} → x ≤ y → (x ⊔ y) == y
  other≤ {x}{y} p = diantisym (≤case x y y p id) (≤inr x y)

  embed : (f : Faces) → Δ₂ → Δb f
  embed ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , x≤y) =
    ((xmin ⊔ x) ⊓ xmax ) , (((ymin ⊔ y) ⊓ ymax )) ,
      ≤pair ymin (ymin ⊔ y) ymax (≤inl ymin y) y≤  ,
      ≤snd (ymin ⊔ y) ymax ,
      ≤pair xmin (xmin ⊔ x) xmax (≤inl xmin x) x≤  ,
      ≤snd (xmin ⊔ x) xmax

  embed-horn : (f : Faces) (xy : Δ₂) → Λ₂ xy → Λb f (embed f xy)
  embed-horn ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , y≤x) =
    case (\ {id →  inl ( (! y≤)) })
         (\ {id → inr id})
         (\ _ _ → trunc)

  embed-horn' : (f : Faces) (xy : Δ₂) → Λb f (embed f xy) → Λ₂ xy 
  embed-horn' ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , y≤x) =
    case {!NO: e.g. y = ymin!}
         {!!}
         (\ _ _ → trunc)

  forget : (f : Faces) (xy : Δb f) → Δ₂
  forget ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , ymin≤y , y≤ymax , xmin≤x , x≤xmax) =
         (x , y , ≤trans x (≤trans xmin y≤ymax yx≤) xmin≤x )

  -- ???
  forget-horn : (f : Faces) (xy : Δb f) → Λb f xy → Λ₂ (forget f xy)
  forget-horn ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , ymin≤y , y≤ymax , xmin≤x , x≤xmax) =
              case (\ y=ymin → {!!})
                   {!!}
                   {!!}

  inbounds : ∀ xmin xmax x → xmin ≤ xmax → xmin ≤ x → x ≤ xmax → ((xmin ⊔ x) ⊓ xmax) == x
  inbounds xmin xmax x x≤  xmin≤x x≤xmax = (((other≤ {xmin}{x} xmin≤x ∘ ap (\ h → xmin ⊔ h) (! x≤xmax)) ∘ ap (\ h → h ⊔ (x ⊓ xmax)) (! x≤)) ∘ distrib xmin x xmax)

  retract : (f : Faces) (xy : Δb f) → embed f (forget f xy) == xy
  retract ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , ymin≤y , y≤ymax , xmin≤x , x≤xmax) =
          pair= (inbounds xmin xmax x x≤ xmin≤x x≤xmax)
          (pair= (inbounds ymin ymax y y≤ ymin≤y y≤ymax ∘ fst-transport-Σ (inbounds xmin xmax x x≤ xmin≤x x≤xmax) (snd (embed f (forget f (x , y , ymin≤y , y≤ymax , xmin≤x , x≤xmax)))) )
                 (pair= uip (pair= uip (pair= uip uip)))) where
    f : Faces
    f = ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) 

  hasDCom₂b : ∀ {l2} (f : Faces) 
                     (A : Δb f → Set l2) → Set (lmax (lsuc lzero) l2)
  hasDCom₂b f A = (xy : Δb f)
              → (h : (xy : Δb f) → Λb f xy → A xy)
              → (α : Set) {{ cα  : Cofib α }}
              → (t : (xy : Δb f) → α → A xy [ Λb f xy ↦ h xy ])
              → A xy [ Λb f xy ↦ h xy , α ↦ fst o t xy ]

  relDCom₂b : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set (lmax (lsuc lzero) (lmax l1 l2))
  relDCom₂b {Γ = Γ} A = (f : Faces) (p : Δb f → Γ) → hasDCom₂b f (A o p)

  relDCom₂b-relDCom₂ :  ∀ {l1 l2} {Γ : Set l2} (A : Γ → Set l1)
                     → relDCom₂ A
                     → relDCom₂b A
  relDCom₂b-relDCom₂ A dcomA f p xy h α t =
    transport (A o p) (retract f xy) (fst d) ,
    (\ phorn → {!fst (snd d)!}) , -- ap (transport (λ x → A (p x)) (retract f xy)) (snd (snd d) (inr phorn)) ∘ {!!}) ,
    (\ pα → ap (transport (λ x → A (p x)) (retract f xy)) (snd (snd d) (inl pα)) ∘ ! (apd (\ H → fst (t H pα)) (retract f xy))) where
    e = embed f
    d = dcomA (p o e)
              (forget f xy)
              (\ x'y' phorn → h (e x'y') (embed-horn f x'y' phorn))
              (α ∨ Λb f xy)
              (\ x'y' → case
                        (\ pα → fst (t (e x'y') pα) , \ phorn → snd (t (e x'y') pα) (embed-horn f x'y' phorn))
                        (\ phorn → {!!})
                        {!!}) 
    -- foo : (f : Faces) (xy : Δb f) (phorn : Λb f xy) (x'y' : Δ₂) → xy == embed f x'y'
    -- foo ((xmax , xmin , x≤) , (ymax , ymin , y≤) , yx≤) (x , y , ymin≤y , y≤ymax , xmin≤x , x≤xmax)
    --     = case (\ y=ymin → \ { (x' , y' , y'≤x') → {!d!}})
    --            {!!}
    --            {!!}
    -- -- transport (A o p) (case (\ q → {!!}) {!!} (\ _ _ → uip) phorn  ) (h xy phorn)

  -- ----------------------------------------------------------------------

  hasFillTriangle :  ∀ {l1 l2} {Γ : Set l2} (A : Γ → Set l1)
                     → relDCom₂b A
                     → relDCom₂ A
  hasFillTriangle A dcomb p (x , y , y≤x) h α t =
    -- morally just d, but off by a proof of ≤, need  id ≤trans y≤x ≤trans id = y≤x
    transport (\ h → A (p (x , y , h))) uip (fst d) ,
      (\ ph → ap (transport (\ h → A (p (x , y , h))) uip) (fst (snd d) ph) ∘ ! (apd (\ z → h (x , y , z) ph) uip)) ,
      (\ pα → ap (transport (\ h → A (p (x , y , h))) uip) (snd (snd d) pα) ∘ ! (apd (\ z → fst (t (x , y , z) pα)) uip)) where
    d = dcomb (((``1 , x , id)) , ((y , ``0 , id)) , y≤x)
              (\ { (x' , y' , _ , y'≤y , x≤x' , _) → p ((x' , y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )))})
              ((x , y , id , id , id , id))
              (\ { (x' , y' , _ , y'≤y , x≤x' , _) phorn → h (x' , y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )) phorn})
              α
              (\ { (x' , y' , _ , y'≤y , x≤x' , _) pα → t (x' , y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )) pα})

  Δ₃ : Set 
  Δ₃ = Σ \ (x : 𝟚) → Σ \ (y : 𝟚) → Σ \ (z : 𝟚) → (z ≤ y) × (y ≤ x)

  horn1 : Δ₃ → Set
  horn1 (x , y , z , _) = (y == z) ∨ (x == ``1)

  hasFill1 : ∀ {l1} (A : Δ₃ → Set l1) → Set (lmax (lsuc lzero) l1)
  hasFill1 A = (h : (xyz : Δ₃) → horn1 xyz → A xyz)
             → (α : Set) {{ cα  : Cofib α }}
             → (t : (xyz : Δ₃) → α → A xyz [ horn1 xyz ↦ h xyz ])
             → (xyz : Δ₃) → A xyz [ horn1 xyz ↦ h xyz , α ↦ fst o t xyz ]

  fill1 : ∀ {l1} (A : Δ₃ → Set l1)
        → relDCom₂b A
        → hasFill1  A 
  fill1 A dcom₂A h α t (x , y , z , z≤y , y≤x) = transport (\ H → A ((x , y , z , z≤y , H))) uip (fst d) , 
                                                 (\ ph → ap (transport (\ H → A ((x , y , z , z≤y , H))) uip) (fst (snd d) ph) ∘ ! (apd (\ H → h (x , y , z , z≤y , H) ph) uip)) ,
                                                 (\ pα → ap (transport (\ H → A ((x , y , z , z≤y , H))) uip) (snd (snd d) pα) ∘ ! (apd (\ H → fst (t (x , y , z , z≤y , H) pα)) uip))
                                                 where
    d = dcom₂A ((``1 , x , id) , (y , z , z≤y) , y≤x)
               (\ {(x' , y' , z≤y' , y'≤y , x≤x' , x'≤1) → (x' , y' , z , z≤y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )) })
               (x , y , z≤y , id , id , id)
               (\ {(x' , y' , z≤y' , y'≤y , x≤x' , x'≤1) → \ hornb → h (x' , y' , z , z≤y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )) hornb})
               α
               (\ {(x' , y' , z≤y' , y'≤y , x≤x' , x'≤1) → \ α → t (x' , y' , z , z≤y' , (≤trans x' (≤trans x y'≤y y≤x) x≤x' )) α})


  horn2 : Δ₃ → Set
  horn2 (x , y , z , _) = (z == ``0) ∨ (y == x)

  hasFill2 : ∀ {l1} (A : Δ₃ → Set l1) → Set (lmax (lsuc lzero) l1)
  hasFill2 A = (h : (xyz : Δ₃) → horn2 xyz → A xyz)
             → (α : Set) {{ cα  : Cofib α }}
             → (t : (xyz : Δ₃) → α → A xyz [ horn2 xyz ↦ h xyz ])
             → (xyz : Δ₃) → A xyz [ horn2 xyz ↦ h xyz , α ↦ fst o t xyz ]

  -- FIXME: seems like some of the bounds are kind of arbitrary here -- here are two options that work
  fill2 : ∀ {l1} (A : Δ₃ → Set l1)
        → relDCom₂b A
        → hasFill2  A 
  fill2 A dcom₂A h α t (x , y , z , z≤y , y≤x) = transport (\ H → A ((x , y , z , H , y≤x))) uip (fst d) , 
                                                 (\ ph → ap (transport (\ H → A ((x , y , z , H , y≤x))) uip) (fst (snd d) ph) ∘ ! (apd (\ H → h (x , y , z , H , y≤x) ph) uip)) ,
                                                 (\ pα → ap (transport (\ H → A ((x , y , z , H , y≤x ))) uip) (snd (snd d) pα) ∘ ! (apd (\ H → fst (t (x , y , z , H , y≤x) pα)) uip)) where
    d = dcom₂A ((x , y , y≤x) , (z , ``0 , id) , z≤y) -- are there other choices that work?
               (\ {(y' , z' , _ , z'≤z , y≤y' , y'≤x) → (x , y' , z' ,  (≤trans y' (≤trans y z'≤z z≤y) y≤y') , y'≤x) })
               (y , z , id , id , id , y≤x)
               (\ {(y' , z' , _ , z'≤z , y≤y' , y'≤x) phorn → h ((x , y' , z' ,  (≤trans y' (≤trans y z'≤z z≤y) y≤y') , y'≤x)) phorn })
               α
               (\ {(y' , z' , _ , z'≤z , y≤y' , y'≤x) pα → t ((x , y' , z' ,  (≤trans y' (≤trans y z'≤z z≤y) y≤y') , y'≤x)) pα })

  fill2' : ∀ {l1} (A : Δ₃ → Set l1)
        → relDCom₂b A
        → hasFill2  A 
  fill2' A dcom₂A h α t (x , y , z , z≤y , y≤x) = transport (\ H → A ((x , y , z , H , y≤x))) uip (fst d) , 
                                                 (\ ph → ap (transport (\ H → A ((x , y , z , H , y≤x))) uip) (fst (snd d) ph) ∘ ! (apd (\ H → h (x , y , z , H , y≤x) ph) uip)) ,
                                                 (\ pα → ap (transport (\ H → A ((x , y , z , H , y≤x ))) uip) (snd (snd d) pα) ∘ ! (apd (\ H → fst (t (x , y , z , H , y≤x) pα)) uip)) where
    d = dcom₂A ((x , z , ≤trans x z≤y y≤x) , (z , ``0 , id) , id) -- are there other choices that work?
               (\ {(y' , z' , _ , z'≤z , z≤y' , y'≤x) → (x , y' , z' ,  ≤trans y' z'≤z z≤y' , y'≤x) })
               (y , z , id , id , z≤y , y≤x)
               (\ {(y' , z' , _ , z'≤z , z≤y' , y'≤x) phorn → h ((x , y' , z' , ≤trans y' z'≤z z≤y' , y'≤x)) phorn })
               α
               (\ {(y' , z' , _ , z'≤z , z≤y' , y'≤x) pα → t ((x , y' , z' , ≤trans y' z'≤z z≤y' , y'≤x)) pα })


  horn3 : Δ₃ → Set
  horn3 (x , y , z , _) = (z == ``0) ∨ (x == ``1)

  hasFill3 : ∀ {l1} (A : Δ₃ → Set l1) → Set (lmax (lsuc lzero) l1)
  hasFill3 A = (h : (xyz : Δ₃) → horn3 xyz → A xyz)
             → (α : Set) {{ cα  : Cofib α }}
             → (t : (xyz : Δ₃) → α → A xyz [ horn3 xyz ↦ h xyz ])
             → (xyz : Δ₃) → A xyz [ horn3 xyz ↦ h xyz , α ↦ fst o t xyz ]

  fill3 : ∀ {l1} (A : Δ₃ → Set l1)
        → relDCom₂b A
        → hasFill3  A 
  fill3 A dcom₂A h α t (x , y , z , z≤y , y≤x) = d where
    d = dcom₂A ((``1 , y , id) , ((y , ``0 , id)) , id)
               (\ {(x , z , ``0≤z , z≤y , y≤x , x≤1) → (x , y , z , z≤y , y≤x) }) 
               (x , z , id , z≤y , y≤x , id)
               (\ {(x , z , ``0≤z , z≤y , y≤x , x≤1) hornb →  h (x , y , z , z≤y , y≤x) hornb })
               α
               (\ {(x , z , ``0≤z , z≤y , y≤x , x≤1) pα →   t (x , y , z , z≤y , y≤x) pα  })
