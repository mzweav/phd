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
open import universe.Sigma
open import Glue
open import directed.Covariant
open import Glue-Weak
import Glue-Com-NoCofib
open import universe.Universe
open import directed.UCov
import directed.universe.FunGlueKan
open import directed.universe.FunGlueKan using (FunGlueDataKan; fungluedatakan; dua-α) 

module directed.universe.FunGlue where

  open Layered

  FunGlueUKan : {@♭ l1 : Level} → FunGlueDataKan {l1} → U{l1}
  FunGlueUKan = directed.universe.FunGlueKan.FunGlueUKan

  FunGlueUKan0 : {@♭ l1 : Level} (d : FunGlueDataKan {l1}) →
                     FunGlueDataKan.i d == ``0
                   → FunGlueUKan d == FunGlueDataKan.A d
  FunGlueUKan0 = directed.universe.FunGlueKan.FunGlueUKan0

  FunGlueUKan1 : {@♭ l1 : Level} (d : FunGlueDataKan {l1}) →
                   FunGlueDataKan.i d == ``1
                 → FunGlueUKan d == FunGlueDataKan.B d
  FunGlueUKan1 = directed.universe.FunGlueKan.FunGlueUKan1

  record FunGlueData {@♭ l : Level} : Set (lmax ℓ₂ (lsuc l)) where
    constructor fungluedata
    field
      A : UCov l
      B : UCov l
      f : ElC A → ElC B
      i : 𝟚

  forget : {@♭ l : Level} → FunGlueData {l} → FunGlueDataKan {l}
  forget (fungluedata A B f i) = fungluedatakan (ElCov A) (ElCov B) f i

  duafun-cov : {@♭ l : Level} → FunGlueData {l} → Set l
  duafun-cov {l} d = El (FunGlueUKan (forget d))

  dua-α-cov : {@♭ l : Level} → FunGlueData {l} → Set
  dua-α-cov d = dua-α (forget d)

  -- need to copy and paste the definition from Kan dua-T to prove it lands in UCov
  dua-T-cov : {@♭ l : Level} → (d : FunGlueData {l}) → dua-α-cov d → UCov l
  dua-T-cov (fungluedata A B f i) = (cased01 (\ _ → A) (\ _ → B))

  relCov-duaF : ∀ {@♭ l : Level} → relCov1 (duafun-cov {l})
  relCov-duaF p α t b = glue _ _ _ _
                         (∨-elimd01 _ (\ x1=0  → fst (tleft x1=0))
                                      (\ x1=1  → fst (tright-fill ``1)))
                         (fst b' ,
                          ∨-elimd01 _ (\ x1=0 → fst (snd b') (inl (inr x1=0)))
                                      (\ x1=1 → fst (snd b') (inr x1=1))) ,
                         (\ pα → glue-cong _ _ _ _ _ _
                                      (λ= (∨-elimd01 _
                                             (\ x1=0 → ! (tleft-α pα x1=0))
                                             (\ x1=1 →  fst (snd (tright-fill ``1)) pα ∘ unglue-α (t ``1 pα) (inr x1=1)  )))
                                      (fst (snd b') (inl (inl pα))) ∘ Glueη (t ``1 pα))  where
    A = FunGlueData.A o p
    B = FunGlueData.B o p
    f : (x : 𝟚) → ElC (A x) → ElC (B x)
    f = \ x → FunGlueData.f (p x)
    x = FunGlueData.i o p

    back-in-time : (x ``1 == ``0) → (y : _) → x y == ``0   -- check can generalize monotonicity for general filling problem 
    back-in-time eq y = transport (\ h → x y ≤ h) eq (dimonotonicity≤ x y ``1 id) 

    -- when the result in is in A, compose in A 
    tleft-fill : (y : 𝟚) (x1=0 : x ``1 == ``0) → _
    tleft-fill y x1=0 =
      dcomEl A y α
             (\ z pα → coe (Glue-α _ _ _ _ (inl (back-in-time x1=0 z))) (t z pα))
             (coe (Glue-α _ _ _ _ (inl (back-in-time x1=0 ``0 ))) (fst b) ,
                 (λ pα → ((ap (coe (Glue-α _ _ _ _ (inl _))) (snd b pα)) ∘ ap (\ h → (coe (Glue-α _ _ _ _ (inl h)) (t ``0 pα))) uip)))
  
    tleft = tleft-fill ``1
  
    -- on α, the composite in A is just t 1
    tleft-α : (pα : α) → (x1=0 : x ``1 == ``0) →
           fst (tleft x1=0) == coe (Glue-α _ _ _ _ (inl x1=0)) (t ``1 pα)
    tleft-α pα x1 = (ap (\ h → coe (Glue-α _ _ _ _ (inl h)) (t ``1 pα)) uip) ∘ ! (fst (snd (tleft x1)) pα)
  
    tright-fill : ∀ y → _
    tright-fill y = dcomEl B y
                        (α)
                        (\ z pα → unglue (t z pα))
                        (unglue (fst b) ,
                                (\ pα → ap unglue (snd b pα)))
  
    -- unglue everyone to B and compose there, agreeing with f (tleft-fill) on x1 = 0
    b' : Σ \ (b' : ElC (B ``1)) → _
    b' = dcomEl B ``1
               ((α ∨ (x ``1 == ``0)) ∨ (x ``1 == ``1))
               ((\ z → case (case (\ pα →  unglue (t z pα))
                               (\ x1=0 → f z (fst (tleft-fill z x1=0)))
                               (\ pα x1=0 → ap (f z) (fst (snd (tleft-fill z x1=0)) pα) ∘ ! (unglue-α (t z pα) (inl (back-in-time x1=0 z)))  ))
                            (\ x1=1 → fst (tright-fill z))
                            (∨-elim _ (\ pα x1=1 → fst (snd (tright-fill z)) pα )
                                      (\ p q → abort (diabort (q ∘ ! p)) )
                                      (λ _ _ → λ= \ _ → uip))))
               (unglue (fst b) ,
                 ∨-elim _ 
                 (∨-elim _ (\ pα → ap unglue (snd b pα))
                          (\ x1=0 → unglue-α (fst b) (inl (back-in-time x1=0 ``0 )) ∘ ! (ap (f ``0) (snd (snd (tleft-fill ``0 x1=0)) id)) )
                          (\ _ _ → uip) )
                 (\ x1=1 → ! (snd (snd (tright-fill ``0)) id))
                 (\ _ _ → uip))

  covFunGlue-unaligned : {@♭ l : Level} → relCov (duafun-cov{l})
  covFunGlue-unaligned {l} = relCov1-relCov duafun-cov
                                            relCov-duaF


  ElCov-cased01 : ∀ {@♭ l : Level} {x : 𝟚}
            → {A : x == ``0 → UCov l} {B : x == ``1 → UCov l}
              (p : (x == ``0) ∨ (x == ``1))
              → ElCov (cased01 A B p) ==
                cased01 (\ x → ElCov (A x)) (\ y → ElCov (B y)) p
  ElCov-cased01 = ∨-elimd01 _ (\ _ → id) ((\ _ → id))


  eliminate-round-trip : ∀ {l : Level} {A : Set l} (B : Set l)
                       → (p : A == B) → (q : B == A)
                       {x : A}
                       → coe q (coe p x) == x
  eliminate-round-trip B id id = id

  -- align the above so that when dua-α-cov is always true it does
  -- what the covariance for A and B say to do 
  hasCov-FunGlue-fiber : {@♭ l : Level} (G : 𝟚 → FunGlueData {l})
                    (p∀α : (x : _) → dua-α-cov (G x))
                  → hasCov (duafun-cov o G) 
  hasCov-FunGlue-fiber G p∀α s' β {{ cβ }} t b =
    coe ((! (Glue-α _ _ _ _ ((p∀α s'))))∘ (ap El (ElCov-cased01 (p∀α s')))) (fst comT) ,
    ((\ pβ → ap (coe (! (Glue-α _ _ _ _ ((p∀α s'))) ∘ (ap El (ElCov-cased01 (p∀α s'))))) (fst (snd comT) pβ) ∘
              ! ( (eliminate-round-trip (El (ElCov (dua-T-cov (G s') (p∀α s'))))
                                        (! (ap El (ElCov-cased01 (p∀α s')))  ∘ (Glue-α (dua-α-cov (G s')) _ _ _ (p∀α s')) ) 
                                        (! (Glue-α _ _ _ _ (p∀α s')) ∘ ap El (ElCov-cased01 (p∀α s')))
                                        ) )   )) ,
    (λ { id →  ap (coe (! (Glue-α _ _ _ _ ((p∀α ``0))) ∘ (ap El (ElCov-cased01 (p∀α ``0))))) (snd (snd comT) id) ∘
              ! ( (eliminate-round-trip (El (ElCov (dua-T-cov (G ``0) (p∀α ``0))))
                                        (! (ap El (ElCov-cased01 (p∀α ``0)))  ∘ (Glue-α (dua-α-cov (G ``0)) _ _ _ (p∀α ``0)) ) 
                                        (! (Glue-α _ _ _ _ (p∀α ``0)) ∘ ap El (ElCov-cased01 (p∀α ``0)))
                                        ) ) })
    where
    comT = dcomEl (\ x → dua-T-cov (G x) (p∀α x)) s' β
                  (\ w pβ →   coe (! (ap El (ElCov-cased01 (p∀α w)))  ∘ (Glue-α _ _ _ _ (p∀α w)) ) (t w pβ)  )
                  ( (coe ( ! (ap El (ElCov-cased01 (p∀α ``0))) ∘ (Glue-α _ _ _ _ ((p∀α ``0))) ) (fst b))  ,
                    ((\ pβ → ap (coe (! (ap El (ElCov-cased01 (p∀α ``0))) ∘ (Glue-α _ _ _ _ (p∀α ``0)) )) ((snd b) pβ))) )

  abstract
    covFunGlue-aligned : {@♭ l : Level} → (G : 𝟚 → FunGlueData{l})
          → _[_↦_] (hasCov (duafun-cov o G)) ((x : _) → (dua-α-cov (G x) )) {{Cofib∀𝟚 {_} {\ x → Cofib∨ }}} (hasCov-FunGlue-fiber G)
    covFunGlue-aligned G = adjust-hasCov (duafun-cov o G) (covFunGlue-unaligned G) ((x : _) → (dua-α-cov (G x) )) {{Cofib∀𝟚 {_} {\ x → Cofib∨ } }} (hasCov-FunGlue-fiber G) 

    covFunGlue : {@♭ l : Level} → relCov (duafun-cov {l})
    covFunGlue G = fst (covFunGlue-aligned G)

    covFunGlue-∀α : {@♭ l : Level}(G : 𝟚 → FunGlueData {l})
               → (p∀α : (x₁ : 𝟚) → dua-α-cov (G x₁)) → hasCov-FunGlue-fiber G p∀α == covFunGlue G
    covFunGlue-∀α G =  snd (covFunGlue-aligned G) 

    covFunGlue-not∀α : {@♭ l : Level} (G : 𝟚 → FunGlueData {l})
               → (not∀α : ((x₁ : 𝟚) → dua-α-cov (G x₁)) → ⊥{lzero})
               → ∀ r' α {{cα : Cofib α}} t b
               → Path _ (fst (covFunGlue G r' α t b)) (fst (covFunGlue-unaligned G r' α t b)) 
    covFunGlue-not∀α G not∀α r' α {{cα}} t b = fst q ,
                                              fst (snd q)   ,
                                              snd (snd q) where
      q = adjust-hasCov-not (duafun-cov o G) (covFunGlue-unaligned G) ((x : _) → (dua-α-cov (G x) )) {{Cofib∀𝟚 {_} {\ x → Cofib∨ } }} (hasCov-FunGlue-fiber G)
                            not∀α r' α t b

  FunGlueUCov : {@♭ l : Level} → FunGlueData {l} → UCov l
  FunGlueUCov {l} = code-cov (FunGlueUKan o forget , covFunGlue {l}) 


  -- Check that sides of code are correct.
  --
  -- This is morally just a consequence of aligning and some messing around with the universe codes---
  -- aligning morally gives this in general without knowing that the cofibration is [i=0 ∨ i=1].
  -- But subsequently we will need the equations stated for each of A and B separately,
  -- to prove that FunGlueUCov (f : A → B) makes a Hom A B.
  -- 
  -- So we unpack the statement that the code is aligned for dua-T-cov (which is cased01 A B)
  -- into facts about each of A and B.  
  --
  -- Everything below here is morally just checking equations on the above.  
  -- But for stating the equations, it helps first write out what the relCov would be for A and B individually,
  -- with some equality wrappers built in, so we repeat a definition like that for
  -- hasCov-FunGlue-fiber here

  fix0 : {@♭ l : Level} (x : (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0)))
        → ElCov{l} (FunGlueUCov (fst x)) == ElCov{l} (FunGlueData.A (fst x))
  fix0 (d , eq) = FunGlueUKan0 (forget d) eq

  fix1 : {@♭ l : Level} (x : (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1)))
        → ElCov{l} (FunGlueUCov (fst x)) == ElCov{l} (FunGlueData.B (fst x))
  fix1 (d , eq) = FunGlueUKan1 (forget d) eq

  covFunGlue0 : {@♭ l : Level} →
                relCov {Γ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))}
                       (λ x → duafun-cov{l} (fst x))
  covFunGlue0 {l} p r α t b =
    transport El (! ((fix0 (p r)))) (fst c)
    , ( (λ pα → ap (transport El (! (fix0 (p r)))) (fst (snd c) pα) ∘ ! (ap= (transport-inv El (fix0 (p r))))  ) )
    , ( (λ {id → ap (transport El (! (fix0 (p r)))) (snd (snd c) id) ∘ ! (ap= (transport-inv El (fix0 (p r))))  }) ) where
    
    c = (dcomEl'{l} (λ x → FunGlueData.A (fst x)) p r α
                (λ z pα → transport El (fix0 (p z)) (t z pα))
                          (transport El (fix0 (p ``0)) (fst b) ,
                          (λ pα → ap (transport El (fix0 (p ``0))) (snd b pα))))


  covFunGlue1 : {@♭ l : Level} →
                relCov {Γ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))}
                       (λ x → duafun-cov{l} (fst x))
  covFunGlue1 {l} p r α t b = 
    transport El (! ((fix1 (p r)))) (fst c)
    , ( (λ pα → ap (transport El (! (fix1 (p r)))) (fst (snd c) pα) ∘ ! (ap= (transport-inv El (fix1 (p r))))  ) )
    , ( (λ {id → ap (transport El (! (fix1 (p r)))) (snd (snd c) id) ∘ ! (ap= (transport-inv El (fix1 (p r))))  }) ) where
    
    c = (dcomEl'{l} (λ x → FunGlueData.B (fst x)) p r α
                (λ z pα → transport El (fix1 (p z)) (t z pα))
                          (transport El (fix1 (p ``0)) (fst b) ,
                          (λ pα → ap (transport El (fix1 (p ``0))) (snd b pα))))

  
  -- covFunGlue has the correct sides on 0 and 1

  restricts0 : {@♭ l : Level}
                 (p : 𝟚 → Σ (λ d → FunGlueData.i d == ``0))
                 (r : 𝟚)
                 (α  : Set)
                 {{cα : Cofib α}}
                 (t : (z : 𝟚) → α → ((duafun-cov{l}) o fst o p) z)
                 (b : ((duafun-cov{l}) o fst o p) ``0 [ α ↦ t ``0 ])
               → _==_
                (fst (covFunGlue{l} (\ z → fst (p z)) r α t b))
                (fst (covFunGlue0{l} p r α t b))
  restricts0 {l} p r α t b = het-to-hom (!h (transport-=h El (! ( (FunGlueUKan0 (fungluedatakan (ElCov (FunGlueData.A (fst (p r)))) (ElCov (FunGlueData.B (fst (p r)))) (FunGlueData.f (fst (p r))) (FunGlueData.i (fst (p r)))) (snd (p r)))))) ∘h
                                           dcomEl=h {A = (λ x → FunGlueData.A (fst (p x)))} {A' = (λ x → FunGlueData.A (fst (p x)))} id r α
                                                   (λ=o1 \ w → λ=o1 \ h → (!h (transport-=h El (fix0 (p w))) ∘h  transport-=h (\ x → x) (id ∘ Glue-α _ _ _ _ (inl (snd (p w)))) ))
                                                   (((!h (transport-=h El (fix0 (p ``0))) ∘h transport-=h (\ x → x) (id ∘ Glue-α _ _ _ _ (inl (snd (p ``0)))))))  ∘h
                                           transport-=h (\ x → x) (! (Glue-α _ _ _ _ (inl (snd (p r))))) 
                                          )
                             -- aligning
                             ∘ (! (ap (\ H → fst (H r α t b)) (covFunGlue-∀α (\ z → fst (p z)) (\ z → inl (snd (p z))))))

  restricts1 : {@♭ l : Level}
                 (p : 𝟚 → Σ (λ d → FunGlueData.i d == ``1))
                 (r : 𝟚)
                 (α  : Set)
                 {{cα : Cofib α}}
                 (t : (z : 𝟚) → α → ((duafun-cov{l}) o fst o p) z)
                 (b : ((duafun-cov{l}) o fst o p) ``0 [ α ↦ t ``0 ])
               → _==_
                (fst (covFunGlue{l} (\ z → fst (p z)) r α t b))
                (fst (covFunGlue1{l} p r α t b))
  restricts1 {l} p r α t b = het-to-hom (!h (transport-=h El (! ( (FunGlueUKan1 (fungluedatakan (ElCov (FunGlueData.A (fst (p r)))) (ElCov (FunGlueData.B (fst (p r)))) (FunGlueData.f (fst (p r))) (FunGlueData.i (fst (p r)))) (snd (p r)))))) ∘h
                                           dcomEl=h {A = (λ x → FunGlueData.B (fst (p x)))} {A' = (λ x → FunGlueData.B (fst (p x)))} id r α
                                                   (λ=o1 \ w → λ=o1 \ h → (!h (transport-=h El (fix1 (p w))) ∘h  transport-=h (\ x → x) (id ∘ Glue-α _ _ _ _ (inr (snd (p w)))) ))
                                                   (((!h (transport-=h El (fix1 (p ``0))) ∘h transport-=h (\ x → x) (id ∘ Glue-α _ _ _ _ (inr (snd (p ``0)))))))  ∘h
                                           transport-=h (\ x → x) (! (Glue-α _ _ _ _ (inr (snd (p r))))) 
                                          )
                               -- aligning
                               ∘ (! (ap (\ H → fst (H r α t b)) (covFunGlue-∀α (\ z → fst (p z)) (\ z → inr (snd (p z))))))


  -- finally, there is some universe stuff to go from covFunGlue having the right sides to
  -- the codes based on these covariance proofs having the right sides
  private
    -- too slow if these are in an abstract block because other things reduce
    FunGlueUCov0' : {@♭ l : Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``0
                 → FunGlueUCov d == FunGlueData.A d
    FunGlueUCov0' {l} (fungluedata A B f .``0) id =
      (FunGlueUCov (fungluedata A B f ``0))
                   =〈 (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))} {Γ = FunGlueData {l}} {(ElCov{l}) o FunGlueUCov} {covFunGlue} fst ((fungluedata A B f ``0) , id)) 〉
      _
                   =〈 ap= (code-cov= (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0)) (\ x → (ElCov{l}) (FunGlueUCov (fst x))) (\ x → (ElCov{l}) (FunGlueData.A (fst x))) (dcomPre fst ((ElCov{l}) o FunGlueUCov) covFunGlue) (dcomEl'{l} (\ x → (FunGlueData.A (fst x)))) fix0 (λ p r α cα t b → restricts0{l} p r α {{cα}} t b )) 〉
      code-cov ((λ x → ElCov (FunGlueData.A (fst x))) , dcomEl' (λ x → FunGlueData.A (fst x))) (fungluedata A B f ``0 , id)
                   =〈  ! (universal-code-cov-η _) ∘ ! (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))} {Γ = UCov l} {A = ElCov} {dcomEl} (\ x → (FunGlueData.A (fst x))) ((fungluedata A B f ``0) , id)) 〉
      (A ∎)
    
    FunGlueUCov1' : {@♭ l : Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``1
                 → FunGlueUCov d == FunGlueData.B d
    FunGlueUCov1' {l} (fungluedata A B f .``1) id =
      (FunGlueUCov (fungluedata A B f ``1))
                   =〈 (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))} {Γ = FunGlueData {l}} {ElCov o FunGlueUCov} {covFunGlue} fst ((fungluedata A B f ``1) , id)) 〉
      _
                   =〈 ap= (code-cov= (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1)) (\ x → ElCov (FunGlueUCov (fst x))) (\ x → ElCov (FunGlueData.B (fst x))) (dcomPre fst (ElCov o FunGlueUCov) covFunGlue) (dcomEl' (\ x → (FunGlueData.B (fst x)))) fix1 (λ p r α cα t b →  restricts1{l} p r α {{cα}} t b)) 〉 
      code-cov ((λ x → ElCov (FunGlueData.B (fst x))) , dcomEl' (λ x → FunGlueData.B (fst x))) (fungluedata A B f ``1 , id)
                   =〈  ! (universal-code-cov-η _) ∘ ! (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))} {Γ = UCov l} {A = ElCov} {dcomEl} (\ x → (FunGlueData.B (fst x))) ((fungluedata A B f ``1) , id)) 〉
      (B ∎)


  -- abstract versions of the overall boundary equations
  -- so that they don't reduce in later files
  abstract
    FunGlueUCov0 : {@♭ l : Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``0
                 → FunGlueUCov d == FunGlueData.A d
    FunGlueUCov0 = FunGlueUCov0'
    
    FunGlueUCov1 : {@♭ l : Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``1
                 → FunGlueUCov d == FunGlueData.B d
    FunGlueUCov1 = FunGlueUCov1'

