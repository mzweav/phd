{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Path
open import universe.Universe
open import FWeld-Weak
open import FibWeld
open import Equiv
open import universe.Path
open import Contractible

module universe.FibWeld where

  -- fix-globe : {l : Level} {A : Set l}
  --           → hasHCom A
  --           → {a0 a1 : A}
  --           → {p q : Path A a0 a1}
  --           → Path (Path A a0 a1) p q
  --           → {a0' : A}
  --           → (r : Path A a0' a0)
  --           → (s : Path A a0' a1)
  --           → (t : Path A a0' a1)
  --           → PathO (\ z → Path A (fst r z) a1)
  --                   ((fst s , ! (fst (snd r)) ∘ fst (snd s) , snd (snd s)))
  --                   (fst p , ! (snd (snd r)) ∘ fst (snd p) , snd (snd p))
  --           → PathO (\ z → Path A (fst r z) a1)
  --                   ((fst t , ! (fst (snd r)) ∘ fst (snd t) , snd (snd t)))
  --                   (fst q , ! (snd (snd r)) ∘ fst (snd q) , snd (snd q))
  --           → Path (Path A a0' a1) s t
  -- fix-globe hcomA {a0 = a0} {a1} g {a0'} r s t sq sq' =
  --   (λ x → (λ y → fst (g' x y)) ,
  --          fst (snd r) ∘ ! (fst (snd (g' x `0)) (inr (inl id))) ,
  --          ! (fst (snd (g' x `1)) (inr (inr id)))) ,
  --          pair= (λ= \ y → ap (\ H → fst H y) (fst (snd sq)) ∘ ! (fst (snd (g' `0 y)) (inl (inl id)))) (pair= uip uip) ,
  --          pair= ((λ= \ y → ap (\ H → fst H y) (fst (snd sq')) ∘ ! (fst (snd (g' `1 y)) (inl (inr id))))) (pair= uip uip) where
  --   g' : ∀ x y → _
  --   g' x y = hcomA `1 `0 (((x == `0) ∨ (x == `1)) ∨ ((y == `0) ∨ (y == `1)))
  --                        (\ z → case (case01 (\ x=0 → fst (fst sq z) y )
  --                                            (\ x=1 → fst (fst sq' z) y))
  --                                    (case01 (\ y=0 → fst r z)
  --                                            (\ y=1 → a1))
  --                                    (∨-elim01 _ (\ x=0 → ∨-elim01 _ (\ y=0 → fst (snd (fst sq z)) ∘ {!OK!})
  --                                                                    (\ y=1 → snd (snd (fst sq z)) ∘ {!OK!}))
  --                                                ((\ x=1 → ∨-elim01 _ (\ y=0 → fst (snd (fst sq' z)) ∘ {!OK!})
  --                                                                     (\ y=1 → snd (snd (fst sq' z)) ∘ {!OK!})))))
  --                        (fst (fst g x) y ,
  --                         ∨-elim _ (∨-elim01 _ (\ x=0 → {!OK!} ∘ ap (\ H → fst H y) (! (fst (snd g))) ∘ ap (\ H → fst H y) (snd (snd sq)) )
  --                                              (\ x=1 → {!OK!} ∘ ap (\ H → fst H y) (! (snd (snd g))) ∘ ap (\ H → fst H y) (snd (snd sq'))))
  --                                  (∨-elim01 _ (\ y=0 → {!OK!} ∘ ! (fst (snd (fst g x))) ∘ fst (snd (fst g x)) ∘ ! (fst (snd (fst g x))) ∘ snd (snd r))
  --                                              (\ y=1 →  ap (fst (fst g x)) (! y=1) ∘ ! (snd (snd (fst g x))) ))
  --                                  (\ _ _ → uip))

  apPath : ∀ {l1 l2} {A : Set l1} {B : Set l2} {a1 a2 : A} (f : A → B) → Path A a1 a2 → Path B (f a1) (f a2)
  apPath f p = (\ x → f (fst p x)) , (ap f (fst (snd p)) , ap f (snd (snd p)))

  abstract
    back : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} → EquivFill A B → B → A
    back e b =  fst (fst ((snd e b) ⊥ (\ x → abort x))) 
    
    inv1 : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} → (e : EquivFill A B) → (b : B) → Path B (fst e (back e b)) b
    inv1 e b =  snd (fst ((snd e b) ⊥ (\ x → abort x))) 
    
    inv2 : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} → (e : EquivFill A B) → (a : A) → Path A a (back e (fst e a))
    inv2 e a = (\ x → fst (fst (use x))) , ! (ap fst ((snd (use `0)) (inl id))) ,  ! (ap fst ((snd (use `1)) (inr id))) where
      use : ∀ x → _
      use x = snd e (fst e a) ((x == `0) ∨ (x == `1))
                  (case01 (\ x=0 → a  , (\ _ → fst e a) , id , id)
                          (\ x=1 → fst (snd e (fst e a) ⊥ (\ x → abort x))))
    
    triangle : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} (hcomB : hasHCom B) → (e : EquivFill A B) (a : A)
         → Path (Path B
                      (fst e (back e (fst e a)))
                      (fst e a))
                (!Path hcomB (apPath (fst e) (inv2 e a)))
                (inv1 e (fst e a))
    triangle hcomB e a = {!!} where -- (\ x → (\ y → fst (snd (fst (use y))) x ) , {!!} ∘ ap (\ H → fst (snd H) x) (! (snd (use `0) (inl id))) , {!!}) , {!!} , {!!} 
      use : ∀ x → _
      use x = snd e (fst e a) ((x == `0) ∨ (x == `1))
                  (case01 (\ x=0 → a  , (\ _ → fst e a) , id , id)
                          (\ x=1 → fst (snd e (fst e a) ⊥ (\ x → abort x))))

  record WeldData (l :{♭} Level) : Set (ℓ₂ ⊔ lsuc l) where
    constructor welddata
    field
      α : Set
      c : Cofib α
      B : U{l}
      T : α → U{l}
      f : (pα : α) → El B → El (T pα) 
      feq : (pα : α) → isEquivFill _ _ (f pα)

  Weld-from-data : {l :{♭} Level} → WeldData l → Set l
  Weld-from-data (welddata α cα B T f feq) = Weld α {{ cα }} (El o T) (El B) f

  hcomWeld : {l :{♭} Level}(W : WeldData l) → hasHCom (Weld-from-data W)
  hcomWeld = (\ W r r' β t b →
                fst (whcom {{cα = WeldData.c W}} (\ pα → hcomEl (WeldData.T W pα)) r r' β t b) ,
                fst (snd (whcom {{cα = WeldData.c W}} (\ pα → hcomEl (WeldData.T W pα)) r r' β t b)) ,
                (\ r=r' → fst (snd (snd (whcom {{cα = WeldData.c W}} (λ pα → hcomEl (WeldData.T W pα)) r r' β t b))) r=r'))
  
  !Path-Weld : {l :{♭} Level} (W : WeldData l) {w w' : _}
               (ws : Path (Weld-from-data W) w w')
               (pα : WeldData.α W)
               (x : I)
             → (fst (!Path (hcomWeld W) ws) x) ==
               coe (! (Weld-α _ {{cα = WeldData.c W}} _ _ _ pα))
                   (fst (!Path (hcomEl (WeldData.T W pα))
                               (apPath (coe (Weld-α _ {{cα = WeldData.c W}} _ _ _ pα)) ws ))
                               x) 
  !Path-Weld W {w = w} {w'}ws pα x = ap (coe (! (Weld-α _ {{cα = WeldData.c W}} _ _ _ pα)))
                                        (het-to-hom (comEl=h id `0 `1 ((x == `0) ∨ (x == `1))
                                                                (λ=o1 \ z → λ=o1 (∨-elim01 _ (\ x=0 → hid) ((\ x=1 → hid))))
                                                                hid))
                                     ∘ ! (snd (snd (snd h)) pα) where
    -- FIXME: can't figure out how to do this without rewriting inverse here
    h = (whcom {{cα = (WeldData.c W)}} (\ pα → (hcomEl (WeldData.T W pα))) `0 `1 ((x == `0) ∨ (x == `1)) 
               (\ z → case (\ x=0 → (fst ws z))
                          ((\ x=1 →  w))
                          (\ p q → abort (iabort (q ∘ ! p))))
              (w , ∨-elim _ ( (\ x=0 → ((fst (snd ws))) )) ( ((λ x=1 → id)) ) (\ _ _ → uip)))
  
  wcoeWeld : {l :{♭} Level} → relWCoe (Weld-from-data{l})
  wcoeWeld W r r' = C.wrec-weak r' , ((\ {id → cr})) where

    inα : (x : I) (pα : (WeldData.α (W x))) → El (WeldData.T (W x) pα) → (Weld-from-data (W x))
    inα x pα = coe (! (Weld-α _ {{cα = WeldData.c (W x)}} _ _ _ pα))

    outα : (x : I) (pα : (WeldData.α (W x))) → (Weld-from-data (W x)) → El (WeldData.T (W x) pα)
    outα x pα = coe (Weld-α _ {{cα = WeldData.c (W x)}} _ _ _ pα)

    win' : (x : I) → El (WeldData.B (W x)) → (Weld-from-data (W x))
    win' x = win _ {{cα = WeldData.c (W x)}} _ _ _ 

    BTpath : ∀ r' b pα → _
    BTpath r' = (\ b pα → apPath (\ H → win' _ (fst (coeU (WeldData.B o W) r r' H))) (inv2 (_ , (WeldData.feq (W r) pα)) b))

    {- C.wrec-weak r' is wcoe_W r -> r' -}
    module C (r' : I) = WRec-Weak {{cα = WeldData.c (W r)}} _ (hcomWeld (W r'))
                                  {- B branch: coerce in B, and then inject through B(r') -}
                                  (\ br → win' r' (fst (coeU (WeldData.B o W) r r' br)))
                                  {- T branch: send down from T(r) to B(r) by f^-1,
                                               coerce in B,
                                               inject through B(r')
                                  -}
                                  (\ pα tr → win' r' (fst (coeU (WeldData.B o W) r r' (back (_ , (WeldData.feq (W r) pα)) tr) )))
                                  {-
                                  Path from B branch to T branch on α:
                                  starting from b:B, the B branch coerces in B and injects from B(r').
                                  the T branch sends it up and back down via f(r), and then 
                                  coerces in B and injects in B(r').
                                  so the path we need is the up-then-down cancelation law, i.e.
                                  f^-1(f b) = b
                                  -}
                                  (BTpath r')

    {- path from coe^r->r(w) to w -}
    cr : (w : (Weld-from-data o W) r) → Path _ (C.wrec-weak r w) w
    cr = WElim-Weak.E.welim _ ((comPath-endpoints (\ b → C.wrec-weak r b) (\ b → b) (hcomWeld (W r))))
                              Bcase
                              Tcase
                              (\ a pα →  (\ x → (\ y → fst (fst (tri' a pα) x) y) ,
                                         ! (left a pα) ∘ fst (snd (fst (tri' a pα) x)) ,
                                         ! (right a pα) ∘ snd (snd (fst (tri' a pα) x))) ,
                                       pair= (λ= \ y → (! (ap (\ H → fst H y) (Bcaseα a pα)) ∘ ! (!Path-Weld (W r) (finv2-path a pα) pα y) ∘ ap (inα r pα) (het-to-hom (comEl=h id _ _ _ (λ=o1 (\ z → λ=o1 (∨-elim01 _ (\ y=0 → hom-to-het (! (ap= (transport-inv-2 (\ x → x) (Weld-α _ {{cα = (WeldData.c (W r))}} _ _ _ pα))))) ((\ y=1 → hom-to-het ((! (win-α _ {{WeldData.c (W r)}} _ _ _ _ pα)))))))) (hom-to-het (! (win-α _ {{WeldData.c (W r)}} _ _ _ _ pα)))))) ∘ ap (\ H → fst H y) (fst (snd (tri' a pα))))
                                             (pair= uip uip) ,
                                       pair= ( ((λ= \ y → (! (ap= (fst-transport-Path' {A = \ _ → _} {a0 = \ z → (C.wrec-weak r z)} {a1 = \ z → z}(win-α! _ {{cα = WeldData.c (W r)}} _ _ _ _ pα) (Tcase pα (WeldData.f (W r) pα a)))) ∘ ap= (! (transport-constant (win-α! _ {{cα = WeldData.c (W r)}} _ _ _ _ pα)))) ∘ ap (\ H → fst H y) (snd (snd (tri' a pα)))) ) )
                                             (pair= uip uip)  ) where

      {- case for B: 
         since coe_B^r->r cancels definitionally, we just need the 
         weak β for wrec-weak, i.e. path from wrec-weak (win b) to win b
       -}
      Bcasep : ∀ b → Path _ (win' r b) (C.wrec-weak r (win' r b))
      Bcasep b = (fst (fst (C.wrec-weak-win r b)) , ap (win' r) (! ((snd (coeU (WeldData.B o W) r r b)) id)) ∘
                  fst (snd (fst (C.wrec-weak-win r b))) , snd (snd (fst (C.wrec-weak-win r b))))

      {- flip around -- maybe there's a way to avoid this by rigging the definitions so that
         everything comes out in the correct orientation? -}
      Bcase : ∀ b → Path _ (C.wrec-weak r (win' r b)) (win' r b)
      Bcase b = (!Path (hcomWeld (W r)) (Bcasep b))

      abstract
        {- on α, coe_W r->r is f(r) o f^-1(r):
                 expanding the branch of the welim and canceling the coe_B gets to win(r)(f^-1 t)
                 and then win(r)(-) is f(r)(-) on α
         -}
        left-t : (pα : _) (t : El (WeldData.T (W r) pα)) → 
                 (C.wrec-weak r (inα r pα t)) == inα r pα (WeldData.f (W r) pα (back (_ , (WeldData.feq(W r) pα)) t))
        left-t pα t = (ap (inα r pα) (ap (WeldData.f (W r) pα) (! (snd (coeU (WeldData.B o W) r r _) id))) ∘
                                     ! (win-α! _ {{cα = WeldData.c (W r)}} _ _ _ _ pα) )
                      ∘ C.wrec-weak-α r pα t 

      {- case for T: 
         by left-t, we need a path f(r)(f^-1(r) t) to t
         i.e. the other composite law.  
       -}
      Tcase : ∀ pα (t : El (WeldData.T (W r) pα)) → Path _ (C.wrec-weak r (inα r pα  t)) (inα r pα t)
      Tcase pα t = (\ z → inα r pα (fst (inv1 ( _ , WeldData.feq (W r) pα) t) z)) ,
                ! (left-t pα t) ∘ ap (inα r pα) ((fst (snd (inv1 ( _ , WeldData.feq (W r) pα) t)))) ,
                ap (inα r pα) ((snd (snd (inv1 ( _ , WeldData.feq (W r) pα) t))))

      -- manual beta reduction

      abstract
         right : ∀ b (pα : _) → (win' r b) == inα r pα (WeldData.f (W r) pα b )
         right b pα = ! (win-α! _ {{cα = WeldData.c (W r)}} _ _ _ _ pα)

         {- on α, (C.wrec-weak r (win' r b)) is f(f^1(f b)) -}
         left : ∀ b (pα : _) → (C.wrec-weak r (win' r b))
               == inα r pα (WeldData.f (W r) pα (back (_ , (WeldData.feq (W r) pα)) (WeldData.f (W r) pα b )) )
         left b pα = (ap (\ H → inα r pα (WeldData.f (W r) pα H))
                     (  (ap (back (_ , WeldData.feq (W r) pα))
                        ((ap= (transport-inv-2 (\ x → x) (Weld-α _ {{cα = (WeldData.c (W r))}} _ _ _ pα)) ) ∘
                         ap (outα r pα) (right _ pα))
                        ∘ ! ((snd (coeU (WeldData.B o W) r r _)) id)) )
                     ∘ right _ pα)
                     ∘ C.wrec-weak-α' r pα (win' r b) 

      -- the path that comes up in the coherence is f (inv2(b))
      finv2 : _
      finv2 = (\ b pα → apPath (\ b → inα r pα (WeldData.f (W r) pα b )) (inv2 (_ , (WeldData.feq (W r) pα)) b))

      finv2-path : ∀ b p-α → _
      finv2-path b pα = ( fst (finv2 b pα) , ! (right b pα) ∘ fst (snd (finv2 b pα))   , ! (left b pα) ∘ snd (snd (finv2 b pα))    )

      abstract
        {- on α, the B case reduces to f(inv2(b)), because BTpath does:
           the ap f is from the win around the inv2
         -}
        Bcasepα : ∀ b (pα : (WeldData.α (W r)))
             → Bcasep b ==  finv2-path b pα
        Bcasepα b pα =  pair= ((λ= \ z → right _ pα ∘ ap (win' r) (! (snd (coeU (WeldData.B o W) r r _) id))) ∘
                              ap fst (! (snd (C.wrec-weak-win r b) pα)))
                             (pair= uip uip)  

      -- (but flipped)
      Bcaseα : ∀ b (pα : (WeldData.α (W r))) → (Bcase b) == (!Path (hcomWeld (W r)) (fst (finv2 b pα) , _ , _))
      Bcaseα b pα = ap (!Path (hcomWeld (W r))) (Bcasepα b pα)

      abstract
        -- use triangle directly
        tri : ∀ t pα → Path (Path (El (WeldData.T(W r) pα))
                                  (WeldData.f (W r) pα (back (_ , WeldData.feq (W r) pα) (WeldData.f (W r) pα t)))
                                  (WeldData.f (W r) pα t))
                            (!Path (hcomEl (WeldData.T (W r) pα)) (apPath (WeldData.f (W r) pα) (inv2 (_ , WeldData.feq (W r) pα) t)))
                            (inv1 (_ , WeldData.feq (W r) pα) (WeldData.f (W r) pα t))
        tri t pα = (triangle (hcomEl (WeldData.T (W r) pα)) (_ , WeldData.feq (W r) pα) t)

        -- transport along strict equality to get it in Weld
        -- FIXME: make apglobe lemma
        tri' : ∀ t pα → Path (Path (Weld-from-data (W r))
                                   (inα r pα (WeldData.f (W r) pα (back (_ , WeldData.feq (W r) pα) (WeldData.f (W r) pα t))))
                                   (inα r pα (WeldData.f (W r) pα t)))
                             (apPath (inα r pα) ((!Path (hcomEl (WeldData.T (W r) pα)) (apPath (WeldData.f (W r) pα) (inv2 (_ , WeldData.feq (W r) pα) t)))))
                             (apPath (inα r pα) ((inv1 (_ , WeldData.feq (W r) pα) (WeldData.f (W r) pα t))))
        tri' t pα = (\ x → ((\ y → inα r pα (fst (fst (tri t pα) x) y)) ,
                            ( ap (inα r pα) (fst (snd (fst (tri t pα) x))) , ap (inα r pα) (snd (snd (fst (tri t pα) x)))))) ,
                            (pair= (λ= \ x → ap (inα r pα) (ap (\ H → fst H x) (fst (snd (tri t pα))))) (pair= uip uip) ,
                             pair= (λ= \ x → ap (inα r pα) (ap (\ H → fst H x) (snd (snd (tri t pα))))) (pair= uip uip))

  comWeld-unaligned : {l :{♭} Level} → relCom (Weld-from-data{l})
  comWeld-unaligned {l} = decompose-com (Weld-from-data{l})
                                        hcomWeld
                                        ( coe-from-wcoe (Weld-from-data {l}) hcomWeld wcoeWeld ) where


