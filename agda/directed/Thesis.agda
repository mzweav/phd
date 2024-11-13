{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Interval
open import Proposition
open import Cofibs
open import Equiv
open import Path
open import Kan
open import universe.Universe
open import universe.U
open import universe.Univalence
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import directed.DirInterval
open import directed.Dircrete
open import directed.Covariant
open import directed.UCov
open import directed.universe.UCov-Com
open import directed.universe.Pi
open import directed.universe.Sigma
open import directed.universe.Path
open import directed.universe.Hom
open import directed.universe.FunGlue
open import directed.descent.Lex
open import directed.descent.Pi
open import directed.descent.Sigma
open import directed.descent.Path
open import directed.descent.Hom
open import directed.descent.FunGlue


module directed.LICS where

  ---------------
  -- Chapter 3 --
  ---------------

  lemma-3-2-4 = directed.Dircrete.discFill-hprop
  lemma-3-2-5-1 = directed.Dircrete.discFill-to-discFill01
  lemma-3-2-5-2 = directed.Dircrete.discFill01-to-discFill
  proposition-3-2-6-1 = directed.Dircrete.isDisc-to-discFill
  proposition-3-2-6-2 = directed.Dircrete.discFill-to-isDisc
  theorem-3-3-2-1 = directed.universe.Sigma
  theorem-3-3-2-2 = directed.universe.Pi
  theorem-3-3-2-3 = directed.universe.Path
  theorem-3-3-2-4 = directed.universe.Hom
  lemma-3-3-3 = directed.universe.Glue-Equiv-Covariant.GlueUCov
  theorem-3-3-4 = directed.DirUnivalence.ua
  theorem-3-3-5 = directed.universe.UCov-Com.UCovU

  ---------------
  -- Chapter 4 --
  ---------------
  lemma-4-1-1 = directed.universe.FunGlue.FunGlueUKan
  lemma-4-1-2 = directed.universe.FunGlue.FunGlueUCov
  lemma-4-1-3 = directed.DirUnivalence.duaβ
  lemma-4-1-4 = directed.DirUnivalence.duaηfun
  lemma-4-2-2 = directed.descent.Lex.QisStack-to-isStack
  lemma-4-2-3 = directed.descent.Pi.ΠisStack
  lemma-4-2-4 = directed.descent.Lex.DΣ-Path
  lemma-4-2-5 = directed.descent.Sigma.ΣisStack
  lemma-4-2-7 = directed.descent.Stack.UCobar-isStack
  lemma-4-2-16 = directed.descent.Path.PathO-isStack
  lemma-4-2-17 = directed.descent.Hom.HomO-isStack
  lemma-4-2-19 = directed.descent.FunGlue.Glue-isStack
  lemma-4-2-25 = directed.DirUnivalence.duaη
  theorem-4-2-26 = directed.DirUnivalence.dua
