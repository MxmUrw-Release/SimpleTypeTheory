{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core {i j} {param : LambdaParam i j} where


open import TypeTheory.Lambda.Core.Type {param = param} public
open import TypeTheory.Lambda.Core.Term {param = param} public
open import TypeTheory.Lambda.Core.TermSub {param = param} public
open import TypeTheory.Lambda.Core.TermSingSub {param = param} public
open import TypeTheory.Lambda.Core.TermProofs {param = param} public



