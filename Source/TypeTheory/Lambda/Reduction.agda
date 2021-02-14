{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Reduction {i j} {param : LambdaParam i j} where


open import TypeTheory.Lambda.Reduction.Beta {param = param} public
open import TypeTheory.Lambda.Reduction.NormalForm {param = param} public
open import TypeTheory.Lambda.Reduction.NormalFormProofs {param = param} public

