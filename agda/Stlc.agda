module Stlc where

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then  x else _ = x
if false then _ else y = y

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

Var = ℕ

data Exp : Set where
  t   : Exp
  f   : Exp
  z   : Exp
  s   : Exp → Exp
  var : Var → Exp
  lam : Var → Exp → Exp
  ap  : Exp → Exp → Exp

 
