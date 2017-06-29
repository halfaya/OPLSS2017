module RecursiveTypes where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data ⊤ : Set where
  tt : ⊤

data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (a , _) = a

snd : {A B : Set} → A × B → B
snd (_ , b) = b

data _+_ (A : Set) (B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

--------------

{-# TERMINATING #-}
rec : (Set → Set) → Set
rec f = f (rec f)

FNat : Set → Set
FNat A = ⊤ + A

Nat : Set
Nat = rec FNat

rzero : Nat
rzero = inl tt

rsuc : Nat → Nat
rsuc = λ n → inr n

ncase : (S : Set) → Nat → (⊤ → S) → (Nat → S) → S
ncase S (inl l) b s = b l
ncase S (inr r) b s = s r

pred : Nat → Nat
pred n = ncase Nat n (λ _ → rzero) (λ k → k)

nrec : Nat → (⊤ → Nat) → (Nat → Nat) → Nat
nrec (inl l) b s = b l
nrec (inr r) b s = s (nrec r b s)

plus : Nat → Nat → Nat
plus a b = nrec a (λ _ → b) (λ k → rsuc k)

five : Nat
five = plus (rsuc (rsuc (rsuc rzero))) (rsuc (rsuc rzero))

------------

-- Roll and Unroll seem superfluous here

roll : FNat Nat → Nat
roll x = x

unroll : Nat → FNat Nat
unroll x = x

rzero' : Nat
rzero' = roll (inl tt)

rsuc' : Nat → Nat
rsuc' = λ n → roll (inr n)

{-
-- Loops when type checking.
{-# NON_TERMINATING #-}
ncase : (S : Set) → Nat → (⊤ → S) → (Nat → S) → S
ncase S n b s with unroll n
ncase S n b s | (inl l) = b l
ncase S n b s | (inr r) = s r
-}
