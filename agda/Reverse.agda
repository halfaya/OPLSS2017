module Reverse where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Properties.Simple using (+-comm)

foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
reverse []       = []
reverse {n = suc n} (x ∷ xs) rewrite (+-comm 1 n) = reverse xs ++ (x ∷ [])
