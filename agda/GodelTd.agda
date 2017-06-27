module GodelTd where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Typ : Set where
  nat : Typ
  arr : Typ → Typ → Typ

data Exp : Set where
  var : ℕ → Exp
  z   : Exp
  s   : Exp → Exp
  rec : Exp → Exp → Exp → Exp
  lam : Typ → Exp → Exp
  ap  : Exp → Exp → Exp

infix  3 _⊦_∷_
infixl 4 _∷ᵣ_

data Ctx : Set where
  []   : Ctx
  _∷ᵣ_ : Ctx → Typ → Ctx

data _⊦_∷_ : Ctx → Exp → Typ → Set where
  refl : {Γ : Ctx} → {τ : Typ} → Γ ∷ᵣ τ ⊦ var 0 ∷ τ
  zero : {Γ : Ctx} → Γ ⊦ z ∷ nat
  suc  : {Γ : Ctx} → {e : Exp} → Γ ⊦ e ∷ nat → Γ ⊦ s e ∷ nat
  rec  : {Γ : Ctx} → {e e₀ e₁ : Exp} → {τ : Typ} →
         Γ ⊦ e ∷ nat →
         Γ ⊦ e₀ ∷ τ →
         Γ ∷ᵣ nat ∷ᵣ τ ⊦ e₁ ∷ τ →
         Γ ⊦ rec e₀ e₁ e ∷ τ
  lam  : {Γ : Ctx} → {e : Exp} → {τ₁ τ₂ : Typ} →
         Γ ∷ᵣ τ₁ ⊦ e ∷ τ₂ → Γ ⊦ lam τ₁ e ∷ arr τ₁ τ₂
  app  : {Γ : Ctx} → {e₁ e₂ : Exp} → {τ τ₂ : Typ} →
         Γ  ⊦ e₁ ∷ arr τ₂ τ → Γ ⊦ e₂ ∷ τ₂ → Γ ⊦ ap e₁ e₂ ∷ τ
