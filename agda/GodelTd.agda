module GodelTd where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

Var = ℕ

data Typ : Set where
  nat : Typ
  arr : Typ → Typ → Typ

data Exp : Set where
  var : Var → Exp
  z   : Exp
  s   : Exp → Exp
  rec : Exp → Exp → Exp → Exp
  lam : Typ → Exp → Exp
  ap  : Exp → Exp → Exp

infix  3 _⊦_∷_ _↦_
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

data Val : Exp → Set where
  zero : Val z
  suc  : {e : Exp} → Val e → Val (s e)
  lam  : {e : Exp} → {τ : Typ} → Val (lam τ e)

-- substitute e for variable 0 in e'
subst : Exp → Exp → Exp
subst e (var zero)     = e
subst e (var (suc n))  = var n
subst e z              = z
subst e (s e')         = s (subst e e')
subst e (rec e₀ e₁ e') = {!!}
subst e (lam x e')     = {!!}
subst e (ap e₀ e₁)     = {!!}

data _↦_ : Exp → Exp → Set where
  suc  : {e e' : Exp} → e ↦ e' → s e ↦ s e'
  app₁ : {e₁ e₂ e₁' : Exp} → e₁ ↦ e₁' → ap e₁ e₂ ↦ ap e₁' e₂
  app₂ : {e₁ e₂ e₂' : Exp} → Val e₁ → e₂ ↦ e₂' → ap e₁ e₂ ↦ ap e₁ e₂'
  appλ : {e e₂ : Exp} → {τ : Typ} → Val e₂ → ap (lam τ e) e₂ ↦ subst e₂ e
  rece : {e e' e₀ e₁ : Exp} → e ↦ e' → rec e₀ e₁ e ↦ rec e₀ e₁ e'
  recz : {e₀ e₁ : Exp} → rec e₀ e₁ z ↦ e₀
  recs : {e e₀ e₁ : Exp} → Val (s e) → rec e₀ e₁ (s e) ↦ subst e (subst (rec e₀ e₁ e) e₁)
