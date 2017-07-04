module GodelTd where

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

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc n = false
suc m == zero  = false
suc m == suc n = m == n

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

cong : {A B : Set} → {a a' : A} → (f : A → B) → a ≡ a' → f a ≡ f a'
cong f refl = refl

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

infix  3 _⊢_⟨_⟩ _↦_
infixl 4 _∷ᵣ_

data Ctx : Set where
  []   : Ctx
  _∷ᵣ_ : Ctx → Typ → Ctx

data _⊢_⟨_⟩ : Ctx → Exp → Typ → Set where
  refl : {Γ : Ctx} → {τ : Typ} → Γ ∷ᵣ τ ⊢ var 0 ⟨ τ ⟩
  zero : {Γ : Ctx} → Γ ⊢ z ⟨ nat ⟩
  suc  : {Γ : Ctx} → {e : Exp} → Γ ⊢ e ⟨ nat ⟩ → Γ ⊢ s e ⟨ nat ⟩
  rec  : {Γ : Ctx} → {e e₀ e₁ : Exp} → {τ : Typ} →
         Γ ⊢ e ⟨ nat ⟩ →
         Γ ⊢ e₀ ⟨ τ ⟩ →
         Γ ∷ᵣ nat ∷ᵣ τ ⊢ e₁ ⟨ τ ⟩ →
         Γ ⊢ rec e₀ e₁ e ⟨ τ ⟩
  lam  : {Γ : Ctx} → {e : Exp} → {τ₁ τ₂ : Typ} →
         Γ ∷ᵣ τ₁ ⊢ e ⟨ τ₂ ⟩ → Γ ⊢ lam τ₁ e ⟨ arr τ₁ τ₂ ⟩
  app  : {Γ : Ctx} → {e₁ e₂ : Exp} → {τ τ₂ : Typ} →
         Γ  ⊢ e₁ ⟨ arr τ₂ τ ⟩ → Γ ⊢ e₂ ⟨ τ₂ ⟩ → Γ ⊢ ap e₁ e₂ ⟨ τ ⟩

data Val : Exp → Set where
  zero : Val z
  suc  : {e : Exp} → Val e → Val (s e)
  lam  : {e : Exp} → {τ : Typ} → Val (lam τ e)

-- substitute e for variable v in e'
subst : Exp → Var → Exp → Exp
subst e v (var x)        = if v == x then e else var x
subst e v z              = z
subst e v (s e')         = s (subst e v e')
subst e v (rec e₀ e₁ e') = rec (subst e v e₀) (subst e v e₁) (subst e v e')
subst e v (lam x e')     = lam x (subst e (suc v) e')
subst e v (ap e₀ e₁)     = ap (subst e v e₀) (subst e v e₁)

-- one step call by value
data _↦_ : Exp → Exp → Set where
  suc  : {e e' : Exp} → e ↦ e' → s e ↦ s e'
  app₁ : {e₁ e₂ e₁' : Exp} → e₁ ↦ e₁' → ap e₁ e₂ ↦ ap e₁' e₂
  app₂ : {e₁ e₂ e₂' : Exp} → Val e₁ → e₂ ↦ e₂' → ap e₁ e₂ ↦ ap e₁ e₂'
  appλ : {e e₂ : Exp} → {τ : Typ} → Val e₂ → ap (lam τ e) e₂ ↦ subst e₂ zero e
  rece : {e e' e₀ e₁ : Exp} → e ↦ e' → rec e₀ e₁ e ↦ rec e₀ e₁ e'
  recz : {e₀ e₁ : Exp} → rec e₀ e₁ z ↦ e₀
  recs : {e e₀ e₁ : Exp} → Val (s e) → rec e₀ e₁ (s e) ↦ subst e zero (subst (rec e₀ e₁ e) zero e₁)

--------------

-- Task 2.1

stepDet : (e e₁ e₂ : Exp) → (e ↦ e₁) → (e ↦ e₂) → e₁ ≡ e₂
stepDet .(s e) .(s e₁) .(s e₂) (suc {e} {e₁} x) (suc {.e} {e₂} x') = cong s (stepDet e e₁ e₂ x x')
stepDet .(ap _ _) .(ap _ _) e (app₁ {e₀} {e₁} {e₂} x) x' = {!!}
stepDet .(ap _ _) .(ap _ _) e (app₂ {e₀} {e₁} {e₂} x x₁) x' = {!!}
stepDet .(ap (lam _ _) _) _ {-.(subst _ 0 _)-} e₂ (appλ x) x' = {!!}
stepDet .(rec _ _ _) .(rec _ _ _) e₂ (rece x) x' = {!!}
stepDet .(rec e₁ _ z) e₁ e₂ recz x' = {!!}
stepDet .(rec _ _ (s _)) _ {-.(subst _ 0 (subst (rec _ _ _) 0 _))-} e₂ (recs x) x' = {!!}

--------------

-- plus = λ a → λ b → rec a b (λ _ → λ r → suc r)
plus : Exp
plus = lam nat (lam nat (rec (var 0) (lam nat (lam nat (s (var 0)))) (var 1)))

seven = ap (ap plus (var 3)) (var 4)

