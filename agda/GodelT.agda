module GodelT where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (a , _) = a

snd : {A B : Set} → A × B → B
snd (_ , b) = b

data _+_ (A : Set) (B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data ⊤ : Set where
  tt : ⊤

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

data List : Set where
  []  : List
  _∷_ : ℕ → List → List

------

rec : {A : Set} → ℕ →  A → (ℕ → A → A) → A
rec zero    e₀ e₁ = e₀
rec (suc n) e₀ e₁ = e₁ n (rec n e₀ e₁)

iter : {A : Set} → ℕ →  A → (A → A) → A
iter zero    e₀ e₁ = e₀
iter (suc n) e₀ e₁ = e₁ (iter n e₀ e₁)

plus : ℕ → ℕ → ℕ
plus = λ a → λ b → rec a b (λ _ → λ r → suc r)

plus' : ℕ → ℕ → ℕ
plus' = λ a → λ b → iter a b (λ r → suc r)

x = plus' 3 7

mult : ℕ → ℕ → ℕ
mult = λ a → λ b → rec a zero (λ _ → λ r → plus b r)

mult' : ℕ → ℕ → ℕ
mult' = λ a → λ b → rec a zero (λ _ → λ r → (λ a → λ b → rec a b (λ _ → λ r → suc r)) b r)

mult'' : ℕ → ℕ → ℕ
mult'' = λ a → λ b → iter a zero (λ r → plus b r)

y = mult'' 31 70

fact : ℕ → ℕ
fact = λ a → rec a 1 (λ x → λ r → mult (suc x) r)

fact' : ℕ → ℕ
fact' = λ a → iter a 1 (λ r → mult a r)

z = fact' 6

pred : ℕ → ℕ
pred = λ a → rec a zero (λ x → λ _ → x)

pred× : ℕ → ℕ × ℕ
pred× = λ n → iter n (0 , 0) (λ p → (snd p , suc (snd p)))

pred' : ℕ → ℕ
pred' = λ a → fst (pred× a)

sub  : ℕ → ℕ → ℕ
sub = λ a → λ b → rec b a (λ _ → λ r → pred r)

reci : {A : Set} → ℕ → A → (ℕ → A → A) → A
reci = λ n → λ b → λ s → snd (iter n (0 , b) (λ p → (suc (fst p) , s (fst p) (snd p))))

plus-ir : ℕ → ℕ → ℕ
plus-ir = λ a → λ b → reci a b (λ _ → λ r → suc r)

------------

-- Day 2 Exercise 2

show : ℕ → (⊤ + ℕ)
show zero    = inl tt
show (suc n) = inr n

hide : (⊤ + ℕ) → ℕ
hide (inl tt) = zero
hide (inr n)  = suc n

showhide : (n : ℕ) → hide (show n) ≡ n
showhide zero    = refl
showhide (suc n) = refl

hideshow : (n : ⊤ + ℕ) → show (hide n) ≡ n 
hideshow (inl tt) = refl
hideshow (inr n)  = refl

-- bonus

lshow : List → ⊤ + (ℕ × List)
lshow []       = inl tt
lshow (n ∷ ns) = inr (n , ns)

lhide : ⊤ + (ℕ × List) → List
lhide (inl tt)       = []
lhide (inr (n , ns)) = n ∷ ns

lshowhide : (ns : List) → lhide (lshow ns) ≡ ns
lshowhide []       = refl
lshowhide (n ∷ ns) = refl

lhideshow : (ns : ⊤ + (ℕ × List)) → lshow (lhide ns) ≡ ns
lhideshow (inl tt)       = refl
lhideshow (inr (n , ns)) = refl

