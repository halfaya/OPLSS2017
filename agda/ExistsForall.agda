module ExistsForall where

open import Data.Product using (Σ; _,_; Σ-syntax)

∃→∀ : {P : Set → Set} {Q : Set} → (Σ[ b ∈ Set ] (P b) → Q) → ((b : Set) → P b → Q)
∃→∀ f b pb = f (b , pb)

∀→∃ : {P : Set → Set} {Q : Set} → ((b : Set) → P b → Q) → (Σ[ b ∈ Set ] (P b) → Q)
∀→∃ f (b , pb) = f b pb

--

∃'→∀' : {P : Set → Set} {Q : Set} → (Σ[ b ∈ Set ] (P b → Q)) → (((b : Set) → P b) → Q)
∃'→∀' (b , f) g = f (g b)

∀'→∃' : {P : Set → Set} {Q : Set} → (((b : Set) → P b) → Q) → (Σ[ b ∈ Set ] (P b → Q))
∀'→∃' {P} {Q} f = ( Q , λ x → f {!!} )

--

∀→∀' : {P : Set → Set} {Q : Set} → ((b : Set) → P b → Q) → (((b : Set) → P b) → Q)
∀→∀' f g = {!!}

∀'→∀ : {P : Set → Set} {Q : Set}  → (((b : Set) → P b) → Q) → ((b : Set) → P b → Q)
∀'→∀ {P} {Q} f b pb = {!!}

--

data ⊥ : Set where

uninhabited : ((P : Set → Set) → (b : Set) → P b) → ⊥
uninhabited f = f (λ _ → ⊥) ⊥
