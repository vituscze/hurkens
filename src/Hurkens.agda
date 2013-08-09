{-# OPTIONS --type-in-type #-}
module Hurkens where

* = Set
□ = Set

⊥ = ∀ p → p

¬_ = λ A → A → ⊥

℘_  = λ A → A → *
℘℘_ = λ A → ℘ ℘ A

U = (X : □) → (℘℘ X → X) → ℘℘ X

τ : ℘℘ U → U
τ t = λ (X : □) (f : ℘℘ X → X) (p : ℘ X) → t λ (x : U) → p (f (x X f))

σ : U → ℘℘ U
σ s = s U λ (t : ℘℘ U) → τ t

τσ : U → U
τσ x = τ (σ x)

Δ : ℘ U
Δ = λ (y : U) → ¬ (∀ (p : ℘ U) → σ y p → p (τσ y))

Ω : U
Ω = τ λ (p : ℘ U) → ∀ (x : U) → σ x p → p x

too-bad₁ : ((p : ℘ U) → ((x : U) → σ x p → p x) → p Ω) → ⊥
too-bad₁ = λ (₀ : ∀ (p : ℘ U) → (∀ (x : U) → σ x p → p x) → p Ω) →
  (₀ Δ λ (x : U) (₂ : σ x Δ) (₃ : ∀ (p : ℘ U) → σ x p → p (τσ x)) →
  (₃ Δ ₂ λ (p : ℘ U) → (₃ λ (y : U) → p (τσ y)))) λ (p : ℘ U) →
  ₀ λ (y : U) → p (τσ y)

too-bad₂ : ⊥
too-bad₂ = too-bad₁ λ (p : ℘ U) (₁ : ∀ (x : U) → σ x p → p x) →
  ₁ Ω λ (x : U) → ₁ (τσ x)

-- The following ends up with stack overflow during type-checking.
{-
too-bad : ⊥
too-bad = (λ (₀ : ∀ (p : ℘ U) → (∀ (x : U) → σ x p → p x) → p Ω) →
  (₀ Δ λ (x : U) (₂ : σ x Δ) (₃ : ∀ (p : ℘ U) → σ x p → p (τσ x)) →
  (₃ Δ ₂ λ (p : ℘ U) → (₃ λ (y : U) → p (τσ y)))) λ (p : ℘ U) →
  ₀ λ (y : U) → p (τσ y)) λ (p : ℘ U) (₁ : ∀ (x : U) → σ x p → p x) →
  ₁ Ω λ (x : U) → ₁ (τσ x)
-}
