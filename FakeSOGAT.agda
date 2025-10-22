module FakeSOGAT where

open import Relation.Binary.PropositionalEquality

infixr 3 _⇒_
_⇒_ : ∀ {I : Set} → (A : I → Set) → (I → Set) → (I → Set)
(A ⇒ B) j = A j → B j

∀[_] : ∀ {I : Set} → (I → Set) → Set
∀[_] {I} P = {Γ : I} → P Γ

data Con : Set
data Ty : Con → Set
data Tm : Con → Set
typeof : ∀[ Tm ⇒ Ty ]

data Con where
  • : Con
  _,_ : (Γ : Con) → Ty Γ → Con

infixr 3 [Tm⇒_]⇒_
[Tm⇒_]⇒_ : (Con → Set) → (Con → Set) → (Con → Set)
([Tm⇒ B ]⇒ C) Γ = (A : Ty Γ) → B (Γ , A) → C Γ

Tm'_⇒_ : (∀ {Γ} → Ty Γ) → (Con → Set) → Con → Set
(Tm' A ⇒ B) Γ = (t : Tm Γ) → typeof t ≡ A {Γ} → B Γ

data Ty where
  U : ∀[ Ty ]
  El : ∀[ Tm' U ⇒ Ty ]
  Π : ∀[ [Tm⇒ Ty ]⇒ Ty ]

data Tm where
  lam : ∀[ [Tm⇒ Tm ]⇒ Tm ]

typeof (lam A f) = Π A (typeof f)
