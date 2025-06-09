{-# OPTIONS --rewriting #-}
module QTT where

open import Agda.Builtin.Equality
  
data Mode : Set where
  m0 : Mode
  m1 : Mode

record Semiring (R : Set) : Set where
  field
    `0` : R
    `1` : R
    _+_ : R → R → R
    _*_ : Mode → R → R
    _**_ : Mode → R → Mode
    ∣_∣ : Mode → R

module Syntax (R : Set) {{Semi-R : Semiring R}} where
  open Semiring Semi-R 
  

    
  data Con : Set
  data Con0 : Set

  data Sub : Con → Con → Set
  data Ty : Con0 → Set
    
  data Con0 where
    • : Con0
    0× : Con → Con0
    _,_ : (Γ : Con0) → Ty Γ → Con0

  data Tm : (m : Mode) → (Γ : Con) → Ty (0× Γ) → Set

  data Con0~ : Con0 → Con0 → Set
  data Con~ : Con → Con → Set
  data Ty~ : ∀ {Γ Γ'} → Con0~ Γ Γ' → Ty Γ → Ty Γ' → Set
    
  variable
    Γ Δ Γ' Γ'' : Con
    Γ0 Δ0 : Con0
    ρ : R
    A : Ty Γ0
    m : Mode

  data Con where
    • : Con
    ↑ : Con0 → Con
    _,[_]_ : (Γ : Con) → (ρ : R) → Ty (0× Γ) → Con
    _×_ : R → Con → Con
    _⊎_by_ : (Γ : Con) → (Γ' : Con) → Con0~ (0× Γ) (0× Γ') → Con
    
  data Ty where
    coe : ∀ {Γ0 Γ0'} → (Γ~ : Con0~ Γ0 Γ0') → Ty Γ0 → Ty Γ0'
    _[_] : (A : Ty Δ0) → Sub (↑ Γ0) (↑ Δ0) → Ty Γ0
    U : Ty Γ0
    El : Tm m0 (↑ Γ0) U → Ty Γ0
    Π : (ρ : R) → (A : Ty Γ0) → Ty (Γ0 , A) → Ty Γ0

  data Con0~ where
    rfl : ∀ {Γ} → Con0~ Γ Γ
    sym : ∀ {Γ Γ'} → Con0~ Γ Γ' → Con0~ Γ' Γ
    trs : ∀ {Γ Γ' Γ''} → Con0~ Γ Γ' → Con0~ Γ' Γ'' → Con0~ Γ Γ''

    • : Con0~ • •
    0× : ∀ {Γ Γ'} → Con~ Γ Γ' → Con0~ (0× Γ) (0× Γ')
    _,_ : ∀ {Γ Γ'}
      → (Γ~ : Con0~ Γ Γ')
      → ∀ {A A'}
      → Ty~ Γ~ A A'
      → Con0~ (Γ , A) (Γ' , A')

    0×× : ∀ {Γ Γ'} → Con~ Γ Γ' → Con0~ (0× (ρ × Γ)) (0× Γ')
    0×• : Con0~ (0× •) •
    _0×,_ : ∀ {Γ Γ'}
      → (Γ~ : Con0~ (0× Γ) Γ')
      → ∀ {A A'} → Ty~ Γ~ A A'
      → Con0~ (0× (Γ ,[ ρ ] A)) (Γ' , A')

    0×↑ : ∀ {Γ0} → Con0~ (0× (↑ Γ0)) Γ0

  data Con~ where
    rfl : ∀ {Γ} → Con~ Γ Γ
    sym : ∀ {Γ Γ'} → Con~ Γ Γ' → Con~ Γ' Γ
    trs : ∀ {Γ Γ' Γ''} → Con~ Γ Γ' → Con~ Γ' Γ'' → Con~ Γ Γ''

    • : Con~ • •
    ↑ : ∀ {Γ Γ'} → Con0~ Γ Γ' → Con~ (↑ Γ) (↑ Γ')
    _,[_]_ : ∀ {Γ Γ' ρ ρ' A A'}
      → (Γ~ : Con~ Γ Γ')
      → Ty~ (0× Γ~) A A'
      → Con~ (Γ ,[ ρ + ρ' ] A) (Γ' ,[ ρ + ρ' ] A')

    ↑• : Con~ (↑ •) •
    _↑,_ : ∀ {Γ Γ'}
      → (Γ~ : Con~ (↑ Γ) Γ')
      → ∀ {A A'} → Ty~ (0× Γ~) A A'
      → Con~ (↑ (Γ , coe 0×↑ A)) (Γ' ,[ `0` ] A')

  data Sub where
    coe : ∀ {Γ Γ' Δ Δ'}
      → (Γ~ : Con~ Γ Γ')
      → (Δ~ : Con~ Δ Δ')
      → Sub Γ Δ
      → Sub Γ' Δ'

    id : Sub Γ Γ
    ε : Sub (↑ (0× Γ)) •
    p0 : Sub (Γ ,[ `0` ] A) Γ
    
    -- Action of the U functor
    ↑0× : Sub Γ Δ → Sub (↑ (0× Γ)) (↑ (0× Δ))

    ext : (σ : Sub Γ Δ)
      → (ρ : R)
      → (0×Γ~ : Con0~ (0× Γ) (0× Γ'))
      → Tm m1 Γ' (A [ coe (↑ 0×Γ~) rfl (↑0× σ) ])
      → Sub (Γ ⊎ Γ' by 0×Γ~) (Δ ,[ m1 * ρ ] A)

    _∘_ : ∀ {E} → Sub Γ Δ → Sub E Γ → Sub E Δ
    
  data Ty~ where
    rfl : ∀ {Γ} {A : Ty Γ} → Ty~ rfl A A

  data Tm where
    _[_] : ∀ {m Γ Δ A} → Tm m Δ A → (σ : Sub Γ Δ) → Tm m Γ (A [ ↑0× σ ])
    q : Tm m (↑ (0× Γ) ,[ `0` ] A) (A [ ↑0× p0 ])
    
    -- Action of the U functor
    ↑0× : ∀ {m Γ A} → Tm m Γ A → Tm m0 (↑ (0× Γ)) (coe (sym 0×↑) A)
    
    lam : ∀ {m B} → Tm m (Γ ,[ m * ρ ] A) B → Tm m Γ (Π ρ A (coe (rfl 0×, rfl) B))
    app : ∀ {m B} → Tm m Γ (Π ρ A B) → Tm m (Γ ,[ ρ ] A) (coe (sym (rfl 0×, rfl)) B)
      
  app' : ∀ {m ρ Γ Γ' A B} → Tm m Γ (Π ρ A B)
    → (0×Γ~ : Con0~ (0× Γ) (0× Γ'))
    → Tm (m ** ρ) Γ' (coe 0×Γ~ A)
    → Tm m (Γ ⊎ ρ × Γ' by trs 0×Γ~ (sym (0×× rfl))) (B [ {!  ext ? ? ? ? !} ])