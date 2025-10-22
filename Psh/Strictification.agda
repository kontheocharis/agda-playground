{-# OPTIONS --type-in-type #-}
module Strictification where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id  : ∀ {x} → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z

    id∘ : ∀ {x y} {f : Hom x y} → id ∘ f ≡ f
    ∘id : ∀ {x y} {f : Hom x y} → f ∘ id ≡ f
    assoc : ∀ {x y z D} {f : Hom z D} {g : Hom y z} {h : Hom x y} → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    
open Cat

∣_∣ : Cat → Set
∣ C ∣ = C .Obj

_[_,_] : ∀ (C : Cat) (A B : ∣ C ∣) → Set
C [ x , y ] = C .Hom x y

Psh : Cat → Cat
Psh C .Obj = ∣ C ∣ → Set
Psh C .Hom x y = ∀ z → x z → y z
Psh C .id = λ _ f → f
Psh C ._∘_ = λ z z₁ z₂ z₃ → z z₂ (z₁ z₂ z₃)
Psh C .id∘ = refl
Psh C .∘id = refl
Psh C .assoc = refl

module _ (C : Cat) where
  variable
    x y z : ∣ C ∣
    f g h : C [ _ , _ ]

  𝐲 : ∣ C ∣ → ∣ Psh C ∣
  𝐲 x y = C [ y , x ]

  𝐲' : C [ x , y ] → (Psh C) [ 𝐲 x , 𝐲 y ]
  𝐲' f z x = (C ∘ f) x
  
  y'-inv : (Psh C) [ 𝐲 x , 𝐲 y ] → C [ x , y ]
  y'-inv f = f _ (C .id)
  

-- open Cat

-- module _ (C : Cat) where
--   open Cat C

--   -- yoneda 