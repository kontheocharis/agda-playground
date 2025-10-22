{-# OPTIONS --large-indices #-}

data Foo : (a : Set) -> (b : a -> Set) -> (c : (x : a) -> b x -> Set) -> Set where
  Bar : ∀ {a b c} → (x : a) → (y : b x) → (z : {!   !} x y) → Foo a b c