{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  X Y Z       : Set ℓ
  P Q         : X → Set ℓ
  x y z       : X
  f g h       : (x : X) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List X

cong : (f : X → Y) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : (P : X → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

{-# BUILTIN REWRITE _≐_ #-}
{-# BUILTIN REWRITE _≡_ #-}

postulate
  transportR : (P : X → Set ℓ) → x ≐ y → P x → P y
  transportR-refl : transportR P refl x ≡ x
{-# REWRITE transportR-refl #-}

variable
  R : X → X → Prop

postulate
  _//_    : (X : Set ℓ) (R : X → X → Prop) → Set ℓ
  proj    : X → X // R
  quot    : R x y → proj {R = R} x ≐ proj {R = R} y

  //-rec : {P : Set ℓ}
    → (proj* : X → P)
    → (quot* : {x y : X} (r : R x y) → proj* x ≐ proj* y)
    → X // R → P
  //-comp : {P : Set ℓ}
    → (proj* : X → P)
    → (quot* : {x y : X} (r : R x y) → proj* x ≐ proj* y)
    → {u : X} → //-rec proj* quot* (proj u) ≐ proj* u

  //-elim : (P : X // R → Set ℓ)
    → (proj* : (x : X) → P (proj x))
    → (quot* : {x y : X} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → (x : X // R) → P x
  //-beta : {R : X → X → Prop} (P : X // R → Set ℓ)
    → (proj* : (x : X) → P (proj x))
    → (quot* : {x y : X} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → {u : X} → //-elim P proj* quot* (proj u) ≐ proj* u
{-# REWRITE //-comp #-}
{-# REWRITE //-beta #-}

-- CWF
data Con : Set

data Ty : Set

data Var : Con → Ty → Set

data Tm' : Con → Ty → Set
data Tm~ : ∀ {Γ A} -> Tm' Γ A → Tm' Γ A → Prop

Tm : Con → Ty → Set
Tm Γ A = Tm' Γ A // Tm~

data Sub' : Con → Con → Set
data Sub~ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' Γ Δ → Prop

Sub : Con → Con → Set
Sub Γ Δ = Sub' Γ Δ // Sub~

variable
  Γ Δ Θ : Con
  A B C : Ty
  t' u' v' t₀' t₁'  : Tm _ _
  t u v t₀ t₁  : Tm' _ _

  σ σ₀ σ₁ σ₂ δ δ₀ δ₁ δ₂ ν ν₁ ν₂ : Sub' _ _

infixl 4 _,_
infixr 5 _∘_
infixl 4 _,'_
infixr 5 _∘'_
infix 5 _[_]
infix 5 _[_]'

data Con where
  ∙   : Con
  _,_ : Con → Ty → Con

data Ty where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Var where
  vz : Var (Γ , A) A
  vs : Var Γ A → Var (Γ , B) A

data Sub' where
  id' : Sub' Γ Γ
  ε'   : Sub' Γ ∙
  _∘'_ : Sub' Γ Δ → Sub' Θ Γ → Sub' Θ Δ
  p' : Sub' (Γ , A) Γ
  _,'_ : Sub' Γ Δ → Tm' Γ A → Sub' Γ (Δ , A)

data Tm' where
  _[_]' : Tm' Δ A → Sub' Γ Δ → Tm' Γ A
  q' : Tm' (Γ , A) A
  lam'  : Tm' (Γ , A) B → Tm' Γ (A ⇒ B)
  app'  : Tm' Γ (A ⇒ B) → Tm' (Γ , A) B

data Tm~ where
  rfl  : Tm~ t t
  sym  : Tm~ t u → Tm~ u t
  trs  : Tm~ t u → Tm~ u v → Tm~ t v

  lam~  : Tm~ t₀ t₁ → Tm~ (lam' t₀) (lam' t₁)
  app~  : Tm~ t₀ t₁ → Tm~ (app' t₀) (app' t₁)
  _[_]~ : Tm~ t₀ t₁ → Sub~ σ₀ σ₁ → Tm~ (t₀ [ σ₀ ]') (t₁ [ σ₁ ]')

  β'    : Tm~ (app' (lam' t)) t
  η'    : Tm~ (lam' (app' t)) t

  q[]'   : Tm~ (q' [ σ ,' t ]') t
  lam[]' : Tm~ (lam' t [ σ ]') (lam' (t [ σ ∘' p' ,' q' ]'))

data Sub~ where
  rfl  : Sub~ σ σ
  sym  : Sub~ σ δ → Sub~ δ σ
  trs  : Sub~ σ δ → Sub~ δ ν → Sub~ σ ν

  _∘~_ : Sub~ σ₀ σ₁ → Sub~ δ₀ δ₁ → Sub~ (σ₀ ∘' δ₀) (σ₁ ∘' δ₁)
  _,~_ : (σ₂ : Sub~ σ₀ σ₁) → Tm~ t₀ t₁ → Sub~ (σ₀ ,' t₀) (σ₁ ,' t₁)

  ------------------------------------------------------------
  εη'  : Sub~ σ ε'
  idl' : Sub~ (id' ∘' σ) σ
  idr' : Sub~ (σ ∘' id') σ
  ass' : Sub~ (σ ∘' δ ∘' ν) ((σ ∘' δ) ∘' ν)
  p∘'  : Sub~ (p' ∘' (σ ,' t)) σ
  pq'  : Sub~ (p' ,' q') (id' {Γ , A})
  ,∘'  : Sub~ ((σ ,' t) ∘' δ) (σ ∘' δ ,' t [ δ ]')



-- var : Var Γ A → Tm Γ A
-- var v = proj (var' v)

coe : ∀ {A B : Prop ℓ} → A ≡ B → A → B
coe refl x = x

lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
lam t = //-rec (λ t' → proj (lam' t')) (λ tr → quot (lam~ tr)) t

app : Tm Γ (A ⇒ B) → Tm (Γ , A) B
app t = //-rec (λ t' → proj (app' t')) (λ tr → quot (app~ tr)) t

_[_] : Tm Δ A → Sub Γ Δ → Tm Γ A
t [ σ ] = //-rec
  (λ t' → //-rec (λ σ' → proj (t' [ σ' ]'))
    (λ σr → quot (rfl [ σr ]~)) σ)
  (λ tr → {!   !})
  t

q : Tm (Γ , A) A
q = proj q'

id : Sub Γ Γ
id = proj id'

ε : Sub Γ ∙
ε = proj ε'

_∘_ : Sub Γ Δ → Sub Θ Γ → Sub Θ Δ
σ ∘ σ' = {!   !}

p : Sub (Γ , A) Γ
p = proj p'

_,,_ : Sub Γ Δ → Tm Γ A → Sub Γ (Δ , A)
_,,_ = {!   !}


-- Equations

β : ∀ {t : Tm' (Γ , A) B} → proj {R = Tm~} (app' (lam' t)) ≐ proj t
β = quot β'

η : ∀ {t : Tm' Γ (A ⇒ B)} → proj {R = Tm~} (lam' (app' t)) ≐ proj t
η = quot η'

q[] : proj {R = Tm~} (q' [ σ ,' t ]') ≐ proj t
q[] = quot q[]'

lam[] : proj {R = Tm~} (lam' t [ σ ]') ≐ proj (lam' (t [ σ ∘' p' ,' q' ]'))
lam[] = quot lam[]'

εη  : proj {R = Sub~} σ ≐ proj ε'
εη = quot εη'

idl : proj {R = Sub~} (id' ∘' σ) ≐ proj σ
idl = quot idl'

idr : proj {R = Sub~} (σ ∘' id') ≐ proj σ
idr = quot idr'

ass : proj {R = Sub~} (σ ∘' δ ∘' ν) ≐ proj ((σ ∘' δ) ∘' ν)
ass = quot ass'

p∘  : proj {R = Sub~} (p' ∘' (σ ,' t)) ≐ proj σ
p∘ = quot p∘'

pq  : proj {R = Sub~} (p' ,' q') ≐ proj (id' {Γ , A})
pq = quot pq'

,∘  : proj {R = Sub~} ((σ ,' t) ∘' δ) ≐ proj (σ ∘' δ ,' t [ δ ]')
,∘ = quot ,∘'

{-# REWRITE β η q[] lam[] εη idl idr ass p∘ pq ,∘ #-}


infixr 10 _⊢_
infix 10 _⊢_≣_

_⊢_ : (Γ : Con) → Tm Γ A → Set
Γ ⊢ t = ⊤

_⊢_≣_ : (Γ : Con) → Tm Γ A → Tm Γ A → Prop
Γ ⊢ t ≣ u = t ≐ u


-- Properties:

β-is-definitional : (∙ , ι) ⊢ app (lam q) ≣ q
β-is-definitional = refl

-- zero : ∙ ⊢ lam (lam (lam ((var (vs (vs vz))) (var (vs vz)))))

-- Quotients

-- Ty' : (Γ : Con') → Set
-- Ty' Γ = Ty (proj Γ) // Ty~


