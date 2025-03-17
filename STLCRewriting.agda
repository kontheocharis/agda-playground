{-# OPTIONS --rewriting --prop --backtracking-instance-search #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.String

-- Problem:
--
-- HOAS (i.e. shallow embedding) is nice to work with because we can re-use the
-- host's functions. However, it does not allow us to inspect the contextual
-- aspects of the syntax. In other words, we cannot inspect an open term so we
-- cannot compile HOAS to machine code for example.
--
-- On the other hand, deep embedding with explicit contexts allows us to inspect
-- the syntax freely, but its equations (substitution calculus) do not hold
-- definitionally, even though they are decidable!.
--
-- This is an attempt to have the best of both words:
--
-- We deeply embed a (simple) type theory in Agda using explicit substitutions, so
-- that our entire syntax is intrinsically well typed and fully inductively
-- defined. We then define equivalence relations on the syntax (inductively),
-- corresponding to the definitional equality rules of the language. Finally, we
-- pick a careful subset of these equations and register them as REWRITING
-- equations. This way, Agda will automatically apply these equations to any goal,
-- effectively deciding the theory we formulated.
--
-- We need not quotient the syntax either; Agda allows us to register any relation
-- as a rewriting relation. This way, we can still compile the syntax as we
-- please, without needing to preserve the setoid structure.
--
-- To deal with de-Brujin indices, we store names in contexts, and use Agda's
-- instance resolution to search for de-Brujin terms that satisfy the given name.
--
-- Overall this works quite well, with the significant disadvantage that rewriting
-- in Agda is quite slow..

variable
  X Y Z       : Set
  P Q         : X → Set
  x y z       : X
  f g h       : (x : X) → P x
  s s' s''     : String

-- This should be readily extensible to dependent types as it is presented using a CWF style.
-- See https://dl.acm.org/doi/10.1145/2837614.2837638 (though we do not use quotients).
-- Also see https://gist.github.com/AndrasKovacs/4fcafec4c97fc1af75210f65c20e624d for a very similar example.

data Con : Set
data Ty : Set

-- Terms and substitutions are setoids

data Tm : Con → Ty → Set
data Tm~ : ∀ {Γ A} -> Tm Γ A → Tm Γ A → Prop

data Sub : Con → Con → Set
data Sub~ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Prop

variable
  Γ Δ Θ : Con
  A B C : Ty
  t u v t₀ t₁  : Tm _ _
  σ σ₀ σ₁ σ₂ δ δ₀ δ₁ δ₂ ν ν₁ ν₂ : Sub _ _

infixr 7 _⇒_
infixl 3 _,_∶_
infixl 3 _,_
infixr 5 _∘_
infix 5 _[_]

data Con where
  ∙   : Con
  -- Remember the names of variables in the context
  _,_∶_ : Con → String → Ty → Con

data Ty where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Sub where
  id : Sub Γ Γ
  ε   : Sub Γ ∙
  _∘_ : Sub Γ Δ → Sub Θ Γ → Sub Θ Δ
  p : Sub (Γ , s ∶ A) Γ
  _,_ : Sub Γ Δ → Tm Γ A → Sub Γ (Δ , s ∶ A)

data Tm where
  _[_] : Tm Δ A → Sub Γ Δ → Tm Γ A
  q : Tm (Γ , s ∶ A) A
  lam  : (s : String) → Tm (Γ , s ∶ A) B → Tm Γ (A ⇒ B)
  app  : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

data Tm~ where
  rfl  : Tm~ t t
  sym  : Tm~ t u → Tm~ u t
  trs  : Tm~ t u → Tm~ u v → Tm~ t v

  lam~  : Tm~ t₀ t₁ → Tm~ (lam s t₀) (lam s t₁)
  app~  : Tm~ t₀ t₁ → Tm~ t u → Tm~ (app t₀ t) (app t₁ u)
  _[_]~ : Tm~ t₀ t₁ → Sub~ σ₀ σ₁ → Tm~ (t₀ [ σ₀ ]) (t₁ [ σ₁ ])

  β    : Tm~ (app (lam s t) u) (t [ id , u ]) -- you can also add η

  [][] : Tm~ ((t [ σ ]) [ δ ]) (t [ σ ∘ δ ])
  [id] : Tm~ (t [ id ]) t

  q[]   : Tm~ ((q {s = s}) [ σ , t ]) t
  lam[] : Tm~ ((lam s t) [ σ ]) (lam s (t [ σ ∘ p , q ]))
  app[] : Tm~ (app t u [ σ ]) (app (t [ σ ]) (u [ σ ]))

data Sub~ where
  rfl  : Sub~ σ σ
  sym  : Sub~ σ δ → Sub~ δ σ
  trs  : Sub~ σ δ → Sub~ δ ν → Sub~ σ ν

  _∘~_ : Sub~ σ₀ σ₁ → Sub~ δ₀ δ₁ → Sub~ (σ₀ ∘ δ₀) (σ₁ ∘ δ₁)
  _,~_ : (σ₂ : Sub~ σ₀ σ₁) → Tm~ t₀ t₁ → Sub~ (_,_ {s = s} σ₀ t₀) (σ₁ , t₁)

  εη  : Sub~ σ ε
  idl : Sub~ (id ∘ σ) σ
  idr : Sub~ (σ ∘ id) σ
  ass : Sub~ ((σ ∘ δ) ∘ ν) (σ ∘ δ ∘ ν)
  p∘  : Sub~ (p {s = s} ∘ (σ , t)) σ
  pq  : Sub~ (p , q) (id {Γ , s ∶ A})
  ,∘  : Sub~ ((_,_ {s = s} σ t) ∘ δ) (σ ∘ δ , t [ δ ])
  idp  : Sub~ (p ∘ σ , q [ σ ]) σ

-- Register these equivalence relations as rewriting relations.
{-# BUILTIN REWRITE Tm~ #-}
{-# BUILTIN REWRITE Sub~ #-}

-- Have to de-declare all of these because of an Agda bug:
-- https://github.com/agda/agda/issues/7738

β' : Tm~ (app (lam s t) u) (t [ id , u ])
β' = β

app[]' : Tm~ (app t u [ σ ]) (app (t [ σ ]) (u [ σ ]))
app[]' = app[]

lam[]' : Tm~ ((lam s t) [ σ ]) (lam s (t [ σ ∘ p , q ]))
lam[]' = lam[]

[][]' : Tm~ ((t [ σ ]) [ δ ]) (t [ σ ∘ δ ])
[][]' = [][]

q[]' : Tm~ ((q {s = s}) [ σ , t ]) t
q[]' = q[]

[id]' : Tm~ (t [ id ]) t
[id]' = [id]

ass' : Sub~ ((σ ∘ δ) ∘ ν) (σ ∘ δ ∘ ν)
ass' = ass

,∘' :  Sub~ ((_,_ {s = s} σ t) ∘ δ) (σ ∘ δ , t [ δ ])
,∘' = ,∘

idl' : Sub~ (id ∘ σ) σ
idl' = idl

idr' : Sub~ (σ ∘ id) σ
idr' = idr

p∘' : Sub~ (p {s = s} ∘ (σ , t)) σ
p∘' = p∘

pq' : Sub~ (p , q) (id {Γ , s ∶ A})
pq' = pq

idp' : Sub~ (p ∘ σ , q [ σ ]) σ
idp' = idp

-- This rewriting system is presented in the paper:
-- https://link.springer.com/chapter/10.1007/bfb0097798

{-# REWRITE β' app[]' lam[]' [][]' q[]' [id]' ass' ,∘' idl' idr' p∘' pq' idp' #-}

-- Syntax to make things look nice

infixr 2 _⊢_
infix 2 _⊢_≣_

_⊢_ : (Γ : Con) → Ty → Set
Γ ⊢ T = Tm Γ T

_⊢_≣_ : (Γ : Con) → Tm Γ A → Tm Γ A → Prop
Γ ⊢ t ≣ u = Tm~ t u

infixl 5 _!_

_!_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
f ! x = app f x

-- Variables:
-- We reuse Agda's instance resolution so that we don't have to deal with de-Brujin indices.

data Var : Con → String → Ty → Set where
  instance
    vz : Var (Γ , s ∶ A) s A
    vs : {{Var Γ s' A}} → Var (Γ , s ∶ B) s' A

get : Var Γ s A → Tm Γ A
get vz = q
get (vs {{x}}) = (get x) [ p ]

var : (s : String) → {{v : Var Γ s A}} → Tm Γ A
var _ {{v}} = get v

-- Basic examples:

β-is-definitional : ∙ , "y" ∶ ι ⊢ app (lam "x" (var "x")) t ≣ t
β-is-definitional = rfl

stuff-reduces-properly : ∙ , "y" ∶ ι ⊢ lam "x" (lam "z" (var "x")) ! var "y" ! var "y" ≣ var "y"
stuff-reduces-properly = rfl

-- Deeply embedded model of natural numbers in STLC that computes definitionally:

ℕ : Ty
ℕ = ι ⇒ (ι ⇒ ι) ⇒ ι

`0` : Γ ⊢ ℕ
`0` = lam "z" (lam "s" (var "z"))

`+1` : Γ ⊢ ℕ ⇒ ℕ
`+1` = lam "n'" (lam "z" (lam "s" (var "s" ! (var "n'" ! var "z" ! var "s"))))

rec-ℕ : Γ ⊢ ι ⇒ (ι ⇒ ι) ⇒ ℕ ⇒ ι
rec-ℕ = lam "base" (lam "rec" (lam "subject" (var "subject" ! var "base" ! var "rec")))

rec-ℕ-0 : ∙ , "x" ∶ ι , "y" ∶ ι ⇒ ι ⊢ rec-ℕ ! var "x" ! var "y" ! `0` ≣ var "x"
rec-ℕ-0 = rfl

rec-ℕ-+1 : ∙ , "x" ∶ ι , "y" ∶ ι ⇒ ι , "n" ∶ ℕ
          ⊢ rec-ℕ ! var "x" ! var "y" ! (`+1` ! var "n")
            ≣ var "y" ! (rec-ℕ ! var "x" ! var "y" ! var "n")
rec-ℕ-+1 = rfl

