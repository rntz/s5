open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Sum
open import Data.Bool hiding (_∧_)

data Mode : Set where
  necc : Mode
  true : Mode
  poss : Mode

_≤_ : Mode -> Mode -> Set
poss ≤ _ = ⊤
_ ≤ necc = ⊤
true ≤ true = ⊤
_ ≤ _ = ⊥

infixr 3 _:⊃_
infixr 4 _:x_
data Type : Set where
  □ : Type -> Type
  ◇ : Type -> Type
  _:⊃_ : Type -> Type -> Type
  _:x_ : Type -> Type -> Type

Cx : Set₁
Cx = Mode -> Type -> Set

∅ : Cx
∅ m a = ⊥

infix 5 _#_
data _#_ (A : Type) (m : Mode) : Cx where
  eq : (A # m) m A

infixr 4 _∪_
_∪_ : Cx -> Cx -> Cx
(X ∪ Y) m a = X m a ⊎ Y m a

-- wipe captures the context manipulation in the premise of the rule:
--
--   Ψ;·;Γ,Φ ⊢ A true
--   -----------------
--   Ψ;Γ;Ψ ⊢ A valid
--
data wipe (X : Cx) : Cx where
  -- could use better names here
  wipe-necc : ∀{A} -> X necc A -> wipe X necc A
  wipe-true : ∀{A} -> X true A -> wipe X poss A
  wipe-poss : ∀{A} -> X poss A -> wipe X poss A

-- choose captures the context manipulation in the premise of the rule:
--
--    Ψ;A;· ⊢ C poss
--   ---------------- select
--   Ψ;Γ;Φ,A ⊢ C poss
--
data choose (X : Cx) {A} (v : X poss A) : Cx where
  -- could use better names here
  choose-necc : ∀{B} -> X necc B -> choose X v necc B
  choose-true : choose X v true A

infix 1 _⊢_is_
data _⊢_is_ (X : Cx) : Type -> Mode -> Set where
  -- hyp : ∀{A} (m : Mode) -> X m A
  hyp : ∀{A} (m : Mode) -> true ≤ m -> X m A -> X ⊢ A is true
  select : ∀{A C} (v : X poss A) -> choose X v ⊢ C is poss -> X ⊢ C is poss
  necc : ∀{A} -> wipe X ⊢ A is true -> X ⊢ A is necc
  poss : ∀{A} -> X ⊢ A is true -> X ⊢ A is poss
  □I : ∀{A} -> X ⊢ A is necc -> X ⊢ □ A is true
  □E : ∀{A B} -> X ⊢ □ A is true -> (A # necc) ∪ X ⊢ B is true
     -> X ⊢ B is true
  ◇I : ∀{A} -> X ⊢ A is poss -> X ⊢ ◇ A is true
  ◇E : ∀{A C} -> X ⊢ ◇ A is true -> (A # poss) ∪ X ⊢ C is true -> X ⊢ C is true
  ⊃I : ∀{A B} -> (A # true) ∪ X ⊢ B is true -> X ⊢ A :⊃ B is true
  ⊃E : ∀{A B} -> X ⊢ A :⊃ B is true -> X ⊢ A is true -> X ⊢ B is true


foo : ∀{A} -> ∅ ⊢ A :⊃ □ (◇ A) is true
foo = ⊃I (□I (necc (◇I (select (wipe-true (inj₁ eq)) (poss (hyp true tt choose-true))))))
