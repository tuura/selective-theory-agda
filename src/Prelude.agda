module Prelude where

-- Booleans
data Bool : Set where
  tt : Bool
  ff : Bool

_||_ : Bool -> Bool -> Bool
tt || y = tt
ff || y = y

_&&_ : Bool -> Bool -> Bool
tt && y = y
ff && y = ff

if_then_else : {A : Set} -> Bool -> A -> A -> A
if tt then x else _ = x
if ff then _ else y = y

-- Eq "type class"
record Eq (A : Set) : Set where
  field
    _==_   : A -> A ->  Bool

open Eq {{...}} public

-- Function composition
_∘_ : ∀ {x y z : Set} -> (y -> z) -> (x -> y) -> (x -> z)
(f ∘ g) x = f (g x)

-- Product type
data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

uncurry : ∀ {x y z : Set} -> (x -> y -> z) -> (x × y) -> z
uncurry f (a , b) = f a b

-- Lists
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 20 _::_
infixr 15 _++_

[_] : ∀ {A} -> A -> List A
[ x ] = x :: []

_++_ : ∀ {A} -> List A -> List A -> List A
[] ++ l = l
(x :: xs) ++ l = x :: (xs ++ l)

foldr : ∀ {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f b [] = b
foldr f b (x :: xs) = f x (foldr f b xs)

map : ∀ {A B} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

zip : ∀ {A B} -> List A -> List B -> List (A × B)
zip [] _                = []
zip _  []               = []
zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

-- Bottom type
-- data ⊥ : Set where

-- ¬ : Set -> Set
-- ¬ A = A -> ⊥

-- Decidable propositions and relations:
-- Rel : Set -> Set₁
-- Rel a = a -> a -> Set

-- data Dec (P : Set) : Set where
--   yes : (p : P) → Dec P
--   no : (¬p : ¬ P) → Dec P

-- Decidable : {a : Set} → Rel a → Set
-- Decidable _∼_ = forall x y → Dec (x ∼ y)

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ
