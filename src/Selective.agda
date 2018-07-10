module Selective where

open import Prelude.Equality

-----------------------------------------------------------------
id : ∀ {a} {A : Set a} → A → A
id x = x
{-# INLINE id #-}

infixl -10 id
syntax id {A = A} x = x ofType A

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x
{-# INLINE const #-}

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x
{-# INLINE flip #-}

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}

infixr -20 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

------------------------------------------------------------------
data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

either : ∀ {A : Set} {B : Set} {C : Set} →
           (A → C) → (B → C) → Either A B → C
either f g (left  x) = f x
either f g (right x) = g x
------------------------------------------------------------------
record Functor (F : Set → Set) : Set₁ where
  infixl 4 _<$>_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

open Functor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap {{super}} : Functor F

  _<*_ : ∀ {A B} → F A → F B → F A
  a <* b = ⦇ const a b ⦈

  _*>_ : ∀ {A B} → F A → F B → F B
  a *> b = ⦇ (const id) a b ⦈

open Applicative {{...}} public

record Bifunctor (P : Set → Set → Set)  : Set₁ where
  field
    bimap : ∀ {A B C D} → (A → B) → (C → D) → P A C → P B D
    
    first : ∀ {A B C} → (A -> B) -> P A C -> P B C
    
    second : ∀ {A B C} → (B -> C) -> P A B -> P A C

open Bifunctor {{...}} public

instance
  BifunctorEither : Bifunctor Either
  -- fmap {{FunctorMaybe}} f m = maybe nothing (just ∘ f) m
  bimap {{BifunctorEither}} f _ (left a)  = left (f a)
  bimap {{BifunctorEither}} _ g (right b) = right (g b)

  first {{BifunctorEither}} f = bimap f id
  
  second {{BifunctorEither}} = bimap id

record Selective (F : Set → Set) : Set₁ where
  field
    overlap {{super}} : Applicative F
    handle : ∀ {A B} → F (Either A B) → F (A → B) → F B

    -- Laws:
    -- (F1) Apply a pure function to the result:
    f1 : ∀ {A B C} {f : B → C} {x : F (Either A B)} {y : F (A → B)} →
         (f <$> (handle x y)) ≡ handle (second f <$> x) ((f ∘_) <$> y)

    -- (F2) Apply a pure function to the left (error) branch:
    f2 : ∀ {A B C} {f : A -> C} {x : F (Either A B)} {y : F (C → B)} →
         handle (first f <$> x) y ≡ handle x ((_∘ f) <$> y)

    -- (F3) Apply a pure function to the handler:
    f3 : ∀ {A B C} {f : C → A → B} {x : F (Either A B)} {y : F C} →
         (handle x (f <$> y)) ≡ handle (first (flip f) <$> x) (flip (_$_) <$> y)

    -- (P1) Apply a pure handler:
    p1 : ∀ {A B} {x : F (Either A B)} {y : A → B} →
         handle x (pure y) ≡ (either y id <$> x)

    -- (P2) Handle a pure error:
    p2 : ∀ {A B} {x : A} {y : F (A → B)} →
         handle (pure (left x)) y ≡ ((_$ x) <$> y)

    -- (A1) Associativity
    
    

open Selective {{...}} public
---------------------------------------------------------------------

--------------------------------------------------------------------
-- Selective laws

-- f1 : ∀ {A B C} {F : Set → Set} {{_ : Selective F}} → {f : B → C} → {x : F (Either A B)} → {y : F (A → B)} →
--      (f <$> (handle x y)) ≡ handle (second f <$> x) ((f ∘_) <$> y) 
-- f1 = {!!}
