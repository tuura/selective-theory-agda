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

data Pair (a b : Set) : Set where
  _×_ : a → b → Pair a b
------------------------------------------------------------------
record Functor (F : Set → Set) : Set₁ where
  infixl 4 _<$>_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

    -- Functor laws
    fmap-id      : ∀ {A} {x : F A} → fmap id x ≡ id x
    fmap-compose : ∀ {A B C} {f : A → B} {g : B → C} {x : F A} →
                   fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x  

  _<$>_ = fmap

open Functor {{...}} public

instance
  FunctorFunction : {X : Set} → Functor (λ Y → (X → Y))
  fmap {{FunctorFunction}} f g = λ x → f (g x)
  fmap-id {{FunctorFunction}} = refl
  fmap-compose {{FunctorFunction}} = refl 


record Applicative (F : Set → Set) : Set₁ where
  infixl 4 _<*>_ _<*_ _*>_
  field
    overlap {{super}} : Functor F
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B

    -- Applicative laws
    ap-identity     : ∀ {A B} {f : F (A → B)} → (pure id <*> f) ≡ f
    ap-homomorphism : ∀ {A B} {x : A} {f : A → B} →
                      (pure f <*> pure x) ≡ pure (f x)
    -- ap-interchange  : u <*> pure y = pure ($y) <*> u
    -- ap-composition  : (.) <$> u <*> v <*> w = u <*> (v <*> w)
    fmap-pure-ap : ∀ {A B} {x : F A} {f : A → B} →
                   (f <$> x) ≡ (pure f <*> x)
  
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

    -- -- (A1) Associativity
    -- a1 : ∀ {A B C} {x : F (Either A B)} {y : F (Either C (A → B))} {z : F (C → A → B)} →
    --      handle x (handle y z) ≡
    --      handle (handle ((λ x → right x) <$> x) (λ a → bimap (λ x → (x × a)) (_$ a) y))

-- A1: handle x (handle y z) = handle (handle (f <$> x) (g <$> y)) (h <$> z)
--       where f x = Right <$> x
--             g y = \a -> bimap (,a) ($a) y
--             h z = uncurry z
-- a1 :: Selective f => f (Either a b) -> f (Either c (a -> b)) -> f (c -> a -> b) -> f b
-- a1 x y z = handle x (handle y z) === handle (handle (f <$> x) (g <$> y)) (h <$> z)
--   where
--     f x = Right <$> x
--     g y = \a -> bimap (,a) ($a) y
--     h z = uncurry z

open Selective {{...}} public

-- | 'Selective' is more powerful than 'Applicative': we can recover the
-- application operator '<*>'. In particular, the following 'Applicative' laws
-- hold when expressed using 'apS':
--
-- * Identity     : pure id <*> v = v
-- * Homomorphism : pure f <*> pure x = pure (f x)
-- * Interchange  : u <*> pure y = pure ($y) <*> u
-- * Composition  : (.) <$> u <*> v <*> w = u <*> (v <*> w)
apS : ∀ {A B : Set} {F : Set → Set} {{_ : Selective F}} →
      F (A → B) → F A → F B
apS f x = handle (left <$> f) (flip (_$_) <$> x)
---------------------------------------------------------------------

