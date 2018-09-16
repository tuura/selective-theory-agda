{-# OPTIONS --type-in-type #-}
module Selective.Theorems where

open import Prelude.Equality
open import Selective

-- Now let's typecheck some theorems


cong-handle : ∀ {A B}  {F : Set → Set} {{_ : Selective F}}
              {x y : F (Either A B)} {f : F (A → B)} →
              x ≡ y → handle x f ≡ handle y f
cong-handle refl = {!!}

cong-handle-handler : ∀ {A B}  {F : Set → Set} {{_ : Selective F}}
                      {x : F (Either A B)} {f g : F (A → B)} →
                      f ≡ g → handle x f ≡ handle x g
cong-handle-handler refl = {!!}

cong-ap-right : ∀ {A B} {F : Set → Set} {{_ : Applicative F}}
                {x y : F A} {f : F (A → B)} →
                x ≡ y → f <*> x ≡ f <*> y
cong-ap-right refl = refl

-- lemma : ∀ {A B} {F : Set → Set} {{_ : Applicative F}}
--         {x : F A} {f : A → B} →
--         pure (_$_) <*> pure f <*> x ≡ (pure f) <*> x
-- lemma = refl

-- Identity: pure id <*> v = v
t1 : ∀ {A : Set} {F : Set → Set} {{_ : Selective F}} →
     (v : F A) → (apS (pure id) v) ≡ v
t1 v = apS (pure id) v
         ≡⟨ refl ⟩                           -- Definition of 'apS'
       handle (left <$> pure id) (flip (_$_) <$> v)
         ≡⟨ cong-handle fmap-pure-ap ⟩
       handle (pure left <*> pure id) (flip (_$_) <$> v)
         ≡⟨  cong-handle ap-homomorphism ⟩   -- Push 'left' inside 'pure'
       handle (pure (left id)) (flip (_$_) <$> v)
         ≡⟨ p2 ⟩                             -- Apply P2
       (_$ id) <$> (flip (_$_) <$> v)
         ≡⟨ refl ⟩                      let f = (_$ id)
                                            g = flip (_$_) in
       f <$> (g <$> v)
         ≡⟨ fmap-pure-ap ⟩
       pure f <*> (g <$> v)
         ≡⟨ cong-ap-right fmap-pure-ap ⟩
       pure f <*> (pure g <*> v)
          ≡⟨ refl ⟩
       pure (_$ id) <*> (pure g <*> v)
          ≡⟨ {!?!} ⟩ -- ap-interchange
       (pure g <*> v) <*> pure id
          ≡⟨ refl ⟩
       pure (λ x f -> f x) <*> v <*> pure id
          ≡⟨ {!!} ⟩
       -- (f <$> g) <$> v
       --   ≡⟨ refl ⟩
       -- (f ∘ g) <$> v
       --   ≡⟨ refl ⟩
       -- ((_$ id) ∘ flip (_$_)) <$> v
       --   ≡⟨ refl ⟩                           -- Simplify
       pure id <*> v
         ≡⟨ fmap-pure-ap ⟩
       id <$> v
         ≡⟨ fmap-id ⟩                        -- Functor identity: fmap id = id
       v ∎

t1' : ∀ {A : Set} {F : Set → Set} {{_ : Selective F}} →
     (v : F A) → (apS (pure id) v) ≡ v
t1' v = apS (pure id) v
         ≡⟨ refl ⟩                           -- Definition of 'apS'
       handle (left <$> pure id) (flip (_$_) <$> v)
         ≡⟨ cong-handle fmap-pure-ap ⟩
       handle (pure left <*> pure id) (flip (_$_) <$> v)
         ≡⟨  cong-handle ap-homomorphism ⟩   -- Push 'left' inside 'pure'
       handle (pure (left id)) (flip (_$_) <$> v)
         ≡⟨ p2 ⟩                             -- Apply P2
       (_$ id) <$> (flip (_$_) <$> v)
         ≡⟨ refl ⟩
                                        let f = (_$ id)
                                            g = flip (_$_) in
       f <$> (g <$> v)
          ≡⟨ {!!} ⟩
       (f ∘ g) <$> v
         ≡⟨ refl ⟩
       ((_$ id) ∘ flip (_$_)) <$> v
         ≡⟨ refl ⟩                           -- Simplify
       id <$> v
         ≡⟨ fmap-id ⟩                        -- Functor identity: fmap id = id
       v ∎

-- Homomorphism: pure f <*> pure x = pure (f x)
t2 : ∀ {A B : Set} {F : Set → Set} {{_ : Selective F}}
     (f : A → B) (x : A) →
     (apS (pure {F} f) (pure x)) ≡ pure (f x)
t2 f x = apS (pure f) (pure x)
            ≡⟨ refl ⟩ -- Definition of 'apS'
         handle (left <$> pure f) (flip (_$_) <$> pure x)
           ≡⟨ cong-handle fmap-pure-ap ⟩  -- Push 'Left' inside 'pure'
         handle (pure left <*> pure f) (flip (_$_) <$> pure x)
           ≡⟨ cong-handle ap-homomorphism ⟩
         handle (pure (left f)) (flip (_$_) <$> pure x)
           ≡⟨ p2 ⟩    -- Apply P2
         (_$ f) <$> (flip (_$_) <$> pure x)
           ≡⟨ {!?!} ⟩ -- Simplify
         f <$> pure x
           ≡⟨ fmap-pure-ap ⟩
         pure f <*> pure x
           ≡⟨ ap-homomorphism ⟩
         pure (f x) ∎

-- Interchange: u <*> pure y = pure ($y) <*> u
t3 : ∀ {A B : Set} {F : Set → Set} {{_ : Selective F}}
     (f : F (A → B)) (x : A) →
      apS f (pure x) ≡ apS (pure (_$ x)) f
t3 f x = {!!}

    -- === -- Express right-hand side of the theorem using 'apS'
    -- apS (pure ($y)) u
    -- === -- Definition of 'apS'
    -- handle (Left <$> pure ($y)) (flip ($) <$> u)
    -- === -- Push 'Left' inside 'pure'
    -- handle (pure (Left ($y))) (flip ($) <$> u)
    -- === -- Apply P2
    -- ($($y)) <$> (flip ($) <$> u)
    -- === -- Simplify, obtaining (#)
    -- ($y) <$> u


either-left-lemma : ∀ {A B C : Set} {x : A} {f : A → C} {g : B → C} →
  either f g (left x) ≡ f x
either-left-lemma = refl

either-left-lemma1 : ∀ {A B C : Set}
   {F : Set → Set} {{_ : Functor F}} →
   {x : F A} {f : A → C} {g : B → C} →
  (either f g <$> (fmap {F = F} left x)) ≡ (f <$> x)
either-left-lemma1 = {!!}

t3-lhs-lemma : ∀ {A B : Set} {F : Set → Set} {{_ : Selective F}}
               (f : F (A → B)) (x : A) →
               apS f (pure x) ≡ ((_$ x) <$> f)
t3-lhs-lemma {A} {B} f x =
  apS f (pure x)
    ≡⟨ refl ⟩ -- Definition of 'apS'
  handle (left <$> f) (flip (_$_) <$> pure x)
    ≡⟨ cong-handle-handler fmap-pure-ap ⟩ -- Rewrite to have a pure handler
  handle (left <$> f) (pure (flip (_$_)) <*> pure x)
    ≡⟨ cong-handle-handler ap-homomorphism ⟩
  handle (left <$> f) (pure (flip (_$_) x))
    ≡⟨ cong-handle-handler refl ⟩
  handle (left <$> f) (pure (_$ x))
    ≡⟨ p1 ⟩   -- Apply P1
  either (_$ x) id <$> (left <$> f)
    ≡⟨ {!!} ⟩
  (_$ x) <$> f ∎
    -- -- Express the lefthand side using 'apS'
    -- apS u (pure y)
    -- === -- Definition of 'apS'
    -- handle (Left <$> u) (flip ($) <$> pure y)
    -- === -- Rewrite to have a pure handler
    -- handle (Left <$> u) (pure ($y))
    -- === -- Apply P1
    -- either ($y) id <$> (Left <$> u)
    -- === -- Simplify, obtaining (#)
    -- ($y) <$> u
