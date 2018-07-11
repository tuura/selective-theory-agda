{-# OPTIONS --type-in-type #-}
module Selective.Theorems where

open import Prelude.Equality
open import Selective

-- Now let's typecheck some theorems


cong-handle : ∀ {A B}  {F : Set → Set} {{_ : Selective F}}
              {x y : F (Either A B)} {f : F (A → B)} →
              x ≡ y → handle x f ≡ handle y f  
cong-handle = {!!}

t1 : ∀ {A : Set} {F : Set → Set} {{_ : Selective F}} →
     (v : F A) → (apS (pure id) v) ≡ v
t1 v = apS (pure id) v
         ≡⟨ refl ⟩   -- Definition of 'apS'
       handle (left <$> pure id) (flip (_$_) <$> v)
         ≡⟨ cong-handle fmap-pure-ap ⟩
       handle (pure left <*> pure id) (flip (_$_) <$> v)
         ≡⟨  cong-handle ap-homomorphism ⟩   -- Push 'left' inside 'pure'
       handle (pure (left id)) (flip (_$_) <$> v)
         ≡⟨ p2 ⟩      -- Apply P2
       (_$ id) <$> (flip (_$_) <$> v)
         ≡⟨ {!!} ⟩
       ((_$ id) <$> (flip (_$_)) <$> v)
         ≡⟨ {!?!} ⟩  
       ((_$ id) ∘ (flip (_$_))) <$> v
         ≡⟨ refl ⟩    -- Simplify
       id <$> v
         ≡⟨ fmap-id ⟩ -- Functor identity: fmap id = id
       v ∎



  -- begin
  --   (x + x) + ε             ≡⟨ L (L (symmetry *right-identity)) ⟩
  --   (x * ε + x) + ε         ≡⟨ L (R (symmetry *right-identity)) ⟩
  --   (x * ε + x * ε) + ε     ≡⟨ R (symmetry *right-identity)     ⟩
  --   (x * ε + x * ε) + ε * ε ≡⟨ symmetry decomposition           ⟩
  --   (x * ε) * ε             ≡⟨ *right-identity                  ⟩
  --   x * ε                   ≡⟨ *right-identity                  ⟩
  --   x
  -- ∎

-- -- Identity: pure id <*> v = v
-- t1 :: Selective f => f a -> f a
-- t1 v =
--     -- Express the lefthand side using 'apS'
--     apS (pure id) v
--     === -- Definition of 'apS'
--     handle (Left <$> pure id) (flip ($) <$> v)
--     === -- Push 'Left' inside 'pure'
--     handle (pure (Left id)) (flip ($) <$> v)
--     === -- Apply P2
--     ($id) <$> (flip ($) <$> v)
--     === -- Simplify
--     id <$> v
--     === -- Functor identity: -- Functor identity: fmap id = id
--     v
