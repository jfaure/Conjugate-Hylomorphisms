{-# Language FlexibleInstances , MultiParamTypeClasses , GADTs , RankNTypes , QuantifiedConstraints , TypeOperators , KindSignatures , DeriveFunctor #-}
module CH where
 
import Prelude hiding (Product , Sum)
import Data.Functor.Identity
import Data.Functor.Base
import Data.Functor.Sum
import Data.Functor.Product
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree
import Control.Comonad.Trans.Env
import Control.Arrow
import Data.Functor.Compose
import GHC.Prim
import GHC.Generics
identity = Prelude.id

{-
instance Adj w m => Adj (EnvT e w) (ReaderT e m) where
  aunit              = ReaderT . flip fmap EnvT . flip lAdjunct
  acounit (EnvT e w) = rAdjunct (flip runReaderT e) w

instance (Adj f g, Adj f' g') => Adj (Sum f f') (Product g g') where
  aunit a = Pair (lAdjunct InL a) (lAdjunct InR a)
  acounit (InL l) = rAdjunct (\(Pair x _) -> x) l
  acounit (InR r) = rAdjunct (\(Pair _ x) -> x) r
-}

-- iff there is a bijection between the sets of arrows: (natural in both A and B)
-- adjunctL : C(L a -> b) ~= D(A -> R B) : adjunctR
data (Functor l , Functor r) => Adjunction l r = Adjunction
 { aunit     :: forall a.   a -> r (l a)
 , counit    :: forall a.   l (r a) -> a
 , adjunctL  :: forall a b. (l a -> b) -> a -> r b
 , adjunctR  :: forall a b. (a -> r b) -> l a -> b
 }

-- Adjoint functors give rise to a monad. unit = aunit ,  join = fmap counit and bind:
adjBind :: (Functor f1, Functor l, Functor r, Functor f2) =>
     Adjunction l r -> f1 (f2 a) -> (a -> b) -> f1 (r (l (f2 b)))
adjBind a = \x f -> fmap (aunit a) (fmap (fmap f) x)

-- ghc ?!
--adjCompose :: (Functor l, Functor r, Functor l', Functor r'
--  , cl ~ Compose l l' , cr ~ Compose r' r) =>
--  Adjunction l r -> Adjunction l' r' -> Adjunction cl cr
--adjCompose a b = mkAdjUnit (fmap (aunit a) . aunit b) (counit a . fmap (counit b))

xUnit :: (Functor f, Functor g, Functor f', Functor g')
  => Adjunction f g -> Adjunction f' g' -> a -> g' (g (f (f' a)))
xUnit a b = fmap (aunit a) . aunit b -- g'gff' OK
xCoUnit :: (Functor f, Functor g, Functor f', Functor g')
  => Adjunction f g -> Adjunction f' g' -> f (f' (g' (g a))) -> a
xCoUnit a b = counit a . fmap (counit b) -- FF'G'G

--f :: forall r l g' g f f' a. 
--  ( r ~ Compose g' g , l ~ Compose f' f
--  , (forall a b. Coercible a b => Coercible (g' (g a)) (g' (g b)))
--  ) => (a -> g' (g (f' (f a)))) -> (a -> r (l a))
--f = coerce
--xxUnit a b = let
--  g = xUnit a b
--  in coerce g

-- shortcut to define adjunctions using adjunction properties
mkAdjUnit :: (Functor l , Functor r) =>
  (forall a b. a -> r (l a)) -> (forall a b. l (r a) -> a) -> Adjunction l r
mkAdjUnit unit counit = Adjunction unit counit (\f->fmap f . unit) (\f->counit . fmap f)
mkAdjlArA :: (Functor l , Functor r) =>
  (forall a b. (l a -> b) -> a -> r b) -> (forall a b. (a -> r b) -> l a -> b) -> Adjunction l r 
mkAdjlArA lA rA = Adjunction (lA identity) (rA identity) lA rA

identityAdjunction = mkAdjlArA (\f -> Identity . f . Identity) (\f -> runIdentity . f . runIdentity)

curryAdjunction :: Adjunction ((,) t) ((->) t)
curryAdjunction = mkAdjlArA (\f a e -> f (e , a)) (\f (e , a) -> f a e)

-- Coproducts and products arise as left and right adjoints of the diagonal functor
-- Diag : C -> C X C , defined by Diag A = (A , A)
-- for products, the left adjunct ⃤⃤is called △ 'split'
data Diag a = Diag a a deriving (Functor , Show)
data DiagProd (k :: * -> * -> *) = DiagProd
--split :: (Functor l , Functor r) => forall a b. (l a -> b) -> a -> r b

--coProdDiagAdj = Adjunction unit coDP split rA where
--  unit = split identity
--  rA = (\f->coDP . fmap f)
--diagProdAdj   = _

-- envReaderAdjunction = mkAdjUnit

sumProdAdj :: (Functor f , Functor f' , Functor g , Functor g')
  => Adjunction f g -> Adjunction f' g' -> Adjunction (f :+: f') (g :*: g')
sumProdAdj adj1 adj2 = mkAdjUnit (\a -> (adjunctL adj1) L1 a :*: (adjunctL adj2) R1 a) (\case { L1 l -> (adjunctR adj1) (\(x :*: _) -> x) l ; R1 r -> (adjunctR adj2) (\(_ :*: x) -> x) r} )

-- Conjugate rule: c1 ~= c2
c1 :: (Functor d , Functor l , Functor r) =>
  Adjunction l r -> (l (d (r b)) -> b) -> (a -> d a) -> l a -> b
c1 adj a c = h where h = a . fmap{-L-} (fmap{-D-} (adjunctL adj h) . c) -- (3.9)
c2 adj a c = h where h = (adjunctR adj) (adjunctL adj a . fmap{-D-} (adjunctL adj h) . c)

hyloShift :: Functor d => (Identity (d (Identity b)) -> b) -> (a -> d a) -> Identity a -> b
hyloShift = c1 identityAdjunction

hAccu :: Functor d => ((p , d (p -> b)) -> b) -> (a -> d a) -> (p , a) -> b
hAccu = c1 curryAdjunction

-- Constant parameters can be modelled using the strength of a functor
--constParam :: Functor f => (f b -> b) -> (a -> f a) -> (a, p) -> b
--constParam a c = h where
--  h = a . fmap h . strength . (c *** identity)
--  strength :: Functor d => (d a , p) -> d (a , p)
--  strength (f , p) = fmap (,p) f
