Copyright (c) Daniel Winograd-Cort 2015

This module implements settability as described in the ICFP paper 
"Settable and Non-Interfering Signal Functions for FRP".

Winograd-Cort, Daniel and Hudak, Paul. Settable and Non-Interfering Signal Functions for FRP. In: International Conference on Functional Programming. ACM, September 2014.

-------------------------------------------------------------------------------

Obviously, we'll be using arrow syntax, and as such, we need to enable GHC's 
arrow syntax language pragma.  We also will be making use of the Typeable and 
Dynamic features, so we enable Typeable deriving for data types.

> {-# LANGUAGE Arrows, DeriveDataTypeable #-}

The module will export the SA type we create as well as the State type.  
However, the State type does not come with constructors.

> module Control.Arrow.SettableArrow (
>   ArrowDelay(..), SettableArrow(..), SA(..),
>   State, reset, 
>   unsafeSA
> ) where

We import:
- Arrow and Category to instantiate their type classes
- Dynamic for use with the State type

> import Prelude hiding (id, (.))
> import Control.Category
> import Control.Arrow
> import Data.Dynamic (Typeable, Dynamic(..), toDyn, fromDyn)

-------------------------------------------------------------------------------
- Events

Events are an option type, and are thus equivalent to the Maybe type.  
Therefore, rather than create a new type for them, we will just use 
the Maybe type.  This makes the code less consistent with that of the 
paper, but it is more extensible for the Haskell community.

We use the following merge function as in the paper, which gives 
preference to the left argument.

> mergeE :: Maybe a -> Maybe a -> Maybe a
> mergeE Nothing t = t
> mergeE e _ = e

-------------------------------------------------------------------------------
- State

Before we can define settability, we must define the State type that controls 
the settable behavior.  This is exactly as outlined in the paper:

> data State = NoState
>            | DState Dynamic
>            | PairState State State
>   deriving (Typeable)

The reset state is a special state that can always be given as an argument 
to any settable arrow and resets it to its default state

> reset :: State
> reset = NoState

We can also split a State Event into its components

> split :: Maybe State -> (Maybe State, Maybe State)
> split Nothing                = (Nothing, Nothing)
> split (Just NoState)         = (Just NoState, Just NoState)
> split (Just (PairState l r)) = (Just l, Just r)
> split (Just (DState _)) = error $ "Tried to split a DState"

> joinS :: State -> State -> State
> joinS NoState NoState = NoState
> joinS s1 s2 = PairState s1 s2

-------------------------------------------------------------------------------
- Settable Arrow

The arrows package (Control.Arrow.Operations in particular) has a delay 
operator that comes in the ArrowCircuit type class.  However, for our 
purposes, we require that the type of delay enforces a Typeable constraint 
on the delayable values.  Thus, we create a new ArrowDelay class:

> class Arrow a => ArrowDelay a where
>   delay :: Typeable b => b -> a b b

Finally, we are able to define our SettableArrow class:

> class SettableArrow a where
>   settable :: a b c -> a (b, Maybe State) (c, State)

and along with it, the SettableArrow wrapper data type that we will use to 
perform our transformation:

> newtype SA a b c = SA (a (b, Maybe State) (c, State))

If we have a base arrow that we need to lift into the SA type and we 
know that there are no settable components within that base arrow, 
then we can use the following helper function:

> unsafeSA :: Arrow a => a b c -> SA a b c
> unsafeSA a = SA $ a *** (arr $ const NoState)

What follows are the instances of the various Arrow classes for an SA 
wrapped arrow.

> instance Arrow a => Category (SA a) where
>   id = SA $ arr $ \(b, _) -> (b, NoState)
>   (SA g) . (SA f) = SA $ 
>     arr (\(b,et) -> (let (el,er) = split et in ((b,el),er))) >>>
>     first f >>> arr (\((c,t1),er) -> ((c,er),t1)) >>> first g >>>
>     arr (\((d,t2),t1) -> (d, joinS t1 t2))
> 
> instance Arrow a => Arrow (SA a) where
>   arr f = SA $ arr $ \(b, _) -> (f b, NoState)
>   first (SA f) = SA $ 
>       arr (\((b,d), et) -> ((b,et),d)) >>> first f >>> arr (\((c,t), d) -> ((c,d),t))
>   second (SA f) = SA $ 
>       arr (\((d,b), et) -> (d,(b,et))) >>> second f >>> arr (\(d,(c,t)) -> ((d,c),t))
>   (SA f) *** (SA g) = SA $ 
>     arr (\((b,b'), et) -> (let (el,er) = split et in ((b,el),(b',er)))) >>>
>     f *** g >>> arr (\((c,t1),(c',t2)) -> ((c,c'), joinS t1 t2))

> instance ArrowLoop a => ArrowLoop (SA a) where
>   loop (SA f) = SA $ loop $ 
>       arr (\((b,et), d) -> ((b,d),et)) >>> f >>> arr (\((c,d), t) -> ((c,t),d))
> 
> instance (ArrowLoop a, ArrowChoice a, ArrowDelay a) => ArrowChoice (SA a) where
>   left ~(SA f) = SA $ proc (bd, et) -> do
>     rec (oldState, pendingUpdate) <- delay (NoState, Nothing) -< (newState, newUpdate)
>         let thisUpdate = mergeE et pendingUpdate
>         (newState, newUpdate, cd) <- case thisUpdate `seq` bd of
>             Left b  -> do
>                 (c,t) <- f -< (b, thisUpdate)
>                 returnA -< (t, Nothing, Left c)
>             Right d -> returnA -< (oldState, thisUpdate, Right d)
>     returnA -< (cd, newState)
>   right ~(SA f) = SA $ proc (db, et) -> do
>     rec (oldState, pendingUpdate) <- delay (NoState, Nothing) -< (newState, newUpdate)
>         let thisUpdate = mergeE et pendingUpdate
>         (newState, newUpdate, dc) <- case thisUpdate `seq` db of
>             Right b  -> do
>                 (c,t) <- f -< (b, thisUpdate)
>                 returnA -< (t, Nothing, Right c)
>             Left d -> returnA -< (oldState, thisUpdate, Left d)
>     returnA -< (dc, newState)
> 
> instance ArrowDelay a => ArrowDelay (SA a) where
>   delay i = SA $ first (delay i &&& id) >>> arr (\((told,tnew),et) -> (f told et, DState (toDyn tnew)))
>    -- proc (tnew,et) -> do
>    --  told <- delay i -< tnew
>    --  returnA -< (f told et, DState (toDyn tnew))
>    where f s Nothing = s
>          f _ (Just NoState) = i
>          f _ (Just (DState d)) = fromDyn d (error "bad Dynamic")
>          f _ (Just (PairState _ _)) = error "delay given PairState."
> 
> instance (Arrow a, ArrowDelay a) => SettableArrow (SA a) where
>   settable (SA f) = SA $ proc ((b, et), et') -> do
>     (c,t) <- f -< (b, mergeE et' et)
>     returnA -< ((c,t), t)



