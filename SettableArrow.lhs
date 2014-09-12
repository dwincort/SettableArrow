Copyright (c) Daniel Winograd-Cort 2014

This file provides code to accompany the ICFP paper "Settable and 
Non-Interfering Signal Functions for FRP" (see citation below).

As a sample instantiation of Arrow, we use a function automaton drawn 
from the ArrowTransformers library.  We then set up the settability 
data types and show the transformation as a set of type classes.  At the 
bottom of this file, we provide some small demonstations.

Winograd-Cort, Daniel and Hudak, Paul. Settable and Non-Interfering Signal Functions for FRP. In: International Conference on Functional Programming. ACM, September 2014.

-------------------------------------------------------------------------------

Obviously, we'll be using arrow syntax, and as such, we need to enable GHC's 
arrow syntax language pragma.  We also will be making use of the Typeable and 
Dynamic features, so we enable Typeable deriving for data types.  Beyond that, 
we use type synonym instances and flexible instances in order to easily adapt 
the Automaton type for our use, and we throw in tuple sections because they're 
nice.

> {-# LANGUAGE Arrows, DeriveDataTypeable #-}
> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
> {-# LANGUAGE TupleSections #-}

We import:
- Arrow and Category to instantiate their type classes
- Dynamic for use with the State type
- Automaton, Stream, and Arrow Operations for use as our sample Arrow instance

> import Prelude hiding (id, (.))
> import Control.Category
> import Control.Arrow
> import Data.Dynamic (Typeable, Dynamic(..), toDyn, fromDyn)
> import Control.Arrow.Transformer.Automaton
> import qualified Data.Stream as S (toList, fromList)
> import qualified Control.Arrow.Operations as OPS (delay)

-------------------------------------------------------------------------------
- The SF type

To begin, we will set up our sample arrow.  As mentioned, we will use 
the Automaton arrow with regular functions.  This is straightforward, and 
we keep this new SF type as a type synonym for ease of use.  We will always 
be creating objects of this type with arrow syntax anyway, so there's no 
need to force us to wrap them by using, say, newtype.

> type SF = Automaton (->)

The arrows package (Control.Arrow.Operations in particular) has a delay 
operator that comes in the ArrowCircuit type class.  However, for our 
purposes, we require that the type of delay enforces a Typeable constraint 
on the delayable values.  Thus, we create a new ArrowDelay class:

> class Arrow a => ArrowDelay a where
>   delay :: Typeable b => b -> a b b

and we use it to wrap ArrowCircuit's delay:

> instance ArrowDelay SF where
>   delay i = OPS.delay i

Finally, we convert the default running behavior to one using Haskell's 
native lists to simplify our testing.  (Note that if finite lists are used, 
this can cause errors.)

> runSF :: SF b c -> [b] -> [c]
> runSF sf inp = S.toList $ runAutomaton (arr snd >>> sf) ((), S.fromList inp)

-------------------------------------------------------------------------------
- Events

Events are an option type, but to maintain consistency with code in the 
paper, we create a new data type for them with an accompanying Functor 
instance:

> data Event a = NoEvent | Event a
>   deriving (Eq, Show, Typeable)
> instance Functor Event where
>   fmap f (Event a) = Event $ f a
>   fmap _ NoEvent = NoEvent

We use the following merge function as in the paper, which gives 
preference to the left argument.

> mergeE :: Event a -> Event a -> Event a
> mergeE NoEvent t = t
> mergeE e _ = e

-------------------------------------------------------------------------------
- State

Before we can define settability, we must define the State type that controls 
the settable behavior.  This is exactly as outlined in the paper:

> data State = NoState
>            | DState Dynamic
>            | PairState State State
>   deriving (Show, Typeable)

The reset state is a special state that can always be given as an argument 
to any settable arrow and resets it to its default state

> reset :: State
> reset = NoState

We can also split a State Event into its components

> split :: Event State -> (Event State, Event State)
> split NoEvent                 = (NoEvent, NoEvent)
> split (Event NoState)         = (Event NoState, Event NoState)
> split (Event (PairState l r)) = (Event l, Event r)
> split (Event (DState _)) = error $ "Tried to split a DState"

-------------------------------------------------------------------------------
- Settable Arrow

Finally, we are able to define our SettableArrow class:

> class SettableArrow a where
>   settable :: a b c -> a (b, Event State) (c, State)

and along with it, the SettableArrow wrapper data type that we will use to 
perform our transformation:

> data SA a b c = SA (a (b, Event State) (c, State))

What follows are the instances of the various Arrow classes for an SA 
wrapped arrow.

> instance Arrow a => Category (SA a) where
>   id = SA $ arr $ \(b, _) -> (b, NoState)
>   (SA g) . (SA f) = SA $ proc (b,et) -> do
>     let (el,er) = split et
>     (c, t1) <- f -< (b, el)
>     (d, t2) <- g -< (c, er)
>     returnA -< (d, PairState t1 t2)
> 
> instance Arrow a => Arrow (SA a) where
>   arr f = SA $ arr $ \(b, _) -> (f b, NoState)
>   first (SA f) = SA $ proc ((b,d), et) -> do
>     (c, t) <- f -< (b, et)
>     returnA -< ((c,d), t)
> 
> instance ArrowLoop a => ArrowLoop (SA a) where
>   loop (SA f) = SA $ proc (b,et) -> do
>     rec ((c,d),t) <- f -< ((b,d),et)
>     returnA -< (c,t)
> 
> instance (ArrowLoop a, ArrowChoice a, ArrowDelay a) => ArrowChoice (SA a) where
>   left ~(SA f) = SA $ proc (bd, et) -> do
>     rec (oldState, pendingUpdate) <- delay (NoState, NoEvent) -< (newState, newUpdate)
>         let thisUpdate = mergeE et pendingUpdate
>         (newState, newUpdate, cd) <- case bd of
>             Left b  -> do
>                 (c,t) <- f -< (b, thisUpdate)
>                 returnA -< (t, NoEvent, Left c)
>             Right d -> returnA -< (oldState, thisUpdate, Right d)
>     returnA -< (cd, newState)
> 
> instance ArrowDelay a => ArrowDelay (SA a) where
>   delay i = SA $ proc (tnew,et) -> do
>     told <- delay i -< tnew
>     returnA -< (f told et, DState (toDyn tnew))
>    where f s NoEvent = s
>          f _ (Event NoState) = i
>          f _ (Event (DState d)) = fromDyn d (error "bad Dynamic")
>          f _ (Event (PairState _ _)) = error "delay given PairState."
> 
> instance (Arrow a, ArrowDelay a) => SettableArrow (SA a) where
>   settable (SA f) = SA $ proc ((b, et), et') -> do
>     (c,t) <- f -< (b, mergeE et' et)
>     returnA -< ((c,t), t)


-------------------------------------------------------------------------------
- Running a Settable Arrow

We'll make two convenience functions for dealing with specifically settable 
arrows.  First, we provide:

> runS :: SA SF b c -> [b] -> [c]
> runS (SA f) xs = map fst $ runSF f (map (,NoEvent) xs)

This runS function will take settable-wrapped SF and ignores all 
State inputs and outputs.  This should behave exactly as an 
unwrapped SF.

Our second convenience function will provide an easy way to store, load, or 
reset the state of our signal function.  Rather than having to manually 
handle the state, this function will accept both the input stream as well as 
a "Control" stream to drive the settability:
- The default value is None, which will provide NoEvent as input and ignore 
  the outputs.
- The Store value will still provide NoEvent as the input, but it will capture 
  the output state to be used later.  Initially, the stored value is reset.
- The Load value will used the stored state as the input to the settable arrow.
- The Reset value will reset the settable arrow to its initial state.

> data Control = None | Store | Load | Reset deriving (Eq, Show)
> 
> runS' :: SA SF b c -> [(b, Control)] -> [c]
> runS' (SA f) bcs = 
>     let out = runSF f inp
>         inp = foo (Event reset) bcs out
>         foo _ [] _ = []
>         foo saved ((b, None):bs) outs = (b,NoEvent):(foo saved bs (tail outs))
>         foo saved ((b, Store):bs) outs = (b,NoEvent):(foo (Event $ snd $ head outs) bs (tail outs))
>         foo saved ((b, Load):bs) outs = (b,saved):(foo saved bs (tail outs))
>         foo saved ((b, Reset):bs) outs = (b,(Event reset)):(foo saved bs (tail outs))
>     in map fst out

-------------------------------------------------------------------------------
- Sample Functions

To test out the settability functionality, we create some simple functions 
that we can make settable or not.  We would like to be able to run them 
either as SFs or as settable-wrapped SFs, so we keep them as polymorphic 
as possible.

First, we make a simple, stateful counter.  We use the Int type annotation 
because a polymorphic type may not be Typeable.

> counter :: (ArrowLoop a, ArrowDelay a) => a () Int
> counter = proc _ -> do
>   rec i <- delay (0 :: Int) -< i+1
>   returnA -< i+1
> 
> testC0 = take 5 $ runSF counter $ repeat ()
> testC1 = take 5 $ runS  counter $ repeat ()

The output of both of these testC tests is [1,2,3,4,5].

In this next example, we will use settability to transfer updates between 
two counters.  First, let's examine a signal function of two parallel 
counters:

> twoCounters :: (ArrowLoop a, ArrowDelay a) => a () (Int,Int)
> twoCounters = proc _ -> do
>   x <- counter -< ()
>   y <- counter -< ()
>   returnA -< (x,y)
> 
> testTC0 = take 5 $ runSF twoCounters $ repeat ()
> testTC1 = take 5 $ runS  twoCounters $ repeat ()

The output of testTC0 and testTC1 will be:
[(1,1),(2,2),(3,3),(4,4),(5,5)].  
The two counters each have their own state, and so they do not interact.  
With settability, however, we can make them interact.  For our settable 
example, we will pipe the state of the first counter into the second:

> twoCounters' :: (SettableArrow a, ArrowLoop a, ArrowDelay a) => a () (Int,Int)
> twoCounters' = proc _ -> do
>   rec s0 <- delay reset -< s2
>       (x,s1) <- settable counter -< ((), Event s0)
>       (y,s2) <- settable counter -< ((), Event s1)
>   returnA -< (x,y)
> 
> testTC2 = take 5 $ runS twoCounters' $ repeat ()

The output of testTC2 will be [(1,2),(3,4),(5,6),(7,8),(9,10)].


-------------------------------------------------------------------------------
- Settability with Non-Interfering Choice

The SF instance that we are working with obeys the Non-Interference law for 
choice described in the paper, so in this section, we will look at a few 
examples specifically to show that off (also to show off settability on 
ArrowChoice in general).

As a simple case, we will take the choice of two counters:

> choiceCounter ::  (ArrowChoice a, ArrowLoop a, ArrowDelay a) => a (Either () ()) Int
> choiceCounter = counter ||| counter
> 
> testChoice = take 6 $ runS' choiceCounter $ zip 
>       [Right (), Right (), Right (), Left (), Left (), Right ()]
>       ([Store, None, None, Load, None, None]++repeat None)

I'm not sure of any canonical arguments for this, so we just take some 
arbitrary ones.  Here, we store the state after the first input and then 
load it for the fourth input.  If we looked at the states of both counters, 
we would expect the following:
    [(0,1), (0,2), (0,3), (1,1), (2,1), (2,2)]
       |                    |
     STORE                LOAD
Thus, the output we actually see will be:
[1,2,3,1,2,2]

---- Arrowized Recursion ----
In this next example, we will perform some arrowized recursion, the new form 
of recursion made possible by non-interfering choice.  In the paper, I show 
a runDynamic function.  To make it simpler to use with the counters, here 
I show the runDynamicN function:

> runDynamicN :: (Eq n, Num n, ArrowChoice a) => a () b -> a n [b]
> runDynamicN sf = proc n -> do
>   case n of
>     0 -> returnA -< []
>     i -> do
>           b <- sf -< ()
>           bs <- runDynamicN sf -< i-1
>           returnA -< b:bs

Notice that it still is making the branching decision based on the streaming 
argument, but it branches based on a number rather than a list of inputs and 
uses () for every input.

Once again, I know of no canonical tests, so here are two arbitrary ones:

> testAR0 = take 9 $ runSF (runDynamicN counter) [3,1,3,2,3,1,2,4,12]
> testAR1 = take 9 $ runS' (runDynamicN counter) $ 
>                     zip [3,1,3,2,3,1,2,4,12] 
>                         ([None, Store, None, None, None, Load]++repeat None)

In the first example, we perform no settability (and so we could have just as 
easily used runS instead of runSF).  We will get the output:
[[1,1,1],[2],[3,2,2],[4,3],[5,4,3],[6],[7,5],[8,6,4,1],[9,7,5,2,1,1,1,1,1,1,1,1]]
Note that the values only increase (e.g. the counter is only active) when the input 
number is low enough.

For testAR2, we perform a store and load, so we expect the following output:
[[1,1,1],[2],[3,2,2],[4,3],[5,4,3],[3],[4,2],[5,3,2,1],[6,4,3,2,1,1,1,1,1,1,1,1]]
          |                         |
        STORE                     LOAD
Note that even state that is not currently 'active' in our recursion is still 
properly loaded.


-------------------------------------------------------------------------------
- Above and beyond

I don't provide any examples of its use here, but as it's in the paper, I 
will here provide the definition of pChoice.

> runDynamic :: ArrowChoice a => a b c -> a [b] [c]
> runDynamic sf = proc lst -> 
>   case lst of
>     [] -> returnA -< []
>     b:bs -> do
>         c <- sf -< b
>         cs <- runDynamic sf -< bs
>         returnA -< c:cs
> 
> pChoice :: (Typeable inp, Eq key, Eq uid, Typeable uid, 
>             ArrowChoice a, ArrowLoop a, ArrowDelay a, SettableArrow a) => 
>     [(key, a (Maybe inp) result)] -> a [(key, (uid, Maybe inp))] [result]
> pChoice [] = arr . const $ [] --constA []
> pChoice ((key, sf):rst) = proc es -> do
>     rec states <- delay [] -< newStates
>         let esThis = map snd $ filter ((== key) . fst) es
>             inputStates = update states esThis
>         output <- runDynamic (first (settable sf)) -< inputStates
>         let newStates = map (\ ((_, s), uid) -> ((Nothing, Event s), uid)) output
>     rs <- pChoice rst -< es
>     returnA -< (map (fst . fst) output) ++ rs
>   where update s [] = s
>         update s ((uid, Nothing):rst) = update (filter ((/= uid) . snd) s) rst
>         update s ((uid, i):rst) = update (((i, Event NoState), uid):s) rst

