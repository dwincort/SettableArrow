Copyright (c) Daniel Winograd-Cort 2014

This file provides code to accompany the ICFP paper "Settable and 
Non-Interfering Signal Functions for FRP" (see citation below).

As a sample instantiation of Arrow, we use a function automaton drawn 
from the ArrowTransformers library.  We then set up the settability 
data types and show the transformation as a set of type classes.  At the 
bottom of this file, we provide some small demonstrations.

Winograd-Cort, Daniel and Hudak, Paul. Settable and Non-Interfering Signal Functions for FRP. In: International Conference on Functional Programming. ACM, September 2014.

-------------------------------------------------------------------------------

Obviously, we'll be using arrow syntax, and as such, we need to enable GHC's 
arrow syntax language pragma.  Beyond that, 
we use type synonym instances and flexible instances in order to easily adapt 
the Automaton type for our use, and we throw in tuple sections because they're 
nice.

> {-# LANGUAGE Arrows #-}
> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
> {-# LANGUAGE TupleSections #-}

We import:
- Arrow and SettableArrow for obvious reasons
- Dynamic to have the Typeable constraint
- Automaton, Stream, and Arrow Operations for use as our sample Arrow instance

> import Control.Arrow
> import Control.Arrow.SettableArrow
> import Data.Dynamic (Typeable)
> import Control.Arrow.Transformer.Automaton
> import qualified Data.Stream as S (toList, fromList)
> import qualified Control.Arrow.Operations as OPS (delay)
> import Data.Maybe (isJust)

-------------------------------------------------------------------------------
- The SF type

To begin, we will set up our sample arrow.  As mentioned, we will use 
the Automaton arrow with regular functions.  This is straightforward, and 
we keep this new SF type as a type synonym for ease of use.  We will always 
be creating objects of this type with arrow syntax anyway, so there's no 
need to force us to wrap them by using, say, newtype.

> type SF = Automaton (->)
> instance ArrowDelay SF where
>   delay i = OPS.delay i

Finally, we convert the default running behavior to one using Haskell's 
native lists to simplify our testing.  (Note that if finite lists are used, 
this can cause errors.)

> runSF :: SF b c -> [b] -> [c]
> runSF sf inp = S.toList $ runAutomaton (arr snd >>> sf) ((), S.fromList inp)


-------------------------------------------------------------------------------
- Running a Settable Arrow

We'll make two convenience functions for dealing with specifically settable 
arrows.  First, we provide:

> runS :: SA SF b c -> [b] -> [c]
> runS (SA f) xs = map fst $ runSF f (map (,Nothing) xs)

This runS function will take settable-wrapped SF and ignores all 
State inputs and outputs.  This should behave exactly as an 
unwrapped SF.

Our second convenience function will provide an easy way to store, load, or 
reset the state of our signal function.  Rather than having to manually 
handle the state, this function will accept both the input stream as well as 
a "Control" stream to drive the settability:
- The default value is None, which will provide Nothing as input and ignore 
  the outputs.
- The Store value will still provide Nothing as the input, but it will capture 
  the output state to be used later.  Initially, the stored value is reset.
- The Load value will used the stored state as the input to the settable arrow.
- The Reset value will reset the settable arrow to its initial state.

> data Control = None | Store | Load | Reset deriving (Eq, Show)
> 
> runS' :: SA SF b c -> [(b, Control)] -> [c]
> runS' (SA f) bcs = 
>     let out = runSF f inp
>         inp = foo (Just reset) bcs out
>         foo _ [] _ = []
>         foo saved ((b, None):bs) outs = (b,Nothing):(foo saved bs (tail outs))
>         foo saved ((b, Store):bs) outs = (b,Nothing):(foo (Just $ snd $ head outs) bs (tail outs))
>         foo saved ((b, Load):bs) outs = (b,saved):(foo saved bs (tail outs))
>         foo saved ((b, Reset):bs) outs = (b,(Just reset)):(foo saved bs (tail outs))
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
>       (x,s1) <- settable counter -< ((), Just s0)
>       (y,s2) <- settable counter -< ((), Just s1)
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
- Some functions from the paper

The paper makes uses of switching in order to compare non-interfering choice 
and settability to it, but we have no concept of switching in our setup 
here.  Therefore, we introduce a new Arrow type class to capture switching 
solely for the purpose of crafting these programs.  A suitable extension to 
SF could be made, but we refrain from that here.

> class Arrow a => ArrowSwitch a where
>   switch :: a b (c, Maybe t) -> (t -> (a b c)) -> a b c
>   rSwitch :: a b c -> a (b, Maybe (a b c)) c
>   pSwitch :: Functor col => col (a b c) -> a (b, col c) (Maybe t)
>           -> (col (a b c) -> t -> a b (col c)) -> a b (col c)

We also provide two helper functions:

> constA :: Arrow a => c -> a b c
> constA c = arr (const c)
> 
> integral :: (ArrowDelay a, ArrowLoop a) => a Double Double
> integral = proc x -> do
>   rec i <- delay 0 -< i + x * dt
>   returnA -< i
>  where dt = 1

With this setup, we can write the three versions of integralWhen

> integralWhenNaive :: (ArrowLoop a, ArrowDelay a) => a (Double, Bool) Double
> integralWhenNaive = proc (i,b) -> do
>   v <- integral -< i
>   vPrev <- delay 0 -< v
>   let vDelta = v - vPrev
>   rec result <- delay 0 -< if b then result + vDelta else result
>   returnA -< result
> 
> integralWhenSwitch :: (ArrowLoop a, ArrowDelay a, ArrowSwitch a) => a (Double, Maybe Bool) Double
> integralWhenSwitch = proc (i, eb) -> do
>   rec v <- rSwitch (constA 0) -< (i,
>             fmap (\b -> if b then (integral >>> arr (+v)) else (constA v)) eb)
>   returnA -< v
> 
> integralWhenChoice :: (ArrowChoice a, ArrowDelay a, ArrowLoop a) => a (Double, Bool) Double
> integralWhenChoice = proc (i,b) -> do
>   rec v <- if b then integral -< i
>                 else returnA -< v'
>       v' <- delay 0 -< v
>   returnA -< v

as well as the three versions of integralReset

> integralResetSwitch :: (ArrowLoop a, ArrowDelay a, ArrowSwitch a) => a (Double, Maybe ()) Double
> integralResetSwitch = proc (i,e) -> do
>   rSwitch integral -< (i, fmap (const integral) e)
> 
> integralResetBasic :: (ArrowLoop a, ArrowDelay a) => a (Double, Maybe ()) Double
> integralResetBasic = proc (i,e) -> do
>   o <- integral -< i
>   rec let k = if isJust e then o else k'
>       k' <- delay 0 -< k
>   returnA -< o-k
> 
> integralReset :: (ArrowLoop a, ArrowDelay a, SettableArrow a) => a (Double, Maybe ()) Double
> integralReset = proc (i,e) -> do
>   (v,_) <- settable integral -< (i, fmap (const reset) e)
>   returnA -< v

and our functions that show off arrowized recursion:

> runNTimes :: Arrow a => Int -> a b c -> a [b] [c]
> runNTimes 0 _  = constA []
> runNTimes n sf = proc (b:bs) -> do
>   c  <- sf -< b
>   cs <- runNTimes (n-1) sf -< bs
>   returnA -< (c:cs)
> 
> runDynamic :: ArrowChoice a => a b c -> a [b] [c]
> runDynamic sf = proc lst -> 
>   case lst of
>     [] -> returnA -< []
>     b:bs -> do
>         c <- sf -< b
>         cs <- runDynamic sf -< bs
>         returnA -< c:cs

-------------------------------------------------------------------------------
- Choice-Based Implementations of Switch

> switchChoice :: (ArrowLoop a, ArrowDelay a, ArrowChoice a) 
>              => a b (c, Maybe t) -> a (Maybe t, b) c -> a b c
> switchChoice sf1 sf2 = proc a -> do
>   rec onOne <- delay True -< not onTwo
>       (b, et) <- if onOne 
>                  then sf1 -< a
>                  else returnA -< (undefined, Nothing)
>       let onTwo = isJust et || not onOne
>   if onTwo then sf2 -< (et, a)
>            else returnA -< b
> 
> pChoice :: (Typeable inp, Eq key, Eq uid, Typeable uid, 
>             ArrowChoice a, ArrowLoop a, ArrowDelay a, SettableArrow a) => 
>     [(key, a (Maybe inp) result)] -> a [(key, (uid, Maybe inp))] [result]
> pChoice [] = constA []
> pChoice ((key, sf):rst) = proc es -> do
>     rec states <- delay [] -< newStates
>         let esThis = map snd $ filter ((== key) . fst) es
>             inputStates = update states esThis
>         output <- runDynamic (first (settable sf)) -< inputStates
>         let newStates = map (\ ((_, s), uid) -> ((Nothing, Just s), uid)) output
>     rs <- pChoice rst -< es
>     returnA -< (map (fst . fst) output) ++ rs
>   where update s [] = s
>         update s ((uid, Nothing):rst) = update (filter ((/= uid) . snd) s) rst
>         update s ((uid, i):rst) = update (((i, Just reset), uid):s) rst



