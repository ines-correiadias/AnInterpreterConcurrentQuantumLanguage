-- Operational semantics of the basic parallel language (presented in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.) 
-- but with probabilistic choice besides parallel commands (probabilities + concurrency):

-- C::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C | C1 || C2

-- NOTA PARA MIM: já testei smallStepList, bigStepList, smallStep, bigStep, applySmallStepList, applyBigStepList, applySmallStep, applyBigStep, simplify

import SemBE_Brookes -- module created in SemBE_Brookes.hs
import GrammarBrookes -- module created in GrammarBrookes.hs
import System.Random -- library that deals with pseudo-random number generation
import Numeric.Probability.Game.Event -- import functions for smallStep and bigStep

-- States
s1= [("a",1), ("b",2), ("c",3)]

--------------------------------------------------------------------------
-- DUVIDAS SOBRE O QUE FAZER A SEGUIR:
-- é preciso resolver o problema do Haskell? - SIM, mas menos prioritario

-- VER: problema do Haskell: 1-0.9 = 0.0999999999
-- quanto a este problema: rever https://stackoverflow.com/questions/33161504/how-to-calculate-floating-point-numbers-in-haskell
-- talvez o mais simples seja mesmo usar o tipo Rational do Prelude
---------------------------------------------------------------------------

-- Note that functions bigStepList, smallStepList, bigStep and smallStep are supposed to be used as arguments of applyBigStepList, applySmallStepList, applyBigStep 
-- and applySmallStep, respectively, which are responsible for checking if all identifiers in the given command are declared in the given state, and 
-- if all probability values in the command are valid.

-- (errorSem c s) is an error message telling that not all free identifiers in c are part of state s and/or not all probabilities in c are valid.
errorSem :: CpC -> S -> String
errorSem c s = "Not all free identifiers in "++(show c)++" are part of state "++(show s)++" AND/OR not all probabilities in "++(show c)++" are valid."

-- (applySmallStepList c s) is the result of applying function smallStepList to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applySmallStepList :: CpC -> S -> [[ConfPC]]
applySmallStepList c s = if (belong (freeC c) s) && (validProb c) then removeZerosList (smallStepList c s) else error (errorSem c s)

-- (applyBigStepList c s) is the result of applying function bigStepList to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStepList :: CpC -> S ->  [[ConfPC]] 
applyBigStepList c s = if (belong (freeC c) s) && (validProb c) then simplify (bigStepList c s) else error (errorSem c s)

-- (applySmallStep c s) is the result of applying function smallStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applySmallStep :: CpC -> S -> IO (CpC,S)
applySmallStep c s = if (belong (freeC c) s) && (validProb c) then smallStep c s else error (errorSem c s)

-- (applyBigStep c s) is the result of applying function bigStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStep :: CpC -> S -> IO (CpC,S)
applyBigStep c s = if (belong (freeC c) s) && (validProb c) then bigStep c s else error (errorSem c s)

freeC :: CpC -> [String] -- (freeC c) is the set of free identifiers in c
freeC SkipPC = []
freeC (AsgPC i e) = i : (freeE e)
freeC (SeqPC c1 c2) = (freeC c1) ++ (freeC c2)
freeC (PC p c1 c2) = (freeC c1) ++ (freeC c2)
freeC (IfTE_PC b c1 c2) = (freeB b) ++ (freeC c1) ++ (freeC c2)
freeC (WhDoPC b c) = (freeB b) ++ (freeC c)
freeC (ParalPC c1 c2) = (freeC c1) ++ (freeC c2)

validProb :: CpC -> Bool -- (validProb c) is True iff c does not contain any invalid probability value (valid ones are between 0 and 1)
validProb (SeqPC c1 c2) = (validProb c1) && (validProb c2)
validProb (PC p c1 c2) = if (p >= 0) && (p <= 1) then (validProb c1) && (validProb c2) else False
validProb (IfTE_PC b c1 c2) = (validProb c1) && (validProb c2)
validProb (WhDoPC b c) = validProb c
validProb (ParalPC c1 c2) = (validProb c1) && (validProb c2)
validProb c = True

removeZerosList :: [[ConfPC]] -> [[ConfPC]] -- (removeZerosList l) removes from l all the configurations with zero probability
removeZerosList l = map removeZeros l

removeZeros :: [ConfPC] -> [ConfPC] -- (removeZeros l) removes the elements of l with zero probability
removeZeros [] = []
removeZeros ((p,c,s):t) = if (p==0) then removeZeros t else (p,c,s):(removeZeros t)

-- (simplify l) removes from l the configurations with zero probability and joins the elements of each list of l with the same command and state
simplify :: [[ConfPC]] -> [[ConfPC]]
simplify l = map sumEquals (removeZerosList l)

sumEquals :: [ConfPC] -> [ConfPC] -- (sumEquals l) joins the elements of l with the same command and state, summing their probabilities into one probability
sumEquals [] = []
sumEquals l = sumEqualsAux [] l

-- Auxiliary to sumEquals: (sumEqualsAux l1 l2) adds the elements of l2 to l1, making sure each element of l1 remains with a different combination of command and state, if
-- they initially have different combinations
sumEqualsAux :: [ConfPC] -> [ConfPC] -> [ConfPC]
sumEqualsAux l [] = l
sumEqualsAux l (h:t) = sumEqualsAux (add h l) t

-- (add (p,c,s) l) adds p to the probability of the element of l with command c and state s, making sure each element (p',c',s') of l remains with a different (c',s'),
-- if they initially have different combinations of c' and s'.
-- If there is no element of l with command c and state s, then (p,c,s) is added to l.
add :: ConfPC -> [ConfPC] -> [ConfPC]
add (p,c,s) [] = [(p,c,s)]
add (p,c,s) ((p',c',s'):t) = if (c==c') && (s==s') then ((p+p', c', s'):t) else (p',c',s'):(add (p,c,s) t)
-- Note: function changeSt will not change the position of the identifiers in the state it receives, so there is no problem in state [a,b] being 
-- considered different from state [b,a], in this case. 

-- smallStepList c s = a list with the next configurations that <c,s> can transition to, in the form of [l1,l2,..,ln]
-- where li represents a probability distribution of configurations 

smallStepList :: CpC -> S -> [[ConfPC]]
smallStepList SkipPC s = [[(1, SkipPC, s)]] -- (in this case, there is no transition)
smallStepList (AsgPC i e) s = [[(1, SkipPC, changeSt i n s)]] where n= (bigStepExp e s)
smallStepList (SeqPC c1 c2) s = if (term c1 s) then [[(1, c2, s)]] else map (lastInSeqProb c2) (smallStepList c1 s)
smallStepList (PC p c1 c2) s = [[(p,c1,s), (1-p,c2,s)]]
smallStepList (IfTE_PC b c1 c2) s = if (bigStepBExp b s) then [[(1,c1,s)]] else [[(1,c2,s)]]
smallStepList (WhDoPC b c) s = [[(1, IfTE_PC b (SeqPC c (WhDoPC b c)) SkipPC, s)]]
smallStepList (ParalPC c1 c2) s
    | term (ParalPC c1 c2) s = [[(1, ParalPC c1 c2, s)]] -- (in this case, there is no transition)
    | term c1 s = map (paral c1) (smallStepList c2 s)
    | term c2 s = map (paral c2) (smallStepList c1 s)
    | otherwise = (map (paral c2) (smallStepList c1 s)) ++ (map (paral c1) (smallStepList c2 s))

term :: CpC -> S -> Bool -- term c s is true iff < c,s > term is provable
term SkipPC s = True
term (ParalPC c1 c2) s = (term c1 s) && (term c2 s)
term c s = False

lastInSeqProb :: CpC -> [ConfPC] -> [ConfPC] -- lastInSeqProb c' l turns each element (p,c,s) of l into (p, c;c', s)
lastInSeqProb c' [] = []
lastInSeqProb c' ((p,c,s):t) = (p, SeqPC c c', s): lastInSeqProb c' t

paral :: CpC -> [ConfPC] -> [ConfPC] -- paral c' l turns each element (p,c,s) of l into (p, c'||c, s)
paral c' [] = []
paral c' ((p,c,s):t) = (p, ParalPC c' c, s): paral c' t

-- Big-step semantics
-- (bigStepList c s) is a list with the different possibilities for the final probability distribution of configurations, when the initial configuration is <c,s> 
-- (bigStepList c s) has the form [d1,d2,..,dn], where di represents a probability distribution of configurations.
-- Every command in (bigStepList c s) is terminated.

bigStepList :: CpC -> S -> [[ConfPC]]
bigStepList SkipPC s = [[(1, SkipPC, s)]] -- (in this case, there is no transition)
bigStepList (AsgPC i e) s = [[(1, SkipPC, changeSt i n s)]]  where n= (bigStepExp e s) 
bigStepList (SeqPC c1 c2) s
    | term c1 s = bigStepList c2 s
    | otherwise = concat $ map bigStepD (beforeC2 c1 c2 s) -- list of possible (sum_j qj <cj_term,vj>) (see corresponding semantics rule)
bigStepList (PC p c1 c2) s = [ (mult p a) ++ (mult (1-p) b) | a <- (bigStepList c1 s), b <- (bigStepList c2 s)] -- list of all possible ( sum_j p pj <cj,vj> ) + ( sum_k (1-p) pk <ck,vk> ) (see corresponding semantic rule)
bigStepList (IfTE_PC b c1 c2) s = if (bigStepBExp b s) then bigStepList c1 s else bigStepList c2 s
bigStepList (WhDoPC b c) s = if (bigStepBExp b s) then (bigStepList (SeqPC c (WhDoPC b c)) s) else (bigStepList SkipPC s)
bigStepList (ParalPC c1 c2) s 
    | term (ParalPC c1 c2) s = [[(1, ParalPC c1 c2, s)]] -- in this case, there is no transition
    | otherwise = concat $ map bigStepD (smallStepList (ParalPC c1 c2) s)

mult :: Prob -> [ConfPC] -> [ConfPC] -- (mult p' confs) multiplies by p' all probabilities of all configurations in list confs
mult p [] = []
mult p' ((p,c,s) : t) = (p'*p, c, s) : (mult p' t)

-- bigStepD gives a list with different possibilities for the final probability distribution of configurations, given an initial probability distribution of configurations
bigStepD :: [ConfPC] -> [[ConfPC]]
bigStepD [] = [[]]
bigStepD ((p,c,s):t) = [ (mult p a) ++ b | a <- (bigStepList c s), b <- (bigStepD t) ]

beforeC2 :: CpC -> CpC -> S -> [[ConfPC]] -- beforeC2 c1 c2 s = list of all possible (sum_i pi <c2, vi>) (see definition of afterC1 below)
beforeC2 c1 c2 s = let afterC1 = bigStepList c1 s -- afterC1 = list of all possible (sum_i pi <ci_term,vi>)
                   in (map (replaceBy c2) afterC1)

replaceBy :: CpC -> [ConfPC] -> [ConfPC] -- replaceBy c' l replaces by c' each c in all elements (p,c,s) of l
replaceBy c [] = []
replaceBy c' ((p,c,s):t) = (p,c',s): replaceBy c' t

-- smallStep c s = the next configuration achieved from configuration <c,s>, through a transition, calculated using a scheduler
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in the case of ParalPC commands with non-terminated components
---- takes into account the probability of each possible next configuration, in case of PC commands

smallStep :: CpC -> S -> IO (CpC,S)
smallStep SkipPC s = return (SkipPC,s) -- (in this case, there is no transition)
smallStep (AsgPC i e) s = return (SkipPC, changeSt i n s) where n = (bigStepExp e s)
smallStep (SeqPC c1 c2) s = if (term c1 s) then (return (c2,s)) else do
    (c1',s') <- smallStep c1 s
    return (SeqPC c1' c2, s')
smallStep (PC p c1 c2) s =
    let dist = [(1, p),(2, 1-p)] -- probabilistic distribution (list of events and their corresponding probabilities) 
        event =  makeEventProb dist -- event corresponding to dist
    in do
       n <- enact event -- (enact event) simulates "event" and gives an outcome according to the probabilities in it
       return ( if (n==1) then (c1,s) else (c2,s) )
smallStep (IfTE_PC b c1 c2) s = if (bigStepBExp b s) then (return (c1,s)) else (return (c2,s))
smallStep (WhDoPC b c) s = return (IfTE_PC b (SeqPC c (WhDoPC b c)) SkipPC, s)
smallStep (ParalPC c1 c2) s
    | term (ParalPC c1 c2) s = return (ParalPC c1 c2, s) -- (in this case, there is no transition)
    | term c1 s = smallStep2nd c1 c2 s
    | term c2 s = smallStep1st c1 c2 s
    | otherwise = do
        x <- sched
        if (x==0) then (smallStep1st c1 c2 s) else (smallStep2nd c1 c2 s)

-- sched returns a pseudo-random number that is either 0 or 1
sched :: IO Int -- function also used in SemBrookes.hs (semantics of the basic parallel language)
sched = do
    g <- getStdGen -- g is the global pseudo-random number generator
    newStdGen -- updates the global pseudo-random number generator 
    return (fst (randomR (0,1) g)) -- (fst (randomR (0,1) g)) is a pseudo-random number between 0 and 1  

smallStep1st :: CpC -> CpC -> S -> IO (CpC,S) -- auxiliary to smallStep
smallStep1st c1 c2 s = do
    (c1', s') <- smallStep c1 s
    return (ParalPC c1' c2, s')

smallStep2nd :: CpC -> CpC -> S -> IO (CpC,S) -- auxiliary to smallStep
smallStep2nd c1 c2 s = do
    (c2', s') <- smallStep c2 s
    return (ParalPC c1 c2', s')

-- bigStep c s = the final configuration achieved from configuration <c,s>, calculated using a scheduler
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in the case of ParalPC commands with non-terminated components
---- takes into account the probability of each possible next configuration, in case of PC commands

bigStep :: CpC -> S -> IO (CpC,S)
bigStep SkipPC s = return (SkipPC,s) -- (in this case, there is no transition)
bigStep (AsgPC i e) s = return (SkipPC, changeSt i n s) where n= (bigStepExp e s)
bigStep (SeqPC c1 c2) s = if (term c1 s) then (bigStep c2 s) else do
    (c1',s') <- smallStep c1 s
    bigStep (SeqPC c1' c2) s'
bigStep (PC p c1 c2) s =
    let dist = [(1, p),(2, 1-p)] -- probabilistic distribution (list of events and their corresponding probabilities) 
        event =  makeEventProb dist -- event corresponding to dist
    in do
       n <- enact event -- (enact event) is a value that simulates "event" and gives an outcome according to the probabilities in it
       if (n==1) then (bigStep c1 s) else (bigStep c2 s)
bigStep (IfTE_PC b c1 c2) s = if (bigStepBExp b s) then (bigStep c1 s) else (bigStep c2 s)
bigStep (WhDoPC b c) s = if (bigStepBExp b s) then (bigStep (SeqPC c (WhDoPC b c)) s) else (bigStep SkipPC s)
bigStep (ParalPC c1 c2) s
    | term (ParalPC c1 c2) s = return (ParalPC c1 c2, s) -- (in this case, there is no transition)
    | term c1 s = bigStep2nd c1 c2 s
    | term c2 s = bigStep1st c1 c2 s
    | otherwise = do
        x <- sched
        if (x==0) then (bigStep1st c1 c2 s) else (bigStep2nd c1 c2 s)

bigStep1st :: CpC -> CpC -> S -> IO (CpC,S) -- auxiliary to bigStep 
bigStep1st c1 c2 s = do
    (c1',s') <- smallStep c1 s
    bigStep (ParalPC c1' c2) s'

bigStep2nd :: CpC -> CpC -> S -> IO (CpC,S) -- auxiliary to bigStep
bigStep2nd c1 c2 s = do
    (c2',s') <- smallStep c2 s
    bigStep (ParalPC c1 c2') s'



-------------------------------------------------------------------
--made from a copy of Semantics_prob.hs,  Semantics_probND.hs, SemBrookes.hs