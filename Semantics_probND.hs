-- Operational semantics of the basic parallel language (presented in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.) 
-- but with probabilistic choice instead of parallel commands, and with non-determinism (ND + Prob):

-- C::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C | C1 or C2

import SemBE_Brookes -- module created in SemBE_Brookes.hs
import GrammarBrookes -- module created in GrammarBrookes.hs
import System.Random -- library that deals with pseudo-random number generation
import Numeric.Probability.Game.Event -- import functions for smallStep and bigStep

-- States
s1= [("a",1), ("b",2), ("c",3)]

-- DUVIDAS SOBRE O QUE FAZER A SEGUIR:
-- é preciso resolver o problema do Haskell? SIM, mas menos prioritario

-- VER: problema do Haskell: 1-0.9 = 0.0999999999 (ver notas no Semantics_prob.hs)

-- Note that functions bigStepList, smallStepList, bigStep and smallStep are supposed to be used as arguments of applyBigStep, applyNextStep, 
-- applyBigStepSch and applyNextStepSch, respectively,
-- which are responsible for checking if all identifiers in the given command are declared in the given state, and if all probability values
-- in the command are valid.

-- (errorSem c s) is an error message telling that not all free identifiers in c are part of state s and/or not all probabilities in c are valid.
errorSem :: Cpnd -> S -> String 
errorSem c s = "Not all free identifiers in "++(show c)++" are part of state "++(show s)++" AND/OR not all probabilities in "++(show c)++" are valid."

-- (applyNextStep c s) is the result of applying function smallStepList to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyNextStep :: Cpnd -> S -> [[ConfPND]]
applyNextStep c s = if (belong (freeC c) s) && (validProb c) then removeZerosList (smallStepList c s) else error (errorSem c s)

-- (applyBigStep c s) is the result of applying function bigStepList to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStep :: Cpnd -> S ->  [[ConfPND]] 
applyBigStep c s = if (belong (freeC c) s) && (validProb c) then simplify (bigStepList c s) else error (errorSem c s)

-- (applyNextStepSch c s) is the result of applying function smallStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyNextStepSch :: Cpnd -> S -> IO (Cpnd,S)
applyNextStepSch c s = if (belong (freeC c) s) && (validProb c) then smallStep c s else error (errorSem c s) 

-- (applyBigStepSch c s) is the result of applying function bigStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStepSch :: Cpnd -> S ->  IO (Cpnd,S)
applyBigStepSch c s = if (belong (freeC c) s) && (validProb c) then bigStep c s else error (errorSem c s)

freeC :: Cpnd -> [String] -- (freeC c) is the set of free identifiers in c
freeC SkipPND = []
freeC (AsgPND i e) = i : (freeE e)
freeC (SeqPND c1 c2) = (freeC c1) ++ (freeC c2)
freeC (PND p c1 c2) = (freeC c1) ++ (freeC c2)
freeC (IfTE_PND b c1 c2) = (freeB b) ++ (freeC c1) ++ (freeC c2)
freeC (WhDoPND b c) = (freeB b) ++ (freeC c) 
freeC (Or c1 c2) = (freeC c1) ++ (freeC c2)

validProb :: Cpnd -> Bool -- (validProb c) is True iff c does not contain any invalid probability value (valid ones are between 0 and 1)
validProb (SeqPND c1 c2) = (validProb c1) && (validProb c2)
validProb (PND p c1 c2) = if (p >= 0) && (p <= 1) then (validProb c1) && (validProb c2) else False
validProb (IfTE_PND b c1 c2) = (validProb c1) && (validProb c2)
validProb (WhDoPND b c) = validProb c
validProb (Or c1 c2) = (validProb c1) && (validProb c2) 
validProb c = True

removeZerosList :: [[ConfPND]] -> [[ConfPND]] -- (removeZerosList l) removes from l all the configurations with zero probability  
removeZerosList l = map removeZeros l

removeZeros :: [ConfPND] -> [ConfPND] -- (removeZeros l) removes the elements of l with zero probability
removeZeros [] = []
removeZeros ((p,c,s):t) = if (p==0) then removeZeros t else (p,c,s):(removeZeros t)

simplify :: [[ConfPND]] -> [[ConfPND]] -- (simplify l) removes from l the configurations with zero probability and joins the elements of each list of l with the same state
simplify l = map sumEquals (removeZerosList l)

sumEquals :: [ConfPND] -> [ConfPND] -- (sumEquals l) joins the elements of l with the same state, summing their probabilities into one probability
sumEquals [] = []
sumEquals l = sumEqualsAux [] l

-- Auxiliary to sumEquals: (sumEqualsAux l1 l2) adds the elements of l2 to l1, making sure each element of l1 has a different state -- REVER COMMENT
sumEqualsAux :: [ConfPND] -> [ConfPND] -> [ConfPND]
sumEqualsAux l [] = l
sumEqualsAux l (h:t) = sumEqualsAux (add h l) t

-- VER se tiro esta função inList
--inList :: ConfPND -> [ConfPND] -> Bool -- (inList (p,c,s) l) is True iff there is an element (p',c',s') of l such that c=c' and s=s'  
--inList c [] = False
--inList (p,c,s) ((p',c',s'):t) = if (c'==c) && (s'==s) then True else inList (p,c,s) t

-- (add (p,c,s) l) adds p to the probability of the element of l with state s, making sure each element (p',c',s') of l remains with a different s'.
-- If there is no element of l with state s, then (p,c,s) is added to l. -- REVER COMMENT
add :: ConfPND -> [ConfPND] -> [ConfPND]
add (p,c,s) [] = [(p,c,s)]
add (p,c,s) ((p',c',s'):t) = if (s==s') then ((p+p', c', s'):t) else (p',c',s'):(add (p,c,s) t)
-- Note: function changeSt will not change the position of the identifiers in the state it receives, so there is no problem in state [a,b] being 
-- considered different from state [b,a], in this case. 

-- smallStepList c s = a ĺist with the different possibilities for the next configuration that <c,s> can transition to, in the form of [l1,l2,..,ln]
-- where li represents a probability distribution of configurations

smallStepList :: Cpnd -> S -> [[ConfPND]]
smallStepList SkipPND s = [ [(1, SkipPND, s)] ] -- in this case, there is no transition
smallStepList (AsgPND i e) s = [ [(1, SkipPND, changeSt i n s)] ] where n = (bigStepExp e s)
smallStepList (SeqPND c1 c2) s = if (term c1 s) then [ [(1, c2, s)] ] else map (lastInSeqProb c2) (smallStepList c1 s)
smallStepList (PND p c1 c2) s = [ [(p,c1,s), (1-p,c2,s)] ]
smallStepList (IfTE_PND b c1 c2) s = if (bigStepBExp b s) then [ [(1,c1,s)] ] else [ [(1,c2,s)] ]
smallStepList (WhDoPND b c) s = [ [(1, IfTE_PND b (SeqPND c (WhDoPND b c)) SkipPND, s)] ]
smallStepList (Or c1 c2) s = (smallStepList c1 s) ++ (smallStepList c2 s) -- new rule

-- smallStep c s = the next configuration achieved from configuration <c,s>, through a transition, calculated using a scheduler
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in case of Or commands
---- takes into account the probability of each possible next configuration, in case of PND commands

smallStep :: Cpnd -> S -> IO (Cpnd,S)
smallStep SkipPND s = return (SkipPND,s)
smallStep (AsgPND i e) s = return (SkipPND, changeSt i n s) where n = (bigStepExp e s)
smallStep (SeqPND c1 c2) s = if (term c1 s) then (return (c2,s)) else do
    (c1',s') <- smallStep c1 s
    return (SeqPND c1' c2, s')
smallStep (PND p c1 c2) s = 
    let dist = [(1, p),(2, 1-p)] -- probabilistic distribution (list of events and their corresponding probabilities) 
        event =  makeEventProb dist -- event corresponding to dist
    in do
       n <- enact event -- (enact event) is a value that simulates "event" and gives an outcome according to the probabilities in it
       return ( if (n==1) then (c1,s) else (c2,s) )
smallStep (IfTE_PND b c1 c2) s = if (bigStepBExp b s) then (return (c1,s)) else (return (c2,s))
smallStep (WhDoPND b c) s = return (IfTE_PND b (SeqPND c (WhDoPND b c)) SkipPND, s)
smallStep (Or c1 c2) s = do
    x <- sched
    if (x==0) then (smallStep c1 s) else (smallStep c2 s)

-- sched returns a pseudo-random number that is either 0 or 1
sched :: IO Int -- function also used in Semantics_lingSimpl.hs (semantics of the basic parallel language)
sched = do
    g <- getStdGen -- g is the global pseudo-random number generator
    newStdGen -- updates the global pseudo-random number generator 
    return (fst (randomR (0,1) g)) -- (fst (randomR (0,1) g)) is a pseudo-random number between 0 and 1  

term :: Cpnd -> S -> Bool -- term c s is true iff < c,s > term is provable
term SkipPND s = True
term c s = False

lastInSeqProb :: Cpnd -> [ConfPND] -> [ConfPND] -- lastInSeqProb c' l turns each element (p,c,s) of l into (p, c;c', s)
lastInSeqProb c' [] = []
lastInSeqProb c' ((p,c,s):t) = (p, SeqPND c c', s): lastInSeqProb c' t

-- bigStepD gives a list with the different possibilities for the final probability distribution of configurations,
-- given an initial probability distribution of configurations
bigStepD :: [ConfPND] -> [[ConfPND]]
bigStepD [] = [[]]
bigStepD ((p,c,s):t) = [ (mult p a) ++ b | a <- (bigStepList c s), b <- (bigStepD t) ]

mult :: Prob -> [ConfPND] -> [ConfPND] -- (mult p' confs) multiplies by p' all probabilities of all configurations in list confs
mult p [] = []
mult p' ((p,c,s) : t) = (p'*p, c, s) : (mult p' t)

-- Big-step semantics for commands
-- bigStepList c s = a ĺist with the different possibilities for the final probability distribution of configurations, when the initial configuration is <c,s>
-- (bigStepList c s) has the form [l1,l2,..,ln], where li represents a probability distribution of configurations.
-- Every command in (bigStepList c s) is Skip.

bigStepList :: Cpnd -> S -> [[ConfPND]]
bigStepList SkipPND s = [ [(1, SkipPND, s)] ] -- (in this case, there is no transition)
bigStepList (AsgPND i e) s = [ [(1, SkipPND, changeSt i n s)] ]  where n = (bigStepExp e s) 
bigStepList (SeqPND c1 c2) s
    | term c1 s = bigStepList c2 s
    | otherwise = concat $ map bigStepD (beforeC2 c1 c2 s) -- list of possible (sum_j qj <skip,vj>) (see corresponding semantics rule)
bigStepList (PND p c1 c2) s = [ (mult p a) ++ (mult (1-p) b) | a <- (bigStepList c1 s), b <- (bigStepList c2 s)] -- list of all possible ( sum_j p pj <cj,vj> ) + ( sum_k (1-p) pk <ck,vk> ) (see corresponding semantic rule)
bigStepList (IfTE_PND b c1 c2) s = if (bigStepBExp b s) then bigStepList c1 s else bigStepList c2 s
bigStepList (WhDoPND b c) s = if (bigStepBExp b s) then (bigStepList (SeqPND c (WhDoPND b c)) s) else (bigStepList SkipPND s)
bigStepList (Or c1 c2) s = (bigStepList c1 s) ++ (bigStepList c2 s)

-- bigStep c s = the final configuration achieved from configuration <c,s>, calculated using a scheduler
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in case of Or commands
---- takes into account the probability of each possible next configuration, in case of PND commands

bigStep :: Cpnd -> S -> IO (Cpnd,S)
bigStep SkipPND s = return (SkipPND,s)
bigStep (AsgPND i e) s = return (SkipPND, changeSt i n s) where n= (bigStepExp e s)
bigStep (SeqPND c1 c2) s = if (term c1 s) then (bigStep c2 s) else do
    (c1',s') <- smallStep c1 s
    bigStep (SeqPND c1' c2) s'
bigStep (PND p c1 c2) s = 
    let dist = [(1, p),(2, 1-p)] -- probabilistic distribution (list of events and their corresponding probabilities) 
        event =  makeEventProb dist -- event corresponding to dist
    in do
       n <- enact event -- (enact event) is a value that simulates "event" and gives an outcome according to the probabilities in it
       if (n==1) then (bigStep c1 s) else (bigStep c2 s)
bigStep (IfTE_PND b c1 c2) s = if (bigStepBExp b s) then (bigStep c1 s) else (bigStep c2 s)
bigStep (WhDoPND b c) s = if (bigStepBExp b s) then (bigStep (SeqPND c (WhDoPND b c)) s) else (bigStep SkipPND s)
bigStep (Or c1 c2) s = do
    x <- sched
    if (x==0) then (bigStep c1 s) else (bigStep c2 s)

beforeC2 :: Cpnd -> Cpnd -> S -> [[ConfPND]] -- beforeC2 c1 c2 s = list of all possible (sum_i pi <c2, vi>) (see definition of afterC1 below)
beforeC2 c1 c2 s = let afterC1 = bigStepList c1 s -- afterC1 = list of all possible (sum_i pi <skip,vi>)
                   in (map (replaceBy c2) afterC1)

replaceBy :: Cpnd -> [ConfPND] -> [ConfPND] -- replaceBy c' l replaces by c' each c in all elements (p,c,s) of l
replaceBy c [] = []
replaceBy c' ((p,c,s):t) = (p,c',s): replaceBy c' t

------------------------------------------------------------
-- useful links: http://learnyouahaskell.com; https://hackage.haskell.org
-- made from a copy of Semantics_prob.hs