-- Operational semantics of the basic parallel language (presented in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.) 
-- but with probabilistic choice instead of parallel commands:

-- C::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C


import Numeric.Probability.Game.Event -- import functions for nextStepSch
import SemBE_Brookes -- module created in SemBE_Brookes.hs
import GrammarBrookes -- module created in GrammarBrookes.hs

-- States
s1= [("a",1), ("b",2), ("c",3)]

-- DUVIDAS SOBRE O QUE FAZER A SEGUIR:
-- é preciso resolver o problema do Haskell? - SIM, mas menos prioritario

-- VER: problema do Haskell: 1-0.9 = 0.0999999999
-- quanto a este problema: rever https://stackoverflow.com/questions/33161504/how-to-calculate-floating-point-numbers-in-haskell
-- talvez o mais simples seja mesmo usar o tipo Rational do Prelude

-- Note that functions bigStep, nextStep, bigStepSch and nextStepSch are supposed to be used as arguments of applyBigStep, applyNextStep, applyBigStepSch 
-- and applyNextStepSch, respectively, which are responsible for checking if all identifiers in the given command are declared in the given state, and 
-- if all probability values in the command are valid.

-- (errorSem c s) is an error message telling that not all free identifiers in c are part of state s and/or not all probabilities in c are valid.
errorSem :: Cp -> S -> String 
errorSem c s = "Not all free identifiers in "++(show c)++" are part of state "++(show s)++" AND/OR not all probabilities in "++(show c)++" are valid."

-- (applyNextStep c s) is the result of applying function nextStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyNextStep :: Cp -> S ->  [ConfP] 
applyNextStep c s = if (belong (freeCp c) s) && (validProb c) then removeZeros (nextStep c s) else error (errorSem c s) 

-- (applyBigStep c s) is the result of applying function bigStep to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStep :: Cp -> S ->  [ConfP] 
applyBigStep c s = if (belong (freeCp c) s) && (validProb c) then simplify (bigStep c s) else error (errorSem c s)

-- (applyNextStepSch c s) is the result of applying function nextStepSch to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyNextStepSch :: Cp -> S -> IO (Cp,S) 
applyNextStepSch c s = if (belong (freeCp c) s) && (validProb c) then nextStepSch c s else error (errorSem c s)

-- (applyBigStepSch c s) is the result of applying function bigStepSch to c and s, if s is defined on all the free identifiers of c and
-- there are no invalid probability values in c
applyBigStepSch :: Cp -> S -> IO (Cp,S) 
applyBigStepSch c s = if (belong (freeCp c) s) && (validProb c) then bigStepSch c s else error (errorSem c s)

freeCp :: Cp -> [String] -- (freeCp c) is the set of free identifiers in c
freeCp SkipP = []
freeCp (AsgP i e) = i : (freeE e)
freeCp (SeqP c1 c2) = (freeCp c1) ++ (freeCp c2)
freeCp (P p c1 c2) = (freeCp c1) ++ (freeCp c2)
freeCp (IfTE_P b c1 c2) = (freeB b) ++ (freeCp c1) ++ (freeCp c2)
freeCp (WhDoP b c) = (freeB b) ++ (freeCp c) 

validProb :: Cp -> Bool -- (validProb c) is True iff c does not contain any invalid probability value (valid ones are between 0 and 1)
validProb (SeqP c1 c2) = (validProb c1) && (validProb c2)
validProb (P p c1 c2) = if (p >= 0) && (p <= 1) then (validProb c1) && (validProb c2) else False
validProb (IfTE_P b c1 c2) = (validProb c1) && (validProb c2)
validProb (WhDoP b c) = validProb c
validProb c = True

removeZeros :: [ConfP] -> [ConfP] -- (removeZeros l) removes the elements of l with zero probability.
removeZeros [] = []
removeZeros ((p,c,s):t) = if (p==0) then removeZeros t else (p,c,s):(removeZeros t)

simplify :: [ConfP] -> [ConfP] -- (simplify l) removes the elements of l with zero probability and then joins the elements of l with the same state
simplify l = sumEquals (removeZeros l)

sumEquals :: [ConfP] -> [ConfP] -- (sumEquals l) joins the elements of l with the same state, summing their probabilities into one probability
sumEquals [] = []
sumEquals l = sumEqualsAux [] l

-- Auxiliary to sumEquals: (sumEqualsAux l1 l2) adds the elements of l2 to l1, making sure each element of l1 has a different state -- REVER COMMENT
sumEqualsAux :: [ConfP] -> [ConfP] -> [ConfP]
sumEqualsAux l [] = l
sumEqualsAux l (h:t) = sumEqualsAux (add h l) t

-- VER se tiro esta função inList.
--inList :: ConfP -> [ConfP] -> Bool -- (inList (p,c,s) l) is True iff there is an element (p',c',s') of l such that s=s'  
--inList c [] = False
--inList (p,c,s) ((p',c',s'):t) = if (s'==s) then True else inList (p,c,s) t

-- (add (p,c,s) l) adds p to the probability of the element of l with state s, making sure each element (p',c',s') of l remains with a different s'.
-- If there is no element of l with state s, then (p,c,s) is added to l. -- REVER COMMENT

add :: ConfP -> [ConfP] -> [ConfP]
add (p,c,s) [] = [(p,c,s)]
add (p,c,s) ((p',c',s'):t) = if (s==s') then ((p+p', c', s'):t) else (p',c',s'):(add (p,c,s) t)
-- Note: function changeSt will not change the position of the identifiers in the state it receives, so there is no problem in state [a,b] being 
-- considered different from state [b,a], in this case. 

-- (nextStep c s) is the probability distribution of configurations that can be achieved from configuration <c,s>, through a transition

nextStep :: Cp -> S -> [ConfP]
nextStep SkipP s = [(1, SkipP, s)] -- 1st rule (in this case, there is no transition)
nextStep (AsgP i e) s = [(1, SkipP, changeSt i n s)] where n= (bigStepExp e s) -- 2nd rule
nextStep (SeqP c1 c2) s = if (term c1 s) then [(1, c2, s)] else map (lastInSeqProb c2) (nextStep c1 s) -- 3rd and 4th rules
nextStep (P p c1 c2) s = [(p,c1,s), (1-p,c2,s)] -- new rule
nextStep (IfTE_P b c1 c2) s = if (bigStepBExp b s) then [(1,c1,s)] else [(1,c2,s)] -- 5th and 6th rules
nextStep (WhDoP b c) s = [(1, IfTE_P b (SeqP c (WhDoP b c)) SkipP, s)] -- 7th rule

term :: Cp -> S -> Bool -- term c s is true iff < c,s > term is provable
term SkipP s = True
term c s = False

lastInSeqProb :: Cp -> ConfP -> ConfP -- lastInSeqProb c' (p,c,s) represents the configuration (p, c;c', s)
lastInSeqProb c' (p,c,s) = (p, SeqP c c', s)

bigStepD :: [ConfP] -> [ConfP] -- bigStepD gives the final configuration given an initial probability distribution of configurations 
bigStepD [] = []
bigStepD ((p,c,s):t) = mult p (bigStep c s) ++ bigStepD t

mult :: Prob -> [ConfP] -> [ConfP] -- (mult p' confs) multiplies by p' all probabilities of all configurations in list confs
mult p [] = []
mult p' ((p,c,s) : t) = (p'*p, c, s) : (mult p' t)

beforeC2 :: Cp -> Cp -> S -> [ConfP] -- beforeC2 c1 c2 s = sum_i pi <c2, vi> (see definition of afterC1 below)
beforeC2 c1 c2 s = let afterC1 = bigStep c1 s -- afterC1 = sum_i pi <skip,vi>
                   in (map (replaceBy c2) afterC1)

replaceBy :: Cp -> ConfP -> ConfP -- replaceBy c' (p,c,s) replaces c by c'
replaceBy c' (p,c,s) = (p,c',s)

-- Big-step semantics
-- (bigStep c s) is the final probability distribution of configurations that can be achieved from configuration <c,s>
-- Every command in (bigStep c s) is Skip.

bigStep :: Cp -> S -> [ConfP] 
bigStep SkipP s = [(1, SkipP, s)] -- (in this case, there is no transition)
bigStep (AsgP i e) s = [(1, SkipP, changeSt i n s)]  where n= (bigStepExp e s) -- bigStepD (nextStep (AsgP i e) s) 
bigStep (SeqP c1 c2) s
    | term c1 s = bigStep c2 s -- bigStepD ([1,c2,s])
    | otherwise = bigStepD (beforeC2 c1 c2 s) -- sum_j qj <skip,vj> (see corresponding semantics rule)
bigStep (P p c1 c2) s = mult p (bigStep c1 s) ++ mult (1-p) (bigStep c2 s) -- ( sum_j p pj <cj,vj> ) + ( sum_k (1-p) pk <ck,vk> ) (see corresponding semantic rule)
bigStep (IfTE_P b c1 c2) s = if (bigStepBExp b s) then bigStep c1 s else bigStep c2 s
bigStep (WhDoP b c) s = if (bigStepBExp b s) then (bigStep (SeqP c (WhDoP b c)) s) else (bigStep SkipP s)

-- Using a SCHEDULER:

-- (nextStepSch c s) is the next configuration achieved from configuration <c,s>, through a transition, calculated using a scheduler
-- that takes into account the probability of each possible next configuration 

nextStepSch :: Cp -> S -> IO (Cp,S)
nextStepSch c s = 
    let confs = applyNextStep c s -- confs is the probability distribution of configurations obtained from <c,s>
        dist = toDist confs 1 -- probabilistic distribution (list of events and their corresponding probabilities)
        event = makeEventProb dist -- event corresponding to dist (value of type EventM Int)
    in do
        n <- enact event -- (enact event) is a value of type IO Int that simulates "event" and gives an outcome according to the probabilities in it
        return (index confs n)

-- (bigStepSch c s) is the final configuration achieved from configuration <c,s>, calculated using a scheduler
-- that takes into account the probability of each possible final configuration 

bigStepSch :: Cp -> S -> IO (Cp,S)
bigStepSch c s =
    let confs = applyBigStep c s -- confs is the final probability distribution of configurations obtained from <c,s>
        dist = toDist confs 1 -- probabilistic distribution (list of events and their corresponding probabilities)
        event = makeEventProb dist -- event corresponding to dist (value of type EventM Int)
    in do
        n <- enact event -- (enact event) is a value of type IO Int that simulates "event" and gives an outcome according to the probabilities in it
        return (index confs n)

toDist :: [ConfP] -> Int -> [(Int,Prob)] -- (toDist l 1) turns an l of the form [(p1,c1,s1),...,(pn,cn,sn)] into a list of the form [(1,p1),...,(n,pn)] 
toDist [] n = []
toDist ((p,c,s):t) n = (n,p) : (toDist t (n+1))

index :: [ConfP] -> Int -> (Cp,S) -- (index confs n) is the configuration corresponding to the n-th element of confs 
index [] n = error "Function index cannot receive an empty list."
index ((p,c,s):t) n
    | (n<=0) = error "Function index is meant to receive a value of type Int larger or equal to 1."
    | (n==1) = (c,s)
    | otherwise = index t (n-1)

-------------------------------------------------------------------
--useful links:
-- https://hackage.haskell.org