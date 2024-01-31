-- Operational semantics of the basic parallel language (presented in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.
-- NOTA PARA MIM: a função smallStepList, smallStep, freeC, freeB, freeE, bigStepList, a bigStepExp, a bigStepBExp, a bigStep, bigStepListToFile, bigStepToFile e histogramSmallStep já foram testadas e parecem funcionar bem.

module SemBrookes where

import GrammarBrookes -- module created in GrammarBrookes.hs
import SemBE_Brookes -- module created in SemBE_Brookes.hs
import ParserBrookes -- module created in ParserBrookes.hs
import ParserBE_Brookes -- module created in ParserBE_Brookes.hs
import System.Random -- library that deals with pseudo-random number generation
import HistogramSem -- module created in HistogramSem.hs
import System.Exit -- in order to get type ExitCode

--data C = Skip | Asg String E | Seq C C | Paral C C | IfTE_C B C C | WhDo B C

-- States
s1= [("a",1), ("b",2), ("c",3)]

-- (bigStepSchToStr str s) returns the result of bigStep for the command corresponding to str and for state s
bigStepSchToStr :: String -> S -> IO (C,S)
bigStepSchToStr str s = applySem bigStep c s
    where c = eitherToT (parseInputC str)

-- (bigStepToFile f s) returns the result of bigStep for the command in file f and for state s
bigStepToFile :: FilePath -> S -> IO (C,S)
bigStepToFile f s = do
    program <- readFile f -- "program" is a String containing the command in f
    bigStepSchToStr program s

-- (bigStepToStr str s) returns the result of bigStepList for the command corresponding to str and for state s
bigStepToStr :: String -> S -> [(C, S)]
bigStepToStr str s = applySem bigStepList c s
    where c = eitherToT (parseInputC str)

-- (bigStepListToFile f s) returns the result of bigStepList for the command in file f and for state s
bigStepListToFile :: FilePath -> S -> IO [(C,S)]
bigStepListToFile f s = do
    program <- readFile f -- "program" is a String containing the command in f
    return (bigStepToStr program s)

applySem :: (C -> S -> a) -> C -> S ->  a -- (applySem f c s) is the result of applying function f to c and s, if s is defined on all the free identifiers of c 
applySem f c s = if (belong (freeC c) s) then (f c s) else error ("Not all free identifiers in "++(show c)++" are part of state "++(show s)) 

freeC :: C -> [String] -- (freeC c) is the set of free identifiers in c (see page 146 of the article) 
freeC Skip = []
freeC (Asg i e) = i : (freeE e)
freeC (Seq c1 c2) = (freeC c1) ++ (freeC c2)
freeC (IfTE_C b c1 c2) = (freeB b) ++ (freeC c1) ++ (freeC c2)
freeC (WhDo b c) = (freeB b) ++ (freeC c)
freeC (Paral c1 c2) = (freeC c1) ++ (freeC c2) 

term :: C -> S -> Bool -- term c s is true iff < c,s > term is provable
term Skip s = True
term (Paral c1 c2) s = (term c1 s) && (term c2 s)
term c s = False

-- Note that functions bigStepList, bigStep, smallStepList and smallStep are supposed to be used as arguments of applySem, which is responsible
-- for checking if all identifiers in the given command are declared in the given state 

-- Big-step semantics for commands
-- bigStepList c s = a ĺist with the different possibilities for the final configurations that <c,s> can transition to
bigStepList :: C -> S -> [(C, S)]
bigStepList Skip s = [(Skip,s)] -- 1st rule (in this case, there is no transition)
bigStepList (Asg i e) s = [(Skip, (changeSt i n s) )] where n = (bigStepExp e s) -- 2nd rule
bigStepList (Seq c1 c2) s =  if (term c1 s) then (bigStepList c2 s) else leaves c2 (bigStepList c1 s) -- 3rd and 4th rules
bigStepList (IfTE_C b c1 c2) s = if (bigStepBExp b s) then (bigStepList c1 s) else bigStepList c2 s -- 5th and 6th rules
bigStepList (WhDo b c) s = if (bigStepBExp b s) then (bigStepList (Seq c (WhDo b c)) s) else (bigStepList Skip s) -- 7th rule
bigStepList (Paral c1 c2) s 
    | term (Paral c1 c2) s = [(Paral c1 c2, s)] -- in this case, there is no transition
    | term c1 s = concat (map (paralBigStep c1) (smallStepList c2 s))
    | term c2 s = concat (map (paralBigStep c2) (smallStepList c1 s))
    | otherwise = concat (map (paralBigStep c2) (smallStepList c1 s)) ++ concat (map (paralBigStep c1) (smallStepList c2 s)) -- 8th, 9th and 10th rules

-- Big-step semantics for commands with scheduler
-- bigStep c s = the final configuration that <c,s> transitions to, calculated using a scheduler
-- This scheduler resolves non-determinism by choosing randomly between the two possible transitions, in case of a parallel composition of non-terminated commands
bigStep :: C -> S -> IO (C,S)
bigStep Skip s = return (Skip,s) -- 1st rule (in this case, there is no transition)
bigStep (Asg i e) s = return (Skip, (changeSt i n s) ) where n = (bigStepExp e s) -- 2nd rule
bigStep (Seq c1 c2) s = if (term c1 s) then (bigStep c2 s) else do
    (c1',s') <- smallStep c1 s
    bigStep (Seq c1' c2) s'
bigStep (IfTE_C b c1 c2) s = if (bigStepBExp b s) then (bigStep c1 s) else bigStep c2 s -- 5th and 6th rules
bigStep (WhDo b c) s = if (bigStepBExp b s) then (bigStep (Seq c (WhDo b c)) s) else (bigStep Skip s) -- 7th rule
bigStep (Paral c1 c2) s
    | term (Paral c1 c2) s = return (Paral c1 c2, s) -- in this case, there is no transition
    | term c1 s = do
        (c2',s') <- smallStep c2 s
        bigStep (Paral c1 c2') s'
    | term c2 s = do
        (c1',s') <- smallStep c1 s
        bigStep (Paral c1' c2) s'
    | otherwise = do
        x <- sched
        if (x==0) then (bigStep1st c1 c2 s) else (bigStep2nd c1 c2 s)

-- sched returns a pseudo-random number that is either 0 or 1
sched :: IO Int
sched = do
    g <- getStdGen -- g is the global pseudo-random number generator
    newStdGen -- updates the global pseudo-random number generator 
    return (fst (randomR (0,1) g)) -- (fst (randomR (0,1) g)) is a pseudo-random number between 0 and 1  

paralBigStep :: C -> (C,S) -> [(C,S)] -- paralBigStep c2 (c1', s1') is a list with all the possible final configurations when the current configuration is < Paral c1' c2, s1' >
paralBigStep c (c',s') = bigStepList (Paral c' c) s'

leaves :: C -> [(C,S)] -> [(C,S)] -- leaves c roots is the list of the possible final configurations when c is the next command and roots is the list of possible current configurations 
leaves c roots = concat (map (bigStepList c) rootStates)
    where rootStates = map snd roots

bigStep1st :: C -> C -> S -> IO (C,S) -- auxiliary to bigStep
bigStep1st c1 c2 s = do
    (c1', s') <- smallStep c1 s
    bigStep (Paral c1' c2) s'

bigStep2nd :: C -> C -> S -> IO (C,S) -- auxiliary to bigStep
bigStep2nd c1 c2 s = do
    (c2', s') <- smallStep c2 s
    bigStep (Paral c1 c2') s'

-- smallStepList c s is the list of configurations that can be achieved from configuration <c,s>, through a transition
smallStepList :: C -> S -> [(C,S)] 
smallStepList Skip s = [(Skip,s)] -- 1st rule (in this case, there is no transition)
smallStepList (Asg i e) s = [(Skip, (changeSt i n s))] where n = (bigStepExp e s) -- 2nd rule
smallStepList (Seq c1 c2) s = if (term c1 s) then [(c2,s)] else (map (lastInSeq c2) (smallStepList c1 s)) -- 3rd and 4th rules
smallStepList (IfTE_C b c1 c2) s = if (bigStepBExp b s) then [(c1,s)] else [(c2,s)] -- 5th and 6th rules
smallStepList (WhDo b c) s = [(IfTE_C b (Seq c (WhDo b c)) Skip, s)] -- 7th rule
smallStepList (Paral c1 c2) s
    | term (Paral c1 c2) s = [(Paral c1 c2, s)] -- in this case, there is no transition
    | term c1 s = map (paral c1) (smallStepList c2 s)
    | term c2 s = map (paral c2) (smallStepList c1 s)
    | otherwise = (map (paral c2) (smallStepList c1 s)) ++ (map (paral c1) (smallStepList c2 s)) -- 8th, 9th and 10th rules

-- (smallStep c s) is the next configuration achieved from configuration <c,s>, through a transition, calculated using a scheduler
-- This scheduler resolves non-determinism by choosing randomly between the two possible transitions, in case of a parallel composition of non-terminated commands
smallStep :: C -> S -> IO (C,S)
smallStep Skip s = return (Skip,s) -- in this case, there is no transition
smallStep (Asg i e) s = return (Skip, (changeSt i n s) ) where n = (bigStepExp e s)
smallStep (Seq c1 c2) s =  if (term c1 s) then (return (c2,s)) else do
    (c1',s') <- smallStep c1 s
    return (Seq c1' c2, s')
smallStep (IfTE_C b c1 c2) s = if (bigStepBExp b s) then (return (c1, s)) else (return (c2, s))
smallStep (WhDo b c) s = return (IfTE_C b (Seq c (WhDo b c)) Skip, s)
smallStep (Paral c1 c2) s
    | term (Paral c1 c2) s = return (Paral c1 c2, s) -- in this case, there is no transition
    | term c1 s = smallStep2nd c1 c2 s
    | term c2 s = smallStep1st c1 c2 s
    | otherwise = do
        x <- sched
        if (x==0) then (smallStep1st c1 c2 s) else (smallStep2nd c1 c2 s) 

smallStep1st :: C -> C -> S -> IO (C,S) -- auxiliary to smallStep
smallStep1st c1 c2 s = do
    (c1', s') <- smallStep c1 s
    return (Paral c1' c2, s')

smallStep2nd :: C -> C -> S -> IO (C,S) -- auxiliary to smallStep
smallStep2nd c1 c2 s = do
    (c2', s') <- smallStep c2 s
    return (Paral c1 c2', s')

lastInSeq :: C -> (C,S) -> (C,S) -- lastInSeq c' (c,s) represents the configuration < Seq c c', s >
lastInSeq c' (c,s) = (Seq c c', s)

paral :: C -> (C,S) -> (C,S) -- paral c (c',s') represents the configuration < Paral c c', s' >
paral c (c',s') = (Paral c c', s')

experiencia :: C -> S -> IO ((C,S),(C,S),(C,S)) -- experiencia: vê se que a, b e c nao sao sempre iguais, nem têm de ser iguais entre si
experiencia c s = do
    a <- smallStep c s
    b <- smallStep c s
    c <- smallStep c s
    return (a,b,c)

---- Functions for building an histogram with the results of the semantics obtained using a scheduler:

-- (histogramSmallStep n c s) plots an histogram whose input is a list with n results of (smallStep c s) (if s is defined on all free identifiers of c), 
-- where each different configuration in the results has a label of the form "<conf x>", where x is an integer.
-- The configuration corresponding to each label is shown in a caption printed on the terminal.

histogramSmallStep :: Int -> C -> S -> IO ExitCode
histogramSmallStep n c s = do
    l <- listSmallStep n c s
    putStrLn "-------------------------------------------\n"
    putStrLn "Histogram Caption:"
    putStrLn ""
    caption 1 (diffResults l)
    putStrLn "-------------------------------------------"
    histogramInt (confIntoDouble l) "Results of the small-step semantics"

-- (listSmallStep n c s) returns a list with n results of (smallStep c s), but only if s is defined on all the free identifiers of c
listSmallStep :: Int -> C -> S -> IO [(C,S)]
listSmallStep 0 c s = return []
listSmallStep n c s = do
    a <- applySem smallStep c s
    as <- listSmallStep (n-1) c s
    return (a:as)

-- caption n [c1,...,cx] prints on the terminal a caption whose i-th line is "< conf (n+i-1) > : ci", with its last line being "< conf (n+x-1) > : cx"  
caption :: Int -> [(C,S)] -> IO ()
caption n [] = putStrLn ""
caption n (h:t) = do
    putStrLn ("<conf "++(show n)++"> : "++(show h))
    caption (n+1) t

-- (diffResults l) is the list obtained from removing from l all the repeated elements
-- e.g. diffResults [c1,c2,c2,c1] = [c1,c2]
diffResults :: [(C,S)] -> [(C,S)] 
diffResults [] = []
diffResults l = diffResultsAux [] l

-- (diffResultsAux l1 l2) is the list that results from adding to l1 the elements of l2, making sure all elements of the list remain different, 
-- if they are initially different
diffResultsAux :: [(C,S)] -> [(C,S)] -> [(C,S)] 
diffResultsAux l [] = l
diffResultsAux l (h:t) = diffResultsAux (addDiff h l) t

addDiff :: (C,S) -> [(C,S)] -> [(C,S)] -- (addDiff x l) is the list that results from adding x to list l iff x is not part of l
addDiff x [] = [x]
addDiff x (h:t) = if (x==h) then (h:t) else h:(addDiff x t)

-- confIntoDouble [c_1,...,c_n] = [d_1,...,d_n], where d_m = integer corresponding to configuration c_m (there is an integer corresponding to each different
-- configuration in [c_1,...,c_n])
-- e.g. confIntoDouble [c1,c2,c3,c1,c3] = [1.0,2.0,3.0,1.0,3.0]
confIntoDouble :: [(C,S)] -> [Double]
confIntoDouble l = indexes l ldiff
    where ldiff = diffResults l

-- (indexes [x_1,...,x_n] l) = [i_1,...,i_n], where i_m = index of the first occurence of x_m in list l, if all elements of [x1,...,xn] belong to l
indexes :: [(C,S)] -> [(C,S)] -> [Double]
indexes [] l = []
indexes (h1:t1) l2 = (listIndex h1 l2) : (indexes t1 l2)

-- listIndex x l = index of the first occurence of x in list l, if x is part of l. If l is not empty and x is not part of it, an error occurs. The index of the first element of l is considered to be 1.
listIndex :: (C,S) -> [(C,S)] -> Double
listIndex x [] = 0
listIndex x (h:t)
    | not (elem x (h:t)) = error ((show x) ++ " does not belong to " ++ (show (h:t)))
    | (x==h) = 1
    | otherwise = 1 + (listIndex x t)


---------------------------------------------------------------

--useful links for this file and SemBE_Brookes.hs:
--https://hackage.haskell.org/; http://learnyouahaskell.com/
--https://book.realworldhaskell.org/read/characters-strings-and-escaping-rules.html 