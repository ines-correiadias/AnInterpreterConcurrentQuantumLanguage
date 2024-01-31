module SemQC where

import GrammarQ -- module created in GrammarQ.hs
import Data.Complex -- module for complex numbers (documentation at: https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Complex.html)
import Data.Matrix -- module for matrix datatype and operations (documentation at: https://hackage.haskell.org/package/matrix-0.3.6.1/docs/Data-Matrix.html)
import System.Random -- library that deals with pseudo-random number generation (documentation at: https://hackage.haskell.org/package/random-1.2.1.1/docs/System-Random.html)
import Numeric.Probability.Game.Event -- import functions for smallStep and bigStep (documentation at: https://hackage.haskell.org/package/game-probability-1.1/docs/Numeric-Probability-Game-Event.html)
import HistogramSem -- module created in HistogramSem.hs
import System.Exit -- in order to get type ExitCode (documentation at: https://hackage.haskell.org/package/base-4.18.0.0/docs/System-Exit.html)

-- A linking function for tests:

l("q") = 1
lT("q1") = 1
lT("q2") = 2
lT("q3") = 3
lT("q4") = 4

-- Matrices for tests:
a = [[1.0:+0, 2.0:+0, 3.0:+0], [4.0:+0, 5.0:+0, 6.0:+0], [7.0:+0, 8.0:+0, 9.0:+0]]
b = [[1.0:+0, 0.0:+0, 0.0:+0], [0.0:+0, 1.0:+0, 0.0:+0], [0.0:+0, 0.0:+0, 1.0:+0]]
s = [c1,c1,c1,c1,c1,c1,c1,c1]
c = [c1,c1,c1,c1,c1,c1,c1]
qTelepInitState = fromLists $ map (map realToComp) [[1/2],[0],[0],[1/2],[1/2],[0],[0],[1/2]] -- |psi> x |beta00>, with |psi> = (|0> + |1>) / sqrt(2)   
qTelepInitStateParal = fromLists $ map (map realToComp) [[0],[1/2],[0],[0],[0],[0],[0],[1/2],[0],[1/2],[0],[0],[0],[0],[0],[1/2]]
state0 = fromLists [[c1],[c0]] -- state |0>
statePlus = fromLists [[hC],[hC]] -- state |+>
state00 = fromLists [[c1],[c0],[c0],[c0]] -- state |00>
state01 = fromLists [[c0],[c1],[c0],[c0]] -- state |01>
state11 = fromLists [[c0],[c0],[c0],[c1]] -- state |11>
statePhi = fromLists [[hC],[c0],[c0],[hC]] -- state (1/(sqrt 2))(|00>+|11>) 
state100 = fromLists [[c0],[c0],[c0],[c0],[c1],[c0],[c0],[c0]] -- state |100>
state101 = fromLists [[c0],[c0],[c0],[c0],[c0],[c1],[c0],[c0]] -- state |101>
state000 = fromLists [[c1],[c0],[c0],[c0],[c0],[c0],[c0],[c0]] -- state |000>
state2Q = fromLists [[oneHalf],[oneHalf],[oneHalf],[oneHalf]] -- state 1/2 (|00> + |01> + |10> + |11>)
phi = map (map realToComp) [[1/(sqrt 2)],[(1/3)*(1/(sqrt 2))],[(-2/3)*(1/(sqrt 2))],[(2/3)*(1/(sqrt 2))]]

-- Program examples

seqHMq2 = Seq (U H ["q2"]) (Meas "q2" Skip Skip)
seqMq2 = Seq Skip (Meas "q2" Skip Skip)
p1= Paral (Seq ( U X ["q1"]) (U H["q2"]) ) (Meas "q1" Skip Skip)
p2= Paral (Paral (U X ["q1"]) (U H ["q2"]) ) (Meas "q1" Skip Skip)
p3= Paral (Seq (U X ["q1"]) (U H ["q2"]) ) (Meas "q2" Skip Skip)
p4= Paral (Paral (U X ["q1"]) (U H ["q2"]) ) (Meas "q2" Skip Skip)
p5= Paral (Seq (U X ["q1"]) (U H ["q1"]) ) (Meas "q1" Skip Skip)
p6= Paral (Paral (U X ["q1"]) (U H ["q1"]) ) (Meas "q1" Skip Skip)

-- Some useful constants:

h = 1/(sqrt 2)
hC = h :+ 0 -- h as a Complex Double value
c1 = 1.0 :+ 0 -- 1 as a Complex Double value
c0 = 0.0 :+ 0 -- 0 as a Complex Double value
i = 0.0 :+ 1 -- i as a Complex Double value
oneHalf = realToComp (1/2) -- 1/2 as a Complex Double value

-- 1-qubit unitary gates in matrix form:

had = fromLists [[hC,hC],[hC,-hC]] -- Hadamard gate
ident = fromLists [[c1,c0],[c0,c1]] -- Identity gate
x = fromLists [[c0,c1],[c1,c0]] -- Pauli X gate
y = fromLists [[c0,-i],[i,c0]] -- Pauli Y gate
z = fromLists [[c1,c0],[c0,-c1]] -- Pauli Z gate

m0 = fromLists [[1,0],[0,0]] -- measurement operator M0 = |0><0| 
m1 = fromLists [[0,0],[0,1]] -- measurement operator M1 = |1><1|
m2 = fromLists [[0,0],[0,2]] -- 2|1><1|

-- Operational semantics of the concurrent quantum language with non-determinism,
-- with syntax C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C) | C or C | C || C 
 
-- (applyBigStepList c l s) = (bigStepList c l s) after joining the elements with the same command and state of each of its lists 
applyBigStepList :: C -> L -> S -> [[ProbConf]]
applyBigStepList c l s = simplify (bigStepList c l s)

-- (simplify l) joins the elements of each list of l with the same command and state
simplify :: [[ProbConf]] -> [[ProbConf]]
simplify l = map sumEquals l

sumEquals :: [ProbConf] -> [ProbConf] -- (sumEquals l) joins the elements of l with the same command and state, summing their probabilities into one probability
sumEquals [] = []
sumEquals l = sumEqualsAux [] l

-- Auxiliary to sumEquals: (sumEqualsAux l1 l2) adds the elements of l2 to l1, making sure each element of l1 remains with a different combination of command and state,
-- if they initially have different combinations
sumEqualsAux :: [ProbConf] -> [ProbConf] -> [ProbConf]
sumEqualsAux l [] = l
sumEqualsAux l (h:t) = sumEqualsAux (add h l) t

-- (add (p,c,s) l) adds p to the probability of the element of l with command c and state s, making sure each element (p',c',s') of l remains with a different (c',s'),
-- if they initially have different combinations of c' and s'.
-- If there is no element of l with command c and state s, then (p,c,s) is added to l.
add :: ProbConf -> [ProbConf] -> [ProbConf]
add (p,c,s) [] = [(p,c,s)]
add (p,c,s) ((p',c',s'):t) = if (c==c') && (s==s') then ((p+p', c', s'):t) else (p',c',s'):(add (p,c,s) t)

-- (smallStepList c l s) is a ĺist with the different possibilities for the probability distribution of configurations that can be achieved
-- from configuration <c,s>, through a transition, with l being a linking function that attributes the integer n to the n-th qubit of state s
-- (smallStepList c l s) has the form of [d1,d2,..,dn], where di represents a probability distribution of configurations.

smallStepList :: C -> L -> S -> [[ProbConf]]
smallStepList Skip l s = [[(1,Skip,s)]] -- in this case, there is no transition
smallStepList (Seq c1 c2) l s = if (term c1 s) then [[(1,c2,s)]] else map (lastInSeqProb c2) (smallStepList c1 l s)
smallStepList (U g vars) l s = [[(1,Skip, applyGate g (qNums vars l) s)]]
smallStepList (Meas q c1 c2) l s
    | (p0 == 0) = [[(p1, c2, s1)]]
    | (p1 == 0) = [[(p0, c1, s0)]]
    | otherwise = [[(p0, c1, s0), (p1, c2, s1)]]
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
smallStepList (Wh q c) l s = [[(1, Meas q Skip (Seq c (Wh q c)), s)]]
smallStepList (Or c1 c2) l s = (smallStepList c1 l s) ++ (smallStepList c2 l s)
smallStepList (Paral c1 c2) l s 
    | term (Paral c1 c2) s = [[(1, Paral c1 c2, s)]] -- (in this case, there is no transition)
    | term c1 s = map (paral c1) (smallStepList c2 l s)
    | term c2 s = map (paral c2) (smallStepList c1 l s)
    | otherwise = (map (paral c2) (smallStepList c1 l s)) ++ (map (paral c1) (smallStepList c2 l s))

-- (bigStepList c l s) is a ĺist with the different possibilities for the final probability distribution of configurations, when the initial configuration
-- is <c,s>, with l being a linking function that attributes integer n to the n-th qubit of state s. 
-- (bigStepList c l s) has the form [d1,d2,..,dn], where di represents a probability distribution of configurations.
-- Every configuration in (bigStepList c l s) is terminated.

bigStepList :: C -> L -> S -> [[ProbConf]]
bigStepList Skip l s = [[(1,Skip,s)]] -- in this case, there is no transition
bigStepList (Seq c1 c2) l s
    | (term c1 s) = bigStepList c2 l s
    | otherwise = concat $ map (bigStepD l) (beforeC2 c1 c2 l s) -- list of possible (sum_j qj <skip,vj>) (see corresponding semantics rule)
bigStepList (U g vars) l s = [[(1,Skip, applyGate g (qNums vars l) s)]]
bigStepList (Meas q c1 c2) l s
    | (p0 == 0) = bigStepList c2 l s1 -- p1 == 1
    | (p1 == 0) = bigStepList c1 l s0 -- p0 == 1
    | otherwise = bigStepD l [(p0, c1, s0), (p1, c2, s1)]
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
bigStepList (Wh q c) l s = bigStepList ( Meas q Skip (Seq c (Wh q c)) ) l s
bigStepList (Or c1 c2) l s = (bigStepList c1 l s) ++ (bigStepList c2 l s)
bigStepList (Paral c1 c2) l s
    | term (Paral c1 c2) s = [[(1, Paral c1 c2, s)]] -- in this case, there is no transition
    | otherwise = concat $ map (bigStepD l) (smallStepList (Paral c1 c2) l s)

smallStep1st :: C -> C -> L -> S -> IO (C,S) -- auxiliary to smallStep
smallStep1st c1 c2 l s = do
    (c1', s') <- smallStep c1 l s
    return (Paral c1' c2, s')

smallStep2nd :: C -> C -> L -> S -> IO (C,S) -- auxiliary to smallStep
smallStep2nd c1 c2 l s = do
    (c2', s') <- smallStep c2 l s
    return (Paral c1 c2', s')

-- bigStep c l s = the final configuration achieved from configuration <c,s>, calculated using a scheduler,
-- with l being a linking function that attributes integer n to the n-th qubit of state s.
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in case of Or and Paral commands
---- takes into account the probability of each possible next configuration, in case of Meas commands

bigStep :: C -> L -> S -> IO (C,S)
bigStep Skip l s = return (Skip,s)
bigStep (Seq c1 c2) l s = if (term c1 s) then bigStep c2 l s else do
    (c1',s') <- smallStep c1 l s
    bigStep (Seq c1' c2) l s'
bigStep (U g vars) l s = return (Skip, applyGate g (qNums vars l) s)
bigStep (Meas q c1 c2) l s
    | (p0 == 0) = bigStep c2 l s1 -- p1 == 1
    | (p1 == 0) = bigStep c1 l s0 -- p0 == 1
    | otherwise = do
            n <- enact event -- (enact event) is a value that simulates "event" and gives an outcome according to the probabilities in it
            if (n==1) then (bigStep c1 l s0) else (bigStep c2 l s1)
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
              dist = [(1, p0),(2, p1)] -- probabilistic distribution (list of events and their corresponding probabilities)
              event = makeEventProb dist -- event corresponding to dist
bigStep (Wh q c) l s = bigStep ( Meas q Skip (Seq c (Wh q c)) ) l s
bigStep (Or c1 c2) l s = do
    x <- sched
    if (x==0) then (bigStep c1 l s) else (bigStep c2 l s)
bigStep (Paral c1 c2) l s
    | term (Paral c1 c2) s = return (Paral c1 c2, s) -- (in this case, there is no transition)
    | term c1 s = bigStep2nd c1 c2 l s
    | term c2 s = bigStep1st c1 c2 l s
    | otherwise = do
        x <- sched
        if (x==0) then (bigStep1st c1 c2 l s) else (bigStep2nd c1 c2 l s)

bigStep1st :: C -> C -> L -> S -> IO (C,S) -- auxiliary to bigStep
bigStep1st c1 c2 l s = do
    (c1',s') <- smallStep c1 l s
    bigStep (Paral c1' c2) l s'

bigStep2nd :: C -> C -> L -> S -> IO (C,S) -- auxiliary to bigStep
bigStep2nd c1 c2 l s = do
    (c2',s') <- smallStep c2 l s
    bigStep (Paral c1 c2') l s'

-- sched returns a pseudo-random number that is either 0 or 1
sched :: IO Int
sched = do
    g <- getStdGen -- g is the global pseudo-random number generator
    newStdGen -- updates the global pseudo-random number generator 
    return (fst (randomR (0,1) g)) -- (fst (randomR (0,1) g)) is a pseudo-random number between 0 and 1  

term :: C -> S -> Bool -- term c s is true iff < c,s > term is provable
term Skip s = True
term (Paral c1 c2) s = (term c1 s) && (term c2 s)
term c s = False

lastInSeqProb :: C -> [ProbConf] -> [ProbConf] -- lastInSeqProb c' l turns each element (p,c,s) of l into (p, c;c', s)
lastInSeqProb c' [] = []
lastInSeqProb c' ((p,c,s):t) = (p, Seq c c', s): lastInSeqProb c' t

-- (bigStepD l confs) = list with the different possibilities for the final probability distribution of configurations,
-- given an initial probability distribution of configurations - confs - and the linking function l associated with confs

bigStepD :: L -> [ProbConf] -> [[ProbConf]]
bigStepD l [] = [[]]
bigStepD l ((p,c,s):t) = [ (multProb p a) ++ b | a <- (bigStepList c l s), b <- (bigStepD l t) ]

multProb :: Prob -> [ProbConf] -> [ProbConf] -- (multProb p' confs) multiplies by p' all probabilities of all configurations in list confs
multProb p [] = []
multProb p' ((p,c,s) : t) = (p'*p, c, s) : (multProb p' t)

-- beforeC2 c1 c2 l s = list of all possible (sum_i pi <c2, vi>) (see definition of afterC1 below), with l being the linking function associated with s
beforeC2 :: C -> C -> L -> S -> [[ProbConf]]
beforeC2 c1 c2 l s = let afterC1 = bigStepList c1 l s -- afterC1 = list of all possible (sum_i pi <ci_term,vi>)
                   in (map (replaceBy c2) afterC1)

replaceBy :: C -> [ProbConf] -> [ProbConf] -- replaceBy c' l replaces by c' each c in all elements (p,c,s) of l
replaceBy c [] = []
replaceBy c' ((p,c,s):t) = (p,c',s): replaceBy c' t

paral :: C -> [ProbConf] -> [ProbConf] -- paral c' l turns each element (p,c,s) of l into (p, c'||c, s)
paral c' [] = []
paral c' ((p,c,s):t) = (p, Paral c' c, s): paral c' t

-- applyGate g nums s = output state that results from applying gate g to qubits whose number is in nums, when the input state is s
-- When g is a 2-qubit gate, the 1st number in nums corresponds to the control qubit, and the 2nd one to the target one.
applyGate :: G -> [Int] -> S -> S
applyGate g nums s
    | g == H = applyH nums s
    | g == I = s
    | g == X = applyX nums s
    | g == Y = applyY nums s
    | g == Z = applyZ nums s
    | g == CNOT = applyCNOT nums s
    | otherwise = applyCZ nums s

-- qNums vars l = list of integers corresponding to vars, according to linking function l
qNums :: QVarList -> L -> [Int]
qNums [] l = []
qNums (h:t) l = l(h) : (qNums t l)

-- prob i n s = probability of measuring qubit number n in state |i>, with i=0,1, if the initial state of the system is s.
prob :: Int -> Int -> S -> Prob
prob i n s
    | (i == 0 || i == 1) = realPart $ matrixToElem $ mult mToStateDagger mToState -- equation (2.92) - Quantum Computation and Quantum Information (Nielson & Chuang)
    | otherwise = error ((show i)++" cannot be the first argument of function prob.")
        where nqubits = numQubits s
              m = if (i==0) then applyToSomeQ m0 [n] nqubits else applyToSomeQ m1 [n] nqubits
              mToState = mult m s
              mToStateDagger = dagger mToState

-- matrixToDouble m returns the only element of matrix m, if it only contains one element
matrixToElem :: Matrix a -> a
matrixToElem m = if (length l == 1) then (head l) else error "Function matrixToDouble is only meant to receive matrices with only 1 element as argument."
    where l = toList m 

-- dagger m = Hermitian conjugate/ adjoint/ conjugate transpose of matrix m, obtained by complex conjugating and transposing m 
dagger :: Matrix (Complex Double) -> Matrix (Complex Double)
dagger m = transpose $ complexConjugate m

-- state i n s = state of the system whose initial state is s, after measuring its n-th qubit to be in state |i>, with i=0,1
state :: Int -> Int -> S -> S
state i n s
    | (i == 0 || i == 1) = fromLists (finalState) -- equation (2.93) - Quantum Computation and Quantum Information (Nielson & Chuang)
    | otherwise = error ((show i)++" cannot be the first argument of function state.")
        where nqubits = numQubits s
              m = if (i==0) then applyToSomeQ m0 [n] nqubits else applyToSomeQ m1 [n] nqubits
              mToState = mult m s
              mToStateL = toLists mToState -- matrix mToState in the form of a list of lists of Complex Double values
              p = prob i n s
              finalState = map ( map ( divideBy (realToComp (sqrt p)) ) ) mToStateL 

-- mult a b = a * b
mult :: Matrix (Complex Double) -> Matrix (Complex Double) -> Matrix (Complex Double)  
mult a b = multStd2 a b

divideBy :: Complex Double -> Complex Double -> Complex Double
divideBy a b = b/a

-- realToComp turns a Double value into its corresponding Complex Double value
realToComp :: Double -> Complex Double
realToComp a = a :+ 0

-- (applyH nums s) is the output state that results from applying an Hadamard gate to the qubits whose number is in nums,
-- when the input state is s
applyH :: [Int] -> S -> S
applyH nums s = mult matrix s
    where matrix = applyToSomeQ had nums (numQubits s)

-- (applyX nums s) is the output state that results from applying a Pauli X gate to the qubits whose number is in nums,
-- when the input state is s
applyX :: [Int] -> S -> S
applyX nums s = mult matrix s
    where matrix = applyToSomeQ x nums (numQubits s)

-- (applyY nums s) is the output state that results from applying a Pauli Y gate to the qubits whose number is in nums,
-- when the input state is s
applyY :: [Int] -> S -> S
applyY nums s = mult matrix s
    where matrix = applyToSomeQ y nums (numQubits s)

-- (applyZ nums s) is the output state that results from applying a Pauli Z gate to the qubits whose number is in nums,
-- when the input state is s
applyZ :: [Int] -> S -> S
applyZ nums s = mult matrix s
    where matrix = applyToSomeQ z nums (numQubits s)

-- (applyCNOT nums s) is the output state that results from applying a CNOT gate to the two qubits whose number is in list nums (the 1st one is the control one
-- and the 2nd one is the target one), when the input state is s. If list nums does not contain only two elements, there is an error.
applyCNOT :: [Int] -> S -> S
applyCNOT l s
    | (length l /= 2) = error "First argument of function applyCNOT must be a list with two elements."
    | otherwise = if (control /= target) then mult matrix s else error "The control and target qubits given as argument to function applyCNOT cannot be the same."
        where control = head l
              target = last l
              nqubits = numQubits s
              listId = gateList ident nqubits
              matrix0 = applyToSomeQ m0 [control] nqubits 
              matrix1 = tensorProduct $ replaceByGate x [target] (replaceByGate m1 [control] listId)
              matrix = sumMatrices matrix0 matrix1 -- equation (6.17) - Quantum Information (Barnett)

-- (applyCZ nums s) is the output state that results from applying a CZ gate to the two qubits whose number is in list nums (the 1st one is the control one
-- and the 2nd one is the target one), when the input state is s. If list nums does not contain only two elements, there is an error.
applyCZ :: [Int] -> S -> S
applyCZ l s
    | (length l /= 2) = error "First argument of function applyCZ must be a list with two elements."
    | otherwise = if (control /= target) then mult matrix s else error "The control and target qubits given as argument to function applyCZ cannot be the same."
        where control = head l
              target = last l
              nqubits = numQubits s
              listId = gateList ident nqubits
              matrix1 = tensorProduct listId 
              matrix2 = tensorProduct $ replaceByGate m1 [target] (replaceByGate m2 [control] listId)
              matrix = subtMatrices matrix1 matrix2 -- equation (6.22) - Quantum Information (Barnett)

-- (applyToSomeQ op nums n) = transformation matrix that corresponds to applying operator op to qubits whose number is in nums,
-- when the total number of qubits is n
applyToSomeQ :: Op -> [Int] -> Int -> Op
applyToSomeQ op nums nqubits
    | (nqubits == 1) = if (nums == [1]) then op else if (nums == []) then ident else error "The second argument of function applyToSomeQ can only be [] or [1], if its third argument is 1."
    | otherwise = tensorProduct (replaceByGate op nums listId)
        where listId = gateList ident nqubits

-- sumMatrices a b = sum of matrices a and b
sumMatrices :: Op -> Op -> Op
sumMatrices a b = elementwise (+) a b

-- subtMatrices a b = a - b, where a and b are matrices
subtMatrices :: Op -> Op -> Op
subtMatrices a b = elementwise (-) a b 

-- (numQubits s) is equal to the number of qubits of a system in state s
numQubits :: S -> Int
numQubits s = if log2IntToDouble == log2 then log2Int else error "The matrix given as argument to function numQubits is not a valid quantum state."
    where log2IntToDouble = (fromIntegral log2Int) :: Double -- log2Int converted to a Double value
          log2Int = round log2 :: Int -- log2 rounded to an Int value
          log2 = logBase 2.0 numElemsDouble -- logarithm base 2 of numElemsDouble (log2 is of type Double)
          numElemsDouble = (fromIntegral numElems) :: Double -- numElems converted to a Double value
          numElems = length (toList s) -- number of elements in matrix s

-- (gateList op n) = list with n elements, all equal to op
gateList :: Op -> Int -> [Op]
gateList op 0 = []
gateList op n = op : (gateList op (n-1))

-- (replaceByGate op nums l) = list l, but replacing by op the elements of l whose indexes are in list nums
-- E.g. replaceByGate A [1,3] [B,C,D] = [A,C,A] 
replaceByGate :: Op -> [Int] -> [Op] -> [Op]
replaceByGate op [] l = l
replaceByGate op (h:t) l
    | (n==0) = error ("Empty operators list received as argument by function replaceByGate.")
    | (h > n) = error ("List of operators given as argument to function replaceByGate does not contain " ++ (show h) ++ " elements.") 
    | (h < 1) = error ("The list of indexes received as argument by function replaceByGate cannot contain integers less than 1.")
    | otherwise = replaceByGate op t nextl
        where n = length l
              first = [op] ++ ( if (n==1) then [] else (elements 2 n l) )
              last = (elements 1 (n-1) l) ++ [op]
              middle = (elements 1 (h-1) l) ++ [op] ++ (elements (h+1) n l)
              nextl = if (h==1) then first else (if (h==n) then last else middle)

-- (elements a b l) = list with elements from l, from the a-th to the b-th, if (a >= 1), (b >= a), (b <= length l), and l is non-empty.
-- Otherwise, an error message is displayed.
-- E.g. elements 1 2 [1,2,3] = [1,2] 
elements :: Int -> Int -> [a] -> [a] 
elements a b [] = error "Unsuitable argument(s) given to function elements."
elements a b (h:t)
    | (a < 1 || a > b) = error "Unsuitable argument(s) given to function elements."
    | (a==1) && (b==1) = [h]
    | (a==1) = h:(elements 1 (b-1) t)
    | otherwise = elements (a-1) (b-1) t

-- tensorProduct l = result of the tensor product between all elements of l (e.g tensorProduct [A,B,C] = A tensor B tensor C)
tensorProduct :: [Op] -> Op
tensorProduct [] = error "No matrices given for the calculation of their tensor product."
tensorProduct [a] = error "Not enough matrices given for the calculation of their tensor product."
tensorProduct [a,b] = fromLists (tensorProductLists (toLists a) (toLists b))
tensorProduct (a:b:t) = tensorProduct [a, (tensorProduct (b:t)) ]

-- (tensorProductLists a b) is the tensor product of a and b, if a and b correspond to matrices
tensorProductLists :: [[Complex Double]] -> [[Complex Double]] -> [[Complex Double]]
tensorProductLists a [] = []
tensorProductLists [] b = []
tensorProductLists (h:t) b = (map (getLineTensor h) b) ++ (tensorProductLists t b)

-- getLineTensor [a1,...,an] b is the result of concatenating (multElemLine a1 b), ..., (multElemLine an b) 
getLineTensor :: [Complex Double] -> [Complex Double] -> [Complex Double]
getLineTensor [] l = []
getLineTensor l [] = []
getLineTensor (h:t) l = (multElemLine h l) ++ (getLineTensor t l)

-- (multElemLine x l) is the list that results from multiplying every element of l by x
multElemLine :: Complex Double -> [Complex Double] -> [Complex Double]
multElemLine x [] = []
multElemLine x (h:t) = xh : (multElemLine x t)
    where (a,theta) = polar x
          (b,phi) = polar h
          xh = mkPolar (a*b) (theta + phi)

-- complexConjugate m is the conjugate of matrix m
complexConjugate :: Matrix (Complex Double) -> Matrix (Complex Double)
complexConjugate m = fromLists (conjugated)
    where mList = toLists m -- matrix m in the form of a list of lists of Complex Double values
          conjugated = map (map conjugate) mList -- mList after complex conjugating all the elements in its lists

-- smallStep c l s = the next configuration achieved from configuration <c,s>, through a transition, calculated using a scheduler,
-- with l being a linking function that attributes the integer n to the n-th qubit of state s
-- This scheduler:
---- non-deterministically chooses between the two possible transitions, in case of Or and Paral commands
---- takes into account the probability of each possible next configuration, in case of Meas commands
smallStep :: C -> L -> S -> IO (C,S)
smallStep Skip l s = return (Skip,s)
smallStep (Seq c1 c2) l s = if (term c1 s) then return (c2,s) else do
    (c1',s') <- smallStep c1 l s
    return (Seq c1' c2, s')
smallStep (U g vars) l s = return (Skip, applyGate g (qNums vars l) s)
smallStep (Meas q c1 c2) l s
    | (p0 == 0) = return (c2, s1) -- p1 == 1
    | (p1 == 0) = return (c1, s0) -- p0 == 1
    | otherwise = do
            n <- enact event -- (enact event) is a value that simulates "event" and gives an outcome according to the probabilities in it
            return ( if (n==1) then (c1, s0) else (c2, s1) )
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
              dist = [(1, p0),(2, p1)] -- probabilistic distribution (list of events and their corresponding probabilities)
              event = makeEventProb dist -- event corresponding to dist
smallStep (Wh q c) l s = return (Meas q Skip (Seq c (Wh q c)), s)
smallStep (Or c1 c2) l s = do
    x <- sched
    if (x==0) then (smallStep c1 l s) else (smallStep c2 l s)
smallStep (Paral c1 c2) l s
    | term (Paral c1 c2) s = return (Paral c1 c2, s) -- (in this case, there is no transition)
    | term c1 s = smallStep2nd c1 c2 l s
    | term c2 s = smallStep1st c1 c2 l s
    | otherwise = do
        x <- sched
        if (x==0) then (smallStep1st c1 c2 l s) else (smallStep2nd c1 c2 l s)

-- Functions for presenting the results of bigStep and smallStep

-- applyBigStep c l s prints on the terminal the result of (bigStep c l s), but in a different format than the one obtained by inputting (bigStep c l s)
-- on the terminal
applyBigStep :: C -> L -> S -> IO ()
applyBigStep c l s = do
    c <- bigStep c l s
    putStrLn (showCSParen c)

-- applySmallStep c l s prints on the terminal the result of (smallStep c l s), but in a different format than the one obtained by inputting (smallStep c l s)
-- on the terminal
applySmallStep :: C -> L -> S -> IO ()
applySmallStep c l s = do
    c <- smallStep c l s
    putStrLn (showCSParen c)

-- showCSParen (c,s) converts (c,s) into a String value that contains c and s in the form of String values inside parentheses, separated by a comma and a new line character
showCSParen :: (C,S) -> String
showCSParen (c,s) = "(" ++ (show c) ++ ",\n" ++ (show s) ++ ")\n"

showLLConf :: [[ProbConf]] -> String -- (showLLConf l) = String value corresponding to l
showLLConf l = "[" ++ (showLLConfAux l) ++ "]"

showLLConfAux :: [[ProbConf]] -> String -- (showLLConfAux l) = String value corresponding to the [ProbConf] values inside l, with a comma and a new line character separating them
showLLConfAux [] = ""
showLLConfAux [c] = "[" ++ (showLConf c) ++ "]"
showLLConfAux (h:t) = "[" ++ (showLConf h) ++ "],\n" ++ (showLLConfAux t)

showLConf :: [ProbConf] -> String -- (showLConf l) = String value corresponding to the ProbConf values inside l, with a comma and a new line character separating them
showLConf [] = ""
showLConf [c] = showConf c
showLConf (h:t) = (showConf h) ++ ",\n" ++ (showLConf t)

showConf :: ProbConf -> String -- showConf (p,c,s) = String value corresponding to (p,c,s), with a new line character before s
showConf (p,c,s) = "(" ++ (show p) ++ "," ++ (show c) ++ ",\n" ++(show s) ++ ")"

---- Functions for building an histogram with the results of the semantics obtained using a scheduler:

-- (histogramBigStep n c l s) plots an histogram whose input is a list with n results of (bigStep c l s), 
-- where each different configuration in the results has a label of the form "<conf x>", where x is an integer.
-- The configuration corresponding to each label is shown in a caption printed on the terminal.

histogramBigStep :: Int -> C -> L -> S -> IO ExitCode
histogramBigStep n c l s = do
    input <- listBigStep n c l s
    putStrLn "-------------------------------------------\n"
    putStrLn "Histogram Caption:"
    putStrLn ""
    caption 1 (diffResults input)
    putStrLn "-------------------------------------------"
    histogramInt (confIntoDouble input) "Results of the big-step semantics"

-- (histogramSmallStep n c l s) plots an histogram whose input is a list with n results of (smallStep c l s), 
-- where each different configuration in the results has a label of the form "<conf x>", where x is an integer.
-- The configuration corresponding to each label is shown in a caption printed on the terminal.

histogramSmallStep :: Int -> C -> L -> S -> IO ExitCode
histogramSmallStep n c l s = do
    input <- listSmallStep n c l s
    putStrLn "-------------------------------------------\n"
    putStrLn "Histogram Caption:"
    putStrLn ""
    caption 1 (diffResults input)
    putStrLn "-------------------------------------------"
    histogramInt (confIntoDouble input) "Results of the small-step semantics"

-- (listBigStep n c l s) returns a list with n results of (bigStep c l s)
listBigStep :: Int -> C -> L -> S -> IO [(C,S)]
listBigStep 0 c l s = return []
listBigStep n c l s = do
    a <- bigStep c l s
    as <- listBigStep (n-1) c l s
    return (a:as)

-- (listSmallStep n c l s) returns a list with n results of (smallStep c l s)
listSmallStep :: Int -> C -> L -> S -> IO [(C,S)]
listSmallStep 0 c l s = return []
listSmallStep n c l s = do
    a <- smallStep c l s
    as <- listSmallStep (n-1) c l s
    return (a:as)

-- caption n [c1,...,cx] prints on the terminal a caption with a list whose i-th element is "< conf (n+i-1) > : ci", with its last element being "< conf (n+x-1) > : cx"  
caption :: Int -> [(C,S)] -> IO ()
caption n [] = putStrLn ""
caption n (h:t) = do
    putStrLn ("<conf "++(show n)++"> : \n"++(showCS h))
    caption (n+1) t

-- showCS (c,s) converts (c,s) into a String value that contains c and s in the form of String values separated by a new line character
showCS :: (C,S) -> String
showCS (c,s) = (show c) ++ "\n" ++ (show s)

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


--------------------------------------------------------------------------------------------------------
--made from a copy of SemQ.hs

--useful link: https://hackage.haskell.org/