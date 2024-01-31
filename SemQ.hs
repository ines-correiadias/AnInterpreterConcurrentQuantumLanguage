module SemQ where

import GrammarQ -- module created in GrammarQ.hs
import Data.Complex -- module for complex numbers (documentation at: https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Complex.html)
import Data.Matrix -- module for matrix datatype and operations (documentation at: https://hackage.haskell.org/package/matrix-0.3.6.1/docs/Data-Matrix.html)


-- A linking function for tests:

l("q1") = 1
l("q2") = 2
l("q3") = 3

-- Matrices for tests:
a = [[1.0:+0, 2.0:+0, 3.0:+0], [4.0:+0, 5.0:+0, 6.0:+0], [7.0:+0, 8.0:+0, 9.0:+0]]
b = [[1.0:+0, 0.0:+0, 0.0:+0], [0.0:+0, 1.0:+0, 0.0:+0], [0.0:+0, 0.0:+0, 1.0:+0]]
s = [c1,c1,c1,c1,c1,c1,c1,c1]
c = [c1,c1,c1,c1,c1,c1,c1]
state00 = fromLists [[c1],[c0],[c0],[c0]] -- state |00>
state01 = fromLists [[c0],[c1],[c0],[c0]] -- state |01>
state11 = fromLists [[c0],[c0],[c0],[c1]] -- state |11>
state100 = fromLists [[c0],[c0],[c0],[c0],[c1],[c0],[c0],[c0]] -- state |100>
state101 = fromLists [[c0],[c0],[c0],[c0],[c0],[c1],[c0],[c0]] -- state |101>
state000 = fromLists [[c1],[c0],[c0],[c0],[c0],[c0],[c0],[c0]] -- state |000>
state2Q = fromLists [[oneHalf],[oneHalf],[oneHalf],[oneHalf]] -- state 1/2 (|00> + |01> + |10> + |11>)
phi = map (map realToComp) [[1/(sqrt 2)],[(1/3)*(1/(sqrt 2))],[(-2/3)*(1/(sqrt 2))],[(2/3)*(1/(sqrt 2))]]
state1 = fromLists [[hC],[c0],[c0],[hC]]

-- Program examples

seqHMq2 = SeqQS (UQS H ["q2"]) (MeasQS "q2" SkipQS SkipQS)
seqMq2 = SeqQS SkipQS (MeasQS "q2" SkipQS SkipQS)
prog1= SeqQS (SeqQS (UQS H ["q1"]) (MeasQS "q2" SkipQS SkipQS)) (UQS X ["q1"]) 
prog2= SeqQS (SeqQS (MeasQS "q2" SkipQS SkipQS) (UQS H ["q1"])) (UQS X ["q1"]) 
prog3= SeqQS (SeqQS (MeasQS "q2" SkipQS SkipQS) (UQS X ["q1"])) (UQS H ["q1"])

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

-- Operational semantics of the simple quantum language (without non-determinism or concurrency),
-- with syntax C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C)

-- (nextStep c l s) is the probability distribution of configurations that can be achieved from configuration <c,s>, through a transition,
-- with l being a linking function that attributes the integer n to the n-th qubit of state s

nextStep :: Cqs -> L -> Sq -> [ConfQ]
nextStep SkipQS l s = [(1,SkipQS,s)] -- in this case, there is no transition -- TESTADO
nextStep (SeqQS c1 c2) l s = if (term c1 s) then [(1,c2,s)] else map (lastInSeqProb c2) (nextStep c1 l s)
nextStep (UQS g vars) l s = [(1,SkipQS, applyGate g (qNums vars l) s)]
nextStep (MeasQS q c1 c2) l s
    | (p0 == 0) = [(p1, c2, s1)]
    | (p1 == 0) = [(p0, c1, s0)]
    | otherwise = [(p0, c1, s0), (p1, c2, s1)]
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
nextStep (WhQS q c) l s = [(1, MeasQS q SkipQS (SeqQS c (WhQS q c)), s)]

-- (bigStep c l s) is the final probability distribution of configurations that can be achieved from configuration <c,s>, through a transition,
-- with l being a linking function that attributes the integer n to the n-th qubit of state s
-- Every command in (bigStep c l s) is SkipQS.

bigStep :: Cqs -> L -> Sq -> [ConfQ]
bigStep SkipQS l s = [(1,SkipQS,s)] -- in this case, there is no transition
bigStep (SeqQS c1 c2) l s
    | (term c1 s) = bigStep c2 l s
    | otherwise = bigStepD l (beforeC2 c1 c2 l s) -- sum_j qj <skip,vj> (see corresponding semantics rule)
bigStep (UQS g vars) l s = [(1,SkipQS, applyGate g (qNums vars l) s)]
bigStep (MeasQS q c1 c2) l s
    | (p0 == 0) = bigStep c2 l s1 -- p1 == 1
    | (p1 == 0) = bigStep c1 l s0 -- p0 == 1
    | otherwise = bigStepD l [(p0, c1, s0), (p1, c2, s1)]
        where p0 = prob 0 (l(q)) s -- probability of measuring qubit q to be in state |0>
              p1 = prob 1 (l(q)) s -- probability of measuring qubit q to be in state |1>
              s0 = state 0 (l(q)) s -- state of the system of qubits after measuring qubit q in state |0>
              s1 = state 1 (l(q)) s -- state of the system of qubits after measuring qubit q in state |1>
bigStep (WhQS q c) l s = bigStep ( MeasQS q SkipQS (SeqQS c (WhQS q c)) ) l s

lastInSeqProb :: Cqs -> ConfQ -> ConfQ -- lastInSeqProb c' (p,c,s) represents the configuration (p, c;c', s)
lastInSeqProb c' (p,c,s) = (p, SeqQS c c', s)

term :: Cqs -> Sq -> Bool -- term c s is true iff < c,s > term is provable
term SkipQS s = True
term c s = False

-- bigStepD l confs gives the final configuration given the initial probability distribution of configurations - confs - and the linking function l associated
-- with confs

bigStepD :: L -> [ConfQ] -> [ConfQ] 
bigStepD l [] = []
bigStepD l ((p,c,s):t) = multProb p (bigStep c l s) ++ bigStepD l t

multProb :: Prob -> [ConfQ] -> [ConfQ] -- (multProb p' confs) multiplies by p' all probabilities of all configurations in list confs
multProb p [] = []
multProb p' ((p,c,s) : t) = (p'*p, c, s) : (multProb p' t)

-- beforeC2 c1 c2 l s = sum_i pi <c2, vi> (see definition of afterC1 below), with l being the linking function associated with s
beforeC2 :: Cqs -> Cqs -> L -> Sq -> [ConfQ]
beforeC2 c1 c2 l s = let afterC1 = bigStep c1 l s -- afterC1 = sum_i pi <skip,vi>
                     in (map (replaceBy c2) afterC1)

replaceBy :: Cqs -> ConfQ -> ConfQ -- replaceBy c' (p,c,s) replaces c by c'
replaceBy c' (p,c,s) = (p,c',s)

-- applyGate g nums s = output state that results from applying gate g to qubits whose number is in nums, when the input state is s
-- When g is a 2-qubit gate, the 1st number in nums corresponds to the control qubit, and the 2nd one to the target one.
applyGate :: G -> [Int] -> Sq -> Sq
applyGate g nums s
    | g == H = applyH nums s
    | g == I = s
    | g == X = applyX nums s
    | g == Y = applyY nums s
    | g == Z = applyZ nums s
    | g == CNOT = applyCNOT nums s
    | otherwise = applyCZ nums s

-- qNums vars l = list of integers corresponding to vars, according to linking function l -- É PRECISO ERRO ESPECIFICO PARA O CASO EM Q NEM TODAS AS VARIAVEIS FORAM DECLARADAS? nao, posso usar o do haskell.
qNums :: QVarList -> L -> [Int]
qNums [] l = []
qNums (h:t) l = l(h) : (qNums t l)

-- prob i n s = probability of measuring qubit number n in state |i>, with i=0,1, if the initial state of the system is s.
prob :: Int -> Int -> Sq -> Prob
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
state :: Int -> Int -> Sq -> Sq
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

-- (applyH nums s) is the output state which results from applying an Hadamard gate to the qubits whose number is in nums,
-- when the input state is s
applyH :: [Int] -> Sq -> Sq
applyH nums s = mult matrix s
    where matrix = applyToSomeQ had nums (numQubits s)

-- (applyX nums s) is the output state which results from applying a Pauli X gate to the qubits whose number is in nums,
-- when the input state is s
applyX :: [Int] -> Sq -> Sq
applyX nums s = mult matrix s
    where matrix = applyToSomeQ x nums (numQubits s)

-- (applyY nums s) is the output state which results from applying a Pauli Y gate to the qubits whose number is in nums,
-- when the input state is s
applyY :: [Int] -> Sq -> Sq
applyY nums s = mult matrix s
    where matrix = applyToSomeQ y nums (numQubits s)

-- (applyZ nums s) is the output state which results from applying a Pauli Z gate to the qubits whose number is in nums,
-- when the input state is s
applyZ :: [Int] -> Sq -> Sq
applyZ nums s = mult matrix s
    where matrix = applyToSomeQ z nums (numQubits s)

-- (applyCNOT nums s) is the output state which results from applying a CNOT gate to the two qubits in list nums (the 1st one is the control one
-- and the 2nd one is the target one), when the input state is s. If list nums does not contain only two elements, there is an error.
applyCNOT :: [Int] -> Sq -> Sq
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

-- (applyCZ nums s) is the output state which results from applying a CZ gate to the two qubits in list nums (the 1st one is the control one
-- and the 2nd one is the target one), when the input state is s. If list nums does not contain only two elements, there is an error.
applyCZ :: [Int] -> Sq -> Sq
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
    | (nqubits == 1) = if (nums == [1]) then op else error "The second argument of function applyToSomeQ can only be [1], if its third argument is 1."
    | otherwise = tensorProduct (replaceByGate op nums listId)
        where listId = gateList ident nqubits

-- sumMatrices a b = sum of matrices a and b
sumMatrices :: Op -> Op -> Op
sumMatrices a b = elementwise (+) a b

-- subtMatrices a b = a - b, where a and b are matrices
subtMatrices :: Op -> Op -> Op
subtMatrices a b = elementwise (-) a b 

-- (numQubits s) is equal to the number of qubits of a system in state s
numQubits :: Sq -> Int
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

--------------------------------------------------------------------------------------------------------
--useful links:
-- https://hackage.haskell.org/

-- https://wiki.haskell.org/Converting_numbers (mentions useful functions for converting numbers)