module GrammarQ where

import Data.Complex -- module for complex numbers (documentation at https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Complex.html)
import Data.Matrix -- module for matrix datatype and operations (documentation at https://hackage.haskell.org/package/matrix-0.3.6.1/docs/Data-Matrix.html)

-- Grammar for the commands of the simple quantum language (without non-determinism or concurrency)

-- C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C)

data Cqs = SkipQS | SeqQS Cqs Cqs | UQS G QVarList | MeasQS QVar Cqs Cqs | WhQS QVar Cqs
         deriving Show

-- Grammar for the commands of the concurrent quantum language with non-determinism

-- C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C) | C || C | C or C

data C = Skip | Seq C C | U G QVarList | Meas QVar C C | Wh QVar C | Paral C C | Or C C
       deriving (Show, Eq)

-- Auxiliary data type, for ParserQ.hs: CAux

data CAux = SkipAux | SeqAux CAux CAux | UAux G QVarList | MeasAux QVar CAux CAux | WhAux QVar CAux | ParalAux CAux CAux | OrAux CAux CAux | Str String
          deriving Show

-- Grammar for the unitary gates included in this language

data G = H | I | X | Y | Z | CNOT | CZ
       deriving (Show, Eq)

-- Quantum variables (which represent quantum systems)

type QVar = String

-- Lists of quantum variables

type QVarList = [QVar]

-- Quantum States

type S = Matrix (Complex Double) -- quantum states are represented by matrices of complex numbers (with one column)

-- Operators

type Op = Matrix (Complex Double)-- operators are represented by matrices of complex numbers

-- Linking functions (they link qubit names (of type QVar) to integers)

type L = (QVar -> Int)

-- Configurations of the form (probability, command of type Cqs, state)

type ConfQ = (Prob, Cqs, S)

-- Configurations of the form (probability, command of type C, state)

type ProbConf = (Prob, C, S)

type Prob = Double -- a value of type Prob represents a probability p (p should be between 0 and 1)


--------------------------------------------------------------------------------------------------------
--useful links:
-- http://learnyouahaskell.com/ ; https://hackage.haskell.org/