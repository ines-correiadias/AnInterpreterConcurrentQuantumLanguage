module GrammarBrookes where

-- Gramática da linguagem simplificada (presente em: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.)

-- "Syntax" e "Finer Granularity" (págs. 146 e 153 desta referencia)

---Gramática para os identificadores (I):

---Grammar for integer expressions (E):
----E::= 0 | 1 | I | E1+E2 | if B then E1 else E2

data E = Zero | One | Id String | PlusE E E | IfTE_E B E E  
       deriving (Show, Eq)

--LeafE Int -> 0, 1, ... (natural numbers)
--"LeafStE String" is only an auxiliary value constructor (the end result of the parser has "LeafE Int" for leaves)
--PlusE x y <=> x+y
--MultE x y <=> x*y

---Gramática para os comandos (C):
----Considerando apenas C::= skip | I:=E | C1;C2 | if B then C1 else C2 | while B do C | C1||C2 (ignorou-se para já o "await")

data C = Skip | Asg String E | Seq C C | Paral C C | IfTE_C B C C | WhDo B C 
       deriving (Show, Eq)

--Skip -> skip
--Asg I E -> I:=E
--Seq C C -> C1;C2 
--Paral C C -> C1 || C2
--StrC String -> only an auxiliary value constructor

-- Auxiliary data type: CAux

data CAux = SkipAux | AsgAux String E | SeqAux CAux CAux | ParalAux CAux CAux | IfTE_CAux BAux CAux CAux | WhDoAux BAux CAux | StrC String
          deriving Show  

---Gramática para as expressões booleanas (B):
----B::= true | false | -B | B1&B2 | E1<=E2 

data B = BTrue | BFalse | Not B | And B B | Leq E E  
       deriving (Show, Eq)

--True -> true
--False -> false
--Not B -> - B
--And B B -> B1 & B2
--Leq E E -> E1 <= E2

-- Auxiliary data type: BAux

data BAux = BTrueAux | BFalseAux | NotAux BAux | AndAux BAux BAux | LeqAux E E | StrB String
          deriving Show

-- States

type S = [ (String, Integer) ]-- S represents states (which are functions represented by [I1=n1, ..., Ik=nk])

------------------------------------------------------------------------------------------------------------------------------
-- Gramática para os comandos que incluem escolha probabilística:

--Cp ::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C

data Cp = SkipP | AsgP String E | SeqP Cp Cp | P Prob Cp Cp | IfTE_P B Cp Cp | WhDoP B Cp -- P Prob Cp Cp allows probabilistic choice
        deriving Show

type Prob = Double -- a value of type Prob represents a probability p (p should be between 0 and 1)

type ConfP = (Prob, Cp, S) -- a value of type ConfP represents a configuration (probability, command, state) 

------------------------------------------------------------------------------------------------------------------------------
-- Gramática para os comandos que incluem probabilidades e não-determinismo (ND+Prob):

--CpND ::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C | C1 or C2

-- Or Cpnd Cpnd allows non-determinism

data Cpnd = SkipPND | AsgPND String E | SeqPND Cpnd Cpnd | PND Prob Cpnd Cpnd | IfTE_PND B Cpnd Cpnd | WhDoPND B Cpnd | Or Cpnd Cpnd  
        deriving Show

type ConfPND = (Prob, Cpnd, S) -- a value of type ConfPND represents a configuration (probability, command, state)

------------------------------------------------------------------------------------------------------------------------------
-- Gramática para os comandos que incluem probabilidade e concorrência (Prob+Conc)

-- C ::= skip | I:=E | C1;C2 | C1 +p C2 | if B then C1 else C2 | while B do C | C1 || C2

data CpC = SkipPC | AsgPC String E | SeqPC CpC CpC | PC Prob CpC CpC | IfTE_PC B CpC CpC | WhDoPC B CpC | ParalPC CpC CpC  
        deriving (Show, Eq)

type ConfPC = (Prob, CpC, S) -- a value of type ConfPC represents a configuration (probability, command, state) 

-------------------------------------------------------------------------------------------------------------------------------

--useful links:
-- http://learnyouahaskell.com/ ; https://hackage.haskell.org