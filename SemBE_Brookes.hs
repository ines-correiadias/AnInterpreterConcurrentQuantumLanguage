-- This module is a continuation of module SemBrookes and contains useful functions for both the semantics of commands of the simplified language (SemBrookes.hs)
-- and the semantics of the commands with probabilistic choice (Semantics_prob.hs).
-- The simplified language is in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.)  

module SemBE_Brookes where

import GrammarBrookes -- module created in GrammarBrookes.hs

-- changeSt i n s is the state [s|i=n] (here, we are not allowing attributions to non-declared identifiers - see section 11.2 from the article) -- REVER: preciso mesmo do auxiliar changeAll?
changeSt :: String -> Integer -> S -> S
changeSt i n [] = []
changeSt i n ((i',n'):t) = if (i'==i) then (i',n):(changeAll i n t) else (i',n'):(changeSt i n t)

-- Auxiliary function to changeSt (changeAll i n s changes the value of all occurrences of i in s)
changeAll :: String -> Integer -> S -> S 
changeAll i n [] = []
changeAll i n ((i',n'):t)
    | (i==i') = (i',n):(changeAll i n t)
    | otherwise = (i',n'):(changeAll i n t)

--data E = Zero | One | Id String | PlusE E E | IfTE_E B E E   

bigStepExp :: E -> S -> Integer -- bigStepExp e s = n means that <e,s> ->* n (see Fig 3 from the article)
bigStepExp Zero s = 0 -- 1st rule
bigStepExp One s = 1 -- 2nd rule
bigStepExp (Id i) s = getValue s i -- 3rd rule
bigStepExp (IfTE_E b e1 e2) s 
    | bigStepBExp b s = bigStepExp e1 s -- 5th rule
    | otherwise = bigStepExp e2 s -- 6th rule
bigStepExp (PlusE e1 e2) s = (bigStepExp e1 s) + (bigStepExp e2 s) -- final rules

getValue :: S -> String -> Integer -- getValue s i = the value that state s attributes to identifier i
getValue [] i = error ("No value attributed to identifier \""++i++"\" was found.")
getValue ((i',n'):t) i = if (i==i') then n' else getValue t i

--data B = BTrue | BFalse | Not B | And B B | Leq E E

bigStepBExp :: B -> S -> Bool -- bigStepBExp b s is the final result obtained by evaluating b in state s
bigStepBExp (BTrue) s = True
bigStepBExp (BFalse) s = False
bigStepBExp (Not b) s = not (bigStepBExp b s)
bigStepBExp (And b1 b2) s = (bigStepBExp b1 s) && (bigStepBExp b2 s)
bigStepBExp (Leq e1 e2) s = (bigStepExp e1 s) <= (bigStepExp e2 s)

freeE :: E -> [String] -- (freeE e) is the set of free identifiers in e
freeE Zero = []
freeE One = []
freeE (Id i) = [i]
freeE (PlusE e1 e2) = (freeE e1) ++ (freeE e2)
freeE (IfTE_E b e1 e2) = (freeB b) ++ (freeE e1) ++ (freeE e2)

freeB :: B -> [String] -- (freeB b) is the set of free identifiers in b
freeB BTrue = []
freeB BFalse = []
freeB (Not b) = freeB b
freeB (And b1 b2) = (freeB b1) ++ (freeB b2)
freeB (Leq e1 e2) = (freeE e1) ++ (freeE e2)

belong :: [String] -> S -> Bool -- (belong ids s) is only True if no identifier in list ids is missing in state s
belong [] s = True
belong (i:t) s = if (declared i s) then belong t s else False 

declared :: String -> S -> Bool -- (declared i s) is True if identifier i is part of state s
declared i [] = False
declared i ((i',n'):t) = if (i' == i) then True else (declared i t)
