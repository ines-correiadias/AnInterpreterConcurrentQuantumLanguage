--Parser of the concurrent quantum language,
-- with syntax C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C) | C or C | C || C

module ParserQ where

import GrammarQ -- module created in GrammarQ.hs
import ParserBE_Brookes -- module created in ParserBE_Brookes.hs
import Text.ParserCombinators.Parsec -- import functions from Parsec (this module exports modules Text.ParserCombinators.Parsec.Prim, Text.ParserCombinators.Parsec.Combinator and Text.ParserCombinators.Parsec.Char)

-- main is used to apply the parser for commands to a program in a txt file

main = do
    putStr "Name of the file to be parsed: " -- print this string to the terminal
    fileName <- getLine -- get name of the file to be read
    program <- readFile fileName -- "program" is a String containing the program in fileName
    print (parseInputC program)-- apply to "program" function parseInputC and print the result 

parseInputC :: String -> Either ParseError C -- test parseC (apply to an input given as argument a parser for commands)
parseInputC input = parse parseC "(unknown)" input

parseC :: GenParser Char st C -- parser for commands
parseC = do
    x <- parseCAux
    return (cAuxToC x)

stringToC :: String -> CAux -- turns a String (with a command) into the corresponding CAux
stringToC input = let right = parse parseCAux "(unknown)" input
                  in eitherToT (right)

parseCAux :: GenParser Char st CAux -- parses a command (which can have certain white spaces before and after) and returns the corresponding value of type CAux
parseCAux = do
    entersOnly -- 0 or more '\n'
    c <- parseCSelect
    spacesAndEnters -- 0 or more spaces or '\n'
    eof
    return c

parseCSelect :: GenParser Char st CAux -- parser which "forwards" the input (which is a command) to another parser, which it selects according to the input
parseCSelect = try(pCParal) <|> try(pCOr) <|> try(pCSeq) <|> try(pCSkip) <|> try(pCGate) <|> try(pCMeas) <|> try(pCWhile) <|> pCParen

pCSkip :: GenParser Char st CAux -- parses commands with value "skip", i.e "Skip" commands
pCSkip = do
    string "skip"
    return SkipAux

pCMeas :: GenParser Char st CAux -- parses Meas commands
pCMeas = do
    string "Meas"
    separateOrJoined
    char '('
    spacesOnly
    q <- parseQVar
    spacesOnly
    char ')'
    separateOrJoined -- there can be no separation between ")" and "->"
    string "->"
    separateOrJoined
    char '('
    separateOrJoined
    c1 <- parseCSelect -- c1 is the first command
    spacesOnly
    char ','
    separateOrJoined
    c2 <- parseCSelect -- c2 is the second command
    separateOrJoined
    char ')'
    return (MeasAux q c1 c2)

pCWhile :: GenParser Char st CAux -- parses While commands
pCWhile = do
    string "while"
    separateElems -- 1 or + spaces followed by 0 or + '\n' / 1 or + '\n'
    string "Meas"
    separateOrJoined
    char '('
    spacesOnly
    q <- parseQVar
    spacesOnly
    char ')'
    separateOrJoined -- there can be no separation between ")" and "{"
    char '{' -- command begins
    separateOrJoined
    c <- parseCSelect
    separateOrJoined
    char '}' -- command ends
    return (WhAux q c)

pCParen :: GenParser Char st CAux -- parses commands with value "(C)"
pCParen = do
    char '('
    separateOrJoined
    cInsideParen <- parseCSelect
    separateOrJoined
    char ')'
    return cInsideParen

pCGate :: GenParser Char st CAux -- parses U commands
pCGate = try(pGate1Q) <|> pGate2Q

pGate1Q :: GenParser Char st CAux -- parses U commands with 1-qubit gates
pGate1Q = do
    g <- gate1Q
    separateOrJoined
    char '('
    separateOrJoined -- there can be no separation between "(" and the name of the quantum variable
    q <- parseQVar -- q is a quantum variable
    qs <- (try(parseQVars) <|> return []) -- qs is either a list of quantum variables or an empty list
    separateOrJoined
    char ')'
    return (UAux g (q:qs))

pGate2Q :: GenParser Char st CAux -- parses U commands with 2-qubit gates
pGate2Q = do
    g <- gate2Q
    separateOrJoined
    char '('
    separateOrJoined -- there can be no separation between "(" and the name of the quantum variable
    q1 <- parseQVar -- q1 is a quantum variable
    spacesOnly
    char ','
    separateOrJoined
    q2 <- parseQVar -- q2 is another quantum variable
    separateOrJoined
    char ')'
    return (UAux g [q1,q2])

gate1Q :: GenParser Char st G -- parses the name of a 1-qubit gate belonging to this language ("H", "I", "X", "Y" or "Z")
gate1Q = do
    s <- ( try (string "H") <|> try (string "I") <|> try (string "X") <|> try (string "Y") <|> (string "Z") )
    return (strToG s)

gate2Q :: GenParser Char st G -- parses the name of a 2-qubit gate belonging to this language ("CNOT" or "CZ")
gate2Q = do
    s <- ( try (string "CNOT") <|> (string "CZ") )
    return (strToG s)

strToG :: String -> G -- (strToG s) = value of type G corresponding to s, if there is one
strToG "H" = H
strToG "I" = I
strToG "X" = X
strToG "Y" = Y
strToG "Z" = Z
strToG "CNOT" = CNOT
strToG "CZ" = CZ
strToG s = error ("No value of type G corresponds to " ++ s)

-- reservedWordQ parses a reserved word ("skip", "H", "I", "X", "Y", "Z", "CNOT", "CZ", "or", "Meas" or "while"), as long as it is followed by neither an alphabetic or numeric Unicode character nor an underscore
reservedWordQ :: GenParser Char st String
reservedWordQ = do
    x <- ( try (string "skip") <|> try (string "H") <|> try (string "I") <|> try (string "X") <|> try (string "Y") <|> try (string "Z") <|> try (string "CNOT") <|> try (string "CZ") <|> try (string "or") <|> try (string "Meas") <|> (string "while") )
    notFollowedBy (try(alphaNum) <|> parseUnderscore)
    return x

parseQVar :: GenParser Char st QVar -- parses quantum variables (corresponding to values of type QVar)
parseQVar = do
    notFollowedBy (reservedWordQ)
    i <- (try(startUnderscore) <|> startLetter) -- the quantum variable can either start with an underscore or with an alphabetic Unicode character  
    return i -- this "i" will not have any white space

parseQVars :: GenParser Char st QVarList -- parseQVars parses a comma followed by a list of quantum variables given in the input, and returns that same list
parseQVars = do
    spacesOnly -- 0 or + spaces
    char ','
    separateOrJoined
    q <- parseQVar -- q is a quantum variable
    qs <- (try (parseQVars) <|> return []) -- qs is either a list of quantum variables or an empty list
    return (q:qs)

pCSeq :: GenParser Char st CAux -- parses commands with value "C1 ; C2", i.e "Seq C C" commands
pCSeq = do
    (SeqAux (Str c1) (Str c2)) <- pCSeqAux
    return (SeqAux (stringToC (c1)) (stringToC (c2)) )

pCSeqAux :: GenParser Char st CAux -- auxiliary parser to pCSeq
pCSeqAux = try(lastSemicolon) <|> someSemicolons

lastSemicolon :: GenParser Char st CAux -- parses commands with value "C1 ; C2" and with only 1 semicolon 
lastSemicolon = do
    c1 <- comSeq
    spacesOnly
    char ';'
    spacesOnly -- 0 or more spaces
    entersOnly -- 0 or more '\n'
    c2 <- comSeq
    notFollowedBy (semicolAfterSpaces) -- guarantees that, if there is more than 1 semicolon in the input, the input is totally consumed 
    return (SeqAux (Str c1) (Str c2))

someSemicolons :: GenParser Char st CAux -- parses commands with value "C1 ; C2" and with more than 1 semicolon
someSemicolons = do
    c <- comSeq
    spacesOnly
    char ';'
    spacesOnly
    entersOnly
    (SeqAux (Str c1) (Str c2)) <- pCSeqAux
    return (SeqAux (Str (c ++ ";" ++ c1)) (Str c2))

comSeq :: GenParser Char st String -- parses commands inside a Seq command (either a Skip, a U, a Meas or a While command, or a command between parentheses)
comSeq = do
    com <- try(pCSkip) <|> try(pCGate) <|> try(pCMeas) <|> try(pCWhile) <|> pCParen
    return (cToString (com))

semicolAfterSpaces :: GenParser Char st Char -- parses 0 or + spaces followed by a ';'
semicolAfterSpaces = do
    spacesOnly
    char ';'

cToString :: CAux -> String -- turns a CAux into the corresponding String
cToString (SkipAux) = "skip"
cToString (SeqAux c1 c2) = cToString(c1) ++ ";" ++ cToString(c2)
cToString (UAux g qs) = (show g) ++ "(" ++ (showQVarList qs) ++ ")"
cToString (MeasAux q c1 c2) = "Meas (" ++ q ++ ") -> (" ++ cToString(c1) ++ ", " ++ cToString(c2) ++ ")"
cToString (WhAux q c) = "while Meas (" ++ q ++ ") {" ++ cToString(c) ++ "}"
cToString (ParalAux c1 c2) = cToString(c1) ++ "||" ++ cToString(c2)
cToString (OrAux c1 c2) = cToString(c1) ++ " or " ++ cToString(c2)
cToString (Str s) = s

-- showQVarList l = string with the elements of l separated by commas
-- showQVarList [q1,q2,q3] = "q1, q2, q3" 
showQVarList :: QVarList -> String
showQVarList [] = ""
showQVarList [q] = q
showQVarList (q1:q2:qs) = q1 ++ ", " ++ q2 ++ (showQVarList qs)

paralAfterSpaces :: GenParser Char st String -- parses 0 or + spaces followed by a "||"
paralAfterSpaces = do
    spacesOnly
    string "||"

lastParal :: GenParser Char st CAux -- parses commands with value "C1 || C2" and with only 1 parallelism symbol
lastParal = do
    c1 <- comParal
    spacesOnly 
    string "||"
    spacesOnly
    entersOnly
    c2 <- comParal
    notFollowedBy (paralAfterSpaces)
    return (ParalAux (Str c1) (Str c2))

someParal :: GenParser Char st CAux -- parses commands with value "C1 || C2" and with more than 1 parallelism symbol
someParal = do
    c <- comParal
    spacesOnly
    string "||"
    spacesOnly
    entersOnly
    (ParalAux (Str c1) (Str c2)) <- pCParalAux
    return (ParalAux (Str (c ++ "||" ++ c1)) (Str c2) )

-- parses commands inside a Paral command (either an Or, a Seq, a Skip, a U, a Meas or a While command, or a command between parentheses)
comParal :: GenParser Char st String
comParal = do
    com <- try(pCOr) <|> try(pCSeq) <|> try(pCSkip) <|> try(pCGate) <|> try(pCMeas) <|> try(pCWhile) <|> pCParen
    return (cToString (com))

pCParal :: GenParser Char st CAux -- parses commands with value "C1 || C2", i.e "Paral C C" commands
pCParal = do
    (ParalAux (Str c1) (Str c2)) <- pCParalAux
    return (ParalAux (stringToC(c1)) (stringToC(c2)) )

pCParalAux :: GenParser Char st CAux -- auxiliary parser to pCParal
pCParalAux = try(lastParal) <|> someParal

orAfterSpaces :: GenParser Char st String -- parses 0 or + spaces followed by a "or"
orAfterSpaces = do
    spacesOnly
    string "or"

lastOr :: GenParser Char st CAux -- parses commands with value "C1 or C2" and with only 1 "or"
lastOr = do
    c1 <- comOr
    spacesOnly 
    string "or"
    spacesOnly
    entersOnly
    c2 <- comOr
    notFollowedBy (orAfterSpaces)
    return (OrAux (Str c1) (Str c2))

someOr :: GenParser Char st CAux -- parses commands with value "C1 or C2" and with more than 1 "or"
someOr = do
    c <- comOr
    spacesOnly
    string "or"
    spacesOnly
    entersOnly
    (OrAux (Str c1) (Str c2)) <- pCOrAux
    return (OrAux (Str (c ++ " or " ++ c1)) (Str c2) )

-- parses commands inside a Or command (either a Seq, a Skip, a U, a Meas or a While command, or a command between parentheses)
comOr :: GenParser Char st String
comOr = do
    com <- try(pCSeq) <|> try(pCSkip) <|> try(pCGate) <|> try(pCMeas) <|> try(pCWhile) <|> pCParen
    return (cToString (com))

pCOrAux :: GenParser Char st CAux -- auxiliary parser to pCOr
pCOrAux = try(lastOr) <|> someOr

pCOr :: GenParser Char st CAux -- parses commands with value "C1 or C2", i.e "Or C C" commands
pCOr = do
    (OrAux (Str c1) (Str c2)) <- pCOrAux
    return (OrAux (stringToC(c1)) (stringToC(c2)) )

-- Function to convert a CAux to the corresponding C.

cAuxToC :: CAux -> C
cAuxToC (SkipAux) = Skip
cAuxToC (SeqAux c1 c2) = Seq (cAuxToC c1) (cAuxToC c2)
cAuxToC (UAux g l) = U g l
cAuxToC (MeasAux q c1 c2) = Meas q (cAuxToC c1) (cAuxToC c2)
cAuxToC (WhAux q c) = Wh q (cAuxToC c)
cAuxToC (ParalAux c1 c2) = Paral (cAuxToC c1) (cAuxToC c2)
cAuxToC (OrAux c1 c2) = Or (cAuxToC c1) (cAuxToC c2)
cAuxToC (Str s) = error "Unable to convert to C."


---------------------------------------------------------------------

-- useful links: https://hackage.haskell.org/; http://learnyouahaskell.com/; https://book.realworldhaskell.org/read/using-parsec.html
-- made from a copy of: ParserBrookes.hs