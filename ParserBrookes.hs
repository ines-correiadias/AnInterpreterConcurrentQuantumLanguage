--Parser da linguagem simplificada (presente em: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.)
---- E::= 0 | 1 | I | E1+E2 | if B then E1 else E2 
---- C::= skip | I:=E | C1;C2 | if B then C1 else C2 | while B do C | C1||C2 (ignorou-se para já o "await")
---- B::= true | false | -B | B1&B2 | E1<=E2

module ParserBrookes where

import GrammarBrookes -- module created in GrammarBrookes.hs
import ParserBE_Brookes -- module created in ParserBE_Brookes.hs
import Text.ParserCombinators.Parsec -- import functions from Parsec (this module exports modules Text.ParserCombinators.Parsec.Prim, Text.ParserCombinators.Parsec.Combinator and Text.ParserCombinators.Parsec.Char)

-- main is used to apply the parser for commands to a program in a txt file

main = do
    putStr "Name of the file to be parsed: " -- print this string to the terminal
    fileName <- getLine -- get name of the file to be read
    program <- readFile fileName -- "program" is a String containing the program in fileName
    print (parseInputC program)-- apply to "program" function parseInputC and print the result 

parseCAux :: GenParser Char st CAux
parseCAux = do
    entersOnly -- 0 or more '\n'
    c <- parseCSelect
    spacesAndEnters -- 0 or more spaces or '\n'
    eof
    return c

parseC :: GenParser Char st C -- parser for commands
parseC = do
    x <- parseCAux
    return (cAuxToC x)

parseInputC :: String -> Either ParseError C -- test parseC (apply to an input given as argument a parser for commands)
parseInputC input = parse parseC "(unknown)" input

parseCSelect :: GenParser Char st CAux -- parser which "forwards" the input (which is a command) to another parser, which it selects according to the input
parseCSelect = try(pCSeq) <|> try(pCParal) <|> try(pCSkip) <|> try(pCAsg) <|> try(pCIf) <|> try(pCWhile) <|> pCParen

pCSeqExp :: String -> Either ParseError CAux -- test pCSeq 
pCSeqExp input = parse pCSeq "(unknown)" input

pCSeq :: GenParser Char st CAux -- parses commands with value "C1 ; C2", i.e "Seq C C" commands
pCSeq = do
    (SeqAux (StrC c1) (StrC c2)) <- pCSeqAux
    return (SeqAux (stringToC (c1)) (stringToC (c2)) )

pCSeqAux :: GenParser Char st CAux -- auxiliary parser to pCSeq
pCSeqAux = try(lastSemicolon) <|> someSemicolons

pCSeqAuxExp :: String -> Either ParseError CAux -- test pCSeq Aux
pCSeqAuxExp input = parse pCSeqAux "(unknown)" input

semicolAfterSpaces :: GenParser Char st Char
semicolAfterSpaces = do
    spacesOnly
    char ';'

lastSemicolon :: GenParser Char st CAux -- parses commands with value "C1 ; C2" and with only 1 semicolon 
lastSemicolon = do
    c1 <- comSeq
    spacesOnly
    char ';'
    spacesOnly -- 0 or more spaces
    entersOnly -- 0 or more '\n'
    c2 <- comSeq
    notFollowedBy (semicolAfterSpaces) -- guarantees that, if there is more than 1 semicolon in the input, the input is totally consumed 
    return (SeqAux (StrC c1) (StrC c2))

someSemicolons :: GenParser Char st CAux -- parses commands with value "C1 ; C2" and with more than 1 semicolon
someSemicolons = do
    c <- comSeq
    spacesOnly
    char ';'
    spacesOnly
    entersOnly
    (SeqAux (StrC c1) (StrC c2)) <- pCSeqAux
    return (SeqAux (StrC (c ++ ";" ++ c1)) (StrC c2))

comSeq :: GenParser Char st String -- parses commands inside a Seq expression (either a Paral, or a Asg, or a Skip, or a ParenC expression)
comSeq = do
    com <- try(pCParal) <|> try(pCSkip) <|> try(pCAsg) <|> try(pCIf) <|> try(pCWhile) <|> pCParen
    return (cToString (com))

cToString :: CAux -> String -- turns a CAux into the corresponding String
cToString (SkipAux) = "skip"
cToString (AsgAux i e) = i ++ ":=" ++ eToString(e)
cToString (SeqAux c1 c2) = cToString(c1) ++ ";" ++ cToString(c2)
cToString (ParalAux c1 c2) = cToString(c1) ++ "||" ++ cToString(c2)
cToString (StrC s) = s
cToString (IfTE_CAux b c1 c2) = "if " ++ bToString(b) ++ " then {" ++ cToString(c1) ++ "} else {" ++ cToString(c2) ++ "}" 
cToString (WhDoAux b c) = "while " ++ bToString(b) ++ " do {" ++ cToString(c) ++ "}" 

stringToC :: String -> CAux -- turns a String (with a command) into the corresponding CAux
stringToC input = let right = parse parseCAux "(unknown)" input
                  in eitherToT (right)

pCParal :: GenParser Char st CAux -- parses commands with value "C1 || C2", i.e "Paral C C" commands
pCParal = do
    (ParalAux (StrC c1) (StrC c2)) <- pCParalAux
    return (ParalAux (stringToC(c1)) (stringToC(c2)) )

parseTestParal :: String -> Either ParseError CAux -- test pCParal
parseTestParal input = parse pCParal "(unknown)" input

pCParalAux :: GenParser Char st CAux -- auxiliary parser to pCParal
pCParalAux = try(lastParal) <|> someParal

paralAfterSpaces :: GenParser Char st String
paralAfterSpaces = do
    spacesOnly
    string "||"

lastParal :: GenParser Char st CAux -- parses commands with value "C1 || C2" and with only 1 parallelism symbol
lastParal = do
    c1 <- comParal
    spacesOnly 
    string "||"
    spacesOnly
    c2 <- comParal
    notFollowedBy (paralAfterSpaces)
    return (ParalAux (StrC c1) (StrC c2))

someParal :: GenParser Char st CAux -- parses commands with value "C1 || C2" and with more than 1 parallelism symbol
someParal = do
    c <- comParal
    spacesOnly
    string "||"
    spacesOnly
    (ParalAux (StrC c1) (StrC c2)) <- pCParalAux
    return (ParalAux (StrC (c ++ "||" ++ c1)) (StrC c2) )

parseTestSomeParal :: String -> Either ParseError CAux -- test comParal
parseTestSomeParal input = parse someParal "(unknown)" input

comParal :: GenParser Char st String -- parses commands inside a Paral expression (either a Asg, or a Skip, or a ParenC expression)
comParal = do
    com <- try(pCSkip) <|> try(pCAsg) <|> try(pCIf) <|> try(pCWhile) <|> pCParen
    return (cToString (com))

parseTestComParal :: String -> Either ParseError String -- test comParal
parseTestComParal input = parse comParal "(unknown)" input

pCAsg :: GenParser Char st CAux -- parses commands with value "I:=E", i.e "Asg I E" commands
pCAsg = do
    i <- parseIdeStr
    spacesOnly
    string ":="
    spacesOnly
    e <- parseESelect
    return (AsgAux i e) -- this "i" will not have any white space

parseTestAsg :: String -> Either ParseError CAux -- test pCAsg
parseTestAsg input = parse pCAsg "(unknown)" input

pCSkip :: GenParser Char st CAux -- parses commands with value "skip", i.e "Skip" commands
pCSkip = do
    string "skip"
    notFollowedBy (try(alphaNum) <|> parseUnderscore) -- so that pCSkip fails when trying to parse an identifier starting with "skip"
    return SkipAux

pCIf :: GenParser Char st CAux
pCIf = do
    string "if"
    separateElems -- 1 or + spaces followed by 0 or + '\n' / 1 or + '\n'
    b <- parseBSelect
    separateElems
    string "then"
    separateOrJoined -- there can be no separation between "then" and "{"
    char '{' -- 1st command begins
    separateOrJoined
    c1 <- parseCSelect
    separateOrJoined
    char '}' -- 1st command ends
    separateOrJoined
    string "else"
    separateOrJoined
    char '{' -- 2nd command begins
    separateOrJoined
    c2 <- parseCSelect
    separateOrJoined
    char '}' -- 2nd command ends
    return (IfTE_CAux b c1 c2)

pCWhile :: GenParser Char st CAux
pCWhile = do
    string "while"
    separateElems
    b <- parseBSelect
    separateElems
    string "do"
    separateOrJoined -- there can be no separation between "do" and "{"
    char '{' -- command begins
    separateOrJoined
    c <- parseCSelect
    separateOrJoined
    char '}' -- command ends
    return (WhDoAux b c)

pCParen :: GenParser Char st CAux -- parses commands with value "(C)", i.e "ParenC" commands
pCParen = do
    char '('
    spacesOnly
    cInsideParen <- parseCSelect
    spacesOnly
    char ')'
    return cInsideParen

-- Function that converts a CAux into the corresponding C.

cAuxToC :: CAux -> C
cAuxToC (SkipAux) = Skip
cAuxToC (AsgAux i e) = Asg i e
cAuxToC (SeqAux c1 c2) = Seq (cAuxToC c1) (cAuxToC c2)
cAuxToC (ParalAux c1 c2) = Paral (cAuxToC c1) (cAuxToC c2)
cAuxToC (IfTE_CAux b c1 c2) = IfTE_C (bAuxToB b) (cAuxToC c1) (cAuxToC c2)
cAuxToC (WhDoAux b c) = WhDo (bAuxToB b) (cAuxToC c)
cAuxToC (StrC s) = error "Unable to convert into C."

-- useful links: https://hackage.haskell.org/); http://learnyouahaskell.com/; https://book.realworldhaskell.org/read/using-parsec.html
