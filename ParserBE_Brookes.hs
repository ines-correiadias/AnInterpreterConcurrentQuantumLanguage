-- Parsers for Exp and BExp (this file is more updated than files ParserE_lingSimpl.hs and ParserB_lingSimpl.hs)

-- ======================================================================================================================

-- Parser for Exp, the set of integer expressions in the simplified language in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.)
-- This parser is part of the parser in file parser_linguagemSimplicada.hs
-- E::= 0 | 1 | I | E1+E2 | if B then E1 else E2
-- Feito a partir de uma cópia do ParserAExp.hs

--This file has the function "parseInputE", which applies to a given input a parser for Exp

module ParserBE_Brookes where

import Text.ParserCombinators.Parsec -- this module exports modules Text.ParserCombinators.Parsec.Prim, Text.ParserCombinators.Parsec.Combinator and Text.ParserCombinators.Parsec.Char 
import GrammarBrookes

-- initial parsers:

parseE :: GenParser Char st E -- initial parser (first parser to be applied to the input)
parseE = do
    spacesOnly
    x <- parseESelect
    spacesOnly
    eof
    return x

parseInputE :: String -> Either ParseError E -- test parseE (apply to an input given as argument a parser for Exp)
parseInputE input = parse parseE "(unknown)" input

parseESelect :: GenParser Char st E -- parser which "forwards" the input to another parser, which it selects according to the input
parseESelect = try(pEPlus) <|> try(pEZero) <|> try(pEOne) <|> try(pEIf) <|> try(pEId) <|> pEParen

parseExpSelect :: String -> Either ParseError E -- test parseESelect
parseExpSelect input = parse parseESelect "(unknown)" input

-- parsers for 0 and 1:

pEZero :: GenParser Char st E -- parses "0"
pEZero = do
    string "0"
    return Zero

parseZeroStr :: GenParser Char st String -- parses "0"
parseZeroStr = do
    string "0"
    return "0"

pEOne :: GenParser Char st E -- parses "1"
pEOne = do
    string "1"
    return One

parseOneStr :: GenParser Char st String -- parses "1"
parseOneStr = do
    string "1"
    return "1"

-- parsers for identifiers

pEId :: GenParser Char st E -- parses identifiers (which can only have alphabetic or numeric Unicode characters, or underscores)
pEId = do
    notFollowedBy (reservedWord)
    i <- (try(startUnderscore) <|> startLetter) -- the identifier can either start with an underscore or with an alphabetic Unicode character  
    return (Id i) -- this "i" will not have any white space

-- reservedWord parses a reserved word ("skip","if","then","else","while","do","true" or "false"), as long as it is followed by neither an alphabetic or numeric Unicode character nor an underscore
reservedWord :: GenParser Char st String
reservedWord = do
    x <- ( try (string "skip") <|> try (string "if") <|> try (string "then") <|> try (string "else") <|> try (string "while") <|> try (string "do") <|> try (string "true") <|> (string "false") )
    notFollowedBy (try(alphaNum) <|> parseUnderscore)
    return x

startUnderscore :: GenParser Char st String -- parses identifiers that start with an underscore
startUnderscore = do
    underscores <- many1 (parseUnderscore) -- "underscores" is a string with underscores only
    a <- alphaNum -- there cannot only be underscores in an identifier (a is an alphabetic or numeric Unicode character)
    b <- many (try(alphaNum) <|> parseUnderscore) -- "b" is either a string that can be composed of alphabetic and numeric Unicode characters and underscores, or an empty string
    return (underscores ++ (a:b))

startLetter :: GenParser Char st String -- parses identifiers that start with a letter
startLetter = do
    h <- letter -- h is an alphabetic Unicode character (which is a letter)
    t <- many (try(alphaNum) <|> parseUnderscore) -- "t" is either a string that can be composed of alphabetic and numeric Unicode characters and underscores, or an empty string
    return (h:t)

parseUnderscore :: GenParser Char st Char -- parses underscores only
parseUnderscore = satisfy (isUnderscore)

isUnderscore :: Char -> Bool -- returns True iff it receives an underscore
isUnderscore c = if (c=='_') then True else False

parseIdeTest :: String -> Either ParseError E -- test pEId
parseIdeTest input = parse pEId "(unknown)" input

parseIdeStr :: GenParser Char st String -- parses identifiers (which can only have alphabetic or numeric Unicode characters, or underscores)
parseIdeStr = do
    notFollowedBy (reservedWord)
    i <- (try(startUnderscore) <|> startLetter) -- the identifier can either start with an underscore or with an alphabetic Unicode character  
    return i -- this "i" will not have any white space

-- parser of IfThenElse expressions:

pEIf :: GenParser Char st E
pEIf = do
    string "if"
    separateElems -- 1 or + spaces followed by 0 or + '\n' / 1 or + '\n'
    b <- parseBSelect
    separateElems
    string "then"
    separateOrJoined -- there can be no separation between "then" and "{"
    char '{' -- 1st expression begins
    separateOrJoined
    e1 <- parseESelect
    separateOrJoined
    char '}' -- 1st expression ends
    separateOrJoined
    string "else"
    separateOrJoined
    char '{' -- 2nd expression begins
    separateOrJoined
    e2 <- parseESelect
    separateOrJoined
    char '}' -- 2nd expression ends
    return (IfTE_E (bAuxToB b) e1 e2)

parseIfETest :: String -> Either ParseError E -- test pEIf
parseIfETest input = parse pEIf "(unknown)" input

parseIfEStr :: GenParser Char st String
parseIfEStr = do
    string "if"
    separateElems
    b <- parseBSelect
    separateElems
    string "then"
    separateOrJoined -- there can be no separation between "then" and "{"
    char '{'
    separateOrJoined
    e1 <- parseESelect
    separateOrJoined
    char '}' -- 1st expression ends
    separateOrJoined
    string "else"
    separateOrJoined
    char '{'
    separateOrJoined
    e2 <- parseESelect
    separateOrJoined
    char '}'
    return (eToString (IfTE_E (bAuxToB b) e1 e2))

-- parser for E expressions inside parentheses:

pEParen :: GenParser Char st E -- parses the E expressions between parentheses
pEParen = do
    char '('
    spacesOnly
    dentroParen <- parseESelect
    spacesOnly
    char ')'
    return dentroParen

parseExpParen :: String -> Either ParseError E -- test pEParen
parseExpParen input = parse (pEParen) "(unknown)" input


-- function used to turn an E into the corresponding String

eToString :: E -> String -- turns an E into the corresponding String
eToString (Zero) = "0"
eToString (One) = "1"
eToString (Id id) = id  
eToString (PlusE a1 a2) = eToString(a1) ++ "+" ++ eToString(a2)
eToString (IfTE_E b e1 e2) = "if " ++ bToString (bToBAux b) ++ " then {" ++ eToString(e1) ++ "} else {" ++ eToString(e2) ++ "}"

-- parsers which return a String: 

termInsideParen :: GenParser Char st String -- parses a term inside parentheses, returning that same term
termInsideParen = do
    char '('
    spacesOnly
    a <- parseESelect
    spacesOnly
    char ')'
    return ("(" ++ (eToString (a)) ++ ")")

parseExpTermoEntreP :: String -> Either ParseError String -- test termInsideParen
parseExpTermoEntreP input = parse (termInsideParen) "(unknown)" input

termPlus :: GenParser Char st String -- parses a term in a PlusE expression: 0, 1, if then else expression, I or E inside parentheses   
termPlus = try(parseZeroStr) <|> try(parseOneStr) <|> try(parseIfEStr) <|> try(parseIdeStr) <|> termInsideParen 

parseExpTermPlus :: String -> Either ParseError String -- test termPlus
parseExpTermPlus input = parse (termPlus) "(unknown)" input


-- functions used to turn a String into the corresponding E:

eitherToT :: Either ParseError t -> t -- turn the result given by function parse into the corresponding x value, if that result is of type Right x
eitherToT (Right x) = x
eitherToT (Left x) = error "Parse error."

stringToE :: String -> E -- turn a String (with an expression) into the corresponding E
stringToE input = let right = parse parseE "(unknown)" input 
                  in eitherToT (right)

-- parsers which return "PlusE E E":

plusAfterSpaces :: GenParser Char st Char
plusAfterSpaces = do
    spacesOnly
    char '+'
    return '+'

lastPlus :: GenParser Char st E -- parses an expression with 1 "main" sum (e.g.: 1+(2+3); 1+2*3; 1+2)
lastPlus = do
    x <- termPlus
    spacesOnly
    char '+'
    spacesOnly
    y <- termPlus
    notFollowedBy (plusAfterSpaces) -- guarantees that, if there are more sums in the expression, they are consumed 
    return (PlusE (Id x) (Id y))

parseExpLastPlus :: String -> Either ParseError E -- test lastPlus
parseExpLastPlus input = parse (lastPlus) "(unknown)" input

somePlus :: GenParser Char st E -- parses an expression with more than 1 "main" sum (ex: 1+2+3; 1+2*4+3)
somePlus = do
    x <- termPlus
    spacesOnly
    char '+'
    spacesOnly
    (PlusE (Id t1) (Id t2)) <- parsePlusAux
    return (PlusE (Id (x ++ "+" ++ t1)) (Id t2))

parsePlusAux :: GenParser Char st E -- auxiliary parser to pEPlus
parsePlusAux = try (lastPlus) <|> somePlus

pEPlus :: GenParser Char st E -- parses PlusE E E expressions
pEPlus = do
    (PlusE (Id x) (Id y)) <- parsePlusAux
    return (PlusE (stringToE(x)) (stringToE(y)) )
    
parseExpPlus :: String -> Either ParseError E -- test pEPlus
parseExpPlus input = parse (pEPlus) "(unknown)" input

-- ===============================================================================================

-- Parser for BExp, the set of boolean expressions in the simplified language in: Stephen Brookes. Full abstraction for a shared-variable parallel language. Information and Computation, 127(2):145–163, 1996.)
-- This parser is part of the parser in file parser_linguagemSimplicada.hs
-- B::= true | false | -B | B1&B2 | E1<=E2
-- Assuming negation has higher precedence than conjunction, and inequality has higher precedence than conjunction and than negation.

parseBAux :: GenParser Char st BAux 
parseBAux = do
    spacesOnly
    b <- parseBSelect
    spacesOnly
    eof
    return b

parseB :: GenParser Char st B -- initial parser (first parser to be applied to the input)
parseB = do
    x <- parseBAux
    return (bAuxToB x)

parseInputB :: String -> Either ParseError B -- test parseB (apply to an input given as argument a parser for BExp)
parseInputB input = parse parseB "(unknown)" input

parseBSelect :: GenParser Char st BAux -- parser which "forwards" the input to another parser, which it selects according to the input
parseBSelect = try(pBAnd) <|> try(pBNot) <|> try(pBLeq) <|> try(pBTrue) <|> try(pBFalse) <|> pBParen

andAfterSpaces :: GenParser Char st Char
andAfterSpaces = do
    spacesOnly
    char '&'
    return '&'

lastAnd :: GenParser Char st BAux
lastAnd = do
    b1 <- termAnd
    spacesOnly
    char '&'
    spacesOnly
    b2 <- termAnd
    notFollowedBy (andAfterSpaces)
    return (AndAux (StrB b1) (StrB b2))

someAnd :: GenParser Char st BAux
someAnd = do
    b <- termAnd
    spacesOnly
    char '&'
    spacesOnly
    (AndAux (StrB b1) (StrB b2)) <- pBAndAux
    return (AndAux (StrB (b++"&"++b1)) (StrB b2) )

pBAndAux :: GenParser Char st BAux
pBAndAux = try(lastAnd) <|> someAnd

pBAnd :: GenParser Char st BAux
pBAnd = do
    (AndAux (StrB b1) (StrB b2)) <- pBAndAux
    return (AndAux (stringToB (b1)) (stringToB (b2)) )

termAnd :: GenParser Char st String
termAnd = do
    term <- try(pBNot) <|> try(pBLeq) <|> try(pBTrue) <|> try(pBFalse) <|> pBParen
    return (bToString (term))

bToString :: BAux -> String -- turns a BAux into the corresponding String
bToString (BTrueAux) = "true"
bToString (BFalseAux) = "false"
bToString (NotAux b) = "- " ++ bToString(b)
bToString (AndAux b1 b2) = bToString(b1) ++ " & " ++ bToString(b2)
bToString (LeqAux e1 e2) = eToString(e1) ++ " <= " ++ eToString(e2)
bToString (StrB s) = s

stringToB :: String -> BAux -- turns a String (with a boolean expression) into the corresponding BAux
stringToB input = let right = parse parseBAux "(unknown)" input 
                  in eitherToT (right)

pBNot :: GenParser Char st BAux
pBNot = do
    char '-'
    spacesOnly
    b <- bNot
    return (NotAux b)

bNot :: GenParser Char st BAux
bNot = try(pBNot) <|> try(pBLeq) <|> try(pBTrue) <|> try(pBFalse) <|> pBParen  

pBLeq :: GenParser Char st BAux
pBLeq = do
    e1 <- parseESelect
    spacesOnly
    string "<="
    spacesOnly
    e2 <- parseESelect
    return (LeqAux e1 e2)

pBTrue :: GenParser Char st BAux
pBTrue = do
    string "true"
    return (BTrueAux)

pBFalse :: GenParser Char st BAux
pBFalse = do
    string "false"
    return (BFalseAux)

pBParen :: GenParser Char st BAux
pBParen = do
    char '('
    spacesOnly
    dentroParen <- parseBSelect
    spacesOnly
    char ')'
    return dentroParen

-- Function that converts a BAux into the corresponding B:

bAuxToB :: BAux -> B
bAuxToB (BTrueAux) = BTrue
bAuxToB (BFalseAux) = BFalse
bAuxToB (NotAux b) = Not (bAuxToB (b))
bAuxToB (AndAux b1 b2) = And (bAuxToB (b1)) (bAuxToB (b2)) 
bAuxToB (LeqAux e1 e2) = Leq e1 e2
bAuxToB (StrB s) = error "Unable to convert into B."

-- Function that converts a B into the corresponding BAux:

bToBAux :: B -> BAux
bToBAux (BTrue) = BTrueAux
bToBAux (BFalse) = BFalseAux
bToBAux (Not b) = NotAux (bToBAux b)
bToBAux (And b1 b2) = AndAux (bToBAux b1) (bToBAux b2)
bToBAux (Leq e1 e2) = LeqAux e1 e2

-- Functions for defining white spaces between elements of the language

separateOrJoined :: GenParser Char st String -- separateOrJoined parses the same as separateElems OR parses the empty string
separateOrJoined = try(separateElems) <|> string ""

separateElems :: GenParser Char st String -- parses 1 or more spaces followed by 0 or more '\n', OR parses 1 or more '\n'
separateElems = try(atLeastOneSpace >> entersOnly) <|> atLeastOneEnter

atLeastOneSpace :: GenParser Char st String -- parses 1 or more spaces
atLeastOneSpace = many1 parseSpace

atLeastOneEnter :: GenParser Char st String -- parses 1 or more '\n' characters
atLeastOneEnter = many1 parseEnter

spacesAndEnters :: GenParser Char st String -- parses 0 or more characters that are either a space or a '\n' character
spacesAndEnters = many parseSpaceOrEnter

parseSpaceOrEnter :: GenParser Char st Char -- succeeds for space characters and '\n' characters
parseSpaceOrEnter = satisfy isSpaceOrEnter

isSpaceOrEnter :: Char -> Bool
isSpaceOrEnter c = (c == ' ' || c == '\n')

spacesOnly :: GenParser Char st String -- parses 0 or more spaces
spacesOnly = many parseSpace

entersOnly :: GenParser Char st String -- parses 0 or more '\n' characters
entersOnly = many parseEnter

parseSpace :: GenParser Char st Char -- succeeds for space characters (' ')
parseSpace = satisfy isSpace

isSpace :: Char -> Bool
isSpace c = (c == ' ')

parseEnter :: GenParser Char st Char -- succeeds for '\n' characters
parseEnter = satisfy isEnter

isEnter :: Char -> Bool
isEnter c = (c == '\n')


-----------------------------------------------------------------------------

-- useful links: https://hackage.haskell.org/; https://book.realworldhaskell.org/read/using-parsec.html; http://learnyouahaskell.com/