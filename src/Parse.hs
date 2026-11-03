module Parse (parseLine, parseType) where

import Text.Parsec
import Ast

parseLine :: Parsec String () Type
parseLine = do
    spaces
    let t = parseType
    spaces
    eof
    t

-- parseCtx :: Parsec String () Context
-- parseCtx = do
--     xs <- many (parseBinding parsePType)
--     eat "|-"
--     ys <- many (parseBinding parseNType)
--     return $ (xs, ys)

-- parseBinding :: Parsec String () a -> Parsec String () (Name, a)
-- parseBinding parser = do
--     name <- parseName -- only accepting uppercase is kinda weird here...
--     eat ":"
--     ty <- parser
--     return (name, ty)

parseType :: Parsec String () Type
parseType = (Positive <$> parsePType) <|> (Negative <$> parseNType)

parseNType :: Parsec String () NType
parseNType = parseBtm <|> parseNAtomic <|> try parseAnd <|> try parseOr <|>
    try parseNot <|> parseDownShift

parsePType :: Parsec String () PType
parsePType = parseTop <|> parsePAtomic <|> try parseTimes <|> try parsePlus <|>
    try parseMinus <|> try parseUpShift <|> parseFunc

parseBtm :: Parsec String () NType
parseBtm = string "btm" >> return Btm

parseNAtomic :: Parsec String () NType
parseNAtomic = NAtomic <$> parseName

parseAnd :: Parsec String () NType
parseAnd = parseOp parseNType "&" And

parseOr :: Parsec String () NType
parseOr = parseOp parseNType "|" Or

parseNot :: Parsec String () NType
parseNot = parseUnary parsePType "~" Not

parseDownShift :: Parsec String () NType
parseDownShift = parseUnary parsePType "v" NShift

parseFunc :: Parsec String () PType
parseFunc = parseOp parsePType "=>" $ \a b -> PShift (Or (Not a) (NShift b))

parseTop :: Parsec String () PType
parseTop = string "top" >> return Top

parsePAtomic :: Parsec String () PType
parsePAtomic = PAtomic <$> parseName

parseTimes :: Parsec String () PType
parseTimes = parseOp parsePType "*" Times

parsePlus :: Parsec String () PType
parsePlus = parseOp parsePType "+" Plus

parseMinus :: Parsec String () PType
parseMinus = parseUnary parseNType "-" Minus

parseUpShift :: Parsec String () PType
parseUpShift = parseUnary parseNType "^" PShift

parseName :: Parsec String () Name
parseName = Global <$> many1 upper

eat :: String -> Parsec String () ()
eat t = spaces >> string t >> spaces >> return ()

open :: Parsec String () ()
open = eat "("

close :: Parsec String () ()
close = eat ")"

parseOp :: (Parsec String () a) -> String -> (a -> a -> b) -> Parsec String () b
parseOp subterm op constr = do
    open
    t1 <- subterm
    eat op 
    t2 <- subterm
    close
    return $ constr t1 t2

parseUnary :: (Parsec String () a) -> String -> (a -> b) -> Parsec String () b
parseUnary subterm op constr = do
    eat op
    t <- subterm
    return $ constr t

