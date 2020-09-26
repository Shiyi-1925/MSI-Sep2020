import Text.Parsec
type Parser a = Parsec String () a

lpar :: Parser Char
lpar = char '('
rpar :: Parser Char
rpar = char ')'

paren :: Parser Char
paren = lpar <|> rpar

eqSign :: Parser String
eqSign = (try $ string "==") <|> string "="

chiffre :: Parser Char
chiffre = oneOf "0123456789"

op :: Parser Char
op = char '+'
