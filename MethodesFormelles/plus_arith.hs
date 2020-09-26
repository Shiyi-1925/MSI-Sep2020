data AExpr = Value Int | Plus AExpr AExpr

eval :: AExpr -> Int
eval (Value a) = a
eval (Plus a b) = (eval a) + (eval b)
