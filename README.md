# lambda-calculator
Реализация лямбда-калькулятора, то есть библиотеки, которая позволяет β-редуцировать лямбда-термы и помогать решать вопросы их αβ-эквивалентности. Так же реализован алгоритм вывода типов лямбда-термов.

Следующий тип данных будет использоваться для описания термов чистого нетипизированного лямбда-иcчиcления:

```
type Symb = String 

infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)
```
