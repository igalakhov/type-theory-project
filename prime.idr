Divides: Nat -> Nat -> Type 
Divides a b = (m ** (a*m = b))

Prime: Nat -> Type
Prime p = (Not (p=1), (x: Nat) -> Divides x p -> Either (x = 1) (x = p))

four_divides_zero: Divides 4 0
four_divides_zero = (0 ** (4*0 = 0))

no_prime_is_zero: (p: Nat) -> (Prime p) -> Not (p=0)
no_prime_is_zero p (p_not_1, p_is_prime) p_is_zero = ?todo_npz

x_divides_xx: (x: Nat) -> Divides x (x*x)
x_divides_xx x = ?todo_xx

x_eq_1_xx_eq_1: (x:Nat) -> (x=1) -> ((x*x)=1)
x_eq_1_xx_eq_1 x = ?todo_xx_eq_1

x_eq_xx_x_zero_or_one: (x:Nat) -> (x = (x*x)) -> Either (x=0) (x=1)
x_eq_xx_x_zero_or_one = ?todo_x_eq_zero_or_one

x_squared_not_prime: (x: Nat) -> (Not (Prime (x*x)))
x_squared_not_prime x xx_prime = case (snd xx_prime) x (x_divides_xx x) of 
    Left x_eq_1 => ((fst xx_prime) (x_eq_1_xx_eq_1 x x_eq_1))
    Right x_eq_xx => ?todo3
