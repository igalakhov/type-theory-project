Divides: Int -> Int -> Type
Divides a b = (m ** (a*m = b))

Coprime: Int -> Int -> Type
Coprime a b = Not (x ** (Not (x = 1), Divides x a, Divides x b))

coprime_comm: (a: Int, b: Int) -> Coprime a b -> Coprime b a
coprime_comm a b f (x ** (x_not_1, x_divides_b, x_divides_a)) = (f (x ** (x_not_1, x_divides_a, x_divides_b)))

coprime_prod: (p: Int, q: Int, x: Int) -> Coprime p x -> Coprime q x -> Coprime (p*q) x 
coprime_prod 
    p q x
    cp1 
    cp2 
    (z ** (z_neq_1, z_div_pq, z_div_x))
    = ?idk
