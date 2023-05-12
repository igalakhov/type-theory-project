Divides: Nat -> Nat -> Type 
Divides a b = (m ** (a*m = b))

Prime: Nat -> Type
Prime p = (Not (p=1), (x: Nat) -> Divides x p -> Either (x = 1) (x = p))

two_divides_zero: Divides 2 0
two_divides_zero = (0 ** Refl)

x_divides_xx: (x: Nat) -> Divides x (x*x)
x_divides_xx x = (x ** Refl)

prev: Nat -> Nat 
prev Z = Z
prev (S x) = x

prev_ok: (x=y) -> (prev x = prev y)
prev_ok Refl = Refl

-- sub x y -> y - x
sub: Nat -> Nat -> Nat 
sub Z x = x 
sub (S y) x = prev (sub y x)

integral_domain: (x: Nat) -> (y: Nat) -> (x*y=0) -> Either (x=0) (y=0)
integral_domain Z _ _ = Left Refl
integral_domain _ Z _ = Right Refl 
integral_domain (S xp) (S yp) xy_0 = void (SIsNotZ xy_0)

cancellation: (x: Nat) -> (y: Nat) -> (z: Nat) -> (z*x = z*y) -> Either (z=0) (x=y)
cancellation x y z zx_eq_zy = ?todo

no_prime_is_zero: (p: Nat) -> (Prime p) -> Not (p=0)
no_prime_is_zero p (p_not_1, p_is_prime) p_is_zero = case p_is_prime 2 (rewrite p_is_zero in two_divides_zero) of 
        Left two_is_one => let 
            one_is_zero = prev_ok two_is_one
            p_is_one = trans (p_is_zero) (sym one_is_zero) in (p_not_1 p_is_one)
        Right y => let 
            one_is_zero = prev_ok (trans (sym p_is_zero) (sym y))
            p_is_one = trans (p_is_zero) one_is_zero
            in (p_not_1 p_is_one)


mult_left_eq: (x, y, z: Nat) -> (x=y) -> ((z*x)=(z*y))
mult_left_eq x y z x_eq_y = cong x_eq_y

mult_right_eq: (x, y, z: Nat) -> (x=y) -> ((x*z)=(y*z))
mult_right_eq x y z x_eq_y = rewrite x_eq_y in Refl

x_eq_1_xx_eq_1: (x:Nat) -> (x=1) -> ((x*x) = 1)
x_eq_1_xx_eq_1 x x_eq_1 = rewrite x_eq_1 in Refl

congdivx: (b: Nat) -> (x=y) -> ((div x b) = (div y b))
congdivx b Refl = Refl

x_eq_xx_x_zero_or_one : (x : Nat) -> x = x * x -> Either (x = 0) (x = 1)
x_eq_xx_x_zero_or_one x x_eq_xx =
  case x of
    Z => Left Refl
    _ => Right ?heheha

x_squared_not_prime: (x: Nat) -> (Not (Prime (x*x)))
x_squared_not_prime x xx_prime = case (snd xx_prime) x (x_divides_xx x) of 
    Left x_eq_1 => ((fst xx_prime) (x_eq_1_xx_eq_1 x x_eq_1))
    Right x_eq_xx => ?todo3

