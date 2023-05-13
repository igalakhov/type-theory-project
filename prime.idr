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

eq_zero: (x: Nat) -> (y: Nat) -> (x=y) -> ((minus x y) = 0)
eq_zero Z Z x_eq_y = Refl
eq_zero (S xp) Z x_eq_y = void (SIsNotZ x_eq_y)
eq_zero Z (S yp) x_eq_y = void (SIsNotZ (sym x_eq_y))
eq_zero (S xp) (S yp) x_eq_y = eq_zero xp yp (prev_ok x_eq_y)

-- y < x
not_eq_zero: (x: Nat, y: Nat) -> (LT y x) -> Not ((minus x y) = 0)
not_eq_zero Z Z y_less_x = void (succNotLTEzero y_less_x)
not_eq_zero (S xp) Z y_less_x = \minus_eq_zero => void (SIsNotZ minus_eq_zero)
not_eq_zero Z (S yp) y_less_x = void (succNotLTEzero y_less_x)
not_eq_zero (S xp) (S yp) (y_less_x) = not_eq_zero xp yp (fromLteSucc y_less_x)

-- zx = zy -> either z = 0 or x=y
cancellation_helper: (x: Nat) -> (y: Nat) -> (z: Nat) -> (LT y x) -> (z*x = z*y) -> Either (z=0) (x=y)
cancellation_helper x y z y_less_x zx_eq_zy = let 
    zx_minus_zy_is_zero = (eq_zero (z*x) (z*y) zx_eq_zy) 
    z_times_x_minus_y_is_zero = trans (multDistributesOverMinusRight z x y) zx_minus_zy_is_zero
    in 
    case integral_domain z (minus x y) z_times_x_minus_y_is_zero of 
        Left z_is_zero => Left z_is_zero
        Right minus_xy_is_zero => void $ (not_eq_zero x y y_less_x) minus_xy_is_zero

my_cmp: (x: Nat, y: Nat) -> Either (x=y) (Either (LT x y) (LT y x))
my_cmp Z Z = Left Refl
my_cmp (S x) Z = Right (Right (LTESucc LTEZero))
my_cmp Z (S y) = Right (Left (LTESucc LTEZero))
my_cmp (S xp) (S yp) = case my_cmp xp yp of 
    Left xp_eq_yp => Left (cong xp_eq_yp)
    Right (Left xp_lt_yp) => Right (Left (LTESucc xp_lt_yp))
    Right (Right yp_lt_xp) => Right (Right (LTESucc yp_lt_xp))

cancellation: (x: Nat, y: Nat, z: Nat) -> (z*x = z*y) -> Either (z=0) (x=y)
cancellation x y z zx_eq_zy = case my_cmp x y of 
    Left x_eq_y => Right x_eq_y
    Right (Left (x_lt_y)) => case cancellation_helper y x z x_lt_y (sym zx_eq_zy) of 
        Left z_0 => Left z_0 
        Right y_eq_x => Right (sym y_eq_x)
    Right (Right (y_lt_x)) => cancellation_helper x y z y_lt_x zx_eq_zy


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
x_eq_xx_x_zero_or_one x x_eq_xx = sym <$> cancellation 1 x x (trans (multOneRightNeutral x) x_eq_xx)

x_zero_xx_zero: (x: Nat) -> x=0 -> (x*x) = 0
x_zero_xx_zero Z x_eq_0 = Refl
x_zero_xx_zero (S x) x_eq_0 = void (SIsNotZ x_eq_0)

x_one_xx_one: (x: Nat) -> x=1 -> (x*x) = 1
x_one_xx_one Z x_eq_1 = void (SIsNotZ (sym x_eq_1))
x_one_xx_one (S Z) x_eq_1 = Refl
x_one_xx_one (S (S x)) x_eq_1 = void (SIsNotZ (prev_ok x_eq_1))

x_squared_not_prime: (x: Nat) -> (Not (Prime (x*x)))
x_squared_not_prime x xx_prime = case (snd xx_prime) x (x_divides_xx x) of 
    Left x_eq_1 => ((fst xx_prime) (x_eq_1_xx_eq_1 x x_eq_1))
    Right x_eq_xx => case x_eq_xx_x_zero_or_one x x_eq_xx of 
        Left x_eq_0 => (no_prime_is_zero (x*x) xx_prime) (x_zero_xx_zero x x_eq_0)
        Right x_eq_1 => (fst xx_prime) (x_one_xx_one x x_eq_1)

n_div_a_div_ab: (a: Nat, b: Nat) -> Divides n a -> Divides n (a*b)
n_div_a_div_ab a n_div_a = ?todo_n_div_a_div_ab

n_divides_a_minus_b: (a: Nat, b: Nat) -> Divides n (minus a b) -> ((Divides n a), (Divides n b))
n_divides_a_minus_b a b n_div_a_min_b = ?n_divides_a_todo

factor_divides_ab: (a: Nat, b: Nat) -> Divides n (a*b) -> Either (Divides n a) (Divides n b)
factor_divides_ab a b n_div_ab = ?factor_divides_todo

pow_a_divides_pow_b: (a: Nat, b: Nat) -> Divides (power a n) (power b n) -> Divides a b
pow_a_divides_pow_b a b an_div_bn = ?pow_todo
