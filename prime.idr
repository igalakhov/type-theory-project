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

-- fequiv
fequiv: (x: a, xp: a, y: b, yp: b, f: a -> b -> c) -> (x=xp) -> (y=yp) -> (f x y) = (f xp yp)
fequiv x xp y yp f x_xp y_yp = trans (cong {f=(`f` y)} x_xp) (cong {f=(f xp)} y_yp)

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

n_div_a_div_ab: (a: Nat, b: Nat, n: Nat) -> Divides n a -> Divides n (a*b)
n_div_a_div_ab a b n (m ** (nm_a)) = ((m*b) ** trans (multAssociative n m b) (cong {f=\x => x*b} nm_a))

-- a=b
-- x=y
-- f(a, x) = f(b, y)

n_divides_a_plus_b: (a: Nat, b: Nat, n: Nat) -> n `Divides` a -> n `Divides` b -> n `Divides` (a + b)
n_divides_a_plus_b a b n (ap ** apn_a) (bp ** bpn_b) = let 
    equiv = fequiv (mult n ap) a (mult n bp) b (\x => \y => x+y) apn_a bpn_b
    dist = multDistributesOverPlusRight n ap bp
    in 
    ((ap+bp) ** (trans dist equiv))

n_divides_a_minus_b: (a: Nat, b: Nat, n: Nat) -> n `Divides` a -> n `Divides` b -> n `Divides` (minus a b)
n_divides_a_minus_b a b n (ap ** apn_a) (bp ** bpn_b) = let 
    equiv = fequiv (mult n ap) a (mult n bp) b (\x => \y => (minus x y)) apn_a bpn_b
    dist = multDistributesOverMinusRight n ap bp
    in 
    ((minus ap bp) ** (trans dist equiv))

divide_product: (a: Nat, b: Nat, c:Nat, d: Nat) -> a `Divides` b -> c `Divides` d -> (a*c) `Divides` (b*d)
divide_product a b c d (ap ** apa_b) (cp ** cpc_d) = let 
    step0 = fequiv (mult a ap) b (mult c cp) d (\x => \y => x*y) apa_b cpc_d
    step1 = multAssociative a ap (mult c cp)
    step2 = multAssociative ap c cp 
    step3 = cong {f=\x => (mult x cp)} (multCommutative ap c)
    step4 = trans step3 (sym $ multAssociative c ap cp)
    step5 = cong {f=\x => (mult a x)} (trans step2 step4)
    step6 = multAssociative a c (mult ap cp)
    step7 = trans step5 step6
    step8 = trans (sym step7) (trans step1 step0)
    in 
    ((mult ap cp) ** step8)

a_div_b_pow: (a: Nat, b: Nat, n: Nat) -> a `Divides` b -> (power a n) `Divides` (power b n)
a_div_b_pow a b Z (m ** am_b) = (1 ** Refl)
a_div_b_pow a b (S x) (m ** am_b) = let 
    (m1 ** m1_mul) = a_div_b_pow a b x (m ** am_b)
    equiv = fequiv (mult a m) b (mult (power a x) m1) (power b x) mult am_b m1_mul
    step0 = multAssociative (mult a m) (power a x) m1
    step1 = cong {f=\y => (mult (mult y (power a x)) m1)} (multCommutative a m)
    step2 = trans step0 step1
    step3 = cong {f=\y => (mult y m1)} (sym (multAssociative m a (power a x)))
    step4 = trans step2 step3
    step5 = cong {f=\y => (mult y m1)} (multCommutative m (mult a (power a x)))
    step6 = trans step4 step5
    step7 = sym (multAssociative (mult a (power a x)) m m1)
    step8 = trans step6 step7
    step9 = trans (sym step8) equiv
    in 
    ((mult m m1) ** step9)

pow_a_divides_pow_b: (a: Nat, b: Nat) -> Divides (power a n) (power b n) -> Divides a b
pow_a_divides_pow_b a b an_div_bn = ?pow_todo


lte_mult_right: (a: Nat, b: Nat) -> Not (b=0) -> a `LTE` (mult a b)
lte_mult_right Z b b_not_0 = lteRefl
lte_mult_right (S k) b b_not_0 = let 
    step0 = lte_mult_right k b b_not_0
    k_less_kplusb = lteAddRight k

    in 
    ?todo_lte


div_less_eq: (a: Nat, b: Nat) -> a `Divides` (S b) -> a `LTE` (S b)
div_less_eq a Z ((S Z) ** am_1) = let 
    a1_eqa = sym $ multOneRightNeutral a
    a_eq_1 = trans a1_eqa am_1
    in
    rewrite a_eq_1 in lteRefl
div_less_eq a x (m ** ax_m_add_1) = ?todo_div

greater_not_div: (a: Nat, b: Nat) -> (S a) `LT` b -> Not $ (S a) `Divides` b
greater_not_div a b sa_lt_b = ?tododo

my_div: (x: Nat, y: Nat) -> (rm ** ((fst rm)*y + (snd rm) = x, LT (snd rm) y))
my_div x y = let 
    q = divNat x y
    r = modNat x y
    rm = (q,r)
    in 
    ?todo_divv