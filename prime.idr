Divides: Nat -> Nat -> Type 
Divides a b = (m ** (a*m = b))

Prime: Nat -> Type
Prime p = (Not (p=1), (x: Nat) -> Divides x p -> Either (x = 1) (x = p))

CoPrime: Nat -> Nat -> Type
CoPrime a b = (x: Nat) -> (Divides x a) -> (Divides x b) -> (x=1) 

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

lt_implies_lte: (a: Nat, b: Nat) -> LT a b -> LTE a b
lt_implies_lte = ?todo_lt

nonzero_product: (a: Nat, b: Nat) -> (a*b = S(_)) -> (a = (S _), b = (S _))

mult_lte: (a: Nat, b: Nat) -> (a*S(_) = b) -> LTE a b

lt_cont: (a: Nat, b: Nat) -> LTE a b -> LT b a -> Void

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

minus_cancel: (x: Nat, y: Nat) -> LTE y x -> ((x-y)+y = x)
minus_cancel Z Z _ = Refl
minus_cancel Z (S yp) y_leq_x = void (succNotLTEzero y_leq_x)
minus_cancel x Z y_leq_x = let 
    step0 = plusZeroRightNeutral (minus x 0)
    step1 = minusZeroRight x
    in 
    trans step0 step1
minus_cancel (S xp) (S yp) y_leq_x = let
    rec_eq = minus_cancel xp yp (fromLteSucc y_leq_x)
    step0 = cong {f=S} rec_eq
    step1 = sym $ plusSuccRightSucc (minus xp yp) yp
    in 
    trans step1 step0

plus_rotate: (x: Nat, y: Nat, z: Nat) -> (x+y)+z = (x+z)+y
plus_rotate x y z = let 
    step0 = cong {f=\zz=>(x+zz)} (plusCommutative y z)
    step1 = sym (plusAssociative x y z)
    step2 = plusAssociative x z y
    in 
    trans (trans step1 step0) step2

my_div: (x: Nat, y: Nat) -> (rm ** ((fst rm)*y + (snd rm) = x, LT (snd rm) y))
my_div Z (S yp) = ((0, 0) ** (Refl, LTESucc $ LTEZero))
my_div (S xp) (S yp) = case my_cmp (S xp) (S yp) of 
    Left x_eq_y => let 
        eq = cong {f=S} (trans (cong {f = (`plus` 0)} (plusZeroRightNeutral yp)) (plusZeroRightNeutral yp))
        in 
        ((1, 0) ** (trans eq (sym x_eq_y), LTESucc $ LTEZero)) 
    Right (Left x_lt_y) => ((0, (S xp)) ** (Refl, x_lt_y))
    Right (Right y_lt_x) => let 
        y_lte_x = lteSuccLeft y_lt_x
        ((q, r) ** (p1, r_le_y)) = my_div ((S xp) - (S yp)) (S yp)
        step0 = minus_cancel (S xp) (S yp) y_lte_x
        step1 = cong {f=\zz => plus zz (mult 1 (S yp))} p1
        step2 = plus_rotate (mult q (S yp)) r (mult 1 (S yp))
        step3 = cong {f=\zz => plus zz r} (multDistributesOverPlusLeft q 1 (S yp))
        step4 = (sym (trans (trans (sym step1) step2) (sym step3)))
        step5 = cong {f=\zz => (plus (minus xp yp) (S zz))} (plusZeroRightNeutral yp)
        step6 = trans (trans step4 step5) step0
        in 
        ((q+1, r) ** (step6, r_le_y))

lte_lemma: (n: Nat, m: Nat, k: Nat) -> (m=k) -> LTE n m -> LTE n k
lte_lemma _ Z Z eq lt = lt
lte_lemma (S np) (S mp) Z eq lt = void $ SIsNotZ eq 
lte_lemma (S np) Z (S kp) eq lt = void $ SIsNotZ (sym eq)
lte_lemma (S np) (S mp) (S kp) eq lt = let 
    rec_case = lte_lemma np mp kp (cong {f=prev} eq) (fromLteSucc lt)
    in 
    LTESucc rec_case


lte_add_k: (n: Nat, m: Nat, k: Nat) -> LTE n m -> LTE n (m+k)
lte_add_k n m Z lt = lte_lemma n m (plus m 0) (sym (plusZeroRightNeutral m)) lt
lte_add_k n m (S kp) lt = let 
    rec_case = lteSuccRight $ lte_add_k n m kp lt 
    eq = plusSuccRightSucc m kp
    in 
    lte_lemma n (S (plus m kp)) (plus m (S kp)) eq rec_case 

lte_mul_succ: (n: Nat, m: Nat) -> LTE n (n*m) -> LTE n (n*(S m))
lte_mul_succ n m lt = let 
    add_k_eq = lte_add_k n (n*m) n lt
    step0 = multRightSuccPlus n m
    step1 = plusCommutative n (mult n m)
    step2 = sym $ trans step0 step1
    in 
    lte_lemma n (plus (mult n m) n) (mult n (S m)) step2 add_k_eq

lte_mul: (n: Nat, m: Nat) -> LTE n (n*(S m))
lte_mul n Z = lte_lemma n n (mult n 1) (sym (multOneRightNeutral n)) lteRefl
lte_mul n (S mp) = lte_mul_succ n (S mp) (lte_mul n mp)

nzmul_geq: (n: Nat, m: Nat) -> Either ((n*m)=0) (LTE n (n*m))
nzmul_geq n Z = Left (multZeroRightZero n)
nzmul_geq n (S mp) = Right (lte_mul n mp)

lte_equal: (n: Nat, m: Nat) -> (n=m) -> LTE n m
lte_equal Z Z eq = LTEZero
lte_equal (S np) Z eq = void (SIsNotZ eq)
lte_equal Z (S mp) eq = void (SIsNotZ (sym eq))
lte_equal (S np) (S mp) eq = LTESucc (lte_equal np mp (cong {f=prev} eq))

lt_contradiction: (n: Nat, m: Nat) -> LT n m -> LTE m n -> Void
lt_contradiction Z Z lt lte = succNotLTEzero lt
lt_contradiction (S np) Z lt lte = succNotLTEzero lt
lt_contradiction Z (S mp) lt lte = succNotLTEzero lte 
lt_contradiction (S np) (S mp) lt lte = lt_contradiction np mp (fromLteSucc lt) (fromLteSucc lte)

decide_zero: (n: Nat) -> Either (n=0) ((n=0) -> Void)
decide_zero Z = Left Refl 
decide_zero (S x) = Right SIsNotZ

divisibility_decidable: (a: Nat, b: Nat) -> Either (a `Divides` b) (Not (a `Divides` b))
divisibility_decidable a b = let 
    ((q, r) ** (p1, p2)) = my_div b a 
    in 
    case (decide_zero r) of 
        Left (r_zero) => let 
            step0 = cong {f=\zz => plus (mult q a) zz} r_zero
            step1 = plusZeroRightNeutral (mult q a)
            step2 = sym (trans step0 step1)
            step3 = trans step2 p1
            step4 = trans (multCommutative a q) step3
            in 
            Left (q ** step4)
        Right (r_nonzero) => Right $ \pf => let 
            (m ** am_b) = pf 
            step0 = trans p1 (sym am_b)
            step1 = cong {f=\zz => minus zz ((mult q a) + 0)} step0
            step2 = plusMinusLeftCancel (mult q a) r 0
            step3 = trans (sym step1) step2
            step4 = trans step3 (minusZeroRight r)
            step5 = cong {f=\zz=> (minus (mult a m) zz)} (plusZeroRightNeutral (mult q a))
            step6 = trans (sym step5) step4
            step7 = cong {f=\zz=> minus (mult a m) zz} (multCommutative q a)
            step8 = trans (sym step7) step6
            step9 = multDistributesOverMinusRight a m q
            step10 = trans step9 step8 -- a*(m-q) = r1
            in 
                case nzmul_geq a (minus m q) of 
                    Left prod_zr => let 
                        r_is_zero = trans (sym step10) prod_zr 
                        in 
                        r_nonzero r_is_zero
                    Right a_leq_prod => let 
                        prod_leq_r = lte_equal (mult a (minus m q)) r step10
                        a_leq_r = lteTransitive a_leq_prod prod_leq_r
                        in 
                        lt_contradiction r a p2 a_leq_r

-- r1 = am - qa
-- aq - am = r1 
-- a(q-m) = r1