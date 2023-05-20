-- Creating a DPair (Dependent Pair) with fst -> m and snd -> proof that a * m = b.
Divides: Nat -> Nat -> Type 
Divides a b = (m ** (a*m = b))

-- An example value that shows 2 divides 0 
two_divides_zero: Divides 2 0
two_divides_zero = (0 ** Refl)

-- Basic properties using cong and Refl.
mult_left_eq: (x, y, z: Nat) -> (x=y) -> ((z*x)=(z*y))
mult_left_eq x y z x_eq_y = cong x_eq_y

mult_right_eq: (x, y, z: Nat) -> (x=y) -> ((x*z)=(y*z))
mult_right_eq x y z x_eq_y = rewrite x_eq_y in Refl

x_eq_1_xx_eq_1: (x:Nat) -> (x=1) -> ((x*x) = 1)
x_eq_1_xx_eq_1 x x_eq_1 = rewrite x_eq_1 in Refl

-- n_div_a_div_ab: for all Nat a, b, and n, if n divides a, then n divides a*b.
n_div_a_div_ab: (a: Nat, b: Nat, n: Nat) -> Divides n a -> Divides n (a*b)
n_div_a_div_ab a b n (m ** (nm_a)) = ((m*b) ** trans (multAssociative n m b) (cong {f=\x => x*b} nm_a))


-- Prime type: Given p =/= 1, x a Nat, and x divides p, it must be that x is 1 or x is p.
Prime: Nat -> Type
Prime p = (Not (p=1), (x: Nat) -> Divides x p -> Either (x = 1) (x = p))

-- Coprime
CoPrime: Nat -> Nat -> Type
CoPrime a b = (x: Nat) -> (Divides x a) -> (Divides x b) -> (x=1) 

-- x_divides_xx: Given any Nat x, x divides x squared.
-- Note the use of Refl directly.
x_divides_xx: (x: Nat) -> Divides x (x*x)
x_divides_xx x = (x ** Refl)

-- prev: Given a Nat, find the predecessor. 
-- Pattern matching in Idris allows us to do this (not in Pie)
total
prev: Nat -> Nat 
prev Z = Z
prev (S x) = x

-- sub: Given two Nats x, y, find x - y.
total
sub: Nat -> Nat -> Nat 
sub Z x = x 
sub (S y) x = prev (sub y x)

-- fequiv_prev: Given x = y, deduce that prev x = prev y
-- Direct application of Refl, similar to the definition of cong.
fequiv_prev: (x=y) -> (prev x = prev y)
fequiv_prev Refl = Refl


-- fequiv: Given a function f: a -> b -> c and two pairs of equivalent inputs (x, y) and (xp, yp), we have that (f x y) = (f xp yp)
-- Used trans as in Pie. 
fequiv: (x: a, xp: a, y: b, yp: b, f: a -> b -> c) -> (x=xp) -> (y=yp) -> (f x y) = (f xp yp)
fequiv x xp y yp f x_xp y_yp = trans (cong {f=(`f` y)} x_xp) (cong {f=(f xp)} y_yp)

-- n_divides_a_plus_b and n_divides_a_minus_b: Using fequiv to show properties.
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

-- integral_domain: Proof that Nat forms an integral domain, i,e, given x*y = 0 -> x = 0 or y = 0
-- Note the use of void to handle contradictions.
integral_domain: (x: Nat) -> (y: Nat) -> (x*y=0) -> Either (x=0) (y=0)
integral_domain Z _ _ = Left Refl
integral_domain _ Z _ = Right Refl 
integral_domain (S xp) (S yp) xy_0 = void (SIsNotZ xy_0)

-- eq_zero: Given Nat x and y, x = y implies x - y = 0
-- x_zero_xx_zero, x_one_xx_one
-- Another example of void.
eq_zero: (x: Nat) -> (y: Nat) -> (x=y) -> ((minus x y) = 0)
eq_zero Z Z x_eq_y = Refl
eq_zero (S xp) Z x_eq_y = void (SIsNotZ x_eq_y)
eq_zero Z (S yp) x_eq_y = void (SIsNotZ (sym x_eq_y))
eq_zero (S xp) (S yp) x_eq_y = eq_zero xp yp (fequiv_prev x_eq_y)

x_zero_xx_zero: (x: Nat) -> x=0 -> (x*x) = 0
x_zero_xx_zero Z x_eq_0 = Refl
x_zero_xx_zero (S x) x_eq_0 = void (SIsNotZ x_eq_0)

x_one_xx_one: (x: Nat) -> x=1 -> (x*x) = 1
x_one_xx_one Z x_eq_1 = void (SIsNotZ (sym x_eq_1))
x_one_xx_one (S Z) x_eq_1 = Refl
x_one_xx_one (S (S x)) x_eq_1 = void (SIsNotZ (fequiv_prev x_eq_1))


-- not_eq_zero: Given Nat x and y, and that y < x, we have that x - y =/= 0.
-- Note the use of proving "Not" types.
not_eq_zero: (x: Nat, y: Nat) -> (LT y x) -> Not ((minus x y) = 0)
not_eq_zero Z Z y_less_x = void (succNotLTEzero y_less_x)
not_eq_zero (S xp) Z y_less_x = \minus_eq_zero => void (SIsNotZ minus_eq_zero)
not_eq_zero Z (S yp) y_less_x = void (succNotLTEzero y_less_x)
not_eq_zero (S xp) (S yp) (y_less_x) = not_eq_zero xp yp (fromLteSucc y_less_x)

-- my_cmp: Decide the ordering of Nat inputs x and y.
-- Use of LTE constructors.
my_cmp: (x: Nat, y: Nat) -> Either (x=y) (Either (LT x y) (LT y x))
my_cmp Z Z = Left Refl
my_cmp (S x) Z = Right (Right (LTESucc LTEZero))
my_cmp Z (S y) = Right (Left (LTESucc LTEZero))
my_cmp (S xp) (S yp) = case my_cmp xp yp of 
    Left xp_eq_yp => Left (cong xp_eq_yp)
    Right (Left xp_lt_yp) => Right (Left (LTESucc xp_lt_yp))
    Right (Right yp_lt_xp) => Right (Right (LTESucc yp_lt_xp))


-- cancellation_helper: For all Nat x, y, and z, given that y < x and z*x = z*y, we have that z = 0 or x = y.
-- Helper for cancellation without the requirement of y < x. 
-- Use of multDistributesOverMinusRight rules and let ... in matching. 
cancellation_helper: (x: Nat) -> (y: Nat) -> (z: Nat) -> (LT y x) -> (z*x = z*y) -> Either (z=0) (x=y)
cancellation_helper x y z y_less_x zx_eq_zy = let 
    zx_minus_zy_is_zero = (eq_zero (z*x) (z*y) zx_eq_zy) 
    z_times_x_minus_y_is_zero = trans (multDistributesOverMinusRight z x y) zx_minus_zy_is_zero
    in 
    case integral_domain z (minus x y) z_times_x_minus_y_is_zero of 
        Left z_is_zero => Left z_is_zero
        Right minus_xy_is_zero => void $ (not_eq_zero x y y_less_x) minus_xy_is_zero


-- cancellation function.
-- Usage of my_cmp to integrate the use of cancellation helper.
cancellation: (x: Nat, y: Nat, z: Nat) -> (z*x = z*y) -> Either (z=0) (x=y)
cancellation x y z zx_eq_zy = case my_cmp x y of 
    Left x_eq_y => Right x_eq_y
    Right (Left (x_lt_y)) => case cancellation_helper y x z x_lt_y (sym zx_eq_zy) of 
        Left z_0 => Left z_0 
        Right y_eq_x => Right (sym y_eq_x)
    Right (Right (y_lt_x)) => cancellation_helper x y z y_lt_x zx_eq_zy


-- x_eq_xx_x_zero_or_one: For all Nat x, if x = x*x, then either x = 0 or x = 1.
-- Example application of monads and cancellation.
x_eq_xx_x_zero_or_one : (x : Nat) -> x = x * x -> Either (x = 0) (x = 1)
x_eq_xx_x_zero_or_one x x_eq_xx = sym <$> cancellation 1 x x (trans (multOneRightNeutral x) x_eq_xx)

-- no_prime_is_zero: For all prime p, p =/= 0
no_prime_is_zero: (p: Nat) -> (Prime p) -> Not (p=0)
no_prime_is_zero p (p_not_1, p_is_prime) p_is_zero = case p_is_prime 2 (rewrite p_is_zero in two_divides_zero) of 
        Left two_is_one => let 
            one_is_zero = fequiv_prev two_is_one
            p_is_one = trans (p_is_zero) (sym one_is_zero) in (p_not_1 p_is_one)
        Right y => let 
            one_is_zero = fequiv_prev (trans (sym p_is_zero) (sym y))
            p_is_one = trans (p_is_zero) one_is_zero
            in (p_not_1 p_is_one)

-- x_squared_not_prime: For all Nat x, x^2 is not prime.
x_squared_not_prime: (x: Nat) -> (Not (Prime (x*x)))
x_squared_not_prime x xx_prime = case (snd xx_prime) x (x_divides_xx x) of 
    Left x_eq_1 => ((fst xx_prime) (x_eq_1_xx_eq_1 x x_eq_1))
    Right x_eq_xx => case x_eq_xx_x_zero_or_one x x_eq_xx of 
        Left x_eq_0 => (no_prime_is_zero (x*x) xx_prime) (x_zero_xx_zero x x_eq_0)
        Right x_eq_1 => (fst xx_prime) (x_one_xx_one x x_eq_1)



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

total my_div: (x: Nat, y: Nat) -> Not (y=0) -> (rm ** ((fst rm)*y + (snd rm) = x, LT (snd rm) y))
my_div x Z nz = void $ nz Refl
my_div Z (S yp) _ = ((0, 0) ** (Refl, LTESucc $ LTEZero))
my_div (S xp) (S yp) nz = case my_cmp (S xp) (S yp) of 
    Left x_eq_y => let 
        eq = cong {f=S} (trans (cong {f = (`plus` 0)} (plusZeroRightNeutral yp)) (plusZeroRightNeutral yp))
        in 
        ((1, 0) ** (trans eq (sym x_eq_y), LTESucc $ LTEZero)) 
    Right (Left x_lt_y) => ((0, (S xp)) ** (Refl, x_lt_y))
    Right (Right y_lt_x) => let 
        y_lte_x = lteSuccLeft y_lt_x
        py_lte_px = fromLteSucc y_lte_x
        ((q, r) ** (p1, r_le_y)) = my_div (assert_smaller (S xp) (xp - yp)) (S yp) SIsNotZ
        step0 = minus_cancel (S xp) (S yp) y_lte_x
        step1 = cong {f=\zz => plus zz (mult 1 (S yp))} p1
        step2 = plus_rotate (mult q (S yp)) r (mult 1 (S yp))
        step3 = cong {f=\zz => plus zz r} (multDistributesOverPlusLeft q 1 (S yp))
        step4 = (sym (trans (trans (sym step1) step2) (sym step3)))
        step5 = cong {f=\zz => (plus (minus xp yp) (S zz))} (plusZeroRightNeutral yp)
        step6 = trans (trans step4 step5) step0
        in 
        ((q+1, r) ** (step6, r_le_y))

total lte_lemma: (n: Nat, m: Nat, k: Nat) -> (m=k) -> LTE n m -> LTE n k
lte_lemma _ Z Z eq lt = lt
lte_lemma Z _ _ eq lt = LTEZero
lte_lemma (S np) (S mp) Z eq lt = void $ SIsNotZ eq 
lte_lemma (S np) Z (S kp) eq lt = void $ SIsNotZ (sym eq)
lte_lemma (S np) (S mp) (S kp) eq lt = let 
    rec_case = lte_lemma np mp kp (cong {f=prev} eq) (fromLteSucc lt)
    in 
    LTESucc rec_case


total lte_add_k: (n: Nat, m: Nat, k: Nat) -> LTE n m -> LTE n (m+k)
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

total divisibility_decidable: (a: Nat, b: Nat) -> Not (a=0) -> Either (a `Divides` b) (Not (a `Divides` b))
divisibility_decidable a b a_nz = let 
    ((q, r) ** (p1, p2)) = my_div b a a_nz 
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

total div_tester_from: (p: Nat, l: Nat) -> LTE 3 p -> LTE 2 l -> LT l p -> Either (x ** ((x `Divides` p), LTE 2 x, LT x p)) ((n: Nat) -> (LTE 2 n) -> (LTE n l) -> Not (n `Divides` p))
div_tester_from p Z _ at_two _ = void $ succNotLTEzero at_two
div_tester_from p (S Z) _ at_two _ = void $ succNotLTEzero $ fromLteSucc at_two
div_tester_from p (S (S Z)) at_three at_two at_p = case divisibility_decidable 2 p SIsNotZ of 
    Left does_divide => Left (2 ** (does_divide, at_two, at_p))
    Right does_not_divide => Right $ \cand => \cand_at_least_2 => \cand_at_most_l => \(nm ** pf) => case my_cmp cand 2 of 
        Left is_two => let 
            step0 = cong {f=\zz => mult zz nm} is_two
            in
            does_not_divide (nm ** (trans (sym step0) pf))
        Right (Left less_two) => lt_contradiction cand 2 less_two cand_at_least_2
        Right (Right more_two) => lt_contradiction 2 cand more_two cand_at_most_l
div_tester_from p l@(S (S (S nl))) at_three at_two at_p = case divisibility_decidable (S (S (S nl))) p SIsNotZ of 
    Left does_divide => Left ((S (S (S nl))) ** (does_divide, at_two, at_p))
    Right does_not_divide => case div_tester_from p (S (S nl)) at_three ((LTESucc . LTESucc) LTEZero) (lteSuccLeft at_p) of 
        Left cand => Left cand
        Right func => Right $ \cand => \cand_at_least_2 => \cand_at_most_l => case my_cmp cand (S (S (S nl))) of 
            Left cand_eq_l => \(nm ** pf) => let 
                step0 = cong {f=\zz => mult zz nm} (sym cand_eq_l)
                step1 = trans step0 pf
                in 
                does_not_divide (nm ** step1)
            Right (Left (cand_lq_l)) => func cand cand_at_least_2 (fromLteSucc cand_lq_l)
            Right (Right (cand_gq_l)) => \div => lt_contradiction (S (S (S nl))) cand cand_gq_l cand_at_most_l

geq_p_div: (n: Nat, p: Nat) -> Not (p=0) -> (LT p n) -> Not (n `Divides` p)
geq_p_div n p pnz lt (nm ** pf) = case nzmul_geq n nm of 
    Left is_zero => pnz $ trans (sym pf) is_zero
    Right leq => lt_contradiction p n lt (lte_lemma n (mult n nm) p pf leq)

zero_not_divide_p: (n: Nat, p: Nat) -> (n=0) -> Not (p=0) -> Not (n `Divides` p)
zero_not_divide_p n p nz pnz (nm ** (pf)) = pnz $ trans (sym pf) (cong {f=\zz => mult zz nm} nz)

le_2_zero_one: (n: Nat) -> (LT n 2) -> Either (n=0) (n=1)
le_2_zero_one Z _ = Left Refl
le_2_zero_one (S Z) _ = Right Refl
le_2_zero_one (S (S x)) lt = void $ succNotLTEzero $ (fromLteSucc . fromLteSucc) lt 

lte_succ_nz: (p: Nat) -> LTE (S x) p -> Not (p=0)
lte_succ_nz Z lt _ = succNotLTEzero lt
lte_succ_nz (S x) _ ct = SIsNotZ ct

cmp_two: (n: Nat, l: Nat) -> Either (LT n l) (LTE l n)
cmp_two n l = case my_cmp n l of 
    Left eq => Right $ lte_lemma l l n (sym eq) lteRefl
    Right (Left lq) => Left lq
    Right (Right gq) => Right $ lteSuccLeft gq

dec_int: (n: Nat, l: Nat, r: Nat) -> Either (LT n l) (Either (LTE l n, LT n r) (Either (n=r) (LT r n))) 
dec_int n l r = case cmp_two n l of
    Left c1 => Left c1 
    Right c1 => case my_cmp n r of 
        Left eq_r => Right (Right (Left eq_r))
        Right (Left lq_r) => Right (Left (c1, lq_r))
        Right (Right gq_r) => Right (Right (Right gq_r))

total div_tester: (p: Nat) -> LTE 3 p -> Either (x ** (x `Divides` p, LTE 2 x, LT x p)) ((n: Nat) -> Not (n=1) -> Not (n=p) -> Not (n `Divides` p))
div_tester (S (S (S np))) at_least_three = case div_tester_from (S (S (S np))) (S (S np)) at_least_three (LTESucc (LTESucc LTEZero)) lteRefl of 
    Left cand => Left cand
    Right func => Right $ \cand => \cand_not_one => \cand_not_p => \cand_div_p => case dec_int cand 2 (S (S (S np))) of 
            Left one_or_zero => case le_2_zero_one cand one_or_zero of 
                Left is_zero => zero_not_divide_p cand (S (S (S np))) is_zero (lte_succ_nz (S (S (S np))) at_least_three) cand_div_p
                Right is_one => cand_not_one is_one
            Right (Right (Left is_p)) => cand_not_p is_p
            Right (Right (Right greater_than_p)) => geq_p_div cand (S (S (S np))) SIsNotZ greater_than_p cand_div_p
            Right (Left (at_least_two, less_than_p)) => func cand at_least_two (fromLteSucc less_than_p) cand_div_p 
div_tester (S (S Z)) at_least_three = void $ succNotLTEzero $ (fromLteSucc . fromLteSucc) at_least_three
div_tester (S Z) at_least_three = void $ succNotLTEzero $ fromLteSucc at_least_three
div_tester Z at_least_three = void $ succNotLTEzero $ at_least_three

less_not_equal: (x: Nat, y: Nat) -> LT x y -> Not (x=y)
less_not_equal Z Z lt eq = succNotLTEzero lt
less_not_equal (S x) Z lt eq = SIsNotZ eq
less_not_equal Z (S y) lt eq = SIsNotZ (sym eq)
less_not_equal (S x) (S y) lt eq = less_not_equal x y (fromLteSucc lt) (cong {f=prev} eq) 

two_divisors: (x: Nat) -> x `Divides` 2 -> Either (x=1) (x=2)
two_divisors Z (x ** eq) = void $ SIsNotZ (sym eq)
two_divisors (S Z) (x ** eq) = Left Refl
two_divisors (S (S Z)) (x ** eq) = Right Refl
two_divisors (S (S (S dp))) (x ** eq) = case nzmul_geq (S (S (S dp))) x of
        Left eq_zero => let 
            two_is_zero = trans (sym eq) eq_zero
            in
            void $ SIsNotZ two_is_zero
        Right geq => let 
            lt_cont = lte_lemma (S (S (S dp))) (plus x (plus x (plus x (mult dp x)))) 2 eq geq
            in 
            void $ succNotLTEzero $ (fromLteSucc . fromLteSucc) lt_cont

two_is_prime: Prime 2
two_is_prime = (\eq => SIsNotZ (cong {f=prev} eq), two_divisors)

dec_eq: (n: Nat, m: Nat) -> Either (n=m) (Not (n=m))
dec_eq Z Z = Left Refl
dec_eq (S x) Z = Right SIsNotZ
dec_eq Z (S y) = Right (SIsNotZ . sym)
dec_eq (S x) (S y) = case dec_eq x y of 
    Left eq => Left (cong {f=S} eq)
    Right ne => Right (ne . (cong {f=prev}))

prime_case: (p: Nat) -> Not (p=1) -> ((n: Nat) -> Not (n=1) -> Not (n=p) -> Not (n `Divides` p)) -> Prime p
prime_case p no func = (no, \cand => \cand_div_p => case dec_eq cand 1 of 
    Left is_one => Left is_one
    Right not_one => case dec_eq cand p of 
        Left is_p => Right is_p 
        Right not_p => void $ func cand not_one not_p cand_div_p
)

total prime_decidable_with_factor: (p: Nat) -> (LTE 3 p) -> Either (Prime p) (Not (Prime p), (x ** (x `Divides` p, LTE 2 x, LT x p)))
prime_decidable_with_factor Z at_least_three = void $ succNotLTEzero $ at_least_three
prime_decidable_with_factor (S Z) at_least_three = void $ succNotLTEzero $ fromLteSucc at_least_three
prime_decidable_with_factor (S (S Z)) at_least_three = void $ succNotLTEzero $ (fromLteSucc . fromLteSucc) at_least_three
prime_decidable_with_factor (S (S (S np))) at_least_three = case div_tester (S (S (S np))) at_least_three of 
    Left (divisor ** (divides, at_least_two, less_than_p)) => 
        let 
            dec_func = \(not_one, dec_func) =>  
                    case dec_func divisor divides of 
                        Left is_one => succNotLTEzero . fromLteSucc $ lte_lemma 2 divisor 1 is_one at_least_two
                        Right is_p => less_not_equal divisor (S (S (S np))) less_than_p is_p
        in
            Right (dec_func, (divisor ** (divides, at_least_two, less_than_p)))
    Right func => Left $ prime_case (S (S (S np))) (\zz => SIsNotZ (cong {f=prev} zz)) func

total prime_decidable: (p: Nat) -> Either (Prime p) (Not (Prime p))
prime_decidable Z = Right $ \is_prime => (no_prime_is_zero Z is_prime) Refl
prime_decidable (S Z) = Right $ \(eq_1, _) => eq_1 Refl
prime_decidable (S (S Z)) = Left two_is_prime
prime_decidable (S (S (S np))) = case prime_decidable_with_factor (S (S (S np))) ((LTESucc . LTESucc . LTESucc) LTEZero) of 
    Left is_prime => Left is_prime
    Right (not_prime, _) => Right not_prime
