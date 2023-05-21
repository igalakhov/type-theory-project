module Prelude.Nat

import Builtins

-- import Prelude.Algebra
-- import Prelude.Basics
-- import Prelude.Bool
-- import Prelude.Cast
-- import Prelude.Interfaces
-- import Prelude.Uninhabited

-- %access public export
-- %default total

||| Natural numbers: unbounded, unsigned integers which can be pattern
||| matched.
data Nat_Num =
    ||| Zero
    Zero |
    ||| Successor
    Succ Nat_Num

||| Convert an Integer to a Nat, mapping negative numbers to 0
fromIntegerNatNum : Integer -> Nat_Num
fromIntegerNatNum 0 = Zero
fromIntegerNatNum n =
  if (n > 0) then
    Succ (fromIntegerNatNum (assert_smaller n (n - 1)))
  else
    Zero

-- 1. +
||| Add two natural numbers.
||| @ n the number to case-split on
||| @ m the other number
Plus : (n, m : Nat_Num) -> Nat_Num
Plus Zero right        = right
Plus (Succ left) right = Succ (Plus left right)

Mult : Nat_Num -> Nat_Num -> Nat_Num
Mult Zero right        = Zero
Mult (Succ left) right = Plus right $ Mult left right


Eq Nat_Num where 
  Zero == Zero = True
  (Succ val) == (Succ otherVal) = val == otherVal
  _ == _ = False

-- Cast Nat Integer where
--   cast = toIntegerNat

Ord Nat_Num where
  compare Zero Zero         = EQ
  compare Zero (Succ k)     = LT
  compare (Succ k) Zero     = GT
  compare (Succ x) (Succ y) = compare x y

Num Nat_Num where
  (+) = Plus
  (*) = Mult
  fromInteger = fromIntegerNatNum



--2. +0=
-- PUT THIS IN PRESENTATION..

total
plus_zero_left : (right : Nat_Num) -> (Plus 0 right) = right
plus_zero_left n = Refl

total
plus_zero_right : (left : Nat_Num) -> (Plus left 0) = left
plus_zero_right Zero = Refl
plus_zero_right (Succ n) = rewrite plus_zero_right n in Refl

--3. add1+=+add1
add1_plus_equal_plus_add1 : (left, right : Nat_Num) -> Succ (left + right) = left + (Succ right)
add1_plus_equal_plus_add1 Zero _ = Refl
add1_plus_equal_plus_add1 (Succ left) right = rewrite add1_plus_equal_plus_add1 left right in Refl

-- ||| 4. comm+

comm_plus : (left, right : Nat_Num) -> left + right = right + left
comm_plus Zero right = rewrite plus_zero_right right in Refl
comm_plus (Succ left) right =
  rewrite comm_plus left right in
    rewrite add1_plus_equal_plus_add1 right left in
      Refl

-- ||| 5. assoc+
associative_plus : (left, centre, right : Nat_Num) ->
  left + (centre + right) = (left + centre) + right
associative_plus Zero _ _ = Refl
associative_plus (Succ left) centre right =
  rewrite associative_plus left centre right in Refl


-- 7. *0=0
mult_zero_left : (right : Nat_Num) -> Zero * right = Zero
mult_zero_left _ = Refl

mult_zero_right : (left : Nat_Num) -> left * Zero = Zero
mult_zero_right Zero        = Refl
mult_zero_right (Succ left) = mult_zero_right left

-- ||| 8. *add1=+*
mult_add1_equal_add1_mult_right : (left, right : Nat_Num) ->
    left * (Succ right) = left + (left * right)
mult_add1_equal_add1_mult_right Zero _ = Refl
mult_add1_equal_add1_mult_right (Succ left) right =
  rewrite mult_add1_equal_add1_mult_right left right in
  rewrite associative_plus left right (left * right) in
  rewrite associative_plus right left (left * right) in
  rewrite comm_plus right left in
    Refl
  
mult_add1_equal_add1_mult_left : (left, right : Nat_Num) ->
  (Succ left) * right = right + (left * right)
mult_add1_equal_add1_mult_left _ _ = Refl

-- 9. comm*
comm_mult : (left, right : Nat_Num) -> left * right = right * left
comm_mult Zero right = rewrite mult_zero_right right in Refl
comm_mult (Succ left) right =
  rewrite comm_mult left right in
  rewrite mult_add1_equal_add1_mult_right right left in
    Refl

-- ||| 10. distr+*
distr_left : (left, centre, right : Nat_Num) ->
  (left + centre) * right = (left * right) + (centre * right)
distr_left Zero _ _ = Refl
distr_left (Succ k) centre right =
  rewrite distr_left k centre right in
    rewrite associative_plus right (k * right) (centre * right) in
      Refl

-- 11. distr*+
-- distr_right : (left, centre, right : Nat_Num) ->
distr_right : (left, centre, right : Nat_Num) ->
  left * (centre + right) = (left * centre) + (left * right)
distr_right left centre right =
  rewrite comm_mult left (centre + right) in
    rewrite comm_mult left centre in
      rewrite comm_mult left right in
  distr_right centre right left


-- 12. assoc*
assoc_mult : (left, centre, right : Nat_Num) ->
  left * (centre * right) = (left * centre) * right
assoc_mult Zero _ _ = Refl
assoc_mult (Succ left) centre right =
  let inductiveHypothesis = assoc_mult left centre right in
    rewrite inductiveHypothesis in
      rewrite distr_left centre (left * centre) right in
        Refl
