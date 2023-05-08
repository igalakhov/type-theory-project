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
data Nat =
    ||| Zero
    Z |
    ||| Successor
    S Nat

||| 1. +
||| Add two natural numbers.
||| @ n the number to case-split on
||| @ m the other number
plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)

||| 2. +0=

plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = Refl

plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) = rewrite plusZeroRightNeutral n in Refl

||| 3. add1+=+add1
plusSuccRightSucc : (left, right : Nat) -> S (left + right) = left + (S right)
plusSuccRightSucc Z _ = Refl
plusSuccRightSucc (S left) right = rewrite plusSuccRightSucc left right in Refl

||| 4. comm+

plusCommutative : (left, right : Nat) -> left + right = right + left
plusCommutative Z right = rewrite plusZeroRightNeutral right in Refl
plusCommutative (S left) right =
  rewrite plusCommutative left right in
    rewrite plusSuccRightSucc right left in
      Refl

||| 5. assoc+
plusAssociative : (left, centre, right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z _ _ = Refl
plusAssociative (S left) centre right =
  rewrite plusAssociative left centre right in Refl

||| 6. *
mult : Nat -> Nat -> Nat
mult Z right        = Z
mult (S left) right = plus right $ mult left right

||| 7. *0=0
multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero _ = Refl

multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

||| 8. *add1=+*
multRightSuccPlus : (left, right : Nat) ->
    left * (S right) = left + (left * right)
multRightSuccPlus Z _ = Refl
multRightSuccPlus (S left) right =
  rewrite multRightSuccPlus left right in
  rewrite plusAssociative left right (left * right) in
  rewrite plusAssociative right left (left * right) in
  rewrite plusCommutative right left in
    Refl
  
multLeftSuccPlus : (left, right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus _ _ = Refl

||| 9. comm*
multCommutative : (left, right : Nat) -> left * right = right * left
multCommutative Z right = rewrite multZeroRightZero right in Refl
multCommutative (S left) right =
  rewrite multCommutative left right in
  rewrite multRightSuccPlus right left in
    Refl

||| 10. distr+*
multDistributesOverPlusLeft : (left, centre, right : Nat) ->
    (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z _ _ = Refl
multDistributesOverPlusLeft (S k) centre right =
  rewrite multDistributesOverPlusLeft k centre right in
      Refl

||| 11. distr*+
multDistributesOverPlusRight : (left, centre, right : Nat) ->
    left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight left centre right =
  rewrite multCommutative left (centre + right) in
    rewrite multCommutative left centre in
      rewrite multCommutative left right in
multDistributesOverPlusLeft centre right left

||| 12. assoc*
multAssociative : (left, centre, right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z _ _ = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    rewrite inductiveHypothesis in
      rewrite multDistributesOverPlusLeft centre (mult left centre) right in
        Refl