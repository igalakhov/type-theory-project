module Main 

nat_induction : (P : Nat -> Type) ->             -- Property to show
                (P Z) ->                         -- Base case
                ((k : Nat) -> P k -> P (S k)) -> -- Inductive step
                (x : Nat) ->                     -- Show for all x
                P x
nat_induction P p_Z p_S Z = p_Z
nat_induction P p_Z p_S (S k) = p_S k (nat_induction P p_Z p_S k)


plus_ind : Nat -> Nat -> Nat
plus_ind n m
   = nat_induction (\_ => Nat)
                   m                      -- Base case, plus_ind Z m
                   (\_, k_rec => S k_rec) -- Inductive step plus_ind (S k) m
                                          -- where k_rec = plus_ind k m
                   n

plusZeroEq_ind : (a:Nat) -> a = plus_ind Z a
plusZeroEq_ind a = nat_induction (\x => x = plus_ind Z x)
                                Refl
                                (\k, k_rec => cong (k_rec))
                                a

-- SplusEqplusS : (a:Nat) -> (b:Nat) -> S (plus' a b) = plus' a (S b)
-- SplusEqplusS Z _ = Refl
-- SplusEqplusS (S a) b = cong (SplusEqplusS a b)

main : IO ()
main = do
    putStrLn (show (plus_ind 3 4)) 


