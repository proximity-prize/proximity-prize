import ProximityPrize.SubmissionLower.FadicNat

set_option Elab.async false

/-!
# Kernel-raw evaluator

The same evaluation chain as `FadicNat`, written with the primitive `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.ble` and `cond`, which the kernel reduces on literals
without unfolding any instance.
-/

set_option autoImplicit false

namespace FadicGate

def rMin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b
def rMax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

def rDenomQR (q r : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add 1 (Nat.div (Nat.mul r (Nat.add r 1)) 2))
      (Nat.mul q (Nat.add (Nat.add 22 (Nat.mul 7 r)) (Nat.div (Nat.mul r (Nat.sub r 1)) 2))))
    (Nat.mul (Nat.add 57 (Nat.mul 6 r)) (Nat.div (Nat.mul q (Nat.sub q 1)) 2)))
    (Nat.mul (Nat.mul (Nat.mul 6 q) (Nat.sub q 1)) (Nat.sub q 2))

def rDenom (n : ℕ) : ℕ := rDenomQR (Nat.div n 6) (Nat.mod n 6)

def rDenomSub (v k : ℕ) : ℕ := cond (Nat.ble k v) (rDenom (Nat.sub v k)) 0

def rCumAux (d v : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (Nat.add (Nat.add (rDenom v) (rDenomSub v (Nat.add (Nat.mul 2 d) 3)))
      (rDenomSub v (Nat.add (Nat.mul 2 d) 4))) (rDenomSub v (Nat.add (Nat.mul 2 d) 5)))
    (Nat.add (Nat.add (Nat.add (rDenomSub v (Nat.add d 1)) (rDenomSub v (Nat.add d 2)))
      (rDenomSub v (Nat.add d 3))) (rDenomSub v (Nat.add (Nat.mul 3 d) 6)))

def rCumulative (d u : ℕ) : ℕ := rCumAux d (rMin u (Nat.mul 3 d))

def rCapped (d u t : ℕ) : ℕ :=
  Nat.sub (rCumulative d u)
    (cond (Nat.ble (Nat.mul 3 (Nat.add t 1)) u)
      (cond (Nat.ble (Nat.add t 1) d)
        (rCumulative (Nat.sub d (Nat.add t 1)) (Nat.sub u (Nat.mul 3 (Nat.add t 1)))) 0) 0)



def rPrefix (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (rPrefix f n) (f n)

def rFlatLo (B J : ℕ) : ℕ := rMin J (Nat.add B 1)

def rFlatHi (B J Θ : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 25 J) Θ)
    (rMax (rFlatLo B J) (rMin (Nat.add B 1) (Nat.add (Nat.div (Nat.sub Θ (Nat.mul 25 J)) 26) 1)))
    (rFlatLo B J)













end FadicGate
