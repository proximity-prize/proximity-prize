import ProximityPrize.SubmissionLower.FadicNat

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

def rPad (Θ q : ℕ) : ℕ := rMin q (Nat.div (Nat.sub Θ (Nat.mul 26 q)) 25)

def rTerm (J T Θ q : ℕ) : ℕ := cond (Nat.ble (Nat.mul 26 q) Θ) (rCapped (rPad Θ q) J T) 0

def rPrefix (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (rPrefix f n) (f n)

def rFlatLo (B J : ℕ) : ℕ := rMin J (Nat.add B 1)

def rFlatHi (B J Θ : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 25 J) Θ)
    (rMax (rFlatLo B J) (rMin (Nat.add B 1) (Nat.add (Nat.div (Nat.sub Θ (Nat.mul 25 J)) 26) 1)))
    (rFlatLo B J)

def rCountAux (B J T Θ lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rPrefix (rTerm J T Θ) lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rPrefix (fun i => rTerm J T Θ (Nat.add hi i)) (Nat.sub (Nat.add B 1) hi))

def rCount (B J T Θ : ℕ) : ℕ := rCountAux B J T Θ (rFlatLo B J) (rFlatHi B J Θ)

def rDepthB (σb xb r a : ℕ) : ℕ := rMin (Nat.mul (Nat.sub r a) σb) (Nat.sub 4012 (Nat.mul a xb))
def rDepthJ (σj xj r a : ℕ) : ℕ := rMin (Nat.mul (Nat.sub r a) σj) (Nat.sub 1650 (Nat.mul a xj))
def rDepthΘ (xb xj a : ℕ) : ℕ :=
  Nat.sub 131312 (Nat.mul a (Nat.add (Nat.mul 26 xb) (Nat.mul 25 xj)))

def rDepthOK (xb xj r a : ℕ) : Bool :=
  (Nat.ble (Nat.mul 3 a) r && Nat.ble (Nat.add a 1) r) &&
    (Nat.ble (Nat.mul a xb) 4012 && Nat.ble (Nat.mul a xj) 1650 &&
      Nat.ble (Nat.mul a (Nat.add (Nat.mul 26 xb) (Nat.mul 25 xj))) 131312)

def rMultAux (σt bl jl r a B J Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble (Nat.mul 26 bl) Θ)
    (rCount (Nat.sub B bl) (Nat.sub J jl) (Nat.mul (Nat.sub r a) σt) (Nat.sub Θ (Nat.mul 26 bl))) 0

def rDepthAux (σt bl jl r a B J Θ : ℕ) : ℕ :=
  Nat.sub (rCount B J (Nat.mul (Nat.sub r a) σt) Θ) (rMultAux σt bl jl r a B J Θ)

def rDepthDim (σb σj σt bl bh jl jh r a : ℕ) : ℕ :=
  cond (rDepthOK bh jh r a)
    (rDepthAux σt bl jl r a (rDepthB σb bh r a) (rDepthJ σj jh r a) (rDepthΘ bh jh a)) 0

def rFadicDim (σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  rPrefix (rDepthDim σb σj σt bl bh jl jh r) (Nat.add (Nat.div r 3) 1)

def rPlainDim (σb σj σt r : ℕ) : ℕ :=
  rCount (rMin (Nat.mul r σb) 4012) (rMin (Nat.mul r σj) 1650) (Nat.mul r σt) 131312

def rIsFull (σb σj σt r : ℕ) : Bool :=
  Nat.ble 4012 (Nat.mul r σb) && Nat.ble 1650 (Nat.mul r σj) && Nat.ble 550 (Nat.mul r σt)

def rGateDim (S σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  cond (rIsFull σb σj σt r) S (rMax (rPlainDim σb σj σt r) (rFadicDim σb σj σt bl bh jl jh r))

def rRowLoss (S σb σj σt bl bh jl jh i : ℕ) : ℕ :=
  Nat.sub S (rGateDim S σb σj σt bl bh jl jh (Nat.add i 1))

end FadicGate
