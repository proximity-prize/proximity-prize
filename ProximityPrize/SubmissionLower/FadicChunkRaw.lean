import ProximityPrize.SubmissionLower.FadicChunk
import ProximityPrize.SubmissionLower.FadicRaw

/-!
# Kernel-raw evaluator of the chunked certificate
-/

set_option autoImplicit false

namespace FadicGate

def rSegLo (base h k : ℕ) : ℕ := Nat.add base (Nat.mul h k)
def rSegHi (base h m k : ℕ) : ℕ :=
  Nat.add base (rMin (Nat.sub (Nat.add (Nat.mul h k) h) 1) (Nat.sub m 1))

def rLowSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 hi) Θ)
    (rCapped (rMin lo (Nat.div (Nat.sub Θ (Nat.mul 26 hi)) 25)) J T) 0

def rHighSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 lo) Θ)
    (rCapped (rMin hi (Nat.div (Nat.sub Θ (Nat.mul 26 lo)) 25)) J T) 0

def rLowSeg (J T Θ base h m k : ℕ) : ℕ := rLowSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)
def rHighSeg (J T Θ base h m k : ℕ) : ℕ := rHighSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)

def rSegSumLow (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rLowSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rLowSeg J T Θ base h m (Nat.div m h)))

def rSegSumHigh (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rHighSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rHighSeg J T Θ base h m (Nat.div m h)))

def rFastLowAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumLow J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumLow J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastHighAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumHigh J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumHigh J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastLow (B J T Θ h : ℕ) : ℕ := rFastLowAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)
def rFastHigh (B J T Θ h : ℕ) : ℕ := rFastHighAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)

def rMultHighAux (h σt bl jl r a B J Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble (Nat.mul 26 bl) Θ)
    (rFastHigh (Nat.sub B bl) (Nat.sub J jl) (Nat.mul (Nat.sub r a) σt) (Nat.sub Θ (Nat.mul 26 bl)) h) 0

def rDepthLowAux (h σt bl jl r a B J Θ : ℕ) : ℕ :=
  Nat.sub (rFastLow B J (Nat.mul (Nat.sub r a) σt) Θ h) (rMultHighAux h σt bl jl r a B J Θ)

def rDepthLow (h σb σj σt bl bh jl jh r a : ℕ) : ℕ :=
  cond (rDepthOK bh jh r a)
    (rDepthLowAux h σt bl jl r a (rDepthB σb bh r a) (rDepthJ σj jh r a) (rDepthΘ bh jh a)) 0

def rFadicLow (h σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  rPrefix (rDepthLow h σb σj σt bl bh jl jh r) (Nat.add (Nat.div r 3) 1)

def rPlainLow (h σb σj σt r : ℕ) : ℕ :=
  rFastLow (rMin (Nat.mul r σb) 4012) (rMin (Nat.mul r σj) 1650) (Nat.mul r σt) 131312 h

def rCertLoss (S h σb σj σt bl bh jl jh i : ℕ) : ℕ :=
  cond (rIsFull σb σj σt (Nat.add i 1)) 0
    (Nat.sub S (rMax (rPlainLow h σb σj σt (Nat.add i 1)) (rFadicLow h σb σj σt bl bh jl jh (Nat.add i 1))))

end FadicGate
