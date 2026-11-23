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







end FadicGate
