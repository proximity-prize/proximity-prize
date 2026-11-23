import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AJ
import ProximityPrize.SubmissionLower.AZ
import ProximityPrize.SubmissionLower.B0
import ProximityPrize.SubmissionLower.DR
import ProximityPrize.SubmissionLower.Z5h1PTd
import ProximityPrize.SubmissionLower.ZO2xefe
import ProximityPrize.SubmissionLower.ZS2Jire
set_option Elab.async false
set_option autoImplicit true
section
namespace aeZ
open bu
def cut (a f :ℕ) :ℕ :=
 if f=7 then 38+min (a/2) (6-(a+1)/2)
 else 46+min ((a+1)/2) (5-a/2) - f
noncomputable section
end
end aeZ
end
section
namespace aSp
open bu MvPolynomial





open private nY from ProximityPrize.SubmissionLower.C0


noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem aEI {s u k :ℕ} (h:s+u<k) :
    nY ((1+Polynomial.X)^s*(1-Polynomial.X)^u:Polynomial Ground) k=0:= by
  rw [nY,Polynomial.coeff_eq_zero_of_natDegree_lt,mul_zero]
  calc
    _≤ s*(1+Polynomial.X:Polynomial Ground).natDegree +
        u*(1-Polynomial.X:Polynomial Ground).natDegree :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add
        (Polynomial.natDegree_pow_le ..) (Polynomial.natDegree_pow_le ..))
    _≤ s+u:= by
      have hp: (1+Polynomial.X:Polynomial Ground).natDegree≤1 :=
        (Polynomial.natDegree_add_le 1 Polynomial.X).trans (by simp)
      have hm: (1-Polynomial.X:Polynomial Ground).natDegree≤1 :=
        (Polynomial.natDegree_sub_le 1 Polynomial.X).trans (by simp)
      simpa using Nat.add_le_add (Nat.mul_le_mul_left s hp) (Nat.mul_le_mul_left u hm)
    _<k :=h
end
end aSp
end
