import ProximityPrize.SubmissionBinaryLower.P64C6Finite

/-!
# Positive normal defect for a forced curve

If the flat auxiliary count is strict and its bias on a curve is positive,
a nonpositive normal defect would force arbitrarily large resultant order.
One finite order exceeding the degree bound gives the contradiction.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Positive

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Boxes P64C6Finite
  BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem positive_defect_of_dimension (R : Tri) (hirr : Irreducible R)
    (D w W q e d : ℕ) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R) (hde : d ≤ e)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q) (s : ι → ℕ)
    (hdim : (∑ i, (conditions (s i) q e).card) < (auxiliary D W q e R.natDegree).card +
      ∑ i, (conditions (s i - lineOrd R (ω i) (y i)) q (e - d)).card)
    (z : F) (P : F[X]) (A : Finset ι) (hP : P.natDegree ≤ D)
    (hcurve : triEval R z P = 0) (hderiv : derivativeAlong R P z ≠ 0)
    (hμ : ∀ i ∈ A, 1 ≤ lineOrd R (ω i) (y i))
    (hmatch : ∀ i ∈ A, P.eval (ω i) = (y i).eval z)
    (hbias : (W : ℤ) < ∑ i ∈ A, (s i : ℤ)) :
    0 < (w : ℤ) - D - ∑ i ∈ A, ((lineOrd R (ω i) (y i) - 1 : ℕ) : ℤ) := by
  classical
  by_contra hn
  have hnonpos : (w : ℤ) - D - ∑ i ∈ A, ((lineOrd R (ω i) (y i) - 1 : ℕ) : ℤ) ≤ 0 :=
    le_of_not_gt hn
  let B := (R.natDegree - 1) * d + R.natDegree * e
  have hc := forced_orders_of_dimension R hirr D w W q e d (B + 1) hRw hRyz hde
    ω y hy s hdim ({z} : Finset F) (fun _ => P) (fun _ => A) (fun _ => B + 1)
    (fun _ _ => hP) (fun v hv => ?_) (fun v hv => ?_)
    (fun _ _ => by omega) (fun _ _ => hμ) (fun v hv => ?_) (fun _ _ ρ _ => ?_)
  · have hx : B + 1 ≤ B := by simpa [B] using hc
    omega
  · have hz : v = z := Finset.mem_singleton.mp hv
    simpa [hz] using hcurve
  · have hz : v = z := Finset.mem_singleton.mp hv
    simpa [hz] using hderiv
  · have hz : v = z := Finset.mem_singleton.mp hv
    simpa [hz] using hmatch
  · have hm : 2 * (ρ : ℤ) *
        ((w : ℤ) - D - ∑ i ∈ A, ((lineOrd R (ω i) (y i) - 1 : ℕ) : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
    omega

end P64C6Positive
end ProximityPrize.SubmissionBinaryLower
