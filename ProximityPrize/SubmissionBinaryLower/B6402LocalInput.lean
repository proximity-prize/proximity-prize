import ProximityPrize.SubmissionBinaryLower.B6402LocalSupport
import ProximityPrize.SubmissionBinaryLower.B6402Moments

/-! The source-degree hypotheses of the exceptional row recursion hold for
the original mixed-degree basis at every site. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402LocalInput
open Polynomial B6401ContactKerD B6401QuotInterp B6402MixedDegree B6402SeedCoordinates B6402QuotientSpace
open B6402PrimarySystem B6402ExceptionalSystem B6402ExceptionalSupport B6402ExceptionalInterpolation B6402LocalSupport
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K : Type*} [Field K] [CharP K 2]

theorem shifted_source {w W s q T : ℕ} (hw : 1<w) (x : K) (y : K[X]) (hy : y.natDegree≤q)
    (u : Global K w W s q T) (j : ℕ) :
    Bounds ((localSource x y u).coeff j) (s+3*j) (W/(w-1)) T := by
  have h := B6402LocalSupport.sum (J:=W/(w-1)) (T:=T) x y q hy (by omega : 0<w) (decode (width q T) u)
  have wt (e : KerDIdx w W s) (hn : decode (width q T) u e≠0) :
      (decode (width q T) u e).natDegree+q*(2*e.1.2.2.1+e.1.2.1)≤T := by
    have hg := decode_with_grade (fun e : KerDIdx w W s => q*grade e.1) T u e hn
    change (decode (width q T) u e).natDegree+q*grade e.1≤T at hg
    have he : 2*e.1.2.2.1+e.1.2.1≤grade e.1 := by unfold grade; omega
    have := Nat.mul_le_mul_left q he; omega
  have wy (e : KerDIdx w W s) (_ : decode (width q T) u e≠0) : 2*e.1.2.2.1+e.1.2.1≤W/(w-1) := by
    have hh := B6402Moments.global_grade_le w W s hw e
    unfold grade at hh; omega
  exact (h wt wy j).mono (by omega) le_rfl le_rfl

theorem factor_series {w WF q H : ℕ} (hw : 0<w) (x : K) (y : K[X]) (hy : y.natDegree≤q)
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (height : mixed q F≤H)
    (ordeg : ∀ i, (F.coeff i).natDegree≤5) :
    Series (localized x y fc) 1 5 H := by
  have h := B6402LocalSupport.sum (J:=5) (T:=H) x y q hy hw fc
  have wt (e : KerDIdx w WF 1) (hn : fc e≠0) : (fc e).natDegree+q*(2*e.1.2.2.1+e.1.2.1)≤H := by
    have hi := coordinate_bound hw fc (heq ▸ height) e hn
    have le := Nat.mul_le_mul_left q (Nat.le_add_right (2*e.1.2.2.1+e.1.2.1) e.1.1)
    omega
  have wy (e : KerDIdx w WF 1) (hn : fc e≠0) : 2*e.1.2.2.1+e.1.2.1≤5 := by
    have hc : coord F e=fc e := heq ▸ coord_sum hw fc e
    have hc' : coord F e≠0 := hc ▸ hn
    have h1 : (F.coeff e.1.1).coeff (2*e.1.2.2.1+e.1.2.1)≠0 := by
      intro hz; apply hc'; simp [coord,hz]
    exact (le_natDegree_of_ne_zero h1).trans (ordeg _)
  exact h wt wy

theorem shifted_factor {w WF q H : ℕ} (hw : 0<w) (x : K) (y : K[X]) (hy : y.natDegree≤q)
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (height : mixed q F≤H)
    (ordeg : ∀ i, (F.coeff i).natDegree≤5) (j : ℕ) :
    Bounds ((localized x y fc).coeff (j+1)) (3*(j+1)) 5 H := by
  exact (factor_series hw x y hy fc F heq height ordeg (j+1)).mono (by omega) le_rfl le_rfl


#print axioms shifted_source
#print axioms shifted_factor
end ProximityPrize.SubmissionBinaryLower.B6402LocalInput
