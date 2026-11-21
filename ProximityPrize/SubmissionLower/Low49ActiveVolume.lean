import ProximityPrize.SubmissionLower.Low49ActiveCount
import ProximityPrize.SubmissionLower.Low48BentVolume

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Low49ActiveVolume
open Finset Polynomial MvPolynomial
open Low48BentLattice (Cap Scale latticePoints lattice_zero)
open Low49ActiveLattice (Fits points)
open Low49ActiveCount (sliceLoss clipped_count)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4_3 (monomial_hilbert_count)
open private latticePolynomial latticePolynomial_eval
  from ProximityPrize.SubmissionLower.Low48BentVolume
open scoped BigOperators Pointwise
noncomputable section

theorem fits_scale {a : Cap} {c : ℕ} (ha : Fits a c) (n : ℕ) :
    Fits (Scale n a) (n*c) := by
  obtain ⟨hb,hj,hc,ht,hh,he⟩ := ha
  have hEven : n*c%2=0 := by rw [Nat.mul_mod]; simp [he]
  refine ⟨?_,?_,?_,?_,?_,hEven⟩
  all_goals first
    | simpa only [Scale,Shape.scale,Nat.mul_add] using Nat.mul_le_mul_left n hb
    | simpa only [Scale,Shape.scale,Nat.mul_left_comm n 3] using Nat.mul_le_mul_left n hj
    | simpa only [Scale,Shape.scale,Nat.mul_left_comm n 2] using Nat.mul_le_mul_left n hc
    | simpa only [Scale,Shape.scale,Nat.mul_add,Nat.mul_left_comm n 2] using Nat.mul_le_mul_left n ht
    | simpa only [Scale,Shape.scale,Nat.mul_left_comm n 2] using Nat.mul_le_mul_left n hh

theorem old_chamber {a : Cap} {c : ℕ} (ha : Fits a c) : Low48BentLattice.Chamber a := by
  obtain ⟨hb,hj,hc,ht,hh,_⟩ := ha
  exact ⟨by omega,hj,by omega⟩

private theorem zero_mem (a : Cap) (c : ℕ) (ha : Fits a c) : 0∈points a c := by
  refine ⟨Low48BentLattice.zero_mem a,?_⟩
  unfold Low49ActiveLattice.Active
  have := ha.1
  have := ha.2.2.1
  simp
  omega

theorem point_zero : points (⟨0,0,0⟩,0) 0 = 0 := by
  ext m
  unfold points
  rw [Set.mem_ofPred_eq, lattice_zero]
  simp only [Set.mem_zero, Nat.mul_zero, Nat.add_zero]
  constructor
  · exact And.left
  · rintro rfl
    simp [Low49ActiveLattice.Active]

theorem point_scale (a : Cap) (c : ℕ) (ha : Fits a c) (n : ℕ) :
    n • points a c = points (Scale n a) (n*c) := by
  induction n with
  | zero => simpa [Scale,Shape.scale] using point_zero.symm
  | succ n ih =>
    rw [succ_nsmul, ih, Low49ActiveLattice.add (fits_scale ha n) ha]
    cases a
    simp [Low48BentLattice.Add, Scale, Shape.scale, Shape.plus, Nat.succ_mul]

def sumLoss (c n : ℚ) : ℚ :=
  let f : ℚ→ℚ := fun h => sliceLoss (c-h)
  n*f 0+n*(n-1)/2*(f 1-f 0)+n*(n-1)*(n-2)/6*(f 2-2*f 1+f 0)+
    n*(n-1)*(n-2)*(n-3)/24*(f 3-3*f 2+3*f 1-f 0)+
    n*(n-1)*(n-2)*(n-3)*(n-4)/120*(f 4-4*f 3+6*f 2-4*f 1+f 0)

theorem sum_loss (c : ℚ) (n : ℕ) :
    ∑ h ∈ range n, sliceLoss (c - h) = sumLoss c n := by
  induction n with
  | zero => simp [sumLoss]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold sumLoss sliceLoss
    ring

private def coeff1 (c h : ℚ) : ℚ :=
  (2/3) * c
    - (2/15) * h

private def coeff2 (c h : ℚ) : ℚ :=
  (5/3) * c^2
    - (2/3) * c * h
    + (2/3) * h^2

private def coeff3 (c _h : ℚ) : ℚ :=
  (4/3) * c^3

private def coeff4 (c h : ℚ) : ℚ :=
  (1/3) * c^4
    + (4/3) * c^3 * h
    - 4 * c^2 * h^2
    + (16/3) * c * h^3
    - (8/3) * h^4

private def coeff5 (c h : ℚ) : ℚ :=
  (2/3) * c^4 * h
    - (8/3) * c^3 * h^2
    + (16/3) * c^2 * h^3
    - (16/3) * c * h^4
    + (32/15) * h^5

theorem sumLoss_eval (c h n : ℚ) :
    sumLoss (n*c) (2*n*h+1) =
      coeff5 c h*n^5+coeff4 c h*n^4+coeff3 c h*n^3+coeff2 c h*n^2+coeff1 c h*n := by
  unfold sumLoss sliceLoss coeff1 coeff2 coeff3 coeff4 coeff5
  ring

def lossPolynomial (c h : ℚ) : ℚ[X] :=
  Polynomial.C (coeff5 c h)*Polynomial.X^5+Polynomial.C (coeff4 c h)*Polynomial.X^4+
    Polynomial.C (coeff3 c h)*Polynomial.X^3+Polynomial.C (coeff2 c h)*Polynomial.X^2+
    Polynomial.C (coeff1 c h)*Polynomial.X^1

theorem ambient_coeff (a : Cap) (c : ℕ) (ha : Fits a c) :
    (affineHilbertPolynomial
      ((⊥ : Ideal GeoJets5).comap (monomialMap GeoField (points a c)).toRingHom)).coeff 5 =
      (Low48BentVolume.bentIntegral a.1.b a.1.j a.1.t a.2 -
        4*((c : ℚ)^5-((c : ℚ)-2*(a.2 : ℚ))^5))/60 := by
  let I := (⊥ : Ideal GeoJets5).comap (monomialMap GeoField (points a c)).toRingHom
  let P := latticePolynomial a-lossPolynomial c a.2
  have hp : affineHilbertPolynomial I=P := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with n hn
    have hm : affineHilbertFunction I n = ((points (Scale n a) (n*c)).ncard : ℕ) := by
      rw [← point_scale a c ha n]
      exact monomial_hilbert_count _ (zero_mem a c ha) n
    rw [hn,hm,clipped_count _ _ (fits_scale ha n),sum_loss]
    simp only [P, Polynomial.eval_sub, latticePolynomial_eval a (old_chamber ha)]
    simp only [lossPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Scale, Shape.scale, pow_one]
    push_cast
    rw [← mul_assoc, sumLoss_eval]
  change (affineHilbertPolynomial I).coeff 5 = _
  rw [hp]
  have hcoeff : (latticePolynomial a).coeff 5 =
      Low48BentVolume.bentIntegral a.1.b a.1.j a.1.t a.2 / 60 := by
    simp only [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num [Low48BentVolume.bentIntegral]
  dsimp only [P]
  rw [Polynomial.coeff_sub,hcoeff]
  simp only [lossPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num [coeff5]
  ring

end
end Low49ActiveVolume
