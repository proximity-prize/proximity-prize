import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import Mathlib.Algebra.MvPolynomial.Coeff

-- merged module Low49ActiveCount
section Merged_Low49ActiveCount

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Low49ActiveCount
open Low48BentLattice (Cap latticePoints coords)
open Low49ActiveLattice (Fits Active points)
open K1_13_6_2_4 (Exponent)
open Finset
open scoped BigOperators
noncomputable section

def missing (a : Cap) (c : ℕ) : Set Exponent := latticePoints a \ points a c

private def clipAt (c h : ℕ) : ℕ := 2*c-2*h
private def indexAt (a : Cap) (h : ℕ) : ℕ := 2*a.1.j-4*h
private def degreeAt (a : Cap) (h : ℕ) : ℕ := 2*a.1.b-h

private def Slices (a : Cap) (c : ℕ) :=
  Σ h : Fin (2*a.2+1), Σ r : Fin (clipAt c h.val), Σ z : Fin (r.val/2+1),
    Fin (r.val-2*z.val+1) × Fin (clipAt c h.val-r.val)

private theorem slices_ext {a : Cap} {c : ℕ} {s t : Slices a c}
    (hh : s.1.val=t.1.val) (hr : s.2.1.val=t.2.1.val)
    (hz : s.2.2.1.val=t.2.2.1.val) (hy : s.2.2.2.1.val=t.2.2.2.1.val)
    (hu : s.2.2.2.2.val=t.2.2.2.2.val) : s=t := by
  rcases s with ⟨⟨h,h₀⟩,⟨r,r₀⟩,⟨z,z₀⟩,⟨y,y₀⟩,⟨u,u₀⟩⟩
  rcases t with ⟨⟨h',h₀'⟩,⟨r',r₀'⟩,⟨z',z₀'⟩,⟨y',y₀'⟩,⟨u',u₀'⟩⟩
  change h=h' at hh
  change r=r' at hr
  change z=z' at hz
  change y=y' at hy
  change u=u' at hu
  subst h' r' z' y' u'
  rfl

private theorem at_bounds {a : Cap} {c h : ℕ} (ha : Fits a c) (hh : h ≤ 2*a.2) :
    2*h ≤ 2*c ∧ 4*h ≤ 2*a.1.j ∧ h ≤ 2*a.1.b ∧
    2*clipAt c h ≤ indexAt a h ∧ clipAt c h ≤ 2*(2*a.1.t-2*h) ∧
    indexAt a h+clipAt c h ≤ degreeAt a h := by
  obtain ⟨hb,hj,hc,ht,hh',_⟩ := ha
  unfold clipAt indexAt degreeAt
  omega

private def slicesEquiv (a : Cap) (c : ℕ) (ha : Fits a c) : missing a c ≃ Slices a c where
  toFun e := by
    have hh := ((coords a e.val).mp e.property.1).2.2.2
    let h : Fin (2*a.2+1) := ⟨e.val 4, Nat.lt_succ_of_le hh⟩
    have hc := at_bounds ha hh
    have he := (coords a e.val).mp e.property.1
    have hcut : 2*a.1.b+2*a.1.j < e.val 0+2*Active e.val+3*e.val 4+2*c := by
      apply Nat.lt_of_not_ge
      exact fun hv => e.property.2 ⟨e.property.1,hv⟩
    let r := indexAt a h.val-Active e.val
    have hr : r < clipAt c h.val ∧ e.val 2+2*e.val 3 ≤ r := by
      dsimp [r,h,clipAt,indexAt,Active] at *
      omega
    let r₀ : Fin (clipAt c h.val) := ⟨r,hr.1⟩
    let z : Fin (r₀.val/2+1) := ⟨e.val 3,by dsimp [r₀]; omega⟩
    let y : Fin (r₀.val-2*z.val+1) := ⟨e.val 2,by dsimp [r₀,z]; omega⟩
    let u := e.val 0 - (degreeAt a h.val - Active e.val + 1 - (clipAt c h.val-r))
    have hu : u < clipAt c h.val-r := by
      dsimp [r,h,u,degreeAt,indexAt,clipAt,Active] at *
      omega
    exact ⟨h,r₀,z,y,⟨u,hu⟩⟩
  invFun s := by
    rcases s with ⟨h,r,z,y,u⟩
    have hh := h.isLt
    have hr := r.isLt
    have hz := z.isLt
    have hy := y.isLt
    have hu := u.isLt
    have hc := at_bounds ha (Nat.le_of_lt_succ hh)
    let act := indexAt a h-r.val
    let x := act - y.val - z.val
    let m0 := degreeAt a h-act+1-(clipAt c h-r.val)+u.val
    let m : Exponent := Finsupp.equivFunOnFinite.symm ![m0,x,y.val,z.val,h.val]
    have hi : m ∈ latticePoints a := by
      apply (coords a m).mpr
      change m0+x+y.val+z.val+h.val ≤ 2*a.1.b ∧
        x+2*y.val+3*z.val+4*h.val ≤ 2*a.1.j ∧ z.val+2*h.val ≤ 2*a.1.t ∧ h.val ≤ 2*a.2
      dsimp [m0,x,act,degreeAt,clipAt,indexAt] at *
      omega
    refine ⟨m,hi,?_⟩
    intro hm
    have hd := hm.2
    change m0+2*(x+y.val+z.val)+3*h.val+2*c ≤ 2*a.1.b+2*a.1.j at hd
    dsimp [m0,x,act,degreeAt,clipAt,indexAt] at *
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    have hh := ((coords a e.val).mp e.property.1).2.2.2
    have hc := at_bounds ha hh
    have he := (coords a e.val).mp e.property.1
    have hcut : 2*a.1.b+2*a.1.j < e.val 0+2*Active e.val+3*e.val 4+2*c := by
      apply Nat.lt_of_not_ge
      exact fun hv => e.property.2 ⟨e.property.1,hv⟩
    fin_cases i
    · change degreeAt a (e.val 4) - (indexAt a (e.val 4) - (indexAt a (e.val 4) - Active e.val)) + 1 -
        (clipAt c (e.val 4) - (indexAt a (e.val 4)-Active e.val)) +
        (e.val 0 - (degreeAt a (e.val 4)-Active e.val+1 -
          (clipAt c (e.val 4)-(indexAt a (e.val 4)-Active e.val)))) = e.val 0
      dsimp [degreeAt,indexAt,clipAt,Active] at *
      omega
    · change indexAt a (e.val 4)-(indexAt a (e.val 4)-Active e.val)-e.val 2-e.val 3 = e.val 1
      dsimp [indexAt,Active] at *
      omega
    · rfl
    · rfl
    · rfl
  right_inv s := by
    rcases s with ⟨⟨h,hh⟩,⟨r,hr⟩,⟨z,hz⟩,⟨y,hy⟩,⟨u,hu⟩⟩
    change r < clipAt c h at hr
    change z < r/2+1 at hz
    change y < r-2*z+1 at hy
    change u < clipAt c h-r at hu
    have hc := at_bounds ha (show h ≤ 2*a.2 by omega)
    have hact : indexAt a h-r-y-z+y+z = indexAt a h-r := by
      have hci := hc.2.2.2.1
      omega
    have hr' : indexAt a h-(indexAt a h-r-y-z+y+z)=r := by
      rw [hact]
      have hci := hc.2.2.2.1
      omega
    apply slices_ext
    · rfl
    · exact hr'
    · rfl
    · rfl
    · change degreeAt a h-(indexAt a h-r)+1-(clipAt c h-r)+u -
        (degreeAt a h-(indexAt a h-r-y-z+y+z)+1 -
          (clipAt c h-(indexAt a h-(indexAt a h-r-y-z+y+z)))) = u
      rw [hr',hact]
      omega


open K1_13_6_2_3_1 (sum_affine sum_pair)

private theorem middle_sum (r : ℕ) :
    (∑ z ∈ range (r/2+1), ((r-2*z+1 : ℕ) : ℚ)) =
      ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ) := by
  have h (z : ℕ) (hz : z ∈ range (r/2+1)) :
      ((r-2*z+1 : ℕ) : ℚ) = (r+1 : ℚ)+(-2)*(z : ℚ) := by
    have h2 : 2*z ≤ r := by have := mem_range.mp hz; omega
    push_cast [Nat.cast_sub h2]
    ring
  rw [sum_congr rfl h, sum_affine]
  push_cast [Nat.cast_sub (show r/2 ≤ r+1 by omega)]
  ring

private theorem card_sum (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((missing a c).ncard : ℚ) = ∑ h ∈ range (2*a.2+1), ∑ r ∈ range (clipAt c h),
      ((clipAt c h-r : ℕ) : ℚ) *
        ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ) := by
  classical
  let : Fintype (Slices a c) := by unfold Slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (slicesEquiv a c ha), Nat.card_eq_fintype_card]
  unfold Slices
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_sum, Nat.cast_mul]
  rw [Fin.sum_univ_eq_sum_range (fun h =>
    ∑ r : Fin (clipAt c h), ∑ z : Fin (r.val/2+1),
      ((r.val-2*z.val+1 : ℕ) : ℚ) * ((clipAt c h-r.val : ℕ) : ℚ))]
  apply sum_congr rfl
  intro h _
  rw [Fin.sum_univ_eq_sum_range (fun r => ∑ z : Fin (r/2+1),
    ((r-2*z.val+1 : ℕ) : ℚ) * ((clipAt c h-r : ℕ) : ℚ))]
  apply sum_congr rfl
  intro r _
  rw [Fin.sum_univ_eq_sum_range (fun z =>
    ((r-2*z+1 : ℕ) : ℚ) * ((clipAt c h-r : ℕ) : ℚ)), ← Finset.sum_mul, middle_sum]
  ring

def sliceLoss (q : ℚ) : ℚ := q*(q+1)^2*(q+2)/3

private def pairedLoss (q i : ℚ) : ℚ :=
    (2*q-2*i)*(i+1)^2 + (2*q-2*i-1)*(i+1)*(i+2)

private theorem sum_paired_loss (q : ℚ) (n : ℕ) :
    ∑ i ∈ range n, pairedLoss q i =
      pairedLoss q 0 * n + (pairedLoss q 1-pairedLoss q 0)*((n : ℚ)*(n-1)/2) +
      (pairedLoss q 2-2*pairedLoss q 1+pairedLoss q 0)*((n : ℚ)*(n-1)*(n-2)/6) +
      (pairedLoss q 3-3*pairedLoss q 2+3*pairedLoss q 1-pairedLoss q 0)*((n : ℚ)*(n-1)*(n-2)*(n-3)/24) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold pairedLoss
    ring

private theorem sum_strip (q : ℕ) :
    (∑ r ∈ range (2*q), ((2*q-r : ℕ) : ℚ) *
      ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ)) = sliceLoss q := by
  rw [sum_pair]
  calc
    _ = ∑ i ∈ range q, pairedLoss q i := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have h0 : (2*i)/2=i := by omega
      have h1 : (2*i+1)/2=i := by omega
      rw [h0,h1]
      push_cast [Nat.cast_sub (show 2*i ≤ 2*q by omega), Nat.cast_sub (show 2*i+1 ≤ 2*q by omega),
        Nat.cast_sub (show i ≤ 2*i+1 by omega), Nat.cast_sub (show i ≤ 2*i+1+1 by omega)]
      unfold pairedLoss
      ring
    _ = _ := by rw [sum_paired_loss]; unfold pairedLoss sliceLoss; ring

theorem loss_count (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((missing a c).ncard : ℚ) =
      ∑ h ∈ range (2*a.2+1), sliceLoss ((c : ℚ) - (h : ℚ)) := by
  rw [card_sum a c ha]
  apply sum_congr rfl
  intro h hh
  have hch : h ≤ c := by
    have := ha.2.2.2.2.1
    have := mem_range.mp hh
    omega
  unfold clipAt
  rw [show 2*c-2*h=2*(c-h) by omega, sum_strip]
  push_cast [Nat.cast_sub hch]
  rfl

theorem clipped_count (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((points a c).ncard : ℚ) = ((latticePoints a).ncard : ℚ) -
      ∑ h ∈ range (2*a.2+1), sliceLoss ((c : ℚ) - (h : ℚ)) := by
  rw [← loss_count a c ha]
  have hn := Set.ncard_sdiff_add_ncard_of_subset
    (s:=points a c) (t:=latticePoints a) (fun _ hm => hm.1) (Low48BentLattice.finite a)
  change (missing a c).ncard + (points a c).ncard = (latticePoints a).ncard at hn
  exact (eq_sub_of_add_eq' (by exact_mod_cast hn))


end
end Low49ActiveCount

end Merged_Low49ActiveCount

-- merged module Low49ActiveVolume
section Merged_Low49ActiveVolume

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
open Low48BentVolume (latticePolynomial latticePolynomial_eval)
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

private theorem old_chamber {a : Cap} {c : ℕ} (ha : Fits a c) : Low48BentLattice.Chamber a := by
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

private def sumLoss (c n : ℚ) : ℚ :=
  let f : ℚ→ℚ := fun h => sliceLoss (c-h)
  n*f 0+n*(n-1)/2*(f 1-f 0)+n*(n-1)*(n-2)/6*(f 2-2*f 1+f 0)+
    n*(n-1)*(n-2)*(n-3)/24*(f 3-3*f 2+3*f 1-f 0)+
    n*(n-1)*(n-2)*(n-3)*(n-4)/120*(f 4-4*f 3+6*f 2-4*f 1+f 0)

private theorem sum_loss (c : ℚ) (n : ℕ) :
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

private theorem sumLoss_eval (c h n : ℚ) :
    sumLoss (n*c) (2*n*h+1) =
      coeff5 c h*n^5+coeff4 c h*n^4+coeff3 c h*n^3+coeff2 c h*n^2+coeff1 c h*n := by
  unfold sumLoss sliceLoss coeff1 coeff2 coeff3 coeff4 coeff5
  ring

private def lossPolynomial (c h : ℚ) : (Polynomial ℚ) :=
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

end Merged_Low49ActiveVolume

-- merged module R6960Low6960ActiveCyclePrice
section Merged_R6960Low6960ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Low6960ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open Low48BentCycle (diagonal_unit grade_sum diagonal_sum coeff_congr)
open Low48BentCycle (ambient_list)
open Low49ActiveVolume (fits_scale point_scale point_zero)

private def integr (a : Cap) : ℚ := integral a

private def signed (p : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p))

private theorem base_signed (p : Shape) :
    Low6960Prices.tiltedSurface p Low6960Prices.primaryBox = (signed p).toNat := by
  change Low48Price.ambientMix (slots.map (caps p)) = _
  exact ambient_list (caps p)

private theorem base_normalize (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p) (positiveDiagonal J))) = (signed p : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p : Shape} (h : ∀ i, Chamber (caps p i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p)) ⊥ Finset.univ ≤
      (Low6960Prices.tiltedSurface p Low6960Prices.primaryBox : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p ≤ ((signed p).toNat : ℤ) by omega)

private theorem fits_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    Fits (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Fits, Low48BentLattice.Sum]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hm := Low49ActiveLattice.fits_add (h i (Finset.mem_insert_self _ _)) hs
    simpa only [Low48BentLattice.Sum, Finset.sum_insert hi, Low48BentLattice.Add, Shape.plus] using hm

private theorem points_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    (∑ i ∈ s, points (a i) (c i)) = points (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Low48BentLattice.Sum] using point_zero.symm
  | insert i s hi ih =>
    have hs (j : Fin 5) (hj : j ∈ s) := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hs,
      Low49ActiveLattice.add (h i (Finset.mem_insert_self _ _)) (fits_sum s a c hs)]
    simp only [Low48BentLattice.Sum, Low48BentLattice.Add, Finset.sum_insert hi, Shape.plus]

private def clipSum (p : Shape) (K : ℕ) (t : Grade) : ℕ := ∑ i, t i * clips p K i

private theorem active_diagonal {p : Shape} {K : ℕ} (t : Grade)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    diagonalExponents (activeFamily p K) t = points (capSum (caps p) t) (clipSum p K t) := by
  have h0 := (active_doubled h).double_zero
  calc
    _ = ∑ i : Fin 5, diagonalExponents (activeFamily p K) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, points (Scale (t i) (caps p i)) (t i * clips p K i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul, diagonal_unit _ h0]
      exact point_scale _ _ (h i) _
    _ = _ := points_sum _ _ _ (fun i _ => fits_scale (h i) _)

private theorem fifth_difference (v : Fin 5 → ℚ) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (∑ i, (positiveDiagonal J i : ℚ) * v i)^5) = 120 * ∏ i, v i := by
  let f : Form := (∑ i : Fin 5, C (v i) * MvPolynomial.X i)^5
  have hlin : (∑ i : Fin 5, (C (v i) * MvPolynomial.X i : Form)).IsHomogeneous 1 := by
    change _ ∈ homogeneousSubmodule (Fin 5) ℚ 1
    apply Submodule.sum_mem
    intro i _
    exact (isHomogeneous_X ℚ i).C_mul _
  have hf : f.IsHomogeneous 5 := by
    simpa only [Nat.mul_one] using hlin.pow 5
  have hsum := cube_extract (Finset.univ : Finset (Fin 5)) f
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  simp_rw [line_coeff, homogeneousComponent_eq_self hf] at hsum
  have he (J : Finset (Fin 5)) :
      eval (fun i => (positiveDiagonal J i : ℚ)) f = (∑ i, (positiveDiagonal J i : ℚ) * v i)^5 := by
    simp [f, mul_comm]
  simp_rw [he] at hsum
  rw [hsum]
  unfold f
  simp only [← smul_eq_C_mul]
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hu (i : Fin 5) : squarefree Finset.univ i = 1 := by simp [squarefree_apply]
  have hd : (squarefree (Finset.univ : Finset (Fin 5))).degree = 5 := by
    simp [K1_13_6_2_4_1.squarefree_degree]
  have hh : (squarefree (Finset.univ : Finset (Fin 5))).support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, hu]
  have hsum' : (squarefree (Finset.univ : Finset (Fin 5))).sum (fun _ m => m) = 5 := hd
  simp [hsum', Finsupp.multinomial_eq, Finsupp.prod, hh, hu, Nat.multinomial,
    Finset.sum_const, Nat.factorial]

private theorem clips_prod (p : Shape) (K : ℕ) (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (Low6960Prices.activeLoss (Low6960Prices.activeClips p K) : ℚ) =
      480 * ((∏ i, (clips p K i : ℚ)) -
        (∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)))) := by
  rw [← clip_list p K ht]
  unfold Low6960Prices.activeLoss
  have hi (i : Fin 5) : 2 * (caps p i).2 ≤ clips p K i := (h i).2.2.2.2.1
  have hle : (∏ i, (clips p K i - 2 * (caps p i).2)) ≤ ∏ i, clips p K i :=
    Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
  have hp (a : Fin 5 → ℕ) : (slots.map a).prod = ∏ i, a i := by
    rw [← List.prod_toFinset a (show slots.Nodup by decide)]
    rw [show slots.toFinset = Finset.univ by decide]
  simp only [List.map_map, Function.comp_apply, hp]
  rw [Nat.cast_mul, Nat.cast_sub hle]
  push_cast [Nat.cast_sub, hi]
  norm_num

theorem active_budget {p : Shape} {K : ℕ} (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (60 * 32 : ℚ) * mixedDegree (activeFamily p K) ⊥ Finset.univ ≤
      (Low6960Prices.tiltedSurfaceActive p Low6960Prices.primaryBox K : ℚ) := by
  classical
  have hcoeff (J : Finset (Fin 5)) :
      (affineHilbertPolynomial (Ideal.comap
        (monomialMap GeoField (diagonalExponents (activeFamily p K) (positiveDiagonal J))) ⊥)).coeff 5 =
      (integr (capSum (caps p) (positiveDiagonal J)) -
        4 * ((clipSum p K (positiveDiagonal J) : ℚ)^5 -
          ((clipSum p K (positiveDiagonal J) : ℚ) -
            2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ))^5)) / 60 := by
    rw [coeff_congr _ _ (active_diagonal _ h)]
    have hs := fits_sum Finset.univ (fun i => Scale (positiveDiagonal J i) (caps p i))
      (fun i => positiveDiagonal J i * clips p K i) (fun i _ => fits_scale (h i) _)
    let a := capSum (caps p) (positiveDiagonal J)
    let c := clipSum p K (positiveDiagonal J)
    change (affineHilbertPolynomial ((⊥ : Ideal K1_13_6_2.GeoJets5).comap
      (monomialMap GeoField (points a c)).toRingHom)).coeff 5 = _
    rw [Low49ActiveVolume.ambient_coeff a c hs]
    unfold integr integral
    rw [Low48BentVolume.cast_price_integral a]
  have hc (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) = ∑ i, (positiveDiagonal J i : ℚ) * clips p K i := by
    unfold clipSum
    push_cast
    rfl
  have hcd (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) -
          2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ) =
        ∑ i, (positiveDiagonal J i : ℚ) * ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)) := by
    rw [hc]
    simp only [capSum, Low48BentLattice.Sum, Scale, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ)^5 = 32 by norm_num, mul_assoc, ← mul_div_assoc (32 : ℚ),
    mul_div_cancel_left₀ _ (by norm_num : (32 : ℚ) ≠ 0)]
  simp_rw [hcoeff, ← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0)]
  have hsum_rearr (A C D : Finset (Fin 5) → ℚ) :
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (A J - 4 * (C J - D J))) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * A J) -
        4 * ((∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * C J) -
          (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * D J)) := by
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw [hsum_rearr, base_normalize]
  simp_rw [hcd, hc]
  simp_rw [fifth_difference]
  rw [show 4 * (120 * (∏ i, (clips p K i : ℚ)) -
      120 * ∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ))) =
      (Low6960Prices.activeLoss (Low6960Prices.activeClips p K) : ℚ) by rw [clips_prod p K ht h]; ring]
  unfold Low6960Prices.tiltedSurfaceActive
  rw [base_signed]
  exact_mod_cast (show signed p - (Low6960Prices.activeLoss (Low6960Prices.activeClips p K) : ℤ) ≤
    (((signed p).toNat - Low6960Prices.activeLoss (Low6960Prices.activeClips p K) : ℕ) : ℤ) by omega)

end
end Low6960ActiveCycle

end Merged_R6960Low6960ActiveCyclePrice
