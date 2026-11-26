import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960HelperPrefix
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960Low6960ActiveCyclePrice
set_option Elab.async false





set_option Elab.async false

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

end Merged6967_R6960Low6960ActiveCyclePrice

section Merged6967_R6960PrefixReceipt
set_option Elab.async false



set_option Elab.async false

-- merged module R6960HelperSource6960
section Merged_R6960HelperSource6960
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
def helperBank : Bank := ⟨⟨294,408,89,7376⟩,777085255680,779461982⟩
theorem helper_bank_checked : P3_7_1.BankOK helperBank := by
  have moment : P1_7_1_3.momentEstimate 408 89 = 779461982 := by
    refine P1_7_1_3_2.moment_from_blocks
      [(128,109021770),(128,353396160),(128,272672821),(113,44371231)] ?_ rfl rfl
    exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
  exact P3_7_1.checked helperBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment
inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary
def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1
def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0
def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 86
  | .mixedBoundary => 79
  | _ => 1
private def compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  (compressedPhase helperBank.shape 179818 h 10 test.slope test.excess test.seed 0 -
    compressedPhase helperBank.shape 179818 h 10 test.slope test.excess test.seed 1 : ℕ) - (debit h helperBank : ℤ)
private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) :
    compressedSurplus h test = surplus helperBank 179818 h 10 test.slope test.excess test.seed := by
  unfold compressedSurplus surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ (by cases test <;> decide)]
private theorem twoSlopes_first :
    compressedSurplus 2359 .twoSlopes = 1315756893570 := by rfl
private theorem twoSlopes_next :
    compressedSurplus 2360 .twoSlopes = 135642678453300 := by rfl
private theorem seedBoundary_first :
    compressedSurplus 2359 .seedBoundary = 951451442183972 := by rfl
private theorem seedBoundary_next :
    compressedSurplus 2360 .seedBoundary = 1086170799811930 := by rfl
private theorem mixedBoundary_first :
    compressedSurplus 2359 .mixedBoundary = 765760703428686 := by rfl
private theorem mixedBoundary_next :
    compressedSurplus 2360 .mixedBoundary = 900411679649940 := by rfl
private theorem jetBoundary_first :
    compressedSurplus 2359 .jetBoundary = 6850472265407568 := by rfl
private theorem jetBoundary_next :
    compressedSurplus 2360 .jetBoundary = 6987702602189220 := by rfl
theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2359≤h) (hi : h≤33579) :
    debit h helperBank < gain helperBank.shape 179818 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2359 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus helperBank 179818 2359 10 test.slope test.excess test.seed ≤
      surplus helperBank 179818 2360 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq, ← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2359≤h) (hi : h≤33579) :
    WidthGuard helperBank 179818 h 10 :=
  width_at_height _ _ 2359 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179818 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q :=
  crt_avoiding_row Crt word helperBank 179818 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (by decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179818 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤85 ∧ (2≤jetDegree G → seedDegree G≤78) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 86≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 79≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179818 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179818 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
#print axioms helper_bank_checked
#print axioms helper_surplus
#print axioms helper_avoids
#print axioms helper_nonzero
#print axioms helper_common_caps
#print axioms helper_not_two
end Lower6960.HelperSource

end Merged_R6960HelperSource6960

-- merged module R6960PrefixReceipt
section Merged_R6960PrefixReceipt

-- merged module R6960DifferentialContact
section Merged_R6960DifferentialContact
noncomputable section
namespace Lower6960.DifferentialContact
open MvPolynomial K1_14_2_2_3
open K1_14_2_2_3_1 (partial_append)
variable {K : Type*} [CommRing K]
abbrev A (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
def Contact (I : Ideal (A K)) (n : ℕ) (f : A K) : Prop :=
  ∀ w : List (Fin 2),w.length<n → partialWord f w∈I
theorem zero_order (I : Ideal (A K)) (f : A K) : Contact I 0 f := by
  intro w h; omega
theorem succ_iff (I : Ideal (A K)) (n : ℕ) (f : A K) :
    Contact I (n+1) f ↔ f∈I ∧ ∀ i, Contact I n (pderiv i f) := by
  constructor
  · intro h; refine ⟨h [] (by simp),?_⟩
    intro i w hw
    rw [←partial_append]
    exact h _ (by simp; omega)
  · rintro ⟨hf,hd⟩ w hw
    induction w using List.reverseRecOn with
    | nil => exact hf
    | append_singleton ws i _ =>
      rw [partial_append]
      apply hd i ws
      simpa using hw
theorem weaken {I : Ideal (A K)} {n m : ℕ} {f : A K} (h : Contact I n f) (le : m≤n) :
    Contact I m f := fun w hw => h w (hw.trans_le le)
def testIdeal (I : Ideal (A K)) (n : ℕ) : Ideal (A K) where
  carrier := {f | Contact I n f}
  zero_mem' := by
    change Contact I n 0
    induction n with
    | zero => exact zero_order I _
    | succ n ih => exact (succ_iff I n 0).2 ⟨I.zero_mem, fun i=>by simpa using ih⟩
  add_mem' := by
    intro f g hf hg
    change Contact I n f at hf
    change Contact I n g at hg
    change Contact I n (f+g)
    induction n generalizing f g with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      obtain ⟨g0,dg⟩ := (succ_iff ..).1 hg
      exact (succ_iff ..).2 ⟨I.add_mem f0 g0, fun i=>by rw [map_add];exact ih (df i) (dg i)⟩
  smul_mem' := by
    intro a f hf
    change Contact I n f at hf
    change Contact I n (a*f)
    induction n generalizing a f with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      refine (succ_iff ..).2 ⟨I.mul_mem_left _ f0,?_⟩
      intro i; rw [pderiv_mul]
      have h1:=ih (pderiv i a) (weaken (m:=n) hf (by omega))
      have h2:=ih a (df i)
      intro w hw
      have distrib (g h : A K) : partialWord (g+h) w=partialWord g w+partialWord h w := by
        clear hw
        induction w with
        | nil => rfl
        | cons j w ih => simp only [partialWord,ih,map_add]
      rw [distrib]
      exact I.add_mem (h1 _ hw) (h2 _ hw)
theorem product {I : Ideal (A K)} (n m : ℕ) (f g : A K)
    (hf : Contact I n f) (hg : Contact I m g) : Contact I (n+m) (f*g) := by
  induction n generalizing m f g with
  | zero =>
    rw [Nat.zero_add]
    exact (testIdeal I m).mul_mem_left f hg
  | succ n ih =>
    induction m generalizing g with
    | zero =>
      rw [Nat.add_zero,mul_comm];exact (testIdeal I (n+1)).mul_mem_left g hf
    | succ m jh =>
      have df := ((succ_iff ..).1 hf).2
      have dg := ((succ_iff ..).1 hg).2
      refine (succ_iff ..).2 ⟨I.mul_mem_left f ((succ_iff ..).1 hg).1,?_⟩
      intro i; rw [pderiv_mul]
      apply (testIdeal I (n+1+m)).add_mem
      · change Contact I (n+1+m) ((pderiv i f)*g)
        simpa only [Nat.succ_add,Nat.add_succ] using ih (m+1) (pderiv i f) g (df i) hg
      · change Contact I (n+1+m) (f*(pderiv i g))
        exact jh (pderiv i g) (dg i)
theorem row_power {I : Ideal (A K)} {f : A K} {n : ℕ} (hf : Contact I n f) (k : ℕ) :
    Contact I (k*n) (f^k) := by
  induction k with
  | zero => rw [Nat.zero_mul]; exact zero_order I _
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact product _ _ _ _ ih hf
theorem row_strip {I : Ideal (A K)} (prime : I.IsPrime) (n : ℕ) (g f : A K)
    (unit : g∉I) (h : Contact I n (g*f)) : Contact I n f := by
  induction n generalizing f with
  | zero => exact zero_order I _
  | succ n ih =>
    obtain ⟨prod0,dprod⟩ := (succ_iff ..).1 h
    refine (succ_iff ..).2 ⟨(prime.mem_or_mem prod0).resolve_left unit,?_⟩
    have low := ih f (weaken h (by omega))
    intro i
    apply ih
    have data:=dprod i
    rw [pderiv_mul] at data
    have first := (testIdeal I n).mul_mem_left (pderiv i g) low
    have diff := (testIdeal I n).sub_mem data first
    change g*(pderiv i f) ∈ testIdeal I n
    simpa only [add_sub_cancel_left] using diff
open K1_14 (Jet Seeds)
open K1_14_2 (Ambient toJet)
open K1_14_2_2_3 (shiftedWord specialize_shiftedWord)
def Native (J : Ideal Ambient) (n : ℕ) (P : Jet) : Prop :=
  ∀ w : List (Fin 2),w.length<n → toJet (shiftedWord P w)∈J
private def coords : Jet →+* A Seeds := seedPresentation.toRingHom.comp toJet
private theorem native_iff (J : Ideal Ambient) (n : ℕ) (P : Jet) :
    Native J n P ↔ Contact (J.comap seedPresentation.symm.toRingHom) n (coords P) := by
  have commute (w : List (Fin 2)) : partialWord (coords P) w=coords (shiftedWord P w) := by
    have hh:=specialize_shiftedWord (RingHom.id Seeds) P w
    simpa [coords,specializeJets,MvPolynomial.map_id] using hh.symm
  constructor
  · intro h w hw
    rw [commute]
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J
    simpa using h w hw
  · intro h w hw
    have mem:=h w hw
    rw [commute] at mem
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J at mem
    simpa using mem
theorem native_power {J : Ideal Ambient} {n k r : ℕ} {P : Jet} (h : Native J n P)
    (fit : r≤k*n) : Native J r (P^k) := by
  apply (native_iff ..).2
  rw [map_pow]
  exact weaken (row_power ((native_iff ..).1 h) k) fit
theorem native_strip {J : Ideal Ambient} (hJ : J.IsPrime) {G P : Jet} (n : ℕ)
    (outside : toJet G∉J) (h : Native J n (G*P)) : Native J n P := by
  let I := J.comap seedPresentation.symm.toRingHom
  let _ : J.IsPrime := hJ
  have mem := (native_iff ..).1 h
  rw [map_mul] at mem
  apply (native_iff ..).2
  apply row_strip (I:=I) (Ideal.IsPrime.comap seedPresentation.symm.toRingHom) n (coords G) (coords P) _ mem
  change seedPresentation.symm (seedPresentation (toJet G))∉J
  simpa using outside
#print axioms native_power
#print axioms native_strip
#print axioms row_power
#print axioms row_strip
end Lower6960.DifferentialContact

end
end Merged_R6960DifferentialContact

-- merged module R6960PrefixRows
section Merged_R6960PrefixRows
noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1 (I K)
open K1_14 (Shape Jet FX Seeds Equation L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (Ambient toJet UsesSeed jetMarkHom)
open Lower6960.DifferentialContact (Native native_strip native_power weaken)
open Lower6960.HelperPrefix (one_helper timesShape)
open K1_14_2_2_3 (shiftedWord shift_word)
open K1_14_2_2_2_1 (divisor_caps)
open scoped Classical
theorem contact_of_crt {h agreement W reserve : ℕ} {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (P : Jet)
    (inside : P ∈ evaluated Crt word s W) (width : W + 2*h*reserve < s.m*agreement)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K) (S : (Polynomial K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (many : agreement ≤ hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i) :
    Native (RingHom.ker (jetMarkHom z S)) (reserve+1) P := by
  intro w hw
  have shift : K1_14_3.SeedShift h (evaluated Crt word) s :=
    fun _ _ hin i r => P0_10_1.evaluated_shift Crt word hin i r
  have mem := shift_word shift inside w
  have fit : W+2*h*w.length<s.m*agreement :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : w.length≤reserve)) _) width
  apply RingHom.mem_ker.mpr
  rw [K1_14_2.eval_toJet]
  exact P0_10_1.contact_vanish Crt word noPole z S residues degree hits many agree _ _ fit _ mem
def Common (V : Submodule FX Jet) (G : Jet) : Prop :=
  Irreducible G ∧ 0<G.natDegree ∧ UsesSeed G ∧ ∀ H∈V, G∣H
structure Prepared {ι : Type*} (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape) where
  exception : Jet
  kind : exception=1 ∨ Common V exception
  free : ι→Jet
  helper : Jet
  helper_mem : helper∈V
  helper_ne : helper≠0
  free_ne : ∀ i,free i≠0
  stripped : ∀ i,∃ k : ℕ, P i=exception^k*free i
  free_caps : ∀ i,K1_14_2_2.RowCaps (free i) (s i)
  moving_caps : ∀ i,K1_14_2_2.RowCaps (helper^(ks i)) (timesShape (ks i) hs)
  no_moving : ∀ i,K1_14_3.NoMovingCommon (free i) (helper^(ks i))
  contacts : ∀ i (J : Ideal Ambient),J.IsPrime → toJet exception∉J →
    ∀ r a : ℕ, r≤ks i*a → Native J r (P i) → (∀ H∈V,Native J a H) →
      Native J r (free i) ∧ Native J r (helper^(ks i))
theorem power_caps {H : Jet} {hs : Shape} (hn : H≠0)
    (cap : K1_14_2_2.RowCaps H hs) (k : ℕ) :
    K1_14_2_2.RowCaps (H^k) (timesShape k hs) := by
  open K1_14_2_2_2_1 in
    obtain ⟨hb,hj,hu⟩ := (rowCaps_iff H hs).mp cap
    apply (rowCaps_iff ..).mpr
    have b : jetDegree (H^k)=k*jetDegree H := P1_7_4_1.factorDegree_pow hn k 0
    have u : seedDegree (H^k)=k*seedDegree H := P1_7_4_1.factorDegree_pow hn k 2
    rw [b,u,natDegree_pow]
    exact ⟨Nat.mul_le_mul_left k hb,Nat.mul_le_mul_left k hj,Nat.mul_le_mul_left k hu⟩
theorem prepare {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    (nonzero : ∃ H∈V,H≠0) (vcaps : ∀ H∈V,K1_14_2_2.RowCaps H hs)
    (unique : ∀ G H,Common V G → Common V H → IsRelPrime G H → False) :
    Nonempty (Prepared P s ks V hs) := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have select (G : Jet) (kind : G=1 ∨ Common V G) (F : ι→Jet)
      (fac : ∀ i,∃ n : ℕ,P i=G^n*F i) (none : ∀ i Q,Common V Q → ¬ Q∣F i) :
      Nonempty (Prepared P s ks V hs) := by
    have nf (i) : F i≠0 := by
      obtain ⟨n,e⟩ := fac i
      exact right_ne_zero_of_mul (e ▸ proper i)
    obtain ⟨H,mem,nh,avoid⟩ := one_helper F ks V nonzero nf (by
      intro i Q irr div pos useed
      by_contra! all
      exact none i Q ⟨irr,pos,useed,all⟩ div)
    refine ⟨⟨G,kind,F,H,mem,nh,nf,fac,?_,fun i=>power_caps nh (vcaps H mem) _,avoid,?_⟩⟩
    · intro i
      obtain ⟨n,e⟩ := fac i
      exact divisor_caps (proper i) (caps i) (dvd_trans (dvd_mul_left (F i) (G^n)) (dvd_of_eq e.symm))
    · intro i J prime regular r a fit hp hc
      obtain ⟨n,e⟩ := fac i
      rw [e] at hp
      have unit : toJet (G^n)∉J := by
        rw [map_pow]
        exact fun bad => regular (prime.mem_of_pow_mem _ bad)
      exact ⟨native_strip prime r unit hp,native_power (hc H mem) fit⟩
  by_cases ex : ∃ G,Common V G
  · obtain ⟨G,g⟩ := ex
    choose F eq avoid using fun i => (FiniteMultiplicity.of_prime_left g.1.prime (proper i)).exists_eq_pow_mul_and_not_dvd
    apply select G (Or.inr g) F (fun i=>⟨_,eq i⟩)
    intro i Q q div
    by_cases same : G∣Q
    · exact avoid i (same.trans div)
    · exact unique G Q g q (g.1.isRelPrime_iff_not_dvd.mpr same)
  · apply select 1 (Or.inl rfl) P (fun i=>⟨0,by simp⟩)
    exact fun _ Q q _ => ex ⟨Q,q⟩
#print axioms contact_of_crt
#print axioms prepare
end Lower6960.PrefixRows

end
end Merged_R6960PrefixRows

-- merged module R6960PrefixReceipt
section Merged_R6960PrefixReceipt
noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1_14 (Shape Jet L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (jetMarkHom toJet)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Lower6960.HelperSource
open Lower6960.DifferentialContact (Native)
def rescueDegrees (G : Jet) : Prop :=
  G.natDegree=1 ∧
    ((jetDegree G=1 ∧ seedDegree G=1) ∨
     (jetDegree G=1 ∧ 2≤seedDegree G ∧ seedDegree G≤6) ∨
     (jetDegree G=1 ∧ 7≤seedDegree G ∧ seedDegree G≤85) ∨
     (2≤jetDegree G ∧ jetDegree G≤7 ∧ 1≤seedDegree G ∧ seedDegree G≤78))
theorem prepare_6960 {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2359≤h) (hi : h≤33579) :
    let V := evaluated Crt word helperBank.shape (helperCutoff h)
    ∃ out : Prepared P s ks V helperBank.shape, out.exception=1 ∨ rescueDegrees out.exception := by
  obtain ⟨out⟩ := prepare P s ks _ helperBank.shape proper caps
    (helper_nonzero Crt word lo hi) (fun _ inside=>evaluated_shape Crt word inside)
    (fun _ _ g i cop=>helper_not_two Crt word lo hi g.1 i.1 cop g.2.1 i.2.1 g.2.2.1
      i.2.2.1 g.2.2.2 i.2.2.2)
  refine ⟨out,out.kind.imp_right ?_⟩
  intro g
  obtain ⟨slope,b0,b1,u0,u1,mixed⟩ :=
    helper_common_caps Crt word lo hi g.1 g.2.2.1 g.2.1 g.2.2.2
  unfold rescueDegrees
  omega
#print axioms prepare_6960
theorem native_at_6960 {ι : Type*} {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2359≤h) (hi : h≤33579) {P : ι→Jet} {s : ι→Shape} {ks : ι→ℕ}
    (out : Prepared P s ks (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape)
    (i : ι) (W r : ℕ) (inside : P i∈evaluated Crt word (s i) W)
    (width : W+2*h*r<(s i).m*179818) (power : r+1≤ks i*11)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K1.K) (S : (Polynomial K1.K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset K1.I) (many : 179818≤hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i)
    (regular : toJet out.exception∉RingHom.ker (jetMarkHom z S)) :
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.helper^(ks i)) := by
  apply out.contacts i _ (RingHom.ker_isPrime _) regular (r+1) 11 power
  · exact contact_of_crt Crt word (s i) _ inside width noPole z S residues degree hits many agree
  · intro H member
    have wh := helper_width lo hi
    unfold WidthGuard cutoffCount at wh
    have fit : helperCutoff h + 2*h*10 < helperBank.shape.m*179818 := by
      unfold helperCutoff cutoffCount
      omega
    exact contact_of_crt Crt word helperBank.shape H member fit noPole z S residues degree hits many agree
#print axioms native_at_6960
end Lower6960.PrefixRows

end
end Merged_R6960PrefixReceipt

end Merged_R6960PrefixReceipt

end Merged6967_R6960PrefixReceipt

section Merged6967_R6966ProofTerminalBanks
set_option Elab.async false



set_option Elab.async false

namespace Research6966.TerminalBanks
open Polynomial
open K1 (I K)
open K1_14 (Shape L Jet liftPoly jetAt)
open K1_14_1 (CRTLift PoleData MarkResidues nodeL evaluated evaluated_shape evaluated_mono)
open K1_14_3 (Surface Parent OrderAt RowCaps)
open scoped Polynomial
noncomputable section

/-- All full-cutoff banks inside one paid geometric shape. The multiplier
is allowed to vary because it does not enter the geometric cutter charge. -/
def inside (s E : Shape) : Prop :=
    0<s.m ∧ s.B≤E.B ∧ s.J≤E.J ∧ s.U≤E.U

def Pass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (A : ℕ) (E : Shape) (q : Surface) : Prop :=
    ∀ s : Shape, inside s E → ∀ F∈evaluated Crt word s (s.m*A-1), F∈q.asIdeal

/-- Failure supplies a single proper cutter of the original paid shape,
vanishing for every marked scalar with the given agreement. -/
theorem failed_cutter {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (positive : 0<A) (regular : ∀ i j,(D.block i).eval (nodeL j) ≠ 0)
    {E : Shape} {q : Surface} (failed : ¬Pass Crt word A E q) :
    ∃ F : Jet, RowCaps F E ∧ F∉q.asIdeal ∧
      ∀ z S, MarkResidues D z S → (liftPoly S).natDegree≤131071+h →
        ∀ T : Finset I, A≤T.card → (∀ i∈T,(liftPoly S).eval (nodeL i)=word i) →
        jetAt F z S=0 := by
  classical
  unfold Pass at failed
  push Not at failed
  obtain ⟨s, ⟨sm,b,j,u⟩, F, mem, proper⟩ := failed
  refine ⟨F,?_,proper,?_⟩
  · intro v y c
    obtain ⟨b₀,j₀,u₀⟩:=evaluated_shape Crt word mem v y c
    exact ⟨b₀.trans b,j₀.trans j,u₀.trans u⟩
  · intro z S res deg T count agree
    exact P0_10_1.contact_vanish Crt word regular z S res deg T count agree s _
      (Nat.sub_lt (Nat.mul_pos sm positive) (by decide)) F mem

/-- A retained parent supplies the whole reserved order for every admissible
row. Both seed shifts may be taken before invoking the original parent theorem. -/
theorem retained_order {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {E s : Shape} {q : Surface} (geo : Parent q) (pass : Pass Crt word A E q)
    (fits : inside s E) {W r : ℕ} (small : r+1<K1.p) (cut : W+2*h*r<s.m*A)
    {F : Jet} (mem : F∈evaluated Crt word s W) : OrderAt q F (r+1) := by
  apply K1_14_3R_1.proof q F (r+1) geo small
  intro i j ij
  have limit := Nat.mul_le_mul_left (2*h) (show i+j≤r by omega)
  rw [Nat.mul_add] at limit
  have f := P0_10_1.evaluated_shift Crt word mem 0 i
  have g := P0_10_1.evaluated_shift Crt word f 1 j
  apply pass s fits
  exact evaluated_mono Crt word rfl rfl rfl le_rfl (by omega) g

/-- One native buffered row controls the joint ordinate product of all its
on-graph sheets. The order uses the actual source pass and actual fibre ideal. -/
theorem product_of_retained {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {E s : Shape} {W r : ℕ} (fits : inside s E) (small : r+1<K1.p)
    (cut : W+2*h*r<s.m*A) {F : Jet} (mem : F∈evaluated Crt word s W)
    (ys : Finset K1_14_3.SeedClosure) (v : K1_14_3.SeedClosure → K1_14_3.SeedClosure)
    (G₁ G₀ : K1_14_3.SeedClosure[X])
    (sheets : ∀ y∈ys, ∃ q : Surface, Parent q ∧ Pass Crt word A E q ∧
      K1_14_3.OnSeedFibre q y (v y) ∧ G₁.eval y≠0 ∧ G₁.eval y*v y=G₀.eval y)
    (J : ℕ) (bound : (K1_14_3.fibreRow F).natDegree ≤ J) :
    (∏ y∈ys,(Polynomial.X (R:=K1_14_3.SeedClosure)-Polynomial.C y))^(r+1) ∣
      TerminalProjection.cleared G₁ G₀ (K1_14_3.fibreRow F) J := by
  apply TerminalProjection.all_sheets G₁ G₀ _ ys v _ _ bound
  intro y hy
  obtain ⟨q,geo,pass,fiber,reg,onG⟩:=sheets y hy
  exact ⟨reg,onG,retained_order Crt word geo pass fits small cut mem y (v y) fiber⟩

#print axioms failed_cutter
#print axioms retained_order
#print axioms product_of_retained
end
end Research6966.TerminalBanks

end Merged6967_R6966ProofTerminalBanks
