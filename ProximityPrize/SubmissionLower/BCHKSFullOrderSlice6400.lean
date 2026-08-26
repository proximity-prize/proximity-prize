import ProximityPrize.SubmissionLower.BCHKSCofactorLocalBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSFullOrderSlice6400

open BCHKSLocalValuation6400
open BCHKSSubstitutionVanish

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
The exact algebra behind the ``full local order'' branch.

For a shifted bivariate polynomial `S(X,Y)` over a coefficient ring, the
`X=0` slice records the received-line fibre at the chosen coordinate.  If
that slice is nonzero, its `Y` degree bounds the two-variable local order.
If both numbers equal `d`, every lower `Y` coefficient of the slice
vanishes, so the slice is a single monomial `a*Y^d`.  After a specialization
where `a` remains nonzero, zero is its unique root.
-/

/-- Evaluation of the inner (`X`) variable at zero, retaining `Y`. -/
noncomputable def zeroXSlice {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) : Polynomial A :=
  S.map (Polynomial.evalRingHom 0)

@[simp]
theorem zeroXSlice_coeff {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) (t : Nat) :
    (zeroXSlice S).coeff t = (S.coeff t).coeff 0 := by
  simp [zeroXSlice, Polynomial.coeff_zero_eq_eval_zero]

/-- A nonzero `X=0` slice witnesses a monomial no later than its `Y`
degree, hence bounds local total order. -/
theorem localOrder_le_natDegree_zeroXSlice
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A))
    (hS : S ≠ 0) (hslice : zeroXSlice S ≠ 0) :
    localOrder S <= (zeroXSlice S).natDegree := by
  let d := (zeroXSlice S).natDegree
  have hlead : (zeroXSlice S).coeff d ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hslice
  by_contra hnot
  have hvan : LocalVanish S (d + 1) :=
    (localVanish_iff_le_localOrder hS (d + 1)).mpr (by omega)
  have hz := hvan 0 d (by omega)
  have hz' : (zeroXSlice S).coeff d = 0 := by
    rw [zeroXSlice_coeff]
    exact hz
  exact hlead hz'

/-- In particular, any a priori `Y`-degree cap on the nonzero coordinate
slice also caps local order. -/
theorem localOrder_le_of_zeroXSlice_natDegree_le
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) (d : Nat)
    (hS : S ≠ 0) (hslice : zeroXSlice S ≠ 0)
    (hdeg : (zeroXSlice S).natDegree <= d) :
    localOrder S <= d :=
  (localOrder_le_natDegree_zeroXSlice S hS hslice).trans hdeg

/-- If local order reaches the slice degree cap, the complete coordinate
slice is its top monomial. -/
theorem zeroXSlice_eq_monomial_of_full_order
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) (d : Nat)
    (hS : S ≠ 0) (horder : localOrder S = d)
    (hdeg : (zeroXSlice S).natDegree <= d) :
    zeroXSlice S =
      Polynomial.monomial d ((zeroXSlice S).coeff d) := by
  have hvan : LocalVanish S d :=
    (localVanish_iff_le_localOrder hS d).mpr (by omega)
  ext t
  by_cases htd : t < d
  · have hz := hvan 0 t (by omega)
    simp [zeroXSlice_coeff, hz, Polynomial.coeff_monomial, Ne.symm (Nat.ne_of_lt htd)]
  · by_cases hdt : d < t
    · have hz : (zeroXSlice S).coeff t = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hdt)
      simp [hz, Polynomial.coeff_monomial, Nat.ne_of_lt hdt]
    · have hEq : t = d := by omega
      subst t
      simp

/-- A nonzero scalar multiple of a positive power has zero as its only
root.  This is the specialization step needed after the leading coordinate
coefficient has been charged separately. -/
theorem eq_zero_of_monomial_eval_eq_zero
    {F : Type*} [Field F]
    (c y : F) (d : Nat) (hc : c ≠ 0) (hd : 1 <= d)
    (heval : Polynomial.eval y (Polynomial.monomial d c) = 0) :
    y = 0 := by
  rw [Polynomial.eval_monomial] at heval
  have hypow : y ^ d = 0 := (mul_eq_zero.mp heval).resolve_left hc
  by_contra hy
  exact (pow_ne_zero d hy) hypow

/-- A full-order generic coordinate slice has a unique root after every
specialization where its top coefficient survives. -/
theorem specialized_root_eq_zero_of_full_order_slice
    {F : Type*} [Field F]
    (S : Polynomial (Polynomial (Polynomial F)))
    (d : ℕ) (z y : F)
    (hS : S ≠ 0)
    (horder : localOrder S = d)
    (hdeg : (zeroXSlice S).natDegree ≤ d)
    (hd : 1 ≤ d)
    (hlead : Polynomial.eval z ((zeroXSlice S).coeff d) ≠ 0)
    (hroot : Polynomial.eval y
      ((zeroXSlice S).map (Polynomial.evalRingHom z)) = 0) :
    y = 0 := by
  have hmono := zeroXSlice_eq_monomial_of_full_order S d hS horder hdeg
  rw [hmono] at hroot
  simp only [Polynomial.map_monomial, Polynomial.eval_monomial,
    Polynomial.coeff_map, Function.comp_apply] at hroot
  exact eq_zero_of_monomial_eval_eq_zero
    (Polynomial.eval z ((zeroXSlice S).coeff d)) y d hlead hd (by
      simpa [Polynomial.eval_monomial] using hroot)

/-- Evaluation of a bivariate polynomial commutes when the inner polynomial
is evaluated at zero. -/
theorem eval_zero_eval_eq_eval_map_zero
    {F : Type*} [Field F]
    (S : Polynomial (Polynomial F)) (U : Polynomial F) :
    Polynomial.eval 0 (Polynomial.eval U S) =
      Polynomial.eval (Polynomial.eval 0 U)
        (S.map (Polynomial.evalRingHom 0)) := by
  induction S using Polynomial.induction_on' with
  | add S T hS hT =>
      simpa using congrArg₂ (fun a b : F ↦ a + b) hS hT
  | monomial n a =>
      simp [Polynomial.eval_monomial, Polynomial.map_monomial]

/-- Evaluating the specialized shifted coordinate slice at the branch offset
is exactly evaluation of the substituted polynomial at that coordinate. -/
theorem eval_zeroXSlice_shift_specialize
    {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (omega z : F) (yZ P : Polynomial F) :
    Polynomial.eval (Polynomial.eval omega P - Polynomial.eval z yZ)
        ((zeroXSlice (Polynomial.Bivariate.shift R
          (Polynomial.C omega) yZ)).map (Polynomial.evalRingHom z)) =
      Polynomial.eval omega (triEval R z P) := by
  let B := specializeZ R z
  let y := Polynomial.eval z yZ
  have hcomp := congrArg (Polynomial.eval 0)
    (comp_eval_eq_shift_eval_tail B P omega y)
  rw [eval_zero_eval_eq_eval_map_zero] at hcomp
  have hslice :
      (zeroXSlice (Polynomial.Bivariate.shift R
          (Polynomial.C omega) yZ)).map (Polynomial.evalRingHom z) =
        zeroXSlice (Polynomial.Bivariate.shift B omega y) := by
    have hshift := specializeZ_shift R (Polynomial.C omega) yZ z
    simp only [Polynomial.eval_C] at hshift
    rw [← hshift]
    ext t
    simp [zeroXSlice, specializeZ, Polynomial.Bivariate.evalX_eq_map,
      Polynomial.coeff_map]
  rw [hslice]
  simpa [B, y, zeroXSlice, Polynomial.Bivariate.evalX_eq_map,
    triEval, specializeZ, Polynomial.eval_comp] using hcomp.symm

/-- A full-order received-line slice forces every specialized polynomial
owner root to equal the received value at that coordinate. -/
theorem owner_matches_received_of_full_order_slice
    {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (omega z : F) (yZ P : Polynomial F) (d : ℕ)
    (hshift : Polynomial.Bivariate.shift R (Polynomial.C omega) yZ ≠ 0)
    (horder : localOrder
      (Polynomial.Bivariate.shift R (Polynomial.C omega) yZ) = d)
    (hdeg : (zeroXSlice
      (Polynomial.Bivariate.shift R (Polynomial.C omega) yZ)).natDegree ≤ d)
    (hd : 1 ≤ d)
    (hlead : Polynomial.eval z
      ((zeroXSlice (Polynomial.Bivariate.shift R
        (Polynomial.C omega) yZ)).coeff d) ≠ 0)
    (hroot : triEval R z P = 0) :
    Polynomial.eval omega P = Polynomial.eval z yZ := by
  apply sub_eq_zero.mp
  apply specialized_root_eq_zero_of_full_order_slice
    (Polynomial.Bivariate.shift R (Polynomial.C omega) yZ) d z
      (Polynomial.eval omega P - Polynomial.eval z yZ)
      hshift horder hdeg hd hlead
  rw [eval_zeroXSlice_shift_specialize]
  simp [hroot]

/-- Arithmetic form of the defect split.  If the total deficit from full
order is at most `g-1` on `a` coordinates and `a=k+g`, at least `k+1`
coordinates have zero deficit. -/
theorem full_order_card_lower_bound
    {iota : Type*} [DecidableEq iota]
    (A : Finset iota) (defect : iota -> Nat)
    (k g : Nat)
    (hcard : A.card = k + g)
    (hsum : (∑ i ∈ A, defect i) < g) :
    k + 1 <= (A.filter fun i => defect i = 0).card := by
  let B := A.filter fun i => defect i ≠ 0
  have hBsum : B.card <= ∑ i ∈ B, defect i := by
    calc
      B.card = ∑ _i ∈ B, 1 := by simp
      _ <= ∑ i ∈ B, defect i := by
        apply Finset.sum_le_sum
        intro i hi
        have hne : defect i ≠ 0 := (Finset.mem_filter.mp hi).2
        omega
  have hsub : (∑ i ∈ B, defect i) <= ∑ i ∈ A, defect i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => (Finset.mem_filter.mp hi).1) (by simp)
  have hB : B.card < g := lt_of_le_of_lt (hBsum.trans hsub) hsum
  have hpartition :
      (A.filter fun i => defect i = 0).card + B.card = A.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, B]
      constructor
      · intro hi
        rcases hi with hi | hi
        · exact hi.1
        · exact hi.1
      · intro hi
        by_cases hz : defect i = 0
        · exact Or.inl ⟨hi, hz⟩
        · exact Or.inr ⟨hi, hz⟩
    · exact Finset.disjoint_left.mpr (by
        intro i hi0 hine
        exact (Finset.mem_filter.mp hine).2 (Finset.mem_filter.mp hi0).2)
  omega

end BCHKSFullOrderSlice6400
end ProximityPrize.SubmissionLower
