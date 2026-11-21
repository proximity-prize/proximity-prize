import ProximityPrize.SubmissionLower.StructuralListPairImages

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial Finset Filter
open scoped BigOperators
open private surfaceBound from ProximityPrize.SubmissionLower.ListProofA

noncomputable section

private theorem affineLead_le {a b c d : ℚ}
    (h : ∀ᶠ m : ℕ in atTop, a*(m : ℚ)+b ≤ c*(m : ℚ)+d) : a ≤ c := by
  by_contra! hn
  have hlarge : ∀ᶠ m : ℕ in atTop, (d-b)/(a-c) < (m : ℚ) :=
    (eventually_gt_atTop ((d-b)/(a-c))).natCast_atTop
  obtain ⟨m, hm, hbig⟩ := (h.and hlarge).exists
  have hp := (div_lt_iff₀ (sub_pos.mpr hn)).mp hbig
  linarith

private theorem curve_eval {P : Ideal CoeffRing} (hP : (affineHilbertPolynomial P).natDegree = 1)
    (x : ℚ) : (affineHilbertPolynomial P).eval x = affineDegree P * x + (affineHilbertPolynomial P).coeff 0 := by
  let H := affineHilbertPolynomial P
  have heq : H = Polynomial.C (H.coeff 0) + Polynomial.C (H.coeff 1) * Polynomial.X := by
    have hp : H.natDegree < 2 := by change (affineHilbertPolynomial P).natDegree < 2; omega
    simpa [sum_range_succ] using H.as_sum_range_C_mul_X_pow' hp
  rw [affineDegree, hP, Nat.factorial_one, Nat.cast_one, one_mul, Polynomial.leadingCoeff, hP]
  change H.eval x = H.coeff 1 * x + H.coeff 0
  conv_lhs => rw [heq]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- Charge all shortened images of a cut jointly in the old source band. -/
theorem jointImageDegrees {ι : Type*} [Fintype ι]
    (T : Chart 2) (hT : ChartOK T) (Q : InitialRing 2) (hQ : Q ∉ sourceIdeal T)
    (a d e L : ℕ) (hda : d < a) (hed : 2*e < d) (he : 0 < e)
    (hQb : Q ∈ bandSpace (L*a) (L*d) (L*e))
    (P : ι → Ideal (InitialRing 2)) (hP : ∀ i, (P i).IsPrime)
    (hE : ∀ i, sourceIdeal T ≤ P i) (hPQ : ∀ i, Q ∈ P i)
    (hAnti : ∀ i j, i ≠ j → ¬ P j ≤ P i)
    (U : ι → Chart 2) (length : ι → ℕ) (hLength : ∀ i, 0 < length i)
    (hDen : ∀ i, (U i).denominator ∈ bandSpace (length i*a) (length i*d) (length i*e))
    (hNum : ∀ i j, (U i).numerator j ∈ bandSpace (length i*a) (length i*d) (length i*e))
    (hDim : ∀ i, (affineHilbertPolynomial (componentIdeal (U i) (P i))).natDegree = 1) :
    (∑ i, affineDegree (componentIdeal (U i) (P i)) / (length i : ℚ)) ≤
      (L : ℚ) * surfaceBound a d e T.equation.totalDegree
        (T.equation.weightedTotalDegree Fin.val : ℕ) (T.equation.degreeOf (Fin.last 2)) := by
  classical
  let D := ∏ i, length i
  have hD : 0 < D := prod_pos fun i _ => hLength i
  let scale (i : ι) := D / length i
  have hm (i : ι) : scale i * length i = D :=
    Nat.div_mul_cancel (dvd_prod_of_mem length (mem_univ i))
  have hscale (i : ι) : 0 < scale i := by by_contra! h; have := hm i; simp [Nat.eq_zero_of_le_zero h] at this; omega
  let primeWeight (i : ι) := affineDegree (componentIdeal (U i) (P i))
  let primeIntercept (i : ι) := (affineHilbertPolynomial (componentIdeal (U i) (P i))).coeff 0
  let charge := (L : ℚ) * surfaceBound a d e T.equation.totalDegree
    (T.equation.weightedTotalDegree Fin.val : ℕ) (T.equation.degreeOf (Fin.last 2))
  obtain ⟨g, hg⟩ := primeSeparators P hP hAnti
  let sepCost (i : ι) := (g i).totalDegree + (g i).weightedTotalDegree Fin.val + (g i).degreeOf (Fin.last 2)
  let loss := ∑ i, sepCost i
  have hloss (i : ι) : sepCost i ≤ loss := single_le_sum (f := sepCost) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hc (m : ℕ) : (∑ i, affineHilbertFunction (componentIdeal (U i) (P i)) (scale i * m)) ≤
      Module.finrank Geo (cutBand T Q ((D*m+loss)*a) ((D*m+loss)*d) ((D*m+loss)*e)) := by
    let bound (i : ι) (z : ℕ) := scale i*m*(length i*z)
    have hbound (i : ι) (z : ℕ) : bound i z = D*m*z := by
      calc
        _ = scale i * length i * m * z := by dsimp [bound]; ring
        _ = _ := by rw [hm]
    apply (sum_le_sum (fun i _ => componentHilbert_le_band (U i) (P i) _ _ _
      (hDen i) (hNum i) (scale i*m))).trans
    apply componentBands_le_cutBand T Q P hP hE hPQ g hg _ _ _ (fun i => bound i a) (fun i => bound i d) (fun i => bound i e)
    intro i
    have hprod (z : ℕ) (hz : 0 < z) : loss ≤ loss*z := by
      simpa using Nat.mul_le_mul_left loss (Nat.one_le_of_lt hz)
    have hpa := hprod a (by omega)
    have hpd := hprod d (by omega)
    have hpe := hprod e he
    rw [hbound, hbound, hbound, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have h₀ := hloss i
    unfold sepCost at h₀
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨v, huv⟩ := eventually_cutBand_rank T hT Q hQ a d e L hda hed he hQb
  have hupper : ∀ᶠ m : ℕ in atTop,
      (Module.finrank Geo (cutBand T Q ((D*m+loss)*a) ((D*m+loss)*d) ((D*m+loss)*e)) : ℚ) ≤
        charge * ((D*m+loss : ℕ) : ℚ) + v := by
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 huv
    filter_upwards [eventually_ge_atTop N₀] with m hm₀
    have hmul : m ≤ D*m := by simpa using Nat.mul_le_mul_right m (Nat.one_le_of_lt hD)
    exact hN₀ _ (by omega)
  have hsingle (i : ι) : ∀ᶠ m : ℕ in atTop,
      (affineHilbertFunction (componentIdeal (U i) (P i)) (scale i*m) : ℚ) =
        primeWeight i * ((scale i : ℚ) * m) + primeIntercept i := by
    obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial (componentIdeal (U i) (P i))
    filter_upwards [eventually_ge_atTop N₀] with m hm₀
    have hmul : m ≤ scale i*m := by simpa using Nat.mul_le_mul_right m (Nat.one_le_of_lt (hscale i))
    rw [← hN₀ _ (hm₀.trans hmul), curve_eval (hDim i), Nat.cast_mul]
  have hfinally : ∀ᶠ m : ℕ in atTop,
      (∑ i, primeWeight i * (scale i : ℚ)) * (m : ℚ) + ∑ i, primeIntercept i ≤
        (charge * D) * (m : ℚ) + (charge * loss + v) := by
    filter_upwards [hupper, eventually_all.2 hsingle] with m hupper hsingle
    have hlower := (Nat.cast_le (α := ℚ)).mpr (hc m)
    push_cast at hlower hupper
    have hh := hlower.trans hupper
    simp_rw [hsingle, ← mul_assoc] at hh
    rw [sum_add_distrib, ← sum_mul] at hh
    linarith only [hh]
  have hlead := affineLead_le hfinally
  have hDq : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  have hEq (i : ι) : primeWeight i * (scale i : ℚ) = (primeWeight i / (length i : ℚ)) * D := by
    have hh : ((scale i : ℚ) * length i) = D := by exact_mod_cast hm i
    have hLen : (length i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hLength i))
    have hdiv := (eq_div_iff hLen).mpr hh
    rw [hdiv]
    ring
  simp_rw [hEq, ← sum_mul] at hlead
  exact le_of_mul_le_mul_right hlead hDq

end

end StructuralList
