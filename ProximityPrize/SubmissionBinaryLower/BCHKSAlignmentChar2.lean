import ProximityPrize.SubmissionBinaryLower.BCHKSInseparable
import ProximityPrize.SubmissionBinaryLower.BCHKSQBadRemoval
import ProximityPrize.SubmissionBinaryLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionBinaryLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionBinaryLower.BCHKSWeightedFactorCaps

/-!
# Polynomial alignment in characteristic two

The staged BCHKS selection picks an irreducible factor `R` of the interpolant
carrying more selected challenges than its capacity `sfCapU (deg_Y R)`.  This
file proves alignment for such a factor by strong induction on `deg_Y R`:

* `∂R/∂Y ≠ 0`: the universal-numerator ledger (`single_factor_alignment_univ`).
* `∂R/∂Y = 0`, `∂R/∂X ≠ 0`: impossible, since `dead_factor_card_le` bounds the
  selected challenges by `2 deg_Y(R) D_Z < sfCapU`.
* `∂R/∂Y = ∂R/∂X = 0`: pass to the Frobenius twist `T` of half the `Y`-degree,
  relabel each challenge `z` by its square root, and double the line exponent.

The resulting theorem replaces the odd-characteristic separability step of the
KoalaBear development.
-/

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark Polynomial
open RationalFunctions RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

abbrev BFld := BinaryIRSProfile.Field

/-- Single-factor alignment for an arbitrary irreducible factor at level `q`. -/
theorem single_factor_alignment (d : ℕ) :
    ∀ (q : ℕ) (U : Fin 2 → BinaryIRSProfile.Index → BFld) (P : BFld → BFld[X])
      (Arow : BFld → Finset BinaryIRSProfile.Index)
      (R : Polynomial (Polynomial (Polynomial BFld))) (S : Finset BFld),
      1 ≤ q → q * d ≤ 6901 → R.natDegree = d → Irreducible R → 0 < d →
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        ((R.coeff j).coeff a).natDegree + q * j < 21907324) →
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + 1048575 * j < 7244000000) →
      (∀ z ∈ S, (P z).natDegree ≤ 1048575) →
      (∀ z ∈ S, triEval R z (P z) = 0) →
      (∀ z ∈ S, 1482911 ≤ (Arow z).card) →
      (∀ z ∈ S, ∀ i ∈ Arow z,
        Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z ^ q * U 1 i) →
      sfCapU d < S.card →
      ∃ T : Finset BFld, T ⊆ S ∧ bchksErrors + 1 < T.card ∧
        ∃ p₀ p₁ : BFld[X], p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
          ∀ z ∈ T, P z = p₀ + Polynomial.C (z ^ q) * p₁ := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro q U P Arow R S hq1 hqd hRd hRi hdpos hYZs hW hPdeg hvan hrow hagree hcard
  classical
  have hd312 : d ≤ 6901 := by nlinarith
  by_cases hsep : R.derivative ≠ 0
  · exact single_factor_alignment_univ q hq1 (by unfold uE; nlinarith) U P Arow R S hRi (by omega)
      (by omega) hsep hYZs hW hPdeg hvan hrow hagree (by rw [hRd]; exact hcard)
  have hY : R.derivative = 0 := not_not.mp hsep
  by_cases hX : dXPoly R ≠ 0
  · exfalso
    have hZcap : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ 21907324 := by
      intro j a
      by_cases h0 : (R.coeff j).coeff a = 0
      · simp [h0]
      · have := hYZs j a h0
        omega
    have hXcap : ∀ j, (R.coeff j).natDegree ≤ 7244000000 := by
      intro j
      by_cases h0 : R.coeff j = 0
      · simp [h0]
      · have := hW j (R.coeff j).natDegree (by
          rw [Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr h0)
        omega
    have hF : 2 * R.natDegree * 7244000000 < Fintype.card BFld := by
      rw [show Fintype.card BFld = 2 ^ (192 : ℕ) from BF64.card_ext3, hRd]
      calc 2 * d * 7244000000 ≤ 2 * 6901 * 7244000000 := by gcongr
        _ < 2 ^ (192 : ℕ) := by norm_num
    have hdead := dead_factor_card_le R hRi (by omega) hY hX 21907324 7244000000
      hZcap hXcap hF S P hvan
    rw [hRd] at hdead
    have hdead' : S.card ≤ 2 * d * uDZ := hdead
    unfold sfCapU at hcard
    generalize uC * uDZ * d = c₁ at hcard
    generalize (bchksErrors + 1) * d = c₂ at hcard
    generalize 2 * d * uDZ = c₃ at hcard hdead'
    omega
  have hX0 : dXPoly R = 0 := not_not.mp hX
  -- Frobenius twist.
  set T := twistPoly R with hTdef
  have hTR : frobLift T = R := frobLift_twistPoly R hY hX0
  have hTdeg : T.natDegree * 2 = d := by
    rw [← hRd, ← hTR, natDegree_frobLift]
  have hTirr : Irreducible T := irreducible_twistPoly R hRi hY hX0
  have hd'lt : T.natDegree < d := by omega
  have hd'pos : 0 < T.natDegree := by omega
  let S' : Finset BFld := S.image sqrtF
  have hS'mem : ∀ s ∈ S', s ^ 2 ∈ S := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
    rw [sqrtF_sq]
    exact hz
  have hS'card : S'.card = S.card :=
    Finset.card_image_of_injective S sqrtF_injective
  have hfrobinj : Function.Injective (fun s : BFld => s ^ 2) := by
    intro a b hab
    exact frobenius_inj BFld 2 (by simpa [frobenius_def] using hab)
  have hYZsT : ∀ j a, ((T.coeff j).coeff a) ≠ 0 →
      ((T.coeff j).coeff a).natDegree + (2 * q) * j < 21907324 := by
    intro j a hja
    have hc := coeff_coeff_frobLift T j a
    rw [hTR] at hc
    have hne : (R.coeff (j * 2)).coeff (a * 2) ≠ 0 := by
      rw [hc]
      exact (Polynomial.map_ne_zero_iff (frobenius_inj BFld 2)).mpr hja
    have hdeg : ((R.coeff (j * 2)).coeff (a * 2)).natDegree = ((T.coeff j).coeff a).natDegree := by
      rw [hc, Polynomial.natDegree_map_eq_of_injective (frobenius_inj BFld 2)]
    have := hYZs (j * 2) (a * 2) hne
    rw [hdeg] at this
    nlinarith
  have hWT : ∀ j a, ((T.coeff j).coeff a) ≠ 0 → a + 1048575 * j < 7244000000 := by
    intro j a hja
    have hc := coeff_coeff_frobLift T j a
    rw [hTR] at hc
    have hne : (R.coeff (j * 2)).coeff (a * 2) ≠ 0 := by
      rw [hc]
      exact (Polynomial.map_ne_zero_iff (frobenius_inj BFld 2)).mpr hja
    have := hW (j * 2) (a * 2) hne
    omega
  obtain ⟨T', hT'S', hT'card, p₀, p₁, hp₀, hp₁, hline⟩ :=
    ih T.natDegree hd'lt (2 * q) U (fun s => P (s ^ 2)) (fun s => Arow (s ^ 2)) T S'
      (by omega) (by nlinarith) rfl hTirr hd'pos hYZsT hWT
      (fun s hs => hPdeg _ (hS'mem s hs))
      (by
        intro s hs
        have h := triEval_frobLift T s (P (s ^ 2))
        rw [hTR, hvan _ (hS'mem s hs)] at h
        exact pow_eq_zero_iff (by norm_num) |>.mp h.symm)
      (fun s hs => hrow _ (hS'mem s hs))
      (by
        intro s hs i hi
        rw [hagree _ (hS'mem s hs) i hi, ← pow_mul])
      (by
        rw [hS'card]
        exact lt_of_le_of_lt (sfCapU_mono (by omega)) hcard)
  refine ⟨T'.image (fun s => s ^ 2), ?_, ?_, p₀, p₁, hp₀, hp₁, ?_⟩
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact hS'mem s (hT'S' hs)
  · rw [Finset.card_image_of_injective T' hfrobinj]
    exact hT'card
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    rw [hline s hs, ← pow_mul]

/-- The polynomial alignment interface, proved in characteristic two. -/
theorem bchksPolynomialAlignment_char2 : BCHKSPolynomialAlignment := by
  classical
  intro U S A P Q hScard hQ hPdeg hAcard hagree hQeval hcaps
  let PE : BFld → BFld[X] := fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0
  have hQY : Q.natDegree ≤ 6902 := by
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlc
    have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a hca).1
    omega
  obtain ⟨Sgood, rfl, hSgoodS, hQz, hQevalgood, -, hlarge⟩ :=
    exists_bchks_Qbad_removal S PE Q hScard hQ
      (by intro z hz; simpa [PE, hz, BCHKSSubstitutionVanish.triEval, triEval,
        BCHKSSubstitutionVanish.specializeZ] using hQeval ⟨z, hz⟩)
      hQY (fun j a ha => (hcaps j a ha).2.2)
      (fun j a ha => (hcaps j a ha).2.1)
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  let RelR : BFld → Polynomial (Polynomial (Polynomial BFld)) → Prop :=
    fun z R => triEval R z (PE z) = 0
  have hRcover : ∀ z ∈ S.filter (fun z => triSpecializeZ Q z ≠ 0), ∃ R ∈ Rs, RelR z R := by
    intro z hz
    obtain ⟨R, hRQ, hRpos, hzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (PE z) (hQz z hz)
        (hQevalgood z hz)
    exact ⟨R, by simp [Rs, hRQ, hRpos], hzero⟩
  have hQY' : Q.natDegree ≤ 6901 := by
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlc
    have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a hca).1
    omega
  have hadd : (∑ R ∈ Rs, sfCapU R.natDegree) = sfCapU (∑ R ∈ Rs, R.natDegree) := by
    unfold sfCapU
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
  have hdsum : (∑ R ∈ Rs, R.natDegree) ≤ 6901 := by
    calc
      (∑ R ∈ Rs, R.natDegree) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset, R.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 6901 := hQY'
  have hsum : (∑ R ∈ Rs, sfCapU R.natDegree) ≤
      10125904 * 21907324 * 6901 + (bchksErrors + 1) * 6901 + 2 * 21907324 * 6901 := by
    rw [hadd]
    calc sfCapU (∑ R ∈ Rs, R.natDegree) ≤ sfCapU 6901 := sfCapU_mono hdsum
      _ = _ := by norm_num [sfCapU, uC, uDZ]
  obtain ⟨R, hRs, hRfib⟩ :=
    exists_rel_fiber_gt_capacity _ Rs RelR (fun R => sfCapU R.natDegree) hRcover
      (hsum.trans_lt hlarge)
  have hRm := Finset.mem_filter.mp hRs
  have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by simpa using hRm.1
  have hRpos : 0 < R.natDegree := hRm.2
  have hRirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hRdeg : R.natDegree ≤ 6901 := by
    calc
      R.natDegree ≤ ∑ B ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          B.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 6901 := hQY'
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 21907324 hQ hRQ
    (fun j a ha => (hcaps j a ha).2.2)
  have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap Q R 1048575 7244000000 hQ hRQ
    (fun j a ha => (hcaps j a ha).2.1)
  let SR := (S.filter fun z => triSpecializeZ Q z ≠ 0).filter fun z => RelR z R
  have hSRS : SR ⊆ S := fun z hz =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  obtain ⟨T, hTSR, hTcard, p₀, p₁, hp₀, hp₁, hline⟩ :=
    single_factor_alignment R.natDegree 1 U PE A R SR le_rfl (by omega) rfl hRirr hRpos
      (by intro j a ha; simpa using hRYZ j a ha) hRW
      (by
        intro z hz
        have hzS := hSRS hz
        simpa [PE, hzS] using hPdeg ⟨z, hzS⟩)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (by
        intro z hz
        have hzS := hSRS hz
        have := hAcard ⟨z, hzS⟩
        exact this)
      (by
        intro z hz i hi
        have hzS := hSRS hz
        simpa [PE, hzS] using hagree ⟨z, hzS⟩ i hi)
      hRfib
  refine ⟨p₀, p₁, T, hTSR.trans hSRS, hTcard, hp₀, hp₁, ?_⟩
  intro z hz
  have hzS := (hTSR.trans hSRS) hz
  simpa [PE, hzS] using hline z hz

end ProximityPrize.SubmissionBinaryLower
