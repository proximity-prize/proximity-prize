import ProximityPrize.SubmissionLower.PrimaryTaperBudget
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.KoalaTaperTransferReceipt

set_option Elab.async false

-- merged module PrimaryTaperMoments
section Merged_PrimaryTaperMoments

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace TaperMoments

open K1_13_2 (denominator cumulative)
open K1_13_2_2 (cumulativeColumns oldWeight CumulativeCount)
open TaperBudget (cap)
open Finset
open scoped BigOperators

open K1_13_2_3 (scaled_denominator polyDen denominator_of_neg)

/-- Twenty-four times the sum of the denominator counts at indices strictly below `n`. -/
def denPrefix (n : ℤ) : ℤ :=
  if n < 0 then 0 else
    let q := n / 6
    let r := n % 6
    984*q + 3084*q*(q-1) + 1728*q*(q-1)*(q-2) + 216*q*(q-1)*(q-2)*(q-3) +
      24*r + 4*r*(r-1)*(r+1) + 12*q*(44*r + 7*r*(r-1)) +
      4*q*r*(r-1)*(r-2) + 12*q*(q-1)*(57*r + 3*r*(r-1)) +
      144*r*q*(q-1)*(q-2)

theorem denPrefix_succ (n : ℤ) :
    denPrefix (n+1) = denPrefix n + 24 * denominator n := by
  by_cases hn : n < 0
  · rw [denominator_of_neg _ hn, show denPrefix n = 0 by simp [denPrefix, hn]]
    by_cases h : n + 1 < 0
    · simp [denPrefix, h]
    · have he : n + 1 = 0 := by omega
      rw [he]
      rfl
  have hn₁ : ¬ n + 1 < 0 := by omega
  have hden := scaled_denominator n (by omega)
  let q := n / 6
  let r := n % 6
  have hq : n / 6 = q := rfl
  have hr : n % 6 = r := rfl
  simp only [denPrefix, ite_eq_right hn, ite_eq_right hn₁, hq, hr]
  rw [hq, hr] at hden
  unfold polyDen at hden
  by_cases hf : r = 5
  · have hq₁ : (n+1)/6 = q+1 := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = 0 := by dsimp [r] at *; omega
    rw [hq₁, hr₁, hf]
    rw [hf] at hden
    linear_combination -12*hden
  · have hq₁ : (n+1)/6 = q := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = r+1 := by dsimp [r] at *; omega
    rw [hq₁, hr₁]
    linear_combination -12*hden

private theorem shift_succ (n a : ℤ) :
    denPrefix ((n+1)-a) = denPrefix (n-a) + 24 * denominator (n-a) := by
  rw [show n+1-a = (n-a)+1 by ring, denPrefix_succ]

def basePrefix (d u : ℤ) : ℤ :=
  denPrefix u - denPrefix (u-(d+1)) - denPrefix (u-(d+2)) - denPrefix (u-(d+3)) +
  denPrefix (u-(2*d+3)) + denPrefix (u-(2*d+4)) + denPrefix (u-(2*d+5)) -
  denPrefix (u-(3*d+6))

def cumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  basePrefix d u + 24 * ((n-u : ℕ) : ℤ) * cumulative d (3*d)

private theorem basePrefix_succ (d n : ℕ) (hn : n ≤ 3*d) :
    basePrefix d ((n : ℤ)+1) = basePrefix d n + 24 * cumulative d n := by
  have hzn : ¬ (n : ℤ) < 0 := by omega
  have hzd : ¬ (d : ℤ) < 0 := by omega
  have hnd : (n : ℤ) ≤ 3*d := by omega
  simp only [basePrefix, denPrefix_succ n, shift_succ, cumulative, hzn, hzd,
    Bool.false_or, decide_false, Bool.false_eq_true, ite_false, min_eq_left hnd]
  ring

theorem cumPrefix_succ (d n : ℕ) :
    cumPrefix d (n+1) = cumPrefix d n + 24 * cumulative d n := by
  by_cases h : n ≤ 3*d
  · simp only [cumPrefix, min_eq_left (show n+1 ≤ 3*d+1 by omega),
      min_eq_left (show n ≤ 3*d+1 by omega), Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul,
      add_zero, Nat.cast_add, Nat.cast_one, basePrefix_succ d n h]
  · have hcast : (3*d+1 : ℕ) ≤ n := by omega
    have hn : (3 : ℤ) * d ≤ n := by omega
    have he : cumulative d n = cumulative d (3*d) := by
      simp [cumulative, show ¬ (d : ℤ) < 0 by omega, show ¬ (n : ℤ) < 0 by omega,
        show ¬ (3 : ℤ)*d < 0 by omega, min_eq_right hn]
    simp only [cumPrefix, min_eq_right hcast,
      min_eq_right (show 3*d+1 ≤ n+1 by omega), he]
    have hsub : (n+1-(3*d+1) : ℕ) = n-(3*d+1)+1 := by omega
    simp only [hsub, Nat.cast_add, Nat.cast_one]
    ring

theorem cumulative_prefix (d n : ℕ) :
    24 * (∑ u ∈ range n, cumulative d (u : ℤ)) = cumPrefix d n := by
  induction n with
  | zero =>
      have hz (v : ℤ) (hv : v ≤ 0) : denPrefix v = 0 := by
        rcases lt_or_eq_of_le hv with h | rfl
        · simp [denPrefix, h]
        · rfl
      simp only [sum_range_zero, mul_zero, cumPrefix, zero_min, Nat.sub_zero, Nat.cast_zero,
        zero_mul, add_zero, basePrefix]
      symm
      simp only [hz 0 (le_refl _), hz (0-((d : ℤ)+1)) (by omega),
        hz (0-((d : ℤ)+2)) (by omega), hz (0-((d : ℤ)+3)) (by omega),
        hz (0-(2*(d : ℤ)+3)) (by omega), hz (0-(2*(d : ℤ)+4)) (by omega),
        hz (0-(2*(d : ℤ)+5)) (by omega), hz (0-(3*(d : ℤ)+6)) (by omega),
        sub_zero, add_zero]
  | succ n ih => rw [sum_range_succ, mul_add, ih, cumPrefix_succ d n]

/-- Weighted-index sum of the retained jets, scaled by 24. -/
def indexMoment (d : ℕ) : ℤ :=
  24 * 1650 * cumulative d 1650 - cumPrefix d 1650

private theorem count_range_ge (v j : ℕ) :
    (∑ u ∈ range j, if v ≤ u then (1 : ℕ) else 0) = j-v := by
  have hset : (range j).filter (fun u => v ≤ u) = Ico v j := by
    ext x
    simp [and_comm]
  rw [← sum_filter, ← card_eq_sum_ones, hset, Nat.card_Ico]

theorem indexMoment_eq (hc : CumulativeCount) (d : ℕ) :
    indexMoment d = 24 * ∑ e ∈ cumulativeColumns d 1650, (e.weight oldWeight : ℤ) := by
  let F := cumulativeColumns d 1650
  have hfilter (u : ℕ) (hu : u < 1650) :
      cumulativeColumns d u = F.filter (fun m => m.weight oldWeight ≤ u) := by
    ext m
    simp only [F, mem_filter, K1_13_2_2.mem_cumulativeColumns]
    change ((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ u) ↔
      (((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ 1650) ∧
        m.weight oldWeight ≤ u)
    omega
  have hswap : (∑ u ∈ range 1650, (cumulativeColumns d u).card) =
      ∑ e ∈ F, (1650 - e.weight oldWeight) := by
    calc
      _ = ∑ u ∈ range 1650, ∑ e ∈ F, if e.weight oldWeight ≤ u then 1 else 0 := by
        apply sum_congr rfl
        intro u hu
        rw [hfilter u (mem_range.mp hu), card_eq_sum_ones, sum_filter]
      _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun e _ => count_range_ge _ _
  have hcast : (∑ u ∈ range 1650, cumulative d (u : ℤ)) =
      ∑ e ∈ F, (1650 - (e.weight oldWeight : ℤ)) := by
    have hu (u : ℕ) := hc (d : ℤ) (u : ℤ)
    simp_rw [← hu]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    apply sum_congr rfl
    intro e he
    have h := (K1_13_2_2.mem_cumulativeColumns.mp he).2
    rw [Nat.cast_sub (by exact_mod_cast h), Nat.cast_ofNat]
  unfold indexMoment
  rw [← cumulative_prefix, hcast, ← hc d 1650]
  have hF : (cumulativeColumns d 1650).card = F.card := rfl
  rw [hF, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  ring

open TaperNormalize (differentiated Eligible)
open K1_13 (Geom)
open K1_13_2 (SourceExponent SourcePolynomial)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finsupp

def gradeCap (q : ℕ) : ℕ := min q (cap q)

def sourceCount : ℤ := ∑ q ∈ range 4013, cumulative (gradeCap q) 1650

def sourceDegree : ℤ := ∑ q ∈ range 4013, (q : ℤ) * cumulative (gradeCap q) 1650

def sourceIndex24 : ℤ := ∑ q ∈ range 4013, indexMoment (gradeCap q)

end TaperMoments

end Merged_PrimaryTaperMoments

-- merged module PrimaryTaperColumns
section Merged_PrimaryTaperColumns

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

namespace TaperColumns

noncomputable section

open K1_13 (Geom)
open K1_13_2 (SourceExponent SourcePolynomial topWeight cumulative)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns CumulativeCount)
open TaperMoments
open TaperBudget (cap)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial Finset
open scoped BigOperators

def Eligible (A D : ℕ) (e : SourceExponent) : Prop :=
  TaperNormalize.Eligible cap e ∧ e.weight (differentialWeight D) ≤ 3000 * A - 1

def exponents (A D : ℕ) : Set SourceExponent := {e | Eligible A D e}

theorem finite_exponents (A D : ℕ) (hD : 3 < D) : (exponents A D).Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) D) ?_
    (3000 * A - 1)).subset (fun e he => he.2)
  intro v
  cases v with
  | none => change 1 ≠ (0 : ℕ); decide
  | some j => exact (differentialWeight_some_pos_of_order_lt_degree hD j).ne'

noncomputable def columns (A D : ℕ) (hD : 3 < D) : Finset SourceExponent :=
  (finite_exponents A D hD).toFinset

noncomputable def Source (A D : ℕ) : Submodule Geom SourcePolynomial :=
  restrictSupport Geom (exponents A D)

instance (A D : ℕ) [Fact (3 < D)] : Module.Finite Geom (Source A D) :=
  restrictSupport_finite (finite_exponents A D Fact.out)

theorem finrank_source (A D : ℕ) (hD : 3 < D) :
    Module.finrank Geom (Source A D) = (columns A D hD).card := by
  have h : (↑(columns A D hD) : Set SourceExponent) = exponents A D :=
    Set.Finite.coe_toFinset (finite_exponents A D hD)
  rw [Source, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) (columns A D hD)

private abbrev vectors := Σ _ : ℕ, Σ _ : JetExp, ℕ

private def width (A D q : ℕ) (m : JetExp) : ℕ :=
  3000*A + m.weight oldWeight - D*q

private noncomputable def tuples (A D : ℕ) : Finset vectors :=
  (range 4013).sigma fun q =>
    (cumulativeColumns (gradeCap q) 1650).sigma fun m => range (width A D q m)

private def jetOf (e : SourceExponent) : JetExp := e.some

private def jetCount (e : SourceExponent) : ℕ := e.weight jetDegreeWeight

private def fill (q : ℕ) (m : JetExp) : JetExp := m + Finsupp.single 0 (q-gradeCap q)

private def trim (q : ℕ) (m : JetExp) : JetExp :=
  Finsupp.equivFunOnFinite.symm ![m 0 - (q-gradeCap q),m 1,m 2,m 3]

private def encode (u : vectors) : SourceExponent :=
  (fill u.1 u.2.1).optionElim u.2.2

private def decode (e : SourceExponent) : vectors :=
  ⟨jetCount e, trim (jetCount e) (jetOf e), e none⟩

theorem sumCount (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]

theorem sumIndex (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]

theorem sumDifferentiated (e : SourceExponent) :
    e.weight TaperNormalize.differentiated = e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, TaperNormalize.differentiated]

private theorem sumTop (e : SourceExponent) : e.weight topWeight = e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight,
    Pi.single_apply, smul_eq_mul]

theorem sumOld (m : JetExp) : m.weight oldWeight = m 1 + 2*m 2 + 3*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, oldWeight, smul_eq_mul, Nat.mul_comm]

theorem sumGrade (m : JetExp) : m.weight gradeWeight = m 0 + m 1 + m 2 + m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, smul_eq_mul]

private theorem weight_add (D : ℕ) (hD : 3 < D) (e : SourceExponent) :
    e.weight (differentialWeight D) + e.weight jetDerivativeWeight =
      e none + D * (e.weight jetDegreeWeight) := by
  rw [sumIndex, sumCount]
  have hs (j a : ℕ) (hj : j ≤ D) : (D-j)*a + j*a = D*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj]
  simp only [Finsupp.weight_eq_sum, Fintype.sum_option, differentialWeight, smul_eq_mul, Nat.mul_one]
  rw [Fin.sum_univ_four]
  change e none + (e (some 0) * D + e (some 1) * (D-1) + e (some 2) * (D-2) +
    e (some 3) * (D-3)) + (e (some 1) + 2 * e (some 2) + 3 * e (some 3)) =
      e none + D * (e (some 0) + e (some 1) + e (some 2) + e (some 3))
  rw [Nat.mul_comm (e (some 0)) D, Nat.mul_comm (e (some 1)) (D-1), Nat.mul_comm (e (some 2)) (D-2),
    Nat.mul_comm (e (some 3)) (D-3)]
  simp only [Nat.mul_add]
  have h₁ := hs 1 (e (some 1)) (by omega)
  have h₂ := hs 2 (e (some 2)) (by omega)
  have h₃ := hs 3 (e (some 3)) (by omega)
  omega

private theorem eligible_iff (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (e : SourceExponent) :
    Eligible A D e ↔
      e.weight jetDegreeWeight ≤ 4012 ∧ e.weight jetDerivativeWeight ≤ 1650 ∧
      e.weight TaperNormalize.differentiated ≤ cap (e.weight jetDegreeWeight) ∧
      e none < 3000*A + e.weight jetDerivativeWeight - D*(e.weight jetDegreeWeight) := by
  unfold Eligible TaperNormalize.Eligible
  have hw := weight_add D hD e
  have hj := sumIndex e
  have ht := sumTop e
  omega

private theorem fill_succ (q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) : fill q m i = m i := by
  simp [fill, Finsupp.single_eq_of_ne hi]

private theorem fill_zero (q : ℕ) (m : JetExp) : fill q m 0 = m 0 + (q-gradeCap q) := by
  simp [fill]

private theorem trim_succ (q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) : trim q m i = m i := by
  fin_cases i <;> simp_all [trim]

private theorem trim_zero (q : ℕ) (m : JetExp) : trim q m 0 = m 0 - (q-gradeCap q) := by
  simp [trim]

private theorem jetOf_some (e : SourceExponent) (i : Fin 4) : jetOf e i = e (some i) := by
  rfl

private theorem encode_some (u : vectors) (i : Fin 4) : encode u (some i) = fill u.1 u.2.1 i := by
  simp [encode]

private theorem encode_none (u : vectors) : encode u none = u.2.2 := by simp [encode]

private theorem encode_grade (q : ℕ) (m : JetExp) (x : ℕ)
    (hm : m.weight gradeWeight = gradeCap q) :
    (encode ⟨q,m,x⟩).weight jetDegreeWeight = q := by
  rw [sumGrade] at hm
  rw [sumCount, encode_some, encode_some, encode_some, encode_some,
    fill_zero, fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]
  change (m 0+(q-gradeCap q))+m 1+m 2+m 3 = q
  have hq : gradeCap q ≤ q := min_le_left _ _
  omega

private theorem encode_index (q : ℕ) (m : JetExp) (x : ℕ) :
    (encode ⟨q,m,x⟩).weight jetDerivativeWeight = m.weight oldWeight := by
  rw [sumIndex, sumOld, encode_some, encode_some, encode_some,
    fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]

private theorem decode_mem (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (e : SourceExponent)
    (he : e ∈ columns A D hD) : decode e ∈ tuples A D := by
  have he' : Eligible A D e := by
    change e ∈ exponents A D
    simpa only [columns, Set.Finite.mem_toFinset] using he
  obtain ⟨hq, hj, hd, hx⟩ := (eligible_iff A D hA hD e).mp he'
  let q := jetCount e
  let m := trim q (jetOf e)
  change ⟨q,m,e none⟩ ∈ tuples A D
  have hv : e (some 1) + e (some 2) + e (some 3) ≤ gradeCap q := by
    rw [sumDifferentiated] at hd
    have h := sumCount e
    exact le_min (by unfold q jetCount; omega) hd
  have hdeg : m.weight gradeWeight = gradeCap q := by
    rw [sumGrade, show m = trim q (jetOf e) by rfl, trim_zero,
      trim_succ _ _ 1 (by decide), trim_succ _ _ 2 (by decide), trim_succ _ _ 3 (by decide)]
    simp only [jetOf_some]
    have h := sumCount e
    change q = _ at h
    have hcap : gradeCap q ≤ q := min_le_left _ _
    omega
  have hidx : m.weight oldWeight = e.weight jetDerivativeWeight := by
    rw [sumOld, sumIndex, show m = trim q (jetOf e) by rfl,
      trim_succ _ _ 1 (by decide), trim_succ _ _ 2 (by decide), trim_succ _ _ 3 (by decide)]
    simp only [jetOf_some]
  have hq' : q ∈ range 4013 := mem_range.mpr (Nat.lt_succ_of_le hq)
  refine mem_sigma.mpr ⟨hq', mem_sigma.mpr ⟨?_,?_⟩⟩
  · exact K1_13_2_2.mem_cumulativeColumns.mpr ⟨by exact_mod_cast hdeg, by exact_mod_cast hidx.trans_le hj⟩
  · exact mem_range.mpr (by rwa [width, hidx])

private theorem encode_mem (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (u : vectors)
    (hu : u ∈ tuples A D) : encode u ∈ columns A D hD := by
  obtain ⟨q,m,x⟩ := u
  obtain ⟨hq, hm, hx⟩ := by simpa only [tuples, mem_sigma, mem_range] using hu
  have hme := K1_13_2_2.mem_cumulativeColumns.mp hm
  have hgrade : m.weight gradeWeight = gradeCap q := by exact_mod_cast hme.1
  have hidx : m.weight oldWeight ≤ 1650 := by exact_mod_cast hme.2
  rw [columns, Set.Finite.mem_toFinset]
  change Eligible A D (encode ⟨q,m,x⟩)
  apply (eligible_iff A D hA hD _).mpr
  rw [encode_grade _ _ _ hgrade, encode_index, encode_none]
  refine ⟨by omega, hidx, ?_, hx⟩
  rw [sumDifferentiated, encode_some, encode_some, encode_some,
    fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]
  rw [sumGrade] at hgrade
  have := min_le_right q (cap q)
  unfold gradeCap at hgrade
  change m 1+m 2+m 3 ≤ cap q
  omega

private theorem encode_decode (A D : ℕ) (hA : 0 < A) (hD : 3 < D)
    (e : SourceExponent) (he : e ∈ columns A D hD) : encode (decode e) = e := by
  have he' : Eligible A D e := by
    change e ∈ exponents A D
    simpa only [columns, Set.Finite.mem_toFinset] using he
  obtain ⟨_, _, hd, _⟩ := (eligible_iff A D hA hD e).mp he'
  have hv : e (some 1) + e (some 2) + e (some 3) ≤ gradeCap (jetCount e) := by
    rw [sumDifferentiated] at hd
    have h := sumCount e
    exact le_min (by unfold jetCount; omega) hd
  ext v
  cases v with
  | none => rw [encode_none]; rfl
  | some i =>
    rw [encode_some]
    change fill (jetCount e) (trim (jetCount e) (jetOf e)) i = _
    by_cases hi : i = 0
    · subst i
      rw [fill_zero, trim_zero, jetOf_some, Nat.sub_add_cancel]
      have h := sumCount e
      change jetCount e = _ at h
      omega
    · rw [fill_succ _ _ _ hi, trim_succ _ _ _ hi, jetOf_some]

private theorem decode_encode (A D : ℕ) (u : vectors) (hu : u ∈ tuples A D) :
    decode (encode u) = u := by
  obtain ⟨q,m,x⟩ := u
  obtain ⟨_, hm, _⟩ := by simpa only [tuples, mem_sigma, mem_range] using hu
  have hgrade : m.weight gradeWeight = gradeCap q :=
    by exact_mod_cast (K1_13_2_2.mem_cumulativeColumns.mp hm).1
  have hq : jetCount (encode ⟨q,m,x⟩) = q := encode_grade _ _ _ hgrade
  have hm' : trim q (jetOf (encode ⟨q,m,x⟩)) = m := by
    ext i
    by_cases hi : i = 0
    · subst i
      rw [trim_zero, jetOf_some, encode_some, fill_zero, Nat.add_sub_cancel]
    · rw [trim_succ _ _ _ hi, jetOf_some, encode_some, fill_succ _ _ _ hi]
  simp [decode, hq, hm', encode_none]

theorem card_columns (A D : ℕ) (hA : 0 < A) (hD : 3 < D) :
    (columns A D hD).card = (tuples A D).card := by
  exact Finset.card_bij' (fun e _ => decode e) (fun u _ => encode u)
    (decode_mem A D hA hD) (encode_mem A D hA hD) (encode_decode A D hA hD) (decode_encode A D)


private theorem scaled_grade_columns (hc : CumulativeCount) (A D q : ℕ)
    (hb : D*q ≤ 3000*A) :
    24 * (∑ e ∈ cumulativeColumns (gradeCap q) 1650, (width A D q e : ℤ)) =
      (24 * (3000*(A : ℤ) - (D : ℤ)*q)) * cumulative (gradeCap q) 1650 +
        indexMoment (gradeCap q) := by
  let d := gradeCap q
  have hwidth (e : JetExp) :
      (width A D q e : ℤ) = ((3000 : ℤ)*A - D*q) + e.weight oldWeight := by
    have hsub : D*q ≤ 3000*A + e.weight oldWeight := by omega
    simp only [width, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simp_rw [hwidth]
  rw [Finset.sum_add_distrib, mul_add]
  rw [indexMoment_eq hc, ← hc (gradeCap q : ℤ) 1650]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem scaled_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hb : D*4012 ≤ 3000*A) :
    24 * ((columns A D hD).card : ℤ) =
      24*(3000*(A : ℤ))*sourceCount - (24*(D : ℤ))*sourceDegree + sourceIndex24 := by
  rw [card_columns A D hA hD]
  simp only [tuples, card_sigma, card_range, Nat.cast_sum]
  rw [mul_sum]
  have hsum : (∑ q ∈ range 4013,
      24 * (∑ e ∈ cumulativeColumns (gradeCap q) 1650, (width A D q e : ℤ))) =
      ∑ q ∈ range 4013,
        (24*(3000*(A : ℤ))*cumulative (gradeCap q) 1650 -
          (24*(D : ℤ))*((q : ℤ)*cumulative (gradeCap q) 1650) + indexMoment (gradeCap q)) := by
    apply sum_congr rfl
    intro q hq
    have hq' : q ≤ 4012 := by have := mem_range.mp hq; omega
    rw [scaled_grade_columns K1_13_2_2_2.proof A D q
      ((Nat.mul_le_mul_left D hq').trans hb)]
    ring
  rw [hsum, sum_add_distrib, sum_sub_distrib]
  simp only [sourceCount, sourceDegree, sourceIndex24, mul_sum]


def jetExponents : Set JetExp :=
  {m | m.weight gradeWeight ≤ 4012 ∧ m.weight oldWeight ≤ 1650 ∧
    m 1 + m 2 + m 3 ≤ cap (m.weight gradeWeight)}

theorem jetExponents_finite : jetExponents.Finite :=
  (Finsupp.finite_of_nat_weight_le gradeWeight (fun j => by simp [gradeWeight]) 4012).subset
    (fun _ h => h.1)

noncomputable def jetColumns : Finset JetExp := jetExponents_finite.toFinset

private noncomputable def jetTuples : Finset (Σ _ : ℕ, JetExp) :=
  (range 4013).sigma fun q => cumulativeColumns (gradeCap q) 1650

private theorem jet_mem_source_zero (m : JetExp) :
    (m.optionElim 0) ∈ columns 1000000 4 (by decide) ↔ m ∈ jetExponents := by
  rw [columns, Set.Finite.mem_toFinset]
  change Eligible 1000000 4 (m.optionElim 0) ↔ _
  rw [eligible_iff _ _ (by decide) (by decide), sumCount, sumIndex, sumDifferentiated]
  simp only [Finsupp.optionElim_apply_some, Finsupp.optionElim_apply_none]
  change m 0 + m 1 + m 2 + m 3 ≤ 4012 ∧ m 1 + 2*m 2 + 3*m 3 ≤ 1650 ∧
      m 1 + m 2 + m 3 ≤ cap (m 0 + m 1 + m 2 + m 3) ∧
      0 < 3000*1000000 + (m 1+2*m 2+3*m 3) - 4*(m 0+m 1+m 2+m 3) ↔
    m.weight gradeWeight ≤ 4012 ∧ m.weight oldWeight ≤ 1650 ∧
      m 1+m 2+m 3 ≤ cap (m.weight gradeWeight)
  rw [sumGrade, sumOld]
  omega

theorem jet_card_eq : (jetColumns.card : ℤ) = sourceCount := by
  have h : jetColumns.card = jetTuples.card := by
    refine card_bij' (fun m _ => ⟨m.weight gradeWeight, trim (m.weight gradeWeight) m⟩)
      (fun u _ => fill u.1 u.2) ?_ ?_ ?_ ?_
    · intro m hm
      have hmem : m ∈ jetExponents := by simpa only [jetColumns, Set.Finite.mem_toFinset] using hm
      have he := (jet_mem_source_zero m).mpr hmem
      have ht := decode_mem 1000000 4 (by decide) (by decide) (m.optionElim 0) he
      have hg : jetCount (m.optionElim 0) = m.weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [Finsupp.optionElim_apply_some]
      have hj : jetOf (m.optionElim 0) = m := by ext i; rw [jetOf_some, Finsupp.optionElim_apply_some]
      change decode (m.optionElim 0) ∈ tuples 1000000 4 at ht
      simp only [decode, hg, hj, tuples, mem_sigma] at ht
      exact mem_sigma.mpr ⟨ht.1, ht.2.1⟩
    · rintro ⟨q,m⟩ hm
      have hq : q ∈ range 4013 := (mem_sigma.mp hm).1
      have hJ : m ∈ cumulativeColumns (gradeCap q) 1650 := (mem_sigma.mp hm).2
      have hwidth : 0 < width 1000000 4 q m := by
        have := mem_range.mp hq
        unfold width
        omega
      have h := encode_mem 1000000 4 (by decide) (by decide) ⟨q,m,0⟩
        (mem_sigma.mpr ⟨hq, mem_sigma.mpr ⟨hJ, mem_range.mpr hwidth⟩⟩)
      simpa only [jetColumns, Set.Finite.mem_toFinset] using (jet_mem_source_zero (fill q m)).mp h
    · intro m hm
      have h := encode_decode 1000000 4 (by decide) (by decide) (m.optionElim 0)
        ((jet_mem_source_zero m).mpr (by simpa only [jetColumns, Set.Finite.mem_toFinset] using hm))
      have hg : jetCount (m.optionElim 0) = m.weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [Finsupp.optionElim_apply_some]
      have hj : jetOf (m.optionElim 0) = m := by ext i; rw [jetOf_some, Finsupp.optionElim_apply_some]
      ext i
      have hi := congrArg (fun e : SourceExponent => e (some i)) h
      simpa only [decode, encode_some, hg, hj, Finsupp.optionElim_apply_some] using hi
    · rintro ⟨q,m⟩ hm
      have hq : q ∈ range 4013 := (mem_sigma.mp hm).1
      have hJ : m ∈ cumulativeColumns (gradeCap q) 1650 := (mem_sigma.mp hm).2
      have hwidth : 0 < width 1000000 4 q m := by
        have := mem_range.mp hq
        unfold width
        omega
      have h := decode_encode 1000000 4 ⟨q,m,0⟩
        (mem_sigma.mpr ⟨hq, mem_sigma.mpr ⟨hJ, mem_range.mpr hwidth⟩⟩)
      have hg : jetCount (encode ⟨q,m,0⟩) = (fill q m).weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [encode_some]
      have hj : jetOf (encode ⟨q,m,0⟩) = fill q m := by ext i; rw [jetOf_some, encode_some]
      simpa only [decode, hg, hj] using congrArg (fun u : vectors => (⟨u.1, u.2.1⟩ : Σ _ : ℕ, JetExp)) h
  rw [h, jetTuples, card_sigma, Nat.cast_sum, sourceCount]
  apply sum_congr rfl
  intro q _
  exact K1_13_2_2_2.proof _ _

end
end TaperColumns

end Merged_PrimaryTaperColumns

-- merged module PrimaryTaperColumnData
section Merged_PrimaryTaperColumnData
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace TaperColumns
open K1_13_2 (cumulative)
open TaperMoments
open Finset
open scoped BigOperators
private abbrev Moments := ℤ × ℤ × ℤ
private def combine (a b : Moments) : Moments := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)
open K1_13_2 (denominator)
open TaperMoments (basePrefix)
private theorem upper_den : denominator 1650 = 125576826 := by decide +kernel
private theorem upper_prefix : denPrefix 1650 = 1244339514000 := by decide +kernel
private def fastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - denominator (1650-d-1) - denominator (1650-d-2) -
      denominator (1650-d-3)
  else cumulative d 1650
private def fastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - denPrefix (1650-(d+1)) - denPrefix (1650-(d+2)) -
      denPrefix (1650-(d+3))
  else cumPrefix d 1650
private theorem fastCount_eq (d : ℕ) : fastCount d = cumulative d 1650 := by
  by_cases hd : 824 ≤ d
  · have hz : ¬ (d : ℤ) < 0 := by omega
    have hmin : (1650 : ℤ) ≤ 3*d := by omega
    have h1 : (1650 : ℤ) - 2*d - 3 < 0 := by omega
    have h2 : (1650 : ℤ) - 2*d - 4 < 0 := by omega
    have h3 : (1650 : ℤ) - 2*d - 5 < 0 := by omega
    have h4 : (1650 : ℤ) - 3*d - 6 < 0 := by omega
    simp only [fastCount, if_pos hd, cumulative, hz, not_lt.mpr (by decide : (0 : ℤ) ≤ 1650),
      decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_left hmin]
    have hn (u : ℤ) (hu : u < 0) : denominator u = 0 := by simp [denominator, hu]
    rw [hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_den]
    simp
  · simp [fastCount, hd]
private theorem fastPrefix_eq (d : ℕ) : fastPrefix d = cumPrefix d 1650 := by
  by_cases hd : 824 ≤ d
  · have hmin : 1650 ≤ 3*d+1 := by omega
    have h1 : (1650 : ℤ) - (2*d+3) < 0 := by omega
    have h2 : (1650 : ℤ) - (2*d+4) < 0 := by omega
    have h3 : (1650 : ℤ) - (2*d+5) < 0 := by omega
    have h4 : (1650 : ℤ) - (3*d+6) < 0 := by omega
    have hn (u : ℤ) (hu : u < 0) : denPrefix u = 0 := by simp [denPrefix, hu]
    simp only [fastPrefix, if_pos hd, cumPrefix, min_eq_left hmin, Nat.sub_self,
      Nat.cast_zero, mul_zero, zero_mul, add_zero, basePrefix, Nat.cast_ofNat,
      hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_prefix, sub_zero]
  · simp [fastPrefix, hd]
private def oneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := fastCount d
  (n, (q : ℤ)*n, fastPrefix d)
private def moments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (moments lo n) (oneRow (lo+n))
private def twiceDenN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  2 + r * (r + 1) + q * (11 + r * (7 + r) + q * (21 + 6 * r + 12 * q))
private def denPrefixN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  r * (20 + 4 * r * r) +
    q * (60 + r * (92 + r * (36 + 4 * r)) +
      q * (276 + r * (216 + 36 * r) + q * (432 + 144 * r + 216 * q)))
private def fden : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (twiceDenN n / 2)
  | Int.negSucc _ => 0
private def fpre : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (denPrefixN n)
  | Int.negSucc _ => 0
private theorem twice_pred (q : ℤ) : 2 * (q * (q - 1) / 2) = q * (q - 1) := by
  have h : (2 : ℤ) ∣ q * (q - 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem twice_succ (q : ℤ) : 2 * (q * (q + 1) / 2) = q * (q + 1) := by
  have h : (2 : ℤ) ∣ q * (q + 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q + 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem den_nat (n : ℕ) : 2 * K1_13_2.denominator (n : ℤ) = (twiceDenN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  have h1 := twice_succ ((n : ℤ) % 6)
  have h2 := twice_pred ((n : ℤ) % 6)
  have h3 := twice_pred ((n : ℤ) / 6)
  simp only [K1_13_2.denominator, hn, ite_false]
  unfold twiceDenN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  linear_combination h1 + ((n : ℤ) / 6) * h2 + (57 + 6 * ((n : ℤ) % 6)) * h3
private theorem fden_eq (u : ℤ) : fden u = K1_13_2.denominator u := by
  rcases u with n | m
  · show ((twiceDenN n / 2 : ℕ) : ℤ) = K1_13_2.denominator (n : ℤ)
    have h := den_nat n
    omega
  · show (0 : ℤ) = K1_13_2.denominator (Int.negSucc m)
    simp [K1_13_2.denominator, Int.negSucc_lt_zero]
private theorem pre_nat (n : ℕ) : TaperMoments.denPrefix (n : ℤ) = (denPrefixN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  simp only [TaperMoments.denPrefix, hn, ite_false]
  unfold denPrefixN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  ring
private theorem fpre_eq (u : ℤ) : fpre u = TaperMoments.denPrefix u := by
  rcases u with n | m
  · show ((denPrefixN n : ℕ) : ℤ) = TaperMoments.denPrefix (n : ℤ)
    exact (pre_nat n).symm
  · show (0 : ℤ) = TaperMoments.denPrefix (Int.negSucc m)
    simp [TaperMoments.denPrefix, Int.negSucc_lt_zero]
private def fcum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    fden v - fden (v - d - 1) - fden (v - d - 2) -
      fden (v - d - 3) + fden (v - 2 * d - 3) +
      fden (v - 2 * d - 4) + fden (v - 2 * d - 5) -
      fden (v - 3 * d - 6)
private theorem fcum_eq (d u : ℤ) : fcum d u = cumulative d u := by
  unfold fcum cumulative
  rw [show fden = K1_13_2.denominator from funext fden_eq]
private def fbase (d u : ℤ) : ℤ :=
  fpre u - fpre (u-(d+1)) - fpre (u-(d+2)) - fpre (u-(d+3)) +
  fpre (u-(2*d+3)) + fpre (u-(2*d+4)) + fpre (u-(2*d+5)) -
  fpre (u-(3*d+6))
private theorem fbase_eq (d u : ℤ) : fbase d u = basePrefix d u := by
  unfold fbase basePrefix
  rw [show fpre = TaperMoments.denPrefix from funext fpre_eq]
private def fcumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  fbase d u + 24 * ((n-u : ℕ) : ℤ) * fcum d (3*d)
private theorem fcumPrefix_eq (d n : ℕ) : fcumPrefix d n = cumPrefix d n := by
  unfold fcumPrefix cumPrefix
  rw [show fbase = basePrefix from funext₂ fbase_eq, show fcum = cumulative from funext₂ fcum_eq]
private def ffastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - fden (1650-d-1) - fden (1650-d-2) -
      fden (1650-d-3)
  else fcum d 1650
private theorem ffastCount_eq (d : ℕ) : ffastCount d = fastCount d := by
  unfold ffastCount fastCount
  simp only [fden_eq, fcum_eq]
private def ffastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - fpre (1650-(d+1)) - fpre (1650-(d+2)) -
      fpre (1650-(d+3))
  else fcumPrefix d 1650
private theorem ffastPrefix_eq (d : ℕ) : ffastPrefix d = fastPrefix d := by
  unfold ffastPrefix fastPrefix
  simp only [fpre_eq, fcumPrefix_eq]
private def foneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := ffastCount d
  (n, (q : ℤ)*n, ffastPrefix d)
private theorem foneRow_eq (q : ℕ) : foneRow q = oneRow q := by
  unfold foneRow oneRow
  simp only [ffastCount_eq, ffastPrefix_eq]
private def fmoments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (fmoments lo n) (foneRow (lo+n))
private theorem moments_fast (lo n : ℕ) : moments lo n = fmoments lo n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [moments, fmoments, ih, foneRow_eq]
private theorem moments_split (lo a b : ℕ) :
    moments lo (a+b) = combine (moments lo a) (moments (lo+a) b) := by
  induction b with
  | zero => simp [moments, combine]
  | succ b ih => rw [Nat.add_succ, moments, moments, ih, Nat.add_assoc]
                 simp only [combine, Int.add_assoc]
private theorem moments_eq (n : ℕ) :
    moments 0 n =
      (∑ q ∈ range n, cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, (q : ℤ)*cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, cumPrefix (gradeCap q) 1650) := by
  induction n with
  | zero => simp [moments]
  | succ n ih => simp only [moments, ih, sum_range_succ, oneRow, combine, Nat.zero_add, fastCount_eq, fastPrefix_eq]
private theorem plateau_count : cumulative ((1650 : ℕ) : ℤ) 1650 = 125576826 := by decide +kernel
private theorem plateau_prefix : cumPrefix 1650 1650 = 1244339514000 := by decide +kernel
private theorem plateau_row (q : ℕ) (lo : 1650 ≤ q) (hi : q < 3514) :
    oneRow q = (125576826, (q : ℤ) * 125576826, 1244339514000) := by
  have hcap : gradeCap q = 1650 := by
    simp only [gradeCap, TaperBudget.cap, if_pos hi, min_eq_right lo]
  simp only [oneRow, hcap, fastCount_eq, fastPrefix_eq, plateau_count, plateau_prefix]
private theorem plateau_components (lo n : ℕ) (start : 1650 ≤ lo) (finish : lo + n ≤ 3514) :
    (moments lo n).1 = (n : ℤ) * 125576826 ∧
    2 * (moments lo n).2.1 = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826 ∧
    (moments lo n).2.2 = (n : ℤ) * 1244339514000 := by
  induction n with
  | zero => norm_num [moments]
  | succ n ih =>
    obtain ⟨hc, hd, hj⟩ := ih (by omega)
    have hr := plateau_row (lo + n) (by omega) (by omega)
    simp only [moments, hr, combine, Nat.cast_succ, Nat.cast_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      ring
    · rw [mul_add, hd]
      ring
    · rw [hj]
      ring
private theorem plateau_value (lo n : ℕ) (s : ℤ) (start : 1650 ≤ lo)
    (finish : lo + n ≤ 3514)
    (mid : 2 * s = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826) :
    moments lo n = ((n : ℤ) * 125576826, s, (n : ℤ) * 1244339514000) := by
  obtain ⟨hc, hd, hj⟩ := plateau_components lo n start finish
  have hs : (moments lo n).2.1 = s := by linarith only [hd, mid]
  exact Prod.ext hc (Prod.ext hs hj)
private theorem chunk0 : moments 0 64 = (766480, 38630592, 28961906688) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk64 : moments 64 64 = (10950160, 1151780032, 392162254848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk128 : moments 128 64 = (46692880, 7734564032, 1570593742848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk192 : moments 192 64 = (124771856, 28444026048, 3916980559872) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk256 : moments 256 64 = (261964304, 76232176832, 7629428072448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk320 : moments 320 64 = (475047440, 168345994432, 12751422824448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk384 : moments 384 64 = (780798480, 326327424192, 19171832537088) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk448 : moments 448 64 = (1195994640, 576013378752, 26624906108928) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk512 : moments 512 64 = (1737323150, 947484425540, 34690308784824) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk576 : moments 576 64 = (2409438080, 1467615274816, 42809297555328) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk640 : moments 640 64 = (3172139904, 2134302060352, 50424594575232) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk704 : moments 704 64 = (3967085440, 2922016831296, 57144114876288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk768 : moments 768 64 = (4735554768, 3790003814602, 62768847096768) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk832 : moments 832 64 = (5423001088, 4686152908112, 67290168195456) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk896 : moments 896 64 = (6008952320, 5576166392144, 70835420387712) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk960 : moments 960 64 = (6500007424, 6447136851280, 73555743947136) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1024 : moments 1024 64 = (6904555008, 7289698404688, 75590356212096) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1088 : moments 1088 64 = (7230983680, 8096632655184, 77065589619072) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1152 : moments 1152 64 = (7487682048, 8862868689232, 78094891702656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1216 : moments 1216 64 = (7683038720, 9585483076944, 78778825095552) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1280 : moments 1280 64 = (7825442304, 10263699872080, 79205067528576) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1344 : moments 1344 64 = (7923281408, 10898890612048, 79448411830656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1408 : moments 1408 64 = (7984944640, 11494574317904, 79570765928832) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1472 : moments 1472 64 = (8018820608, 12056417494352, 79621152848256) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1536 : moments 1536 64 = (8033297920, 12592234129744, 79635710712192) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1600 : moments 1600 50 = (6278689200, 10199732826645, 62216939575080) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1650 : moments 1650 1864 = (234075203664, 604265138258616, 2319448854096000) :=
  plateau_value 1650 1864 604265138258616 (by decide) (by decide) (by decide)
private theorem chunk3514 : moments 3514 6 = (753368160, 2649219120421, 7466006383320) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3520 : moments 3520 64 = (8032072282, 28525854344641, 79634768477448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3584 : moments 3584 64 = (8014274720, 28975464060405, 79615399984032) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3648 : moments 3648 64 = (7973908122, 29339703821282, 79551178982208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3712 : moments 3712 64 = (7901339158, 29578175247143, 79398146595168) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3776 : moments 3776 64 = (7787486114, 29650119438357, 79098473674512) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3840 : moments 3840 64 = (7622412918, 29509140942244, 78577078832208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3904 : moments 3904 64 = (7397254232, 29110514169461, 77746943352288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3968 : moments 3968 45 = (5029151191, 20065722297522, 53950645283400) := by
  rw [moments_fast]
  decide +kernel
private theorem join (lo n m next full : ℕ) (a b result : Moments)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : combine a b = result)
    (ha : moments lo n = a) (hb : moments next m = b) :
    moments lo full = result := by
  rw [← hLen, moments_split, ha, hStart, hb]
  exact hValue
private theorem checked : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) := by
  have tail3968 := chunk3968
  have tail3904 : moments 3904 109 = (12426405423, 49176236466983, 131697588635688) :=
    join 3904 64 45 3968 109 (7397254232, 29110514169461, 77746943352288) (5029151191, 20065722297522, 53950645283400) (12426405423, 49176236466983, 131697588635688) (by decide) (by decide) (by decide) chunk3904 tail3968
  have tail3840 : moments 3840 173 = (20048818341, 78685377409227, 210274667467896) :=
    join 3840 64 109 3904 173 (7622412918, 29509140942244, 78577078832208) (12426405423, 49176236466983, 131697588635688) (20048818341, 78685377409227, 210274667467896) (by decide) (by decide) (by decide) chunk3840 tail3904
  have tail3776 : moments 3776 237 = (27836304455, 108335496847584, 289373141142408) :=
    join 3776 64 173 3840 237 (7787486114, 29650119438357, 79098473674512) (20048818341, 78685377409227, 210274667467896) (27836304455, 108335496847584, 289373141142408) (by decide) (by decide) (by decide) chunk3776 tail3840
  have tail3712 : moments 3712 301 = (35737643613, 137913672094727, 368771287737576) :=
    join 3712 64 237 3776 301 (7901339158, 29578175247143, 79398146595168) (27836304455, 108335496847584, 289373141142408) (35737643613, 137913672094727, 368771287737576) (by decide) (by decide) (by decide) chunk3712 tail3776
  have tail3648 : moments 3648 365 = (43711551735, 167253375916009, 448322466719784) :=
    join 3648 64 301 3712 365 (7973908122, 29339703821282, 79551178982208) (35737643613, 137913672094727, 368771287737576) (43711551735, 167253375916009, 448322466719784) (by decide) (by decide) (by decide) chunk3648 tail3712
  have tail3584 : moments 3584 429 = (51725826455, 196228839976414, 527937866703816) :=
    join 3584 64 365 3648 429 (8014274720, 28975464060405, 79615399984032) (43711551735, 167253375916009, 448322466719784) (51725826455, 196228839976414, 527937866703816) (by decide) (by decide) (by decide) chunk3584 tail3648
  have tail3520 : moments 3520 493 = (59757898737, 224754694321055, 607572635181264) :=
    join 3520 64 429 3584 493 (8032072282, 28525854344641, 79634768477448) (51725826455, 196228839976414, 527937866703816) (59757898737, 224754694321055, 607572635181264) (by decide) (by decide) (by decide) chunk3520 tail3584
  have tail3514 : moments 3514 499 = (60511266897, 227403913441476, 615038641564584) :=
    join 3514 6 493 3520 499 (753368160, 2649219120421, 7466006383320) (59757898737, 224754694321055, 607572635181264) (60511266897, 227403913441476, 615038641564584) (by decide) (by decide) (by decide) chunk3514 tail3520
  have tail1650 : moments 1650 2363 = (294586470561, 831669051700092, 2934487495660584) :=
    join 1650 1864 499 3514 2363 (234075203664, 604265138258616, 2319448854096000) (60511266897, 227403913441476, 615038641564584) (294586470561, 831669051700092, 2934487495660584) (by decide) (by decide) (by decide) chunk1650 tail3514
  have tail1600 : moments 1600 2413 = (300865159761, 841868784526737, 2996704435235664) :=
    join 1600 50 2363 1650 2413 (6278689200, 10199732826645, 62216939575080) (294586470561, 831669051700092, 2934487495660584) (300865159761, 841868784526737, 2996704435235664) (by decide) (by decide) (by decide) chunk1600 tail1650
  have tail1536 : moments 1536 2477 = (308898457681, 854461018656481, 3076340145947856) :=
    join 1536 64 2413 1600 2477 (8033297920, 12592234129744, 79635710712192) (300865159761, 841868784526737, 2996704435235664) (308898457681, 854461018656481, 3076340145947856) (by decide) (by decide) (by decide) chunk1536 tail1600
  have tail1472 : moments 1472 2541 = (316917278289, 866517436150833, 3155961298796112) :=
    join 1472 64 2477 1536 2541 (8018820608, 12056417494352, 79621152848256) (308898457681, 854461018656481, 3076340145947856) (316917278289, 866517436150833, 3155961298796112) (by decide) (by decide) (by decide) chunk1472 tail1536
  have tail1408 : moments 1408 2605 = (324902222929, 878012010468737, 3235532064724944) :=
    join 1408 64 2541 1472 2605 (7984944640, 11494574317904, 79570765928832) (316917278289, 866517436150833, 3155961298796112) (324902222929, 878012010468737, 3235532064724944) (by decide) (by decide) (by decide) chunk1408 tail1472
  have tail1344 : moments 1344 2669 = (332825504337, 888910901080785, 3314980476555600) :=
    join 1344 64 2605 1408 2669 (7923281408, 10898890612048, 79448411830656) (324902222929, 878012010468737, 3235532064724944) (332825504337, 888910901080785, 3314980476555600) (by decide) (by decide) (by decide) chunk1344 tail1408
  have tail1280 : moments 1280 2733 = (340650946641, 899174600952865, 3394185544084176) :=
    join 1280 64 2669 1344 2733 (7825442304, 10263699872080, 79205067528576) (332825504337, 888910901080785, 3314980476555600) (340650946641, 899174600952865, 3394185544084176) (by decide) (by decide) (by decide) chunk1280 tail1344
  have tail1216 : moments 1216 2797 = (348333985361, 908760084029809, 3472964369179728) :=
    join 1216 64 2733 1280 2797 (7683038720, 9585483076944, 78778825095552) (340650946641, 899174600952865, 3394185544084176) (348333985361, 908760084029809, 3472964369179728) (by decide) (by decide) (by decide) chunk1216 tail1280
  have tail1152 : moments 1152 2861 = (355821667409, 917622952719041, 3551059260882384) :=
    join 1152 64 2797 1216 2861 (7487682048, 8862868689232, 78094891702656) (348333985361, 908760084029809, 3472964369179728) (355821667409, 917622952719041, 3551059260882384) (by decide) (by decide) (by decide) chunk1152 tail1216
  have tail1088 : moments 1088 2925 = (363052651089, 925719585374225, 3628124850501456) :=
    join 1088 64 2861 1152 2925 (7230983680, 8096632655184, 77065589619072) (355821667409, 917622952719041, 3551059260882384) (363052651089, 925719585374225, 3628124850501456) (by decide) (by decide) (by decide) chunk1088 tail1152
  have tail1024 : moments 1024 2989 = (369957206097, 933009283778913, 3703715206713552) :=
    join 1024 64 2925 1088 2989 (6904555008, 7289698404688, 75590356212096) (363052651089, 925719585374225, 3628124850501456) (369957206097, 933009283778913, 3703715206713552) (by decide) (by decide) (by decide) chunk1024 tail1088
  have tail960 : moments 960 3053 = (376457213521, 939456420630193, 3777270950660688) :=
    join 960 64 2989 1024 3053 (6500007424, 6447136851280, 73555743947136) (369957206097, 933009283778913, 3703715206713552) (376457213521, 939456420630193, 3777270950660688) (by decide) (by decide) (by decide) chunk960 tail1024
  have tail896 : moments 896 3117 = (382466165841, 945032587022337, 3848106371048400) :=
    join 896 64 3053 960 3117 (6008952320, 5576166392144, 70835420387712) (376457213521, 939456420630193, 3777270950660688) (382466165841, 945032587022337, 3848106371048400) (by decide) (by decide) (by decide) chunk896 tail960
  have tail832 : moments 832 3181 = (387889166929, 949718739930449, 3915396539243856) :=
    join 832 64 3117 896 3181 (5423001088, 4686152908112, 67290168195456) (382466165841, 945032587022337, 3848106371048400) (387889166929, 949718739930449, 3915396539243856) (by decide) (by decide) (by decide) chunk832 tail896
  have tail768 : moments 768 3245 = (392624721697, 953508743745051, 3978165386340624) :=
    join 768 64 3181 832 3245 (4735554768, 3790003814602, 62768847096768) (387889166929, 949718739930449, 3915396539243856) (392624721697, 953508743745051, 3978165386340624) (by decide) (by decide) (by decide) chunk768 tail832
  have tail704 : moments 704 3309 = (396591807137, 956430760576347, 4035309501216912) :=
    join 704 64 3245 768 3309 (3967085440, 2922016831296, 57144114876288) (392624721697, 953508743745051, 3978165386340624) (396591807137, 956430760576347, 4035309501216912) (by decide) (by decide) (by decide) chunk704 tail768
  have tail640 : moments 640 3373 = (399763947041, 958565062636699, 4085734095792144) :=
    join 640 64 3309 704 3373 (3172139904, 2134302060352, 50424594575232) (396591807137, 956430760576347, 4035309501216912) (399763947041, 958565062636699, 4085734095792144) (by decide) (by decide) (by decide) chunk640 tail704
  have tail576 : moments 576 3437 = (402173385121, 960032677911515, 4128543393347472) :=
    join 576 64 3373 640 3437 (2409438080, 1467615274816, 42809297555328) (399763947041, 958565062636699, 4085734095792144) (402173385121, 960032677911515, 4128543393347472) (by decide) (by decide) (by decide) chunk576 tail640
  have tail512 : moments 512 3501 = (403910708271, 960980162337055, 4163233702132296) :=
    join 512 64 3437 576 3501 (1737323150, 947484425540, 34690308784824) (402173385121, 960032677911515, 4128543393347472) (403910708271, 960980162337055, 4163233702132296) (by decide) (by decide) (by decide) chunk512 tail576
  have tail448 : moments 448 3565 = (405106702911, 961556175715807, 4189858608241224) :=
    join 448 64 3501 512 3565 (1195994640, 576013378752, 26624906108928) (403910708271, 960980162337055, 4163233702132296) (405106702911, 961556175715807, 4189858608241224) (by decide) (by decide) (by decide) chunk448 tail512
  have tail384 : moments 384 3629 = (405887501391, 961882503139999, 4209030440778312) :=
    join 384 64 3565 448 3629 (780798480, 326327424192, 19171832537088) (405106702911, 961556175715807, 4189858608241224) (405887501391, 961882503139999, 4209030440778312) (by decide) (by decide) (by decide) chunk384 tail448
  have tail320 : moments 320 3693 = (406362548831, 962050849134431, 4221781863602760) :=
    join 320 64 3629 384 3693 (475047440, 168345994432, 12751422824448) (405887501391, 961882503139999, 4209030440778312) (406362548831, 962050849134431, 4221781863602760) (by decide) (by decide) (by decide) chunk320 tail384
  have tail256 : moments 256 3757 = (406624513135, 962127081311263, 4229411291675208) :=
    join 256 64 3693 320 3757 (261964304, 76232176832, 7629428072448) (406362548831, 962050849134431, 4221781863602760) (406624513135, 962127081311263, 4229411291675208) (by decide) (by decide) (by decide) chunk256 tail320
  have tail192 : moments 192 3821 = (406749284991, 962155525337311, 4233328272235080) :=
    join 192 64 3757 256 3821 (124771856, 28444026048, 3916980559872) (406624513135, 962127081311263, 4229411291675208) (406749284991, 962155525337311, 4233328272235080) (by decide) (by decide) (by decide) chunk192 tail256
  have tail128 : moments 128 3885 = (406795977871, 962163259901343, 4234898865977928) :=
    join 128 64 3821 192 3885 (46692880, 7734564032, 1570593742848) (406749284991, 962155525337311, 4233328272235080) (406795977871, 962163259901343, 4234898865977928) (by decide) (by decide) (by decide) chunk128 tail192
  have tail64 : moments 64 3949 = (406806928031, 962164411681375, 4235291028232776) :=
    join 64 64 3885 128 3949 (10950160, 1151780032, 392162254848) (406795977871, 962163259901343, 4234898865977928) (406806928031, 962164411681375, 4235291028232776) (by decide) (by decide) (by decide) chunk64 tail128
  have tail0 : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) :=
    join 0 64 3949 64 4013 (766480, 38630592, 28961906688) (406806928031, 962164411681375, 4235291028232776) (406807694511, 962164450311967, 4235319990139464) (by decide) (by decide) (by decide) chunk0 tail64
  exact tail0
theorem sourceCount_eq : sourceCount = 406807694511 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj e
  rw [sourceCount]; exact h.1
theorem sourceDegree_eq : sourceDegree = 962164450311967 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj (Prod.mk.inj e).2
  rw [sourceDegree]; exact h.1
theorem sourceIndex24_eq : sourceIndex24 = 11874264712496136 := by
  have hp := congrArg (fun x : Moments => x.2.2) ((moments_eq 4013).symm.trans checked)
  change (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = 4235319990139464 at hp
  unfold sourceIndex24
  simp only [indexMoment, sum_sub_distrib, ← mul_sum]
  change (24 * 1650) * sourceCount - (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = _
  rw [sourceCount_eq, hp]
  decide
def compactCount (A D : ℕ) : ℕ :=
  3000*A*406807694511 + 494761029687339 - D*962164450311967
theorem exact_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A) :
    (columns A D hD).card = compactCount A D := by
  have h := scaled_columns A D hA hD hBudget
  rw [sourceCount_eq, sourceDegree_eq, sourceIndex24_eq] at h
  unfold compactCount
  push_cast at h
  omega
#print axioms exact_columns
end TaperColumns

end Merged_PrimaryTaperColumnData

-- merged module PrimaryTaperFamily
section Merged_PrimaryTaperFamily

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace PrimaryTaper

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial (mem_support_iff monomial)
open TaperColumns
open TaperBudget (cap)
open scoped BigOperators

open P0_9_2 (weight_eq_sum map_independent_family pointContact high_monomial_vanishes)
open TaperColumns (sumCount sumIndex sumDifferentiated sumGrade sumOld)

def primaryBox : Shape := ⟨4012, 1650, 550⟩

def TrueWeightLE {n : ℕ} (D : ℕ) (P : Row n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ T

def JetsBounded (P : Row 4) : Prop := ∀ m ∈ P.support, m ∈ jetExponents

theorem row_bounds {A D : ℕ} (Q : Source A D) :
    InBox (shape (toRow Q.1)) primaryBox ∧
    TrueWeightLE D (toRow Q.1) (3000*A-1) ∧ JetsBounded (toRow Q.1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ 3000*A-1 ∧
      m ∈ jetExponents := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, Eligible A D e := Q.2
    obtain ⟨⟨hb, hj, ht, hcap⟩, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have hmem : m ∈ jetExponents := by
      change m.weight K1_13_2_2.gradeWeight ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧
        m 1+m 2+m 3 ≤ cap (m.weight K1_13_2_2.gradeWeight)
      rw [sumGrade, sumOld]
      rw [sumCount] at hb
      rw [sumIndex] at hj
      rw [sumDifferentiated, sumCount] at hcap
      simpa only [Finsupp.optionElim_apply_some] using And.intro hb (And.intro hj hcap)
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) D =
        (fun v => v.elim 1 (fun i => D - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => D - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw, hmem⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2.1
  · exact fun m hm => (h m hm).2.2.2.2

def nodeMap {A D : ℕ} (x y : Geom) : Source A D →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict (Source A D)

def wordMap (A D : ℕ) (w : I → K) : Source A D →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))

theorem contact_of_word_kernel {A D : ℕ} (w : I → K) (Q : Source A D) (hQ : wordMap A D w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd

theorem local_range_finite (x y : Geom) :
    Module.Finite Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
      (TaperNormalize.space cap))) := by
  have hsub :
      LinearMap.range ((localConstraintAt 3000 x y).domRestrict (TaperNormalize.space cap)) ≤
        LinearMap.range (K1_13_2.nodeMap 0 0) := by
    rintro _ ⟨Q, rfl⟩
    let R := globalPointTranslation x y Q.1
    have hR : R ∈ TaperNormalize.space cap := TaperNormalize.translate TaperBudget.cap_antitone x y Q
    change localConstraintAt 3000 x y Q.1 ∈ _
    rw [localConstraintAt_eq_zero_globalPointTranslation]
    change localConstraintAt 3000 0 0 R ∈ _
    rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    by_cases hx : e none < 3000
    · obtain ⟨hg, hj, ht, _⟩ := hR he
      have hw := weight_le_add_mul_totalJetDegree 133671 e
      change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
      have hOld : K1_13_2.SourceEligible e := ⟨hg,hj,ht,by omega⟩
      have hMono : monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
        (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
      exact ⟨⟨_, hMono⟩, rfl⟩
    · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
      exact Submodule.zero_mem _
  exact Module.Finite.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)









theorem symbol_rank {n : ℕ} (x : Geom) (e : Fin n → Row 4)
    (he : ∀ i, JetsBounded (e i))
    (hli : LinearIndependent Geom (fun i => K1_13_3.symbolAt x (e i))) :
    n ≤ 406807694511 := by
  let V := MvPolynomial.restrictSupport Geom jetExponents
  let v : Fin n → V := fun i =>
    ⟨K1_13_3.symbolAt x (e i), fun m hm => he i m (MvPolynomial.support_map_subset _ _ hm)⟩
  letI : Module.Finite Geom V := MvPolynomial.restrictSupport_finite jetExponents_finite
  have hv : LinearIndependent Geom v := LinearIndependent.of_comp V.subtype hli
  have hd : Module.finrank Geom V = jetColumns.card := by
    change Module.finrank Geom (MvPolynomial.restrictSupport Geom jetExponents) = _
    rw [← jetExponents_finite.coe_toFinset]
    exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) jetColumns
  have hn : jetColumns.card = 406807694511 := by
    exact_mod_cast jet_card_eq.trans sourceCount_eq
  simpa only [Fintype.card_fin, hd, hn] using hv.fintype_card_le_finrank

#print axioms symbol_rank
end
end PrimaryTaper

end Merged_PrimaryTaperFamily

-- merged module Wide50EulerPrimaryFamily
section Merged_Wide50EulerPrimaryFamily

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace Wide50EulerPrimary

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open PrimaryTaper (nodeMap wordMap row_bounds primaryBox TrueWeightLE JetsBounded contact_of_word_kernel)
open TaperColumns
open KoalaTaperTransfer
open scoped BigOperators
open PrimaryTaper (local_range_finite)
open P0_9_2 (map_independent_family)

private theorem rank_at_position {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ KoalaTaperTransfer.localRank := by
  letI := local_range_finite x y
  apply (Submodule.finrank_mono ?_).trans (KoalaTaperTransfer.node_rank x y)
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

theorem word_rank (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * KoalaTaperTransfer.localRank := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, KoalaTaperTransfer.localRank := Finset.sum_le_sum fun i _ => rank_at_position _ _
    _ = _ := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

def sourceRank (A D : ℕ) : ℕ := compactCount A D - 262144 * KoalaTaperTransfer.localRank

def layerNeed (A D : ℕ) : ℕ := sourceRank A D / (A-D+3) + 1

theorem primary_family (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := (finrank_source A D hD).trans (exact_columns A D hA hD hBudget)
  have hr := word_rank A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩




#print axioms primary_family
end
end Wide50EulerPrimary

end Merged_Wide50EulerPrimaryFamily
