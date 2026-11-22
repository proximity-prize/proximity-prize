import ProximityPrize.SubmissionLower.PrimaryTaperMoments

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

private theorem sumCount (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]

private theorem sumIndex (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]

private theorem sumDifferentiated (e : SourceExponent) :
    e.weight TaperNormalize.differentiated = e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, TaperNormalize.differentiated]

private theorem sumTop (e : SourceExponent) : e.weight topWeight = e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight,
    Pi.single_apply, smul_eq_mul]

private theorem sumOld (m : JetExp) : m.weight oldWeight = m 1 + 2*m 2 + 3*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, oldWeight, smul_eq_mul, Nat.mul_comm]

private theorem sumGrade (m : JetExp) : m.weight gradeWeight = m 0 + m 1 + m 2 + m 3 := by
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
