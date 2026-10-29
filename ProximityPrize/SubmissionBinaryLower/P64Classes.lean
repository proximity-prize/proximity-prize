import ProximityPrize.SubmissionBinaryLower.P64S3
import ProximityPrize.SubmissionBinaryLower.P64Final

/-!
# Classes 0 to 5 and the reduction of `ClassBounds` to the high-degree interface

`classBounds_of_high` proves `P64Final.ClassBounds K1 K2 K3` from `HighInterface K1 K2 K3` (and
`2 ≤ K2`). Per factor `R` of the interpolant, with `Vs` its single-factor slopes:

| `h` | argument | row |
|---|---|---|
| 0 | `(S_R) = ∅` | 0 |
| 1 | every line is full, Lemma AF | `208984·d + 117013736431` |
| 2 | Theorem Q2(a) and Theorem D, or Lemma AF | same |
| 3 | `S_1`-good (Lemma S_t) or Corollary S3 | class 3 or 4 |
| ≥ 4 | `S_t`-good, Lemma AF, 4.10.2 (`∂_Y R = 0 ≠ ∂_X R`), else `HighInterface` | class 3, 5, `2hd`, surface |

Class 1 uses Lemma AF in place of Proposition L (PROOF.md 4.3): for `h = 1` every line on `R`
is full, and Lemma AF's bound fits the class-1 row of `factorBound`.

`HighInterface` is what remains: classes 6 and 7 (PROOF.md 4.8, 4.9) for factors of `Y`-degree at
least four that are not `S_t`-good for any `t ≤ 4`, have fewer than 208984 full lines and at least
208984 lines, and are not of the 4.10.2 kind (so they are separable or Frobenius twists).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Classes

open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open BCHKSSubstitutionVanish P64LineOrder P64Cofactor P64Light P64Aux P64S3
  P64Charging P64Ledger P64Interp P64Incidence

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yzd" => P64Caps.YZ.yzSupportDegree
local notation "dom" => BinaryIRSProfile.domain

/-- **The remaining assumption**: classes 6 and 7 (with the Frobenius twists of 4.10.3). -/
def HighInterface (K1 K2 K3 : ℚ) : Prop :=
  ∀ (u₀ u₁ : Idx → Fld) (R : Tri) (Vs : Finset Fld) (P : Fld → Fld[X])
    (Az : Fld → Finset Idx),
    Irreducible R → 4 ≤ R.natDegree → ¬ (derivative R = 0 ∧ dXPoly R ≠ 0) →
    wd R 1048575 ≤ 249292 * 1482911 - 1 → yzd R 1 ≤ 58589180685 →
    (∀ t q, ¬ StGood dom u₀ u₁ R t q) →
    (full dom u₀ u₁ R).card < 208984 → 208984 ≤ (lam dom (lineOf u₀ u₁) R).card →
    BadData dom u₀ u₁ R Vs P Az →
    (∀ z ∈ Vs, Dangerous dom (lineOf u₀ u₁) 1048575 1482911 R (Az z)) →
    (Vs.card : ℚ) ≤ K1 * 2097152 * yzd R 1 + K2 * R.natDegree * yzd R 1 +
      K3 * 2097152 * (yzd R 1 + R.natDegree)

section Rows

variable {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
include hK1 hK2 hK3

lemma factorBound_ge (h d w : ℕ) :
    cAlpha * d + cBeta * h + K2 * (h * d) ≤ factorBound K1 K2 K3 h d w := by
  unfold factorBound
  have t1 : 0 ≤ (K1 + K3) * 2097152 * (d : ℚ) := by positivity
  have t2 : 0 ≤ K3 * 2097152 * (h : ℚ) := by positivity
  have t3 : 0 ≤ (4 / 1048575 : ℚ) * (w * d) := by positivity
  nlinarith

/-- Lemma AF's bound is below the charge of any factor with `h ≥ 1`. -/
lemma af_le {h d w c : ℕ} (hh : 1 ≤ h) (hc : c ≤ 208984 * d + 117013736431) :
    (c : ℚ) ≤ factorBound K1 K2 K3 h d w := by
  have h1 := factorBound_ge hK1 hK2 hK3 h d w
  have hc' : (c : ℚ) ≤ 208984 * d + 117013736431 := by exact_mod_cast hc
  have hh' : (1 : ℚ) ≤ h := by exact_mod_cast hh
  have t4 : 0 ≤ K2 * ((h : ℚ) * d) := by positivity
  have hd : (0 : ℚ) ≤ d := by positivity
  simp only [cAlpha, cBeta] at h1
  nlinarith

lemma stGood_le {h d w J c : ℕ} (hc : c ≤ h * (4 * 58589180686 - 1) + J * d)
    (hJ : J * 1048575 ≤ 4 * w) : (c : ℚ) ≤ factorBound K1 K2 K3 h d w := by
  have hc2 : c ≤ h * 234356722743 + J * d := by omega
  have hc' : (c : ℚ) ≤ h * (4 * 58589180686 - 1) + J * d := by
    have : (c : ℚ) ≤ h * 234356722743 + J * d := by exact_mod_cast hc2
    linarith
  have hJ' : (J : ℚ) * 1048575 ≤ 4 * w := by exact_mod_cast hJ
  have hd : (0 : ℚ) ≤ d := by positivity
  have hJd : (J : ℚ) * d ≤ (4 / 1048575) * (w * d) := by
    have := mul_le_mul_of_nonneg_right hJ' hd
    nlinarith
  have := row3_le hK1 hK2 hK3 h d w
  linarith

lemma insep_le (hK2' : 2 ≤ K2) {h d w c : ℕ} (hc : c ≤ 2 * h * d) :
    (c : ℚ) ≤ factorBound K1 K2 K3 h d w := by
  have h1 := factorBound_ge hK1 hK2 hK3 h d w
  have hc' : (c : ℚ) ≤ 2 * h * d := by exact_mod_cast hc
  have hhd : (0 : ℚ) ≤ h * d := by positivity
  have t1 : 0 ≤ cAlpha * (d : ℚ) := mul_nonneg (by norm_num [cAlpha]) (Nat.cast_nonneg _)
  have t2 : 0 ≤ cBeta * (h : ℚ) := mul_nonneg (by norm_num [cBeta]) (Nat.cast_nonneg _)
  nlinarith

end Rows

/-- The data of one factor `R` of the interpolant, with full agreement sets. -/
theorem badData_caseSingle (U : Fin 2 → Idx → Fld) (Q R : Tri) (S : Finset Fld)
    (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hdata : ∀ z ∈ S, (P z).natDegree ≤ 1048575 ∧ 1482911 ≤ (Az z).card ∧
      (∀ i ∈ Az z, (P z).eval (dom i) = U 0 i + z * U 1 i) ∧ P64Final.BadOn U (Az z)) :
    BadData dom (U 0) (U 1) R (caseSingle Q S P R) P
      (fun z => Finset.univ.filter fun i => (P z).eval (dom i) = U 0 i + z * U 1 i) := by
  classical
  have hmem : ∀ z ∈ caseSingle Q S P R, z ∈ S ∧ triEval R z (P z) = 0 := by
    intro z hz
    simp only [caseSingle, Finset.mem_filter] at hz
    exact ⟨hz.1, hz.2.2.1⟩
  have hsub : ∀ z ∈ S, Az z ⊆ Finset.univ.filter fun i => (P z).eval (dom i) = U 0 i + z * U 1 i :=
    fun z hz i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hdata z hz).2.2.1 i hi
  refine ⟨fun z hz => (hmem z hz).2, fun z hz => (hdata z (hmem z hz).1).1, ?_, ?_, ?_⟩
  · intro z hz
    exact (hdata z (hmem z hz).1).2.1.trans (Finset.card_le_card (hsub z (hmem z hz).1))
  · intro z hz i
    simp
  · rintro z hz ⟨p₀, p₁, h₀, h₁, hag⟩
    exact (hdata z (hmem z hz).1).2.2.2 ⟨p₀, p₁, h₀, h₁, fun i hi => hag i (hsub z (hmem z hz).1 hi)⟩

/-- A factor's degrees are below the interpolant's. -/
theorem factor_caps (Q R : Tri) (hQ : GSCaps Q) (hR : R ∈ factors Q) :
    wd R 1048575 ≤ 249292 * 1482911 - 1 ∧ yzd R 1 ≤ 58589180685 := by
  classical
  obtain ⟨c, hc⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (α := Tri)
    (Multiset.mem_toFinset.mp hR)
  have hR0 : R ≠ 0 := by rintro rfl; exact hQ.ne_zero (by rw [hc, zero_mul])
  have hc0 : c ≠ 0 := by rintro rfl; exact hQ.ne_zero (by rw [hc, mul_zero])
  have hw := P64Caps.Weighted.weightedSupportDegree_mul R c 1048575 hR0 hc0
  have hy := P64Caps.YZ.yzSupportDegree_mul R c 1 hR0 hc0
  rw [← hc] at hw hy
  have := hQ.weighted_lt
  have := hQ.yz_le
  omega

lemma card_field : Fintype.card Fld = 2 ^ 192 := BF64.card_ext3

/-- **Per-factor bound.** -/
theorem card_caseSingle_le {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hK2' : 2 ≤ K2) (hhigh : HighInterface K1 K2 K3)
    (U : Fin 2 → Idx → Fld) (Q : Tri) (S : Finset Fld) (P : Fld → Fld[X])
    (Az : Fld → Finset Idx) (hQ : GSCaps Q)
    (hGS : ∀ i, OrdGE Q (dom i)
      ((Polynomial.C (U 0 i) : Polynomial Fld) + Polynomial.X * Polynomial.C (U 1 i)) 249292)
    (hdata : ∀ z ∈ S, (P z).natDegree ≤ 1048575 ∧ 1482911 ≤ (Az z).card ∧
      (∀ i ∈ Az z, (P z).eval (dom i) = U 0 i + z * U 1 i) ∧ P64Final.BadOn U (Az z))
    (R : Tri) (hR : R ∈ factors Q) :
    ((caseSingle Q S P R).card : ℚ) ≤
      factorBound K1 K2 K3 R.natDegree (yzd R 1) (wd R 1048575) := by
  classical
  set Az' : Fld → Finset Idx :=
    fun z => Finset.univ.filter fun i => (P z).eval (dom i) = U 0 i + z * U 1 i with hAz'
  have hbd := badData_caseSingle U Q R S P Az hdata
  rw [← hAz'] at hbd
  have hirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R
      (Multiset.mem_toFinset.mp hR)).irreducible
  obtain ⟨hwR, hyR⟩ := factor_caps Q R hQ hR
  have hdang : 2 ≤ R.natDegree → ∀ z ∈ caseSingle Q S P R,
      Dangerous dom (lineOf (U 0) (U 1)) 1048575 1482911 R (Az' z) := fun h2 =>
    caseSingle_dangerous dom (lineOf (U 0) (U 1)) 249292 1048575 1482911 Q hQ.ne_zero S P Az'
      (by norm_num) hGS hQ.weighted_lt (fun z hz => (hdata z hz).1)
      (fun z hz => ((hdata z hz).2.1).trans (Finset.card_le_card fun i hi => by
        simp only [hAz', Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hdata z hz).2.2.1 i hi))
      (fun z hz i hi => by
        simp only [hAz', Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [hi, eval_lineOf])
      R hR h2
  have hhw : 1048575 * R.natDegree ≤ wd R 1048575 :=
    natDegree_mul_le_weightedSupportDegree R hirr.ne_zero _
  have hF : 2 ^ 128 ≤ Fintype.card Fld := by rw [card_field]; norm_num
  have hlamfull : ∀ i, i ∈ lam dom (lineOf (U 0) (U 1)) R → R.natDegree = 1 →
      i ∈ full dom (U 0) (U 1) R := by
    intro i hi h1
    simp only [lam, full, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have := lineOrd_le_natDegree_of_irreducible hirr (by omega) (dom i) (lineOf (U 0) (U 1) i)
    omega
  have hAF : 1 ≤ R.natDegree → (208984 ≤ (full dom (U 0) (U 1) R).card ∨
      (lam dom (lineOf (U 0) (U 1)) R).card ≤ 208983) →
      ((caseSingle Q S P R).card : ℚ) ≤
        factorBound K1 K2 K3 R.natDegree (yzd R 1) (wd R 1048575) := fun h1 hl =>
    af_le hK1 hK2 hK3 h1 (card_le_of_afLight dom (by simp) (U 0) (U 1) hirr h1 hbd hl)
  have hSt : ∀ t q, StGood dom (U 0) (U 1) R t q → 2 ≤ R.natDegree →
      ((caseSingle Q S P R).card : ℚ) ≤
        factorBound K1 K2 K3 R.natDegree (yzd R 1) (wd R 1048575) := by
    intro t q hg h2
    have hc := card_le_of_stGood dom (U 0) (U 1) hirr (by omega) hbd (hdang h2) hwR hF hg
    refine stGood_le hK1 hK2 hK3 hc ?_
    have h1 := Nat.div_mul_le_self (t * wd R 1048575 - 1482911) 1048575
    have h2 : t * wd R 1048575 ≤ 4 * wd R 1048575 := Nat.mul_le_mul_right _ hg.2.1
    omega
  obtain h0 | h1 | h2 | h3 | h4 : R.natDegree = 0 ∨ R.natDegree = 1 ∨ R.natDegree = 2 ∨
      R.natDegree = 3 ∨ 4 ≤ R.natDegree := by omega
  · rw [caseSingle_eq_empty_of_natDegree_eq_zero Q S P R hR h0, Finset.card_empty,
      Nat.cast_zero]
    have := factorBound_ge hK1 hK2 hK3 R.natDegree (yzd R 1) (wd R 1048575)
    have t1 : 0 ≤ cAlpha * ((yzd R 1 : ℕ) : ℚ) :=
      mul_nonneg (by norm_num [cAlpha]) (Nat.cast_nonneg _)
    have t2 : 0 ≤ cBeta * ((R.natDegree : ℕ) : ℚ) :=
      mul_nonneg (by norm_num [cBeta]) (Nat.cast_nonneg _)
    have t3 : 0 ≤ K2 * (((R.natDegree : ℕ) : ℚ) * ((yzd R 1 : ℕ) : ℚ)) :=
      mul_nonneg hK2 (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    linarith
  · apply hAF (by omega)
    by_cases hl : (lam dom (lineOf (U 0) (U 1)) R).card ≤ 208983
    · exact Or.inr hl
    · left
      have : lam dom (lineOf (U 0) (U 1)) R ⊆ full dom (U 0) (U 1) R :=
        fun i hi => hlamfull i hi h1
      have := Finset.card_le_card this
      omega
  · by_cases hfew : (full dom (U 0) (U 1) R).card < 208984
    · have hempty : caseSingle Q S P R = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact not_dangerous_of_quadric dom (U 0) (U 1) hirr h2 hfew (Az' z)
          (hdang (by omega) z hz)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      have := factorBound_ge hK1 hK2 hK3 R.natDegree (yzd R 1) (wd R 1048575)
      have t1 : 0 ≤ cAlpha * ((yzd R 1 : ℕ) : ℚ) :=
        mul_nonneg (by norm_num [cAlpha]) (Nat.cast_nonneg _)
      have t2 : 0 ≤ cBeta * ((R.natDegree : ℕ) : ℚ) :=
        mul_nonneg (by norm_num [cBeta]) (Nat.cast_nonneg _)
      have t3 : 0 ≤ K2 * (((R.natDegree : ℕ) : ℚ) * ((yzd R 1 : ℕ) : ℚ)) :=
        mul_nonneg hK2 (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      linarith
    · exact hAF (by omega) (Or.inl (by omega))
  · rcases stGood_or_full dom (U 0) (U 1) hirr h3 hwR with ⟨q, hg⟩ | hfull
    · exact hSt 1 q hg (by omega)
    · have hc := card_le_of_cubic dom (U 0) (U 1) hirr h3 hbd hfull
      have := row4_le hK1 hK2 hK3 (yzd R 1) (wd R 1048575)
      rw [h3]
      have hc' : ((caseSingle Q S P R).card : ℚ) ≤ 89952 * (yzd R 1 : ℚ) + 2172022111004 := by
        exact_mod_cast hc
      push_cast at this
      linarith
  · by_cases hg : ∃ t q, StGood dom (U 0) (U 1) R t q
    · obtain ⟨t, q, hg⟩ := hg
      exact hSt t q hg (by omega)
    push Not at hg
    by_cases hl : 208984 ≤ (full dom (U 0) (U 1) R).card ∨
        (lam dom (lineOf (U 0) (U 1)) R).card ≤ 208983
    · exact hAF (by omega) hl
    push Not at hl
    by_cases hins : derivative R = 0 ∧ dXPoly R ≠ 0
    · have hXcap : ∀ j, (R.coeff j).natDegree ≤ wd R 1048575 :=
        P64Resultant.coeff_natDegree_le_weighted R 1048575
      have hF' : 2 * R.natDegree * wd R 1048575 < Fintype.card Fld := by
        rw [card_field]
        have hh : 2 * R.natDegree ≤ 2 ^ 20 := by omega
        have hw' : wd R 1048575 ≤ 2 ^ 40 := by omega
        calc _ ≤ 2 ^ 20 * 2 ^ 40 := Nat.mul_le_mul hh hw'
          _ < 2 ^ 192 := by norm_num
      have hc := card_le_of_inseparable R hirr (by omega) hins.1 hins.2 _ hXcap hF'
        (caseSingle Q S P R) P hbd.on_curve
      exact insep_le hK1 hK2 hK3 hK2' hc
    · have hc := hhigh (U 0) (U 1) R (caseSingle Q S P R) P Az' hirr h4 hins hwR hyR hg hl.1
        hl.2 hbd (hdang (by omega))
      exact hc.trans (rowSurf_le hK1 hK2 hK3 _ _ _)

/-- **ClassBounds from the high-degree interface.** -/
theorem classBounds_of_high {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hK2' : 2 ≤ K2) (hhigh : HighInterface K1 K2 K3) : P64Final.ClassBounds K1 K2 K3 :=
  fun U Q S P Az hQ hGS hdata R hR =>
    card_caseSingle_le hK1 hK2 hK3 hK2' hhigh U Q S P Az hQ hGS hdata R hR

end P64Classes
end ProximityPrize.SubmissionBinaryLower

namespace ProximityPrize.Benchmark.Binary

open ProximityPrize.SubmissionBinaryLower

/-- The 64.00 claim, conditional only on classes 6 and 7. -/
theorem protocolClaim6400_of_high {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 2 ≤ K2)
    (hK3 : 0 ≤ K3)
    (hK : K1 * 2097152 * 58589180685 + K2 * 352552 * 58589180685 +
      K3 * 2097152 * (58589180685 + 352552) ≤ 17864703000000000000)
    (hhigh : P64Classes.HighInterface K1 K2 K3) :
    ProtocolClaim 6400 78622925 268435456 :=
  protocolClaim6400_of_classBounds hK1 (by linarith) hK3 hK
    (P64Classes.classBounds_of_high hK1 (by linarith) hK3 hK2 hhigh)

end ProximityPrize.Benchmark.Binary
