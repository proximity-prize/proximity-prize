import ProximityPrize.SubmissionBinaryLower.P64SurfInterface

/-!
# The ledger (PROOF.md 6)

Every row of PROOF.md 6 that is charged per factor is written as a linear form in
`d, h, w·d, h·d` of the factor (`d = yzSupportDegree R 1`, `h = deg_Y R`,
`w = weightedSupportDegree R D`). A per-factor constant `c` of a class with fixed `Y`-degree `h₀`
becomes `(c / h₀)·h`. `factorBound` is the sum of all rows, so each class bound is below it and
each row gets the whole budget `Σ h ≤ J - 1`, `Σ d ≤ DZ - 1`, `Σ w ≤ mA - 1` (formal-plan.md
section 5, item 3: fixed and heavy are not used).

The class lemmas (Proposition L, Theorem Q2, Lemma S_t, Corollary S3, Lemma 2.1 / Lemma AF and the
surface interface) are to be discharged by showing `|(S_R)| ≤` their row, then
`row ≤ factorBound` by the `row*_le` lemmas below. The pair case `(P)` needs Lemma R and enters
as a hypothesis. The `(Y0)` case is proved here.

Side condition for the surface constants:
`K1·n·(DZ-1) + K2·(J-1)(DZ-1) + K3·n·(DZ-1 + J-1) ≤ 17864703000000000000`.
The class rows other than the interface total below `582040819351262325` (computed), against
`2^64 - 235031 - 17864703000000000000 = 582041073709316585` available.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Ledger

open Polynomial BCHKSSubstitutionVanish P64Charging

/-- Sum of the `d`-coefficients of the non-interface rows: classes 1, 2, 4, 5. -/
def cAlpha : ℚ := (1048575 + 5) + 208984 + 89952 + 352552

/-- Sum of the `h`-coefficients of the non-interface rows: classes 1, 2, 3, 4, 5. -/
def cBeta : ℚ :=
  2097152 + 117013736431 / 2 + (4 * 58589180686 - 1) + 2172022111004 / 3 + 58589180685

/-- The per-factor charge: all rows of PROOF.md 6 in linear form. -/
def factorBound (K1 K2 K3 : ℚ) (h d w : ℕ) : ℚ :=
  (cAlpha + (K1 + K3) * 2097152) * d + (cBeta + K3 * 2097152) * h +
    (4 / 1048575) * (w * d) + K2 * (h * d)

section Rows

variable {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
include hK1 hK2 hK3

private lemma terms_nonneg (h d w : ℕ) :
    0 ≤ (K1 + K3) * 2097152 * (d : ℚ) ∧ 0 ≤ K3 * 2097152 * (h : ℚ) ∧
      0 ≤ (4 / 1048575 : ℚ) * (w * d) ∧ 0 ≤ K2 * ((h : ℚ) * d) ∧ 0 ≤ (d : ℚ) ∧ 0 ≤ (h : ℚ) :=
  ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩

/-- Class 1 (Y-linear, Proposition L): `(D + 5)·d + n`. -/
lemma row1_le (d w : ℕ) :
    ((1048575 + 5) * d + 2097152 : ℚ) ≤ factorBound K1 K2 K3 1 d w := by
  obtain ⟨t1, t2, t3, t4, t5, _⟩ := terms_nonneg hK1 hK2 hK3 1 d w
  simp only [factorBound, cAlpha, cBeta, Nat.cast_one] at *
  nlinarith

/-- Class 2 (quadrics, Theorem Q2 and A2): `208984·d + 117013736431`. -/
lemma row2_le (d w : ℕ) :
    (208984 * d + 117013736431 : ℚ) ≤ factorBound K1 K2 K3 2 d w := by
  obtain ⟨t1, t2, t3, t4, t5, _⟩ := terms_nonneg hK1 hK2 hK3 2 d w
  simp only [factorBound, cAlpha, cBeta, Nat.cast_ofNat] at *
  nlinarith

/-- Class 3 (S_t-good, Lemma S_t): `h(4·DZ - 1) + (4w/D)·d`, which dominates
`h(4·DZ - 1) + ⌊(4w - A)/D⌋·d`. -/
lemma row3_le (h d w : ℕ) :
    ((4 * 58589180686 - 1) * h + (4 / 1048575) * (w * d) : ℚ) ≤ factorBound K1 K2 K3 h d w := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := terms_nonneg hK1 hK2 hK3 h d w
  simp only [factorBound, cAlpha, cBeta] at *
  nlinarith

/-- Class 4 (residual cubics, Corollary S3 and A2): `89952·d + 2172022111004`. -/
lemma row4_le (d w : ℕ) :
    (89952 * d + 2172022111004 : ℚ) ≤ factorBound K1 K2 K3 3 d w := by
  obtain ⟨t1, t2, t3, t4, t5, _⟩ := terms_nonneg hK1 hK2 hK3 3 d w
  simp only [factorBound, cAlpha, cBeta, Nat.cast_ofNat] at *
  nlinarith

/-- Class 5 (caps, Lemma 2.1 and Lemma AF): `cap_R = h(DZ - 1) + (J - 1)·d`. -/
lemma row5_le (h d w : ℕ) :
    (58589180685 * h + 352552 * d : ℚ) ≤ factorBound K1 K2 K3 h d w := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := terms_nonneg hK1 hK2 hK3 h d w
  simp only [factorBound, cAlpha, cBeta] at *
  nlinarith

/-- Classes 6 and 7 (the surface interface): `K1·n·d + K2·h·d + K3·n·(d + h)`. -/
lemma rowSurf_le (h d w : ℕ) :
    (K1 * 2097152 * d + K2 * h * d + K3 * 2097152 * (d + h) : ℚ) ≤
      factorBound K1 K2 K3 h d w := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := terms_nonneg hK1 hK2 hK3 h d w
  simp only [factorBound, cAlpha, cBeta] at *
  nlinarith

end Rows

variable {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

omit [NormalizationMonoid F] in
/-- Lemma 3.1, case `(Y0)`: the slopes `z` with `Q(X, Y, z) = 0` are roots of one nonzero
coefficient of `Q` in `F[Z]`, so there are at most `d_Q ≤ DZ - 1` of them. -/
theorem card_caseY0_le (Q : Tri) (hQ : Q ≠ 0) (S : Finset F) :
    (caseY0 Q S).card ≤ P64Caps.YZ.yzSupportDegree Q 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, Q.coeff j ≠ 0 := ⟨Q.natDegree, by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ⟩
  obtain ⟨a, ha⟩ : ∃ a, (Q.coeff j).coeff a ≠ 0 := ⟨(Q.coeff j).natDegree, by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hj⟩
  set c := (Q.coeff j).coeff a
  have hsub : caseY0 Q S ⊆ c.roots.toFinset := by
    intro z hz
    simp only [caseY0, Finset.mem_filter] at hz
    have h0 := congrArg (fun G => (G.coeff j).coeff a) hz.2
    simp only [specializeZ, coeff_map, coeff_zero] at h0
    rw [Multiset.mem_toFinset, mem_roots ha]
    simpa [c] using h0
  calc (caseY0 Q S).card ≤ c.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := card_roots' c
    _ ≤ Polynomial.Bivariate.degreeX (Q.coeff j) :=
        Polynomial.Bivariate.coeff_natDegree_le_degreeX _ a
    _ ≤ P64Caps.YZ.yzSupportDegree Q 1 := by
        have := P64Caps.YZ.coeffWeight_le_of_ne Q 1 j hj
        omega

/-- The per-factor charges summed over the factors of `Q`, with the budgets (2.4). -/
theorem sum_factorBound_le {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (Q : Tri) (hQ : Q ≠ 0) (Hb Db Wb : ℕ) (hh : Q.natDegree ≤ Hb)
    (hd : P64Caps.YZ.yzSupportDegree Q 1 ≤ Db)
    (hw : P64Caps.Weighted.weightedSupportDegree Q 1048575 ≤ Wb) :
    ∑ R ∈ factors Q, factorBound K1 K2 K3 R.natDegree (P64Caps.YZ.yzSupportDegree R 1)
        (P64Caps.Weighted.weightedSupportDegree R 1048575) ≤
      factorBound K1 K2 K3 Hb Db Wb := by
  classical
  set s := factors Q
  set hR : Tri → ℕ := fun R => R.natDegree
  set dR : Tri → ℕ := fun R => P64Caps.YZ.yzSupportDegree R 1
  set wR : Tri → ℕ := fun R => P64Caps.Weighted.weightedSupportDegree R 1048575
  have sh : ∑ R ∈ s, hR R ≤ Hb := (sum_natDegree_le Q hQ).trans hh
  have sd : ∑ R ∈ s, dR R ≤ Db := (sum_yz_le Q hQ 1).trans hd
  have sw : ∑ R ∈ s, wR R ≤ Wb := (sum_weighted_le Q hQ 1048575).trans hw
  have swd : ∑ R ∈ s, wR R * dR R ≤ Wb * Db :=
    (sum_mul_le_mul_sum s wR dR).trans (Nat.mul_le_mul sw sd)
  have shd : ∑ R ∈ s, hR R * dR R ≤ Hb * Db :=
    (sum_mul_le_mul_sum s hR dR).trans (Nat.mul_le_mul sh sd)
  have shQ : (∑ R ∈ s, (hR R : ℚ)) ≤ Hb := by exact_mod_cast sh
  have sdQ : (∑ R ∈ s, (dR R : ℚ)) ≤ Db := by exact_mod_cast sd
  have swdQ : (∑ R ∈ s, (wR R : ℚ) * dR R) ≤ (Wb : ℚ) * Db := by exact_mod_cast swd
  have shdQ : (∑ R ∈ s, (hR R : ℚ) * dR R) ≤ (Hb : ℚ) * Db := by exact_mod_cast shd
  have hexp : ∑ R ∈ s, factorBound K1 K2 K3 (hR R) (dR R) (wR R) =
      (cAlpha + (K1 + K3) * 2097152) * ∑ R ∈ s, (dR R : ℚ) +
        (cBeta + K3 * 2097152) * ∑ R ∈ s, (hR R : ℚ) +
        (4 / 1048575) * ∑ R ∈ s, (wR R : ℚ) * dR R + K2 * ∑ R ∈ s, (hR R : ℚ) * dR R := by
    simp only [factorBound, Finset.sum_add_distrib, Finset.mul_sum]
  change ∑ R ∈ s, factorBound K1 K2 K3 (hR R) (dR R) (wR R) ≤ _
  rw [hexp]
  have hA : 0 ≤ cAlpha + (K1 + K3) * 2097152 := by unfold cAlpha; positivity
  have hB : 0 ≤ cBeta + K3 * 2097152 := by unfold cBeta; positivity
  unfold factorBound
  gcongr

/-- **Ledger.** For a nonzero interpolant `Q` within the degree caps of Lemma E, bad slopes `S`
with witnesses `P` on `Q` (Lemma GS), the pair bound of Lemma 3.1 and the per-factor class
bounds, `|S| ≤ 2^64 - 235031`. -/
theorem card_bad_le {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hK : K1 * 2097152 * 58589180685 + K2 * 352552 * 58589180685 +
      K3 * 2097152 * (58589180685 + 352552) ≤ 17864703000000000000)
    (Q : Tri) (hQ : Q ≠ 0) (hh : Q.natDegree ≤ 352552)
    (hd : P64Caps.YZ.yzSupportDegree Q 1 ≤ 58589180685)
    (hw : P64Caps.Weighted.weightedSupportDegree Q 1048575 ≤ 249292 * 1482911 - 1)
    (S : Finset F) (P : F → F[X]) (hbad : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hpair : (casePair Q S P).card ≤ 352552 * 58589180685)
    (hclass : ∀ R ∈ factors Q, ((caseSingle Q S P R).card : ℚ) ≤
      factorBound K1 K2 K3 R.natDegree (P64Caps.YZ.yzSupportDegree R 1)
        (P64Caps.Weighted.weightedSupportDegree R 1048575)) :
    S.card ≤ 2 ^ 64 - 235031 := by
  have hcover := card_le_cover Q hQ S P hbad
  have hY0 := (card_caseY0_le Q hQ S).trans hd
  have hw' : P64Caps.Weighted.weightedSupportDegree Q 1048575 ≤ 369677849011 := by
    norm_num at hw; omega
  have hsum := (Finset.sum_le_sum hclass).trans
    (sum_factorBound_le hK1 hK2 hK3 Q hQ _ _ _ hh hd hw')
  have hcoverQ : (S.card : ℚ) ≤ (caseY0 Q S).card + (casePair Q S P).card +
      ∑ R ∈ factors Q, ((caseSingle Q S P R).card : ℚ) := by exact_mod_cast hcover
  have hY0Q : ((caseY0 Q S).card : ℚ) ≤ 58589180685 := by exact_mod_cast hY0
  have hpairQ : ((casePair Q S P).card : ℚ) ≤ 352552 * 58589180685 := by exact_mod_cast hpair
  simp only [factorBound, cAlpha, cBeta, Nat.cast_ofNat] at hsum
  have htot : (S.card : ℚ) ≤ 18446744073709316585 := by linarith
  have : S.card ≤ 18446744073709316585 := by exact_mod_cast htot
  norm_num
  exact this

end P64Ledger
end ProximityPrize.SubmissionBinaryLower
