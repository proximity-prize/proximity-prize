import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C1
import ProximityPrize.SubmissionLower.W2

/-
Research draft, outside the submission archive; not compiled.

The input is genuine univariate root divisibility of the top Y coefficient
at Y degree 0 or 1. No dimension estimate is a hypothesis. In particular,
this file does not assume the unproved contact/colon-to-root bridge.

All coefficient boxes below are C1's boxes, not Q's older seed-only box.
-/
namespace ProximityPrize.SubmissionLower.RegularColonQuotientProjection
open scoped BigOperators
open RCN100 RCN355
noncomputable section
variable {K : Type*} [Field K]

abbrev Index (D w L : ℕ) := CoefficientIndex D w L 0

theorem index_ext {D w L : ℕ} {c d : Index D w L}
    (hy : c.1.val = d.1.val)
    (hz : c.2.2.1.val = d.2.2.1.val)
    (hx : c.2.2.2.val = d.2.2.2.val) : c = d := by
  apply columnExponent_injective D w L 0
  ext i
  fin_cases i
  · simpa only [columnExponent_x] using hx
  · simpa only [columnExponent_y] using hy
  · simp only [columnExponent_r]
    have hc := c.2.1.isLt
    have hd := d.2.1.isLt
    omega
  · simpa only [columnExponent_z] using hz

/-- The coefficient of Y^j Z^z, viewed as a univariate polynomial in X. -/
def xSlice {D w L : ℕ} (a : Index D w L → K) (j z : ℕ) : Polynomial K :=
  ∑ c : Index D w L,
    if c.1.val = j ∧ c.2.2.1.val = z then
      Polynomial.monomial c.2.2.2.val (a c)
    else 0

theorem xSlice_coeff {D w L : ℕ} (a : Index D w L → K)
    (c : Index D w L) :
    (xSlice a c.1.val c.2.2.1.val).coeff c.2.2.2.val = a c := by
  classical
  rw [xSlice, Polynomial.finsetSum_coeff, Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    by_cases hy : d.1.val = c.1.val
    · by_cases hz : d.2.2.1.val = c.2.2.1.val
      · have hx : d.2.2.2.val ≠ c.2.2.2.val := by
          intro h
          exact hdc (index_ext hy hz h)
        simp [hy, hz, Polynomial.coeff_monomial, hx, Ne.symm hx]
      · simp [hz]
    · simp [hy]
  · simp

theorem xSlice_coeff_eq_zero {D w L : ℕ} (a : Index D w L → K)
    (j z e : ℕ)
    (h : ∀ c : Index D w L, c.1.val = j → c.2.2.1.val = z →
      c.2.2.2.val = e → a c = 0) : (xSlice a j z).coeff e = 0 := by
  classical
  rw [xSlice, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hy : c.1.val = j
  · by_cases hz : c.2.2.1.val = z
    · by_cases hx : c.2.2.2.val = e
      · simp [hy, hz, hx, h c hy hz hx]
      · simp [hy, hz, Polynomial.coeff_monomial, hx, Ne.symm hx]
    · simp [hz]
  · simp [hy]

def residualMass (points : Finset K) (mu : K → ℕ) (j : ℕ) : ℕ :=
  ∑ x ∈ points, (mu x - j)

/-- This avoids products of (X-x), coprimality, and K(Z) entirely. -/
theorem polynomial_eq_zero_of_roots_and_high_coefficients
    (points : Finset K) (orders : K → ℕ) (p : Polynomial K)
    (hroot : ∀ x ∈ points, (Polynomial.X - Polynomial.C x) ^ orders x ∣ p)
    (hhigh : ∀ e : ℕ, (∑ x ∈ points, orders x) ≤ e → p.coeff e = 0) :
    p = 0 := by
  classical
  by_contra hp
  have hdegree : (∑ x ∈ points, orders x) ≤ p.natDegree := by
    calc
      _ ≤ ∑ x ∈ points, p.rootMultiplicity x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Polynomial.le_rootMultiplicity_iff hp).mpr (hroot x hx)
      _ ≤ p.natDegree := sum_rootMultiplicity_le_natDegree p points
  have hc := hhigh p.natDegree hdegree
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (by simpa only [Polynomial.coeff_natDegree] using hc)

theorem layer_eq_zero {D w L : ℕ} (a : Index D w L → K)
    (points : Finset K) (mu : K → ℕ) (j : ℕ)
    (hroot : ∀ z x, x ∈ points →
      (Polynomial.X - Polynomial.C x) ^ (mu x - j) ∣ xSlice a j z)
    (hhigh : ∀ c : Index D w L, c.1.val = j →
      residualMass points mu j ≤ c.2.2.2.val → a c = 0) :
    ∀ c : Index D w L, c.1.val = j → a c = 0 := by
  intro c hc
  have hz : xSlice a j c.2.2.1.val = 0 := by
    apply polynomial_eq_zero_of_roots_and_high_coefficients
      points (fun x => mu x - j)
    · exact hroot c.2.2.1.val
    · intro e he
      apply xSlice_coeff_eq_zero
      intro b hb _ hbe
      apply hhigh b hb
      change residualMass points mu j ≤ e at he
      simpa only [hbe] using he
  have hcoeff := xSlice_coeff a c
  rw [hc, hz, Polynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

/-- Only the two low Y layers have any coefficients discarded. -/
def twoLayerCut (points : Finset K) (mu : K → ℕ) (j : ℕ) : ℕ :=
  if j ≤ 1 then residualMass points mu j else 0

theorem twoLayer_zero_criterion {D w L : ℕ} (a : Index D w L → K)
    (points : Finset K) (mu : K → ℕ)
    (hroot : ∀ j : ℕ, j ≤ 1 →
      (∀ c : Index D w L, j < c.1.val → a c = 0) →
      ∀ z x, x ∈ points →
        (Polynomial.X - Polynomial.C x) ^ (mu x - j) ∣ xSlice a j z)
    (hkept : ∀ c : Index D w L,
      twoLayerCut points mu c.1.val ≤ c.2.2.2.val → a c = 0) : a = 0 := by
  have hhigh : ∀ c : Index D w L, 1 < c.1.val → a c = 0 := by
    intro c hc
    apply hkept c
    simp [twoLayerCut, Nat.not_le.mpr hc]
  have h1 : ∀ c : Index D w L, c.1.val = 1 → a c = 0 := by
    apply layer_eq_zero a points mu 1 (hroot 1 (by decide) hhigh)
    intro c hc he
    apply hkept c
    simpa [twoLayerCut, hc] using he
  have habove0 : ∀ c : Index D w L, 0 < c.1.val → a c = 0 := by
    intro c hc
    by_cases h : c.1.val = 1
    · exact h1 c h
    · exact hhigh c (by omega)
  have h0 : ∀ c : Index D w L, c.1.val = 0 → a c = 0 := by
    apply layer_eq_zero a points mu 0 (hroot 0 (by decide) habove0)
    intro c hc he
    apply hkept c
    simpa [twoLayerCut, hc] using he
  funext c
  by_cases h : c.1.val = 0
  · exact h0 c h
  · exact habove0 c (by omega)

/-- Coordinates in the high-X strip of each Y layer. The X coordinate is
    stored after subtracting the lower endpoint, keeping the target finite. -/
abbrev RetainedIndex (D w L : ℕ) (cut : ℕ → ℕ) :=
  (j : Fin (L + 1)) × (Fin (L + 1 - j.val) × Fin (D - w * j.val - cut j.val))

def retainedColumn {D w L : ℕ} (cut : ℕ → ℕ)
    (c : RetainedIndex D w L cut) : Index D w L :=
  ⟨c.1, ⟨0, ⟨⟨c.2.1.val, by simpa using c.2.1.isLt⟩,
    ⟨cut c.1.val + c.2.2.val, by
      have h := c.2.2.isLt
      change cut c.1.val + c.2.2.val < D - w * c.1.val
      omega⟩⟩⟩⟩

theorem retainedColumn_preimage {D w L : ℕ} (cut : ℕ → ℕ)
    (c : Index D w L) (hc : cut c.1.val ≤ c.2.2.2.val) :
    ∃ b : RetainedIndex D w L cut, retainedColumn cut b = c := by
  have hr : c.2.1.val = 0 := by have h := c.2.1.isLt; omega
  let b : RetainedIndex D w L cut :=
    ⟨c.1, ⟨⟨c.2.2.1.val, by simpa only [hr, Nat.sub_zero] using c.2.2.1.isLt⟩,
      ⟨c.2.2.2.val - cut c.1.val, by
        have h := c.2.2.2.isLt
        rw [hr, Nat.mul_zero, Nat.sub_zero] at h
        omega⟩⟩⟩
  refine ⟨b, ?_⟩
  apply index_ext
  · rfl
  · rfl
  · change cut c.1.val + (c.2.2.2.val - cut c.1.val) = c.2.2.2.val
    omega

def coefficientProjection {D w L : ℕ}
    (V : Submodule K (Index D w L → K)) (cut : ℕ → ℕ) :
    V →ₗ[K] (RetainedIndex D w L cut → K) where
  toFun a c := a.1 (retainedColumn cut c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def LowTopRootDivisibility {D w L : ℕ}
    (V : Submodule K (Index D w L → K)) (points : Finset K) (mu : K → ℕ) : Prop :=
  ∀ a : V, ∀ j : ℕ, j ≤ 1 →
    (∀ c : Index D w L, j < c.1.val → a.1 c = 0) →
    ∀ z x, x ∈ points →
      (Polynomial.X - Polynomial.C x) ^ (mu x - j) ∣ xSlice a.1 j z

theorem coefficientProjection_injective {D w L : ℕ}
    (V : Submodule K (Index D w L → K)) (points : Finset K) (mu : K → ℕ)
    (hroot : LowTopRootDivisibility V points mu) :
    Function.Injective (coefficientProjection V (twoLayerCut points mu)) := by
  intro a b hab
  have hd : coefficientProjection V (twoLayerCut points mu) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hz : (a - b).1 = 0 := by
    apply twoLayer_zero_criterion (a - b).1 points mu (hroot (a - b))
    intro c hc
    obtain ⟨d, hdc⟩ := retainedColumn_preimage (twoLayerCut points mu) c hc
    have hh := congrFun hd d
    change (a - b).1 (retainedColumn (twoLayerCut points mu) d) = 0 at hh
    simpa only [hdc] using hh
  have hsub : a - b = 0 := Subtype.ext hz
  exact sub_eq_zero.mp hsub

theorem finrank_le_retained_card {D w L : ℕ}
    (V : Submodule K (Index D w L → K)) (points : Finset K) (mu : K → ℕ)
    (hroot : LowTopRootDivisibility V points mu) :
    Module.finrank K V ≤ Fintype.card (RetainedIndex D w L (twoLayerCut points mu)) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (coefficientProjection_injective V points mu hroot)
  simpa only [Module.finrank_fintype_fun_eq_card] using h

theorem retainedIndex_card (D w L : ℕ) (cut : ℕ → ℕ) :
    Fintype.card (RetainedIndex D w L cut) =
      ∑ j ∈ Finset.range (L + 1), (L + 1 - j) * (D - w * j - cut j) := by
  simp [RetainedIndex, Fintype.card_sigma, Finset.sum_range]

theorem mass_zero_le_one_add_card (points : Finset K) (mu : K → ℕ) :
    residualMass points mu 0 ≤ residualMass points mu 1 + points.card := by
  classical
  unfold residualMass
  simp only [Nat.sub_zero]
  calc
    (∑ x ∈ points, mu x) ≤ ∑ x ∈ points, (mu x - 1 + 1) := by
      apply Finset.sum_le_sum
      intro x _
      omega
    _ = (∑ x ∈ points, (mu x - 1)) + points.card := by
      simp [Finset.sum_add_distrib]

def candidateWidth : Fin 5 → ℕ := ![50962, 182035, 305380, 174309, 43238]

abbrev CandidateIndex :=
  (j : Fin 5) × (Fin (239947 - j.val) × Fin (candidateWidth j))

theorem retained_width_le_candidate
    (points : Finset K) (mu : K → ℕ) (D : ℕ)
    (hcard : points.card = 262144)
    (hmass : D ≤ residualMass points mu 0 + 50962)
    (hD : D ≤ 567522) (j : Fin 5) :
    D - 131071 * j.val - twoLayerCut points mu j.val ≤ candidateWidth j := by
  have hm := mass_zero_le_one_add_card points mu
  rw [hcard] at hm
  fin_cases j
  · change D - residualMass points mu 0 ≤ 50962
    omega
  · change D - 131071 - residualMass points mu 1 ≤ 182035
    omega
  · change D - 262142 ≤ 305380
    omega
  · change D - 393213 ≤ 174309
    omega
  · change D - 524284 ≤ 43238
    omega

theorem retainedIndex_y_lt_five {D L : ℕ} (cut : ℕ → ℕ)
    (hD : D ≤ 567522) (c : RetainedIndex D 131071 L cut) : c.1.val < 5 := by
  have h := c.2.2.isLt
  omega

def candidateIndexMap {D L : ℕ}
    (points : Finset K) (mu : K → ℕ)
    (hcard : points.card = 262144)
    (hmass : D ≤ residualMass points mu 0 + 50962)
    (hD : D ≤ 567522) (hL : L ≤ 239946)
    (c : RetainedIndex D 131071 L (twoLayerCut points mu)) : CandidateIndex :=
  ⟨⟨c.1.val, retainedIndex_y_lt_five _ hD c⟩,
    ⟨⟨c.2.1.val, by have h := c.2.1.isLt; omega⟩,
      ⟨c.2.2.val, lt_of_lt_of_le c.2.2.isLt
        (retained_width_le_candidate points mu D hcard hmass hD
          ⟨c.1.val, retainedIndex_y_lt_five _ hD c⟩)⟩⟩⟩

theorem retainedIndex_ext {D w L : ℕ} {cut : ℕ → ℕ}
    {c d : RetainedIndex D w L cut}
    (hy : c.1.val = d.1.val) (hz : c.2.1.val = d.2.1.val)
    (hx : c.2.2.val = d.2.2.val) : c = d := by
  rcases c with ⟨⟨cj, hcj⟩, ⟨⟨cz, hcz⟩, ⟨ce, hce⟩⟩⟩
  rcases d with ⟨⟨dj, hdj⟩, ⟨⟨dz, hdz⟩, ⟨de, hde⟩⟩⟩
  change cj = dj at hy
  change cz = dz at hz
  change ce = de at hx
  subst dj
  subst dz
  subst de
  rfl

theorem candidateIndexMap_injective {D L : ℕ}
    (points : Finset K) (mu : K → ℕ)
    (hcard : points.card = 262144)
    (hmass : D ≤ residualMass points mu 0 + 50962)
    (hD : D ≤ 567522) (hL : L ≤ 239946) :
    Function.Injective (candidateIndexMap points mu hcard hmass hD hL) := by
  intro c d h
  apply retainedIndex_ext
  · exact congrArg (fun e : CandidateIndex => e.1.val) h
  · exact congrArg (fun e : CandidateIndex => e.2.1.val) h
  · exact congrArg (fun e : CandidateIndex => e.2.2.val) h

theorem candidateIndex_card : Fintype.card CandidateIndex = 181380207354 := by
  norm_num [CandidateIndex, Fintype.card_sigma, Fin.sum_univ_succ, candidateWidth]

/-- The parameter D is the actual quotient weighted bound. Only the final
    coordinate embedding uses its numerical upper bound. -/
theorem finrank_le_candidate {D L : ℕ}
    (V : Submodule K (Index D 131071 L → K))
    (points : Finset K) (mu : K → ℕ)
    (hroot : LowTopRootDivisibility V points mu)
    (hcard : points.card = 262144)
    (hmass : D ≤ residualMass points mu 0 + 50962)
    (hD : D ≤ 567522) (hL : L ≤ 239946) :
    Module.finrank K V ≤ 181380207354 := by
  calc
    Module.finrank K V ≤
        Fintype.card (RetainedIndex D 131071 L (twoLayerCut points mu)) :=
      finrank_le_retained_card V points mu hroot
    _ ≤ Fintype.card CandidateIndex := Fintype.card_le_of_injective _
      (candidateIndexMap_injective points mu hcard hmass hD hL)
    _ = 181380207354 := candidateIndex_card

end
end ProximityPrize.SubmissionLower.RegularColonQuotientProjection
