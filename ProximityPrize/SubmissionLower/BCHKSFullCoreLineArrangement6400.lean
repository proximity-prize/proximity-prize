import ProximityPrize.SubmissionLower.BCHKSLinearSelectedCore
namespace ProximityPrize.SubmissionLower
namespace BCHKSFullCoreLineArrangement6400
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
noncomputable def coreLocator
    {F : Type*} [Field F] (E : Finset F) : F[X] :=
  ∏ x ∈ E, ((Polynomial.X : F[X]) - Polynomial.C x)
theorem coreLocator_monic
    {F : Type*} [Field F] (E : Finset F) :
    (coreLocator E).Monic := by
  classical
  simpa only [coreLocator] using
    (Polynomial.monic_prod_X_sub_C (fun x : F => x) E)
@[simp] theorem coreLocator_natDegree
    {F : Type*} [Field F] (E : Finset F) :
    (coreLocator E).natDegree = E.card := by
  classical
  simpa [coreLocator] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card E (fun x : F => x))
theorem coreLocator_eval_ne_zero_of_not_mem
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (x : F) (hx : x ∉ E) :
    (coreLocator E).eval x ≠ 0 := by
  classical
  rw [coreLocator, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro y hy
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (fun hxy ↦ hx (by simpa [hxy] using hy))
theorem coreLocator_dvd_of_eval_eq_zero
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (D : F[X])
    (hzero : ∀ x ∈ E, D.eval x = 0) :
    coreLocator E ∣ D := by
  classical
  unfold coreLocator
  apply Finset.prod_dvd_of_coprime
  · intro x hx y hy hxy
    exact Polynomial.pairwise_coprime_X_sub_C (fun _ _ h => h) hxy
  · intro x hx
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero x hx
theorem eq_add_C_mul_coreLocator
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (P Q : F[X]) (k : ℕ)
    (hcard : E.card = k)
    (hPdeg : P.natDegree ≤ k) (hQdeg : Q.natDegree ≤ k)
    (heval : ∀ x ∈ E, P.eval x = Q.eval x) :
    ∃ c : F, P = Q + C c * coreLocator E := by
  classical
  let D : F[X] := P - Q
  have hDdeg : D.natDegree ≤ k := by
    dsimp [D]
    exact (Polynomial.natDegree_sub_le P Q).trans (max_le hPdeg hQdeg)
  have hDzero : ∀ x ∈ E, D.eval x = 0 := by
    intro x hx
    simp [D, heval x hx]
  have hGdvd : coreLocator E ∣ D :=
    coreLocator_dvd_of_eval_eq_zero E D hDzero
  have hGdeg : D.natDegree ≤ (coreLocator E).natDegree := by
    simpa [coreLocator_natDegree, hcard] using hDdeg
  have hshape : D = C D.leadingCoeff * coreLocator E :=
    Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (coreLocator_monic E) hGdvd hGdeg
  refine ⟨D.leadingCoeff, ?_⟩
  dsimp [D] at hshape
  linear_combination hshape
def bchksFullCoreOutsideCount6400 : ℕ := 131073
def bchksFullCoreExtraAgreement6400 : ℕ := 54293
def bchksFullCoreNonalignedPointCap6400 : ℕ := 158218
def bchksFullCoreLargeClassCount6400 : ℕ := 2
def bchksFullCoreOwnerCap6400 : ℕ := 311778
lemma bchksFullCore_lineArrangementLedger6400 :
    bchksFullCoreOutsideCount6400 = 262144 - 131071 ∧
    bchksFullCoreExtraAgreement6400 = 185364 - 131071 ∧
    bchksFullCoreNonalignedPointCap6400 =
      (bchksFullCoreOutsideCount6400 *
          (bchksFullCoreOutsideCount6400 - 1) / 2) /
        (bchksFullCoreExtraAgreement6400 - 1) ∧
    bchksFullCoreLargeClassCount6400 =
      bchksFullCoreOutsideCount6400 /
        bchksFullCoreExtraAgreement6400 ∧
    bchksFullCoreOwnerCap6400 =
      bchksFullCoreNonalignedPointCap6400 +
        bchksFullCoreLargeClassCount6400 * 76780 ∧
    bchksFullCoreOwnerCap6400 < 42324 * 76781 := by
  norm_num [bchksFullCoreOutsideCount6400,
    bchksFullCoreExtraAgreement6400,
    bchksFullCoreNonalignedPointCap6400,
    bchksFullCoreLargeClassCount6400,
    bchksFullCoreOwnerCap6400]
end BCHKSFullCoreLineArrangement6400
end ProximityPrize.SubmissionLower
