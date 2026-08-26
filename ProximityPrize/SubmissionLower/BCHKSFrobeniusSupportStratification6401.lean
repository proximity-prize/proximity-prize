import ProximityPrize.SubmissionLower.BCHKSUniversalPolynomialAlignment6399
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusSupportStratification6401
open Polynomial
open ProximityPrize.Benchmark
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def actualAgreementSet6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) : Finset IRSProfile.Index :=
  Finset.univ.filter fun i =>
    Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i
def actualErrorSupport6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) : Finset IRSProfile.Index :=
  Finset.univ \ actualAgreementSet6401 u0 u1 P z
theorem actualAgreement_add_error_card6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) :
    (actualAgreementSet6401 u0 u1 P z).card +
        (actualErrorSupport6401 u0 u1 P z).card = n6401 := by
  classical
  change (actualAgreementSet6401 u0 u1 P z).card +
    ((Finset.univ : Finset IRSProfile.Index) \
      actualAgreementSet6401 u0 u1 P z).card = n6401
  rw [Finset.card_sdiff_of_subset (by simp :
    actualAgreementSet6401 u0 u1 P z ⊆
      (Finset.univ : Finset IRSProfile.Index))]
  have hle : (actualAgreementSet6401 u0 u1 P z).card ≤ 262144 := by
    have := Finset.card_le_card (show
      actualAgreementSet6401 u0 u1 P z ⊆
        (Finset.univ : Finset IRSProfile.Index) by simp)
    norm_num [IRSProfile.Index] at this ⊢
    exact this
  norm_num [n6401, IRSProfile.Index]
  omega
theorem actualAgreement_card_ge_of_chosen_rows6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (z : IRSProfile.Field)
    (hAcard : a6401 ≤ (A z).card)
    (howner : ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i) :
    a6401 ≤ (actualAgreementSet6401 u0 u1 P z).card := by
  apply hAcard.trans (Finset.card_le_card ?_)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, howner i hi⟩
theorem actualErrorSupport_card_le_target6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (z : IRSProfile.Field)
    (hAcard : a6401 ≤ (A z).card)
    (howner : ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i) :
    (actualErrorSupport6401 u0 u1 P z).card ≤ bchksErrors6401 := by
  have hsum := actualAgreement_add_error_card6401 u0 u1 P z
  have hagree := actualAgreement_card_ge_of_chosen_rows6401
    u0 u1 P A z hAcard howner
  norm_num [n6401, a6401, bchksErrors6401] at hsum hagree ⊢
  omega
def oldRadiusOwners6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (S : Finset IRSProfile.Field) : Finset IRSProfile.Field :=
  S.filter fun z =>
    (actualErrorSupport6401 u0 u1 P z).card ≤ bchksErrors6399
private theorem degree_lt_baseDimension_of_natDegree_le6401
    {p : Polynomial IRSProfile.Field}
    (hp : p.natDegree ≤ ownerDegreeCap6401) :
    p.degree < (IRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hp0]
    norm_num [IRSProfile.baseDimension, ownerDegreeCap6401] at hp ⊢
    omega
theorem oldRadiusOwners_card_le_6399_of_no_curve6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    (oldRadiusOwners6401 u0 u1 P S).card ≤ bchksNumerator6399 := by
  classical
  let Slow := oldRadiusOwners6401 u0 u1 P S
  by_contra hcap
  have hlarge : bchksNumerator6399 < Slow.card := by
    dsimp [Slow]
    omega
  let U : Fin 2 → IRSProfile.Index → IRSProfile.Field := ![u0, u1]
  let Aold : IRSProfile.Field → Finset IRSProfile.Index := fun z =>
    actualAgreementSet6401 u0 u1 P z
  have hAold : ∀ z ∈ Slow,
      Fintype.card IRSProfile.Index - bchksErrors6399 ≤ (Aold z).card := by
    intro z hz
    have herr : (actualErrorSupport6401 u0 u1 P z).card ≤
        bchksErrors6399 := (Finset.mem_filter.mp hz).2
    have hsum := actualAgreement_add_error_card6401 u0 u1 P z
    dsimp [Aold]
    norm_num [IRSProfile.Index, n6401, bchksErrors6399] at hsum herr ⊢
    omega
  have hcomb : ∀ z ∈ Slow,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (Aold z) ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (Aold z) := by
    intro z hz
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    let w := ReedSolomon.evalOnPoints IRSProfile.domain (P z)
    refine ⟨w, ?_, ?_⟩
    · apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
      exact degree_lt_baseDimension_of_natDegree_le6401
        (hPdegree z (Finset.mem_filter.mp hz).1)
    · funext x
      have hx := (Finset.mem_filter.mp x.2).2
      simpa [w, U, Aold, actualAgreementSet6401,
        LinearCode.projectedWord, ReedSolomon.evalOnPoints] using hx.symm
  let halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6399 bchksNumerator6399 :=
    alignmentBound6399_of_polynomialAlignment bchksPolynomialAlignment6399
  obtain ⟨p, hpcode, T, hTSlow, hTcard, hagree⟩ :=
    halign U Slow Aold hlarge hAold hcomb
  have hpPoly : ∀ j : Fin 2, ∃ q : Polynomial IRSProfile.Field,
      q.degree < (IRSProfile.baseDimension : WithBot ℕ) ∧
        p j = ReedSolomon.evalOnPoints IRSProfile.domain q := by
    intro j
    have hj := hpcode j
    change p j ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hj
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hj
    exact hj
  choose q hqdeg hpq using hpPoly
  have hqnat : ∀ j : Fin 2, (q j).natDegree ≤ ownerDegreeCap6401 := by
    intro j
    by_cases hq0 : q j = 0
    · simp [hq0]
    · have hj : (q j).natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hq0).2 (hqdeg j)
      norm_num [IRSProfile.baseDimension, ownerDegreeCap6401] at hj ⊢
      omega
  have hTS : T ⊆ S := hTSlow.trans (by
    intro z hz
    exact (Finset.mem_filter.mp hz).1)
  have hTout : weakCurveOutput6401 ≤ T.card := by
    norm_num [weakCurveOutput6401,
      BCHKSSphericalL3Radius76855Audit6401.targetSeedOutput,
      bchksErrors6399] at hTcard ⊢
    omega
  have hpolyline : ∀ z ∈ T,
      P z = q 0 + Polynomial.C z * q 1 := by
    intro z hz
    have hzSlow := hTSlow hz
    have hzS : z ∈ S := hTS hz
    let E := Aold z
    have hEcard : ownerDegreeCap6401 < E.card := by
      have hE := hAold z hzSlow
      norm_num [IRSProfile.Index, bchksErrors6399,
        ownerDegreeCap6401] at hE ⊢
      dsimp [E]
      omega
    let roots : Finset IRSProfile.Field := E.map IRSProfile.domain
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' (P z)
      (q 0 + Polynomial.C z * q 1) roots
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      have hrow := hagree z hz i hi
      have hxP : Polynomial.eval (IRSProfile.domain i) (P z) =
          u0 i + z * u1 i := by
        exact (Finset.mem_filter.mp hi).2
      have hp0 := congrFun (hpq 0) i
      have hp1 := congrFun (hpq 1) i
      change u0 i + z * u1 i = p 0 i + z * p 1 i at hrow
      change p 0 i = Polynomial.eval (IRSProfile.domain i) (q 0) at hp0
      change p 1 i = Polynomial.eval (IRSProfile.domain i) (q 1) at hp1
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C]
      calc
        Polynomial.eval (IRSProfile.domain i) (P z) =
            u0 i + z * u1 i := hxP
        _ = p 0 i + z * p 1 i := hrow
        _ = Polynomial.eval (IRSProfile.domain i) (q 0) +
            z * Polynomial.eval (IRSProfile.domain i) (q 1) := by
              rw [hp0, hp1]
    · have hzq1 : (Polynomial.C z * q 1).natDegree ≤
          ownerDegreeCap6401 :=
        (Polynomial.natDegree_C_mul_le z (q 1)).trans (hqnat 1)
      have hrhs : (q 0 + Polynomial.C z * q 1).natDegree ≤
          ownerDegreeCap6401 :=
        (Polynomial.natDegree_add_le _ _).trans
          (max_le (hqnat 0) hzq1)
      rw [Finset.card_map]
      exact (max_le (hPdegree z hzS) hrhs).trans_lt hEcard
  exact hfail ⟨q 0, q 1, hqnat 0, hqnat 1,
    T, hTS, hTout, hpolyline⟩
theorem nonOldRadiusOwners_card_lower6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    weakCurveSeedInput6401 - bchksNumerator6399 ≤
      (S \ oldRadiusOwners6401 u0 u1 P S).card := by
  have hsub : oldRadiusOwners6401 u0 u1 P S ⊆ S := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  rw [Finset.card_sdiff_of_subset hsub]
  have hcap := oldRadiusOwners_card_le_6399_of_no_curve6401
    u0 u1 S P hPdegree hfail
  omega
theorem nonOldRadiusOwners_exact_headroom6401 :
    weakCurveSeedInput6401 - bchksNumerator6399 =
      185800471298159157 := by
  norm_num [weakCurveSeedInput6401, bchksNumerator6399,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401, n6401,
    BCHKSSphericalL3Radius76855Audit6401.wideListBound]
def newErrorWeights6401 : Finset ℕ :=
  Finset.Icc (bchksErrors6399 + 1) bchksErrors6401
theorem newErrorWeights_card6401 : newErrorWeights6401.card = 20 := by
  native_decide
theorem exists_large_exact_error_fiber6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hAcard : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    ∃ s ∈ newErrorWeights6401,
      8679559967140553 <
        ((S \ oldRadiusOwners6401 u0 u1 P S).filter fun z =>
          (actualErrorSupport6401 u0 u1 P z).card = s).card := by
  classical
  let Shigh := S \ oldRadiusOwners6401 u0 u1 P S
  let weight : IRSProfile.Field → ℕ := fun z =>
    (actualErrorSupport6401 u0 u1 P z).card
  have hShigh : 185800471298159157 ≤ Shigh.card := by
    have h := nonOldRadiusOwners_card_lower6401
      u0 u1 S P hlarge hPdegree hfail
    rw [nonOldRadiusOwners_exact_headroom6401] at h
    exact h
  have hmaps : ∀ z ∈ Shigh, weight z ∈ newErrorWeights6401 := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hznot : z ∉ oldRadiusOwners6401 u0 u1 P S :=
      (Finset.mem_sdiff.mp hz).2
    have hlower : bchksErrors6399 < weight z := by
      by_contra hnot
      have hle : weight z ≤ bchksErrors6399 := by omega
      exact hznot (Finset.mem_filter.mpr ⟨hzS, hle⟩)
    have hupper : weight z ≤ bchksErrors6401 :=
      actualErrorSupport_card_le_target6401 u0 u1 P A z
        (hAcard z hzS) (howner z hzS)
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  have hpigeon : newErrorWeights6401.card * 8679559967140553 < Shigh.card := by
    rw [newErrorWeights_card6401]
    omega
  by_contra hnone
  push Not at hnone
  have hsum : Shigh.card =
      ∑ s ∈ newErrorWeights6401,
        (Shigh.filter fun z => weight z = s).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hupper : Shigh.card ≤
      newErrorWeights6401.card * 8679559967140553 := by
    rw [hsum]
    calc
      (∑ s ∈ newErrorWeights6401,
          (Shigh.filter fun z => weight z = s).card) ≤
          ∑ _s ∈ newErrorWeights6401, 8679559967140553 := by
            exact Finset.sum_le_sum fun s hs => hnone s hs
      _ = newErrorWeights6401.card * 8679559967140553 := by simp
  exact (Nat.not_lt_of_ge hupper) hpigeon
end BCHKSFrobeniusSupportStratification6401
end ProximityPrize.SubmissionLower
