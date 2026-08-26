import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveSupportFiber6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveSupportEnvelope6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSReceivedTailCompressionTwoOwner6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveSupportFiber6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
section Generic
variable {F : Type} [Field F] [DecidableEq F]
  {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
  {u0 u1 : Fin n6401 → F}
  {S : Finset F} {A : F → Finset (Fin n6401)}
  {P : F → Polynomial F}
private theorem owner_eval_of_outside_supportEnvelope6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (E : Finset W.PuncturedIndex)
    (hsupport : puncturedErrorSupport6401 W z ⊆ E)
    (i : W.PuncturedIndex) (hi : i ∉ E) :
    Polynomial.eval (alpha i.1) (P z) = u0 i.1 + z * u1 i.1 := by
  have hinot : i ∉ puncturedErrorSupport6401 W z := by
    intro himem
    exact hi (hsupport himem)
  have hzero : W.puncturedOwnerError z i = 0 := by
    simpa [puncturedErrorSupport6401] using hinot
  dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError] at hzero
  exact sub_eq_zero.mp hzero
theorem curveWitness_of_puncturedErrorSupportEnvelope6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) (E : Finset W.PuncturedIndex)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hsupport : ∀ z ∈ T, puncturedErrorSupport6401 W z ⊆ E)
    (hcomplement : ownerDegreeCap6401 <
      ((Finset.univ : Finset W.PuncturedIndex) \ E).card) :
    PolynomialAffineCurveWitness6401 S P := by
  classical
  have hTS : T ⊆ S := by
    intro z hz
    exact (Finset.mem_filter.mp (hTgood hz)).1
  have htwo : 1 < Fintype.card {z // z ∈ T} := by
    rw [Fintype.card_coe]
    have hseed : 2 ≤ weakCurveOutput6401 := by native_decide
    omega
  obtain ⟨r, s, hrs⟩ := Fintype.one_lt_card_iff.mp htwo
  have hrsValue : r.1 ≠ s.1 := by
    intro h
    exact hrs (Subtype.ext h)
  let p0 : Polynomial F :=
    reconstructedBasePolynomial6401 r.1 s.1 (P r.1) (P s.1)
  let p1 : Polynomial F :=
    reconstructedDirectionPolynomial6401 r.1 s.1 (P r.1) (P s.1)
  have hp0 : p0.natDegree ≤ ownerDegreeCap6401 := by
    exact reconstructedBasePolynomial_natDegree_le6401
      r.1 s.1 (P r.1) (P s.1) ownerDegreeCap6401
        (hPdegree r.1 (hTS r.2)) (hPdegree s.1 (hTS s.2))
  have hp1 : p1.natDegree ≤ ownerDegreeCap6401 := by
    exact reconstructedDirectionPolynomial_natDegree_le6401
      r.1 s.1 (P r.1) (P s.1) ownerDegreeCap6401
        (hPdegree r.1 (hTS r.2)) (hPdegree s.1 (hTS s.2))
  let U : Finset W.PuncturedIndex := Finset.univ \ E
  have heval : ∀ z ∈ T, ∀ i ∈ U,
      Polynomial.eval (alpha i.1) (P z) = u0 i.1 + z * u1 i.1 := by
    intro z hz i hi
    exact owner_eval_of_outside_supportEnvelope6401 W z E
      (hsupport z hz) i (Finset.mem_sdiff.mp hi).2
  have hline : ∀ z ∈ T,
      P z = p0 + Polynomial.C z * p1 := by
    intro z hz
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      (P z) (p0 + Polynomial.C z * p1) (U.map W.puncturedAlpha)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hrEval := heval r.1 r.2 i hi
      have hsEval := heval s.1 s.2 i hi
      have hzEval := heval z hz i hi
      have hp0Eval : Polynomial.eval (alpha i.1) p0 = u0 i.1 := by
        simpa [p0] using reconstructedBasePolynomial_eval6401
          r.1 s.1 (alpha i.1) (u0 i.1) (u1 i.1)
            (P r.1) (P s.1) hrsValue hrEval hsEval
      have hp1Eval : Polynomial.eval (alpha i.1) p1 = u1 i.1 := by
        simpa [p1] using reconstructedDirectionPolynomial_eval6401
          r.1 s.1 (alpha i.1) (u0 i.1) (u1 i.1)
            (P r.1) (P s.1) hrsValue hrEval hsEval
      change Polynomial.eval (alpha i.1) (P z) =
        Polynomial.eval (alpha i.1) (p0 + Polynomial.C z * p1)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      rw [hp0Eval, hp1Eval]
      exact hzEval
    · rw [Finset.card_map]
      have hlineDegree :
          (p0 + Polynomial.C z * p1).natDegree ≤
            ownerDegreeCap6401 := by
        apply (Polynomial.natDegree_add_le _ _).trans
        exact max_le hp0
          ((Polynomial.natDegree_C_mul_le z p1).trans hp1)
      exact (max_le (hPdegree z (hTS hz)) hlineDegree).trans_lt
        (by simpa [U] using hcomplement)
  exact ⟨p0, p1, hp0, hp1, T, hTS, hTcard, hline⟩
noncomputable def puncturedErrorSupportUnion6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) : Finset W.PuncturedIndex :=
  T.biUnion (puncturedErrorSupport6401 W)
theorem puncturedErrorSupport_subset_union6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) (z : F) (hz : z ∈ T) :
    puncturedErrorSupport6401 W z ⊆ puncturedErrorSupportUnion6401 W T := by
  classical
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨z, hz, hi⟩
theorem noCurve_supportUnion_complement_card_le_131071_6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    ((Finset.univ : Finset W.PuncturedIndex) \
      puncturedErrorSupportUnion6401 W T).card ≤ ownerDegreeCap6401 := by
  by_contra hnot
  have hlarge : ownerDegreeCap6401 <
      ((Finset.univ : Finset W.PuncturedIndex) \
        puncturedErrorSupportUnion6401 W T).card := by omega
  exact hfail (curveWitness_of_puncturedErrorSupportEnvelope6401
    W T (puncturedErrorSupportUnion6401 W T) hTgood hTcard hPdegree
      (fun z hz ↦ puncturedErrorSupport_subset_union6401 W T z hz) hlarge)
theorem noCurve_supportUnion_card_ge_108566_6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    108566 ≤ (puncturedErrorSupportUnion6401 W T).card := by
  classical
  let E := puncturedErrorSupportUnion6401 W T
  have houtside :
      ((Finset.univ : Finset W.PuncturedIndex) \ E).card ≤
        ownerDegreeCap6401 := by
    simpa [E] using noCurve_supportUnion_complement_card_le_131071_6401
      W T hTgood hTcard hPdegree hfail
  have hpartition := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ E)
  rw [Finset.card_univ] at hpartition
  have hpunctured := W.puncturedIndex_card_ge_239637
  have hcap : ownerDegreeCap6401 = 131071 := by native_decide
  change 108566 ≤ E.card
  omega
theorem binarySupportCube_is_only_abstract6401 :
    76732 + 58 = 76790 ∧
      76732 + 2 * 58 = 76848 ∧
      76848 < 108566 ∧
      weakCurveSeedInput6401 < 2 ^ 58 := by
  native_decide
end Generic
end BCHKSExtremePrimitiveSupportEnvelope6401
end ProximityPrize.SubmissionLower
