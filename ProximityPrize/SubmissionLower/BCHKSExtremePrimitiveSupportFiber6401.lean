import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveNormDivisorFork6401
import ProximityPrize.SubmissionLower.BCHKSReceivedTailCompressionTwoOwner6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveSupportFiber6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSReceivedTailCompressionTwoOwner6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
section Generic
variable {F : Type} [Field F] [DecidableEq F]
  {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
  {u0 u1 : Fin n6401 → F}
  {S : Finset F} {A : F → Finset (Fin n6401)}
  {P : F → Polynomial F}
private theorem error_eq_zero_of_not_mem_puncturedSupport6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (i : W.PuncturedIndex)
    (hi : i ∉ puncturedErrorSupport6401 W z) :
    W.puncturedOwnerError z i = 0 := by
  simpa [puncturedErrorSupport6401] using hi
theorem puncturedSupport_complement_card_ge_162847_6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (howner : ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    162847 ≤
      ((Finset.univ : Finset W.PuncturedIndex) \
        puncturedErrorSupport6401 W z).card := by
  classical
  let retained : Finset (Fin n6401) :=
    A z \ W.sourcePuncture.badCoordinates
  let liftRetained : Finset W.PuncturedIndex :=
    retained.attach.map
      { toFun := fun i ↦
          ⟨i.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
            (Finset.mem_sdiff.mp i.2).2⟩⟩
        inj' := by
          intro i j hij
          apply Subtype.ext
          exact congrArg (fun x : W.PuncturedIndex ↦ x.1) hij }
  have hcard : liftRetained.card = retained.card := by
    rw [Finset.card_map, Finset.card_attach]
  have hsub : liftRetained ⊆
      (Finset.univ : Finset W.PuncturedIndex) \
        puncturedErrorSupport6401 W z := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have hjretained : j.1 ∈ retained := j.2
    have hjA : j.1 ∈ A z := (Finset.mem_sdiff.mp hjretained).1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hsupp
    have herr : W.puncturedOwnerError z
        ⟨j.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hjretained).2⟩⟩ ≠ 0 :=
      (Finset.mem_filter.mp hsupp).2
    apply herr
    dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError]
    rw [howner j.1 hjA]
    exact sub_self _
  have hretained := W.retained_agreements z hz
  rw [← hcard] at hretained
  exact hretained.trans (Finset.card_le_card hsub)
private theorem owner_eval_of_not_mem_puncturedSupport6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (i : W.PuncturedIndex)
    (hi : i ∉ puncturedErrorSupport6401 W z) :
    Polynomial.eval (alpha i.1) (P z) = u0 i.1 + z * u1 i.1 := by
  have hzero := error_eq_zero_of_not_mem_puncturedSupport6401 W z i hi
  dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError] at hzero
  exact sub_eq_zero.mp hzero
theorem curveWitness_of_constant_puncturedErrorSupport6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) (E : Finset W.PuncturedIndex)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hsupport : ∀ z ∈ T, puncturedErrorSupport6401 W z = E) :
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
  have hUcard : 162847 ≤ U.card := by
    have h := puncturedSupport_complement_card_ge_162847_6401
      W r.1 (hTgood r.2) (howner r.1 (hTS r.2))
    simpa [U, hsupport r.1 r.2] using h
  have hUlarge : ownerDegreeCap6401 < U.card := by
    have hcap : ownerDegreeCap6401 < 162847 := by native_decide
    exact hcap.trans_le hUcard
  have heval : ∀ z ∈ T, ∀ i ∈ U,
      Polynomial.eval (alpha i.1) (P z) = u0 i.1 + z * u1 i.1 := by
    intro z hz i hi
    apply owner_eval_of_not_mem_puncturedSupport6401 W z i
    have hiE : i ∉ E := (Finset.mem_sdiff.mp hi).2
    rw [hsupport z hz]
    exact hiE
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
      exact (max_le (hPdegree z (hTS hz)) hlineDegree).trans_lt hUlarge
  exact ⟨p0, p1, hp0, hp1, T, hTS, hTcard, hline⟩
theorem constant_puncturedErrorSupport_card_le_1182_of_noCurve6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) (E : Finset W.PuncturedIndex)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hsupport : ∀ z ∈ T, puncturedErrorSupport6401 W z = E)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    T.card ≤ 1182 := by
  by_contra hnot
  have hlarge : weakCurveOutput6401 ≤ T.card := by
    rw [show weakCurveOutput6401 = 1183 by native_decide]
    omega
  exact hfail (curveWitness_of_constant_puncturedErrorSupport6401
    W T E hTgood hlarge hPdegree howner hsupport)
noncomputable def puncturedErrorSupportFiber6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (G : Finset F) (E : Finset W.PuncturedIndex) : Finset F :=
  G.filter fun z ↦ puncturedErrorSupport6401 W z = E
theorem retainedOwner_card_le_supportAtlas_mul_1182_of_noCurve6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (G : Finset F) (atlas : Finset (Finset W.PuncturedIndex))
    (hGgood : G ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hcover : ∀ z ∈ G, ∃ E ∈ atlas,
      puncturedErrorSupport6401 W z = E)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    G.card ≤ atlas.card * 1182 := by
  classical
  let fiber := fun E : Finset W.PuncturedIndex ↦
    puncturedErrorSupportFiber6401 W G E
  have hfiber : ∀ E ∈ atlas, (fiber E).card ≤ 1182 := by
    intro E hE
    apply constant_puncturedErrorSupport_card_le_1182_of_noCurve6401
      W (fiber E) E
    · intro z hz
      exact hGgood (Finset.mem_filter.mp hz).1
    · exact hPdegree
    · exact howner
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · exact hfail
  have hunion : atlas.biUnion fiber = G := by
    ext z
    constructor
    · intro hz
      obtain ⟨E, _hE, hzFiber⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hzFiber).1
    · intro hz
      obtain ⟨E, hE, hzSupport⟩ := hcover z hz
      exact Finset.mem_biUnion.mpr
        ⟨E, hE, Finset.mem_filter.mpr ⟨hz, hzSupport⟩⟩
  rw [← hunion]
  exact Finset.card_biUnion_le_card_mul atlas fiber 1182 hfiber
theorem curveWitness_of_puncturedSupportAtlas6401
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (G : Finset F) (atlas : Finset (Finset W.PuncturedIndex))
    (hGgood : G ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hcover : ∀ z ∈ G, ∃ E ∈ atlas,
      puncturedErrorSupport6401 W z = E)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hlarge : atlas.card * 1182 < G.card) :
    PolynomialAffineCurveWitness6401 S P := by
  by_contra hfail
  have hcap := retainedOwner_card_le_supportAtlas_mul_1182_of_noCurve6401
    W G atlas hGgood hcover hPdegree howner hfail
  omega
end Generic
end BCHKSExtremePrimitiveSupportFiber6401
end ProximityPrize.SubmissionLower
