import ProximityPrize.SubmissionLower.BCHKSFrobeniusConstantPairClosure6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveFullReceivedSlopeClosure6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusConstantPairClosure6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section FullSlope
variable {F : Type*} [Field F]
noncomputable def fullSlopeNormalizedOwner6401
    (P : F → F[X]) (V : F[X]) (z : F) : F[X] :=
  P z - Polynomial.C z * V
theorem fullSlopeNormalizedOwner_natDegree_le6401
    (P : F → F[X]) (V : F[X]) (z : F)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hV : V.natDegree ≤ ownerDegreeCap6401) :
    (fullSlopeNormalizedOwner6401 P V z).natDegree ≤
      ownerDegreeCap6401 := by
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hP ((Polynomial.natDegree_C_mul_le z V).trans hV))
theorem fullSlopeNormalizedOwner_eval_eq_intercept6401
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (P : F → F[X]) (V : F[X]) (z : F) (i : Fin n6401)
    (hV : V.eval (alpha i) = u1 i)
    (howner : (P z).eval (alpha i) = u0 i + z * u1 i) :
    (fullSlopeNormalizedOwner6401 P V z).eval (alpha i) = u0 i := by
  simp only [fullSlopeNormalizedOwner6401, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, hV, howner]
  ring
def fullReceivedSlopeOwnerCap6401 : Nat :=
  BCHKSList6401.listBound6401 * 1182
theorem fullReceivedSlopeOwnerCap_exact6401 :
    fullReceivedSlopeOwnerCap6401 = 20148187608 := by
  native_decide
theorem fullReceivedSlope_ownerFamily_card_le6401
    [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → F[X]) (V : F[X])
    (hVdegree : V.natDegree ≤ ownerDegreeCap6401)
    (hV : ∀ i, V.eval (alpha i) = u1 i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      (P z).eval (alpha i) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ fullReceivedSlopeOwnerCap6401 := by
  classical
  let N : F → F[X] := fullSlopeNormalizedOwner6401 P V
  let T : Finset F[X] := S.image N
  let source : {R // R ∈ T} → F := fun R ↦
    Classical.choose (Finset.mem_image.mp R.2)
  have hsourceS (R : {R // R ∈ T}) : source R ∈ S :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).1
  have hsourceEq (R : {R // R ∈ T}) : N (source R) = R.1 :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).2
  let AT : {R // R ∈ T} → Finset (Fin n6401) :=
    fun R ↦ A (source R)
  have hTcard : T.card ≤ BCHKSList6401.listBound6401 := by
    have hbound := scalarPolynomialFamily_card_le_17045844
      alpha u0 (fun R : {R // R ∈ T} ↦ R.1) AT
      Subtype.val_injective
      (by
        intro R
        rw [← hsourceEq R]
        exact fullSlopeNormalizedOwner_natDegree_le6401 P V (source R)
          (hPdegree (source R) (hsourceS R)) hVdegree)
      (by
        intro R
        exact hrow (source R) (hsourceS R))
      (by
        intro R i hi
        rw [← hsourceEq R]
        exact fullSlopeNormalizedOwner_eval_eq_intercept6401
          alpha u0 u1 P V (source R) i (hV i)
            (howner (source R) (hsourceS R) i hi))
    simpa using hbound
  let fiber : F[X] → Finset F := fun R ↦
    S.filter fun z ↦ N z = R
  have hfiber : ∀ R ∈ T, (fiber R).card ≤ 1182 := by
    intro R hRT
    have hRdegree : R.natDegree ≤ ownerDegreeCap6401 := by
      obtain ⟨z, hzS, hNz⟩ := Finset.mem_image.mp hRT
      rw [← hNz]
      exact fullSlopeNormalizedOwner_natDegree_le6401 P V z
        (hPdegree z hzS) hVdegree
    apply affineFamily_card_le_1182_of_no_curveWitness6401
      S (fiber R) P R V hfail hRdegree hVdegree
    · intro z hz
      exact (Finset.mem_filter.mp hz).1
    · intro z hz
      have hNz : N z = R := (Finset.mem_filter.mp hz).2
      dsimp only [N, fullSlopeNormalizedOwner6401] at hNz
      linear_combination hNz
  have hcover : T.biUnion fiber = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨R, _hRT, hzfib⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hzfib).1
    · intro hz
      apply Finset.mem_biUnion.mpr
      refine ⟨N z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  rw [← hcover]
  apply (Finset.card_biUnion_le_card_mul T fiber 1182 hfiber).trans
  exact Nat.mul_le_mul_right 1182 hTcard
theorem polynomialAffineCurveWitness_of_fullReceivedSlope6401
    [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → F[X]) (V : F[X])
    (hVdegree : V.natDegree ≤ ownerDegreeCap6401)
    (hV : ∀ i, V.eval (alpha i) = u1 i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      (P z).eval (alpha i) = u0 i + z * u1 i)
    (hlarge : fullReceivedSlopeOwnerCap6401 < S.card) :
    PolynomialAffineCurveWitness6401 S P := by
  by_contra hfail
  have hcap := fullReceivedSlope_ownerFamily_card_le6401
    alpha u0 u1 S A P V hVdegree hV hPdegree hrow howner hfail
  omega
end FullSlope
end BCHKSExtremePrimitiveFullReceivedSlopeClosure6401
end ProximityPrize.SubmissionLower
