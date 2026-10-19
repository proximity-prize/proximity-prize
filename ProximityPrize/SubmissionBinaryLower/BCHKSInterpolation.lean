import ProximityPrize.SubmissionBinaryLower.BCHKSConcreteGS
import ProximityPrize.SubmissionBinaryLower.BCHKSSubstitutionVanish

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open BCHKSConcreteGS
open BCHKSSubstitutionVanish

/-- Concrete GS interpolation plus the multiplicity/root-counting step, starting
from caller-chosen close RS codewords. -/
theorem exists_bchks_interpolant_vanishing
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (S : Finset BinaryIRSProfile.Field) (A : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (hA : ∀ z ∈ S, 1483227 ≤ (A z).card)
    (hcomb : ∀ z ∈ S,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod BinaryIRSProfile.baseCode (A z)) :
    ∃ (P : ↥S → Polynomial BinaryIRSProfile.Field)
      (Q : Polynomial (Polynomial (Polynomial BinaryIRSProfile.Field))),
      Q ≠ 0 ∧
      (∀ z : ↥S, (P z).natDegree ≤ 1048575) ∧
      (∀ z : ↥S, ∀ i ∈ A z,
        Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) ∧
      (∀ z : ↥S, BCHKSSubstitutionVanish.triEval Q z.1 (P z) = 0) ∧
      (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
        j < 1289 ∧ a + 1048575 * j < 1351219797 ∧
          ((Q.coeff j).coeff a).natDegree + j < 1180364) := by
  classical
  have hw : ∀ z : ↥S, ∃ p : Polynomial BinaryIRSProfile.Field,
      p.natDegree ≤ 1048575 ∧
      ∀ i ∈ A z.1,
        Polynomial.eval (BinaryIRSProfile.domain i) p = U 0 i + z.1 * U 1 i := by
    intro z
    have hz := hcomb z.1 z.2
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hz
    obtain ⟨c, hc, hceq⟩ := hz
    change c ∈ ReedSolomon.code BinaryIRSProfile.domain BinaryIRSProfile.baseDimension at hc
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
    obtain ⟨p, hpdeg, rfl⟩ := hc
    refine ⟨p, ?_, ?_⟩
    · by_cases hp : p = 0
      · simp [hp]
      · have hlt : p.natDegree < BinaryIRSProfile.baseDimension :=
          (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
        norm_num [BinaryIRSProfile.baseDimension] at hlt ⊢
        omega
    · intro i hi
      have heq := congrFun hceq ⟨i, hi⟩
      simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using heq.symm
  let P : ↥S → Polynomial BinaryIRSProfile.Field := fun z => Classical.choose (hw z)
  have hPdeg : ∀ z : ↥S, (P z).natDegree ≤ 1048575 :=
    fun z => (Classical.choose_spec (hw z)).1
  have hPagree : ∀ z : ↥S, ∀ i ∈ A z.1,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i :=
    fun z => (Classical.choose_spec (hw z)).2
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGS.exists_interpolant BinaryIRSProfile.domain (U 0) (U 1)
  refine ⟨P, Q, hQ, hPdeg, hPagree, ?_, hcaps⟩
  intro z
  apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    Q z.1 (P z) BinaryIRSProfile.domain (A z.1)
    (fun i => Polynomial.C (U 0 i) + Polynomial.X * Polynomial.C (U 1 i))
    911 1048575 1351219796
  · intro i hi s t h hs
    have hz := congrArg (fun p : Polynomial BinaryIRSProfile.Field => p.coeff h)
      (hvan i s t hs)
    exact hz
  · intro i hi
    rw [hPagree z i hi]
    simp
    ring
  · exact hPdeg z
  · intro j a hja
    have hc := hcaps j a hja
    norm_num [BCHKSConcreteGS.DY, BCHKSConcreteGS.DX,
      BCHKSConcreteGS.k, BCHKSConcreteGS.DZ] at hc
    omega
  · have hc := hA z.1 z.2
    omega

end ProximityPrize.SubmissionBinaryLower
