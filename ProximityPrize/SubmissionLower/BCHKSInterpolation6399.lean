import ProximityPrize.SubmissionLower.BCHKSConcreteGS6399
import ProximityPrize.SubmissionLower.BCHKSSubstitutionVanish

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open BCHKSConcreteGS6399
open BCHKSSubstitutionVanish

/-- Concrete GS interpolation plus the multiplicity/root-counting step, starting
from caller-chosen close RS codewords. -/
theorem exists_bchks_interpolant_vanishing6399
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field) (A : IRSProfile.Field → Finset IRSProfile.Index)
    (hA : ∀ z ∈ S, 185374 ≤ (A z).card)
    (hcomb : ∀ z ∈ S,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (A z)) :
    ∃ (P : ↥S → Polynomial IRSProfile.Field)
      (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field))),
      Q ≠ 0 ∧
      (∀ z : ↥S, (P z).natDegree ≤ 131071) ∧
      (∀ z : ↥S, ∀ i ∈ A z,
        Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) ∧
      (∀ z : ↥S, BCHKSSubstitutionVanish.triEval Q z.1 (P z) = 0) ∧
      (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
        j < 5280 ∧ a + 131071 * j < 692001142 ∧
          ((Q.coeff j).coeff a).natDegree + j < 13141403) := by
  classical
  have hw : ∀ z : ↥S, ∃ p : Polynomial IRSProfile.Field,
      p.natDegree ≤ 131071 ∧
      ∀ i ∈ A z.1,
        Polynomial.eval (IRSProfile.domain i) p = U 0 i + z.1 * U 1 i := by
    intro z
    have hz := hcomb z.1 z.2
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hz
    obtain ⟨c, hc, hceq⟩ := hz
    change c ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hc
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
    obtain ⟨p, hpdeg, rfl⟩ := hc
    refine ⟨p, ?_, ?_⟩
    · by_cases hp : p = 0
      · simp [hp]
      · have hlt : p.natDegree < IRSProfile.baseDimension :=
          (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
        norm_num [IRSProfile.baseDimension] at hlt ⊢
        omega
    · intro i hi
      have heq := congrFun hceq ⟨i, hi⟩
      simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using heq.symm
  let P : ↥S → Polynomial IRSProfile.Field := fun z => Classical.choose (hw z)
  have hPdeg : ∀ z : ↥S, (P z).natDegree ≤ 131071 :=
    fun z => (Classical.choose_spec (hw z)).1
  have hPagree : ∀ z : ↥S, ∀ i ∈ A z.1,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i :=
    fun z => (Classical.choose_spec (hw z)).2
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGS6399.exists_interpolant IRSProfile.domain (U 0) (U 1)
  refine ⟨P, Q, hQ, hPdeg, hPagree, ?_, hcaps⟩
  intro z
  apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    Q z.1 (P z) IRSProfile.domain (A z.1)
    (fun i => Polynomial.C (U 0 i) + Polynomial.X * Polynomial.C (U 1 i))
    3733 131071 692001141
  · intro i hi s t h hs
    have hz := congrArg (fun p : Polynomial IRSProfile.Field => p.coeff h)
      (hvan i s t hs)
    exact hz
  · intro i hi
    rw [hPagree z i hi]
    simp
    ring
  · exact hPdeg z
  · intro j a hja
    have hc := hcaps j a hja
    norm_num [BCHKSConcreteGS6399.DY, BCHKSConcreteGS6399.DX,
      BCHKSConcreteGS6399.k, BCHKSConcreteGS6399.DZ] at hc
    omega
  · have hc := hA z.1 z.2
    omega

end ProximityPrize.SubmissionLower
