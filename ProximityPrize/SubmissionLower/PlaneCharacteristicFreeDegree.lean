import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.MatrixIrreducibleMultiplicity
import ProximityPrize.SubmissionLower.PlaneSylvesterFieldDegree

/-!
# Characteristic-free planar field-degree bound

The base generator contributes its full irreducible minpoly degree.  The
second generator contributes the full residue-field Sylvester corank.  The
irreducible determinant-multiplicity theorem couples the two factors, so the
result counts the entire extension degree without a separability hypothesis.
-/

namespace ProximityPrize.SubmissionLower.PlaneCharacteristicFreeDegree

open MatrixIrreducibleMultiplicity PlaneSylvesterFieldDegree

noncomputable section

variable {K A E : Type*} [Field K] [Field A] [Field E]
variable [Algebra K A] [Algebra A E] [Algebra K E] [IsScalarTower K A E]

/-- Two algebraic generators satisfying a proper planar pair have full tower
degree bounded by the actual fixed-degree resultant. -/
theorem finrank_le_resultant_natDegree
    [FiniteDimensional K A] [FiniteDimensional A E] [FiniteDimensional K E]
    (x : A) (y : E) (pbA : PowerBasis K A) (pbE : PowerBasis A E)
    (hgenA : pbA.gen = x) (hgenE : pbE.gen = y)
    (P Q : Polynomial (Polynomial K)) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hdim : pbE.dim ≤ m + n)
    (hPy : Polynomial.eval₂ (algebraMap A E) y
      (P.map (Polynomial.eval₂RingHom (algebraMap K A) x)) = 0)
    (hQy : Polynomial.eval₂ (algebraMap A E) y
      (Q.map (Polynomial.eval₂RingHom (algebraMap K A) x)) = 0)
    (hres : Polynomial.resultant P Q m n ≠ 0) :
    Module.finrank K E ≤ (Polynomial.resultant P Q m n).natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  let f : Polynomial K →+* A := Polynomial.eval₂RingHom (algebraMap K A) x
  let mu : Polynomial K := minpoly K x
  have hxint : IsIntegral K x := by
    rw [← hgenA]
    exact pbA.isIntegral_gen
  have hmuirr : Irreducible mu := minpoly.irreducible hxint
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨g, _, hg⟩ := pbA.exists_eq_aeval a
    refine ⟨g, ?_⟩
    change (Polynomial.aeval x) g = a
    rw [← hgenA]
    exact hg.symm
  have hker : ∀ g, f g = 0 ↔ mu ∣ g := by
    intro g
    change (Polynomial.aeval x) g = 0 ↔ minpoly K x ∣ g
    exact minpoly.dvd_iff.symm
  let p : Polynomial A := P.map f
  let q : Polynomial A := Q.map f
  have hpdeg : p.natDegree ≤ m := Polynomial.natDegree_map_le.trans hP
  have hqdeg : q.natDegree ≤ n := Polynomial.natDegree_map_le.trans hQ
  have hrelative : Module.finrank A E ≤
      m + n - (Polynomial.sylvester p q m n).rank :=
    finrank_le_sylvester_corank p q m n y pbE hgenE hpdeg hqdeg hdim hPy hQy
  let M : Matrix (Fin (m + n)) (Fin (m + n)) (Polynomial K) :=
    Polynomial.sylvester P Q m n
  have hdet : M.det ≠ 0 := by
    simpa [M, Polynomial.resultant] using hres
  have hmatrix : Polynomial.sylvester p q m n = f.mapMatrix M := by
    simpa [p, q, M] using Polynomial.sylvester_map_map P Q m n f
  have hbase : Module.finrank K A = mu.natDegree := by
    rw [pbA.finrank]
    simpa [mu, hgenA] using pbA.natDegree_minpoly.symm
  have hproduct : Module.finrank K A * Module.finrank A E = Module.finrank K E :=
    Module.finrank_mul_finrank K A E
  rw [← hproduct, hbase]
  calc
    mu.natDegree * Module.finrank A E ≤
        mu.natDegree * (m + n - (Polynomial.sylvester p q m n).rank) :=
      Nat.mul_le_mul_left _ hrelative
    _ = mu.natDegree * (Fintype.card (Fin (m + n)) - (f.mapMatrix M).rank) := by
      rw [Fintype.card_fin, hmatrix]
    _ ≤ M.det.natDegree :=
      natDegree_mul_corank_le_of_surjective_specialization
        mu hmuirr f hsurj hker M hdet
    _ = (Polynomial.resultant P Q m n).natDegree := by
      rfl

end

end ProximityPrize.SubmissionLower.PlaneCharacteristicFreeDegree

#print axioms ProximityPrize.SubmissionLower.PlaneCharacteristicFreeDegree.finrank_le_resultant_natDegree
