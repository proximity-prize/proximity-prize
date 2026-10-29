import ProximityPrize.SubmissionBinaryLower.P64C7Bessel

/-!
# The local slice at an irreducible factor

The slice is nonzero at every horizontal coordinate. Removing its lowest
power of the vertical variable gives the hypotheses used by DLT.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Slice

open Polynomial P64LineOrder P64C7Auxiliary

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

theorem exists_slice (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (x : F) (y : F[X]) :
    ∃ (ν : ℕ) (R'' : Polynomial (Polynomial F)), ν ≤ R.natDegree ∧
      (lineShift R x y).map (Polynomial.constantCoeff (R := Polynomial F)) =
        Polynomial.X ^ ν * R'' ∧ R''.coeff 0 ≠ 0 := by
  let Q := (lineShift R x y).map (Polynomial.constantCoeff (R := Polynomial F))
  have heq : Q = (evalXAt R x).comp (Polynomial.X + Polynomial.C y) := by
    ext b : 1
    simpa [Q, Polynomial.coeff_zero_eq_eval_zero] using lineShift_coeff_zero R x y b
  have hQ : Q ≠ 0 := by
    rw [heq]
    exact comp_X_add_C_ne_zero_iff.mpr (evalXAt_ne_zero_of_irreducible hirr hh x)
  have hd : Polynomial.X ^ Q.natTrailingDegree ∣ Q :=
    Polynomial.X_pow_dvd_iff.mpr (fun _ hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj)
  obtain ⟨R'', hR''⟩ := hd
  refine ⟨Q.natTrailingDegree, R'', ?_, hR'', ?_⟩
  · exact Q.natTrailingDegree_le_natDegree.trans
      (Polynomial.natDegree_map_le.trans (lineShift_degree_le R x y))
  · have hc := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQ
    have he := congrArg (fun G : Polynomial (Polynomial F) => G.coeff Q.natTrailingDegree) hR''
    simp only [Polynomial.coeff_X_pow_mul', le_refl, if_true, Nat.sub_self] at he
    rwa [← he]

end P64C7Slice
end ProximityPrize.SubmissionBinaryLower
