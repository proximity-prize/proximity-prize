import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research
import ProximityPrize.SubmissionLower.ContactRegularFactorGate

/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactFlagProjectionPositivity6543Research

open scoped Classical
open ContactRegularFactorGate
open ContactFlagTriangularProjectionResearch
open ContactFlagExactSeparableProjection6543Research
open ContactFlagPrincipalCycles6543Research
open ActualPlaneCoordinateKernel

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

/-- .
 -/
theorem derivative_planeMap (order : Equiv (Fin 3) (Fin 3)) (F : Poly3 K) :
    Polynomial.derivative (planeMap K order F) =
      planeMap K order (MvPolynomial.pderiv (order 1) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      obtain ⟨j, rfl⟩ := order.surjective i
      fin_cases j <;>
        simp [MvPolynomial.pderiv_mul, hP, Polynomial.derivative_mul,
          planeMap_X_first, planeMap_X_outer, planeMap_X_inner,
          Pi.single_apply] <;> ring

/-- .
 -/
theorem planeMap_natDegree_pos_of_pderiv_ne_zero
    (order : Equiv (Fin 3) (Fin 3)) (F : Poly3 K)
    (hderiv : MvPolynomial.pderiv (order 1) F ≠ 0) :
    0 < (planeMap K order F).natDegree := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hplanezero : Polynomial.derivative (planeMap K order F) = 0 :=
    Polynomial.derivative_of_natDegree_zero hzero
  rw [derivative_planeMap] at hplanezero
  apply hderiv
  apply planeMap_injective K order
  simpa only [map_zero] using hplanezero

/-- . -/
theorem pderiv_one_flagAlgHom (lam mu nu : K) (F : Poly3 K) :
    MvPolynomial.pderiv (1 : Fin 3) (flagAlgHom lam mu nu F) =
      flagAlgHom lam mu nu (MvPolynomial.pderiv (1 : Fin 3) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [flagImage, hP, MvPolynomial.pderiv_mul,
          Derivation.leibniz] <;> ring

/-- .
 -/
theorem pderiv_zero_flagAlgHom_nested (lam mu : K) (F : Poly3 K) :
    MvPolynomial.pderiv (0 : Fin 3)
        (flagAlgHom lam mu (mu * lam) F) =
      flagAlgHom lam mu (mu * lam)
        (MvPolynomial.pderiv (0 : Fin 3) F -
          MvPolynomial.C mu * MvPolynomial.pderiv (1 : Fin 3) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      simp [hP, hQ, mul_add, sub_eq_add_neg] <;> ring
  | mul_X P i hP =>
      fin_cases i <;>
        simp [flagImage, hP, MvPolynomial.pderiv_mul,
          Derivation.leibniz] <;> ring

/-- .

 -/
theorem flag_u_z_outer_positive_of_pderiv
    (lam mu : K) (G : Poly3 K)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    0 < (planeMap K uOrder
          (flagAlgHom lam mu (mu * lam) G)).natDegree ∧
      0 < (planeMap K zOrder
          (flagAlgHom lam mu (mu * lam) G)).natDegree := by
  have hflag : MvPolynomial.pderiv (1 : Fin 3)
      (flagAlgHom lam mu (mu * lam) G) ≠ 0 := by
    rw [pderiv_one_flagAlgHom]
    exact (flagEquiv lam mu (mu * lam)).injective.ne hderiv
  constructor
  · apply planeMap_natDegree_pos_of_pderiv_ne_zero uOrder
    simpa [uOrder] using hflag
  · apply planeMap_natDegree_pos_of_pderiv_ne_zero zOrder
    simpa [zOrder, Equiv.swap_apply_def] using hflag

section Characteristic

variable (p : ℕ) [CharP K p]

/-- .
 -/
theorem flag_u_z_outer_positive
    (lam mu : K) (G : Poly3 K)
    (hSpos : 0 < G.degreeOf 1) (hSchar : G.degreeOf 1 < p) :
    0 < (planeMap K uOrder
          (flagAlgHom lam mu (mu * lam) G)).natDegree ∧
      0 < (planeMap K zOrder
          (flagAlgHom lam mu (mu * lam) G)).natDegree := by
  have hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0 := by
    intro hzero
    have hz := (pderiv_zero_iff_degree_zero_below_char
      (1 : Fin 3) G p hSchar).mp hzero
    omega
  exact flag_u_z_outer_positive_of_pderiv lam mu G hderiv

/-- .
 -/
theorem flag_v_outer_positive_of_directional
    (lam mu : K) (G : Poly3 K)
    (hdirectional : MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C mu * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    0 < (planeMap K vOrder
        (flagAlgHom lam mu (mu * lam) G)).natDegree := by
  apply planeMap_natDegree_pos_of_pderiv_ne_zero vOrder
  simpa [vOrder, Equiv.swap_apply_def,
    pderiv_zero_flagAlgHom_nested] using
    (flagEquiv lam mu (mu * lam)).injective.ne hdirectional

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega p]
variable {G T H : MvPolynomial (Fin 3) Omega}
variable
    {hseparator : ∀ C : ContactRegularComponentCover.RegularComponent
        Omega G T H,
      Transcendental Omega
        (ActualCurveCoordinateField.coordinate Omega C.1 2)}
    {hproj : ∀ C : ContactRegularComponentCover.RegularComponent
        Omega G T H,
      ActualCurveZeroCount.ProjectionsFiniteSeparable Omega C.1}

/-- .
 -/
theorem flagProjectionPositivity_of_degree_directional
    (D : NestedFlagProjectionData hseparator hproj)
    (hSpos : 0 < G.degreeOf 1) (hSchar : G.degreeOf 1 < p)
    (hdirectional : MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C D.mu * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    FlagProjectionPositivity D G := by
  have huz := flag_u_z_outer_positive p D.lam D.mu G hSpos hSchar
  exact ⟨huz.1,
    flag_v_outer_positive_of_directional D.lam D.mu G hdirectional,
    huz.2⟩

/-- .
 -/
theorem flagProjectionPositivity_of_derivatives
    (D : NestedFlagProjectionData hseparator hproj)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hdirectional : MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C D.mu * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    FlagProjectionPositivity D G := by
  have huz := flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv
  exact ⟨huz.1,
    flag_v_outer_positive_of_directional D.lam D.mu G hdirectional,
    huz.2⟩

end Characteristic

end

end ProximityPrize.SubmissionLower.ContactFlagProjectionPositivity6543Research
