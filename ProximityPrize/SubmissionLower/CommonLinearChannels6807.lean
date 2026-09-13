import ProximityPrize.SubmissionLower.ActualGenericChannel6807
/-
UNCOMPILED. Structural common-linear-coordinate data for the SAME original unit
family. These are equalities of rational functions, not requested cost bounds.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.CommonLinearChannels6807
open scoped Classical BigOperators
open RCN002 RCN022 RCN030 RCN037 RCN038 RCN040 RCN042 RCN046 RCN093
open RCN095 RCN207 RCN237 RCN264 RCN340 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 40000
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
local notation "Poly" => MvPolynomial (Fin 3) Ω

def linearZ : Poly := MvPolynomial.X 2
def linearU (lam : Ω) : Poly := MvPolynomial.X 0 + MvPolynomial.C lam * MvPolynomial.X 2
def linearA (mu lam : Ω) : Poly := MvPolynomial.X 1 +
  MvPolynomial.C mu * MvPolynomial.X 0 + MvPolynomial.C (mu*lam) * MvPolynomial.X 2

private theorem inFlag_X (i : Fin 3) (q : FlagDegree)
    (hi : InFlag q (Finsupp.single i 1)) : PolynomialInFlag q (MvPolynomial.X i : Poly) := by
  intro e he
  have hh : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
private theorem inFlag_add_poly {q : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag q A) (hB : PolynomialInFlag q B) : PolynomialInFlag q (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
private theorem inFlag_const_mul {q : FlagDegree} {A : Poly}
    (c : Ω) (hA : PolynomialInFlag q A) : PolynomialInFlag q (MvPolynomial.C c * A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_in_flag : PolynomialInFlag unitZFlag (linearZ : Poly) := by
  exact inFlag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_in_flag (lam : Ω) : PolynomialInFlag unitYZFlag (linearU lam) := by
  exact inFlag_add_poly
    (inFlag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (inFlag_const_mul lam (inFlag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_in_flag (mu lam : Ω) : PolynomialInFlag unitAllFlag (linearA mu lam) := by
  exact inFlag_add_poly (inFlag_add_poly
    (inFlag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (inFlag_const_mul mu (inFlag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (inFlag_const_mul (mu*lam) (inFlag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem eval_linearZ (P : Ideal Poly) [P.IsPrime] :
    coordinateEvaluation Ω P (linearZ : Poly) = coordinate Ω P 2 := rfl
theorem eval_linearU (P : Ideal Poly) [P.IsPrime] (lam : Ω) :
    coordinateEvaluation Ω P (linearU lam) = affineU Ω P lam := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearU,affineU,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]
theorem eval_linearA (P : Ideal Poly) [P.IsPrime] (mu lam : Ω) :
    coordinateEvaluation Ω P (linearA mu lam) = affineV Ω P mu (mu*lam) := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearA,affineV,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]

theorem flagMixed_swap_last (p q r : FlagDegree) : flagMixed p q r = flagMixed p r q := by
  simp only [flagMixed]
  ring

variable {G T H : MvPolynomial (Fin 3) Ω} {p q : FlagDegree}
  {base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1}

/-- A generic AdaptiveUnitProjectionFamily alone does NOT imply this structure.
The constructor below is for the original common activeNestedUnitFamily only. -/
structure CommonLinearValues
    (unit : AdaptiveUnitProjectionFamily (Omega := Ω) (G := G) (T := T) (H := H) base p q) where
  lam : Ω
  mu : Ω
  yzValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 lam
  allValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) = affineV Ω C.1 mu (mu*lam)

theorem common_z_value (unit : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
      coordinateEvaluation Ω C.1 (linearZ : Poly) := unit.zValue C

theorem common_u_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
      coordinateEvaluation Ω C.1 (linearU D.lam) := by
  rw [eval_linearU]
  exact D.yzValue C

theorem common_a_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
      coordinateEvaluation Ω C.1 (linearA D.mu D.lam) := by
  rw [eval_linearA]
  exact D.allValue C

/-- The common parameters and the projections are the old constructor's actual
ones. In particular no minimization over separately chosen families is made. -/
def of_active_nested
    (base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (hactive : ∀ C : RegularComponent Ω G T H,
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2) ≠ 0)
    (hZ : ∀ C : RegularComponent Ω G T H, LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (D : AdaptiveNestedProjectionDataActive (Omega := Ω) (G := G) (T := T) (H := H)
      base hactive hSderiv)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p) (hTsupport : T.support ⊆ flagSupport q) :
    CommonLinearValues (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport) where
  lam := D.lam
  mu := D.mu
  yzValue := by
    intro C
    change coordinateValue Ω (CoordinateField Ω C.1)
      (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
    exact coordinateOfGate_value _ _
  allValue := by
    intro C
    change (elementEmbedding Ω (CoordinateField Ω C.1)
      (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
    exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _

/-- Congruent-cut transport preserves the actual common rational functions,
not just their three numeric costs. The old and new component primes are defeq. -/
def of_congruent_cut {T' : Poly} (h : G ∣ T-T')
    {base' : ∀ C : RegularComponent Ω G T' H, SeparableLiteralCoordinate C.1}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (newBase : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (D : CommonLinearValues U) :
    CommonLinearValues (LocatorHybridTransportC2.unitFamilyOfCongruentCut h U newBase) where
  lam := D.lam
  mu := D.mu
  yzValue C := D.yzValue (RCN066.regularComponentEquiv h C)
  allValue C := D.allValue (RCN066.regularComponentEquiv h C)

end
end ProximityPrize.SubmissionLower.CommonLinearChannels6807
