import ProximityPrize.SubmissionLower.MovingFiberProjection6811

/-! Feed the source-sensitive projection bounds into the actual native curve
budget. This bounds a pure polynomial cut on the moving fiber and charges no
multiplicity-weighted moving-degree term that the consumer does not need.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
open scoped Classical BigOperators
open RCN002 RCN022 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN093 RCN095 RCN135 RCN136 RCN207
open RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 40000
variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance : DecidableEq Ω := Classical.decEq Ω
local notation "Poly3" => MvPolynomial (Fin 3) Ω

def linearZ : Poly3 := MvPolynomial.X 2
def linearU (a : Ω) : Poly3 := MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 2
def linearA (b a : Ω) : Poly3 := MvPolynomial.X 1 + MvPolynomial.C b * MvPolynomial.X 0 +
  MvPolynomial.C (b*a) * MvPolynomial.X 2

omit [IsAlgClosed Ω] in
private theorem flag_X (i : Fin 3) (p : FlagDegree)
    (hi : InFlag p (Finsupp.single i 1)) : PolynomialInFlag p (MvPolynomial.X i : Poly3) := by
  intro e he
  have : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
omit [IsAlgClosed Ω] in
private theorem flag_add {p : FlagDegree} {A B : Poly3}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag p B) : PolynomialInFlag p (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
omit [IsAlgClosed Ω] in
private theorem flag_scale {p : FlagDegree} {A : Poly3} (c : Ω)
    (hA : PolynomialInFlag p A) : PolynomialInFlag p (MvPolynomial.C c*A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_flag : PolynomialInFlag unitZFlag (linearZ : Poly3) :=
  flag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_flag (a : Ω) : PolynomialInFlag unitYZFlag (linearU a) :=
  flag_add (flag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (flag_scale a (flag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_flag (b a : Ω) : PolynomialInFlag unitAllFlag (linearA b a) :=
  flag_add (flag_add (flag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (flag_scale b (flag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (flag_scale (b*a) (flag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem exists_common_native_unit {G N R : Poly3} (p q : FlagDegree)
    (base : ∀ C : RegularComponent Ω G N R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hG : Irreducible G) (hproper : ¬ G ∣ N)
    (hGflag : PolynomialInFlag p G) (hNflag : PolynomialInFlag q N) :
    ∃ (unit : AdaptiveUnitProjectionFamily base p q) (a b : Ω),
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
        coordinateEvaluation Ω C.1 linearZ) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
        coordinateEvaluation Ω C.1 (linearU a)) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        coordinateEvaluation Ω C.1 (linearA b a)) := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  let unit := adaptiveUnitProjectionFamily_of_nested p q base hY hZ hderiv D hG hproper
    ((support_subset_flagSupport_iff _ _).mpr hGflag) ((support_subset_flagSupport_iff _ _).mpr hNflag)
  refine ⟨unit,D.lam,D.mu,?_,?_,?_⟩
  · intro C
    exact unit.zValue C
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 D.lam := by
      change coordinateValue Ω (CoordinateField Ω C.1)
        (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
      exact coordinateOfGate_value _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearU,affineU,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        affineV Ω C.1 D.mu (D.mu*D.lam) := by
      change (elementEmbedding Ω (CoordinateField Ω C.1)
        (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
      exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearA,affineV,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]

#print axioms exists_common_native_unit
end
end ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
