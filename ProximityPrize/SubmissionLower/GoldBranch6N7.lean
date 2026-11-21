import ProximityPrize.SubmissionLower.GoldBranch6N5
import ProximityPrize.SubmissionLower.GoldBranch6N6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32 Row)
open K1_13_7 (LowerPoint pointIdeal pairIdeal tripleIdeal localColength)
open P3_6 (commonBox resultantBox fatOrder divisorOrder isolatedOrder taylorLength
  linearChart incidenceGap physicalDegree)
abbrev curveLength : ℕ := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
def divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
theorem divisorBox_eq : divisorBox = ⟨22994, 7683, 0⟩ := by
  have hb : commonBox.b + resultantBox.b / divisorOrder = 22994 := by decide
  have hj : commonBox.j + resultantBox.j / divisorOrder = 7683 := by decide
  unfold divisorBox
  rw [hb, hj]
end
end P3_6_7
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32 atJet)
open K1_13_6 (GeoJets toGeneric separant cycleLength intersectionIdeal Invariant)
open K1_13_7 (LowerCaps genericRow)
open K1_13_7_2 (evalTrajectory LiftedSurface lowerFlow liftLower)
open P3_6 (taylorLength physicalDegree)
open P3_6_7 (fatChart divisorBox)
structure ReducedCut (f : Row 4) (D q : Row 3) : Prop where
  ne_zero : q ≠ 0
  divides : q ∣ D
  caps : LowerCaps q divisorBox.b divisorBox.j
  reduced : Squarefree (genericRow q)
  proper : IsRelPrime (toGeneric f) (toGeneric (liftLower q))
  roots : ∀ S : Geom[X], atJet D S = 0 → atJet q S = 0
  flow_box : InBox (shape (lowerFlow q)) ⟨divisorBox.b, divisorBox.j + 1, 1⟩
  simple : ∀ surface, (h : LiftedSurface f q surface) → surface.height = 2 ∧
    cycleLength (intersectionIdeal f (liftLower q)) surface h.minimal.isPrime = 1
  invariant : ∀ surface, LiftedSurface f q surface → toGeneric (lowerFlow q) ∈ surface → Invariant f surface
def cutBox (x : Shape) : Shape :=
  let h := fatChart x
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P3_6_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : L[X]),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
def universalPolynomial : CoeffRing[X] :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val
def universalEval (f : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f
def coefficientPointIdeal (S : Geom[X]) : Ideal CoeffRing :=
  RingHom.ker (MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val))
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
def IntegratedMark (f : Row 4) (S : Geom[X]) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S
end
end P3_6_7_2
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_2_2 (stride raw topLinear denominator numerator hasseNumerator)
open K1_13_7_1 (weight_const_mul_le top_le_index shape_chamber Chamber)
open K1_13_1 (indexDegree_eq)
open private raw_false raw_true_compare from ProximityPrize.SubmissionLower.Fast070
open private raw_bound sep_pow_bound from ProximityPrize.SubmissionLower.Fast070
open private specializes topLinear_regular from ProximityPrize.SubmissionLower.Fast070
local notation "W" => MvPolynomial.weightedTotalDegree
end
end P3_6_7_2
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace P3_6_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7
open K1_13_7_2_4 K1_13_7_2_4_2
open P3_6 (physicalDegree anchorCutoff)
open private intDerivation coeffDeriv coeffDeriv_zero_of_shift zero_of_stationary_eval
  rowTrajectory rowTrajectory_stationary eval_chartTrajectory from ProximityPrize.SubmissionLower.Fast066
open private sum_monomial_eq_of_coeffs from ProximityPrize.SubmissionLower.Fast066
open private trajectory_at_component component_ne_zero from ProximityPrize.SubmissionLower.Fast066
private theorem length_le : P3_6.taylorLength ≤ K1_13.taylorLength := by decide
private theorem numerator_mem_from {f : Row 4} {P : Ideal GeoJets}
    (hinv : Invariant f P) (hmem : toGeneric (P3_6_6.membershipTest f) ∈ P)
    {n : ℕ} (hn : P3_6.taylorLength ≤ n) : toGeneric (jetNumerator f n) ∈ P := by
  induction n, hn using Nat.le_induction with
  | base => exact hmem
  | succ n _ ih =>
    rw [jetNumerator, clearedStep]
    simp only [toGeneric, map_sub, map_mul]
    exact P.sub_mem (P.mul_mem_left _ (hinv _ ih)) (P.mul_mem_left _ ih)
private theorem chart_degree {f : Row 4} {P : Ideal GeoJets}
    (hinv : Invariant f P) (hmem : toGeneric (P3_6_6.membershipTest f) ∈ P) :
    (chartPolynomial f P).natDegree ≤ physicalDegree := by
  rw [chartPolynomial, natDegree_taylor]
  apply natDegree_sum_le_of_forall_le
  intro i _
  by_cases hi : i.val < P3_6.taylorLength
  · exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ hi)
  · have htail := numerator_mem_from hinv hmem (Nat.le_of_not_gt hi)
    have hi4 : ¬i.val < 4 := fun h => hi (h.trans (by decide : 4 < P3_6.taylorLength))
    rw [chartJet, dite_eq_right hi4, onChart_zero (f := f) htail, mul_zero, monomial_zero_right,
      natDegree_zero]
    exact Nat.zero_le _
private theorem row_degree {R : Type*} [CommRing R]
    (k : Geom →+* R) (Q : Row 4) (U : R[X]) {B : ℕ}
    (hQ : P3_6.TrueWeightLE Q B) (hU : U.natDegree ≤ physicalDegree) :
    (rowTrajectory k Q U).natDegree ≤ B := by
  classical
  unfold rowTrajectory
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  refine (natDegree_mul_le_of_le Polynomial.natDegree_map_le ?_).trans (hQ m hm)
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  change _ ≤ (physicalDegree - i.val) * m i
  rw [Nat.mul_comm]
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans (Nat.sub_le_sub_right hU _))
private theorem solves_fresh {f : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) (hw : P3_6.TrueWeightLE f anchorCutoff)
    (hf : toGeneric f ∈ P) (hinv : Invariant f P)
    (hmem : toGeneric (P3_6_6.membershipTest f) ∈ P)
    (δ : Derivation Geom (ChartRing f P) (ChartRing f P)) (hδ : FollowsFlow f P δ) :
    trajectory (componentConstants P) f ((chartPolynomial f P).map (genericLift f P hs)) = 0 := by
  let U := chartPolynomial f P
  let x := chartCenter f P
  let k := chartConstants f P
  let V := rowTrajectory k f U
  let d := intDerivation (R := ChartRing f P) δ.toLinearMap.toAddMonoidHom δ.map_one_eq_zero
    (fun a b => by
      change δ (a * b) = a * δ b + b * δ a
      simpa only [smul_eq_mul] using δ.leibniz a b)
  have hx : d x = 1 := chartCenter_deriv hδ
  have hc (a : Geom) : d (k a) = 0 := chartConstants_deriv hδ a
  have hU : coeffDeriv d U = 0 :=
    coeffDeriv_zero_of_shift d x hx U
      (chartTaylor_shift hδ (numerator_mem_from hinv hmem length_le))
  have he : V.eval x = 0 := (eval_chartTrajectory f P f).trans (onChart_zero hf)
  have hd : V.natDegree ≤ anchorCutoff := row_degree k f U hw (chart_degree hinv hmem)
  have hz : V = 0 := zero_of_stationary_eval d x hx V
    (rowTrajectory_stationary d k hc f U hU) he (fun n hn => chart_factorial_unit f P
      (hn.trans_lt (hd.trans_lt (by decide : anchorCutoff < K1.p))))
  let φ := genericLift f P hs
  have hk : φ.comp (chartConstants f P) = componentConstants P := by
    apply RingHom.ext
    intro a
    simpa only [RingHom.comp_apply, chartConstants, componentConstants, geomConstants,
      toGeneric, MvPolynomial.map_C] using
      genericLift_onChart f P hs (MvPolynomial.C (C a))
  have hm : V.map φ = trajectory (componentConstants P) f (U.map φ) := by
    change (mapRingHom φ) (MvPolynomial.eval₂ (mapRingHom (chartConstants f P))
      (fun i : Fin 4 => hasseDeriv i.val U) f) = _
    rw [MvPolynomial.hom_eval₂ f (mapRingHom (chartConstants f P)) (mapRingHom φ)
      (fun i : Fin 4 => hasseDeriv i.val U), mapRingHom_comp, hk, trajectory]
    simp only [coe_mapRingHom, hasseDeriv_map]
  rw [← hm, hz, Polynomial.map_zero]
private def retunedEval {L : Type} [Field L] (k : Geom →+* L) (U : L[X]) :
    P3_6_7_2.CoeffRing →+* L :=
  MvPolynomial.eval₂Hom k (fun i : Fin P3_6.taylorLength => U.coeff i.val)
private theorem map_universal {L : Type} [Field L] (k : Geom →+* L) (U : L[X])
    (hd : U.natDegree < P3_6.taylorLength) (Q : Row 4) :
    (P3_6_7_2.universalEval Q).map (retunedEval k U) = trajectory k Q U := by
  let e := retunedEval k U
  have hU : P3_6_7_2.universalPolynomial.map e = U := by
    rw [P3_6_7_2.universalPolynomial, Polynomial.map_sum]
    simp only [C_mul_X_pow_eq_monomial, map_monomial, e, retunedEval, MvPolynomial.eval₂Hom_X']
    exact sum_monomial_eq_of_coeffs _ U hd (fun _ => rfl)
  have hk : e.comp MvPolynomial.C = k := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  change (mapRingHom e) (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C)
    (fun i : Fin 4 => hasseDeriv i.val P3_6_7_2.universalPolynomial) Q) = trajectory k Q U
  rw [MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp, hk]
  simp only [Polynomial.coe_mapRingHom, ← hasseDeriv_map, hU, trajectory]
end
end P3_6_7_2_2
end
section
set_option autoImplicit false
namespace P3_6_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open P3_6 (taylorLength)
open P3_6_7_2 (CoeffRing FatTaylor)
abbrev CoeffIdeal := Ideal CoeffRing
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) GeoField
def jetLinear {k : Type*} [Field k] (a : k) (i : ℕ) :
    MvPolynomial (Fin taylorLength) k :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C ((j.val.choose i : k) * a ^ (j.val - i)) * MvPolynomial.X j
def extendIdeal (A : CoeffIdeal) : Ideal FreshCoeffRing :=
  A.map (MvPolynomial.map geomConstants)
def freshJetMap : GeoJets →+* FreshCoeffRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => jetLinear genericArgument i.val)
def freshImage (A : CoeffIdeal) : JetIdeal :=
  (extendIdeal A).comap freshJetMap
structure FreshChart (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal) : Prop where
  extended_prime : (extendIdeal A).IsPrime
  dimension_eq : dimension (freshImage A) = dimension A
  factor : toGeneric f ∈ freshImage A
  regular : toGeneric (separant f) ∉ freshImage A
  test : toGeneric T.test ∈ freshImage A
  denom : toGeneric T.denom ∉ freshImage A
  recovers : ∀ i, MvPolynomial.X i * freshJetMap (toGeneric T.denom) -
    freshJetMap (toGeneric (T.numer i)) ∈ extendIdeal A
end
end P3_6_7_2_3
end
section
namespace P3_6_7_3
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open P3_6 (physicalDegree)
section
open private K1_13_7_5_2.denominator from ProximityPrize.SubmissionLower.Fast072
open private numerator P0_9_7_3_1.numerator_bound denominator_bound P0_9_7_3_1.coefficients_recover from ProximityPrize.SubmissionLower.PortLow7
local notation "W" => MvPolynomial.weightedTotalDegree
end
section
open private K1_13_7_1.denominator from ProximityPrize.SubmissionLower.Fast059
open private coefficientNumerator coefficients_fit P0_9_7_3_2.coefficients_recover from ProximityPrize.SubmissionLower.PortLow7
end
end
end P3_6_7_3
end
