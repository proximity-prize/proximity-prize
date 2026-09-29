import ProximityPrize.SubmissionLower.MovingSourceCarrierField6814

/-! Assemble the actual source alternative and the standard small-degree
projection suppliers into the regular moving-family endpoint. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePacket6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN002 RCN003 RCN037 RCN042 RCN046 RCN084 RCN095 RCN135 RCN136 RCN234 RCN156 RCN264 RCN341
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierField6814 MovingSourceGeometricBudget6814

theorem exists_projection_data
    {E : Type} [Field E] [IsAlgClosed E]
    (G H R : MvPolynomial (Fin 3) E) (hG : Irreducible G) (hproper : ¬G∣H)
    (p q : FlagDegree) (hp : PolynomialInFlag p G) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP E c] (hdeg : p.zOnly+p.yz+p.all<c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c) :
    ∃ base : ∀ C : RegularComponent E G H R, SeparableLiteralCoordinate C.1,
      (∀ C : RegularComponent E G H R, LiteralProjectionGate C 0) ∧
      (∀ C : RegularComponent E G H R, LiteralProjectionGate C 2) := by
  have hgate (C : RegularComponent E G H R) (i : Fin 3)
      (hi : Transcendental E (coordinate E C.1 i)) := by
    have hgdeg (j : Fin 3) : G.degreeOf j≤p.zOnly+p.yz+p.all := degreeOf_le_flag_total G p hp j
    have hhdeg (j : Fin 3) : H.degreeOf j≤q.zOnly+q.yz+q.all := degreeOf_le_flag_total H q hq j
    have hprod (u v : Fin 3) : H.degreeOf u*G.degreeOf v+G.degreeOf u*H.degreeOf v < c := by
      calc
        _ ≤ (q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
            (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) :=
          Nat.add_le_add (Nat.mul_le_mul (hhdeg u) (hgdeg v))
            (Nat.mul_le_mul (hgdeg u) (hhdeg v))
        _ = 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) := by ring
        _ < c := hmix
    apply finite_separable_at_of_original_coordinate_gate E C.1 i hi c G H hG
      (regularComponent_G_mem E G H R C) (regularComponent_T_mem E G H R C)
      hproper (fun j => (hgdeg j).trans_lt hdeg)
    have hi3 : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [RCN001.coordinateMixedDegree_zero]; exact hprod 1 2
    · rw [RCN001.coordinateMixedDegree_one]; exact hprod 0 2
    · rw [RCN001.coordinateMixedDegree_two]; exact hprod 0 1
  refine ⟨fun C => Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
    (regularComponent_ne_point E G H R C) (hgate C 0) (hgate C 2)),?_,?_⟩
  · exact fun C => hgate C 0
  · exact fun C => hgate C 2

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)

/-- No desired count, source dimension, faithful map, helper identity, or
projection-data supplier is assumed. This is the regular simple-quadratic
branch; its ownership/coverage hypotheses remain visible. -/
theorem exists_helper_or_regular_projection
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJU : 9≤U) (hUT : U≤T) (hT : T≤1700)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (G : MvPolynomial (Fin 3) OmegaT) (hcarrier : G∣surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬G∣regularEquation F quadratic A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (p q : FlagDegree) (hp : PolynomialInFlag p G)
    (hq : PolynomialInFlag q (regularEquation F quadratic A))
    (hdeg : p.zOnly+p.yz+p.all<2130706433)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<2130706433) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ base : ∀ C : MovingFamily F G quadratic A, SeparableLiteralCoordinate C.1,
        Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩) := by
  rcases exists_helper_or_global_pair nodes u0 u1 hN J hJi hmid hB hJdegree U T hJbounds hT
    F hFT r y t hr hy ht hF hpos hsmall hroot with hhelp | hpair
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hJdiv,hQdiv,hQbounds,hQdegree⟩ := hpair
  obtain ⟨base,hY,hZ⟩ := exists_projection_data G (regularEquation F quadratic A)
    (regularDenominator F A) hG hproper p q hp hq 2130706433 hdeg hmix
  exact Or.inr ⟨base,exists_regular_moving_projection_family J Q hJi.ne_zero hQ hcop
    hJdegree hQdegree U T hJU hUT hJbounds hQbounds F hJdiv hQdiv
    quadratic A hden hquadratic hA G hcarrier base hY hZ hderiv⟩

#print axioms exists_projection_data
#print axioms exists_helper_or_regular_projection
end
end ProximityPrize.SubmissionLower.MovingSourcePacket6814
