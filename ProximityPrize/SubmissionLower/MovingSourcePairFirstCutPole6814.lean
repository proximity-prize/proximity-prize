import ProximityPrize.SubmissionLower.MovingSourceExtendedMovingDegrees6814
import ProximityPrize.SubmissionLower.HFreeDir6813

/-! Directional first-cut mass uses the actual moving pole budget directly.
No source-flag bound is silently substituted for the new pair degree sum. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairFirstCutPole6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators WithZero
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open ActualFirstCutPole6807 HFreeDir6813
local notation "w" => RCN326.w

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem first_pole_mass_of_moving_budget
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (hH : surfaceMap phi (polyH K F)∉C)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hbudget : HFreeSliceBudgetCap phi F C C0 (HFree6812.infCap d))
    (scale CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu∈W, flagPole nu.val (coordinate E C) (hfreeFlagDir d r v z C0))≤(CX : ℤ))
    (hMoving : ∀ W : Finset (Place E (CoordinateField E C)),
      (scale : ℤ)*(∑ nu∈W, RCN064.movingPoleTarget C (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) nu)≤(CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((3*scale : ℕ) : ℤ)*(∑ nu∈W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
      (scale : ℤ)*(CX : ℤ)+((4*(w+1) : ℕ) : ℤ)*(CV : ℤ) := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  let L := CoordinateField E C
  let ev := SecondJetComponentRoots.coefficientMap phi C
  let H := ev (polyH K F)
  let sigma := ev (polyG K F)/H
  let theta := fun nu : Place E L =>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag + RCN187.poleOrder nu.val sigma)
  let Hf : FlagDegree := ⟨z,v,r-1⟩
  have hHne : H ≠ 0 := by
    intro hz
    apply hH
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mp hz
  let Pl := RCN026.placesFor E L H hHne
  set W' := W ∪ Pl with hW'
  have hsource : (scale : ℤ)*(∑ nu ∈ W', theta nu)≤(CV : ℤ) := by
    have hh := hMoving W'
    simpa only [theta,sigma,H,ev,RCN064.movingPoleTarget,RCN204.flagPole_unitAll,
      RCN204.flagPole_unitYZ,SecondJetComponentRoots.coefficientMap,RCN064.movingRatio,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hh
  have htarget : (∑ nu ∈ W', RCN064.movingPoleTarget C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu) = ∑ nu ∈ W', theta nu := by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta, RCN204.flagPole_unitAll, RCN204.flagPole_unitYZ]
    rfl
  -- zeros of `H` are bounded by its poles, hence by its flag
  have hHF := (BoundaryTailAlgebra.boundary_surfaceMap_flags phi F r v z (by omega) (by omega)
    hR hYR hAll).1
  have hpoleH (nu : Place E L) :
      RCN346.poleOrder E L nu H ≤ flagPole nu.val (coordinate E C) Hf := by
    apply pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E L)
      (RCN344.constant_value_le_one E L nu) (coordinate E C) Hf _ hHF
    simpa only [H, ev, SecondJetComponentRoots.coefficientMap,
      coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hzero : (∑ nu ∈ W', RCN026.zeroOrder E L nu H) ≤
      ∑ nu ∈ W', flagPole nu.val (coordinate E C) Hf := by
    have hout : ∀ nu ∈ W'.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H = 0 := by
      intro nu hnu
      have hno : RCN026.order E L nu H = 0 := by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.placesFor_covers E L H hHne nu hne)
      simp only [RCN026.zeroOrder, hno, max_self]
    calc
      _ = (∑ nu ∈ W'.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H) +
          ∑ nu ∈ W'.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H :=
        (Finset.sum_filter_add_sum_filter_not W' _ _).symm
      _ = ∑ nu ∈ W'.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H := by
        rw [Finset.sum_eq_zero hout, add_zero]
      _ ≤ ∑ nu ∈ Pl, RCN026.zeroOrder E L nu H :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu => (Finset.mem_filter.mp hnu).2)
          (fun nu _ _ => RCN026.zeroOrder_nonneg E L nu H)
      _ = ∑ nu ∈ Pl, RCN346.poleOrder E L nu H := RCN026.sum_placesFor_zero_eq_pole E L H hHne
      _ ≤ ∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf := Finset.sum_le_sum (fun nu _ => hpoleH nu)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) Hf)
  -- `2•flag(H) = cusp + cap`, and the cap is dominated by `infCap d`
  have hcusp : 2 * (∑ nu ∈ W', flagPole nu.val (coordinate E C) Hf) ≤
      (∑ nu ∈ W', flagPole nu.val (coordinate E C) (cuspFlag d r v z)) +
        ∑ nu ∈ W', flagPole nu.val (coordinate E C) (HFree6812.infCap d) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun nu _ => ?_
    have e1 := congrArg (flagPole nu.val (coordinate E C)) (cusp_add_cap d r v z hr hv)
    rw [RCN204.flagPole_add, RCN204.flagPole_nsmul] at e1
    have e2 := capFlag_pole_le nu.val (coordinate E C) d r hr
    push_cast at e1
    linarith
  have hX := hXbudget W'
  simp only [hfreeFlagDir, RCN204.flagPole_add, RCN204.flagPole_nsmul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hX
  have hb := hbudget.pole_le W'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hb
  rw [htarget] at hb
  have hWW : (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      ∑ nu ∈ W', RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun nu _ _ => le_max_left _ _)
  push_cast at hb hsource hX ⊢
  have hk : (0 : ℤ) ≤ (scale : ℤ) := by positivity
  have hw : (0 : ℤ) ≤ (w : ℤ)+1 := by positivity
  have e0 := mul_le_mul_of_nonneg_left (show
    2 * (∑ nu ∈ W', RCN026.zeroOrder E L nu H) ≤
      (∑ nu ∈ W', flagPole nu.val (coordinate E C) (cuspFlag d r v z)) +
        ∑ nu ∈ W', flagPole nu.val (coordinate E C) (HFree6812.infCap d) by linarith) hw
  have hb' : 3 * (∑ nu ∈ W', RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      4 * ((w : ℤ)+1) * (∑ nu ∈ W', theta nu) + (CX : ℤ) := by
    nlinarith
  have e1 := mul_le_mul_of_nonneg_left hb' hk
  have e2 := mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num : (0 : ℤ) ≤ 4) hw)
  have e3 := mul_le_mul_of_nonneg_left hWW (mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) hk)
  nlinarith

section Stage
variable {I T : Type} [Fintype T] [Nonempty T] [Algebra (GenericField K) E]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Omega" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "phiE" => RingHom.comp (algebraMap Omega E) (polynomialEmbedding K)

/-- Actual first-tail multiplicities, bounded using the constructed
moving budget on the prime slice. This preserves the directional
infinity saving in the submitted architecture. -/
theorem first_cut_on_prime_slice_of_moving_budget
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Omega (old i).1 →ₐ[Omega] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D≤RingHom.ker (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Omega E S.G∈D)
    (hisolated : scalarPolynomialMap Omega E (globalTailCut (polynomialEmbedding K) S.F (w+1))∉D)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree)
    (hbudget : surfaceMap phiE S.F∈D → surfaceMap phiE (polyH K S.F)∉D →
      HFreeSliceBudgetCap phiE S.F D C0 (HFree6812.infCap d))
    (moving : RCN199.MovingPoleBudget D (surfaceMap phiE (polyH K S.F)) (surfaceMap phiE (polyG K S.F)))
    (CX : ℕ)
    (hX : ∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu∈W, flagPole nu.val (coordinate E D) (hfreeFlagDir d r v z C0))≤(CX : ℤ)) :
    3*(∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i))≤
      CX+4*(w+1)*moving.movingCost := by
  apply ActualWeightedFirstSlice6807.first_cut_on_prime_slice_of S hproper old emb hinj D sep
    hpoint hcarrier hisolated (2*w-1) 3 (CX+4*(w+1)*moving.movingCost)
  intro hFd hHd _ W
  have hh := first_pole_mass_of_moving_budget phiE S.F D sep hHd d r v z hr hv hR hYR hAll
    C0 (hbudget hFd hHd) 1 CX moving.movingCost hX
    (fun U => by simpa only [Nat.cast_one,one_mul] using moving.movingPole U) W
  simpa only [Nat.mul_one,Nat.cast_one,one_mul,Nat.cast_add,Nat.cast_mul] using hh

end Stage

#print axioms first_pole_mass_of_moving_budget
#print axioms first_cut_on_prime_slice_of_moving_budget
end
end ProximityPrize.SubmissionLower.MovingSourcePairFirstCutPole6814
