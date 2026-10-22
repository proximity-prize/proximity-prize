import ProximityPrize.SubmissionLower.MergedInfra6815_36
import ProximityPrize.SubmissionLower.HFreeDir6813
import ProximityPrize.SubmissionLower.MergedInfra6815_31
set_option Elab.async false
section MergedPart0
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

end Stage

end
end ProximityPrize.SubmissionLower.MovingSourcePairFirstCutPole6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceSlicePrimeFamily6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open scoped Classical
open MvPolynomial RCN084 RCN137 RCN264 WeightedSliceAssignment6807

variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E

theorem derivative_mem_of_two_factors (F G H : Poly) (P : Ideal Poly)
    (hprod : G*H∣F) (hG : G∈P) (hH : H∈P) : pderiv (1 : Fin 3) F∈P := by
  obtain ⟨Q,rfl⟩ := hprod
  rw [pderiv_mul,pderiv_mul]
  exact P.add_mem
    (P.mul_mem_right Q (P.add_mem (P.mul_mem_left _ hH) (P.mul_mem_right _ hG)))
    (P.mul_mem_right _ (P.mul_mem_right H hG))

theorem slice_prime_injective (F N R : Poly) (hFne : F≠0)
    (hR : R∈Ideal.span ({F,pderiv (1 : Fin 3) F} : Set Poly)) :
    Function.Injective (fun a : SliceComponent F N R => a.2.1) := by
  classical
  rintro ⟨ga,Ca⟩ ⟨gb,Cb⟩ he
  change Ca.1=Cb.1 at he
  have hga := activeFactors_spec F N ga
  have hgb := activeFactors_spec F N gb
  have hgeq : ga=gb := by
    apply Subtype.ext
    by_contra hne
    have hsubset : ({ga.1,gb.1} : Finset Poly)⊆normalizedFactorSet F := by
      intro P0 hP0
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP0
      rcases hP0 with rfl | rfl
      · exact (Finset.mem_filter.mp ga.2).1
      · exact (Finset.mem_filter.mp gb.2).1
    have hprod : ga.1*gb.1∣F := by
      have hh := (Finset.prod_dvd_prod_of_subset {ga.1,gb.1} (normalizedFactorSet F) id hsubset).trans
        (normalizedFactorSet_product_dvd F hFne)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have ha : ga.1∈Ca.1 := regularComponent_G_mem E ga.1 N R Ca
    have hb : gb.1∈Ca.1 := by rw [he]; exact regularComponent_G_mem E gb.1 N R Cb
    have hF : F∈Ca.1 := Ca.1.mem_of_dvd hga.2.1 ha
    have hd := derivative_mem_of_two_factors F ga.1 gb.1 Ca.1 hprod ha hb
    have hspan : Ideal.span ({F,pderiv (1 : Fin 3) F} : Set Poly)≤Ca.1 := by
      apply Ideal.span_le.mpr
      intro P0 hP0
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP0
      rcases hP0 with rfl | rfl
      · exact hF
      · exact hd
    exact regularComponent_H_not_mem E ga.1 N R Ca (hspan hR)
  cases hgeq
  exact congrArg (fun C : RegularComponent E ga.1 N R => (⟨ga,C⟩ : SliceComponent F N R)) (Subtype.ext he)

end
end ProximityPrize.SubmissionLower.MovingSourceSlicePrimeFamily6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourceIndexedMovingCoordinates6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators WithZero
open RCN002 RCN022 RCN064 RCN095 RCN187 RCN207 RCN208 RCN212 RCN264 RCN295 RCN341 RCN344
open RCN184 RCN133 RCN114 RCN005 RCN006 RCN044 RCN037 RCN042 RCN035

variable {E I : Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" => MvPolynomial (Fin 3) E

private theorem field_eval (P : Ideal Poly) [P.IsPrime] (A : Poly) :
    MvPolynomial.eval₂Hom (algebraMap E (CoordinateField E P)) (coordinate E P) A=coordinateEvaluation E P A := by
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm

theorem exists_indexed_moving_coordinates
    (P : I → Ideal Poly) [∀ i,(P i).IsPrime]
    (base : ∀ i, SeparableLiteralCoordinate (P i)) (H G : Poly) :
    ∃ (Q A : Poly) (projection : ∀ i, SeparableCoordinate E (CoordinateField E (P i))),
      PolynomialInFlag (2 • unitAllFlag) Q ∧ PolynomialInFlag unitYZFlag A ∧
      ∀ i, A∉P i ∧
        SeparableCoordinate.value E (CoordinateField E (P i)) (projection i)=movingValue (P i) H G Q A ∧
        ∀ nu : RCN026.Place E (CoordinateField E (P i)),
          poleOrder nu.val (SeparableCoordinate.value E (CoordinateField E (P i)) (projection i))=
            movingPoleTarget (P i) H G nu := by
  obtain ⟨c,hc⟩ := exists_common_coefficients (K:=E)
    (fun i => CoordinateField E (P i)) (fun i => coordinate E (P i))
    (fun i => movingRatio (P i) H G) (fun i => (base i).index)
    (fun i => base_differential_ne_zero (base i))
    (fun i => movingRelevantPlaces (base i) (movingRatio (P i) H G))
  let Q := quadraticPolynomial c
  let A := linearPolynomial c
  have hJ (i : I) :
      coefficientEvaluation (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) movingSupport c=
        movingValue (P i) H G Q A := by
    rw [coefficientEvaluation_eq,field_eval,field_eval]
    simp only [movingValue,movingRatio,Q,A,mul_div_assoc]
  have hA (i : I) : coefficientEvaluation (coordinate E (P i)) linearSupport (restrictU c)=
      coordinateEvaluation E (P i) A := field_eval (P i) A
  have hx (i : I) := hc i
  simp only [hA,hJ] at hx
  have hnot (i : I) : A∉P i := by
    intro hh
    exact (hx i).1 ((SecondJetComponentRoots.evaluation_zero_iff (P i) A).mpr hh)
  have gate (i : I) := moving_projection_gate (base i) H G Q A (hx i).2.1
  let projection (i : I) : SeparableCoordinate E (CoordinateField E (P i)) := {
    embedding := elementEmbedding E (CoordinateField E (P i)) (movingValue (P i) H G Q A) (gate i).choose
    finite := (gate i).choose_spec.1
    separable := (gate i).choose_spec.2.1 }
  have hv (i : I) : SeparableCoordinate.value E (CoordinateField E (P i)) (projection i)=
      movingValue (P i) H G Q A := elementEmbedding_variable E (CoordinateField E (P i)) _ (gate i).choose
  refine ⟨Q,A,projection,quadraticPolynomial_inFlag c,linearPolynomial_inFlag c,fun i => ⟨hnot i,hv i,?_⟩⟩
  intro nu
  rw [hv]
  by_cases hn : nu∈movingRelevantPlaces (base i) (movingRatio (P i) H G)
  · exact poleOrder_eq_of_valuation_eq_exp nu.val _ _
      (by dsimp [movingPoleTarget,poleOrder]; positivity) ((hx i).2.2 nu hn).1
  · obtain ⟨hcoord,hw⟩ := outside_movingRelevantPlaces (base i) (movingRatio (P i) H G) nu hn
    have hz : exponentSetPoleWeight nu.val (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) movingSupport=0 := by
      rw [exponentSetPoleWeight_moving]
      simp [hcoord,hw]
    have hp := (poleOrder_eval_le_support nu.val (algebraMap E (CoordinateField E (P i)))
      (constant_value_le_one E (CoordinateField E (P i)) nu)
      (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G))
      (polynomialOfSupport movingSupport c)).trans
      (supportPoleWeight_le_exponentSetPoleWeight _ _ _ movingSupport (support_polynomialOfSupport_subset _ _))
    change poleOrder nu.val (coefficientEvaluation _ _ c)≤_ at hp
    rw [hJ i,hz] at hp
    have hp0 := le_antisymm hp (le_max_left _ _)
    simpa [movingPoleTarget,hcoord,hw] using hp0

end
end ProximityPrize.SubmissionLower.MovingSourceIndexedMovingCoordinates6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceIndexedMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814 MovingSourceExtendedPointCount6814
open MovingSourceExtendedMovingDegrees6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap eta)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)
local instance : Algebra (RatFunc E) OmegaT := targetAlgebra E
local instance : IsScalarTower E (RatFunc E) OmegaT := target_tower E

theorem sum_indexed_moving_degrees
    {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (S : Source F)
    (G : I → MvPolynomial (Fin 3) Omega) (hGF : ∀ i, G i∣frozenCarrier eta F)
    (Q A : MvPolynomial (Fin 3) Omega) (scale z u v : ℕ)
    (hbound : ExtendedPointBudget eta F S Q A scale z u v)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (W : FlagDegree) (hcut : PolynomialInFlag W (extendedTargetCut n coeff Q A))
    (old : ∀ i, ExtendedFactorFamily eta F (G i) n coeff)
    (hold : Function.Injective (fun i => (old i).1))
    (hleading : ∀ i, S.leading (codeMap eta)∉(old i).1)
    (hA : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Omega (CoordinateField Omega (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Omega (CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A) :
    scale*(∑ i, SeparableCoordinate.degree Omega (CoordinateField Omega (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v := by
  classical
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq fun a => ((projection i).embedding.commutes a).symm
  letI : ∀ i, FiniteDimensional (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).separable
  let points := genericFiberPoints (B:=RatFunc Omega) (L:=OmegaT) prime
  have hinj : Function.Injective prime := hold
  have hwhole (i : I) : lift (G i)∣extendedCarrier eta F := by
    have hh := map_dvd (MvPolynomial.map (coefficientEmbedding Omega)) (hGF i)
    simpa only [frozenCarrier,lift_frozen,extendedCarrier] using hh
  have certificate (i : I) (f : CoordinateField Omega (prime i) →ₐ[RatFunc Omega] OmegaT) :
      let x := embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (extendedCarrier eta F)=0 ∧
      MvPolynomial.eval x (extendedEquation eta F Q A)=0 ∧
      MvPolynomial.aeval x (extendedTargetCut n coeff Q A)=0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0 ∧
      IsolatedPoint (extendedCarrier eta F) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A) x := by
    have hj : algebraMap (RatFunc Omega) (CoordinateField Omega (prime i)) (rationalVariable Omega)=
        movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A := hvalue i
    have hc := embedding_point_certificate (G i) (frozenH eta F) (frozenG eta F) Q A n coeff
      (old i) hj (hA i) f
    have hc' :
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (lift (G i))=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (extendedEquation eta F Q A)=0 ∧
        MvPolynomial.aeval (embeddingPoint (prime i) (f.restrictScalars Omega)) (extendedTargetCut n coeff Q A)=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (surfaceMap phi (polyH K F)*lift A)≠0 ∧
        IsolatedPoint (lift (G i)) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A)
          (embeddingPoint (prime i) (f.restrictScalars Omega)) := by
      simpa only [scalar_eq_lift,frozenH,frozenG,lift_frozen,target_variable,extendedEquation,extendedTargetCut] using hc
    have hzero := map_dvd (MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))) (hwhole i)
    rw [hc'.1,zero_dvd_iff] at hzero
    have hreg : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))
        (MvPolynomial.pderiv (1 : Fin 3) (extendedCarrier eta F))≠0 := by
      have hr := hc'.2.2.2.1
      rw [map_mul,mul_ne_zero_iff] at hr
      simpa only [extendedCarrier,RCN267.surfaceMap_pderiv_R,polyH] using hr.1
    exact ⟨hzero,hc'.2.1,hc'.2.2.1,hc'.2.2.2.1,
      MovingSourceFactorIsolation6814.isolated_whole_of_factor
        (extendedCarrier eta F) (lift (G i)) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A)
        (hwhole i) _ hc'.1 hreg hc'.2.2.2.2⟩
  have hc : ∀ x ∈ points,
      MvPolynomial.eval x (extendedCarrier eta F)=0 ∧ MvPolynomial.eval x (extendedEquation eta F Q A)=0 ∧
      MvPolynomial.eval x (extendedDenominator eta F A*S.leading phi)≠0 ∧
      MvPolynomial.aeval x (extendedTargetCut n coeff Q A)=0 ∧
      IsolatedPoint (extendedCarrier eta F) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hh := certificate i f
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.2⟩
    have hHA := hh.2.2.2.1
    rw [map_mul,mul_ne_zero_iff] at hHA
    have hL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (S.leading phi)≠0 := by
      have he : S.leading phi=lift (S.leading (codeMap eta)) := (lift_frozen eta _).symm
      rw [he,eval_lift_embedding]
      intro hz
      exact hleading i ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
    simpa only [commonBaseEmbeddingPoint,extendedDenominator,map_mul,map_ofNat] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hHA.1) (mul_ne_zero h2 hHA.2)) hL
  have hb := hbound W (extendedTargetCut n coeff Q A) hcut points
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2.1)
    (fun x hx => (hc x hx).2.2.1) (fun x hx => (hc x hx).2.2.2.1)
    (fun x hx => (hc x hx).2.2.2.2)
  have hcard := genericFiberPoints_card (B:=RatFunc Omega) (L:=OmegaT) prime hinj
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hb

end
end ProximityPrize.SubmissionLower.MovingSourceIndexedMovingDegrees6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN084 RCN095 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceExtendedCoefficients6814
open MovingSourceExtendedPointCount6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceIndexedMovingCoordinates6814 MovingSourceIndexedMovingDegrees6814
open MovingSourceSlicePrimeFamily6814 WeightedSliceAssignment6807 SmallSliceBudgets6807

variable {K E : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Poly" => MvPolynomial (Fin 3) E

theorem filteredCut_zero (N H G : Poly) : filteredCut 0 (fun _ => N) H G=N := by
  simp [filteredCut,Fin.sum_univ_one]

theorem targetCut_zero (N Q A : Poly) :
    extendedTargetCut 0 (fun _ => N) Q A=MvPolynomial.map (coefficientEmbedding E) N := by
  simp [extendedTargetCut,eliminatedCut,filteredCut,Fin.sum_univ_one]

theorem exists_slice_moving_budget
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G N : Poly) (hG : G≠0) (hGF : G∣frozenCarrier eta F)
    (hR : frozenH eta F∈Ideal.span ({G,MvPolynomial.pderiv (1 : Fin 3) G} : Set Poly))
    (q : FlagDegree) (hN : PolynomialInFlag q N)
    (B : SliceBudgets G N (frozenH eta F) q)
    (active : Finset (SliceComponent G N (frozenH eta F)))
    (hlead : ∀ a∈active, SZ.leading (codeMap eta)∉a.2.1)
    (scale z u v : ℕ)
    (hbound : ∀ Q A : Poly, (2 : Poly)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta F SZ Q A scale z u v) :
    ∃ moving : ∀ a : active, MovingPoleBudget a.val.2.1 (frozenH eta F) (frozenG eta F),
      (∀ a : active, (moving a).zCost=(B.unit a.val.1).zCost a.val.2 ∧
        (moving a).yzCost=(B.unit a.val.1).yzCost a.val.2 ∧
        (moving a).allCost=(B.unit a.val.1).allCost a.val.2) ∧
      scale*(∑ a : active, (moving a).movingCost)≤q.zOnly*z+q.yz*u+q.all*v := by
  let P (a : active) := a.val.2.1
  let base (a : active) := B.base a.val.1 a.val.2
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_indexed_moving_coordinates P base (frozenH eta F) (frozenG eta F)
  let moving (a : active) : MovingPoleBudget (P a) (frozenH eta F) (frozenG eta F) := {
    zCost := (B.unit a.val.1).zCost a.val.2
    yzCost := (B.unit a.val.1).yzCost a.val.2
    allCost := (B.unit a.val.1).allCost a.val.2
    movingCost := SeparableCoordinate.degree E (CoordinateField E (P a)) (projection a)
    zPole := (B.unit a.val.1).zPole a.val.2
    yzPole := (B.unit a.val.1).yzPole a.val.2
    allPole := (B.unit a.val.1).allPole a.val.2
    movingPole := by
      intro W
      calc
        _=∑ nu∈W, RCN346.poleOrder E (CoordinateField E (P a)) nu
            (SeparableCoordinate.value E (CoordinateField E (P a)) (projection a)) := by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj a).2.2 nu).symm
        _≤_ := SeparableCoordinate.finite_sum_pole_le_degree E (CoordinateField E (P a)) (projection a) W }
  refine ⟨moving,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hactive : Nonempty active
  · let a0 : active := Classical.choice hactive
    have hAne : A≠0 := by intro hz; exact (hproj a0).1 (hz ▸ (P a0).zero_mem)
    have h2 : (2 : Poly)≠0 := (CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
    let factor (a : active) : Poly := a.val.1.val
    let old (a : active) : ExtendedFactorFamily eta F (factor a) 0 (fun _ => N) :=
      ⟨P a,by simpa only [filteredCut_zero] using a.val.2.property⟩
    have hinj : Function.Injective (fun a : active => (old a).1) := by
      intro a b hab
      apply Subtype.ext
      exact slice_prime_injective G N (frozenH eta F) hG hR hab
    have hcut : PolynomialInFlag q (extendedTargetCut 0 (fun _ => N) Q A) := by
      rw [targetCut_zero]
      exact inFlag_map _ hN
    have hh := sum_indexed_moving_degrees eta F SZ factor
      (fun a => (activeFactors_spec G N a.val.1).2.1.trans hGF)
      Q A scale z u v (hbound Q A (mul_ne_zero h2 hAne) hQ hA)
      0 (fun _ => N) q hcut old hinj (fun a => hlead a.val a.property)
      (fun a => (hproj a).1) projection (fun a => (hproj a).2.1)
    exact hh
  · letI : IsEmpty active := ⟨fun a => hactive ⟨a⟩⟩
    simp

end
end ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN002 RCN007 RCN074 RCN076 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN159
open RCN199 RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open GenericSlicePoints6807 WeightedSliceAssignment6807 SmallSliceBudgets6807 ActiveSliceAssembly6807
open MovingFiberThreeSources6811 HFreeDir6813
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourcePairFirstCutPole6814 MovingSourceSliceMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

variable {K I E T : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433] [Fintype T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)
local notation "phiE" => RingHom.comp (algebraMap Ω E) (polynomialEmbedding K)

end
end ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open GenericSlicePoints6807 HFreeDir6813 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedPointCount6814
open MovingSourceExtendedThickPair6814 MovingSourceCoupledClearing6814

variable {K I E A : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433]
  [Algebra (RatFunc (GenericField K)) E] [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] [Fintype A]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)

end
end ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 35000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811 MovingFiberRetainedStage6811 HFreeDir6813
open MovingSourceExtendedPointCount6814
local notation "w" => RCN326.w

def price (W : FlagDegree) (z u v : ℕ) : ℕ := W.zOnly*z+W.yz*u+W.all*v
def pairNumerator (scale z u v t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale*(∑ j : Fin 3, weight (cellNormal t y r) j*flagMixed flag
    (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j))+
    4*(w+1)*price (cellNormal t y r) z u v+
    3*65539*price (rawFirstFlag t y r) z u v

theorem sum_weight_price (W : FlagDegree) (z u v : ℕ) :
    (∑ j : Fin 3, weight W j*price (MovingFiberThreeSources6811.direction j) z u v)=price W z u v := by
  simp [Fin.sum_univ_three,weight,MovingFiberThreeSources6811.direction,price,unitZFlag,unitYZFlag,unitAllFlag]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

end
end ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open HFreeDir6813 MovingSourcePairRetainedStage6814 MovingSourceCoupledClearing6814
open MovingSourceExtendedPointCount6814
open MovingSourceReducedGamma6814
local notation "w" => RCN326.w

def stageScale {K : Type} [Field K] {F : MvPolynomial (Fin 4) K} (SZ : Source F) (delta : ℕ) : ℕ := SZ.d*delta
def pairStageCost {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (delta t y r : ℕ) (flag : FlagDegree) : ℕ :=
  pairNumerator (stageScale SZ delta)
    (delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    t y r flag/(3*stageScale SZ delta)

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

end
end ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN095 BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814

def coefficient (t y r : ℕ) (j : Fin 3) : ℕ :=
  4*(RCN326.w+1)*weight (cellNormal t y r) j+3*65539*weight (rawFirstFlag t y r) j

def fixedNumerator (t y r : ℕ) (p : FlagDegree) : ℕ :=
  ∑ j : Fin 3, weight (cellNormal t y r) j*
    flagMixed p (HFreeDir6813.hfreeFirstDir t y r j) (direction j)

theorem pairNumerator_eq (scale z u v t y r : ℕ) (p : FlagDegree) :
    pairNumerator scale z u v t y r p=
      scale*fixedNumerator t y r p+coefficient t y r 0*z+
      coefficient t y r 1*u+coefficient t y r 2*v := by
  simp only [pairNumerator,fixedNumerator,coefficient,price,weight,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_succ]
  ring

end
end ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
end MergedPart9
