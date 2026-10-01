import ProximityPrize.SubmissionLower.MergedInfra6815_40
import ProximityPrize.SubmissionLower.MergedInfra6815_26
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceOuterLocalMass6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open ActualSliceMultiplicity6807 ActualFirstCutPole6807 GenericSlicePoints6807
open MovingSourcePairFirstCutPole6814 HFreeDir6813
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper

variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {p errorCap : ℕ} [CharP (GenericField K) p]
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "phiE" => RingHom.comp (algebraMap Ω E) (polynomialEmbedding K)

theorem outer_first_cut_on_prime_slice
    (Gamma : T → Finset K) (flag : T → FlagDegree)
    (S : ∀ i, Stage K I (Gamma i) x p (flag i) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : ∀ i, (S i).F=F)
    (hproper : ∀ i, ¬(S i).G∣globalTailCut (polynomialEmbedding K) (S i).F (w+1))
    (old : ∀ i, FirstTailComponent (S i))
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D≤RingHom.ker (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : ∀ i, scalarPolynomialMap Ω E (S i).G∈D)
    (hisolated : scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) F (w+1))∉D)
    (e d cost : ℕ)
    (hpole : surfaceMap phiE F∈D → surfaceMap phiE (polyH K F)∉D →
      ∀ W : Finset (Place E (CoordinateField E D)),
        (d : ℤ)*(∑ nu∈W, RCN187.poleOrder nu.val
          (SecondJetComponentRoots.coefficientMap phiE D (baseNumerator F (w-1))/
            SecondJetComponentRoots.coefficientMap phiE D (polyH K F)^e))≤cost) :
    d*(∑ i, localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i))≤cost := by
  classical
  let A := CoordinateRing E D
  let Lf := CoordinateField E D
  letI := quotientPolynomialAlgebra E D sep.index
  letI := polynomialBaseAlgebra E D sep.index
  letI := rationalBaseAlgebra E D sep.index sep.transcendental
  letI := quotientBaseScalarTower E D sep.index
  letI := quotientFractionScalarTower E D sep.index
  letI := polynomialRationalScalarTower E D sep.index sep.transcendental
  letI := rationalBaseScalarTower E D sep.index sep.transcendental
  letI : FiniteDimensional (RatFunc E) Lf := sep.finite
  letI : Algebra.IsSeparable (RatFunc E) Lf := sep.separable
  let i0 : T := Classical.choice inferInstance
  let ev := SecondJetComponentRoots.coefficientMap phiE D
  let evalPoint := fun i => pointHom E D (slicePoint (S i) (old i) (emb i) D (hpoint i))
  let mu := fun i => localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i)
  let a : A := firstTailInSlice (S i0) D
  let H : A := originalToSlice (K := K) D (polyH K F)
  let c : A := firstTailScalarInSlice (K := K) D
  let b : A := c*H^(e+3)
  let iota : A →+* Lf := algebraMap A Lf
  have haEq (i : T) : a=firstTailInSlice (S i) D := by
    simp only [a,firstTailInSlice,hF]
  have hpi : Function.Injective evalPoint := by
    intro i j hh
    exact hinj (congrArg Subtype.val (pointHom_injective E D hh))
  have hmu : ∀ i, 1≤mu i := fun i => one_le_localMultiplicity (S i) (hproper i) (old i)
  have ha : ∀ i, a∈(RingHom.ker (evalPoint i).toRingHom)^(mu i) := by
    intro i
    rw [haEq i]
    exact actual_first_tail_mem_point_power (S i) (hproper i) (old i) (emb i) D (hpoint i) (hcarrier i)
  have hHpt : ∀ i, evalPoint i H≠0 := by
    intro i
    have hh := original_H_point_ne_zero (S i) (old i) (emb i) D (hpoint i)
    simpa only [hF] using hh
  have hcpt : ∀ i, evalPoint i c≠0 := fun i => firstTailScalar_point_ne_zero D _
  have hb : ∀ i, evalPoint i b≠0 := by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota : Function.Injective iota := IsFractionRing.injective A Lf
  have hHi : iota H≠0 := by
    intro hz
    have hh : H=0 := hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hh,map_zero])
  have hci : iota c≠0 := by
    intro hz
    have hh : c=0 := hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hh,map_zero])
  have hai : iota a≠0 := by
    intro hz
    apply firstTailInSlice_ne_zero (S i0) D (by simpa only [hF] using hisolated)
    exact hiota (by simpa only [map_zero] using hz)
  have hbi : iota b≠0 := by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx : iota a/iota b≠0 := div_ne_zero hai hbi
  have hrepr : iota a/iota b=ev (baseNumerator F (w-1))/ev (polyH K F)^e := by
    have hn : a=c*H^3*originalToSlice (K := K) D (baseNumerator F (w-1)) := by
      simpa only [hF] using firstTailInSlice_normal_form (S i0) D
    have hh := normalized_first_tail_identity iota a
      (originalToSlice (K := K) D (baseNumerator F (w-1))) H c e hn hHi hci
    exact hh.trans (by rw [originalToSlice_fraction_value,originalToSlice_fraction_value]; rfl)
  have hFd : surfaceMap phiE F∈D := by
    rw [←hF i0,←scalar_surfaceMap]
    exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E) (S i0).G_dvd_surface) (hcarrier i0)
  have hHd : surfaceMap phiE (polyH K F)∉D := by
    intro hm
    have hz := RingHom.mem_ker.mp (hpoint i0 hm)
    change MvPolynomial.eval (embeddingPoint (old i0).1 (emb i0))
      (surfaceMap phiE (polyH K F))=0 at hz
    apply scalar_eval_ne_zero (old i0).1 (emb i0)
      (surfaceMap (polynomialEmbedding K) (polyH K (S i0).F))
      (RCN312.firstTailComponent_regularity_not_mem (S i0) (old i0))
    simpa only [scalar_surfaceMap,hF,MvPolynomial.aeval_eq_eval] using hz
  apply WeightedZeroMass6807.weighted_affine_points_scaled E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d : ℤ)*(∑ nu∈W, RCN187.poleOrder nu.val (iota a/iota b))≤(cost : ℤ)
  rw [hrepr]
  exact hpole hFd hHd W

end
end ProximityPrize.SubmissionLower.MovingSourceOuterLocalMass6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceOuterAllSlices6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN026 (Place)
open RCN204 (flagPole)
open RCN002 RCN007 RCN055 RCN074 RCN076 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN159 RCN199 RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open GenericSlicePoints6807 WeightedSliceAssignment6807 SmallSliceBudgets6807 ActiveSliceAssembly6807
open MovingFiberThreeSources6811 HFreeDir6813 MovingSourceExtendedCoefficients6814
open MovingSourceExtendedMovingDegrees6814 MovingSourceExtendedPointCount6814
open MovingSourcePairFirstCutPole6814 MovingSourceSliceMovingBudget6814 MovingSourceOuterLocalMass6814

variable {K I E T : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433] [Fintype T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)
local notation "phiE" => RingHom.comp (algebraMap Ω E) (polynomialEmbedding K)

theorem outer_first_cut_all_slices
    (Gamma : T → Finset K) (flag : T → FlagDegree)
    (S : ∀ i, Stage K I (Gamma i) x 2130706433 (flag i) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ i, (S i).F=F)
    (parent : FlagDegree) (hparent : PolynomialInFlag parent (frozenCarrier eta F))
    (hproper : ∀ i, ¬(S i).G∣globalTailCut (polynomialEmbedding K) (S i).F (w+1))
    (old : ∀ i, FirstTailComponent (S i))
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (N : PE) (q : FlagDegree) (hNq : PolynomialInFlag q N)
    (hNpoint : ∀ i, MvPolynomial.eval (embeddingPoint (old i).1 (emb i)) N=0)
    (hisolated : ∀ i, IsolatedPoint (scalarPolynomialMap Ω E (S i).G) N
      (scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) (S i).F (w+1)))
      (embeddingPoint (old i).1 (emb i)))
    (hdeg : parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix : 2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source F) (hleading : ∀ i, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree)
    (hbudget : ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
      surfaceMap phiE F∈D → N∈D → surfaceMap phiE (polyH K F)∉D →
      HFreeSliceBudgetCap phiE F D C0 (HFree6812.infCap d))
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q A : PE, (2 : PE)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta F SZ Q A scale zCap uCap vCap) :
    3*scale*(∑ i, localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let carrier := frozenCarrier eta F
  let A := scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) F (w+1))
  let R := frozenH eta F
  let point := fun i => embeddingPoint (old i).1 (emb i)
  let mu := fun i => localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i)
  let first := hfreeFlagDir d r v z C0
  have freeze (P : MvPolynomial (Fin 4) K) :
      scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) P)=surfaceMap (codeMap eta) P := by
    simp only [scalarPolynomialMap,surfaceMap,codeMap,RingHom.comp_apply,MvPolynomial.map_map]
  have hReq : R=scalarPolynomialMap Ω E (regularitySurface (polynomialEmbedding K) F) :=
    (freeze (polyH K F)).symm
  have hRderiv : R=MvPolynomial.pderiv (1 : Fin 3) carrier :=
    (RCN267.surfaceMap_pderiv_R (codeMap eta) F).symm
  have hcar : carrier≠0 := by
    intro hz
    exact hF (surfaceMap_injective (codeMap eta) (codeMap_injective eta)
      (by simpa only [carrier,frozenCarrier,map_zero] using hz))
  have hdiv (i : T) : scalarPolynomialMap Ω E (S i).G∣carrier := by
    have hh := map_dvd (scalarPolynomialMap Ω E) (S i).G_dvd_surface
    rw [hSF i,freeze] at hh
    exact hh
  have hGpoint (i : T) : MvPolynomial.eval (point i) (scalarPolynomialMap Ω E (S i).G)=0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_G_mem Ω (S i).G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1 (S i).G=0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hFpoint (i : T) : MvPolynomial.eval (point i) carrier=0 := by
    have hh := map_dvd (MvPolynomial.eval (point i)) (hdiv i)
    rw [hGpoint i,zero_dvd_iff] at hh
    exact hh
  have hApoint (i : T) : MvPolynomial.eval (point i) A=0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_T_mem Ω (S i).G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1 (globalTailCut (polynomialEmbedding K) F (w+1))=0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker,←hSF i]
      exact hc
    rw [hz,map_zero]
  have hRpoint (i : T) : MvPolynomial.eval (point i) R≠0 := by
    rw [hReq,←hSF i]
    exact scalar_eval_ne_zero (old i).1 (emb i) _
      (regularComponent_H_not_mem Ω (S i).G _ _ (old i))
  have hDpoint (i : T) : MvPolynomial.eval (point i) (MvPolynomial.pderiv (1 : Fin 3) carrier)≠0 := by
    rw [←hRderiv]
    exact hRpoint i
  have hiso (i : T) : IsolatedPoint carrier N A (point i) := by
    exact MovingSourceFactorIsolation6814.isolated_whole_of_factor carrier
      (scalarPolynomialMap Ω E (S i).G) N A (hdiv i) (point i) (hGpoint i) (hDpoint i)
      (by simpa only [hSF] using hisolated i)
  have hcover (i : T) : ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval (point i) g.1=0 :=
    exists_active_factor_of_isolated carrier N A R hcar (point i)
      (hFpoint i) (hApoint i) (hRpoint i) (hDpoint i) (hiso i)
  obtain ⟨assign,hassigned⟩ := exists_point_assignment carrier N R point hcover hNpoint hRpoint
  have hRspan : R∈Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set PE) := by
    rw [hRderiv]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let budgets := Classical.choice (exists_sliceBudgets carrier N R parent q hcar hparent hNq
    2130706433 hdeg hmix)
  let active : Finset (SliceComponent carrier N R) := Finset.univ.image assign
  have hLpoint (i : T) : MvPolynomial.eval (point i) (SZ.leading (codeMap eta))≠0 := by
    have he : SZ.leading (codeMap eta)=scalarPolynomialMap Ω E (SZ.leading (polynomialEmbedding K)) := (freeze _).symm
    rw [he]
    exact scalar_eval_ne_zero (old i).1 (emb i) _ (hleading i)
  have hlead : ∀ a∈active, SZ.leading (codeMap eta)∉a.2.1 := by
    intro a ha hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    exact hLpoint i (hassigned i (hi ▸ hmem))
  obtain ⟨moving,_,hMoving⟩ := exists_slice_moving_budget eta F SZ carrier N hcar dvd_rfl hRspan
    q hNq budgets active hlead scale zCap uCap vCap hbound
  let CX (a : SliceComponent carrier N R) := (budgets.unit a.1).toPrimeFlagBudgetFamily.weightedCost first a.2
  have hlocal (a : active) : 3*(∑ i with assign i=a.val, mu i)≤CX a.val+4*(w+1)*(moving a).movingCost := by
    let T0 := {i : T // assign i=a.val}
    have hne : Nonempty T0 := by
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨i,hi⟩⟩
    letI : Nonempty T0 := hne
    let old0 := fun i : T0 => old i.1
    let emb0 := fun i : T0 => emb i.1
    have hi0 : Function.Injective (fun i : T0 => embeddingPoint (old0 i).1 (emb0 i)) := by
      intro i j hh
      exact Subtype.ext (hinj hh)
    have hpt (i : T0) : a.val.2.1≤RingHom.ker
        (MvPolynomial.aeval (embeddingPoint (old0 i).1 (emb0 i)) : PE →ₐ[E] E).toRingHom := by
      have hh := hassigned i.1
      rw [i.2] at hh
      exact hh
    have hcarD : carrier∈a.val.2.1 := a.val.2.1.mem_of_dvd
      (activeFactors_spec carrier N a.val.1).2.1 (regularComponent_G_mem E a.val.1.val N R a.val.2)
    have hstageD (i : T0) : scalarPolynomialMap Ω E (S i.1).G∈a.val.2.1 := by
      obtain ⟨Q,hQ,hQne⟩ := MovingSourceFactorIsolation6814.quotient_nonzero_at_regular_point
        carrier (scalarPolynomialMap Ω E (S i.1).G) (hdiv i.1) (point i.1) (hGpoint i.1) (hDpoint i.1)
      have hQnot : Q∉a.val.2.1 := fun hmem => hQne (hpt i hmem)
      have hprod : scalarPolynomialMap Ω E (S i.1).G*Q∈a.val.2.1 :=
        (congrArg (fun P : PE => P∈a.val.2.1) hQ).mp hcarD
      exact (inferInstance : a.val.2.1.IsPrime).mem_or_mem hprod |>.resolve_right hQnot
    let i0 : T0 := Classical.choice hne
    have hAz : A∉a.val.2.1 := by
      have hh := first_tail_not_mem_assigned carrier N A R point assign hassigned hiso i0.1
      rwa [i0.2] at hh
    have hb := outer_first_cut_on_prime_slice (fun i : T0 => Gamma i.1) (fun i : T0 => flag i.1)
      (fun i : T0 => S i.1) F (fun i => hSF i.1) (fun i => hproper i.1)
      old0 emb0 hi0 a.val.2.1 (budgets.base a.val.1 a.val.2) hpt hstageD hAz (2*w-1) 3
      (CX a.val+4*(w+1)*(moving a).movingCost) (by
        intro hFd hHd W
        have hh := first_pole_mass_of_moving_budget phiE F a.val.2.1
          (budgets.base a.val.1 a.val.2) hHd d r v z hr hv hR hYR hAll C0
          (hbudget _ (budgets.base a.val.1 a.val.2) hFd
            (regularComponent_T_mem E a.val.1.val N R a.val.2) hHd)
          1 (CX a.val) (moving a).movingCost
          (PureFlagSliceBudget6807.sum_flagPole_le (budgets.unit a.val.1) a.val.2 first)
          (fun U => by simpa only [Nat.cast_one,one_mul,frozenH,frozenG,codeMap] using (moving a).movingPole U) W
        simpa only [Nat.mul_one,Nat.cast_one,one_mul,Nat.cast_add,Nat.cast_mul] using hh)
    have hsum : (∑ i with assign i=a.val, mu i)=∑ i : T0, mu i.1 := by
      simpa only [T0,Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset T)) mu (p := fun i => assign i=a.val)).symm
    rw [hsum]
    exact hb
  have hCX : (∑ a : active, CX a.val)≤flagMixed parent q first := by
    rw [Finset.sum_coe_sort]
    calc
      _≤∑ a : SliceComponent carrier N R, CX a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _=∑ g : ↥(activeFactors carrier N), ∑ C : RegularComponent E g.1 N R,
          (budgets.unit g).toPrimeFlagBudgetFamily.weightedCost first C := Fintype.sum_sigma _
      _≤_ := sum_cost_le carrier N R parent q first hcar hparent budgets
  let assign0 (i : T) : active := ⟨assign i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hpartition : (∑ a : active, ∑ i with assign i=a.val, mu i)=∑ i, mu i := by
    have hh := weighted_assignment_sum assign0 mu
    simpa only [assign0,Subtype.ext_iff] using hh
  have hsum := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset active)) => hlocal a)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  rw [hpartition] at hsum
  calc
    _=scale*(3*∑ i, mu i) := by ring
    _≤scale*((∑ a : active, CX a.val)+4*(w+1)*(∑ a : active, (moving a).movingCost)) :=
      Nat.mul_le_mul_left scale hsum
    _=scale*(∑ a : active, CX a.val)+4*(w+1)*(scale*∑ a : active, (moving a).movingCost) := by ring
    _≤_ := Nat.add_le_add (Nat.mul_le_mul_left scale hCX) (Nat.mul_le_mul_left (4*(w+1)) hMoving)

end
end ProximityPrize.SubmissionLower.MovingSourceOuterAllSlices6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourceOuterChannel6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open GenericSlicePoints6807 HFreeDir6813 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceOuterAllSlices6814

variable {K I E A : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433]
  [Algebra (RatFunc (GenericField K)) E] [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] [Fintype A]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)

theorem outer_first_cut_generic_channel
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree) (hparent : PolynomialInFlag parent (frozenCarrier eta F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, SeparableCoordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, SeparableCoordinate.value Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix : 2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      SeparableCoordinate.degree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let oldPrime := fun a => (old a).1
  letI : ∀ a : A, Algebra (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => (projection a).embedding.toRingHom.toAlgebra
  letI : ∀ a : A, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => IsScalarTower.of_algebraMap_eq fun c => ((projection a).embedding.commutes c).symm
  letI : ∀ a : A, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (oldPrime a)) := fun a => (projection a).finite
  letI : ∀ a : A, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (oldPrime a)) := fun a => (projection a).separable
  let T := (a : A) × (CoordinateField Ω (oldPrime a) →ₐ[RatFunc Ω] E)
  let oldT := fun i : T => old i.1
  let embT := fun i : T => i.2.restrictScalars Ω
  let N := sliceEquation (E := E) ell
  have hpoints : Function.Injective (fun i : T => embeddingPoint (oldT i).1 (embT i)) :=
    commonBaseEmbeddingPoint_injective oldPrime hold
  have hcert (i : T) := GenericSlicePoints6807.embedding_point_certificate (S i.1).G
    (globalTailCut (polynomialEmbedding K) (S i.1).F (w+1))
    (RCN243.regularitySurface (polynomialEmbedding K) (S i.1).F) ell (old i.1) (hvalue i.1) i.2
  have hNq : PolynomialInFlag q N := inFlag_sub_poly (inFlag_const q _) (inFlag_map _ hell)
  have hmass := outer_first_cut_all_slices (fun i : T => Gamma i.1) (fun i : T => flag i.1)
    (fun i : T => S i.1) F hF (fun i => hSF i.1) parent hparent (fun i => hproper i.1)
    oldT embT hpoints N q hNq (fun i => (hcert i).2.1) (fun i => (hcert i).2.2.2.2)
    hdeg hmix SZ (fun i => hleading i.1) d r v z hr hv hR hYR hAll C0
    (fun D _ sep hFD hND hHD => hfree D sep hFD hND hHD) scale zCap uCap vCap hbound
  have hsum := GenericSlicePoints6807.weighted_embedding_sum (E := E) oldPrime
    (fun a => localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a))
  simpa only [oldT,embT,T,SeparableCoordinate.degree,oldPrime,hsum] using hmass

theorem outer_first_cut_coordinate_channel
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree) (hparent : PolynomialInFlag parent (frozenCarrier eta F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix : 2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let Alive : Set A := {a | ∃ c, projection a=Sum.inr c}
  let sep := fun a : Alive => Classical.choose a.2
  have hsep (a : Alive) : projection a.1=Sum.inr (sep a) := Classical.choose_spec a.2
  let old0 := fun a : Alive => old a.1
  have hi0 : Function.Injective (fun a : Alive => (old0 a).1) := by
    intro a b hh
    exact Subtype.ext (hold hh)
  have hv0 (a : Alive) : SeparableCoordinate.value Ω (CoordinateField Ω (old0 a).1) (sep a)=
      coordinateEvaluation Ω (old0 a).1 ell := by
    have hh := hvalue a.1
    rw [hsep a] at hh
    exact hh
  let weight := fun a => localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)
  have hsum : (∑ a, weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))=
      ∑ a : Alive, weight a.1*SeparableCoordinate.degree Ω (CoordinateField Ω (old0 a).1) (sep a) := by
    apply Finset.sum_congr_set Alive
      (fun a => weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))
      (fun a => weight a.1*SeparableCoordinate.degree Ω (CoordinateField Ω (old0 a).1) (sep a))
    · intro a ha
      simp only [hsep ⟨a,ha⟩,coordinateDegree,Sum.elim_inr,old0]
    · intro a ha
      cases hpj : projection a with
      | inl c => simp only [hpj,coordinateDegree,Sum.elim_inl,Nat.mul_zero]
      | inr c => exact (ha ⟨c,hpj⟩).elim
  have hb := outer_first_cut_generic_channel (E := E)
    (fun a : Alive => Gamma a.1) (fun a : Alive => flag a.1) (fun a : Alive => S a.1)
    F hF (fun a => hSF a.1) parent hparent (fun a => hproper a.1) old0 hi0 ell q hell
    sep hv0 hdeg hmix SZ (fun a => hleading a.1) d r v z hr hv hR hYR hAll C0 hfree
    scale zCap uCap vCap hbound
  change 3*scale*(∑ a, weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤_
  rw [hsum]
  exact hb

end
end ProximityPrize.SubmissionLower.MovingSourceOuterChannel6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceSuppliedFrame6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 30000
open scoped Classical
open RCN030 RCN066 RCN086 RCN095 RCN135 RCN136 RCN159 RCN198 RCN199 RCN207 RCN237 RCN243 RCN244 RCN263 RCN264 RCN275
open RCN327 RCN332 RCN334 RCN336 RCN338 RCN340 RCN341 RCN344
open RCN002 RCN037 RCN038 RCN042 RCN074 RCN134 RCN156 RCN248
open LocatorHybridTransportC2 CommonLinearChannels6807

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p errorCap a b s : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p]
local notation "Ω" => GenericField K
variable (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (support a b s))
variable (hp : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1)) (geometry : ReducedActiveGeometry S)

def suppliedReducedUnit :=
  activeNestedUnitFamily geometry.base geometry.hactive geometry.hZ
    (RCN315.residualStage_pderiv_one_ne_zero_of_support S) geometry.data
    S.irreducible_G (reducedFirstCut_proper S hp)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag (support a b s) (w+1)) (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

def suppliedBase (C : FirstTailComponent S) : SeparableLiteralCoordinate C.1 := by
  let C' : RegularComponent Ω S.G (reducedFirstCut S)
      (regularitySurface (polynomialEmbedding K) S.F) :=
    ⟨C.1,by
      rw [←regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
      exact C.2⟩
  exact geometry.base C'

def suppliedUnit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
  (suppliedReducedUnit S hp geometry) (suppliedBase S geometry)

def suppliedCommon : CommonLinearValues (suppliedUnit S hp geometry) :=
  of_congruent_cut (ordinary_sub_reducedFirstCut_dvd S) (suppliedReducedUnit S hp geometry)
    (suppliedBase S geometry)
    (of_active_nested geometry.base geometry.hactive geometry.hZ
      (RCN315.residualStage_pderiv_one_ne_zero_of_support S) geometry.data
      S.irreducible_G (reducedFirstCut_proper S hp)
      ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
      ((support_subset_flagSupport_iff
        (reducedResidualAgreementFlag (support a b s) (w+1)) (reducedFirstCut S)).2 (reducedFirstCut_in_flag S)))

theorem suppliedCommon_lam : (suppliedCommon S hp geometry).lam=geometry.data.lam := rfl
theorem suppliedCommon_mu : (suppliedCommon S hp geometry).mu=geometry.data.mu := rfl

def suppliedBudget := (suppliedUnit S hp geometry).toPrimeFlagBudgetFamily

theorem suppliedBudget_yzPositive (C : FirstTailComponent S) :
    1≤(suppliedBudget S hp geometry).yzCost C := by
  let C' : RegularComponent Ω S.G (reducedFirstCut S)
      (regularitySurface (polynomialEmbedding K) S.F) :=
    ⟨C.1,by
      rw [←regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
      exact C.2⟩
  change 1≤coordinateDegree Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  rw [common_u_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C,
    suppliedCommon_lam,eval_linearU]
  exact geometry.data.uTranscendental C'

theorem suppliedBudget_yzPole (C : FirstTailComponent S) :
    LiteralSupportPoleBound (suppliedBase S geometry C) (flagSupport unitYZFlag)
      ((suppliedBudget S hp geometry).yzCost C) := by
  exact (suppliedUnit S hp geometry).toAdaptiveUnitPoleBudget.yzPole C

theorem supplied_u_value (lam : Ω) (hlam : geometry.data.lam=lam) (C : FirstTailComponent S) :
    coordinateValue Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)=
      coordinateEvaluation Ω C.1 (linearU lam) := by
  have hh := common_u_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C
  simpa only [suppliedCommon_lam,hlam] using hh

theorem supplied_a_value (lam mu : Ω) (hlam : geometry.data.lam=lam) (hmu : geometry.data.mu=mu)
    (C : FirstTailComponent S) :
    coordinateValue Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).allProjection C)=
      coordinateEvaluation Ω C.1 (linearA mu lam) := by
  have hh := common_a_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C
  simpa only [suppliedCommon_lam,suppliedCommon_mu,hlam,hmu] using hh

end
end ProximityPrize.SubmissionLower.MovingSourceSuppliedFrame6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceCommonChannelBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open HFree6812 HFreeDir6813 CommonLinearChannels6807 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceExtendedThickPair6814
open MovingSourceOuterChannel6814 MovingSourceCoupledClearing6814
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

def commonChannel (lam mu : Ω) : Fin 3 → MvPolynomial (Fin 3) Ω :=
  ![linearZ,linearU lam,linearA mu lam]

private theorem cast_ne {n : ℕ} (h0 : 0<n) (hn : n<2130706433) : (n : K)≠0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

private theorem slice_budget
    (F : MvPolynomial (Fin 4) K) (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9 : N≤9678) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (hFD : surfaceMap (HFree6812.phiE K E) F∈D)
    (hHD : surfaceMap (HFree6812.phiE K E) (polyH K F)∉D) (d : Fin 3)
    (c : Fin 3 → Ω) (i : Fin 3) (hci : c i=1) (q : Fin 3 → Polynomial K)
    (hqd : DirShape d q) (hq : ∀ m, polynomialEmbedding K (q m)=c m) (hq1 : i=1 ∨ q 1=0)
    (hslice : MvPolynomial.C (sliceValue Ω E)-scalarPolynomialMap Ω E
      (∑ m, MvPolynomial.C (c m)*MvPolynomial.X m)∈D) :
    HFreeSliceBudgetCap (HFree6812.phiE K E) F D unitAllFlag (infCap d) := by
  have hNK : ∀ n : ℕ, 0<n → n≤N → (n : K)≠0 := fun n h0 hn => cast_ne h0 (by omega)
  exact ⟨hfree_slice_budget_dir d F D sep hFD hHD c i hci q hqd hq hslice
    (by exact_mod_cast cast_ne (K:=K) (n:=2) (by decide) (by decide))
    (hchar_gap F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap F D hHD c i hci q hq hq1 hslice N hN hNK)⟩

theorem common_channel_hfree
    (F : MvPolynomial (Fin 4) K) (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9 : N≤9678) (lam mu : Ω)
    (hlam : lam∈Set.range (polynomialEmbedding K)) (hmu : mu∈Set.range (polynomialEmbedding K))
    (j : Fin 3) : HFreeChannelDir (E:=E) F (commonChannel lam mu j) unitAllFlag j := by
  intro D _ sep hFD hsl hHD
  obtain ⟨ql,hql⟩ := hlam
  obtain ⟨qm,hqm⟩ := hmu
  have go := slice_budget (E:=E) F N hN hN9 D sep hFD hHD j
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![0,0,1] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearZ := by simp [linearZ,Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![1,0,lam] 0 rfl ![1,0,ql] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp [hql]) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![1,0,lam] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearU lam := by simp [linearU,Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![mu,1,mu*lam] 1 rfl ![qm,1,qm*ql] trivial
      (fun m => by fin_cases m <;> simp [hql,hqm]) (Or.inl rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![mu,1,mu*lam] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearA mu lam := by simp [linearA,Fin.sum_univ_three]; ring
    rw [he]; exact hsl

variable {I A : Type} [Fintype A] [CharP E 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}

include E in
theorem outer_first_cut_from_sources
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree)
    (hp : ∀ (L : Type) [Field L] (phi : Polynomial K →+* L), PolynomialInFlag parent (surfaceMap phi F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (lam mu : Ω) (hlam : lam∈Set.range (polynomialEmbedding K)) (hmu : mu∈Set.range (polynomialEmbedding K))
    (j : Fin 3) (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 (commonChannel lam mu j))
    (hlinear : 2*(parent.zOnly+parent.yz+parent.all)<2130706433)
    (SZ SP SQ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : MvPolynomial.weightedTotalDegree residualTotalWeights F≤r+v+z) (hsmall : r+v+z≤9678)
    (hpos : 0<F.degreeOf 2) (hcharF : F.degreeOf 2<2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d) (hchar : delta≤2130706433) (hZchar : SZ.k<2130706433)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    3*(SZ.d*delta)*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      (SZ.d*delta)*flagMixed parent (direction j) (hfreeFlagDir j r v z unitAllFlag)+
        4*(w+1)*((direction j).zOnly*(delta*flagMixed parent unitZFlag SZ.flag)+
          (direction j).yz*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)+
          (direction j).all*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)) := by
  have hell : PolynomialInFlag (direction j) (commonChannel lam mu j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag lam
    · exact linearA_in_flag mu lam
  have hq : (direction j).zOnly+(direction j).yz+(direction j).all=1 := by fin_cases j <;> rfl
  have hAll' : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ) := Or.inr (by exact_mod_cast hAll)
  exact outer_first_cut_coordinate_channel (E:=E) Gamma flag S F hF hSF parent (hp _ _)
    hproper old hold (commonChannel lam mu j) (direction j) hell projection hvalue (by omega)
    (by rw [hq,mul_one]; exact hlinear) SZ hleading j r v z hr hv hR hYR hAll' unitAllFlag
    (common_channel_hfree F (r+v+z) hAll hsmall lam mu hlam hmu j) _ _ _ _
    (fun Q U hden hQf hUf => extended_sources_point_budget (algebraMap Ω E) F hF hpos hcharF
      SP SQ hcop delta hd hP hQ hchar SZ hZchar parent (hp _ _) hlinear Q U hden hQf hUf hz hu)

end
end ProximityPrize.SubmissionLower.MovingSourceCommonChannelBudget6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceOuterMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN074 RCN086 RCN095 RCN135 RCN136 RCN198 RCN199 RCN200 RCN207 RCN208 RCN209 RCN264 RCN313 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceMovingDegrees6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceIndexedMovingDegrees6814 MovingSourceIndexedMovingCoordinates6814

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local notation "Ω" => GenericField K
local notation "Poly" => MvPolynomial (Fin 3) Ω

theorem outer_first_tail_pair_degrees
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G : I → Poly) (hGF : ∀ i, G i∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w) (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (Q A : Poly) (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (scale z u v : ℕ) (hbound : ExtendedPointBudget (RingHom.id Ω) F SZ Q A scale z u v)
    (old : ∀ i, RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F))
    (hold : Function.Injective (fun i => (old i).1)) (hlead : ∀ i, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (hAnonzero : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    scale*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v := by
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩ := exists_filtered_certificate (polynomialEmbedding K)
    a b s F hR hYR hAll (w+1) (by omega) (tailSelector (w+1)) 0 0 0
  have heq' : globalTailCut (polynomialEmbedding K) F (w+1)=filteredCut w coeff (baseH F) (baseG F) := heq
  let old' : ∀ i, ExtendedFactorFamily (RingHom.id Ω) F (G i) w coeff := fun i =>
    ⟨(old i).1,by
      change (old i).1∈regularComponents Ω (G i) (filteredCut w coeff (baseH F) (baseG F)) (baseH F)
      rw [←heq']
      exact (old i).2⟩
  obtain ⟨hHflag,hGflag⟩ := RCN201.surfaceMap_HG_flags (polynomialEmbedding K) a b s F hR hYR hAll
  have hcut := targetCut_small_flag F a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel Q A hQ hA
  exact sum_indexed_moving_degrees (RingHom.id Ω) F SZ G hGF Q A scale z u v hbound
    w coeff _ hcut old' hold hlead hAnonzero projection hvalue

theorem exists_outer_first_tail_pair_budget
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G : I → Poly) (hGF : ∀ i, G i∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w) (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (base : ∀ i, ∀ C : RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F),
      SeparableLiteralCoordinate C.1)
    (p : I → FlagDegree) (tailFlag : FlagDegree) (unit : ∀ i, AdaptiveUnitProjectionFamily (base i) (p i) tailFlag)
    (old : ∀ i, RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F))
    (hold : Function.Injective (fun i => (old i).1))
    (active : Finset I) (hlead : ∀ i∈active, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (scale z u v : ℕ)
    (hbound : ∀ Q A : Poly, (2 : Poly)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget (RingHom.id Ω) F SZ Q A scale z u v) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    ∃ budget : ∀ i, MovingPoleBudget (old i).1 (baseH F) (baseG F),
      (∀ i, (budget i).zCost=(unit i).toPrimeFlagBudgetFamily.zCost (old i) ∧
        (budget i).yzCost=(unit i).toPrimeFlagBudgetFamily.yzCost (old i) ∧
        (budget i).allCost=(unit i).toPrimeFlagBudgetFamily.allCost (old i)) ∧
      scale*(∑ i∈active, (budget i).movingCost)≤W.zOnly*z+W.yz*u+W.all*v := by
  classical
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_indexed_moving_coordinates
    (fun i => (old i).1) (fun i => base i (old i)) (baseH F) (baseG F)
  let budget (i : I) : MovingPoleBudget (old i).1 (baseH F) (baseG F) := {
    zCost := (unit i).toPrimeFlagBudgetFamily.zCost (old i)
    yzCost := (unit i).toPrimeFlagBudgetFamily.yzCost (old i)
    allCost := (unit i).toPrimeFlagBudgetFamily.allCost (old i)
    movingCost := SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)
    zPole := (unit i).toAdaptiveUnitPoleBudget.zPole (old i)
    yzPole := (unit i).toAdaptiveUnitPoleBudget.yzPole (old i)
    allPole := (unit i).toAdaptiveUnitPoleBudget.allPole (old i)
    movingPole := by
      intro U
      calc
        _=∑ nu∈U, RCN187.poleOrder nu.val
            (SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i)) := by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj i).2.2 nu).symm
        _≤_ := SeparableCoordinate.finite_sum_pole_le_degree Ω (CoordinateField Ω (old i).1) (projection i) U }
  refine ⟨budget,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hempty : active=∅
  · simp [hempty]
  obtain ⟨i0,hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hAne : A≠0 := by intro hz; exact (hproj i0).1 (hz ▸ (old i0).1.zero_mem)
  have htwo : (2 : Poly)≠0 := (CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
  have hb := outer_first_tail_pair_degrees F SZ (fun i : active => G i.val) (fun i => hGF i.val)
    a b s w hw hR hYR hAll Q A hQ hA scale z u v (hbound Q A (mul_ne_zero htwo hAne) hQ hA)
    (fun i => old i.val) (fun i j hh => Subtype.ext (hold hh))
    (fun i => hlead i.val i.property) (fun i => (hproj i.val).1)
    (fun i => projection i.val) (fun i => (hproj i.val).2.1)
  change scale*(∑ i∈active, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))≤_
  rwa [Finset.sum_coe_sort active (fun i => SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))] at hb

end
end ProximityPrize.SubmissionLower.MovingSourceOuterMovingBudget6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourceOuterPrimeInjection6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 30000
open scoped Classical
open RCN002 RCN074 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136 RCN137 RCN156 RCN159 RCN243 RCN244 RCN264 RCN267 RCN313
open WeightedSliceAssignment6807 ActiveSliceAssembly6807 MovingSourceSlicePrimeFamily6814
variable {K I J : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {p errorCap : ℕ} [CharP (GenericField K) p]
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "Poly" => MvPolynomial (Fin 3) Ω
local notation "w" => RCN326.w

theorem outer_stage_primes_injective
    (Gamma : J → Finset K) (flag : J → FlagDegree)
    (S : ∀ j, Stage K I (Gamma j) x p (flag j) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ j, (S j).F=F)
    (hG : ∀ j, (S j).G∈normalizedFactorSet (surfaceMap (polynomialEmbedding K) F))
    (hGinj : Function.Injective (fun j => (S j).G))
    (hproper : ∀ j, ¬(S j).G∣globalTailCut (polynomialEmbedding K) (S j).F (w+1)) :
    Function.Injective (fun a : (j : J) × FirstTailComponent (S j) => a.2.1) := by
  let carrier := surfaceMap (polynomialEmbedding K) F
  have hcar : carrier≠0 := by
    intro hz
    exact hF (surfaceMap_injective (polynomialEmbedding K) (polynomialEmbedding_injective K)
      (by simpa only [carrier,map_zero] using hz))
  rintro ⟨i,Ci⟩ ⟨j,Cj⟩ he
  have hg : (S i).G=(S j).G := by
    by_contra hne
    have hsubset : ({(S i).G,(S j).G} : Finset Poly)⊆normalizedFactorSet carrier := by
      intro P hP
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact hG i
      · exact hG j
    have hprod : (S i).G*(S j).G∣carrier := by
      have hh := (Finset.prod_dvd_prod_of_subset {(S i).G,(S j).G} (normalizedFactorSet carrier) id hsubset).trans
        (normalizedFactorSet_product_dvd carrier hcar)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have hiG : (S i).G∈Ci.1 := regularComponent_G_mem Ω (S i).G _ _ Ci
    have hjG : (S j).G∈Ci.1 := by
      have hh := regularComponent_G_mem Ω (S j).G _ _ Cj
      exact (congrArg (fun P : Ideal Poly => (S j).G∈P) he).mpr hh
    have hd := derivative_mem_of_two_factors carrier (S i).G (S j).G Ci.1 hprod hiG hjG
    apply regularComponent_H_not_mem Ω (S i).G _ _ Ci
    change surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) (S i).F)∈Ci.1
    have hr : surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) (S i).F)=
        MvPolynomial.pderiv (1 : Fin 3) carrier := by
      rw [hSF i]
      exact (surfaceMap_pderiv_R (polynomialEmbedding K) F).symm
    exact (congrArg (fun P : Poly => P∈Ci.1) hr).mpr hd
  have hi : i=j := hGinj hg
  cases hi
  exact congrArg (fun C : FirstTailComponent (S i) => (⟨i,C⟩ : (j : J) × FirstTailComponent (S j)))
    (Subtype.ext he)

end
end ProximityPrize.SubmissionLower.MovingSourceOuterPrimeInjection6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourcePacketLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceCoupledClearing6814 SecondJetCoefficients
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.MovingSourcePacketLeading6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourceBandGeometry6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN137 RCN156 RCN159 RCN174 RCN198
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN319 RCN327 RCN334
open LocatorHybridCells LocatorHybridCellsC1 MovingSourceUniformTail6814 MovingSourceOuterPrimeInjection6814
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Packet (x : I → K) (t y r : ℕ) where
  rlow : 4≤r
  rhigh : r≤13
  ylow : r+2≤y
  yhigh : y≤59
  yt : y≤t
  thigh : t≤4100
  D : ℕ
  Dlow : 131072≤D
  Dchar : D<2130706433
  F : MvPolynomial (Fin 4) K
  irreducible : Irreducible F
  rdegree : 0<F.degreeOf 2
  box : F∈globalCoefficientBox K D w t r
  support : ResidualSupportData (cellSupport t y r) F
  selected : K → Polynomial K
  seeds : Finset K
  nodes : Finset I
  u0 : I → K
  u1 : I → K
  injective : Set.InjOn x nodes
  nodeCount : nodes.card=262144
  degree : ∀ gamma∈seeds, (selected gamma).natDegree≤w
  agreement : ∀ gamma∈seeds, 181245≤
    (nodes.filter (fun i => (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card
  solution : ∀ gamma∈seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma∈seeds, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80899

namespace Packet
variable {x : I → K} {t y r : ℕ} (P : Packet x t y r)

include P in
theorem support_caps : (cellSupport t y r).s=r ∧ (cellSupport t y r).ys=y ∧
    (cellSupport t y r).total=t := by
  have := P.rlow
  have := P.ylow
  have := P.yt
  dsimp [cellSupport,RCN198.support,cellA,cellB,cellS]
  omega

theorem r_weight : wt residualSWeights P.F≤r := by
  simpa only [P.support_caps.1] using P.support.s_weight

theorem y_weight : wt residualYSWeights P.F≤y := by
  simpa only [P.support_caps.2.1] using P.support.ys_weight

theorem total_weight : wt residualTotalWeights P.F≤t := by
  simpa only [P.support_caps.2.2] using P.support.total_weight

theorem coordinate_bounds : P.F.degreeOf 1≤y ∧ P.F.degreeOf 2≤r ∧ P.F.degreeOf 3≤t := by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using P.support.coordinate_bounds

def restrict (Delta : Finset K) (hsub : Delta⊆P.seeds) : Packet x t y r :=
  {P with seeds := Delta
          degree := fun gamma hg => P.degree gamma (hsub hg)
          agreement := fun gamma hg => P.agreement gamma (hsub hg)
          solution := fun gamma hg => P.solution gamma (hsub hg)
          regular := fun gamma hg => P.regular gamma (hsub hg)
          noPencil := noLargeSelectedPencil_mono P.selected P.seeds Delta w 80899 hsub P.noPencil}

def stage (g : GeometricFactor K P.F) :
    ResidualStage (polynomialEmbedding K) (geometricSeeds K P.F P.selected P.seeds g) x
      2130706433 80899 (geometricCumulativeFlag K g) w (cellSupport t y r) :=
  reflagResidualStage
    (geometricResidualStageOfSupport K (cellSupport t y r) P.F P.irreducible P.rdegree
      (P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega : r<2130706433)) P.support
      P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.degree P.solution P.regular P.noPencil (by decide) g)
    (polynomialIn_surfaceCumulativeFlag g.val)

theorem stage_F (g : GeometricFactor K P.F) : (P.stage g).F=P.F := rfl
theorem stage_flag (g : GeometricFactor K P.F) :
    (geometricCumulativeFlag K g).all≤r ∧
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all≤y ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all≤t := by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using
    geometricCumulativeFlag_le_support P.F P.irreducible.ne_zero P.support g

theorem stage_agreement (g : GeometricFactor K P.F) :
    ∀ gamma∈geometricSeeds K P.F P.selected P.seeds g, 181245≤((P.stage g).agreementFiber gamma).card :=
  fun gamma hg => P.agreement gamma (geometricSeeds_subset K P.F P.selected P.seeds g hg)

theorem parent_flag (L : Type) [Field L] (phi : Polynomial K →+* L) :
    PolynomialInFlag ⟨t-y,y-r,r⟩ (surfaceMap phi P.F) :=
  MovingSourceReducedGamma6814.surface_flag_of_caps phi P.F r y t (by have := P.ylow; omega) P.yt
    P.r_weight P.y_weight P.total_weight

theorem stage_proper (hproper : ¬P.F∣numerator K P.F (w+1)) (g : GeometricFactor K P.F) :
    ¬(P.stage g).G∣globalTailCut (polynomialEmbedding K) (P.stage g).F (w+1) := by
  intro hg
  exact hproper ((geometric_tail_dvd_iff_original (P.stage g) P.irreducible (w+1)).mp hg)

theorem prime_injective (hproper : ¬P.F∣numerator K P.F (w+1)) :
    Function.Injective (fun a : (g : GeometricFactor K P.F) × FirstTailComponent (P.stage g) => a.2.1) := by
  apply outer_stage_primes_injective (geometricSeeds K P.F P.selected P.seeds)
    (geometricCumulativeFlag K) P.stage P.F P.irreducible.ne_zero P.stage_F
  · intro g
    exact g.property
  · intro g h he
    exact Subtype.ext he
  · exact P.stage_proper hproper

theorem seeds_cover : P.seeds.card≤∑ g : GeometricFactor K P.F,
    (geometricSeeds K P.F P.selected P.seeds g).card :=
  card_le_sum_geometricSeeds K P.F P.irreducible.ne_zero P.selected P.seeds P.solution

end Packet
end
end ProximityPrize.SubmissionLower.MovingSourceBandGeometry6815
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.CertifiedFactorInputs6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical
open MvPolynomial RCN081 RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN275 RCN319
open LocatorHybridCells MovingSourceBandGeometry6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem code_weight_lower (F : MvPolynomial (Fin 4) K) (hF : F≠0) (B R : ℕ)
    (hB : wt residualYSWeights F=B) (hR : wt residualSWeights F≤R) :
    131071*B-R≤wt (RCN081.contactWeights 131071) F := by
  have hc := RCN180.residualYS_mul_le_contact_add_slope F 131071 (by decide)
  rw [hB] at hc
  omega

theorem relative_box_of_carrier_box (F : MvPolynomial (Fin 4) K) (D L s T R : ℕ)
    (hbox : F∈RCN174.globalCoefficientBox K D 131071 L s)
    (hT : wt residualTotalWeights F≤T) (hR : wt residualSWeights F≤R) :
    F∈RCN100.globalCoefficientBox K D 1 T R := by
  intro e he
  have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hT
  have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights he).trans hR
  have hc := (hbox he).2.2
  rw [RCN081.weight_fin4] at ht hr
  simp [residualTotalWeights,residualSWeights] at ht hr
  change e 1+e 2+e 3≤T ∧ e 2≤R ∧ e 0+1*e 1+(1-1)*e 2<D
  omega

def factorPacket {H : MvPolynomial (Fin 4) K} (F : RCN266.RegularIndex H)
    (D L s t y r : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (hbox : F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hrlo : 4≤r) (hrhi : r≤13) (hylo : r+2≤y) (hyhi : y≤59) (hyt : y≤t) (hthi : t≤4100)
    (hR : wt residualSWeights F.val≤r) (hY : wt residualYSWeights F.val≤y)
    (hT : wt residualTotalWeights F.val≤t)
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899) : Packet (nodes : I → K) t y r where
  rlow := hrlo
  rhigh := hrhi
  ylow := hylo
  yhigh := hyhi
  yt := hyt
  thigh := hthi
  D := D
  Dlow := hDlow
  Dchar := hDchar
  F := F.val
  irreducible := (RCN167.positiveRFactors_spec H F.val F.property).1
  rdegree := (RCN167.positiveRFactors_spec H F.val F.property).2.2
  box := by
    intro e he
    have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hT
    have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights he).trans hR
    rw [RCN081.weight_fin4] at ht hr
    simp [residualTotalWeights,residualSWeights] at ht hr
    exact ⟨by omega,by omega,(hbox he).2.2⟩
  support := by
    constructor <;> dsimp [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega
  selected := selected
  seeds := RCN140.regularSeeds H selected Gamma F
  nodes := Finset.univ
  u0 := u0
  u1 := u1
  injective := nodes.injective.injOn
  nodeCount := by simpa only [Finset.card_univ] using hI
  degree := fun gamma hg => hdegree gamma (RCN140.regularSeeds_subset H selected Gamma F hg)
  agreement := fun gamma hg => hagreement gamma (RCN140.regularSeeds_subset H selected Gamma F hg)
  solution := fun _ hg => (Finset.mem_filter.mp hg).2.1
  regular := fun _ hg => (Finset.mem_filter.mp hg).2.2
  noPencil := noLargeSelectedPencil_mono selected Gamma _ 131071 80899
    (RCN140.regularSeeds_subset H selected Gamma F) hno

end
end ProximityPrize.SubmissionLower.CertifiedFactorInputs6815
end MergedPart9
