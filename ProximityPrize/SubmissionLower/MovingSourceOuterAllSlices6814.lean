import ProximityPrize.SubmissionLower.MovingSourceOuterLocalMass6814

/-! One first-cut count over ALL outer geometric Stages. The carrier is
the original surface, not one selected factor, so the moving pair price
is paid once. Individual Stage multiplicities are retained unchanged. -/
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

#print axioms outer_first_cut_all_slices
end
end ProximityPrize.SubmissionLower.MovingSourceOuterAllSlices6814
