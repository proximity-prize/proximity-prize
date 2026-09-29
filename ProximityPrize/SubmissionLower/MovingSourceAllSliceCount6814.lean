import ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814

/-! Actual all-slices first-cut aggregation. One disjoint assignment and
one common moving projection cover every assigned geometric factor.
Neither local count bounds nor a shared moving sum are assumptions. -/
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

theorem first_cut_all_slices
    (S : Stage K I Gamma x 2130706433 flag errorCap stageSupport)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (N : PE) (q : FlagDegree) (hNq : PolynomialInFlag q N)
    (hNpoint : ∀ i, MvPolynomial.eval (embeddingPoint (old i).1 (emb i)) N=0)
    (hisolated : ∀ i, IsolatedPoint (scalarPolynomialMap Ω E S.G) N
      (scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1)))
      (embeddingPoint (old i).1 (emb i)))
    (hdeg : flag.zOnly+flag.yz+flag.all<2130706433)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source S.F) (hleading : ∀ i, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree)
    (hbudget : ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
      surfaceMap phiE S.F∈D → N∈D → surfaceMap phiE (polyH K S.F)∉D →
      HFreeSliceBudgetCap phiE S.F D C0 (HFree6812.infCap d))
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q A : PE, (2 : PE)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta S.F SZ Q A scale zCap uCap vCap) :
    3*scale*(∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i))≤
      scale*flagMixed flag q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let F := scalarPolynomialMap Ω E S.G
  let A := scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1))
  let R := frozenH eta S.F
  let point := fun i => embeddingPoint (old i).1 (emb i)
  let mu := fun i => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)
  let first := hfreeFlagDir d r v z C0
  have freeze (P : MvPolynomial (Fin 4) K) :
      scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) P)=surfaceMap (codeMap eta) P := by
    simp only [scalarPolynomialMap,surfaceMap,codeMap,RingHom.comp_apply,MvPolynomial.map_map]
  have hReq : R=scalarPolynomialMap Ω E (regularitySurface (polynomialEmbedding K) S.F) :=
    (freeze (polyH K S.F)).symm
  have hF : F ≠ 0 := by
    intro hz
    apply S.irreducible_G.ne_zero
    apply MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
    simpa only [F, scalarPolynomialMap, map_zero] using hz
  have hFp : PolynomialInFlag flag F := inFlag_map _ S.flag_support
  have hFpoint (i : T) : MvPolynomial.eval (point i) F = 0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_G_mem Ω S.G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1 S.G = 0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hApoint (i : T) : MvPolynomial.eval (point i) A = 0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_T_mem Ω S.G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1
        (globalTailCut (polynomialEmbedding K) S.F (w+1)) = 0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hRpoint (i : T) : MvPolynomial.eval (point i) R ≠ 0 := by
    rw [hReq]
    exact scalar_eval_ne_zero (old i).1 (emb i) _
      (regularComponent_H_not_mem Ω S.G _ _ (old i))
  have hDpoint (i : T) :
      MvPolynomial.eval (point i) (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0 := by
    have hh := scalar_eval_ne_zero (old i).1 (emb i)
      (MvPolynomial.pderiv (1 : Fin 3) S.G) (carrier_derivative_not_mem S (old i))
    simpa only [F,scalarPolynomialMap,MvPolynomial.pderiv_map] using hh
  have hcover (i : T) : ∃ g : ↥(activeFactors F N), MvPolynomial.eval (point i) g.1 = 0 :=
    exists_active_factor_of_isolated F N A R hF (point i)
      (hFpoint i) (hApoint i) (hRpoint i) (hDpoint i) (hisolated i)
  obtain ⟨assign,hassigned⟩ := exists_point_assignment F N R point hcover hNpoint hRpoint

  have hGF : F∣frozenCarrier eta S.F := by
    have hh := map_dvd (scalarPolynomialMap Ω E) S.G_dvd_surface
    rw [freeze] at hh
    exact hh
  have hRspan : R∈Ideal.span ({F,MvPolynomial.pderiv (1 : Fin 3) F} : Set PE) := by
    have hh : regularitySurface (polynomialEmbedding K) S.F∈
        Ideal.span ({S.G,MvPolynomial.pderiv (1 : Fin 3) S.G} : Set (MvPolynomial (Fin 3) Ω)) := by
      rw [regularitySurface,←RCN267.surfaceMap_pderiv_R]
      exact RCN076.pderiv_mem_span_of_dvd S.G _ S.G_dvd_surface
    rw [hReq]
    exact RCN076.scalar_derivative_span (E:=E) S.G _ hh
  let budgets := Classical.choice (exists_sliceBudgets F N R flag q hF hFp hNq 2130706433 hdeg hmix)
  let active : Finset (SliceComponent F N R) := Finset.univ.image assign
  have hLpoint (i : T) : MvPolynomial.eval (point i) (SZ.leading (codeMap eta))≠0 := by
    have he : SZ.leading (codeMap eta)=scalarPolynomialMap Ω E (SZ.leading (polynomialEmbedding K)) := (freeze _).symm
    rw [he]
    exact scalar_eval_ne_zero (old i).1 (emb i) _ (hleading i)
  have hlead : ∀ a∈active, SZ.leading (codeMap eta)∉a.2.1 := by
    intro a ha hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    apply hLpoint i
    exact hassigned i (hi ▸ hmem)
  obtain ⟨moving,_,hMoving⟩ := exists_slice_moving_budget eta S.F SZ F N hF hGF hRspan q hNq
    budgets active hlead scale zCap uCap vCap hbound
  let CX (a : SliceComponent F N R) := (budgets.unit a.1).toPrimeFlagBudgetFamily.weightedCost first a.2
  have hlocal (a : active) :
      3*(∑ i with assign i=a.val, mu i)≤CX a.val+4*(w+1)*(moving a).movingCost := by
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
    have hcar : F∈a.val.2.1 := a.val.2.1.mem_of_dvd (activeFactors_spec F N a.val.1).2.1
      (regularComponent_G_mem E a.val.1.val N R a.val.2)
    let i0 : T0 := Classical.choice hne
    have hAz : A∉a.val.2.1 := by
      have hh := first_tail_not_mem_assigned F N A R point assign hassigned hisolated i0.1
      rwa [i0.2] at hh
    have hb := first_cut_on_prime_slice_of_moving_budget S hproper old0 emb0 hi0 a.val.2.1
      (budgets.base a.val.1 a.val.2) hpt hcar hAz d r v z hr hv hR hYR hAll C0
      (fun hFd hHd => hbudget _ (budgets.base a.val.1 a.val.2) hFd
        (regularComponent_T_mem E a.val.1.val N R a.val.2) hHd)
      (moving a) (CX a.val) (PureFlagSliceBudget6807.sum_flagPole_le (budgets.unit a.val.1) a.val.2 first)
    have hsum : (∑ i with assign i=a.val, mu i)=∑ i : T0, mu i.1 := by
      simpa only [T0,Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset T)) mu (p := fun i => assign i=a.val)).symm
    rw [hsum]
    exact hb
  have hCX : (∑ a : active, CX a.val)≤flagMixed flag q first := by
    rw [Finset.sum_coe_sort]
    calc
      _≤∑ a : SliceComponent F N R, CX a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _=∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
          (budgets.unit g).toPrimeFlagBudgetFamily.weightedCost first C := Fintype.sum_sigma _
      _≤_ := sum_cost_le F N R flag q first hF hFp budgets
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

#print axioms first_cut_all_slices
end
end ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814
