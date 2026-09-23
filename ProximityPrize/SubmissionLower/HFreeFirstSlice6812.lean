/-
H-free first cut. The only new input is `HFreeSliceBudget`; it replaces the
first-cut local pole bound, and everything else reuses the 6807 chain.
-/
import ProximityPrize.SubmissionLower.ActiveSliceAssembly6807

namespace ProximityPrize.SubmissionLower.HFreeFirstSlice6812
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" => RCN326.w

/-- The H-free first-cut flag: `2(w+1)` copies of the flag `⟨z,v,r-1⟩` of `H = ∂F/∂Y'`
(`boundary_surfaceMap_flags`) and `3` copies of the constant flag `C0`. -/
def hfreeFlag (r v z : ℕ) (C0 : FlagDegree) : FlagDegree :=
  (2*(w+1)) • (⟨z,v,r-1⟩ : FlagDegree) + 3 • C0

section Slice
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

/-- **The H-free per-slice pole budget (hypothesis).**
`C` is a prime of `E[Y,Y',Γ]` (coordinates `0,1,2`) with function field
`L = CoordinateField E C`; `ν` ranges over `Place E L` (normalized valuations of `L`
trivial on `E`); `ev = coefficientMap phi C`; `H = ev (∂F/∂Y')`, `G = ev (polyG F)`.
With `τ = ev (baseNumerator F (w-1)) / H^(2w-1)` (`= Y^(w+1)`), for every finite `W`:
`3·Σ_{ν∈W} pole_ν τ ≤ Σ_{ν∈W} [(w+1)·(4·T_ν + 2·zero_ν H) + 3·flagPole_ν C0]`,
where `pole_ν = RCN187.poleOrder` (`max 0 (log ν ·)`), `T_ν = RCN064.movingPoleTarget`
`= max (2·max(p Y, p Y', p Γ)) (max(p Y, p Γ) + p(G/H))`, and
`zero_ν H = RCN026.zeroOrder = max 0 (ord_ν H)`.
It is the per-place bound `3·pole_ν τ ≤ (w+1)(4T_ν + 2 ord⁺_ν H) + 3c_ν`,
`c_ν ≤ flagPole_ν C0`, summed over `W`. -/
structure HFreeSliceBudget (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 : FlagDegree) : Prop where
  pole_le : ∀ W : Finset (Place E (CoordinateField E C)),
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F))) +
      3*flagPole nu.val (coordinate E C) C0)

/-- H6: the H-free analogue of `FirstSlicePoleBudget6807.actual_first_source_pole_mass`. -/
theorem hfree_source_pole_mass
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (r v z : ℕ) (hr : 2 ≤ r) (hv : 1 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hbudget : HFreeSliceBudget phi F C C0) (CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C) (hfreeFlag r v z C0)) ≤ (CX : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((3*(k+1) : ℕ) : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      ((k+1 : ℕ) : ℤ)*(CX : ℤ)+((4*(w+1) : ℕ) : ℤ)*(CV : ℤ) := by
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
  -- the moving mass, exactly as in `actual_first_source_pole_mass`
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hVbudget W
  have hsource : ((k+1 : ℕ) : ℤ)*(∑ nu ∈ W, theta nu) ≤ (CV : ℤ) := by
    simpa only [SecondJetPoleScaling.pole_half _ h2, theta, sigma, H, ev,
      SecondJetComponentRoots.coefficientMap, RCN064.movingRatio,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hs
  have htarget : (∑ nu ∈ W, RCN064.movingPoleTarget C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu) = ∑ nu ∈ W, theta nu := by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta, RCN204.flagPole_unitAll, RCN204.flagPole_unitYZ]
    rfl
  -- zeros of `H` are bounded by its poles, hence by its flag
  let Pl := RCN026.placesFor E L H hHne
  have hHF := (BoundaryTailAlgebra.boundary_surfaceMap_flags phi F r v z hr hv hR hYR hAll).1
  have hpoleH (nu : Place E L) :
      RCN346.poleOrder E L nu H ≤ flagPole nu.val (coordinate E C) Hf := by
    apply pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E L)
      (RCN344.constant_value_le_one E L nu) (coordinate E C) Hf _ hHF
    simpa only [H, ev, SecondJetComponentRoots.coefficientMap,
      coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hzero : (∑ nu ∈ W, RCN026.zeroOrder E L nu H) ≤
      ∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf := by
    have hout : ∀ nu ∈ W.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H = 0 := by
      intro nu hnu
      have hno : RCN026.order E L nu H = 0 := by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.placesFor_covers E L H hHne nu hne)
      simp only [RCN026.zeroOrder, hno, max_self]
    calc
      _ = (∑ nu ∈ W.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H) +
          ∑ nu ∈ W.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H :=
        (Finset.sum_filter_add_sum_filter_not W _ _).symm
      _ = ∑ nu ∈ W.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H := by
        rw [Finset.sum_eq_zero hout, add_zero]
      _ ≤ ∑ nu ∈ Pl, RCN026.zeroOrder E L nu H :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu => (Finset.mem_filter.mp hnu).2)
          (fun nu _ _ => RCN026.zeroOrder_nonneg E L nu H)
      _ = ∑ nu ∈ Pl, RCN346.poleOrder E L nu H := RCN026.sum_placesFor_zero_eq_pole E L H hHne
      _ ≤ _ := Finset.sum_le_sum (fun nu _ => hpoleH nu)
  -- the X-budget on `W ∪ Pl` covers both the `H` and the `C0` parts
  have hX := hXbudget (W ∪ Pl)
  have hXsplit : 2*((w+1 : ℕ) : ℤ)*(∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf) +
      3*(∑ nu ∈ W, flagPole nu.val (coordinate E C) C0) ≤ (CX : ℤ) := by
    refine le_trans ?_ hX
    simp only [hfreeFlag, RCN204.flagPole_add, RCN204.flagPole_nsmul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := W) (s₂ := Pl))
      (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) Hf)
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left (s₁ := W) (s₂ := Pl))
      (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) C0)
    push_cast
    nlinarith
  have hb := hbudget.pole_le W
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  rw [htarget] at hb
  push_cast at hb hsource ⊢
  have hk : (0 : ℤ) ≤ (k : ℤ)+1 := by positivity
  have hw : (0 : ℤ) ≤ (w : ℤ)+1 := by positivity
  have e1 := mul_le_mul_of_nonneg_left hb hk
  have e2 := mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num : (0 : ℤ) ≤ 4) hw)
  have e3 := mul_le_mul_of_nonneg_left hzero (mul_nonneg hk (mul_nonneg (by norm_num : (0 : ℤ) ≤ 2) hw))
  have e4 := mul_le_mul_of_nonneg_left hXsplit hk
  push_cast at e4
  nlinarith

end Slice

section Stage
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)

/-- H7: the H-free analogue of `ActualWeightedFirstSlice6807.first_cut_on_prime_slice`;
the counted function is `τ` itself (denominator `c*H^(2w+2)`). -/
theorem first_cut_on_prime_slice_hfree [Fintype T] [Nonempty T]
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D)
    (hisolated : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (w+1)) ∉ D)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hlead : ∀ i, surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff ∉ (old i).1)
    (hdiv : ∀ j ≤ k, S.F ∣ helper P S.F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree)
    (hbudget : surfaceMap φE S.F ∈ D → surfaceMap φE (polyH K S.F) ∉ D →
      HFreeSliceBudget φE S.F D C0)
    (CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D) (hfreeFlag r v z C0)) ≤ (CX : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D)
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)) ≤ (CV : ℤ)) :
    3*(k+1) * (∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤
      (k+1)*CX+4*(w+1)*CV := by
  apply ActualWeightedFirstSlice6807.first_cut_on_prime_slice_of S hproper old emb hinj D sep
    hpoint hcarrier hisolated (2*w-1) (3*(k+1)) ((k+1)*CX+4*(w+1)*CV)
  intro hFd hHd hnot W
  have hs := hfree_source_pole_mass φE S.F D sep P B U L s k n0 hS hP hBU hUL hdn hB hn
    hFd hHd (hnot _ hlead) hdiv h2 hfact r v z (by omega) (by omega) hR hYR hAll C0
    (hbudget hFd hHd) CX CV hXbudget hVbudget W
  simpa only [Nat.cast_add, Nat.cast_mul] using hs

variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- The H-free hypothesis for one slice direction `ell`: every prime slice component
`D ∋ F, T-ell` with `H ∉ D` carries an `HFreeSliceBudget`. -/
def HFreeChannel (F : MvPolynomial (Fin 4) K) (ell : MvPolynomial (Fin 3) Ω)
    (C0 : FlagDegree) : Prop :=
  ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
    surfaceMap φE F ∈ D → GenericSlicePoints6807.sliceEquation (E := E) ell ∈ D →
    surfaceMap φE (polyH K F) ∉ D → HFreeSliceBudget φE F D C0

/-- H8 glue: the H-free per-slice charge `3(k+1) | (k+1)•hfreeFlag + 4(w+1)•V`. -/
theorem hfree_slice_charge
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (ell : MvPolynomial (Fin 3) Ω)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, S.F ∣ helper P S.F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hH : HFreeChannel (E := E) S.F ell C0) :
    ActiveSliceAssembly6807.SliceCharge (E := E) S hproper
      (fun C => surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff ∉ C.1)
      (GenericSlicePoints6807.sliceEquation (E := E) ell) (3*(k+1)) (k+1) (4*(w+1))
      (hfreeFlag r v z C0) (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) :=
  fun _ _ _ old hlead emb hinj D _ sep hpt hcar hN hA CX CV hX hV =>
    first_cut_on_prime_slice_hfree S hproper old emb hinj D sep hpt hcar hA
      P B U L s k n0 hS hP hBU hUL hdn hB hn hlead hdiv h2 hfact r v z hr hv hR hYR hAll C0
      (fun hFd hHd => hH D sep hFd hN hHd) CX CV hX hV

end Stage
end
end ProximityPrize.SubmissionLower.HFreeFirstSlice6812
