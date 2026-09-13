/-
UNCOMPILED. All active slice factors, actual Stage multiplicities, and empty
fibres are assembled here. The only geometric point inputs are incidence with
the slice and isolation; GenericSlicePoints6807 constructs both from embeddings.
There is no input CJ, CV, first-cut budget, or joint budget.
-/
import ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807
import ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
import ProximityPrize.SubmissionLower.SmallSliceBudgets6807

namespace ProximityPrize.SubmissionLower.ActiveSliceAssembly6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN007 RCN084 RCN095 RCN134 RCN135 RCN136 RCN156 RCN159
open RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 GenericSlicePoints6807 WeightedSliceAssignment6807
open SmallSliceBudgets6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w

/-- Regularity of the original F forces regularity of the chosen carrier at
an old prime; it is stronger than merely saying the derivative polynomial is
not identically zero. -/
theorem carrier_derivative_not_mem
    (S : Stage K I Gamma x p flag errorCap stageSupport) (C : FirstTailComponent S) :
    MvPolynomial.pderiv (1 : Fin 3) S.G ∉ C.1 := by
  intro hd
  apply RCN312.firstTailComponent_regularity_not_mem S C
  change surfaceMap (polynomialEmbedding K)
    (MvPolynomial.pderiv (2 : Fin 4) S.F) ∈ C.1
  rw [← surfaceMap_pderiv_R]
  obtain ⟨Q,hQ⟩ := S.G_dvd_surface
  rw [hQ,MvPolynomial.pderiv_mul]
  exact C.1.add_mem (C.1.mul_mem_right Q hd)
    (C.1.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) Q)
      (regularComponent_G_mem Ω S.G _ _ C))

/-- This theorem actually constructs the pure-flag budgets and disjoint point
assignment. Repeated components and empty fibres do not add multiplicity. -/
theorem first_cut_on_all_active_slices
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (N : PE) (q : FlagDegree) (hNq : PolynomialInFlag q N)
    (hNpoint : ∀ i, MvPolynomial.eval (embeddingPoint (old i).1 (emb i)) N = 0)
    (hisolated : ∀ i, IsolatedPoint (scalarPolynomialMap Ω E S.G) N
      (scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1)))
      (embeddingPoint (old i).1 (emb i)))
    (hdeg : flag.zOnly+flag.yz+flag.all < p)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all) < p)
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
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ)) :
    (k+1)*(∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤
      flagMixed flag q ((k+1) • firstBaseFlag (w-1) r v z +
        w • SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  classical
  let F := scalarPolynomialMap Ω E S.G
  let A := scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1))
  let R := scalarPolynomialMap Ω E (regularitySurface (polynomialEmbedding K) S.F)
  let point := fun i => embeddingPoint (old i).1 (emb i)
  let mu := fun i => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)
  let J := firstBaseFlag (w-1) r v z
  let V := SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0
  let D1 := (k+1) • J + w • V
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
  have hRpoint (i : T) : MvPolynomial.eval (point i) R ≠ 0 :=
    scalar_eval_ne_zero (old i).1 (emb i) _
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
  let budgets := Classical.choice
    (exists_sliceBudgets F N R flag q hF hFp hNq p hdeg hmix)
  let cost := fun a : SliceComponent F N R =>
    (budgets.unit a.1).toPrimeFlagBudgetFamily.weightedCost D1 a.2
  have hlocal (a : SliceComponent F N R) :
      (k+1)*(∑ i with assign i = a, mu i) ≤ cost a := by
    let T0 := {i : T // assign i = a}
    by_cases hne : Nonempty T0
    · letI : Nonempty T0 := hne
      let old0 := fun i : T0 => old i.1
      let emb0 := fun i : T0 => emb i.1
      have hi0 : Function.Injective (fun i : T0 => embeddingPoint (old0 i).1 (emb0 i)) := by
        intro i j hh
        exact Subtype.ext (hinj hh)
      have hpt (i : T0) : a.2.1 ≤ RingHom.ker
          (MvPolynomial.aeval (embeddingPoint (old0 i).1 (emb0 i)) : PE →ₐ[E] E).toRingHom := by
        have he : assign i.1 = a := i.2
        have hh := hassigned i.1
        rw [he] at hh
        exact hh
      have hcar : F ∈ a.2.1 := a.2.1.mem_of_dvd (activeFactors_spec F N a.1).2.1
        (regularComponent_G_mem E a.1.1 N R a.2)
      let i0 : T0 := Classical.choice hne
      have hAz : A ∉ a.2.1 := by
        have hh := first_tail_not_mem_assigned F N A R point assign hassigned hisolated i0.1
        have he : assign i0.1 = a := i0.2
        rwa [he] at hh
      let unit := budgets.unit a.1
      let CJ := unit.toPrimeFlagBudgetFamily.weightedCost J a.2
      let CV := unit.toPrimeFlagBudgetFamily.weightedCost V a.2
      have hb := ActualWeightedFirstSlice6807.first_cut_on_prime_slice S hproper
        old0 emb0 hi0 a.2.1 (budgets.base a.1 a.2) hpt hcar hAz
        P B U L s k n0 hS hP hBU hUL hdn hB hn (fun i => hlead i.1) hdiv h2 hfact
        r v z hr hv hR hYR hAll CJ CV
        (PureFlagSliceBudget6807.sum_flagPole_le unit a.2 J)
        (PureFlagSliceBudget6807.sum_flagPole_le unit a.2 V)
      have hsum : (∑ i with assign i = a, mu i) = ∑ i : T0, mu i.1 := by
        simpa only [T0,Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset T))
            mu (p := fun i => assign i = a)).symm
      rw [hsum]
      calc
        _ ≤ (k+1)*CJ+w*CV := hb
        _ = cost a := (PureFlagSliceBudget6807.weightedCost_add_smul
          unit a.2 (k+1) w J V).symm
    · have he : (Finset.univ.filter (fun i : T => assign i = a)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hne ⟨⟨i,(Finset.mem_filter.mp hi).2⟩⟩
      simp only [he,Finset.sum_empty,Nat.mul_zero,Nat.zero_le]
  calc
    _ ≤ ∑ a : SliceComponent F N R, cost a := sum_local_slice_bounds assign mu cost (k+1) hlocal
    _ = ∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
        (budgets.unit g).toPrimeFlagBudgetFamily.weightedCost D1 C := by
      rw [Fintype.sum_sigma]
    _ ≤ flagMixed flag q D1 := sum_cost_le F N R flag q D1 hF hFp budgets
end
end ProximityPrize.SubmissionLower.ActiveSliceAssembly6807
