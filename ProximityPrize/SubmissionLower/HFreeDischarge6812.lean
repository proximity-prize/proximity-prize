import ProximityPrize.SubmissionLower.HFreeChar6812
import ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
import ProximityPrize.SubmissionLower.HFreeDefer6812

/-!
Discharge of the H-free stage hypothesis `MovingFiberRetainedStage6811.HFreeStage` through
`HFree6812.hfree_slice_budget`, channel by channel.  One input remains OPEN, isolated as a single
named theorem: `hdefer_gap` (continuity + residual separability at every place of the slice
function field).  `hchar_gap` (pole/zero orders below the characteristic) is proved in
`HFreeChar6812` from the cell's total-degree bound.
-/
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
noncomputable section
set_option autoImplicit false

section Gaps
variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- hdefer: pieces 3 and 4 (`CrudeBound`, `ResiduallySeparable`) at every place of
`L0` over the slice.  Exactly the `hdefer` input of `hfree_slice_budget`. -/
theorem hdefer_gap (F : MvPolynomial (Fin 4) K) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m) (hq1 : i = 1 ∨ q 1 = 0)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N)
    (hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0) :
    ∀ (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
      (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
      (ν : RCN026.Place E (CoordinateField E D)) (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰),
      1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))) :=
  hdefer_holds F D hHD c i hci q hq hq1 hslice N hN hNK

/-- hchar: on a slice component of a surface of total `(Y,Y',Γ)`-degree `≤ N ≤ 9678`, the pole
and zero orders entering the lowest-term argument are below the characteristic (`hchar_holds`).
This is the `hchar` input of `hfree_slice_budget`. -/
theorem hchar_gap [CharP K 2130706433] (F : MvPolynomial (Fin 4) K)
    (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hFD : surfaceMap (phiE K E) F ∈ D) (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N) (hN9 : N ≤ 9678) :
    ∀ ν : RCN026.Place E (CoordinateField E D), ∀ n : ℕ, 0 < n →
      (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0 :=
  hchar_holds F D sep hFD hHD c i hci hslice N hN hN9

end Gaps

section Stage
open MovingFiberRetainedStage6811 CommonLinearChannels6807 LocatorHybridCells
variable {K I : Type} [Field K] [CharP K 2130706433]
  {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  [CharP (GenericField K) 2130706433]

omit [CharP (GenericField K) 2130706433] in
private theorem natCast_ne_zero_K {n : ℕ} (h0 : 0 < n) (hn : n < 2130706433) : (n : K) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

omit [CharP (GenericField K) 2130706433] in
/-- One slice direction: `hfree_slice_budget` fed by the two gaps. -/
private theorem channel_budget {E : Type} [Field E] [IsAlgClosed E]
    [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
    [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
    (F : MvPolynomial (Fin 4) K) (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N)
    (hN9 : N ≤ 9678) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (hFD : surfaceMap (phiE K E) F ∈ D)
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m) (hq1 : i = 1 ∨ q 1 = 0)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D) :
    HFreeFirstSlice6812.HFreeSliceBudget (phiE K E) F D unitAllFlag := by
  have hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0 :=
    fun n h0 hn => natCast_ne_zero_K h0 (by omega)
  exact ⟨hfree_slice_budget F D sep hFD hHD c i hci q hq hslice
    (by exact_mod_cast natCast_ne_zero_K (K := K) (n := 2) (by norm_num) (by norm_num))
    (hchar_gap F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap F D hHD c i hci q hq hq1 hslice N hN hNK)⟩

/-- The H-free stage hypothesis, from `hfree_slice_budget`, `hchar_gap` and the open
`hdefer_gap`.  `htot` holds for every certificate cell (`t ≤ 7501`). -/
theorem hfree_stage_of_gaps {t y r : ℕ}
    (S : RCN159.ResidualStage (polynomialEmbedding K) Gamma x 2130706433 errorCap flag RCN326.w
      (cellSupport t y r)) (htot : (cellSupport t y r).total ≤ 9678) : HFreeStage S := by
  intro hproper hflagChar hmixedRed j D _ sep hFD hsl hHD
  set common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed with hcommon
  obtain ⟨ql, hql⟩ := ReducedCommonLinear6807.original_common_lam_poly S hproper hflagChar hmixedRed
  obtain ⟨qm, hqm⟩ := ReducedCommonLinear6807.original_common_mu_poly S hproper hflagChar hmixedRed
  have go := channel_budget S.F _ S.surface_total_weight htot D sep hFD hHD
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (fun m => by fin_cases m <;> simp) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![0,0,1] : Fin 3 → GenericField K) m) * MvPolynomial.X m :
        MvPolynomial (Fin 3) (GenericField K)) = linearZ := by
      simp [linearZ, Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![1,0,common.lam] 0 rfl ![1,0,ql] (fun m => by fin_cases m <;> simp [hql, hcommon])
      (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![1,0,common.lam] : Fin 3 → GenericField K) m) * MvPolynomial.X m :
        MvPolynomial (Fin 3) (GenericField K)) = linearU common.lam := by
      simp [linearU, Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![common.mu,1,common.mu*common.lam] 1 rfl ![qm,1,qm*ql]
      (fun m => by fin_cases m <;> simp [hql, hqm, hcommon]) (Or.inl rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![common.mu,1,common.mu*common.lam] : Fin 3 → GenericField K) m) *
        MvPolynomial.X m : MvPolynomial (Fin 3) (GenericField K)) = linearA common.mu common.lam := by
      simp [linearA, Fin.sum_univ_three]; ring
    rw [he]; exact hsl
end Stage

end
end ProximityPrize.SubmissionLower.HFree6812
