import ProximityPrize.SubmissionLower.LocatorDerivativeDegreeCaps6803

/-!
# One terminal product for all derivative tails

The old derivative-chain cover counted one `R`-free tail for every positive
factor, and then counted the already `R`-free factors once more.  Here those
polynomials are multiplied before counting.  Their union of seed sets is
therefore contained in the zero set of one nonzero, `R`-free polynomial.
-/

namespace ProximityPrize.SubmissionLower.LocatorAggregateTerminalProduct6803

open scoped Classical BigOperators
open RCN071 RCN081 RCN082 RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN156
  RCN167 RCN174 RCN234 RCN267 RCN313 RCN319
open LocatorDerivativeChain LocatorDerivativeWeightDescent6803
  LocatorDerivativeDegreeCaps6803 LocatorFactorAggregate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- The original factors before differentiating the positive-`R` part. -/
def terminalOriginalProduct (Q : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  rfreeProduct Q * ∏ F ∈ positiveRFactors Q, F

/-- Replace every positive-`R` factor by its terminal derivative. -/
def aggregateTerminalProduct (Q : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  rfreeProduct Q * ∏ F ∈ positiveRFactors Q, dR (chainLength F) F

/-- The single seed set which will replace every factor tail and the
separate `rfreeSeeds` population. -/
def aggregateTerminalSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun gamma ↦ specialization K (selected gamma) gamma
    (aggregateTerminalProduct Q) = 0

theorem terminalOriginalProduct_eq_activeProduct
    (Q : MvPolynomial (Fin 4) K) :
    terminalOriginalProduct Q = ∏ F ∈ activeFactors Q, F := by
  classical
  simp only [terminalOriginalProduct, rfreeProduct, positiveRFactors,
    Nat.pos_iff_ne_zero]
  exact Finset.prod_filter_mul_prod_filter_not (activeFactors Q)
    (fun F ↦ F.degreeOf (2 : Fin 4) = 0) id

theorem terminalOriginalProduct_dvd
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    terminalOriginalProduct Q ∣ Q := by
  rw [terminalOriginalProduct_eq_activeProduct]
  exact activeFactors_product_dvd Q hQ

theorem aggregateTerminalProduct_ne_zero
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p) :
    aggregateTerminalProduct Q ≠ 0 := by
  classical
  apply mul_ne_zero (rfreeProduct_ne_zero Q hQ)
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  have hspec := positiveRFactors_spec Q F hF
  have hFsmall : F.degreeOf (2 : Fin 4) < p :=
    (RCN081.degreeOf_le_of_dvd (2 : Fin 4) F Q hspec.2.1 hQ).trans_lt hsmall
  exact dR_ne_zero F hspec.1.ne_zero p hFsmall (chainLength F) le_rfl

theorem aggregateTerminalProduct_R_degree
    (Q : MvPolynomial (Fin 4) K) :
    (aggregateTerminalProduct Q).degreeOf (2 : Fin 4) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (MvPolynomial.degreeOf_mul_le (2 : Fin 4)
    (rfreeProduct Q)
    (∏ F ∈ positiveRFactors Q, dR (chainLength F) F)).trans
  rw [rfreeProduct_R_degree, Nat.zero_add]
  apply (MvPolynomial.degreeOf_prod_le (2 : Fin 4)
    (positiveRFactors Q) (fun F ↦ dR (chainLength F) F)).trans
  simp only [chainLength_spec, Finset.sum_const_zero, le_refl]

/-- Differentiating each positive factor pays for its own chain length before
the factors are multiplied.  This generic form is used with the middle and
total cumulative weights. -/
theorem aggregateTerminalProduct_weight_add_chainLength_le
    (weights : Fin 4 → ℕ) (hweight : weights (2 : Fin 4) = 1)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hchainWeight : ∀ F ∈ positiveRFactors Q,
      chainLength F ≤ wt weights F) :
    wt weights (aggregateTerminalProduct Q) +
        ∑ F ∈ positiveRFactors Q, chainLength F ≤
      wt weights Q := by
  classical
  have hrfree := rfreeProduct_ne_zero Q hQ
  have hfactor : ∀ F ∈ positiveRFactors Q, F ≠ 0 := by
    intro F hF
    exact (positiveRFactors_spec Q F hF).1.ne_zero
  have hterminal : ∀ F ∈ positiveRFactors Q,
      dR (chainLength F) F ≠ 0 := by
    intro F hF
    have hspec := positiveRFactors_spec Q F hF
    have hFsmall : F.degreeOf (2 : Fin 4) < p :=
      (RCN081.degreeOf_le_of_dvd (2 : Fin 4) F Q hspec.2.1 hQ).trans_lt
        hsmall
    exact dR_ne_zero F hspec.1.ne_zero p hFsmall (chainLength F) le_rfl
  have hterminalProd :
      (∏ F ∈ positiveRFactors Q, dR (chainLength F) F) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hterminal
  have hfactorProd : (∏ F ∈ positiveRFactors Q, F) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor
  have haggregateWeight : wt weights (aggregateTerminalProduct Q) =
      wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights (dR (chainLength F) F) := by
    unfold aggregateTerminalProduct
    have hraw : MvPolynomial.weightedTotalDegree weights
        (rfreeProduct Q *
          ∏ F ∈ positiveRFactors Q, dR (chainLength F) F) =
        MvPolynomial.weightedTotalDegree weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            MvPolynomial.weightedTotalDegree weights
              (dR (chainLength F) F) := by
      rw [weightedTotalDegree_mul weights _ _ hrfree hterminalProd,
        RCN071.weightedTotalDegree_prod_eq weights (positiveRFactors Q)
          (fun F ↦ dR (chainLength F) F) hterminal]
    simpa only [RCN234.wt] using hraw
  have horiginalWeight : wt weights (terminalOriginalProduct Q) =
      wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights F := by
    unfold terminalOriginalProduct
    have hraw : MvPolynomial.weightedTotalDegree weights
        (rfreeProduct Q * ∏ F ∈ positiveRFactors Q, F) =
        MvPolynomial.weightedTotalDegree weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            MvPolynomial.weightedTotalDegree weights F := by
      rw [weightedTotalDegree_mul weights _ _ hrfree hfactorProd,
        RCN071.weightedTotalDegree_prod_eq weights (positiveRFactors Q)
          (fun F ↦ F) hfactor]
    simpa only [RCN234.wt] using hraw
  have hsum :
      (∑ F ∈ positiveRFactors Q, wt weights (dR (chainLength F) F)) +
          ∑ F ∈ positiveRFactors Q, chainLength F ≤
        ∑ F ∈ positiveRFactors Q, wt weights F := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro F hF
    have hdesc := dR_wt_le_sub weights hweight F (chainLength F)
      (wt weights F) le_rfl
    have hlen := hchainWeight F hF
    omega
  rw [haggregateWeight]
  calc
    (wt weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            wt weights (dR (chainLength F) F)) +
        ∑ F ∈ positiveRFactors Q, chainLength F =
      wt weights (rfreeProduct Q) +
        ((∑ F ∈ positiveRFactors Q,
            wt weights (dR (chainLength F) F)) +
          ∑ F ∈ positiveRFactors Q, chainLength F) := by omega
    _ ≤ wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights F :=
      Nat.add_le_add_left hsum _
    _ = wt weights (terminalOriginalProduct Q) := horiginalWeight.symm
    _ ≤ wt weights Q := weightedTotalDegree_le_of_dvd weights
      (terminalOriginalProduct Q) Q (terminalOriginalProduct_dvd Q hQ) hQ

/-- Scaled terminal descent.  This records the full weight of the eliminated
`R` exponent, and is therefore useful for contact weights where `R` has
weight `w - 1`. -/
theorem aggregateTerminalProduct_weight_add_scaledChainLength_le
    (weights : Fin 4 → ℕ) (r : ℕ)
    (hweight : weights (2 : Fin 4) = r)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hchainWeight : ∀ F ∈ positiveRFactors Q,
      r * chainLength F ≤ wt weights F) :
    wt weights (aggregateTerminalProduct Q) +
        r * (∑ F ∈ positiveRFactors Q, chainLength F) ≤
      wt weights Q := by
  classical
  have hrfree := rfreeProduct_ne_zero Q hQ
  have hfactor : ∀ F ∈ positiveRFactors Q, F ≠ 0 := by
    intro F hF
    exact (positiveRFactors_spec Q F hF).1.ne_zero
  have hterminal : ∀ F ∈ positiveRFactors Q,
      dR (chainLength F) F ≠ 0 := by
    intro F hF
    have hspec := positiveRFactors_spec Q F hF
    have hFsmall : F.degreeOf (2 : Fin 4) < p :=
      (RCN081.degreeOf_le_of_dvd (2 : Fin 4) F Q hspec.2.1 hQ).trans_lt
        hsmall
    exact dR_ne_zero F hspec.1.ne_zero p hFsmall (chainLength F) le_rfl
  have hterminalProd :
      (∏ F ∈ positiveRFactors Q, dR (chainLength F) F) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hterminal
  have hfactorProd : (∏ F ∈ positiveRFactors Q, F) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor
  have haggregateWeight : wt weights (aggregateTerminalProduct Q) =
      wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights (dR (chainLength F) F) := by
    unfold aggregateTerminalProduct
    have hraw : MvPolynomial.weightedTotalDegree weights
        (rfreeProduct Q *
          ∏ F ∈ positiveRFactors Q, dR (chainLength F) F) =
        MvPolynomial.weightedTotalDegree weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            MvPolynomial.weightedTotalDegree weights
              (dR (chainLength F) F) := by
      rw [weightedTotalDegree_mul weights _ _ hrfree hterminalProd,
        RCN071.weightedTotalDegree_prod_eq weights (positiveRFactors Q)
          (fun F ↦ dR (chainLength F) F) hterminal]
    simpa only [RCN234.wt] using hraw
  have horiginalWeight : wt weights (terminalOriginalProduct Q) =
      wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights F := by
    unfold terminalOriginalProduct
    have hraw : MvPolynomial.weightedTotalDegree weights
        (rfreeProduct Q * ∏ F ∈ positiveRFactors Q, F) =
        MvPolynomial.weightedTotalDegree weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            MvPolynomial.weightedTotalDegree weights F := by
      rw [weightedTotalDegree_mul weights _ _ hrfree hfactorProd,
        RCN071.weightedTotalDegree_prod_eq weights (positiveRFactors Q)
          (fun F ↦ F) hfactor]
    simpa only [RCN234.wt] using hraw
  have hsum :
      (∑ F ∈ positiveRFactors Q, wt weights (dR (chainLength F) F)) +
          ∑ F ∈ positiveRFactors Q, r * chainLength F ≤
        ∑ F ∈ positiveRFactors Q, wt weights F := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro F hF
    have hdesc := dR_wt_le_sub_mul weights r hweight F (chainLength F)
      (wt weights F) le_rfl
    rw [Nat.mul_comm (chainLength F) r] at hdesc
    have hlen := hchainWeight F hF
    omega
  rw [haggregateWeight, Finset.mul_sum]
  calc
    (wt weights (rfreeProduct Q) +
          ∑ F ∈ positiveRFactors Q,
            wt weights (dR (chainLength F) F)) +
        ∑ F ∈ positiveRFactors Q, r * chainLength F =
      wt weights (rfreeProduct Q) +
        ((∑ F ∈ positiveRFactors Q,
            wt weights (dR (chainLength F) F)) +
          ∑ F ∈ positiveRFactors Q, r * chainLength F) := by omega
    _ ≤ wt weights (rfreeProduct Q) +
        ∑ F ∈ positiveRFactors Q, wt weights F :=
      Nat.add_le_add_left hsum _
    _ = wt weights (terminalOriginalProduct Q) := horiginalWeight.symm
    _ ≤ wt weights Q := weightedTotalDegree_le_of_dvd weights
      (terminalOriginalProduct Q) Q (terminalOriginalProduct_dvd Q hQ) hQ

theorem degreeOf_mul_coordinateWeight_le_wt
    (weights : Fin 4 → ℕ) (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (i : Fin 4) :
    F.degreeOf i * weights i ≤ wt weights F := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup]
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF) (fun e ↦ e i)
  rw [heq]
  have hweight := MvPolynomial.le_weightedTotalDegree weights hd
  rw [RCN081.weight_fin4] at hweight
  change d i * weights i ≤ MvPolynomial.weightedTotalDegree weights F
  fin_cases i
  · change d 0 * weights 0 ≤ MvPolynomial.weightedTotalDegree weights F
    omega
  · change d 1 * weights 1 ≤ MvPolynomial.weightedTotalDegree weights F
    omega
  · change d 2 * weights 2 ≤ MvPolynomial.weightedTotalDegree weights F
    omega
  · change d 3 * weights 3 ≤ MvPolynomial.weightedTotalDegree weights F
    omega

/-- Contact weight drops by `w - 1` for every derivative taken before the
terminal factors are multiplied. -/
theorem aggregateTerminalProduct_contact_add_scaledChainLength_le
    (w : ℕ) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p) :
    wt (contactWeights w) (aggregateTerminalProduct Q) +
        (w - 1) * (∑ F ∈ positiveRFactors Q, chainLength F) ≤
      wt (contactWeights w) Q := by
  apply aggregateTerminalProduct_weight_add_scaledChainLength_le
    (contactWeights w) (w - 1) (by simp [contactWeights]) Q hQ p hsmall
  intro F hF
  have hlen := chainLength_le F
  calc
    (w - 1) * chainLength F ≤ (w - 1) * F.degreeOf (2 : Fin 4) :=
      Nat.mul_le_mul_left (w - 1) hlen
    _ = F.degreeOf (2 : Fin 4) * (contactWeights w) (2 : Fin 4) := by
      simp [contactWeights, Nat.mul_comm]
    _ ≤ wt (contactWeights w) F :=
      degreeOf_mul_coordinateWeight_le_wt (contactWeights w) F
        (positiveRFactors_spec Q F hF).1.ne_zero 2

theorem positiveFactors_chainLength_sum_pos
    (Q : MvPolynomial (Fin 4) K)
    (hpositive : (positiveRFactors Q).Nonempty) :
    1 ≤ ∑ F ∈ positiveRFactors Q, chainLength F := by
  obtain ⟨F, hF⟩ := hpositive
  exact (chainLength_pos F (positiveRFactors_spec Q F hF).2.2).trans
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hF)

theorem aggregateTerminalProduct_contact_le_sub
    (w : ℕ) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty) :
    wt (contactWeights w) (aggregateTerminalProduct Q) ≤
      wt (contactWeights w) Q - (w - 1) := by
  have hmain := aggregateTerminalProduct_contact_add_scaledChainLength_le
    w Q hQ p hsmall
  have hsum := positiveFactors_chainLength_sum_pos Q hpositive
  have hscaled : w - 1 ≤
      (w - 1) * (∑ F ∈ positiveRFactors Q, chainLength F) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (w - 1) hsum
  omega

theorem aggregateTerminalProduct_middle_add_chainLength_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p) :
    wt residualYSWeights (aggregateTerminalProduct Q) +
        ∑ F ∈ positiveRFactors Q, chainLength F ≤
      wt residualYSWeights Q := by
  apply aggregateTerminalProduct_weight_add_chainLength_le
    residualYSWeights rfl Q hQ p hsmall
  intro F hF
  rw [← show middle (originalCumulativeFlag F) = wt residualYSWeights F by
    simpa [middle] using (originalCumulativeFlag_cumulative F).2.1]
  have hdegree := degreeR_le_allCumulative F
  have hlength := chainLength_le F
  change chainLength F ≤
    (originalCumulativeFlag F).yz + (originalCumulativeFlag F).all
  omega

theorem aggregateTerminalProduct_total_add_chainLength_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p) :
    wt residualTotalWeights (aggregateTerminalProduct Q) +
        ∑ F ∈ positiveRFactors Q, chainLength F ≤
      wt residualTotalWeights Q := by
  apply aggregateTerminalProduct_weight_add_chainLength_le
    residualTotalWeights rfl Q hQ p hsmall
  intro F hF
  rw [← show total (originalCumulativeFlag F) = wt residualTotalWeights F by
    simpa [total] using (originalCumulativeFlag_cumulative F).2.2]
  have hdegree := degreeR_le_allCumulative F
  have hlength := chainLength_le F
  change chainLength F ≤ (originalCumulativeFlag F).zOnly +
    (originalCumulativeFlag F).yz + (originalCumulativeFlag F).all
  omega

theorem aggregateTerminalProduct_middle_le_sub
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty) :
    wt residualYSWeights (aggregateTerminalProduct Q) ≤
      wt residualYSWeights Q - 1 := by
  have hmain := aggregateTerminalProduct_middle_add_chainLength_le
    Q hQ p hsmall
  have hsum := positiveFactors_chainLength_sum_pos Q hpositive
  omega

theorem aggregateTerminalProduct_total_le_sub
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty) :
    wt residualTotalWeights (aggregateTerminalProduct Q) ≤
      wt residualTotalWeights Q - 1 := by
  have hmain := aggregateTerminalProduct_total_add_chainLength_le
    Q hQ p hsmall
  have hsum := positiveFactors_chainLength_sum_pos Q hpositive
  omega

theorem seedWeight_le_residualTotalWeight
    (F : MvPolynomial (Fin 4) K) :
    wt seedWeights F ≤ wt residualTotalWeights F := by
  change MvPolynomial.weightedTotalDegree seedWeights F ≤
    MvPolynomial.weightedTotalDegree residualTotalWeights F
  apply (weightedTotalDegree_le_iff seedWeights F _).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [RCN081.weight_fin4] at h
  rw [RCN081.weight_fin4]
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    MvPolynomial.weightedTotalDegree residualTotalWeights F at h
  change d 0 * 0 + d 1 * 1 + d 2 * 0 + d 3 * 1 ≤
    MvPolynomial.weightedTotalDegree residualTotalWeights F
  norm_num at h ⊢
  omega

/-- The single terminal product lies in one ordinary tail box.  The contact
cap spends `w - 1`, and the seed-total cap spends one, whenever a positive
factor (hence a derivative chain) is present. -/
theorem aggregateTerminalProduct_mem_tail_box
    (w contactCap totalCap : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty)
    (hcontact : wt (contactWeights w) Q ≤ contactCap)
    (htotal : wt residualTotalWeights Q ≤ totalCap) :
    aggregateTerminalProduct Q ∈ globalCoefficientBox K
      (contactCap - (w - 1) + 1) w (totalCap - 1) 1 := by
  apply (mem_globalCoefficientBox_iff (aggregateTerminalProduct Q)
    (contactCap - (w - 1) + 1) w (totalCap - 1) 1 (by omega)).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact (seedWeight_le_residualTotalWeight (aggregateTerminalProduct Q)).trans
      ((aggregateTerminalProduct_total_le_sub Q hQ p hsmall hpositive).trans
        (Nat.sub_le_sub_right htotal 1))
  · have hslope : slopeWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> simp [slopeWeights, Pi.single_apply]
    rw [hslope, MvPolynomial.weightedTotalDegree_piSingle]
    rw [aggregateTerminalProduct_R_degree]
    omega
  · have h := (aggregateTerminalProduct_contact_le_sub
      w Q hQ p hsmall hpositive).trans
        (Nat.sub_le_sub_right hcontact (w - 1))
    change MvPolynomial.weightedTotalDegree (contactWeights w)
      (aggregateTerminalProduct Q) ≤ contactCap - (w - 1) at h
    simpa only [Nat.add_sub_cancel] using h

theorem tailSeeds_subset_aggregateTerminalSeeds
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    tailSeeds F selected Gamma ⊆
      aggregateTerminalSeeds Q selected Gamma := by
  intro gamma hgamma
  have hdata := Finset.mem_filter.mp hgamma
  apply Finset.mem_filter.mpr
  refine ⟨hdata.1, ?_⟩
  unfold aggregateTerminalProduct
  rw [map_mul]
  apply mul_eq_zero_of_right
  rw [map_prod]
  apply Finset.prod_eq_zero hF
  exact hdata.2

theorem rfreeSeeds_subset_aggregateTerminalSeeds
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    rfreeSeeds Q selected Gamma ⊆
      aggregateTerminalSeeds Q selected Gamma := by
  intro gamma hgamma
  have hdata := Finset.mem_filter.mp hgamma
  apply Finset.mem_filter.mpr
  refine ⟨hdata.1, ?_⟩
  unfold aggregateTerminalProduct
  rw [map_mul, hdata.2, zero_mul]

theorem all_tailSeeds_subset_aggregateTerminalSeeds
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    ((positiveRFactors Q).biUnion fun F ↦ tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma ⊆
      aggregateTerminalSeeds Q selected Gamma := by
  intro gamma hgamma
  rcases Finset.mem_union.mp hgamma with htail | hrfree
  · obtain ⟨F, hF, hgammaF⟩ := Finset.mem_biUnion.mp htail
    exact tailSeeds_subset_aggregateTerminalSeeds Q selected Gamma F hF hgammaF
  · exact rfreeSeeds_subset_aggregateTerminalSeeds Q selected Gamma hrfree

end

end ProximityPrize.SubmissionLower.LocatorAggregateTerminalProduct6803
