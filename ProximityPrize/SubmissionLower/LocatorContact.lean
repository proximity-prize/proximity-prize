import ProximityPrize.SubmissionLower.ContactOrderBridge
import ProximityPrize.SubmissionLower.L1

/-!
Locator-weighted differentiation for the whole contact kernel.

The reverse contact-to-kernel bridge below uses the original C1 constraint
map, not a relaxed interpolation condition. Multiplication by the full node
locator compensates the contact-order loss of R differentiation. Its X
degree costs weighted-degree slack but does not consume the Y/R/Z total cap.

These are new 67.36 source proofs, pending local compilation. They introduce
no regularity or higher-specialized-derivative assumptions.
-/
namespace ProximityPrize.SubmissionLower.LocatorContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122
open RCN156 RCN180 RCN234 RCN313
open ContactOrderBridge

noncomputable section

variable {K I : Type*} [Field K] [Fintype I]
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

theorem mem_kernel_of_contactAtLeast
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (a : CoefficientIndex D w L s → K)
    (ha : ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (reconstruct K D w L s a)) :
    a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) := by
  classical
  apply LinearMap.mem_ker.mpr
  funext i r
  apply Subtype.ext
  change contactJet K (m - r.val)
    ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val a) : Poly K) = 0
  apply (contactJet_eq_zero_iff K (m - r.val) _).mpr
  rw [← translation_reconstruct_coeff K D w L s (nodes i) (u0 i) (u1 i) a r.val]
  exact (contactAtLeast_iff_block_divisibility K (nodes i) (u0 i) (u1 i) m
    (reconstruct K D w L s a)).mp (ha i) r.val

theorem mem_kernel_iff_contactAtLeast
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (a : CoefficientIndex D w L s → K) :
    a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ↔
      ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
        (reconstruct K D w L s a) := by
  constructor
  · intro ha i
    exact contactAtLeast_of_mem_kernel K D w L s m nodes u0 u1 a ha i
  · exact mem_kernel_of_contactAtLeast D w L s m nodes u0 u1 a

theorem exists_kernel_array_of_box_of_contact
    (D w L s m : ℕ) (nodes u0 u1 : I → K) (Q : P4 K)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcontact : ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m Q) :
    ∃ a : CoefficientIndex D w L s → K,
      a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ∧
        reconstruct K D w L s a = Q := by
  let qbox : globalCoefficientBox K D w L s := ⟨Q, hbox⟩
  let a : CoefficientIndex D w L s → K := encodeBox qbox
  have heq : reconstruct K D w L s a = Q := reconstruct_encodeBox qbox
  refine ⟨a, ?_, heq⟩
  apply mem_kernel_of_contactAtLeast D w L s m nodes u0 u1 a
  intro i
  rw [heq]
  exact hcontact i

def nodeFactor (x : K) : P4 K := MvPolynomial.X 0 - MvPolynomial.C x

def locator (nodes : I → K) : P4 K := ∏ i : I, nodeFactor (nodes i)

theorem nodeFactor_ne_zero (x : K) : nodeFactor x ≠ 0 := by
  classical
  intro hz
  have hsingle : (Finsupp.single (0 : Fin 4) 1 : Fin 4 →₀ ℕ) ≠ 0 := by
    intro hs
    have h := congrArg (fun d : Fin 4 →₀ ℕ => d 0) hs
    simpa using h
  have h := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 4) 1)) hz
  simpa [nodeFactor, MvPolynomial.coeff_C, hsingle.symm] using h

theorem locator_ne_zero (nodes : I → K) : locator nodes ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact nodeFactor_ne_zero (nodes i)

theorem nodeFactor_wt_le (weights : Fin 4 → ℕ) (x : K) :
    wt weights (nodeFactor x) ≤ weights 0 := by
  have h := wt_sub_le weights (MvPolynomial.X (0 : Fin 4) : P4 K)
    (MvPolynomial.C x)
  simpa only [nodeFactor, wt_X, wt_C, Nat.max_zero] using h

private theorem wt_prod_le_sum (weights : Fin 4 → ℕ) (J : Finset I)
    (f : I → P4 K) :
    wt weights (∏ i ∈ J, f i) ≤ ∑ i ∈ J, wt weights (f i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      simpa only [Nat.cast_one] using (wt_natCast (K := K) weights 1).le
  | @insert i J hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (wt_mul_le weights (f i) (∏ j ∈ J, f j)).trans
        (Nat.add_le_add_left ih _)

theorem locator_wt_le (weights : Fin 4 → ℕ) (nodes : I → K) :
    wt weights (locator nodes) ≤ Fintype.card I * weights 0 := by
  classical
  calc
    wt weights (locator nodes) ≤ ∑ i : I, wt weights (nodeFactor (nodes i)) :=
      wt_prod_le_sum weights Finset.univ (fun i => nodeFactor (nodes i))
    _ ≤ ∑ _i : I, weights 0 :=
      Finset.sum_le_sum (fun i _ => nodeFactor_wt_le weights (nodes i))
    _ = Fintype.card I * weights 0 := by simp

theorem locator_contact_weight_le (nodes : I → K) (w : ℕ) :
    wt (contactWeights w) (locator nodes) ≤ Fintype.card I := by
  simpa [contactWeights] using locator_wt_le (contactWeights w) nodes

theorem locator_total_weight_zero (nodes : I → K) :
    wt residualTotalWeights (locator nodes) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [residualTotalWeights] using locator_wt_le residualTotalWeights nodes

theorem locator_slope_weight_zero (nodes : I → K) :
    wt residualSWeights (locator nodes) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [residualSWeights] using locator_wt_le residualSWeights nodes

theorem slope_weight_eq_degreeR (Q : P4 K) :
    wt residualSWeights Q = Q.degreeOf (2 : Fin 4) := by
  change Q.support.sup (Finsupp.weight residualSWeights) = Q.degreeOf (2 : Fin 4)
  rw [MvPolynomial.degreeOf_eq_sup]
  apply congrArg (fun f : (Fin 4 →₀ ℕ) → ℕ => Q.support.sup f)
  funext d
  rw [weight_fin4]
  simp [residualSWeights]

theorem locator_degreeR (nodes : I → K) :
    (locator nodes).degreeOf (2 : Fin 4) = 0 := by
  rw [← slope_weight_eq_degreeR]
  exact locator_slope_weight_zero nodes

theorem nodeFactor_contactAtLeast_one (x u0 u1 : K) :
    ContactAtLeast K x u0 u1 1 (nodeFactor x) := by
  change AtLeast localWeights 1 (localize K x u0 u1 (nodeFactor x))
  have heq : localize K x u0 u1 (nodeFactor x) = MvPolynomial.X 0 := by
    simp [nodeFactor, localize, localVariables]
  rw [heq]
  exact atLeast_X localWeights (0 : Fin 4)

theorem locator_contactAtLeast_one (nodes : I → K) (u0 u1 : K) (i : I) :
    ContactAtLeast K (nodes i) u0 u1 1 (locator nodes) := by
  classical
  have hdiv : nodeFactor (nodes i) ∣ locator nodes :=
    Finset.dvd_prod_of_mem (fun j => nodeFactor (nodes j)) (Finset.mem_univ i)
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ]
  change AtLeast localWeights 1
    (localize K (nodes i) u0 u1 (nodeFactor (nodes i) * Q))
  rw [map_mul]
  have hfactor : AtLeast localWeights 1
      (localize K (nodes i) u0 u1 (nodeFactor (nodes i))) :=
    nodeFactor_contactAtLeast_one (nodes i) u0 u1
  have hrest := atLeast_zero localWeights (localize K (nodes i) u0 u1 Q)
  simpa only [Nat.add_zero] using atLeast_mul localWeights hfactor hrest

theorem locator_pderiv_contactAtLeast
    (nodes u0 u1 : I → K) (m : ℕ) (Q : P4 K) (hm : 1 ≤ m)
    (hQ : ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m Q) :
    ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q) := by
  intro i
  have hloc : AtLeast localWeights 1
      (localize K (nodes i) (u0 i) (u1 i) (locator nodes)) :=
    locator_contactAtLeast_one nodes (u0 i) (u1 i) i
  have hder : AtLeast localWeights (m - 1)
      (localize K (nodes i) (u0 i) (u1 i)
        (MvPolynomial.pderiv (2 : Fin 4) Q)) :=
    contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) m Q (hQ i)
  change AtLeast localWeights m (localize K (nodes i) (u0 i) (u1 i)
    (locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q))
  rw [map_mul]
  have horder : 1 + (m - 1) = m := by omega
  simpa only [horder] using atLeast_mul localWeights hloc hder

theorem pderiv_R_weight_add_le (weights : Fin 4 → ℕ) (Q : P4 K)
    (hder : MvPolynomial.pderiv (2 : Fin 4) Q ≠ 0) :
    wt weights (MvPolynomial.pderiv (2 : Fin 4) Q) + weights 2 ≤ wt weights Q := by
  classical
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup
    (MvPolynomial.pderiv (2 : Fin 4) Q).support
    (MvPolynomial.support_nonempty.mpr hder) (Finsupp.weight weights)
  have hbefore := support_before_pderiv (2 : Fin 4) Q d hd
  have hbound := MvPolynomial.le_weightedTotalDegree weights hbefore
  change wt weights (MvPolynomial.pderiv (2 : Fin 4) Q) =
    Finsupp.weight weights d at heq
  rw [heq]
  simpa only [wt, map_add, Finsupp.weight_single, one_nsmul] using hbound

theorem locator_pderiv_mem_box
    (nodes : I → K) (Q : P4 K) (D w L s : ℕ)
    (hQ : Q ∈ globalCoefficientBox K D w L s)
    (hmargin : wt (contactWeights w) Q + Fintype.card I < D + (w - 1)) :
    locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q ∈
      globalCoefficientBox K D w L s := by
  classical
  by_cases hder : MvPolynomial.pderiv (2 : Fin 4) Q = 0
  · rw [hder, mul_zero]
    exact (globalCoefficientBox K D w L s).zero_mem
  have hC := pderiv_R_weight_add_le (contactWeights w) Q hder
  change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) Q) +
    (w - 1) ≤ wt (contactWeights w) Q at hC
  have hD : 0 < D := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hQ
  apply (mem_flagGlobalCoefficientBox_iff
    (locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q) D w L s hD).mpr
  have hT := pderiv_R_weight_add_le residualTotalWeights Q hder
  change wt residualTotalWeights (MvPolynomial.pderiv (2 : Fin 4) Q) + 1 ≤
    wt residualTotalWeights Q at hT
  have hS := pderiv_R_weight_add_le residualSWeights Q hder
  change wt residualSWeights (MvPolynomial.pderiv (2 : Fin 4) Q) + 1 ≤
    wt residualSWeights Q at hS
  have hmulT := wt_mul_le residualTotalWeights (locator nodes)
    (MvPolynomial.pderiv (2 : Fin 4) Q)
  have hmulS := wt_mul_le residualSWeights (locator nodes)
    (MvPolynomial.pderiv (2 : Fin 4) Q)
  have hmulC := wt_mul_le (contactWeights w) (locator nodes)
    (MvPolynomial.pderiv (2 : Fin 4) Q)
  rw [locator_total_weight_zero, Nat.zero_add] at hmulT
  rw [locator_slope_weight_zero, Nat.zero_add] at hmulS
  have hN := locator_contact_weight_le nodes w
  exact ⟨by omega, by omega, by omega⟩

theorem locator_pderiv_degreeR_le (nodes : I → K) (Q : P4 K) (s : ℕ)
    (hQ : Q.degreeOf (2 : Fin 4) ≤ s) :
    (locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q).degreeOf (2 : Fin 4) ≤ s - 1 := by
  have hmul := MvPolynomial.degreeOf_mul_le (2 : Fin 4) (locator nodes)
    (MvPolynomial.pderiv (2 : Fin 4) Q)
  rw [locator_degreeR, Nat.zero_add] at hmul
  exact hmul.trans (pderiv_same_degree_bound (2 : Fin 4) Q s hQ)

theorem pderiv_R_ne_zero_of_degree_lt_char (Q : P4 K) (p : ℕ) [CharP K p]
    (hpos : 0 < Q.degreeOf (2 : Fin 4)) (hlt : Q.degreeOf (2 : Fin 4) < p) :
    MvPolynomial.pderiv (2 : Fin 4) Q ≠ 0 := by
  classical
  intro hz
  have hzero : Q.degreeOf (2 : Fin 4) ≤ 0 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    by_contra hnot
    have hdpos : 0 < d 2 := by omega
    have hdlt : d 2 < p :=
      (MvPolynomial.le_degreeOf_of_mem_support (2 : Fin 4) hd).trans_lt hlt
    let e : Fin 4 →₀ ℕ := d - Finsupp.single (2 : Fin 4) 1
    have hsingle : Finsupp.single (2 : Fin 4) 1 ≤ d :=
      Finsupp.single_le_iff.mpr (by omega)
    have heq : e + Finsupp.single (2 : Fin 4) 1 = d := tsub_add_cancel_of_le hsingle
    have hr : e 2 + 1 = d 2 := by
      have h := congrArg (fun f : Fin 4 →₀ ℕ => f 2) heq
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
    have hcast : (d 2 : K) ≠ 0 := by
      intro hc
      exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
        ((CharP.cast_eq_zero_iff K p (d 2)).mp hc)
    have hscalar : (e 2 : K) + 1 = (d 2 : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) hr
    have hc := congrArg (MvPolynomial.coeff e) hz
    rw [MvPolynomial.coeff_pderiv, heq, MvPolynomial.coeff_zero, hscalar] at hc
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcast) hc
  omega

theorem locator_pderiv_ne_zero_of_degree_lt_char
    (nodes : I → K) (Q : P4 K) (p : ℕ) [CharP K p]
    (hpos : 0 < Q.degreeOf (2 : Fin 4)) (hlt : Q.degreeOf (2 : Fin 4) < p) :
    locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q ≠ 0 :=
  mul_ne_zero (locator_ne_zero nodes) (pderiv_R_ne_zero_of_degree_lt_char Q p hpos hlt)

theorem locator_pderiv_ne_zero_of_degree_lt_ringChar
    (nodes : I → K) (Q : P4 K)
    (hpos : 0 < Q.degreeOf (2 : Fin 4))
    (hlt : Q.degreeOf (2 : Fin 4) < ringChar K) :
    locator nodes * MvPolynomial.pderiv (2 : Fin 4) Q ≠ 0 :=
  locator_pderiv_ne_zero_of_degree_lt_char nodes Q (ringChar K) hpos hlt

theorem exists_kernel_array_locator_pderiv
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (a : CoefficientIndex D w L s → K)
    (ha : a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1))
    (hm : 1 ≤ m)
    (hmargin : wt (contactWeights w) (reconstruct K D w L s a) + Fintype.card I <
      D + (w - 1)) :
    ∃ b : CoefficientIndex D w L s → K,
      b ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ∧
        reconstruct K D w L s b =
          locator nodes * MvPolynomial.pderiv (2 : Fin 4) (reconstruct K D w L s a) := by
  have hcontact : ∀ i : I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (reconstruct K D w L s a) :=
    fun i => contactAtLeast_of_mem_kernel K D w L s m nodes u0 u1 a ha i
  exact exists_kernel_array_of_box_of_contact D w L s m nodes u0 u1
    (locator nodes * MvPolynomial.pderiv (2 : Fin 4) (reconstruct K D w L s a))
    (locator_pderiv_mem_box nodes (reconstruct K D w L s a) D w L s
      (reconstruct_mem_globalCoefficientBox K D w L s a) hmargin)
    (locator_pderiv_contactAtLeast nodes u0 u1 m (reconstruct K D w L s a) hm hcontact)

end
end ProximityPrize.SubmissionLower.LocatorContact
