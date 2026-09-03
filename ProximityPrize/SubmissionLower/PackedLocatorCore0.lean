import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.ContactOrderBridge
import ProximityPrize.SubmissionLower.DW
import ProximityPrize.SubmissionLower.Z4
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.D
import ProximityPrize.SubmissionLower.BI
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.CommonShearTightPrototype
import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.FQ
import ProximityPrize.SubmissionLower.AL
import ProximityPrize.SubmissionLower.I
import ProximityPrize.SubmissionLower.J3
import ProximityPrize.SubmissionLower.AB
import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.EM
import ProximityPrize.SubmissionLower.W
import ProximityPrize.SubmissionLower.E9
import ProximityPrize.SubmissionLower.F0
import ProximityPrize.SubmissionLower.P1
import ProximityPrize.SubmissionLower.KernelEval

/-! Packed from ProximityPrize.SubmissionLower.LocatorNestedProjection. -/
section PackedLocator_LocatorNestedProjection
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN156 RCN180 RCN234
noncomputable section
variable {K:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def nestedExponents (D w T YS S:ℕ):Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧ d 2 ≤ S ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}
def nestedCoefficientBox (K:Type*) [Field K] (D w T YS S:ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (nestedExponents D w T YS S)

/-- The PR #437 kernel-cheap range sum. -/
def kernelSumRange (f : ℕ → ℕ) : ℕ → ℕ := KernelEval.sumRange f

theorem kernelSumRange_succ (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f (n + 1) = kernelSumRange f n + f n := by
  exact KernelEval.sumRange_succ f n

theorem kernelSumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f n = ∑ i ∈ Finset.range n, f i := by
  exact KernelEval.sumRange_eq f n

theorem finset_sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) =
      (m + 1) * a - (m + 1) * m / 2 := by
  exact KernelEval.sum_range_sub a m h

def channelCount (T YS S:ℕ):ℕ :=
  kernelSumRange (fun y =>
    let M := min S (min (T - y) (YS - y))
    (M + 1) * (T + 1 - y) - (M + 1) * M / 2) (min T YS + 1)

theorem channelCount_eq (T YS S : ℕ) :
    channelCount T YS S =
      ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S (min (T - y) (YS - y)) + 1),
          (T + 1 - y - r) := by
  rw [channelCount, kernelSumRange_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  let M := min S (min (T - y) (YS - y))
  have hM : M ≤ T + 1 - y := by
    have hMT : M ≤ T - y := by
      exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    omega
  simpa [M] using (finset_sum_range_sub (T + 1 - y) M hM).symm
abbrev HighBandIndex (delta T YS S:ℕ) :=
  (y:Fin (min T YS + 1)) ×
    (r:Fin (min S (min (T - y.val) (YS - y.val)) + 1)) ×
      (Fin (T + 1 - y.val - r.val) × Fin delta)
theorem highBandIndex_card (delta T YS S:ℕ) :
    Fintype.card (HighBandIndex delta T YS S) = delta * channelCount T YS S:=by
  rw [channelCount_eq]
  simp [HighBandIndex, Fintype.card_sigma,
    Finset.sum_range, Finset.mul_sum, Nat.mul_comm]
def highBandExponent (w Dlow:ℕ) {delta T YS S:ℕ}
    (c:HighBandIndex delta T YS S):Fin 4 →₀ ℕ :=
  Finsupp.single 0 (Dlow - w * c.1.val - (w - 1) * c.2.1.val + c.2.2.2.val) +
    Finsupp.single 1 c.1.val + Finsupp.single 2 c.2.1.val +
      Finsupp.single 3 c.2.2.1.val
def highBandMap (w Dlow delta T YS S:ℕ) :
    MvPolynomial (Fin 4) K →ₗ[K] (HighBandIndex delta T YS S → K) :=
  LinearMap.pi (fun c => MvPolynomial.lcoeff K (highBandExponent w Dlow c))
@[simp] theorem highBandMap_apply (w Dlow delta T YS S:ℕ)
    (P:MvPolynomial (Fin 4) K) (c:HighBandIndex delta T YS S) :
    highBandMap w Dlow delta T YS S P c =
      MvPolynomial.coeff (highBandExponent w Dlow c) P:=rfl
theorem mem_low_of_highBandMap_eq_zero
    (Dhigh Dlow w delta T YS S:ℕ)
    (hwidth:Dhigh ≤ Dlow + delta) (P:MvPolynomial (Fin 4) K)
    (hP:P ∈ nestedCoefficientBox K Dhigh w T YS S)
    (hzero:highBandMap w Dlow delta T YS S P = 0) :
    P ∈ nestedCoefficientBox K Dlow w T YS S:=by
  intro d hd
  rcases hP hd with ⟨hT, hYS, hS, hD⟩
  refine ⟨hT, hYS, hS, ?_⟩
  by_contra hnot
  have hy:d 1 < min T YS + 1:=by omega
  have hr:d 2 < min S (min (T - d 1) (YS - d 1)) + 1:=by omega
  have hz:d 3 < T + 1 - d 1 - d 2:=by omega
  have hstart:Dlow - w * d 1 - (w - 1) * d 2 ≤ d 0:=by omega
  have hx:d 0 - (Dlow - w * d 1 - (w - 1) * d 2) < delta:=by omega
  let c:HighBandIndex delta T YS S :=
    ⟨⟨d 1, hy⟩, ⟨⟨d 2, hr⟩,
      ⟨⟨d 3, hz⟩, ⟨d 0 - (Dlow - w * d 1 - (w - 1) * d 2), hx⟩⟩⟩⟩
  have he:highBandExponent w Dlow c = d:=by
    ext i
    fin_cases i <;> simp [highBandExponent, c] <;> omega
  have hc:=congrFun hzero c
  have hcoeff:MvPolynomial.coeff d P = 0:=by
    simpa only [highBandMap_apply, he, Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
theorem nested_mem_global {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) :
    P ∈ RCN100.globalCoefficientBox K D w T S:=by
  intro d hd
  have h:=hP hd
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩
theorem nested_mem_weights {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) (hne:P ≠ 0) :
    wt residualTotalWeights P ≤ T ∧ wt residualYSWeights P ≤ YS ∧
      wt residualSWeights P ≤ S ∧ wt (contactWeights w) P < D:=by
  have hD:0 < D:=by
    obtain ⟨d, hd⟩:=MvPolynomial.support_nonempty.mpr hne
    have h:=(hP hd).2.2.2
    omega
  have h:=(mem_flagGlobalCoefficientBox_iff P D w T S hD).mp
    (nested_mem_global hP)
  refine ⟨h.1, ?_, h.2.1, by omega⟩
  apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
  intro d hd
  have hdYS:=(hP hd).2.1
  rw [weight_fin4]
  simpa [residualYSWeights] using hdYS
theorem flag_box_ys_bound (D w L s YS:ℕ) (hw:1 ≤ w)
    (hshape:D + s ≤ w * (YS + 1)) (P:MvPolynomial (Fin 4) K)
    (hP:P ∈ RCN100.globalCoefficientBox K D w L s) :
    wt residualYSWeights P ≤ YS:=by
  apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
  intro d hd
  have hs:=(hP hd).2.1
  have hc:=(hP hd).2.2
  have hwr:w * d 2 = (w - 1) * d 2 + d 2:=by
    calc
      w * d 2 = ((w - 1) + 1) * d 2:=by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2:=by ring
  have hm:w * (d 1 + d 2) < w * (YS + 1):=by
    rw [Nat.mul_add, hwr]
    omega
  have hlt:d 1 + d 2 < YS + 1 :=
    (Nat.mul_lt_mul_left (by omega:0 < w)).mp hm
  rw [weight_fin4]
  simpa [residualYSWeights] using (Nat.le_of_lt_succ hlt)
section LinearSelection
variable {V:Type*} [AddCommGroup V] [Module K V]
theorem exists_nonzero_image_mem_low
    (Dhigh Dlow w delta T YS S:ℕ)
    (hwidth:Dhigh ≤ Dlow + delta)
    (q:V →ₗ[K] MvPolynomial (Fin 4) K) (hq:Function.Injective q)
    (hmem:∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (hsource:delta * channelCount T YS S < Module.finrank K V) :
    ∃ v:V, v ≠ 0 ∧ q v ≠ 0 ∧ q v ∈ nestedCoefficientBox K Dlow w T YS S:=by
  classical
  let band:=(highBandMap (K:=K) w Dlow delta T YS S).comp q
  have hex:∃ v:V, v ≠ 0 ∧ band v = 0:=by
    by_contra hn
    have hzero:∀ v:V, band v = 0 → v = 0:=by
      intro v hv
      by_contra hv0
      exact hn ⟨v, hv0, hv⟩
    have hinj:Function.Injective band:=by
      intro v u h
      have hz:band (v - u) = 0:=by rw [map_sub, h, sub_self]
      exact sub_eq_zero.mp (hzero (v - u) hz)
    have hle:=LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card] at hle
    exact (not_lt_of_ge hle) hsource
  obtain ⟨v, hv, hband⟩:=hex
  have hqv:q v ≠ 0:=by
    intro hz
    apply hv
    apply hq
    simpa only [map_zero] using hz
  refine ⟨v, hv, hqv, ?_⟩
  exact mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
    (q v) (hmem v) hband
end LinearSelection
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorNestedProjection

/-! Packed from ProximityPrize.SubmissionLower.LocatorContact. -/
section PackedLocator_LocatorContact
namespace ProximityPrize.SubmissionLower.LocatorContact
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN156 RCN180 RCN234 RCN313 ContactOrderBridge
noncomputable section
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem mem_kernel_of_contactAtLeast
    (D w L s m:ℕ) (nodes u0 u1:I → K)
    (a:CoefficientIndex D w L s → K)
    (ha:∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (reconstruct K D w L s a)) :
    a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1):=by
  classical
  apply LinearMap.mem_ker.mpr
  funext i r
  apply Subtype.ext
  change contactJet K (m - r.val)
    ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val a):Poly K) = 0
  apply (contactJet_eq_zero_iff K (m - r.val) _).mpr
  rw [← translation_reconstruct_coeff K D w L s (nodes i) (u0 i) (u1 i) a r.val]
  exact (contactAtLeast_iff_block_divisibility K (nodes i) (u0 i) (u1 i) m
    (reconstruct K D w L s a)).mp (ha i) r.val
theorem mem_kernel_iff_contactAtLeast
    (D w L s m:ℕ) (nodes u0 u1:I → K)
    (a:CoefficientIndex D w L s → K) :
    a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ↔
      ∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
        (reconstruct K D w L s a):=by
  constructor
  · intro ha i
    exact contactAtLeast_of_mem_kernel K D w L s m nodes u0 u1 a ha i
  · exact mem_kernel_of_contactAtLeast D w L s m nodes u0 u1 a
theorem exists_kernel_array_of_box_of_contact
    (D w L s m:ℕ) (nodes u0 u1:I → K) (Q:P4 K)
    (hbox:Q ∈ globalCoefficientBox K D w L s)
    (hcontact:∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m Q) :
    ∃ a:CoefficientIndex D w L s → K,
      a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ∧
        reconstruct K D w L s a = Q:=by
  let qbox:globalCoefficientBox K D w L s:=⟨Q, hbox⟩
  let a:CoefficientIndex D w L s → K:=encodeBox qbox
  have heq:reconstruct K D w L s a = Q:=reconstruct_encodeBox qbox
  refine ⟨a, ?_, heq⟩
  apply mem_kernel_of_contactAtLeast D w L s m nodes u0 u1 a
  intro i
  rw [heq]
  exact hcontact i
def nodeFactor (x:K):P4 K:=MvPolynomial.X 0 - MvPolynomial.C x
def locator (nodes:I → K):P4 K:=∏ i:I, nodeFactor (nodes i)
theorem nodeFactor_ne_zero (x:K):nodeFactor x ≠ 0:=by
  classical
  intro hz
  have hsingle:(Finsupp.single (0:Fin 4) 1:Fin 4 →₀ ℕ) ≠ 0:=by
    intro hs
    have h:=congrArg (fun d:Fin 4 →₀ ℕ => d 0) hs
    simpa using h
  have h:=congrArg (MvPolynomial.coeff (Finsupp.single (0:Fin 4) 1)) hz
  simpa [nodeFactor, MvPolynomial.coeff_C, hsingle.symm] using h
theorem locator_ne_zero (nodes:I → K):locator nodes ≠ 0:=by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact nodeFactor_ne_zero (nodes i)
theorem nodeFactor_wt_le (weights:Fin 4 → ℕ) (x:K) :
    wt weights (nodeFactor x) ≤ weights 0:=by
  have h:=wt_sub_le weights (MvPolynomial.X (0:Fin 4):P4 K)
    (MvPolynomial.C x)
  simpa only [nodeFactor, wt_X, wt_C, Nat.max_zero] using h
private theorem wt_prod_le_sum (weights:Fin 4 → ℕ) (J:Finset I)
    (f:I → P4 K) :
    wt weights (∏ i ∈ J, f i) ≤ ∑ i ∈ J, wt weights (f i):=by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      simpa only [Nat.cast_one] using (wt_natCast (K:=K) weights 1).le
  | @insert i J hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (wt_mul_le weights (f i) (∏ j ∈ J, f j)).trans
        (Nat.add_le_add_left ih _)
theorem locator_wt_le (weights:Fin 4 → ℕ) (nodes:I → K) :
    wt weights (locator nodes) ≤ Fintype.card I * weights 0:=by
  classical
  calc
    wt weights (locator nodes) ≤ ∑ i:I, wt weights (nodeFactor (nodes i)) :=
      wt_prod_le_sum weights Finset.univ (fun i => nodeFactor (nodes i))
    _ ≤ ∑ _i:I, weights 0 :=
      Finset.sum_le_sum (fun i _ => nodeFactor_wt_le weights (nodes i))
    _ = Fintype.card I * weights 0:=by simp
theorem locator_contact_weight_le (nodes:I → K) (w:ℕ) :
    wt (contactWeights w) (locator nodes) ≤ Fintype.card I:=by
  simpa [contactWeights] using locator_wt_le (contactWeights w) nodes
theorem locator_total_weight_zero (nodes:I → K) :
    wt residualTotalWeights (locator nodes) = 0:=by
  apply Nat.eq_zero_of_le_zero
  simpa [residualTotalWeights] using locator_wt_le residualTotalWeights nodes
theorem locator_slope_weight_zero (nodes:I → K) :
    wt residualSWeights (locator nodes) = 0:=by
  apply Nat.eq_zero_of_le_zero
  simpa [residualSWeights] using locator_wt_le residualSWeights nodes
theorem slope_weight_eq_degreeR (Q:P4 K) :
    wt residualSWeights Q = Q.degreeOf (2:Fin 4):=by
  change Q.support.sup (Finsupp.weight residualSWeights) = Q.degreeOf (2:Fin 4)
  rw [MvPolynomial.degreeOf_eq_sup]
  apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => Q.support.sup f)
  funext d
  rw [weight_fin4]
  simp [residualSWeights]
theorem locator_degreeR (nodes:I → K) :
    (locator nodes).degreeOf (2:Fin 4) = 0:=by
  rw [← slope_weight_eq_degreeR]
  exact locator_slope_weight_zero nodes
theorem nodeFactor_contactAtLeast_one (x u0 u1:K) :
    ContactAtLeast K x u0 u1 1 (nodeFactor x):=by
  change AtLeast localWeights 1 (localize K x u0 u1 (nodeFactor x))
  have heq:localize K x u0 u1 (nodeFactor x) = MvPolynomial.X 0:=by
    simp [nodeFactor, localize, localVariables]
  rw [heq]
  exact atLeast_X localWeights (0:Fin 4)
theorem locator_contactAtLeast_one (nodes:I → K) (u0 u1:K) (i:I) :
    ContactAtLeast K (nodes i) u0 u1 1 (locator nodes):=by
  classical
  have hdiv:nodeFactor (nodes i) ∣ locator nodes :=
    Finset.dvd_prod_of_mem (fun j => nodeFactor (nodes j)) (Finset.mem_univ i)
  obtain ⟨Q, hQ⟩:=hdiv
  rw [hQ]
  change AtLeast localWeights 1
    (localize K (nodes i) u0 u1 (nodeFactor (nodes i) * Q))
  rw [map_mul]
  have hfactor:AtLeast localWeights 1
      (localize K (nodes i) u0 u1 (nodeFactor (nodes i))) :=
    nodeFactor_contactAtLeast_one (nodes i) u0 u1
  have hrest:=atLeast_zero localWeights (localize K (nodes i) u0 u1 Q)
  simpa only [Nat.add_zero] using atLeast_mul localWeights hfactor hrest
theorem locator_pderiv_contactAtLeast
    (nodes u0 u1:I → K) (m:ℕ) (Q:P4 K) (hm:1 ≤ m)
    (hQ:∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m Q) :
    ∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (locator nodes * MvPolynomial.pderiv (2:Fin 4) Q):=by
  intro i
  have hloc:AtLeast localWeights 1
      (localize K (nodes i) (u0 i) (u1 i) (locator nodes)) :=
    locator_contactAtLeast_one nodes (u0 i) (u1 i) i
  have hder:AtLeast localWeights (m - 1)
      (localize K (nodes i) (u0 i) (u1 i)
        (MvPolynomial.pderiv (2:Fin 4) Q)) :=
    contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) m Q (hQ i)
  change AtLeast localWeights m (localize K (nodes i) (u0 i) (u1 i)
    (locator nodes * MvPolynomial.pderiv (2:Fin 4) Q))
  rw [map_mul]
  have horder:1 + (m - 1) = m:=by omega
  simpa only [horder] using atLeast_mul localWeights hloc hder
theorem pderiv_R_weight_add_le (weights:Fin 4 → ℕ) (Q:P4 K)
    (hder:MvPolynomial.pderiv (2:Fin 4) Q ≠ 0) :
    wt weights (MvPolynomial.pderiv (2:Fin 4) Q) + weights 2 ≤ wt weights Q:=by
  classical
  obtain ⟨d, hd, heq⟩:=Finset.exists_mem_eq_sup
    (MvPolynomial.pderiv (2:Fin 4) Q).support
    (MvPolynomial.support_nonempty.mpr hder) (Finsupp.weight weights)
  have hbefore:=support_before_pderiv (2:Fin 4) Q d hd
  have hbound:=MvPolynomial.le_weightedTotalDegree weights hbefore
  change wt weights (MvPolynomial.pderiv (2:Fin 4) Q) =
    Finsupp.weight weights d at heq
  rw [heq]
  simpa only [wt, map_add, Finsupp.weight_single, one_nsmul] using hbound
theorem locator_pderiv_mem_box
    (nodes:I → K) (Q:P4 K) (D w L s:ℕ)
    (hQ:Q ∈ globalCoefficientBox K D w L s)
    (hmargin:wt (contactWeights w) Q + Fintype.card I < D + (w - 1)) :
    locator nodes * MvPolynomial.pderiv (2:Fin 4) Q ∈
      globalCoefficientBox K D w L s:=by
  classical
  by_cases hder:MvPolynomial.pderiv (2:Fin 4) Q = 0
  · rw [hder, mul_zero]
    exact (globalCoefficientBox K D w L s).zero_mem
  have hC:=pderiv_R_weight_add_le (contactWeights w) Q hder
  change wt (contactWeights w) (MvPolynomial.pderiv (2:Fin 4) Q) +
    (w - 1) ≤ wt (contactWeights w) Q at hC
  have hD:0 < D:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hQ
  apply (mem_flagGlobalCoefficientBox_iff
    (locator nodes * MvPolynomial.pderiv (2:Fin 4) Q) D w L s hD).mpr
  have hT:=pderiv_R_weight_add_le residualTotalWeights Q hder
  change wt residualTotalWeights (MvPolynomial.pderiv (2:Fin 4) Q) + 1 ≤
    wt residualTotalWeights Q at hT
  have hS:=pderiv_R_weight_add_le residualSWeights Q hder
  change wt residualSWeights (MvPolynomial.pderiv (2:Fin 4) Q) + 1 ≤
    wt residualSWeights Q at hS
  have hmulT:=wt_mul_le residualTotalWeights (locator nodes)
    (MvPolynomial.pderiv (2:Fin 4) Q)
  have hmulS:=wt_mul_le residualSWeights (locator nodes)
    (MvPolynomial.pderiv (2:Fin 4) Q)
  have hmulC:=wt_mul_le (contactWeights w) (locator nodes)
    (MvPolynomial.pderiv (2:Fin 4) Q)
  rw [locator_total_weight_zero, Nat.zero_add] at hmulT
  rw [locator_slope_weight_zero, Nat.zero_add] at hmulS
  have hN:=locator_contact_weight_le nodes w
  exact ⟨by omega, by omega, by omega⟩
theorem locator_pderiv_degreeR_le (nodes:I → K) (Q:P4 K) (s:ℕ)
    (hQ:Q.degreeOf (2:Fin 4) ≤ s) :
    (locator nodes * MvPolynomial.pderiv (2:Fin 4) Q).degreeOf (2:Fin 4) ≤ s - 1:=by
  have hmul:=MvPolynomial.degreeOf_mul_le (2:Fin 4) (locator nodes)
    (MvPolynomial.pderiv (2:Fin 4) Q)
  rw [locator_degreeR, Nat.zero_add] at hmul
  exact hmul.trans (pderiv_same_degree_bound (2:Fin 4) Q s hQ)
theorem pderiv_R_ne_zero_of_degree_lt_char (Q:P4 K) (p:ℕ) [CharP K p]
    (hpos:0 < Q.degreeOf (2:Fin 4)) (hlt:Q.degreeOf (2:Fin 4) < p) :
    MvPolynomial.pderiv (2:Fin 4) Q ≠ 0:=by
  classical
  intro hz
  have hzero:Q.degreeOf (2:Fin 4) ≤ 0:=by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    by_contra hnot
    have hdpos:0 < d 2:=by omega
    have hdlt:d 2 < p :=
      (MvPolynomial.le_degreeOf_of_mem_support (2:Fin 4) hd).trans_lt hlt
    let e:Fin 4 →₀ ℕ:=d - Finsupp.single (2:Fin 4) 1
    have hsingle:Finsupp.single (2:Fin 4) 1 ≤ d :=
      Finsupp.single_le_iff.mpr (by omega)
    have heq:e + Finsupp.single (2:Fin 4) 1 = d:=tsub_add_cancel_of_le hsingle
    have hr:e 2 + 1 = d 2:=by
      have h:=congrArg (fun f:Fin 4 →₀ ℕ => f 2) heq
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
    have hcast:(d 2:K) ≠ 0:=by
      intro hc
      exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
        ((CharP.cast_eq_zero_iff K p (d 2)).mp hc)
    have hscalar:(e 2:K) + 1 = (d 2:K):=by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n:ℕ => (n:K)) hr
    have hc:=congrArg (MvPolynomial.coeff e) hz
    rw [MvPolynomial.coeff_pderiv, heq, MvPolynomial.coeff_zero, hscalar] at hc
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcast) hc
  omega
theorem locator_pderiv_ne_zero_of_degree_lt_char
    (nodes:I → K) (Q:P4 K) (p:ℕ) [CharP K p]
    (hpos:0 < Q.degreeOf (2:Fin 4)) (hlt:Q.degreeOf (2:Fin 4) < p) :
    locator nodes * MvPolynomial.pderiv (2:Fin 4) Q ≠ 0 :=
  mul_ne_zero (locator_ne_zero nodes) (pderiv_R_ne_zero_of_degree_lt_char Q p hpos hlt)
theorem locator_pderiv_ne_zero_of_degree_lt_ringChar
    (nodes:I → K) (Q:P4 K)
    (hpos:0 < Q.degreeOf (2:Fin 4))
    (hlt:Q.degreeOf (2:Fin 4) < ringChar K) :
    locator nodes * MvPolynomial.pderiv (2:Fin 4) Q ≠ 0 :=
  locator_pderiv_ne_zero_of_degree_lt_char nodes Q (ringChar K) hpos hlt
theorem exists_kernel_array_locator_pderiv
    (D w L s m:ℕ) (nodes u0 u1:I → K)
    (a:CoefficientIndex D w L s → K)
    (ha:a ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1))
    (hm:1 ≤ m)
    (hmargin:wt (contactWeights w) (reconstruct K D w L s a) + Fintype.card I <
      D + (w - 1)) :
    ∃ b:CoefficientIndex D w L s → K,
      b ∈ LinearMap.ker (constraintMap K D w L s m nodes u0 u1) ∧
        reconstruct K D w L s b =
          locator nodes * MvPolynomial.pderiv (2:Fin 4) (reconstruct K D w L s a):=by
  have hcontact:∀ i:I, ContactAtLeast K (nodes i) (u0 i) (u1 i) m
      (reconstruct K D w L s a) :=
    fun i => contactAtLeast_of_mem_kernel K D w L s m nodes u0 u1 a ha i
  exact exists_kernel_array_of_box_of_contact D w L s m nodes u0 u1
    (locator nodes * MvPolynomial.pderiv (2:Fin 4) (reconstruct K D w L s a))
    (locator_pderiv_mem_box nodes (reconstruct K D w L s a) D w L s
      (reconstruct_mem_globalCoefficientBox K D w L s a) hmargin)
    (locator_pderiv_contactAtLeast nodes u0 u1 m (reconstruct K D w L s a) hm hcontact)
end
end ProximityPrize.SubmissionLower.LocatorContact
end PackedLocator_LocatorContact

/-! Packed from ProximityPrize.SubmissionLower.LocatorLowQuotient. -/
section PackedLocator_LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
theorem quotient_box_of_full_divisor
    (D w L s m c t r:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ kernelReconstructLinear (K:=K) D w L s m nodes u0 u1 v)
    (hc:c ≤ wt (contactWeights w) F)
    (ht:t ≤ wt residualTotalWeights F) (hr:r ≤ wt residualSWeights F) :
    ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      quotientPolynomial (kernelReconstructLinear (K:=K) D w L s m nodes u0 u1)
        F hdiv v ∈ globalCoefficientBox K (D - c) w (L - t) (s - r):=by
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  intro v
  by_cases hv:v = 0
  · subst v
    have hz:quotientPolynomial recon F hdiv 0 = 0 :=
      (quotientLinear recon F hF hdiv).map_zero
    rw [hz]
    exact (globalCoefficientBox K _ _ _ _).zero_mem
  · have hQ:recon v ≠ 0:=by
      intro hz
      apply hv
      apply kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1
      simpa only [map_zero] using hz
    have heq:=recon_eq_mul_quotientPolynomial recon F hdiv v
    have hq:quotientPolynomial recon F hdiv v ≠ 0:=by
      intro hz
      exact hQ (by rw [heq, hz, mul_zero])
    have hReconBox:recon v ∈ globalCoefficientBox K D w L s:=by
      change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) F (quotientPolynomial recon F hdiv v)
      D w L s c t r hQ hF hq hReconBox heq hc ht hr
theorem exists_fixed_low_quotient_finrank
    (D w L s m Ysrc delta:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      Module.finrank K (ConstraintKernel (K:=K) D w L s m nodes u0 u1)) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q = reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s:=by
  classical
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  have hdivK:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ recon v:=by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q:=quotientLinear recon F hF hdivK
  have hqinj:Function.Injective q :=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1)
      F hF hdivK
  have hprod (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1) :
      recon v = F * q v:=recon_eq_mul_quotientPolynomial recon F hdivK v
  have hqbox:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ globalCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) :=
    quotient_box_of_full_divisor D w L s m
      (wt (contactWeights w) F) (wt residualTotalWeights F) (wt residualSWeights F)
      nodes u0 u1 F hF hdivK le_rfl le_rfl le_rfl
  have hqYS (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1) :
      wt residualYSWeights (q v) ≤ Ysrc - wt residualYSWeights F:=by
    by_cases hv:v = 0
    · subst v
      simp [wt, MvPolynomial.weightedTotalDegree]
    · have hqv:q v ≠ 0:=by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc:wt residualYSWeights (recon v) ≤ Ysrc:=by
        apply flag_box_ys_bound D w L s Ysrc hw hshape
        change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
        exact reconstruct_mem_globalCoefficientBox K D w L s v.1
      have hmul:=weightedTotalDegree_mul residualYSWeights F (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ nestedCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hwidth:D - wt (contactWeights w) F ≤
      (D - delta - wt (contactWeights w) F) + delta:=by omega
  obtain ⟨v, hv, hQ, hlow⟩:=exists_nonzero_image_mem_low
    (D - wt (contactWeights w) F) (D - delta - wt (contactWeights w) F)
    w delta (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
      (s - wt residualSWeights F) hwidth q hqinj hqNested hsource
  have heq:F * q v = reconstruct K D w L s v.1:=by
    simpa only [recon, kernelReconstructLinear_apply] using (hprod v).symm
  refine ⟨v, q v, hv, hQ, heq, hlow, ?_⟩
  have hsourceBox:F * q v ∈ globalCoefficientBox K D w L s:=by
    rw [heq]
    exact reconstruct_mem_globalCoefficientBox K D w L s v.1
  have hparent:0 < D - delta:=by
    have h:=(nested_mem_weights hlow hQ).2.2.2
    omega
  have hD:0 < D:=by omega
  have hsrc:=(mem_flagGlobalCoefficientBox_iff (F * q v) D w L s hD).mp hsourceBox
  have hqc:=(nested_mem_weights hlow hQ).2.2.2
  have hmul:=weightedTotalDegree_mul (contactWeights w) F (q v) hF hQ
  apply (mem_flagGlobalCoefficientBox_iff (F * q v) (D - delta) w L s hparent).mpr
  refine ⟨hsrc.1, hsrc.2.1, ?_⟩
  simp only [wt] at hqc ⊢
  omega
theorem exists_fixed_low_quotient
    (D w L s m Ysrc delta:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q = reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s :=
  exists_fixed_low_quotient_finrank D w L s m Ysrc delta nodes u0 u1 F hF hdiv hw hshape
    (hsource.trans_le (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1))
theorem specialization_pderiv_R_eq_zero_of_kernel_low_box
    (D Dlow w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
    (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
    (hlow:reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hw:1 ≤ w) (hP:P.natDegree ≤ w)
    (hcapacity:Dlow ≤ (m - 1) * support.card + (w - 1))
    (hvalues:∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2:Fin 4) (reconstruct K D w L s v.1)) = 0:=by
  classical
  let H:=reconstruct K D w L s v.1
  by_contra hne
  have hH:H ≠ 0:=by
    intro hz
    apply hne
    change RCN319.specialization K P gamma (MvPolynomial.pderiv (2:Fin 4) H) = 0
    simp only [hz, map_zero]
  have hDlow:0 < Dlow:=by
    obtain ⟨d, hd⟩:=MvPolynomial.support_nonempty.mpr hH
    have h:=(hlow hd).2.2
    omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hdegree:=ContactOrderBridge.specialized_R_derivative_degree
    K H P gamma w (Dlow - 1) hP hcaps.2.2 hne
  rw [RCN101.specialization_eq_ordinary] at hdegree
  have hdegreeStrict :
      (RCN122.specialization K P gamma (MvPolynomial.pderiv (2:Fin 4) H)).natDegree <
        (m - 1) * support.card:=by
    rw [RCN101.specialization_eq_ordinary]
    omega
  have hcontact:∀ i ∈ support, ∀ r:ℕ,
      slopeDifference K ^ (m - 1 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2:Fin 4) H)).coeff r:=by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 1) _).mp
    apply ContactOrderBridge.contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) m H
    exact ContactOrderBridge.contactAtLeast_of_mem_kernel
      K D w L s m nodes u0 u1 v.1 v.2 i
  have hz:=RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2:Fin 4) H) P gamma nodes u0 u1 support (m - 1)
    hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz
theorem exists_fixed_quotient_with_derivative_vanishing
    (D w L s m Ysrc delta agreements:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s)
    (hcapacity:D - delta ≤ (m - 1) * agreements + (w - 1))
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q = reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧
      ∀ gamma ∈ Gamma, RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F * Q)) = 0:=by
  obtain ⟨v, Q, hv, hQ, heq, hbox, hprod⟩ :=
    exists_fixed_low_quotient D w L s m Ysrc delta nodes u0 u1
      F hF hdiv hw hshape hsource
  refine ⟨v, Q, hv, hQ, heq, hbox, hprod, ?_⟩
  intro gamma hgamma
  let support:=(Finset.univ:Finset I).filter (fun i =>
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard:agreements ≤ support.card:=hagreement gamma hgamma
  have hcap:D - delta ≤ (m - 1) * support.card + (w - 1) :=
    hcapacity.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 1) hcard) _)
  have hvalues:∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i:=by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hvbox:reconstruct K D w L s v.1 ∈ globalCoefficientBox K (D - delta) w L s:=by
    rw [← heq]
    exact hprod
  rw [heq]
  exact specialization_pderiv_R_eq_zero_of_kernel_low_box
    D (D - delta) w L s m nodes u0 u1 v hvbox (selected gamma) gamma support
    hw (hdegree gamma hgamma) hcap hvalues
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorLowQuotient

/-! Packed from ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance. -/
section PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
theorem isRelPrime_of_weight_lt (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (hlt:wt weights Q < wt weights F):IsRelPrime F Q:=by
  apply hF.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact (not_lt_of_ge (weightedTotalDegree_le_of_dvd weights F Q hdiv hQ)) hlt
theorem isRelPrime_of_weight_sub_bound (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (B:ℕ) (hbound:wt weights Q ≤ B - wt weights F)
    (hhalf:B < 2 * wt weights F):IsRelPrime F Q:=by
  apply isRelPrime_of_weight_lt weights F Q hF hQ
  omega
private theorem regular_mem_normalizedFactors
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def regularIndexSelf (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1, ?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G => 0 < G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_, hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G => 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_, by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (regular_mem_normalizedFactors H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem regularIndexSelf_val (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(regularIndexSelf H F).1 = F.1:=rfl
theorem regularVector_le_mixedCost (P:UnequalParameters)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1 ≤ P.leftY) (hR:F.degreeOf 2 ≤ P.leftR)
    (hZ:F.degreeOf 3 ≤ P.leftZ) :
    (RCN052.regularVector P F).y ≤ P.mixedCost.y ∧
      (RCN052.regularVector P F).r ≤ P.mixedCost.r ∧
      (RCN052.regularVector P F).z ≤ P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
theorem regularSeeds_count_le_intersection
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hQzero:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ P.regularCountCap:=by
  let Fself:=regularIndexSelf H F
  have hcount:=RCN052.regularPairSeeds_bound P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.regularPairSeeds F.1 Q selected Gamma Fself =
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.regularPairSeeds, RCN140.regularSeeds, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=regularVector_le_mixedCost P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.agreement (RCN052.regularVector P F.1) ≤
      RCN294.dot P.agreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.agreement.y hv.1)
        (Nat.mul_le_mul_left P.agreement.r hv.2.1))
      (Nat.mul_le_mul_left P.agreement.z hv.2.2)
  apply P.regular_count_le _ (by unfold UnequalParameters.gap; omega)
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n - P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors + 1) * P.gap) hv.2.2))
theorem regularSeeds_count_le_intersection_of_product
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hproduct:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F.1 * Q)) = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ P.regularCountCap:=by
  apply regularSeeds_count_le_intersection P H Q F hrel p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  intro gamma hgamma
  obtain ⟨hFzero, hregular⟩:=(Finset.mem_filter.mp hgamma).2
  have hmul :
      RCN319.specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F.1) *
        RCN319.specialization K (selected gamma) gamma Q = 0:=by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul,
      hFzero, zero_mul, add_zero] using hproduct gamma hgamma
  exact (mul_eq_zero.mp hmul).resolve_left hregular
end
end ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem quotient_mem_nestedCoefficientBox_of_mul_eq
    (P F Q : MvPolynomial (Fin 4) K) (D w T YS S : ℕ)
    (hP : P ≠ 0) (hF : F ≠ 0) (hQ : Q ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : P = F * Q) :
    Q ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
  have hglobal :
      Q ∈ globalCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_mem_flagGlobalCoefficientBox_of_mul_eq P F Q D w T S
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) hP hF hQ (nested_mem_global hbox) heq
      le_rfl le_rfl le_rfl
  have hPYS : wt residualYSWeights P ≤ YS :=
    (nested_mem_weights hbox hP).2.1
  have hmul := weightedTotalDegree_mul residualYSWeights F Q hF hQ
  have hsum : wt residualYSWeights F + wt residualYSWeights Q ≤ YS := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F +
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ YS
    rw [← hmul, ← heq]
    exact hPYS
  have hQYS : wt residualYSWeights Q ≤ YS - wt residualYSWeights F := by
    omega
  intro d hd
  have hb := hglobal hd
  have hy := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at hy
  simp only [wt] at hQYS
  simp only [residualYSWeights] at hy ⊢
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  change d 1 + d 2 ≤ YS -
    MvPolynomial.weightedTotalDegree residualYSWeights F
  simpa [residualYSWeights] using hy.trans hQYS

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Apply the contact high-band projection to `q` and, only if every first-low
quotient is still divisible by `F`, divide once more and apply a second
high-band projection.  The second branch therefore pays for a second band,
not for the entire square-divisible coefficient box. -/
theorem exists_first_low_not_dvd_or_second_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧
      H ∈ nestedCoefficientBox K (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) := by
  classical
  let band := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let low := LinearMap.ker band
  have hrange : Module.finrank K band.range ≤ delta * channelCount T YS S := by
    calc
      Module.finrank K band.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        band.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowrank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) <
        Module.finrank K low := by
    have hsum := band.finrank_range_add_finrank_ker
    change Module.finrank K band.range + Module.finrank K low =
      Module.finrank K V at hsum
    omega
  let qlow : low →ₗ[K] MvPolynomial (Fin 4) K := q.comp low.subtype
  have hqlow : Function.Injective qlow := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  by_cases hdiv : ∀ v : low, F ∣ qlow v
  · let qtwo := quotientLinear qlow F hF hdiv
    have hqtwo : Function.Injective qtwo :=
      quotientLinear_injective qlow hqlow F hF hdiv
    have hqbox : ∀ v : low,
        qlow v ∈ nestedCoefficientBox K Dlow w T YS S := by
      intro v
      have hhigh : q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S := hmem v.1
      have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
        have hv := v.2
        change band v.1 = 0 at hv
        simpa only [band, qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hv
      simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using
        mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
          (q v.1) hhigh hzero
    have htwoBox : ∀ v : low,
        qtwo v ∈ nestedCoefficientBox K (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqlowv : qlow v ≠ 0 := by
          intro hz
          apply hv
          apply hqlow
          simpa only [map_zero] using hz
        have hqtwoV : qtwo v ≠ 0 := by
          intro hz
          apply hqlowv
          rw [recon_eq_mul_quotientPolynomial qlow F hdiv v]
          change F * qtwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qlow v) F (qtwo v) Dlow w T YS S hqlowv hF hqtwoV (hqbox v)
            (recon_eq_mul_quotientPolynomial qlow F hdiv v)
    have hwidthTwo : Dlow - wt (contactWeights w) F ≤
        (Dlow - delta - wt (contactWeights w) F) + delta := by omega
    obtain ⟨v, hv, hH, hHbox⟩ := exists_nonzero_image_mem_low
      (Dlow - wt (contactWeights w) F)
      (Dlow - delta - wt (contactWeights w) F) w delta
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) hwidthTwo qtwo hqtwo htwoBox hlowrank
    right
    refine ⟨v.1, qtwo v, ?_, hH, ?_, hHbox⟩
    · intro hz
      apply hv
      exact Subtype.ext hz
    · change F * quotientPolynomial qlow F hdiv v = qlow v
      exact (recon_eq_mul_quotientPolynomial qlow F hdiv v).symm
  · push Not at hdiv
    obtain ⟨v, hvdiv⟩ := hdiv
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvdiv
      have hvzero : v = 0 := Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hhigh : q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S := hmem v.1
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hvker := v.2
      change band v.1 = 0 at hvker
      simpa only [band, LinearMap.comp_apply, Submodule.coe_subtype] using hvker
    left
    refine ⟨v.1, hv, hqv,
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) hhigh hzero, ?_⟩
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R2_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 2) * support.card + 2 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (reconstruct K D w L s v.1))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    apply hne
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H)) = 0
    rw [hz, map_zero]
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hweight := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hder1weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≤ Dlow - 1 - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4) H) P gamma w (Dlow - 1 - (w - 1))
    hP hder1weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))).natDegree <
        (m - 2) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 2 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 2) _).mp
    have hfirst := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have hsecond := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) hfirst
    simpa only [Nat.sub_sub] using hsecond
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))
    P gamma nodes u0 u1 support (m - 2) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R2_square_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (htwo : (2 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hsecond : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (F * (F * Q)))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have htwoPoly : (2 : Polynomial K) ≠ 0 := by
    intro hz
    apply htwo
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (2 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) *
      RCN319.specialization K P gamma Q = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, two_mul, add_mul, mul_assoc] using hsecond
  have hcoef : (2 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0 :=
    mul_ne_zero htwoPoly (mul_ne_zero hregular hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end SecondDerivative

end

end ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Three successive high-band projections.  The first two quotient stages
expose a coprime branch when possible; if both quotient families remain
divisible by `F`, the last branch writes the original low source as
`F * (F * J)` and places `J` below the third high band. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - 2 * wt residualTotalWeights F)
              (YS - 2 * wt residualYSWeights F)
              (S - 2 * wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧ ¬ F ∣ H ∧
      H ∈ nestedCoefficientBox K
        (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * J) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 2 * delta - 2 * wt (contactWeights w) F) w
        (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F)
          (S - 2 * wt residualSWeights F)) := by
  classical
  let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let lowOne := LinearMap.ker bandOne
  have hrangeOne : Module.finrank K bandOne.range ≤
      delta * channelCount T YS S := by
    calc
      Module.finrank K bandOne.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        bandOne.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowOneRank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) +
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) <
        Module.finrank K lowOne := by
    have hsum := bandOne.finrank_range_add_finrank_ker
    change Module.finrank K bandOne.range + Module.finrank K lowOne =
      Module.finrank K V at hsum
    omega
  let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
  have hqOne : Function.Injective qOne := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  have hqOneBox : ∀ v : lowOne,
      qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
    intro v
    have hhigh := hmem v.1
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hv := v.2
      change bandOne v.1 = 0 at hv
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hv
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) hhigh hzero
  by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
  · let qTwo := quotientLinear qOne F hF hdivOne
    have hqTwo : Function.Injective qTwo :=
      quotientLinear_injective qOne hqOne F hF hdivOne
    have hqTwoBox : ∀ v : lowOne,
        qTwo v ∈ nestedCoefficientBox K
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqOneV : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hqTwoV : qTwo v ≠ 0 := by
          intro hz
          apply hqOneV
          rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
          change F * qTwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
            (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
    let TOne := T - wt residualTotalWeights F
    let YOne := YS - wt residualYSWeights F
    let SOne := S - wt residualSWeights F
    let DOneHigh := Dlow - wt (contactWeights w) F
    let DOneLow := Dlow - delta - wt (contactWeights w) F
    have hwidthTwo : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    let bandTwo :=
      (highBandMap (K := K) w DOneLow delta TOne YOne SOne).comp qTwo
    let lowTwo := LinearMap.ker bandTwo
    have hrangeTwo : Module.finrank K bandTwo.range ≤
        delta * channelCount TOne YOne SOne := by
      calc
        Module.finrank K bandTwo.range ≤
            Module.finrank K (HighBandIndex delta TOne YOne SOne → K) :=
          bandTwo.range.finrank_le
        _ = delta * channelCount TOne YOne SOne := by
          rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
    have hlowTwoRank :
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) <
          Module.finrank K lowTwo := by
      have hsum := bandTwo.finrank_range_add_finrank_ker
      change Module.finrank K bandTwo.range + Module.finrank K lowTwo =
        Module.finrank K lowOne at hsum
      have hrangeTwo' : Module.finrank K bandTwo.range ≤
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) := by
        simpa only [TOne, YOne, SOne] using hrangeTwo
      omega
    let qTwoLow : lowTwo →ₗ[K] MvPolynomial (Fin 4) K :=
      qTwo.comp lowTwo.subtype
    have hqTwoLow : Function.Injective qTwoLow := by
      intro a b hab
      apply Subtype.ext
      apply hqTwo
      simpa only [qTwoLow, LinearMap.comp_apply, Submodule.coe_subtype] using hab
    have hqTwoLowBox : ∀ v : lowTwo,
        qTwoLow v ∈ nestedCoefficientBox K DOneLow w TOne YOne SOne := by
      intro v
      have hhigh := hqTwoBox v.1
      have hzero : highBandMap w DOneLow delta TOne YOne SOne
          (qTwo v.1) = 0 := by
        have hv := v.2
        change bandTwo v.1 = 0 at hv
        simpa only [bandTwo, qTwoLow, LinearMap.comp_apply,
          Submodule.coe_subtype] using hv
      exact mem_low_of_highBandMap_eq_zero DOneHigh DOneLow w delta
        TOne YOne SOne hwidthTwo (qTwo v.1) hhigh hzero
    by_cases hdivTwo : ∀ v : lowTwo, F ∣ qTwoLow v
    · let qThree := quotientLinear qTwoLow F hF hdivTwo
      have hqThree : Function.Injective qThree :=
        quotientLinear_injective qTwoLow hqTwoLow F hF hdivTwo
      have hqThreeBox : ∀ v : lowTwo,
          qThree v ∈ nestedCoefficientBox K
            (DOneLow - wt (contactWeights w) F) w
            (TOne - wt residualTotalWeights F)
            (YOne - wt residualYSWeights F)
            (SOne - wt residualSWeights F) := by
        intro v
        by_cases hv : v = 0
        · subst v
          rw [map_zero]
          exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
        · have hqTwoV : qTwoLow v ≠ 0 := by
            intro hz
            apply hv
            apply hqTwoLow
            simpa only [map_zero] using hz
          have hqThreeV : qThree v ≠ 0 := by
            intro hz
            apply hqTwoV
            rw [recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v]
            change F * qThree v = 0
            rw [hz, mul_zero]
          exact quotient_mem_nestedCoefficientBox_of_mul_eq
            (qTwoLow v) F (qThree v) DOneLow w TOne YOne SOne
              hqTwoV hF hqThreeV (hqTwoLowBox v)
              (recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v)
      let TTwo := T - 2 * wt residualTotalWeights F
      let YTwo := YS - 2 * wt residualYSWeights F
      let STwo := S - 2 * wt residualSWeights F
      let DTwoHigh := Dlow - delta - 2 * wt (contactWeights w) F
      let DTwoLow := Dlow - 2 * delta - 2 * wt (contactWeights w) F
      have hwidthThree : DTwoHigh ≤ DTwoLow + delta := by
        simp only [DTwoHigh, DTwoLow]
        omega
      have hqThreeBox' : ∀ v : lowTwo,
          qThree v ∈ nestedCoefficientBox K DTwoHigh w TTwo YTwo STwo := by
        intro v
        have hD : DOneLow - wt (contactWeights w) F = DTwoHigh := by
          simp only [DOneLow, DTwoHigh]
          omega
        have hT : TOne - wt residualTotalWeights F = TTwo := by
          simp only [TOne, TTwo]
          omega
        have hY : YOne - wt residualYSWeights F = YTwo := by
          simp only [YOne, YTwo]
          omega
        have hS : SOne - wt residualSWeights F = STwo := by
          simp only [SOne, STwo]
          omega
        simpa only [hD, hT, hY, hS] using hqThreeBox v
      obtain ⟨v, hv, hJ, hJbox⟩ := exists_nonzero_image_mem_low
        DTwoHigh DTwoLow w delta TTwo YTwo STwo hwidthThree qThree hqThree
        hqThreeBox' hlowTwoRank
      right
      right
      refine ⟨v.1.1, qThree v, ?_, hJ, ?_, ?_⟩
      · intro hz
        apply hv
        apply Subtype.ext
        exact Subtype.ext hz
      · calc
          F * (F * qThree v) = F * qTwoLow v := by
            congr 1
            exact (recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v).symm
          _ = qOne v.1 := by
            exact (recon_eq_mul_quotientPolynomial qOne F hdivOne v.1).symm
          _ = q v.1.1 := rfl
      · simpa only [DTwoLow, TTwo, YTwo, STwo] using hJbox
    · push Not at hdivTwo
      obtain ⟨v, hvdiv⟩ := hdivTwo
      have hv : v.1.1 ≠ 0 := by
        intro hz
        apply hvdiv
        have hvzero : v = 0 := by
          apply Subtype.ext
          exact Subtype.ext hz
        rw [hvzero]
        simp only [map_zero]
        exact dvd_zero F
      have hH : qTwoLow v ≠ 0 := by
        intro hz
        apply hvdiv
        rw [hz]
        exact dvd_zero F
      right
      left
      refine ⟨v.1.1, qTwoLow v, hv, hH, ?_, hvdiv, ?_⟩
      · calc
          F * qTwoLow v = qOne v.1 :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v.1).symm
          _ = q v.1.1 := rfl
      · simpa only [DOneLow, TOne, YOne, SOne] using hqTwoLowBox v
  · push Not at hdivOne
    obtain ⟨v, hvdiv⟩ := hdivOne
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvdiv
      have hvzero : v = 0 := Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    left
    refine ⟨v.1, hv, hqv, hqOneBox v, ?_⟩
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section ThirdDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- A third `R`-derivative of a low kernel reconstruction specializes to zero
once the residual contact order and the global weighted-degree cap leave room
for the usual root-counting argument. -/
theorem specialization_pderiv_R3_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 3) * support.card + 3 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (reconstruct K D w L s v.1)))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    apply hne
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) = 0
    rw [hz, map_zero]
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    exact hder3 (by rw [hz, map_zero])
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hder1weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≤ Dlow - 1 - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    omega
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hder2weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≤
        Dlow - 1 - 2 * (w - 1) := by
    change wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) P gamma w
    (Dlow - 1 - 2 * (w - 1)) hP hder2weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))).natDegree <
        (m - 3) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 3 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H)))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 3) _).mp
    have hfirst := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have hsecond := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) hfirst
    have hthird := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) hsecond
    simpa only [Nat.sub_sub] using hthird
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)))
    P gamma nodes u0 u1 support (m - 3) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

/-- On the specialization where `F` itself vanishes, the third product-rule
derivative of `F³ Q` is `6 * (∂ᴿ F)³ * Q`.  Thus regularity of the
chosen factor and nonvanishing of `6` force the specialization of `Q` to
vanish. -/
theorem specialization_eq_zero_of_pderiv_R3_cube_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hsix : (6 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hthird : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) (F * (F * (F * Q)))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hsixPoly : (6 : Polynomial K) ≠ 0 := by
    intro hz
    apply hsix
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (6 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hthird
    ring_nf at hthird ⊢
    exact hthird
  have hcoef : (6 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0 :=
    mul_ne_zero hsixPoly
      (mul_ne_zero (mul_ne_zero hregular hregular) hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Four successive high-band projections.  This is one outer projection and
the cubic extractor applied to its first quotient. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - 2 * wt residualTotalWeights F)
              (YS - 2 * wt residualYSWeights F)
              (S - 2 * wt residualSWeights F) +
          delta * channelCount
            (T - 3 * wt residualTotalWeights F)
              (YS - 3 * wt residualYSWeights F)
              (S - 3 * wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧ ¬ F ∣ H ∧
      H ∈ nestedCoefficientBox K
        (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * J) = q v ∧ ¬ F ∣ J ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 2 * delta - 2 * wt (contactWeights w) F) w
        (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F)
          (S - 2 * wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * J)) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 3 * delta - 3 * wt (contactWeights w) F) w
        (T - 3 * wt residualTotalWeights F)
          (YS - 3 * wt residualYSWeights F)
          (S - 3 * wt residualSWeights F)) := by
  classical
  let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let lowOne := LinearMap.ker bandOne
  have hrangeOne : Module.finrank K bandOne.range ≤
      delta * channelCount T YS S := by
    calc
      Module.finrank K bandOne.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        bandOne.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowOneRank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) +
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) +
        delta * channelCount
          (T - 3 * wt residualTotalWeights F)
            (YS - 3 * wt residualYSWeights F)
            (S - 3 * wt residualSWeights F) <
        Module.finrank K lowOne := by
    have hsum := bandOne.finrank_range_add_finrank_ker
    change Module.finrank K bandOne.range + Module.finrank K lowOne =
      Module.finrank K V at hsum
    omega
  let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
  have hqOne : Function.Injective qOne := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  have hqOneBox : ∀ v : lowOne,
      qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
    intro v
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hv := v.2
      change bandOne v.1 = 0 at hv
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
        using hv
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) (hmem v.1) hzero
  by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
  · let qTwo := quotientLinear qOne F hF hdivOne
    have hqTwo : Function.Injective qTwo :=
      quotientLinear_injective qOne hqOne F hF hdivOne
    have hqTwoBox : ∀ v : lowOne,
        qTwo v ∈ nestedCoefficientBox K
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqOneV : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hqTwoV : qTwo v ≠ 0 := by
          intro hz
          apply hqOneV
          rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
          change F * qTwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
            (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
    let TOne := T - wt residualTotalWeights F
    let YOne := YS - wt residualYSWeights F
    let SOne := S - wt residualSWeights F
    let DOneHigh := Dlow - wt (contactWeights w) F
    let DOneLow := Dlow - delta - wt (contactWeights w) F
    have hwidthRest : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    have hsourceRest :
        delta * channelCount TOne YOne SOne +
            delta * channelCount
              (TOne - wt residualTotalWeights F)
                (YOne - wt residualYSWeights F)
                (SOne - wt residualSWeights F) +
            delta * channelCount
              (TOne - 2 * wt residualTotalWeights F)
                (YOne - 2 * wt residualYSWeights F)
                (SOne - 2 * wt residualSWeights F) <
          Module.finrank K lowOne := by
      simp only [TOne, YOne, SOne]
      have hT2 : T - wt residualTotalWeights F - wt residualTotalWeights F =
          T - 2 * wt residualTotalWeights F := by omega
      have hY2 : YS - wt residualYSWeights F - wt residualYSWeights F =
          YS - 2 * wt residualYSWeights F := by omega
      have hS2 : S - wt residualSWeights F - wt residualSWeights F =
          S - 2 * wt residualSWeights F := by omega
      have hT3 : T - wt residualTotalWeights F - 2 * wt residualTotalWeights F =
          T - 3 * wt residualTotalWeights F := by omega
      have hY3 : YS - wt residualYSWeights F - 2 * wt residualYSWeights F =
          YS - 3 * wt residualYSWeights F := by omega
      have hS3 : S - wt residualSWeights F - 2 * wt residualSWeights F =
          S - 3 * wt residualSWeights F := by omega
      simpa only [hT2, hY2, hS2, hT3, hY3, hS3] using hlowOneRank
    rcases exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
      DOneHigh DOneLow w delta TOne YOne SOne hwidthRest qTwo hqTwo
        hqTwoBox F hF hsourceRest with hfirst | hsecond | hthird
    · obtain ⟨v, hv, hH, hbox, hndvd⟩ := hfirst
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      left
      refine ⟨v.1, qTwo v, hv', hH, ?_, hndvd, ?_⟩
      · calc
          F * qTwo v = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · simpa only [DOneLow, TOne, YOne, SOne] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hndvd, hbox⟩ := hsecond
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      left
      refine ⟨v.1, J, hv', hJ, ?_, hndvd, ?_⟩
      · calc
          F * (F * J) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - delta - wt (contactWeights w) F =
            Dlow - 2 * delta - 2 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - wt residualTotalWeights F =
            T - 2 * wt residualTotalWeights F := by
          simp only [TOne]
          omega
        have hY : YOne - wt residualYSWeights F =
            YS - 2 * wt residualYSWeights F := by
          simp only [YOne]
          omega
        have hS : SOne - wt residualSWeights F =
            S - 2 * wt residualSWeights F := by
          simp only [SOne]
          omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hbox⟩ := hthird
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      refine ⟨v.1, J, hv', hJ, ?_, ?_⟩
      · calc
          F * (F * (F * J)) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - 2 * delta - 2 * wt (contactWeights w) F =
            Dlow - 3 * delta - 3 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - 2 * wt residualTotalWeights F =
            T - 3 * wt residualTotalWeights F := by
          simp only [TOne]
          omega
        have hY : YOne - 2 * wt residualYSWeights F =
            YS - 3 * wt residualYSWeights F := by
          simp only [YOne]
          omega
        have hS : SOne - 2 * wt residualSWeights F =
            S - 3 * wt residualSWeights F := by
          simp only [SOne]
          omega
        simpa only [hD, hT, hY, hS] using hbox
  · push Not at hdivOne
    obtain ⟨v, hvdiv⟩ := hdivOne
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvdiv
      have hvzero : v = 0 := Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    left
    refine ⟨v.1, hv, hqv, hqOneBox v, ?_⟩
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section FourthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R4_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 4) * support.card + 4 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (reconstruct K D w L s v.1))))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder4 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    exact hder4 (by rw [hz, map_zero])
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    exact hder3 (by rw [hz, map_zero])
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hweight3 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) hder3
  have hder3weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≤
        Dlow - 1 - 3 * (w - 1) := by
    have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
      ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) at hweight3
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) P gamma w
    (Dlow - 1 - 3 * (w - 1)) hP hder3weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H))))).natDegree <
        (m - 4) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 4 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) H))))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 4) _).mp
    have h1 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have h2 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) h1
    have h3 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) h2
    have h4 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 3)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) h3
    simpa only [Nat.sub_sub] using h4
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))))
    P gamma nodes u0 u1 support (m - 4) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R4_fourth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : (24 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfourth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (F * (F * (F * (F * Q)))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (24 : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (24 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 4 *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hfourth
    ring_nf at hfourth ⊢
    exact hfourth
  have hcoef : (24 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 4 ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero 4 hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end FourthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Five successive high-band projections, obtained by applying the
four-stage extractor to the quotient after one outer projection. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - 2 * wt residualTotalWeights F)
              (YS - 2 * wt residualYSWeights F)
              (S - 2 * wt residualSWeights F) +
          delta * channelCount
            (T - 3 * wt residualTotalWeights F)
              (YS - 3 * wt residualYSWeights F)
              (S - 3 * wt residualSWeights F) +
          delta * channelCount
            (T - 4 * wt residualTotalWeights F)
              (YS - 4 * wt residualYSWeights F)
              (S - 4 * wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧ ¬ F ∣ H ∧
      H ∈ nestedCoefficientBox K
        (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * J) = q v ∧ ¬ F ∣ J ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 2 * delta - 2 * wt (contactWeights w) F) w
        (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F)
          (S - 2 * wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * J)) = q v ∧ ¬ F ∣ J ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 3 * delta - 3 * wt (contactWeights w) F) w
        (T - 3 * wt residualTotalWeights F)
          (YS - 3 * wt residualYSWeights F)
          (S - 3 * wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * (F * J))) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 4 * delta - 4 * wt (contactWeights w) F) w
        (T - 4 * wt residualTotalWeights F)
          (YS - 4 * wt residualYSWeights F)
          (S - 4 * wt residualSWeights F)) := by
  classical
  let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let lowOne := LinearMap.ker bandOne
  have hrangeOne : Module.finrank K bandOne.range ≤
      delta * channelCount T YS S := by
    calc
      Module.finrank K bandOne.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        bandOne.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowOneRank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) +
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) +
        delta * channelCount
          (T - 3 * wt residualTotalWeights F)
            (YS - 3 * wt residualYSWeights F)
            (S - 3 * wt residualSWeights F) +
        delta * channelCount
          (T - 4 * wt residualTotalWeights F)
            (YS - 4 * wt residualYSWeights F)
            (S - 4 * wt residualSWeights F) <
        Module.finrank K lowOne := by
    have hsum := bandOne.finrank_range_add_finrank_ker
    change Module.finrank K bandOne.range + Module.finrank K lowOne =
      Module.finrank K V at hsum
    omega
  let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
  have hqOne : Function.Injective qOne := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  have hqOneBox : ∀ v : lowOne,
      qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
    intro v
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hv := v.2
      change bandOne v.1 = 0 at hv
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
        using hv
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) (hmem v.1) hzero
  by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
  · let qTwo := quotientLinear qOne F hF hdivOne
    have hqTwo : Function.Injective qTwo :=
      quotientLinear_injective qOne hqOne F hF hdivOne
    have hqTwoBox : ∀ v : lowOne,
        qTwo v ∈ nestedCoefficientBox K
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqOneV : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hqTwoV : qTwo v ≠ 0 := by
          intro hz
          apply hqOneV
          rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
          change F * qTwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
            (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
    let TOne := T - wt residualTotalWeights F
    let YOne := YS - wt residualYSWeights F
    let SOne := S - wt residualSWeights F
    let DOneHigh := Dlow - wt (contactWeights w) F
    let DOneLow := Dlow - delta - wt (contactWeights w) F
    have hwidthRest : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    have hsourceRest :
        delta * channelCount TOne YOne SOne +
            delta * channelCount
              (TOne - wt residualTotalWeights F)
                (YOne - wt residualYSWeights F)
                (SOne - wt residualSWeights F) +
            delta * channelCount
              (TOne - 2 * wt residualTotalWeights F)
                (YOne - 2 * wt residualYSWeights F)
                (SOne - 2 * wt residualSWeights F) +
            delta * channelCount
              (TOne - 3 * wt residualTotalWeights F)
                (YOne - 3 * wt residualYSWeights F)
                (SOne - 3 * wt residualSWeights F) <
          Module.finrank K lowOne := by
      simp only [TOne, YOne, SOne]
      have hT2 : T - wt residualTotalWeights F - wt residualTotalWeights F =
          T - 2 * wt residualTotalWeights F := by omega
      have hY2 : YS - wt residualYSWeights F - wt residualYSWeights F =
          YS - 2 * wt residualYSWeights F := by omega
      have hS2 : S - wt residualSWeights F - wt residualSWeights F =
          S - 2 * wt residualSWeights F := by omega
      have hT3 : T - wt residualTotalWeights F - 2 * wt residualTotalWeights F =
          T - 3 * wt residualTotalWeights F := by omega
      have hY3 : YS - wt residualYSWeights F - 2 * wt residualYSWeights F =
          YS - 3 * wt residualYSWeights F := by omega
      have hS3 : S - wt residualSWeights F - 2 * wt residualSWeights F =
          S - 3 * wt residualSWeights F := by omega
      have hT4 : T - wt residualTotalWeights F - 3 * wt residualTotalWeights F =
          T - 4 * wt residualTotalWeights F := by omega
      have hY4 : YS - wt residualYSWeights F - 3 * wt residualYSWeights F =
          YS - 4 * wt residualYSWeights F := by omega
      have hS4 : S - wt residualSWeights F - 3 * wt residualSWeights F =
          S - 4 * wt residualSWeights F := by omega
      simpa only [hT2, hY2, hS2, hT3, hY3, hS3, hT4, hY4, hS4]
        using hlowOneRank
    rcases
      exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low
        DOneHigh DOneLow w delta TOne YOne SOne hwidthRest qTwo hqTwo
          hqTwoBox F hF hsourceRest with hfirst | hsecond | hthird | hfourth
    · obtain ⟨v, hv, hH, hbox, hndvd⟩ := hfirst
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      left
      refine ⟨v.1, qTwo v, hv', hH, ?_, hndvd, ?_⟩
      · calc
          F * qTwo v = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · simpa only [DOneLow, TOne, YOne, SOne] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hndvd, hbox⟩ := hsecond
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      left
      refine ⟨v.1, J, hv', hJ, ?_, hndvd, ?_⟩
      · calc
          F * (F * J) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - delta - wt (contactWeights w) F =
            Dlow - 2 * delta - 2 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - wt residualTotalWeights F =
            T - 2 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - wt residualYSWeights F =
            YS - 2 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - wt residualSWeights F =
            S - 2 * wt residualSWeights F := by simp only [SOne]; omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hndvd, hbox⟩ := hthird
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      left
      refine ⟨v.1, J, hv', hJ, ?_, hndvd, ?_⟩
      · calc
          F * (F * (F * J)) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - 2 * delta - 2 * wt (contactWeights w) F =
            Dlow - 3 * delta - 3 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - 2 * wt residualTotalWeights F =
            T - 3 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - 2 * wt residualYSWeights F =
            YS - 3 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - 2 * wt residualSWeights F =
            S - 3 * wt residualSWeights F := by simp only [SOne]; omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hbox⟩ := hfourth
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      right
      refine ⟨v.1, J, hv', hJ, ?_, ?_⟩
      · calc
          F * (F * (F * (F * J))) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - 3 * delta - 3 * wt (contactWeights w) F =
            Dlow - 4 * delta - 4 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - 3 * wt residualTotalWeights F =
            T - 4 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - 3 * wt residualYSWeights F =
            YS - 4 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - 3 * wt residualSWeights F =
            S - 4 * wt residualSWeights F := by simp only [SOne]; omega
        simpa only [hD, hT, hY, hS] using hbox
  · push Not at hdivOne
    obtain ⟨v, hvdiv⟩ := hdivOne
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvdiv
      have hvzero : v = 0 := Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    left
    refine ⟨v.1, hv, hqv, hqOneBox v, ?_⟩
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section FifthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R5_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 5) * support.card + 5 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (reconstruct K D w L s v.1)))))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder5 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hder4 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≠ 0 := by
    intro hz
    exact hder5 (by rw [hz, map_zero])
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    exact hder4 (by rw [hz, map_zero])
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    exact hder3 (by rw [hz, map_zero])
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hweight3 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) hder3
  have hweight4 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) hder4
  have hder4weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) ≤
        Dlow - 1 - 4 * (w - 1) := by
    have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
      ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) at hweight3
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)))) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) at hweight4
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)))) P gamma w
    (Dlow - 1 - 4 * (w - 1)) hP hder4weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) H)))))).natDegree <
        (m - 5) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 5 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4)
                  (MvPolynomial.pderiv (2 : Fin 4) H)))))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 5) _).mp
    have h1 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have h2 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) h1
    have h3 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) h2
    have h4 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 3)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) h3
    have h5 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) h4
    simpa only [Nat.sub_sub] using h5
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))))
    P gamma nodes u0 u1 support (m - 5) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R5_fifth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : (120 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfifth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (F * (F * (F * (F * (F * Q)))))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (120 : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (120 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 5 *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hfifth
    ring_nf at hfifth ⊢
    exact hfifth
  have hcoef : (120 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 5 ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero 5 hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end FifthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance

/-! Packed from ProximityPrize.SubmissionLower.LocatorQuotientMonotone. -/
section PackedLocator_LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
theorem channelCount_mono {T T' YS YS' S S':ℕ}
    (ht:T ≤ T') (hy:YS ≤ YS') (hs:S ≤ S') :
    channelCount T YS S ≤ channelCount T' YS' S':=by
  rw [channelCount_eq, channelCount_eq]
  calc
    _ ≤ ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S' (min (T' - y) (YS' - y)) + 1),
          (T' + 1 - y - r):=by
      apply Finset.sum_le_sum
      intro y _
      have hin:Finset.range (min S (min (T-y) (YS-y)) + 1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y)) + 1):=by
        apply Finset.range_mono
        have h:=min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _ => by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => Nat.zero_le _))
    _ ≤ _:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _
theorem nestedCoefficientBox_mono
    {K:Type*} [Field K] {D D' w T T' YS YS' S S':ℕ}
    (hD:D ≤ D') (hT:T ≤ T') (hYS:YS ≤ YS') (hS:S ≤ S')
    {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) :
    P ∈ nestedCoefficientBox K D' w T' YS' S':=by
  intro d hd
  have h:=hP hd
  exact ⟨h.1.trans hT, h.2.1.trans hYS, h.2.2.1.trans hS,
    h.2.2.2.trans_le hD⟩
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorQuotientMonotone

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance. -/
section PackedLocator_LocatorArbitraryPowerAvoidance

/-!
# Arbitrarily many successive locator quotient projections

This is the recursive form of the explicitly unrolled second-through-ninth
power-avoidance lemmas.  It deliberately concerns only the linear high-band
selection.  Contact-order vanishing and extraction of the terminal quotient
from an iterated derivative are independent consumers of the witness returned
here.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The exact cumulative cost of `k` successive high-band projections.
The decrement form is chosen so that removing the first projection is
definitionally the same budget at the shifted quotient box. -/
def powerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T YS S +
        powerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) k

/-- Enlarging the current box and decreasing its per-stage losses can only
increase the cumulative high-band budget. -/
theorem powerBandBudget_mono
    (delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k : ℕ)
    (hT : T₁ ≤ T₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hdT : dT₂ ≤ dT₁) (hdY : dY₂ ≤ dY₁)
    (hdS : dS₂ ≤ dS₁) :
    powerBandBudget delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
      powerBandBudget delta dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  induction k generalizing T₁ Y₁ S₁ T₂ Y₂ S₂ with
  | zero =>
      simp only [powerBandBudget]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta (channelCount_mono hT hY hS)
      · apply ih
        · omega
        · omega
        · omega

/-- After `steps + 1` high-band projections, some nonzero member of the
source family has an `F`-adic stage `j`.  A nonterminal stage is coprime to
`F`; the last stage is allowed to remain divisible because the consumer uses
its terminal weight inequality instead.

The stage is represented by `j : Fin (steps + 1)`.  Thus the returned source
identity is `F ^ j * J = q v`, while the corresponding original reconstructed
row (which already has one outer factor `F`) is `F ^ (j+1) * J`.
-/
theorem exists_power_stage_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : P4 K) (hF : F ≠ 0)
    (hsource :
      powerBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F) T YS S (steps + 1) <
        Module.finrank K V) :
    ∃ (j : Fin (steps + 1)) (v : V) (J : P4 K),
      v ≠ 0 ∧ J ≠ 0 ∧ F ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta - j.val * wt (contactWeights w) F) w
        (T - j.val * wt residualTotalWeights F)
        (YS - j.val * wt residualYSWeights F)
        (S - j.val * wt residualSWeights F) ∧
      (j.val + 1 < steps + 1 → ¬ F ∣ J) := by
  classical
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hfirst : delta * channelCount T YS S < Module.finrank K V := by
        simpa only [powerBandBudget, Nat.add_zero] using hsource
      obtain ⟨v, hv, hqv, hlow⟩ :=
        exists_nonzero_image_mem_low Dhigh Dlow w delta T YS S hwidth
          q hq hmem hfirst
      refine ⟨⟨0, by omega⟩, v, q v, hv, hqv, ?_, ?_, ?_⟩
      · simp
      · simpa only [Fin.val_zero, zero_mul, Nat.zero_mul, Nat.sub_zero]
          using hlow
      · intro hlt
        omega
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T YS S +
                powerBandBudget delta
                  (wt residualTotalWeights F) (wt residualYSWeights F)
                  (wt residualSWeights F)
                  (T - wt residualTotalWeights F)
                  (YS - wt residualYSWeights F)
                  (S - wt residualSWeights F) (steps + 1) <
              Module.finrank K V := by
          simpa only [powerBandBudget, Nat.succ_eq_add_one,
            Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
      · let qTwo := quotientLinear qOne F hF hdivOne
        have hqTwo : Function.Injective qTwo :=
          quotientLinear_injective qOne hqOne F hF hdivOne
        have hqTwoBox : ∀ v : lowOne,
            qTwo v ∈ nestedCoefficientBox K
              (Dlow - wt (contactWeights w) F) w
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) := by
          intro v
          by_cases hv : v = 0
          · subst v
            rw [map_zero]
            exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
          · have hqOneV : qOne v ≠ 0 := by
              intro hz
              apply hv
              apply hqOne
              simpa only [map_zero] using hz
            have hqTwoV : qTwo v ≠ 0 := by
              intro hz
              apply hqOneV
              rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
              change F * qTwo v = 0
              rw [hz, mul_zero]
            exact quotient_mem_nestedCoefficientBox_of_mul_eq
              (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
                (hqOneBox v)
                (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
        let DOneHigh := Dlow - wt (contactWeights w) F
        let DOneLow := Dlow - delta - wt (contactWeights w) F
        let TOne := T - wt residualTotalWeights F
        let YOne := YS - wt residualYSWeights F
        let SOne := S - wt residualSWeights F
        have hwidthRest : DOneHigh ≤ DOneLow + delta := by
          simp only [DOneHigh, DOneLow]
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hwidthRest qTwo hqTwo
            (by simpa only [DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [TOne, YOne, SOne] using hlowOneRank)
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, v.1, J, ?_, hJ, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change F ^ (j.val + 1) * J = q v.1
          calc
            F ^ (j.val + 1) * J = F * (F ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = F * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) F =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) F := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights F =
              T - (j.val + 1) * wt residualTotalWeights F := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights F =
              YS - (j.val + 1) * wt residualYSWeights F := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights F =
              S - (j.val + 1) * wt residualSWeights F := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          simpa only [jUp, hD, hT, hY, hS] using hbox
        · intro hlt
          apply hterminal
          change j.val + 1 < steps + 1
          change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
          omega
      · push Not at hdivOne
        obtain ⟨v, hvdiv⟩ := hdivOne
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hvdiv
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero F
        have hqv : q v.1 ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [map_zero] using hz
        let jZero : Fin (Nat.succ steps + 1) := ⟨0, by omega⟩
        refine ⟨jZero, v.1, q v.1, hv, hqv, ?_, ?_, ?_⟩
        · simp only [jZero, Fin.val_zero, pow_zero, one_mul]
        · simpa only [jZero, Fin.val_zero, zero_mul, Nat.zero_mul,
            Nat.sub_zero, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
            using hqOneBox v
        · intro _hlt
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype]
            using hvdiv

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance
end PackedLocator_LocatorArbitraryPowerAvoidance

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact. -/
section PackedLocator_LocatorArbitraryPowerContact

/-!
# Arbitrary-order locator contact and power extraction

This module is the order-independent consumer for
`LocatorArbitraryPowerAvoidance`.  It replaces the explicitly unrolled
second-through-tenth derivative arguments by three reusable facts:

* an `R`-derivative lowers contact order by at most one;
* a nonzero `j`-fold `R`-derivative loses at least `j` times the `R` weight;
* at derivative order `j`, the surviving term of `dR^[j] (F^j * Q)` is
  `j! * Q * (dR F)^j` after specializing on `F = 0`.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The `j`-fold derivative in the received-coordinate variable. -/
def iteratePderivR (j : ℕ) (Q : P4 K) : P4 K :=
  (fun H : P4 K => MvPolynomial.pderiv (2 : Fin 4) H)^[j] Q

@[simp] theorem iteratePderivR_zero (Q : P4 K) :
    iteratePderivR 0 Q = Q := rfl

theorem iteratePderivR_succ (j : ℕ) (Q : P4 K) :
    iteratePderivR (j + 1) Q =
      MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) := by
  simp only [iteratePderivR, Function.iterate_succ_apply']

@[simp] theorem iteratePderivR_zero_poly (j : ℕ) :
    iteratePderivR (K := K) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratePderivR_succ, ih, map_zero]

/-- Contact order falls by at most one at every received-coordinate
derivative, uniformly in the number of iterations. -/
theorem contactAtLeast_iteratePderivR
    (x u0 u1 : K) (m j : ℕ) (Q : P4 K)
    (hQ : ContactOrderBridge.ContactAtLeast K x u0 u1 m Q) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - j)
      (iteratePderivR j Q) := by
  induction j with
  | zero => simpa only [iteratePderivR_zero, Nat.sub_zero] using hQ
  | succ j ih =>
      rw [iteratePderivR_succ]
      have hnext := ContactOrderBridge.contactAtLeast_pderiv_R
        K x u0 u1 (m - j) (iteratePderivR j Q) ih
      simpa only [Nat.sub_sub] using hnext

/-- If a successor iterate is nonzero, its immediate predecessor is nonzero. -/
theorem iteratePderivR_ne_zero_of_succ
    (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR (j + 1) Q ≠ 0) :
    iteratePderivR j Q ≠ 0 := by
  intro hz
  apply hne
  rw [iteratePderivR_succ, hz, map_zero]

/-- A nonzero `j`-fold received-coordinate derivative pays `j` copies of
the received-coordinate weight.  This is the generic replacement for all
manually chained `pderiv_R_weight_add_le` calculations. -/
theorem iteratePderivR_weight_add_le
    (weights : Fin 4 → ℕ) (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR j Q ≠ 0) :
    wt weights (iteratePderivR j Q) + j * weights 2 ≤ wt weights Q := by
  induction j with
  | zero =>
      simp only [iteratePderivR_zero, Nat.zero_mul, Nat.add_zero]
      exact le_rfl
  | succ j ih =>
      have hprev : iteratePderivR j Q ≠ 0 :=
        iteratePderivR_ne_zero_of_succ Q j (by
          simpa only [Nat.succ_eq_add_one] using hne)
      have hstepNe :
          MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hstep := LocatorContact.pderiv_R_weight_add_le
        weights (iteratePderivR j Q) hstepNe
      calc
        wt weights (iteratePderivR (Nat.succ j) Q) +
              Nat.succ j * weights 2 =
            (wt weights (MvPolynomial.pderiv (2 : Fin 4)
              (iteratePderivR j Q)) + weights 2) + j * weights 2 := by
              simp only [Nat.succ_eq_add_one, iteratePderivR_succ,
                Nat.add_mul, one_mul]
              ac_rfl
        _ ≤ wt weights (iteratePderivR j Q) + j * weights 2 :=
          Nat.add_le_add_right hstep _
        _ ≤ wt weights Q := ih hprev

theorem iteratePderivR_weight_le_sub
    (weights : Fin 4 → ℕ) (Q : P4 K) (j d : ℕ)
    (hne : iteratePderivR j Q ≠ 0)
    (hQ : wt weights Q ≤ d) :
    wt weights (iteratePderivR j Q) ≤ d - j * weights 2 := by
  exact Nat.le_sub_of_add_le
    ((iteratePderivR_weight_add_le weights Q j hne).trans hQ)

section KernelVanishing

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- The generic contact/degree vanishing theorem at derivative order `j`.
The capacity hypothesis is exactly the one used by each previously unrolled
fixed-order theorem. -/
theorem specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - j) * support.card + j * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (iteratePderivR j (reconstruct K D w L s v.1)) = 0 := by
  classical
  cases j with
  | zero => omega
  | succ k =>
      let H := reconstruct K D w L s v.1
      by_contra hne
      have hfinal : iteratePderivR (Nat.succ k) H ≠ 0 := by
        intro hz
        apply hne
        rw [hz, map_zero]
      have hprev : iteratePderivR k H ≠ 0 := by
        apply iteratePderivR_ne_zero_of_succ H k
        simpa only [Nat.succ_eq_add_one] using hfinal
      have hH : H ≠ 0 := by
        intro hz
        apply hfinal
        rw [hz, iteratePderivR_zero_poly]
      have hDlow : 0 < Dlow := by
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
        have h := (hlow hd).2.2
        omega
      have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
        ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
      have hprevWeight :
          wt (contactWeights w) (iteratePderivR k H) ≤
            Dlow - 1 - k * (w - 1) := by
        have hbound := iteratePderivR_weight_le_sub
          (contactWeights w) H k (Dlow - 1) hprev hHweight
        change wt (contactWeights w) (iteratePderivR k H) ≤
          Dlow - 1 - k * (w - 1) at hbound
        exact hbound
      have hregular : RCN319.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR k H)) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
        (iteratePderivR k H) P gamma w
        (Dlow - 1 - k * (w - 1)) hP hprevWeight hregular
      have hdegreeStrict :
          (RCN122.specialization K P gamma
            (iteratePderivR (Nat.succ k) H)).natDegree <
              (m - Nat.succ k) * support.card := by
        rw [Nat.succ_eq_add_one, iteratePderivR_succ]
        rw [RCN101.specialization_eq_ordinary]
        rw [RCN101.specialization_eq_ordinary] at hdegree
        have hkc : k * (w - 1) ≤ Dlow - 1 := by
          by_contra hnot
          have hlt : Dlow - 1 < k * (w - 1) := Nat.lt_of_not_ge hnot
          have hzero : Dlow - 1 - k * (w - 1) = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hzero] at hdegree
          have hwOne : w - 1 = 0 := by omega
          rw [hwOne, Nat.mul_zero] at hlt
          omega
        have hsplit :
            (Dlow - 1 - k * (w - 1)) + k * (w - 1) = Dlow - 1 :=
          Nat.sub_add_cancel hkc
        have hwSplit : w - 1 + 1 = w := Nat.sub_add_cancel hw
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hcapacity
        omega
      have hcontact : ∀ i ∈ support, ∀ r : ℕ,
          slopeDifference K ^ (m - Nat.succ k - r) ∣
            (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
              (iteratePderivR (Nat.succ k) H)).coeff r := by
        intro i _hi
        apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
          K (nodes i) (u0 i) (u1 i) (m - Nat.succ k) _).mp
        exact contactAtLeast_iteratePderivR
          (nodes i) (u0 i) (u1 i) m (Nat.succ k) H
          (ContactOrderBridge.contactAtLeast_of_mem_kernel
            K D w L s m nodes u0 u1 v.1 v.2 i)
      have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
        (iteratePderivR (Nat.succ k) H) P gamma nodes u0 u1 support
        (m - Nat.succ k) hcontact hvalues hdegreeStrict
      apply hne
      simpa only [H, RCN101.specialization_eq_ordinary] using hz

end KernelVanishing

/-- Local factorial divisibility criterion, kept here because `CH`'s
corresponding helper is intentionally private. -/
private theorem prime_dvd_factorial_local : ∀ {n p : ℕ},
    p.Prime → (p ∣ n.factorial ↔ p ≤ n)
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
      rw [Nat.factorial_succ, hp.dvd_mul, prime_dvd_factorial_local hp]
      exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
        fun h => (_root_.lt_or_eq_of_le h).elim
          (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩

/-- A prime characteristic larger than `j` does not annihilate `j!`. -/
theorem factorial_ne_zero_of_lt_char
    (p j : ℕ) [CharP K p] (hp : p.Prime) (hj : j < p) :
    (j.factorial : K) ≠ 0 := by
  intro hz
  have hdvd : p ∣ j.factorial :=
    (CharP.cast_eq_zero_iff K p j.factorial).mp hz
  exact (not_le_of_gt hj) ((prime_dvd_factorial_local hp).mp hdvd)

/-- Generic extraction of the terminal quotient from a `j`th derivative.
After specializing on `F = 0`, `RCN324.iterate_pow_mul_expansion` kills its
error term and leaves `j! * Q * (dR F)^j`. -/
theorem specialization_eq_zero_of_iteratePderivR_power_product
    (j : ℕ) (P : Polynomial K) (gamma : K) (F Q : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  obtain ⟨error, herror⟩ := RCN324.iterate_pow_mul_expansion
    (MvPolynomial.pderiv (2 : Fin 4)) F Q j j le_rfl
  have hexpansion :
      iteratePderivR j (F ^ j * Q) =
        (j.descFactorial j : P4 K) * F ^ (j - j) * Q *
            (MvPolynomial.pderiv (2 : Fin 4) F) ^ j +
          F ^ (j - j + 1) * error := by
    simpa only [iteratePderivR] using herror
  rw [hexpansion] at hpower
  have hmul :
      (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j = 0 := by
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, one_mul, mul_one,
      zero_add, pow_one, map_add, map_mul, map_pow, map_natCast,
      map_one, hFzero, zero_mul, add_zero] using hpower
  have hfactorialPoly : (j.factorial : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hcoef :
      (j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero j hregular)
  have hmul' :
      ((j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j) *
        RCN319.specialization K P gamma Q = 0 := by
    calc
      _ = (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j := by ring
      _ = 0 := hmul
  exact (mul_eq_zero.mp hmul').resolve_left hcoef

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact
end PackedLocator_LocatorArbitraryPowerContact

/-! Packed from ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance. -/
section PackedLocator_LocatorTwoFactorAvoidance

/-!
# A shared high-band route for two regular factors

The one-factor power route pays for a high-band projection independently for
every regular factor.  For two factors the projection can be shared.  On the
resulting low subspace there are only four cases: neither divisibility
condition is universal, exactly one is universal, or both are universal.  In
the first case one vector avoids both divisors; in a one-universal case the
other factor is finished and the universal factor continues through the
one-factor route; in the both-universal case the product is divided out and
the shared route continues.

This file contains the linear-algebraic core.  It intentionally returns
weight bounds rather than coefficient-box membership: those are precisely
the data consumed by the derivative and unequal-pair arguments, and they are
stable when the other factor is multiplied back into a recursively produced
helper.
-/

namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance
  LocatorArbitraryPowerContact

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The budget for a shared two-factor route.  After the current common band
there are three possible continuations: only `F`, only `G`, or both.  Taking
their maximum is sound because the divisibility case split chooses only one
continuation. -/
def twoFactorBandBudget
    (delta fT fY fS gT gY gS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      delta * channelCount T YS S +
        max
          (powerBandBudget delta fT fY fS
            (T - fT) (YS - fY) (S - fS) n)
          (max
            (powerBandBudget delta gT gY gS
              (T - gT) (YS - gY) (S - gS) n)
            (twoFactorBandBudget delta fT fY fS gT gY gS
              (T - fT - gT) (YS - fY - gY) (S - fS - gS) n))

/-- A stage for one target factor.  `j` records how many copies have been
removed from the input family.  At a nonterminal stage the helper is coprime
to the target irreducible; at the last stage the consumer may instead use a
terminal weight inequality. -/
def HasFactorStage [AddCommMonoid V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ j.val * J = q v ∧
    wt residualTotalWeights J ≤ T - j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤ YS - j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤ S - j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      Dlow - j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)

/-- Two proper divisibility subspaces cannot cover a vector space.  For two
subspaces this has a particularly cheap constructive proof: in the crossed
case `x + y` avoids both divisors. -/
theorem exists_not_dvd_both
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K)
    (hF : ¬ ∀ v, F ∣ q v) (hG : ¬ ∀ v, G ∣ q v) :
    ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  push_neg at hF hG
  obtain ⟨x, hxF⟩ := hF
  obtain ⟨y, hyG⟩ := hG
  by_cases hxG : G ∣ q x
  · by_cases hyF : F ∣ q y
    · refine ⟨x + y, ?_, ?_⟩
      · intro hsum
        apply hxF
        have hd : F ∣ q (x + y) - q y := dvd_sub hsum hyF
        simpa only [map_add, add_sub_cancel_right] using hd
      · intro hsum
        apply hyG
        have hd : G ∣ q (x + y) - q x := dvd_sub hsum hxG
        simpa only [map_add, add_sub_cancel_left] using hd
    · exact ⟨y, hyF, hyG⟩
  · exact ⟨x, hxF, hxG⟩

/-- Package the four cases used by the shared recursion. -/
theorem two_divisor_cases
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K) :
    ((∀ v, F ∣ q v) ∧ (∀ v, G ∣ q v)) ∨
      ((∀ v, F ∣ q v) ∧ ∃ v, ¬ G ∣ q v) ∨
      ((∃ v, ¬ F ∣ q v) ∧ ∀ v, G ∣ q v) ∨
      ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  by_cases hF : ∀ v, F ∣ q v
  · by_cases hG : ∀ v, G ∣ q v
    · exact Or.inl ⟨hF, hG⟩
    · right; left
      push_neg at hG
      exact ⟨hF, hG⟩
  · by_cases hG : ∀ v, G ∣ q v
    · right; right; left
      push_neg at hF
      exact ⟨hF, hG⟩
    · right; right; right
      exact exists_not_dvd_both q F G hF hG

private theorem regular_mem_normalizedFactors
    (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H := by
  have hactive : F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf : F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

/-- Distinct regular indices are represented by distinct normalized prime
factors, hence are relatively prime. -/
theorem regularIndex_isRelPrime_of_ne
    (H : P4 K) (F G : RCN266.RegularIndex H) (hne : F.1 ≠ G.1) :
    IsRelPrime F.1 G.1 := by
  have hFs := RCN167.positiveRFactors_spec H F.1 F.2
  have hGs := RCN167.positiveRFactors_spec H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (regular_mem_normalizedFactors H F) (regular_mem_normalizedFactors H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd

/-- Universal divisibility by two relatively-prime factors is universal
divisibility by their product.  This is the entry point for quotienting an
`FG`-divisible source family before starting the shared bands. -/
theorem product_dvd_of_two_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K) (hrel : IsRelPrime F G)
    (hF : ∀ v, F ∣ q v) (hG : ∀ v, G ∣ q v) :
    ∀ v, F * G ∣ q v := by
  intro v
  exact hrel.mul_dvd (hF v) (hG v)

/-- Dividing an injective nested-box family by a universal divisor preserves
injectivity and subtracts the four factor weights. -/
theorem quotientLinear_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F : P4 K) (hF : F ≠ 0) (hdiv : ∀ v, F ∣ q v) :
    Function.Injective (quotientLinear q F hF hdiv) ∧
      (∀ v, q v = F * quotientLinear q F hF hdiv v) ∧
      ∀ v, quotientLinear q F hF hdiv v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) := by
  classical
  let qF := quotientLinear q F hF hdiv
  have hqF : Function.Injective qF :=
    quotientLinear_injective q hq F hF hdiv
  have hprod (v : V) : q v = F * qF v :=
    recon_eq_mul_quotientPolynomial q F hdiv v
  refine ⟨hqF, hprod, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    rw [map_zero]
    exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
  · have hqv : q v ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv : qF v ≠ 0 := by
      intro hz
      apply hqv
      rw [hprod v, hz, mul_zero]
    exact quotient_mem_nestedCoefficientBox_of_mul_eq
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

/-- Quotient an `FG`-divisible source family by both factors while retaining
the separated weight decrements needed by the pair budget. -/
theorem exists_twoFactor_quotient_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hdivF : ∀ v, F ∣ q v) (hdivG : ∀ v, G ∣ q v) :
    ∃ qFG : V →ₗ[K] P4 K,
      Function.Injective qFG ∧
      (∀ v, q v = F * (G * qFG v)) ∧
      ∀ v, qFG v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F - wt (contactWeights w) G) w
        (T - wt residualTotalWeights F - wt residualTotalWeights G)
        (YS - wt residualYSWeights F - wt residualYSWeights G)
        (S - wt residualSWeights F - wt residualSWeights G) := by
  let qF := quotientLinear q F hF hdivF
  have hdataF := quotientLinear_nested_data D w T YS S q hq hmem F hF hdivF
  have hqF : Function.Injective qF := by
    simpa only [qF] using hdataF.1
  have hprodF : ∀ v, q v = F * qF v := by
    simpa only [qF] using hdataF.2.1
  have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F)
      (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
    simpa only [qF] using hdataF.2.2
  have hdivG' : ∀ v, G ∣ qF v := by
    intro v
    apply hrel.symm.dvd_of_dvd_mul_left
    rw [← hprodF v]
    exact hdivG v
  let qFG := quotientLinear qF G hG hdivG'
  have hdataG := quotientLinear_nested_data
    (D - wt (contactWeights w) F) w
    (T - wt residualTotalWeights F)
    (YS - wt residualYSWeights F)
    (S - wt residualSWeights F)
    qF hqF hqFBox G hG hdivG'
  refine ⟨qFG, ?_, ?_, ?_⟩
  · simpa only [qFG] using hdataG.1
  · intro v
    calc
      q v = F * qF v := hprodF v
      _ = F * (G * qFG v) := by
        rw [hdataG.2.1 v]
  · simpa only [qFG] using hdataG.2.2

/-- Exact weighted degree of a nonzero power. -/
theorem wt_pow_eq (weights : Fin 4 → ℕ) (F : P4 K) (hF : F ≠ 0)
    (j : ℕ) : wt weights (F ^ j) = j * wt weights F := by
  unfold wt
  induction j with
  | zero => simp [pow_zero, MvPolynomial.weightedTotalDegree]
  | succ j ih =>
      rw [pow_succ', weightedTotalDegree_mul weights F (F ^ j) hF
        (pow_ne_zero j hF), ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
      omega

/-- If a boxed polynomial is `F^j * J`, the three residual weights of `J`
are the ambient weights minus the corresponding factor weights. -/
theorem residual_bounds_of_power_identity
    (D w T YS S j : ℕ) (P F J : P4 K)
    (hP : P ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : F ^ j * J = P) :
    wt residualTotalWeights J ≤ T - j * wt residualTotalWeights F ∧
      wt residualYSWeights J ≤ YS - j * wt residualYSWeights F ∧
      wt residualSWeights J ≤ S - j * wt residualSWeights F := by
  have hb := nested_mem_weights hbox hP
  have one (weights : Fin 4 → ℕ) (B : ℕ)
      (hPB : wt weights P ≤ B) :
      wt weights J ≤ B - j * wt weights F := by
    have hm := weightedTotalDegree_mul weights (F ^ j) J
      (pow_ne_zero j hF) hJ
    have hp := wt_pow_eq weights F hF j
    unfold wt at hPB ⊢ hp
    rw [hp, heq] at hm
    omega
  exact ⟨one residualTotalWeights T hb.1,
    one residualYSWeights YS hb.2.1,
    one residualSWeights S hb.2.2.1⟩

private theorem sub_one_then_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem sub_pair_then_mul (a x y j : ℕ) :
    a - x - y - j * x - j * y =
      a - (j + 1) * x - (j + 1) * y := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

/-- Arithmetic used when a recursively produced helper for one factor is
multiplied by the other factor.  Expanding `(j+1) * _` first keeps the proof
inside Presburger arithmetic. -/
private theorem cross_contact_lt
    (a delta cSelf cOther j x : ℕ)
    (h : x < a - delta - cSelf - cOther - j * delta - j * cSelf) :
    cOther + x < a - (j + 1) * delta - (j + 1) * cSelf := by
  simp only [Nat.add_mul, one_mul]
  omega

/-- A single high-band chain simultaneously supplies helpers for two coprime
factors.  Relative to two independent invocations, the first band is always
paid once; whenever both divisibility conditions remain universal, all later
bands are shared as well. -/
theorem exists_two_factor_stages_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hsource :
      twoFactorBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F)
          (wt residualTotalWeights G) (wt residualYSWeights G)
          (wt residualSWeights G) T YS S (steps + 1) <
        Module.finrank K V) :
    HasFactorStage (steps + 1) Dlow w delta T YS S q F ∧
      HasFactorStage (steps + 1) Dlow w delta T YS S q G := by
  classical
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hfirst : delta * channelCount T YS S < Module.finrank K V := by
        simpa [twoFactorBandBudget, powerBandBudget] using hsource
      obtain ⟨v, hv, hqv, hlow⟩ :=
        exists_nonzero_image_mem_low Dhigh Dlow w delta T YS S hwidth
          q hq hmem hfirst
      have hb := nested_mem_weights hlow hqv
      let j0 : Fin (0 + 1) := ⟨0, by omega⟩
      have one (A : P4 K) :
          HasFactorStage (0 + 1) Dlow w delta T YS S q A := by
        refine ⟨j0, v, q v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro hlt
          omega
      exact ⟨one F, one G⟩
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have htail :
          max
            (powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1))
            (max
              (powerBandBudget delta
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights G)
                (YS - wt residualYSWeights G)
                (S - wt residualSWeights G) (steps + 1))
              (twoFactorBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights F - wt residualTotalWeights G)
                (YS - wt residualYSWeights F - wt residualYSWeights G)
                (S - wt residualSWeights F - wt residualSWeights G)
                (steps + 1))) < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget := hsource
        rw [twoFactorBandBudget] at hbudget
        have hrangeTail : Module.finrank K bandOne.range +
            max
              (powerBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (T - wt residualTotalWeights F)
                (YS - wt residualYSWeights F)
                (S - wt residualSWeights F) (steps + 1))
              (max
                (powerBandBudget delta
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights G)
                  (YS - wt residualYSWeights G)
                  (S - wt residualSWeights G) (steps + 1))
                (twoFactorBandBudget delta
                  (wt residualTotalWeights F) (wt residualYSWeights F)
                  (wt residualSWeights F)
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights F - wt residualTotalWeights G)
                  (YS - wt residualYSWeights F - wt residualYSWeights G)
                  (S - wt residualSWeights F - wt residualSWeights G)
                  (steps + 1))) < Module.finrank K V := by
          exact (Nat.add_le_add_right hrangeOne _).trans_lt (by
            simpa only [Nat.succ_eq_add_one] using hbudget)
        rw [← hsum] at hrangeTail
        exact Nat.lt_of_add_lt_add_left hrangeTail
      have hsourceF :
          powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1) <
            Module.finrank K lowOne :=
        (Nat.le_max_left _ _).trans_lt htail
      have hsourceG :
          powerBandBudget delta
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights G)
              (YS - wt residualYSWeights G)
              (S - wt residualSWeights G) (steps + 1) <
            Module.finrank K lowOne :=
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans_lt htail
      have hsourceBoth :
          twoFactorBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights F - wt residualTotalWeights G)
              (YS - wt residualYSWeights F - wt residualYSWeights G)
              (S - wt residualSWeights F - wt residualSWeights G)
              (steps + 1) < Module.finrank K lowOne :=
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans_lt htail
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      have immediate (A : P4 K) (v : lowOne) (hnot : ¬ A ∣ qOne v) :
          HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q A := by
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hnot
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero A
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype,
            map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        let j0 : Fin (Nat.succ steps + 1) := ⟨0, by omega⟩
        refine ⟨j0, v.1, qOne v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro _hlt
          exact hnot
      rcases two_divisor_cases qOne F G with hboth | honeF | honeG | hneither
      · rcases hboth with ⟨hdivF, hdivG⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hdivG' : ∀ v, G ∣ qF v := by
          intro v
          apply hrel.symm.dvd_of_dvd_mul_left
          rw [← hprodF v]
          exact hdivG v
        let qFG := quotientLinear qF G hG hdivG'
        have hdataG := quotientLinear_nested_data
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F)
          (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)
          qF hqF hqFBox G hG hdivG'
        have hqFG : Function.Injective qFG := by
          simpa only [qFG] using hdataG.1
        have hprodG : ∀ v, qF v = G * qFG v := by
          simpa only [qFG] using hdataG.2.1
        have hqFGBox : ∀ v, qFG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F - wt (contactWeights w) G) w
            (T - wt residualTotalWeights F - wt residualTotalWeights G)
            (YS - wt residualYSWeights F - wt residualYSWeights G)
            (S - wt residualSWeights F - wt residualSWeights G) := by
          simpa only [qFG] using hdataG.2.2
        have hwidthRest :
            Dlow - wt (contactWeights w) F - wt (contactWeights w) G ≤
              (Dlow - delta - wt (contactWeights w) F -
                wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨stageF, stageG⟩ := ih
          (Dlow - wt (contactWeights w) F - wt (contactWeights w) G)
          (Dlow - delta - wt (contactWeights w) F -
            wt (contactWeights w) G)
          (T - wt residualTotalWeights F - wt residualTotalWeights G)
          (YS - wt residualYSWeights F - wt residualYSWeights G)
          (S - wt residualSWeights F - wt residualSWeights G)
          hwidthRest qFG hqFG hqFGBox hsourceBoth
        have liftF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          rcases stageF with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := G * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hG hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : F ^ (j.val + 1) * JUp = qOne v := by
            calc
              F ^ (j.val + 1) * JUp = F * (G * (F ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) F JUp hqOneV hF hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) G + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) G J
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) F) (wt (contactWeights w) G)
                j.val (wt (contactWeights w) J) hC)
          · intro hlt
            have hn : ¬ F ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.dvd_of_dvd_mul_left hd)
        have liftG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          rcases stageG with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := F * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hF hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : G ^ (j.val + 1) * JUp = qOne v := by
            calc
              G ^ (j.val + 1) * JUp = F * (G * (G ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) G JUp hqOneV hG hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) F + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) F J
            have hC' : wt (contactWeights w) J <
                Dlow - delta - wt (contactWeights w) G -
                  wt (contactWeights w) F - j.val * delta -
                    j.val * wt (contactWeights w) G := by
              simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hC
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) G) (wt (contactWeights w) F)
                j.val (wt (contactWeights w) J) hC')
          · intro hlt
            have hn : ¬ G ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.symm.dvd_of_dvd_mul_left hd)
        exact ⟨liftF, liftG⟩
      · rcases honeF with ⟨hdivF, ⟨vG, hvG⟩⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hwidthRest : Dlow - wt (contactWeights w) F ≤
            (Dlow - delta - wt (contactWeights w) F) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) F)
            (Dlow - delta - wt (contactWeights w) F)
            w delta
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F)
            hwidthRest qF hqF hqFBox F hF hsourceF
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change F ^ (j.val + 1) * J = q v.1
            calc
              F ^ (j.val + 1) * J = F * (F ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = F * qF v := by rw [heq]
              _ = qOne v := (hprodF v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨stageF, immediate G vG hvG⟩
      · rcases honeG with ⟨⟨vF, hvF⟩, hdivG⟩
        let qG := quotientLinear qOne G hG hdivG
        have hdataG := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox G hG hdivG
        have hqG : Function.Injective qG := by
          simpa only [qG] using hdataG.1
        have hprodG : ∀ v, qOne v = G * qG v := by
          simpa only [qG] using hdataG.2.1
        have hqGBox : ∀ v, qG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) G) w
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G) := by
          simpa only [qG] using hdataG.2.2
        have hwidthRest : Dlow - wt (contactWeights w) G ≤
            (Dlow - delta - wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) G)
            (Dlow - delta - wt (contactWeights w) G)
            w delta
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G)
            hwidthRest qG hqG hqGBox G hG hsourceG
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change G ^ (j.val + 1) * J = q v.1
            calc
              G ^ (j.val + 1) * J = G * (G ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = G * qG v := by rw [heq]
              _ = qOne v := (hprodG v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨immediate F vF hvF, stageG⟩
      · obtain ⟨v, hvF, hvG⟩ := hneither
        exact ⟨immediate F v hvF, immediate G v hvG⟩

/-- A directed helper after removing one outer copy of each factor.  For the
`F` direction the original source is `F^(j+1) * (G * J)`.  Consequently the
derivative argument makes `J` vanish on the `F`-regular seeds away from the
collision locus `G = 0`; the collision locus itself can use `G` as its cut.
-/
def HasDirectedOuterStage [AddCommMonoid V] [Module K V]
    (fuel D w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F G : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ (j.val + 1) * (G * J) = q v ∧
    wt residualTotalWeights J ≤
      T - wt residualTotalWeights F - wt residualTotalWeights G -
        j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤
      YS - wt residualYSWeights F - wt residualYSWeights G -
        j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤
      S - wt residualSWeights F - wt residualSWeights G -
        j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)

/-- Entry point from an original source family universally divisible by both
regular factors.  It exposes the residual directed helper `J`, not `G * J`,
so the consumer can split into the off-collision (`J`) and collision (`G`)
seed classes without inflating the common helper caps. -/
theorem exists_directed_outer_stages_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps D w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hdivF : ∀ v, F ∣ q v) (hdivG : ∀ v, G ∣ q v)
    (hsource :
      twoFactorBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F)
          (wt residualTotalWeights G) (wt residualYSWeights G)
          (wt residualSWeights G)
          (T - wt residualTotalWeights F - wt residualTotalWeights G)
          (YS - wt residualYSWeights F - wt residualYSWeights G)
          (S - wt residualSWeights F - wt residualSWeights G)
          (steps + 1) < Module.finrank K V) :
    HasDirectedOuterStage (steps + 1) D w delta T YS S q F G ∧
      HasDirectedOuterStage (steps + 1) D w delta T YS S q G F := by
  classical
  obtain ⟨qFG, hqFG, hprod, hqFGBox⟩ :=
    exists_twoFactor_quotient_nested_data D w T YS S q hq hmem
      F G hF hG hrel hdivF hdivG
  have hwidth :
      D - wt (contactWeights w) F - wt (contactWeights w) G ≤
        (D - delta - wt (contactWeights w) F -
          wt (contactWeights w) G) + delta := by
    omega
  obtain ⟨stageF, stageG⟩ :=
    exists_two_factor_stages_of_bandBudget_succ steps
      (D - wt (contactWeights w) F - wt (contactWeights w) G)
      (D - delta - wt (contactWeights w) F - wt (contactWeights w) G)
      w delta
      (T - wt residualTotalWeights F - wt residualTotalWeights G)
      (YS - wt residualYSWeights F - wt residualYSWeights G)
      (S - wt residualSWeights F - wt residualSWeights G)
      hwidth qFG hqFG hqFGBox F G hF hG hrel hsource
  have directedF :
      HasDirectedOuterStage (steps + 1) D w delta T YS S q F G := by
    rcases stageF with
      ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hC, hterminal⟩
    refine ⟨j, v, J, hv, hJ, ?_, hT, hY, hS, hC, hterminal⟩
    calc
      F ^ (j.val + 1) * (G * J) = F * (G * (F ^ j.val * J)) := by
        rw [pow_succ']
        ring
      _ = F * (G * qFG v) := by rw [heq]
      _ = q v := (hprod v).symm
  have directedG :
      HasDirectedOuterStage (steps + 1) D w delta T YS S q G F := by
    rcases stageG with
      ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hC, hterminal⟩
    refine ⟨j, v, J, hv, hJ, ?_, ?_, ?_, ?_, ?_, hterminal⟩
    · calc
        G ^ (j.val + 1) * (F * J) = F * (G * (G ^ j.val * J)) := by
          rw [pow_succ']
          ring
        _ = F * (G * qFG v) := by rw [heq]
        _ = q v := (hprod v).symm
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hT
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hY
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hS
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hC
  exact ⟨directedF, directedG⟩

/-- After extracting the `F`-power term, the residual helper vanishes away
from the collision with `G`.  This is the exact soundness interface needed by
the directed consumer: collision seeds are charged using `G`, and every other
`F`-regular seed is charged using `J`. -/
theorem specialization_eq_zero_of_iteratePderivR_twoFactor_offCollision
    (j : ℕ) (P : Polynomial K) (gamma : K) (F G J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGnonzero : RCN319.specialization K P gamma G ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * (G * J))) = 0) :
    RCN319.specialization K P gamma J = 0 := by
  have hGJ := specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F (G * J) hfactorial hFzero hregular hpower
  have hmul : RCN319.specialization K P gamma G *
      RCN319.specialization K P gamma J = 0 := by
    simpa only [map_mul] using hGJ
  exact (mul_eq_zero.mp hmul).resolve_left hGnonzero

private theorem reconstruct_mem_low_of_directed_power
    {I : Type} [Fintype I]
    (D w L S m delta j : ℕ) (nodes : I → K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (F G J : P4 K)
    (heq : F ^ (j + 1) * (G * J) =
      reconstruct K D w L S v.1)
    (hD : 0 < D) (hlowpos : 0 < D - (j + 1) * delta)
    (hcontact : wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j * delta - j * wt (contactWeights w) F) :
    reconstruct K D w L S v.1 ∈
      globalCoefficientBox K (D - (j + 1) * delta) w L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) D w L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D w L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) (D - (j + 1) * delta) w L S
      hlowpos).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have houter := wt_mul_le (contactWeights w) (F ^ (j + 1)) (G * J)
  have hpow := wt_pow_le (contactWeights w) F (j + 1)
  have hinner := wt_mul_le (contactWeights w) G J
  simp only [Nat.add_mul, one_mul] at hpow ⊢
  omega

/-- Turn one directed outer stage into a concrete helper vanishing on every
`F`-regular seed outside the `F/G` collision locus.  The returned derivative
order is `j+1`, while the low contact cutoff is `D-(j+1)*delta`; keeping these
two quantities together avoids the common off-by-one error in the outer-FG
route. -/
theorem exists_directed_helper_zero_offCollision
    {I : Type} [Fintype I] [DecidableEq I]
    (fuel D w L S m delta T YS agreements p : ℕ)
    [CharP K p] (hp : p.Prime)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (H : P4 K) (F G : RCN266.RegularIndex H)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hD : 0 < D) (hw : 1 ≤ w) (hfuelChar : fuel < p)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hcapacity : ∀ a, 1 ≤ a → a ≤ fuel →
      D - a * delta ≤ (m - a) * agreements + a * (w - 1))
    (hlowpos : ∀ a, 1 ≤ a → a ≤ fuel → 0 < D - a * delta)
    (hstage : HasDirectedOuterStage fuel D w delta T YS S
      (kernelReconstructLinear (K := K) D w L S m nodes u0 u1)
      F.1 G.1) :
    ∃ (j : Fin fuel)
        (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
        (J : P4 K),
      v ≠ 0 ∧ J ≠ 0 ∧
      F.1 ^ (j.val + 1) * (G.1 * J) = reconstruct K D w L S v.1 ∧
      wt residualTotalWeights J ≤
        T - wt residualTotalWeights F.1 - wt residualTotalWeights G.1 -
          j.val * wt residualTotalWeights F.1 ∧
      wt residualYSWeights J ≤
        YS - wt residualYSWeights F.1 - wt residualYSWeights G.1 -
          j.val * wt residualYSWeights F.1 ∧
      wt residualSWeights J ≤
        S - wt residualSWeights F.1 - wt residualSWeights G.1 -
          j.val * wt residualSWeights F.1 ∧
      (j.val + 1 < fuel → ¬ F.1 ∣ J) ∧
      ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma G.1 ≠ 0 →
          RCN319.specialization K (selected gamma) gamma J = 0 := by
  classical
  rcases hstage with
    ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hcontact, hterminal⟩
  have heq' : F.1 ^ (j.val + 1) * (G.1 * J) =
      reconstruct K D w L S v.1 := by
    simpa only [kernelReconstructLinear_apply] using heq
  have hjpos : 1 ≤ j.val + 1 := by omega
  have hjle : j.val + 1 ≤ fuel := by omega
  have hlow : reconstruct K D w L S v.1 ∈
      globalCoefficientBox K (D - (j.val + 1) * delta) w L S :=
    reconstruct_mem_low_of_directed_power D w L S m delta j.val
      nodes u0 u1 v F.1 G.1 J heq' hD (hlowpos _ hjpos hjle) hcontact
  refine ⟨j, v, J, hv, hJ, heq', hT, hY, hS, hterminal, ?_⟩
  intro gamma hgamma hGnonzero
  have hgammaG := regularSeeds_subset H selected Gamma F hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard : agreements ≤ support.card := hagreement gamma hgammaG
  have hcap : D - (j.val + 1) * delta ≤
      (m - (j.val + 1)) * support.card + (j.val + 1) * (w - 1) :=
    (hcapacity _ hjpos hjle).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left (m - (j.val + 1)) hcard) _)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j.val + 1) D (D - (j.val + 1) * delta) w L S m
    nodes u0 u1 v hlow (selected gamma) gamma support hjpos
    hw (hdegree gamma hgammaG) hcap hvalues
  rw [← heq'] at hder
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  exact specialization_eq_zero_of_iteratePderivR_twoFactor_offCollision
    (j.val + 1) (selected gamma) gamma F.1 G.1 J
    (factorial_ne_zero_of_lt_char p (j.val + 1) hp
      (hjle.trans_lt hfuelChar))
    hFzero hregular hGnonzero hder

end

end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorAggregate. -/
section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz + p.all
def total (p:FlagDegree):ℕ:=p.zOnly + p.yz + p.all
def Below (p q:FlagDegree):Prop :=
  p.all ≤ q.all ∧ middle p ≤ middle q ∧ total p ≤ total q
def cap (t y s:ℕ):FlagDegree:=⟨t - y, y - s, s⟩
theorem cap_cumulative (t y s:ℕ) (hsy:s ≤ y) (hyt:y ≤ t) :
    (cap t y s).all = s ∧ middle (cap t y s) = y ∧ total (cap t y s) = t:=by
  dsimp [cap, middle, total]
  omega
theorem mixed_expansion (p q r:FlagDegree) :
    flagMixed p q r =
      (q.all * r.all + q.yz * r.all + q.all * r.yz) * total p +
      (q.zOnly * r.all + q.all * r.zOnly) * middle p +
      (q.yz * r.yz + q.zOnly * r.yz + q.yz * r.zOnly) * p.all:=by
  simp only [flagMixed, middle, total]
  ring
theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree) :
    flagMixed p q r ≤ flagMixed P q r:=by
  rw [mixed_expansion p q r, mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)
theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r ≤ flagMixed p Q r:=by
  calc
    flagMixed p q r = flagMixed q p r:=by unfold flagMixed; ring
    _ ≤ flagMixed Q p r:=mixed_mono_first h p r
    _ = flagMixed p Q r:=by unfold flagMixed; ring
theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r ≤ flagMixed p q R:=by
  calc
    flagMixed p q r = flagMixed r q p:=by unfold flagMixed; ring
    _ ≤ flagMixed R q p:=mixed_mono_first h q p
    _ = flagMixed p q R:=by unfold flagMixed; ring
theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r ≤ flagMixed p Q R :=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)
theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i, (p i).all) ≤ P.all)
    (hy:(∑ i, middle (p i)) ≤ middle P)
    (ht:(∑ i, total (p i)) ≤ total P) :
    (∑ i, flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p + 1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree :=
  ⟨2 * (padT p - padY p) * d,
    1 + 2 * (padY p - padS p) * d,
    2 * (padS p - 1) * d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ :=
  flagMixed p (paddedTail p d) (paddedTail p e)
theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ) :
    (paddedTail p d).all = 2 * (padS p - 1) * d ∧
    middle (paddedTail p d) = 1 + 2 * (padY p - 1) * d ∧
    total (paddedTail p d) = 1 + 2 * (padT p - 1) * d:=by
  have hs:1 ≤ padS p:=by
    have h:2 ≤ padS p:=le_max_right _ _
    omega
  have hy:padS p + 1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  have hyadd:padY p - padS p + (padS p - 1) = padY p - 1:=by omega
  have htadd:padT p - padY p + (padY p - padS p) + (padS p - 1) =
      padT p - 1:=by omega
  refine ⟨rfl, ?_, ?_⟩
  · change (1 + 2 * (padY p - padS p) * d) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padY p - padS p + (padS p - 1)) * d:=by ring
      _ = _:=by rw [hyadd]
  · change (2 * (padT p - padY p) * d +
      (1 + 2 * (padY p - padS p) * d)) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padT p - padY p + (padY p - padS p) +
        (padS p - 1)) * d:=by ring
      _ = _:=by rw [htadd]
theorem padding_mono {p q:FlagDegree} (h:Below p q) :
    padS p ≤ padS q ∧ padY p ≤ padY q ∧ padT p ≤ padT q:=by
  have hs:padS p ≤ padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p ≤ padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p ≤ padT q:=max_le_max h.2.2 hy
  exact ⟨hs, hy, ht⟩
theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q) :
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a ≤ b):2 * (a - 1) * d ≤ 2 * (b - 1) * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  exact ⟨hm hc.1, Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩
theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q) :
    paddedCost d e p ≤ paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))
theorem merge_padded_costs {I:Type*} [Fintype I]
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i, (p i).all) ≤ P.all)
    (hy:(∑ i, middle (p i)) ≤ middle P)
    (ht:(∑ i, total (p i)) ≤ total P) :
    (∑ i, paddedCost d e (p i)) ≤ paddedCost d e P:=by
  classical
  have hi (i:I):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht⟩
  calc
    (∑ i, paddedCost d e (p i)) ≤
        ∑ i, flagMixed (p i) (paddedTail P d) (paddedTail P e) :=
      Finset.sum_le_sum (fun i _ =>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _ ≤ paddedCost d e P:=sum_mixed_le p P _ _ hs hy ht
theorem sum_mixed_le_finset {I:Type*} (s:Finset I)
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i ∈ s, (p i).all) ≤ P.all)
    (hy:(∑ i ∈ s, middle (p i)) ≤ middle P)
    (ht:(∑ i ∈ s, total (p i)) ≤ total P) :
    (∑ i ∈ s, flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
theorem merge_padded_costs_finset {I:Type*} (s:Finset I)
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i ∈ s, (p i).all) ≤ P.all)
    (hy:(∑ i ∈ s, middle (p i)) ≤ middle P)
    (ht:(∑ i ∈ s, total (p i)) ≤ total P) :
    (∑ i ∈ s, paddedCost d e (p i)) ≤ paddedCost d e P:=by
  classical
  have hi (i:I) (h:i ∈ s):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans hs,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans hy,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans ht⟩
  calc
    (∑ i ∈ s, paddedCost d e (p i)) ≤
        ∑ i ∈ s, flagMixed (p i) (paddedTail P d) (paddedTail P e) :=
      Finset.sum_le_sum (fun i h => mixed_mono_tails (p i)
        (paddedTail_mono d (hi i h)) (paddedTail_mono e (hi i h)))
    _ ≤ paddedCost d e P:=sum_mixed_le_finset s p P _ _ hs hy ht
theorem paddedTail_cap (t y s d:ℕ)
    (hs:2 ≤ s) (hy:s + 1 ≤ y) (ht:y ≤ t) :
    paddedTail (cap t y s) d =
      ⟨2 * (t - y) * d, 1 + 2 * (y - s) * d, 2 * (s - 1) * d⟩:=by
  have hc:=cap_cumulative t y s (by omega) ht
  have hps:padS (cap t y s) = s:=by
    change max s 2 = s
    exact max_eq_left hs
  have hpy:padY (cap t y s) = y:=by
    unfold padY
    rw [hc.2.1, hps, max_eq_left hy]
  have hpt:padT (cap t y s) = t:=by
    unfold padT
    rw [hc.2.2, hpy, max_eq_left ht]
  simp only [paddedTail, hps, hpy, hpt]
private abbrev lowCap6751:ℕ:=261420997282933785
theorem all_le_middle (p:FlagDegree):p.all ≤ middle p:=by
  dsimp [middle]
  omega
theorem middle_le_total (p:FlagDegree):middle p ≤ total p:=by
  dsimp [middle, total]
  omega
theorem all_le_total (p:FlagDegree):p.all ≤ total p :=
  (all_le_middle p).trans (middle_le_total p)
theorem below_cap_of_bounds (p:FlagDegree) (t y s:ℕ)
    (hsy:s ≤ y) (hyt:y ≤ t)
    (hs:p.all ≤ s) (hy:middle p ≤ y) (ht:total p ≤ t) :
    Below p (cap t y s):=by
  have hc:=cap_cumulative t y s hsy hyt
  unfold Below
  rw [hc.1, hc.2.1, hc.2.2]
  exact ⟨hs, hy, ht⟩
private theorem below_total_flag (p:FlagDegree) :
    Below p ⟨0, 0, total p⟩:=by
  unfold Below
  refine ⟨all_le_total p, ?_, ?_⟩
  · simpa only [middle, Nat.zero_add] using middle_le_total p
  · simp only [total, Nat.zero_add, le_refl]
private def diagonalRate (u s:ℕ):ℕ :=
  flagMixed ⟨0, 0, 1⟩
    (paddedTail (cap u u s) 131072)
    (paddedTail (cap u u s) 131073)
private theorem cost_le_diagonal_rate (p:FlagDegree) (u s:ℕ)
    (h:Below p (cap u u s)) :
    paddedCost 131072 131073 p ≤ diagonalRate u s * total p:=by
  calc
    _ ≤ flagMixed p (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073) :=
      mixed_mono_tails p (paddedTail_mono 131072 h) (paddedTail_mono 131073 h)
    _ ≤ flagMixed ⟨0, 0, total p⟩ (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073) :=
      mixed_mono_first (below_total_flag p) _ _
    _ = diagonalRate u s * total p:=by
      simp only [diagonalRate, flagMixed]
      ring
private theorem affine64 (t:ℕ) (ht:64 ≤ t) :
    paddedCost 131072 131073 (cap t 64 7) + 5324494425030747 =
      157093929156634 * t:=by
  have hsub:t - 64 + 64 = t:=Nat.sub_add_cancel ht
  unfold paddedCost
  rw [paddedTail_cap t 64 7 131072 (by decide) (by decide) ht,
    paddedTail_cap t 64 7 131073 (by decide) (by decide) ht]
  simp only [cap, flagMixed]
  ring_nf
  omega
private theorem rate_of_affine {t c top alpha deficit:ℕ}
    (ht:t ≤ 1698) (hc:c + deficit = alpha * t)
    (hTop:top + deficit = alpha * 1698) (hbound:top ≤ lowCap6751) :
    1698 * c ≤ lowCap6751 * t:=by
  have hscaled:1698 * c + deficit * t ≤ top * t + deficit * t:=by
    calc
      _ ≤ 1698 * c + deficit * 1698 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left deficit ht) _
      _ = (c + deficit) * 1698:=by ring
      _ = (alpha * t) * 1698:=by rw [hc]
      _ = (alpha * 1698) * t:=by ring
      _ = (top + deficit) * t:=by rw [← hTop]
      _ = top * t + deficit * t:=by ring
  exact (Nat.le_of_add_le_add_right hscaled).trans
    (Nat.mul_le_mul_right t hbound)
private theorem large_rate64 (t:ℕ) (hlo:64 ≤ t) (hhi:t ≤ 1698) :
    1698 * paddedCost 131072 131073 (cap t 64 7) ≤ lowCap6751 * t:=by
  have htop:=affine64 1698 (by decide)
  have hb:paddedCost 131072 131073 (cap 1698 64 7) ≤ lowCap6751:=by
    unfold lowCap6751
    omega
  exact rate_of_affine hhi (affine64 t hlo) htop hb
private theorem middle_tail_formula64 (p:FlagDegree) :
    flagMixed p (paddedTail (cap 64 64 7) 131072)
        (paddedTail (cap 64 64 7) 131073) =
      49478403883020 * total p + 223271313211507 * p.all:=by
  norm_num [paddedTail, padT, padY, padS, cap, total, middle, flagMixed]
  ring
private theorem middle_rate64 (t:ℕ) (ht:15 ≤ t) :
    1698 * (49478403883020 * t + 223271313211507 * 7) ≤ lowCap6751 * t:=by
  unfold lowCap6751
  omega
theorem rate_bound_6751_low (p:FlagDegree)
    (hs:p.all ≤ 7) (hy:middle p ≤ 64) (ht:total p ≤ 1698) :
    1698 * paddedCost 131072 131073 p ≤ 261420997282933785 * total p:=by
  have hn:=middle_le_total p
  by_cases ht15:total p ≤ 15
  · have hb:=below_cap_of_bounds p 15 15 7 (by decide) (by decide)
      hs (hn.trans ht15) ht15
    have hc:=cost_le_diagonal_rate p 15 7 hb
    have hk:1698 * diagonalRate 15 7 ≤ 261420997282933785:=by decide
    calc
      _ ≤ 1698 * (diagonalRate 15 7 * total p):=Nat.mul_le_mul_left 1698 hc
      _ = (1698 * diagonalRate 15 7) * total p:=by ring
      _ ≤ _:=Nat.mul_le_mul_right (total p) hk
  · by_cases ht64:total p ≤ 64
    · have hb:=below_cap_of_bounds p 64 64 7 (by decide) (by decide) hs hy ht64
      have hc:paddedCost 131072 131073 p ≤
          49478403883020 * total p + 223271313211507 * 7:=by
        calc
          _ ≤ flagMixed p (paddedTail (cap 64 64 7) 131072)
              (paddedTail (cap 64 64 7) 131073) :=
            mixed_mono_tails p (paddedTail_mono 131072 hb) (paddedTail_mono 131073 hb)
          _ = 49478403883020 * total p + 223271313211507 * p.all :=
            middle_tail_formula64 p
          _ ≤ _:=Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
      exact (Nat.mul_le_mul_left 1698 hc).trans (middle_rate64 (total p) (by omega))
    · have hlo:64 ≤ total p:=by omega
      have hb:=below_cap_of_bounds p (total p) 64 7 (by decide) hlo hs hy (le_refl _)
      exact (Nat.mul_le_mul_left 1698 (paddedCost_mono 131072 131073 hb)).trans
        (large_rate64 (total p) hlo ht)
theorem aggregate_6751_low {I:Type*} [Fintype I] (p:I → FlagDegree)
    (hs:∀ i, (p i).all ≤ 7) (hy:∀ i, middle (p i) ≤ 64)
    (htsum:(∑ i, total (p i)) ≤ 1698) :
    (∑ i, paddedCost 131072 131073 (p i)) ≤ 261420997282933785:=by
  classical
  have hti (i:I):total (p i) ≤ 1698 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans htsum
  have hscaled:1698 * (∑ i, paddedCost 131072 131073 (p i)) ≤
      1698 * 261420997282933785:=by
    calc
      _ = ∑ i, 1698 * paddedCost 131072 131073 (p i):=by rw [Finset.mul_sum]
      _ ≤ ∑ i, 261420997282933785 * total (p i) :=
        Finset.sum_le_sum (fun i _ => rate_bound_6751_low (p i) (hs i) (hy i) (hti i))
      _ = 261420997282933785 * (∑ i, total (p i)):=by rw [Finset.mul_sum]
      _ ≤ 261420997282933785 * 1698:=Nat.mul_le_mul_left _ htsum
      _ = 1698 * 261420997282933785:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)
end ProximityPrize.SubmissionLower.LocatorFactorAggregate
end PackedLocator_LocatorFactorAggregate

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCost. -/
section PackedLocator_LocatorHybridCost

/-!
# Hybrid second-surface cost

The ordinary cost of a regular factor with cumulative flag `p` is the padded
two-tail Bezout count `paddedCost 131072 131073 p`.  When the padded slope is at
least `2` and the padded middle exceeds the padded slope by at least `2`, the
delayed second tail can be replaced by the hybrid coordinate surface, giving
`hybridCost p`, which is smaller by roughly a fifth on the binding cells.  All
tail flags are monotone in the padded cumulative degrees, so the cost is
monotone under `Below`, exactly like `paddedCost`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open scoped BigOperators
open RCN095 LocatorFactorAggregate

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- Sharp first tail `⟨2a·d, 1+(2b+1)·d, (2s+3)·d⟩` at `d = 131072`, with
`a = padT - padY`, `b = padY - padS - 1`, `s = padS - 2`. -/
def sharpTail (p : FlagDegree) : FlagDegree :=
  ⟨2 * (padT p - padY p) * 131072,
    1 + (2 * (padY p - padS p) - 1) * 131072,
    (2 * padS p - 1) * 131072⟩

def rationalFlag (p : FlagDegree) : FlagDegree :=
  ⟨131072 * (padT p - padY p) + 2 * (padT p - padY p),
    131072 * (padY p - padS p - 1) + 2 * (padY p - padS p - 1) + 2,
    131072 * (padS p - 2) + 2 * (padS p - 2) + 3⟩

def hybridCoordinate (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 65536, 196608⟩

def movingFiber (p : FlagDegree) : FlagDegree :=
  ⟨padT p - padY p, padY p - padS p, padS p + 1⟩

def movingCut (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 131072, 262144⟩

def hybridCost (p : FlagDegree) : ℕ :=
  flagMixed p (sharpTail p) (hybridCoordinate p) +
    131072 * flagMixed p (movingFiber p) (movingCut p)

/-- The hybrid branch applies when the slope is at least `2` and the middle
exceeds the slope by at least `2`. -/
def HybridApplies (p : FlagDegree) : Prop := 2 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridApplies p) := by
  unfold HybridApplies; infer_instance

def ordinaryCostOf (p : FlagDegree) : ℕ :=
  if HybridApplies p then hybridCost p else paddedCost 131072 131073 p

theorem pad_bounds (p : FlagDegree) :
    2 ≤ padS p ∧ padS p + 1 ≤ padY p ∧ padY p ≤ padT p :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

theorem sharpTail_cumulative (p : FlagDegree) :
    (sharpTail p).all = (2 * padS p - 1) * 131072 ∧
      middle (sharpTail p) = 1 + 2 * (padY p - 1) * 131072 ∧
      total (sharpTail p) = 1 + 2 * (padT p - 1) * 131072 := by
  have h := pad_bounds p
  dsimp only [sharpTail, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem hybridCoordinate_cumulative (p : FlagDegree) :
    (hybridCoordinate p).all = 131074 * (padS p - 2) + 196611 ∧
      middle (hybridCoordinate p) = 131074 * (padY p - 3) + 262149 ∧
      total (hybridCoordinate p) = 131074 * (padT p - 3) + 262149 := by
  have h := pad_bounds p
  dsimp only [hybridCoordinate, rationalFlag, middle, total, add_zOnly, add_yz, add_all]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingFiber_cumulative (p : FlagDegree) :
    (movingFiber p).all = padS p + 1 ∧
      middle (movingFiber p) = padY p + 1 ∧
      total (movingFiber p) = padT p + 1 := by
  have h := pad_bounds p
  dsimp only [movingFiber, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingCut_cumulative (p : FlagDegree) :
    (movingCut p).all = 131074 * (padS p - 2) + 262147 ∧
      middle (movingCut p) = 131074 * (padY p - 3) + 393221 ∧
      total (movingCut p) = 131074 * (padT p - 3) + 393221 := by
  have h := pad_bounds p
  dsimp only [movingCut, rationalFlag, middle, total, add_zOnly, add_yz, add_all]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem sharpTail_mono {p q : FlagDegree} (h : Below p q) :
    Below (sharpTail p) (sharpTail q) := by
  have hp := sharpTail_cumulative p
  have hq := sharpTail_cumulative q
  have hc := padding_mono h
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem hybridCoordinate_mono {p q : FlagDegree} (h : Below p q) :
    Below (hybridCoordinate p) (hybridCoordinate q) := by
  have hp := hybridCoordinate_cumulative p
  have hq := hybridCoordinate_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem movingFiber_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingFiber p) (movingFiber q) := by
  have hp := movingFiber_cumulative p
  have hq := movingFiber_cumulative q
  have hc := padding_mono h
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem movingCut_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingCut p) (movingCut q) := by
  have hp := movingCut_cumulative p
  have hq := movingCut_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem hybridCost_mono {p q : FlagDegree} (h : Below p q) :
    hybridCost p ≤ hybridCost q := by
  unfold hybridCost
  apply Nat.add_le_add
  · exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (sharpTail_mono h) (hybridCoordinate_mono h))
  · apply Nat.mul_le_mul_left
    exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (movingFiber_mono h) (movingCut_mono h))

/-- Per-factor hybrid bounds at the factor's own padded tails merge into the
hybrid cost of the cumulative flag. -/
theorem merge_hybrid_costs {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, (flagMixed (p i) (sharpTail P) (hybridCoordinate P) +
      131072 * flagMixed (p i) (movingFiber P) (movingCut P))) ≤ hybridCost P := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hybridCost
  apply Nat.add_le_add
  · exact sum_mixed_le p P _ _ hs hy ht
  · exact Nat.mul_le_mul_left _ (sum_mixed_le p P _ _ hs hy ht)

theorem hybridApplies_of_below {p q : FlagDegree} (hall : p.all = q.all)
    (hpq : Below p q) (hp : HybridApplies p) : HybridApplies q := by
  obtain ⟨h1, h2⟩ := hp
  exact ⟨hall ▸ h1, by have := hpq.2.1; omega⟩

theorem ordinaryCostOf_le_of_hybrid (p : FlagDegree) (hp : HybridApplies p) :
    ordinaryCostOf p = hybridCost p := by
  unfold ordinaryCostOf
  rw [if_pos hp]

theorem ordinaryCostOf_le_of_padded (p : FlagDegree) (hp : ¬ HybridApplies p) :
    ordinaryCostOf p = paddedCost 131072 131073 p := by
  unfold ordinaryCostOf
  rw [if_neg hp]

/-- Both per-factor bounds: the padded one always, the hybrid one when it applies. -/
def OwnBound (count : ℕ) (p : FlagDegree) : Prop :=
  count ≤ paddedCost 131072 131073 p ∧ (HybridApplies p → count ≤ hybridCost p)

theorem ownBound_le_ordinaryCostOf {count : ℕ} {p : FlagDegree} (h : OwnBound count p) :
    count ≤ ordinaryCostOf p := by
  unfold ordinaryCostOf
  split_ifs with hp
  · exact h.2 hp
  · exact h.1


end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCost

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchProductRoute. -/
section PackedLocator_LocatorBatchProductRoute

/-!
# Collision-free extraction from a batch of regular factors

Let `A` be a finite set of distinct regular factors and let `P` be their
product.  Suppose a shared power route has reached a quotient family `q` at
depth `j`, so an original row has the form `P^j * q v`.  At the first stage
where not every factor divides every value of `q`, the nonuniversal
divisibility conditions are proper submodules.  A finite-union argument
chooses one `v` avoiding all of them simultaneously.

For `F ∈ A` put `G_F = ∏ (A.erase F)` and retain the cofactor in the
helper:

`Q_F = G_F^j * q v`.

Then `P^j * q v = F^j * Q_F`.  Consequently the order-`j` derivative
extraction makes `Q_F` vanish on every `F`-regular seed, including seeds at
which another factor vanishes.  There is no internal-collision error term or
collision charge.  Pairwise coprimality also gives `IsRelPrime F Q_F`, and
the cofactor exactly restores all residual weight lost to the other factors.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorTwoFactorAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-! ## Divisibility subspaces and simultaneous avoidance -/

/-- The preimage under a linear polynomial family of the principal ideal
generated by `F`. -/
def dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) : Submodule K V where
  carrier := {v | F ∣ q v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x + y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' := by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

@[simp] theorem mem_dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) (v : V) :
    v ∈ dvdSubmodule q F ↔ F ∣ q v := Iff.rfl

theorem dvdSubmodule_ne_top_of_not_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K)
    (h : ¬ ∀ v, F ∣ q v) :
    dvdSubmodule q F ≠ ⊤ := by
  intro htop
  apply h
  intro v
  have hv : v ∈ dvdSubmodule q F := by rw [htop]; trivial
  exact hv

/-- A field with more elements than the number of nonuniversal factors
contains one vector avoiding every corresponding divisibility subspace.
The vector is automatically nonzero when the factor set is nonempty. -/
theorem exists_avoiding_nonuniversal_factors
    [AddCommGroup V] [Module K V]
    {A : Type} [DecidableEq A] (s : Finset A) (hs : s.Nonempty)
    (q : V →ₗ[K] P4 K) (factor : A → P4 K)
    (hnonuniversal : ∀ a ∈ s, ¬ ∀ v, factor a ∣ q v)
    (hcard : s.card < ENat.card K) :
    ∃ v, v ≠ 0 ∧ ∀ a ∈ s, ¬ factor a ∣ q v := by
  classical
  let bad : s → Submodule K V := fun a => dvdSubmodule q (factor a.1)
  have hproper : ∀ a : s, bad a ≠ ⊤ := by
    intro a
    exact dvdSubmodule_ne_top_of_not_universal q (factor a.1)
      (hnonuniversal a.1 a.2)
  have hsmall : (Finset.univ : Finset s).card < ENat.card K := by
    simpa using hcard
  have hss := RCN133.finite_iUnion_ssubset
    (Finset.univ : Finset s) bad hproper hsmall
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hss
  have havoid : ∀ a : s, v ∉ bad a := by
    intro a hmem
    apply hv
    simp only [Set.mem_iUnion, Finset.mem_univ, true_and]
    exact ⟨a, trivial, hmem⟩
  have hv0 : v ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hs
    have hnot := havoid ⟨a, ha⟩
    apply hnot
    subst v
    change factor a ∣ q 0
    simp
  refine ⟨v, hv0, ?_⟩
  intro a ha
  simpa only [bad, mem_dvdSubmodule] using havoid ⟨a, ha⟩

/-! ## Products of distinct regular factors -/

/-- The squarefree product represented by a finite set of regular indices. -/
def regularProduct (H : P4 K) (A : Finset (RCN266.RegularIndex H)) : P4 K :=
  ∏ F ∈ A, F.1

/-- The complementary product after removing one regular index. -/
def regularCofactor (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) : P4 K :=
  ∏ G ∈ A.erase F, G.1

theorem regularFactor_ne_zero (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ≠ 0 :=
  (RCN167.positiveRFactors_spec H F.1 F.2).1.ne_zero

theorem regularProduct_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) : regularProduct H A ≠ 0 := by
  classical
  unfold regularProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  exact regularFactor_ne_zero H F

theorem regularCofactor_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) (F : RCN266.RegularIndex H) :
    regularCofactor H A F ≠ 0 := by
  classical
  unfold regularCofactor
  apply Finset.prod_ne_zero_iff.mpr
  intro G hG
  exact regularFactor_ne_zero H G

/-- Exact factor/cofactor decomposition of the batch product. -/
theorem regularFactor_mul_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    F.1 * regularCofactor H A F = regularProduct H A := by
  classical
  simpa only [regularProduct, regularCofactor] using
    Finset.mul_prod_erase A (fun G => G.1) hFA

/-- A regular factor is coprime to the product of all the other regular
factors in the same finite set. -/
theorem regularFactor_isRelPrime_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    IsRelPrime F.1 (regularCofactor H A F) := by
  classical
  unfold regularCofactor
  apply IsRelPrime.prod_right
  intro G hG
  have hGe := Finset.mem_erase.mp hG
  apply regularIndex_isRelPrime_of_ne H F G
  intro heq
  apply hGe.1
  exact Subtype.ext heq.symm

/-- Splitting a batch power around one selected factor. -/
theorem regularProduct_power_split
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) :
    regularProduct H A ^ j * J =
      F.1 ^ j * (regularCofactor H A F ^ j * J) := by
  rw [← regularFactor_mul_cofactor H A F hFA, mul_pow]
  ring

/-- Avoiding `F` in the common residual witness makes the cofactor-retaining
helper coprime to `F`. -/
theorem regularFactor_isRelPrime_liftedHelper
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) (hnot : ¬ F.1 ∣ J) :
    IsRelPrime F.1 (regularCofactor H A F ^ j * J) := by
  have hFirred := (RCN167.positiveRFactors_spec H F.1 F.2).1
  apply hFirred.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hnot
  exact ((regularFactor_isRelPrime_cofactor H A F hFA).pow_right)
    |>.dvd_of_dvd_mul_left hd

/-! ## Exact restoration of residual weights -/

/-- Multiplying the common residual witness by the complementary product
restores precisely the weight spent on all factors other than `F`. -/
theorem cofactor_power_mul_weight_le_sub
    (weights : Fin 4 → ℕ) (B j : ℕ) (F C J : P4 K)
    (hF : F ≠ 0) (hC : C ≠ 0) (hJ : J ≠ 0)
    (hfeasible : j * wt weights (F * C) ≤ B)
    (hbound : wt weights J ≤ B - j * wt weights (F * C)) :
    wt weights (C ^ j * J) ≤ B - j * wt weights F := by
  have hFC := weightedTotalDegree_mul weights F C hF hC
  have hCJ := weightedTotalDegree_mul weights (C ^ j) J
    (pow_ne_zero j hC) hJ
  have hCp := wt_pow_eq weights C hC j
  unfold wt at hfeasible hbound hFC hCJ hCp ⊢
  rw [hFC, Nat.mul_add] at hfeasible hbound
  rw [hCp] at hCJ
  rw [hCJ]
  let f := MvPolynomial.weightedTotalDegree weights F
  let c := MvPolynomial.weightedTotalDegree weights C
  let x := MvPolynomial.weightedTotalDegree weights J
  change j * f + j * c ≤ B at hfeasible
  change x ≤ B - (j * f + j * c) at hbound
  change j * c + x ≤ B - j * f
  have htotal : j * f + (j * c + x) ≤ B := by
    calc
      j * f + (j * c + x) = (j * f + j * c) + x := by omega
      _ ≤ (j * f + j * c) + (B - (j * f + j * c)) :=
        Nat.add_le_add_left hbound _
      _ = B := Nat.add_sub_of_le hfeasible
  have htotal' : (j * c + x) + j * f ≤ B := by
    simpa only [Nat.add_comm] using htotal
  exact Nat.le_sub_of_add_le htotal'

/-- The three residual bounds for every lifted helper. -/
theorem liftedHelper_residual_bounds
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (T YS S j : ℕ) (J : P4 K) (hJ : J ≠ 0)
    (hT : wt residualTotalWeights J ≤
      T - j * wt residualTotalWeights (regularProduct H A))
    (hY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights (regularProduct H A))
    (hS : wt residualSWeights J ≤
      S - j * wt residualSWeights (regularProduct H A))
    (hTfeasible : j * wt residualTotalWeights (regularProduct H A) ≤ T)
    (hYfeasible : j * wt residualYSWeights (regularProduct H A) ≤ YS)
    (hSfeasible : j * wt residualSWeights (regularProduct H A) ≤ S) :
    wt residualTotalWeights (regularCofactor H A F ^ j * J) ≤
        T - j * wt residualTotalWeights F.1 ∧
      wt residualYSWeights (regularCofactor H A F ^ j * J) ≤
        YS - j * wt residualYSWeights F.1 ∧
      wt residualSWeights (regularCofactor H A F ^ j * J) ≤
        S - j * wt residualSWeights F.1 := by
  have hfactor := regularFactor_mul_cofactor H A F hFA
  have hF0 := regularFactor_ne_zero H F
  have hC0 := regularCofactor_ne_zero H A F
  rw [← hfactor] at hT hY hS hTfeasible hYfeasible hSfeasible
  exact ⟨
    cofactor_power_mul_weight_le_sub residualTotalWeights T j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hTfeasible hT,
    cofactor_power_mul_weight_le_sub residualYSWeights YS j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hYfeasible hY,
    cofactor_power_mul_weight_le_sub residualSWeights S j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hSfeasible hS⟩

/-! ## One common witness and all collision-free helpers -/

/-- At a nonuniversal batch stage, one vector gives coprime helpers for every
nonuniversal factor, with the sharp per-factor residual caps.

Crucially, `hnonuniversal` concerns the displayed current family `q`.  It must
be established again after every high-band projection; nonuniversality on an
earlier ambient family does not survive restriction to a kernel. -/
theorem exists_collisionFree_batch_helpers
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A N : Finset (RCN266.RegularIndex H))
    (hNA : N ⊆ A) (hN : N.Nonempty)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (j Dq w T YS S : ℕ)
    (hbox : ∀ v, q v ∈ nestedCoefficientBox K Dq w
      (T - j * wt residualTotalWeights (regularProduct H A))
      (YS - j * wt residualYSWeights (regularProduct H A))
      (S - j * wt residualSWeights (regularProduct H A)))
    (hfeasible :
      j * wt residualTotalWeights (regularProduct H A) ≤ T ∧
      j * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      j * wt residualSWeights (regularProduct H A) ≤ S)
    (hnonuniversal : ∀ F ∈ N, ¬ ∀ v, F.1 ∣ q v)
    (hcard : N.card < ENat.card K) :
    ∃ (v : V) (J : P4 K),
      v ≠ 0 ∧ J = q v ∧ J ≠ 0 ∧
      ∀ F ∈ N,
        let QF := regularCofactor H A F ^ j * J
        QF ≠ 0 ∧ IsRelPrime F.1 QF ∧
          regularProduct H A ^ j * J = F.1 ^ j * QF ∧
          wt residualTotalWeights QF ≤
            T - j * wt residualTotalWeights F.1 ∧
          wt residualYSWeights QF ≤
            YS - j * wt residualYSWeights F.1 ∧
          wt residualSWeights QF ≤
            S - j * wt residualSWeights F.1 := by
  classical
  obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
    N hN q (fun F => F.1) hnonuniversal hcard
  let J := q v
  have hJ : J ≠ 0 := by
    intro hz
    apply hv
    apply hq
    simpa only [J, map_zero] using hz
  have hweights := nested_mem_weights (hbox v) hJ
  refine ⟨v, J, hv, rfl, hJ, ?_⟩
  intro F hFN
  have hFA := hNA hFN
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 :=
    mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFN)
  have heq := regularProduct_power_split H A F hFA j J
  have hb := liftedHelper_residual_bounds H A F hFA T YS S j J hJ
    hweights.1 hweights.2.1 hweights.2.2.1
    hfeasible.1 hfeasible.2.1 hfeasible.2.2
  exact ⟨hQF, hrel, heq, hb⟩

/-! ## The current post-projection split -/

/-- Factors whose divisibility subspace is the whole *current* domain. -/
noncomputable def universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Finset (RCN266.RegularIndex H) := by
  classical
  exact A.filter fun F => ∀ v, F.1 ∣ q v

@[simp] theorem mem_universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (F : RCN266.RegularIndex H) :
    F ∈ universalFactors H A q ↔ F ∈ A ∧ ∀ v, F.1 ∣ q v := by
  classical
  simp only [universalFactors, Finset.mem_filter]

theorem universalFactors_subset
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : universalFactors H A q ⊆ A := by
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.1

/-- Individual universal divisibility combines to divisibility by the entire
squarefree regular product. -/
theorem regularProduct_dvd_of_each
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (Q : P4 K)
    (hdiv : ∀ F ∈ A, F.1 ∣ Q) : regularProduct H A ∣ Q := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [regularProduct, Finset.notMem_empty,
      Finset.prod_empty, one_dvd]
  | @insert F A hFA ih =>
      have hFdiv : F.1 ∣ Q := hdiv F (Finset.mem_insert_self F A)
      have hAdiv : regularProduct H A ∣ Q := by
        apply ih
        intro G hGA
        exact hdiv G (Finset.mem_insert_of_mem hGA)
      have hrel : IsRelPrime F.1 (regularProduct H A) := by
        unfold regularProduct
        apply IsRelPrime.prod_right
        intro G hGA
        apply regularIndex_isRelPrime_of_ne H F G
        intro heq
        apply hFA
        have hFG : F = G := Subtype.ext heq
        rwa [hFG]
      have hprod : regularProduct H (insert F A) =
          F.1 * regularProduct H A := by
        simp only [regularProduct, Finset.prod_insert hFA]
      rw [hprod]
      exact hrel.mul_dvd hFdiv hAdiv

/-- The squarefree product of any set of regular indices divides the
ambient carrier polynomial.  This is the bridge used after a universal
source split: the source controls the product's narrow coordinates, while
the selected carrier still controls its total coordinate. -/
theorem regularProduct_dvd_carrier
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) :
    regularProduct H A ∣ H := by
  apply regularProduct_dvd_of_each
  intro F _hFA
  exact (RCN167.positiveRFactors_spec H F.1 F.2).2.1

/-- The product of the current universal subset divides every value of the
current family. -/
theorem universalProduct_dvd
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) :
    ∀ v, regularProduct H (universalFactors H A q) ∣ q v := by
  intro v
  apply regularProduct_dvd_of_each
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.2 v

/-- Packaged conclusion of `exists_collisionFree_batch_helpers`. -/
def HasCollisionFreeBatchHelpers
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A N : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (j T YS S : ℕ) : Prop :=
  ∃ (v : V) (J : P4 K),
    v ≠ 0 ∧ J = q v ∧ J ≠ 0 ∧
    ∀ F ∈ N,
      let QF := regularCofactor H A F ^ j * J
      QF ≠ 0 ∧ IsRelPrime F.1 QF ∧
        regularProduct H A ^ j * J = F.1 ^ j * QF ∧
        wt residualTotalWeights QF ≤
          T - j * wt residualTotalWeights F.1 ∧
        wt residualYSWeights QF ≤
          YS - j * wt residualYSWeights F.1 ∧
        wt residualSWeights QF ≤
          S - j * wt residualSWeights F.1

/-- One explicit adapter from a current post-projection family to the U/N
case split used by the abstract phase recursion.

If every factor is universal, the first component supplies divisibility by
the whole product for the next shared quotient round.  Otherwise `U` is a
strict subset and one common witness supplies all helpers for `N = A \ U`.
The recursive child on `U` should normally be built from a fresh source; this
theorem intentionally does not claim that restricting or quotienting the
current family preserves nonuniversality. -/
theorem currentPostProjection_split
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (j Dq w T YS S : ℕ)
    (hbox : ∀ v, q v ∈ nestedCoefficientBox K Dq w
      (T - j * wt residualTotalWeights (regularProduct H A))
      (YS - j * wt residualYSWeights (regularProduct H A))
      (S - j * wt residualSWeights (regularProduct H A)))
    (hfeasible :
      j * wt residualTotalWeights (regularProduct H A) ≤ T ∧
      j * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      j * wt residualSWeights (regularProduct H A) ≤ S)
    (hfield : ∀ B : Finset (RCN266.RegularIndex H), B ⊆ A →
      B.card < ENat.card K) :
    let U := universalFactors H A q
    (∀ v, regularProduct H U ∣ q v) ∧
      (U = A ∨
        U ⊂ A ∧ HasCollisionFreeBatchHelpers H A (A \ U) q j T YS S) := by
  classical
  let U := universalFactors H A q
  have hUsub : U ⊆ A := universalFactors_subset H A q
  have hprod : ∀ v, regularProduct H U ∣ q v :=
    universalProduct_dvd H A q
  refine ⟨hprod, ?_⟩
  by_cases hall : U = A
  · exact Or.inl hall
  · right
    have hproper : U ⊂ A :=
      (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
    have hN : (A \ U).Nonempty := by
      apply Finset.sdiff_nonempty.mpr
      intro hAU
      exact hall (Finset.Subset.antisymm hUsub hAU)
    have hnonuniversal : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ q v := by
      intro F hFN hdiv
      have hparts := Finset.mem_sdiff.mp hFN
      apply hparts.2
      exact (mem_universalFactors H A q F).mpr ⟨hparts.1, hdiv⟩
    refine ⟨hproper, ?_⟩
    exact exists_collisionFree_batch_helpers H A (A \ U)
      Finset.sdiff_subset hN q hq j Dq w T YS S hbox hfeasible
      hnonuniversal (hfield (A \ U) Finset.sdiff_subset)

/-! ## Quotienting a fully universal batch -/

private theorem sub_mul_then_one (a b j:ℕ):
    a-j*b-b=a-(j+1)*b:=by
  rw [Nat.sub_sub,Nat.add_mul,one_mul]

/-- A raw constraint-kernel reconstruction lies in the nested source box as
soon as the usual contact/slope shape inequality supplies its YS cap. -/
theorem kernelReconstruct_mem_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1)):
    ∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      kernelReconstructLinear (K:=K) D w L S m nodes u0 u1 v ∈
        nestedCoefficientBox K D w L YS S:=by
  intro v d hd
  have hglobal:=reconstruct_mem_globalCoefficientBox K D w L S v.1
  have hb:=hglobal hd
  have hYS:=flag_box_ys_bound D w L S YS hw hshape
    (reconstruct K D w L S v.1) hglobal
  have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hYS
  rw [weight_fin4] at hy
  simp only [residualYSWeights] at hy
  refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
  simpa [residualYSWeights] using hy

/-- Source-entry adapter for a universally divisible squarefree regular
product.  This is the batch analogue of the single-factor private
`quotient_nested` construction: it builds the injective quotient family and
subtracts the product's four weights exactly once. -/
theorem kernelQuotient_regularProduct_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1))
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      regularProduct H A ∣ reconstruct K D w L S v.1):
    ∃ q:ConstraintKernel (K:=K) D w L S m nodes u0 u1 →ₗ[K] P4 K,
      Function.Injective q ∧
      (∀ v,reconstruct K D w L S v.1=regularProduct H A*q v) ∧
      ∀ v,q v ∈ nestedCoefficientBox K
        (D-wt (contactWeights w) (regularProduct H A)) w
        (L-wt residualTotalWeights (regularProduct H A))
        (YS-wt residualYSWeights (regularProduct H A))
        (S-wt residualSWeights (regularProduct H A)):=by
  let recon:=kernelReconstructLinear (K:=K) D w L S m nodes u0 u1
  have hdiv':∀ v,regularProduct H A ∣ recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using hdiv v
  obtain ⟨hq,hprod,hbox⟩:=quotientLinear_nested_data D w L YS S recon
    (kernelReconstructLinear_injective (K:=K) D w L S m nodes u0 u1)
    (kernelReconstruct_mem_nested D w L S m YS nodes u0 u1 hw hshape)
    (regularProduct H A) (regularProduct_ne_zero H A) hdiv'
  let q:=quotientLinear recon (regularProduct H A)
    (regularProduct_ne_zero H A) hdiv'
  refine ⟨q,hq,?_,?_⟩
  · intro v
    simpa only [recon,kernelReconstructLinear_apply,q] using hprod v
  · exact hbox

/-- If the entire current batch product divides an injective family, divide
by that product in one operation.  The family remains injective, the product
power advances from `j` to `j+1`, and all four residual coordinates are
normalized to the new exponent. -/
theorem quotient_by_universal_regularProduct
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V →ₗ[K] P4 K) (hq:Function.Injective q)
    (j Dq w T YS S:ℕ)
    (hmem:∀ v,q v ∈ nestedCoefficientBox K Dq w
      (T-j*wt residualTotalWeights (regularProduct H A))
      (YS-j*wt residualYSWeights (regularProduct H A))
      (S-j*wt residualSWeights (regularProduct H A)))
    (hdiv:∀ v,regularProduct H A ∣ q v):
    ∃ qNext:V →ₗ[K] P4 K,
      Function.Injective qNext ∧
      (∀ v,regularProduct H A^j*q v=
        regularProduct H A^(j+1)*qNext v) ∧
      ∀ v,qNext v ∈ nestedCoefficientBox K
        (Dq-wt (contactWeights w) (regularProduct H A)) w
        (T-(j+1)*wt residualTotalWeights (regularProduct H A))
        (YS-(j+1)*wt residualYSWeights (regularProduct H A))
        (S-(j+1)*wt residualSWeights (regularProduct H A)):=by
  classical
  let P:=regularProduct H A
  let qNext:=quotientLinear q P (regularProduct_ne_zero H A) hdiv
  obtain ⟨hqNext,hprod,hnext⟩:=quotientLinear_nested_data
    Dq w
      (T-j*wt residualTotalWeights P)
      (YS-j*wt residualYSWeights P)
      (S-j*wt residualSWeights P)
      q hq hmem P (regularProduct_ne_zero H A) hdiv
  refine ⟨qNext,hqNext,?_,?_⟩
  · intro v
    change P^j*q v=P^(j+1)*qNext v
    rw [hprod v,pow_succ]
    ring
  · intro v
    have hv:=hnext v
    simpa only [P,sub_mul_then_one] using hv

/-- Complete current-stage adapter.  It first partitions factors using the
displayed post-projection family.  A proper universal child emits simultaneous
helpers for its complement.  If every factor is universal, it additionally
constructs the next injective quotient family and advances the common product
power.  Thus a consumer never has to infer post-projection properness from an
earlier source stage. -/
theorem currentPostProjection_split_or_advance
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V →ₗ[K] P4 K) (hq:Function.Injective q)
    (j Dq w T YS S:ℕ)
    (hbox:∀ v,q v ∈ nestedCoefficientBox K Dq w
      (T-j*wt residualTotalWeights (regularProduct H A))
      (YS-j*wt residualYSWeights (regularProduct H A))
      (S-j*wt residualSWeights (regularProduct H A)))
    (hfeasible:
      j*wt residualTotalWeights (regularProduct H A) ≤ T ∧
      j*wt residualYSWeights (regularProduct H A) ≤ YS ∧
      j*wt residualSWeights (regularProduct H A) ≤ S)
    (hfield:∀ B:Finset (RCN266.RegularIndex H),B ⊆ A →
      B.card < ENat.card K):
    let U:=universalFactors H A q
    (∀ v,regularProduct H U ∣ q v) ∧
      ((U ⊂ A ∧ HasCollisionFreeBatchHelpers H A (A\U) q j T YS S) ∨
        (U=A ∧ ∃ qNext:V →ₗ[K] P4 K,
          Function.Injective qNext ∧
          (∀ v,regularProduct H A^j*q v=
            regularProduct H A^(j+1)*qNext v) ∧
          ∀ v,qNext v ∈ nestedCoefficientBox K
            (Dq-wt (contactWeights w) (regularProduct H A)) w
            (T-(j+1)*wt residualTotalWeights (regularProduct H A))
            (YS-(j+1)*wt residualYSWeights (regularProduct H A))
            (S-(j+1)*wt residualSWeights (regularProduct H A)))):=by
  classical
  let U:=universalFactors H A q
  obtain ⟨hprod,hcase⟩:=currentPostProjection_split H A q hq
    j Dq w T YS S hbox hfeasible hfield
  refine ⟨hprod,?_⟩
  rcases hcase with hall | hproper
  · right
    refine ⟨hall,?_⟩
    have hdivA:∀ v,regularProduct H A ∣ q v:=by
      intro v
      rw [← hall]
      exact hprod v
    exact quotient_by_universal_regularProduct H A q hq
      j Dq w T YS S hbox hdivA
  · exact Or.inl hproper

/-! ## First strict exit in a shared product-power chain -/

/-- A shared band chain exits when the post-projection universal factors form
a strict subset `U` of the current batch.  The index `j` counts additional
whole-product quotients after the displayed input family `q`; thus a source
which was quotiented once before calling this interface has original power
`j+1` at the exit. -/
def HasBatchExitStage
    [AddCommGroup V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Prop :=
  ∃ (j : Fin fuel) (U : Finset (RCN266.RegularIndex H)) (v : V) (J : P4 K),
    U ⊂ A ∧ v ≠ 0 ∧ J ≠ 0 ∧
      regularProduct H A ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta -
          j.val * wt (contactWeights w) (regularProduct H A)) w
        (T - j.val * wt residualTotalWeights (regularProduct H A))
        (YS - j.val * wt residualYSWeights (regularProduct H A))
        (S - j.val * wt residualSWeights (regularProduct H A)) ∧
      ∀ F ∈ A \ U, ¬ F.1 ∣ J

/-- The batch analogue of `exists_power_stage_of_bandBudget_succ`.  At each
band the universal subset is recomputed on the projected family.  A proper
subset exits immediately; an all-universal stage quotients the entire
squarefree product and continues.  The terminal residual inequality rules
out an all-universal final stage.

This theorem is deliberately only the linear-algebraic stage selector.  Its
consumer multiplies the retained cofactor back into `J`, performs derivative
extraction, and applies the desired helper-count cap. -/
theorem exists_batchExitStage_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (hA : A.Nonempty)
    (hsource :
      powerBandBudget delta
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          T YS S (steps + 1) < Module.finrank K V)
    (hterminal :
      T - steps * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - steps * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - steps * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfield : A.card < ENat.card K) :
    HasBatchExitStage (steps + 1) Dlow w delta T YS S H A q := by
  classical
  let P := regularProduct H A
  have hP : P ≠ 0 := by
    simpa only [P] using regularProduct_ne_zero H A
  change powerBandBudget delta
      (wt residualTotalWeights P) (wt residualYSWeights P)
      (wt residualSWeights P) T YS S (steps + 1) <
    Module.finrank K V at hsource
  change
    T - steps * wt residualTotalWeights P < wt residualTotalWeights P ∨
    YS - steps * wt residualYSWeights P < wt residualYSWeights P ∨
    S - steps * wt residualSWeights P < wt residualSWeights P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hfirst : delta * channelCount T YS S < Module.finrank K V := by
          simpa only [powerBandBudget, Nat.add_zero] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v, hv⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        have hdivT : wt residualTotalWeights P ≤
            wt residualTotalWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualTotalWeights P
              (qOne v) (hdivP v) hqv
        have hdivY : wt residualYSWeights P ≤
            wt residualYSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualYSWeights P
              (qOne v) (hdivP v) hqv
        have hdivS : wt residualSWeights P ≤
            wt residualSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualSWeights P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hs
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          powerBandBudget delta
              (wt residualTotalWeights P) (wt residualYSWeights P)
              (wt residualSWeights P)
              (T - wt residualTotalWeights P)
              (YS - wt residualYSWeights P)
              (S - wt residualSWeights P) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T YS S +
                powerBandBudget delta
                  (wt residualTotalWeights P) (wt residualYSWeights P)
                  (wt residualSWeights P)
                  (T - wt residualTotalWeights P)
                  (YS - wt residualYSWeights P)
                  (S - wt residualSWeights P) (steps + 1) <
              Module.finrank K V := by
          simpa only [powerBandBudget, Nat.succ_eq_add_one,
            Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo := quotientLinear qOne P hP hdivP
        obtain ⟨hqTwo, _hprodTwo, hqTwoBox⟩ :=
          quotientLinear_nested_data Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh := Dlow - wt (contactWeights w) P
        let DOneLow := Dlow - delta - wt (contactWeights w) P
        let TOne := T - wt residualTotalWeights P
        let YOne := YS - wt residualYSWeights P
        let SOne := S - wt residualSWeights P
        have hwidthRest : DOneHigh ≤ DOneLow + delta := by
          simp only [DOneHigh, DOneLow]
          omega
        have hterminalRest :
            TOne - steps * wt residualTotalWeights P <
                wt residualTotalWeights P ∨
            YOne - steps * wt residualYSWeights P <
                wt residualYSWeights P ∨
            SOne - steps * wt residualSWeights P <
                wt residualSWeights P := by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using ht
          · right; left
            simpa only [YOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hy
          · right; right
            simpa only [SOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hs
        obtain ⟨j, child, v, J, hchild, hv, hJ, heq, hbox, havoid⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hwidthRest qTwo hqTwo
            (by simpa only [qTwo, DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [TOne, YOne, SOne] using hlowOneRank)
            hterminalRest
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, child, v.1, J, hchild, ?_, hJ, ?_, ?_, havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P ^ (j.val + 1) * J = q v.1
          calc
            P ^ (j.val + 1) * J = P * (P ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = P * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne P hdivP v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) P =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) P := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights P =
              T - (j.val + 1) * wt residualTotalWeights P := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights P =
              YS - (j.val + 1) * wt residualYSWeights P := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights P =
              S - (j.val + 1) * wt residualSWeights P := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          change J ∈ nestedCoefficientBox K
            (DOneLow - j.val * delta -
              j.val * wt (contactWeights w) P) w
            (TOne - j.val * wt residualTotalWeights P)
            (YOne - j.val * wt residualYSWeights P)
            (SOne - j.val * wt residualSWeights P) at hbox
          change J ∈ nestedCoefficientBox K
            (Dlow - (j.val + 1) * delta -
              (j.val + 1) * wt (contactWeights w) P) w
            (T - (j.val + 1) * wt residualTotalWeights P)
            (YS - (j.val + 1) * wt residualYSWeights P)
            (S - (j.val + 1) * wt residualSWeights P)
          rw [hD, hT, hY, hS] at hbox
          exact hbox
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid

/-! ## Derivative extraction has no internal-collision locus -/

/-- The retained complementary product is part of the helper passed to the
power-extraction lemma.  Hence this conclusion holds on every regular seed,
without assuming that the complementary product specializes nonzero. -/
theorem specialization_eq_zero_of_batch_power
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (P : Polynomial K) (gamma : K) (J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F.1 = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F.1) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (regularProduct H A ^ j * J)) = 0) :
    RCN319.specialization K P gamma
      (regularCofactor H A F ^ j * J) = 0 := by
  rw [regularProduct_power_split H A F hFA j J] at hpower
  exact specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F.1 (regularCofactor H A F ^ j * J)
    hfactorial hFzero hregular hpower

/-- Kernel/contact wrapper for the collision-free batch extraction.  The
only capacity cost is the derivative order `j`; no specialization condition
on any other regular factor appears. -/
theorem batch_helper_zero_on_regularSeeds
    {I : Type} [Fintype I] [DecidableEq I]
    (j D Dlow w L S m agreements p : ℕ)
    [CharP K p] (hp : p.Prime)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (J : P4 K)
    (hj : 1 ≤ j) (hjchar : j < p) (hw : 1 ≤ w)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hcapacity : Dlow ≤ (m - j) * agreements + j * (w - 1))
    (hlow : reconstruct K D w L S v.1 ∈
      globalCoefficientBox K Dlow w L S)
    (heq : regularProduct H A ^ j * J = reconstruct K D w L S v.1) :
    ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (regularCofactor H A F ^ j * J) = 0 := by
  classical
  intro gamma hgamma
  have hgammaG := regularSeeds_subset H selected Gamma F hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard : agreements ≤ support.card := hagreement gamma hgammaG
  have hcap : Dlow ≤ (m - j) * support.card + j * (w - 1) :=
    hcapacity.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (m - j) hcard) _)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
    j D Dlow w L S m nodes u0 u1 v hlow
    (selected gamma) gamma support hj hw (hdegree gamma hgammaG)
    hcap hvalues
  rw [← heq] at hder
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  exact specialization_eq_zero_of_batch_power H A F hFA j
    (selected gamma) gamma J
    (factorial_ne_zero_of_lt_char p j hp hjchar)
    hFzero hregular hder

/-! ## Numerical one-split interface -/

/-- A one-split counting lemma.  Factors in `U` are the universal branch and
are charged by an ordinary cap; every other factor is charged by the helper
obtained from the common batch witness.  All numerical work is isolated in
the final branch inequality. -/
theorem regularSeeds_sum_le_of_one_split
    (H : P4 K) (A U : Finset (RCN266.RegularIndex H)) (hUA : U ⊆ A)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ordinaryCap helperCap : RCN266.RegularIndex H → ℕ) (B : ℕ)
    (hordinary : ∀ F ∈ U,
      (regularSeeds H selected Gamma F).card ≤ ordinaryCap F)
    (hhelper : ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ helperCap F)
    (hbranch : (∑ F ∈ U, ordinaryCap F) +
      (∑ F ∈ A \ U, helperCap F) ≤ B) :
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤ B := by
  classical
  have hsplit : A = U ∪ (A \ U) := by
    ext F
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hFA
      by_cases hFU : F ∈ U
      · exact Or.inl hFU
      · exact Or.inr ⟨hFA, hFU⟩
    · intro h
      exact h.elim (fun h => hUA h) (fun h => h.1)
  have hdisjoint : Disjoint U (A \ U) := by
    apply Finset.disjoint_left.mpr
    intro F hFU hFd
    exact (Finset.mem_sdiff.mp hFd).2 hFU
  rw [hsplit, Finset.sum_union hdisjoint]
  exact (Nat.add_le_add
    (Finset.sum_le_sum fun F hF => hordinary F hF)
    (Finset.sum_le_sum fun F hF => hhelper F hF)).trans hbranch

/-! ## Abstract recursion by a phase potential

The state type below is deliberately indexed by an arbitrary well-founded
phase rank.  A state may therefore carry the current quotient space, its
post-projection linear family, the product identity, and all box receipts;
none of those data has to be compressed into a flag.  Its `factors` are
exactly the factors universal immediately after the preceding projection.

At a successor state a consumer has two choices.

* Stop, by showing that the sum of ordinary per-factor caps fits the current
  potential.
* Produce a child state on the universal subset `U`.  All factors in `A \ U`
  must receive helper bounds from the *current* post-projection family.  The
  child potential plus those helper caps must fit the parent potential.

The child may have `U = A`; the phase rank then records one fewer band of the
same source.  When `U ⊂ A`, the child may instead reset to a fresh source and
the phase rank can encode a lexicographic measure such as aggregate positive
R-weight followed by that source's remaining bands.  At rank zero `hbase` is the
terminal receipt (usually the fact that no nonempty universal subset fits the
residual box, followed by one last simultaneous-avoidance split).
-/

/-- Soundness of a recursive post-projection partition certificate.  This is
pure finite-sum bookkeeping: all algebraic obligations are localized in
`hstep`, and all numerical obligations are localized in `hbase`, the stop
alternative, and the displayed potential inequality. -/
theorem sum_count_le_of_phasePotential
    {A : Type} [DecidableEq A]
    (count ordinaryCap : A → ℕ)
    (State : ℕ → Type)
    (factors : (n : ℕ) → State n → Finset A)
    (potential : (n : ℕ) → State n → ℕ)
    (hordinary : ∀ a, count a ≤ ordinaryCap a)
    (hbase : ∀ s : State 0,
      (∑ a ∈ factors 0 s, ordinaryCap a) ≤ potential 0 s)
    (hstep : ∀ n (s : State (n + 1)),
      ((∑ a ∈ factors (n + 1) s, ordinaryCap a) ≤
          potential (n + 1) s) ∨
        ∃ (t : State n) (helperCap : A → ℕ),
          factors n t ⊆ factors (n + 1) s ∧
          (∀ a ∈ factors (n + 1) s \ factors n t,
            count a ≤ helperCap a) ∧
          potential n t +
              (∑ a ∈ factors (n + 1) s \ factors n t, helperCap a) ≤
            potential (n + 1) s)
    (n : ℕ) (s : State n) :
    (∑ a ∈ factors n s, count a) ≤ potential n s := by
  induction n with
  | zero =>
      exact (Finset.sum_le_sum fun a _ha => hordinary a).trans (hbase s)
  | succ n ih =>
      rcases hstep n s with hstop | ⟨t, helperCap, hsub, hhelper, hpot⟩
      · exact (Finset.sum_le_sum fun a _ha => hordinary a).trans hstop
      · let current := factors (n + 1) s
        let universal := factors n t
        have hsplit : current = universal ∪ (current \ universal) := by
          ext a
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · intro ha
            by_cases hau : a ∈ universal
            · exact Or.inl hau
            · exact Or.inr ⟨ha, hau⟩
          · intro ha
            exact ha.elim (fun hau => hsub hau) (fun hd => hd.1)
        have hdisjoint : Disjoint universal (current \ universal) := by
          apply Finset.disjoint_left.mpr
          intro a hau had
          exact (Finset.mem_sdiff.mp had).2 hau
        change (∑ a ∈ current, count a) ≤ potential (n + 1) s
        rw [hsplit, Finset.sum_union hdisjoint]
        exact (Nat.add_le_add (ih t)
          (Finset.sum_le_sum fun a ha => hhelper a ha)).trans hpot

/-- Specialization of the abstract phase-potential recursion to regular-seed
counts.  `OwnBound` is precisely the ordinary stopping interface already
produced by `LocatorFixedOwnBound`; batch helper consumers need only populate
the second branch of `hstep`. -/
theorem regularSeeds_sum_le_of_phasePotential
    (H : P4 K) (selected : K → Polynomial K) (Gamma : Finset K)
    (State : ℕ → Type)
    (factors : (n : ℕ) → State n →
      Finset (RCN266.RegularIndex H))
    (potential : (n : ℕ) → State n → ℕ)
    (hown : ∀ F, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : ∀ s : State 0,
      (∑ F ∈ factors 0 s,
        LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H F)) ≤
          potential 0 s)
    (hstep : ∀ n (s : State (n + 1)),
      ((∑ F ∈ factors (n + 1) s,
          LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H F)) ≤
            potential (n + 1) s) ∨
        ∃ (t : State n) (helperCap : RCN266.RegularIndex H → ℕ),
          factors n t ⊆ factors (n + 1) s ∧
          (∀ F ∈ factors (n + 1) s \ factors n t,
            (regularSeeds H selected Gamma F).card ≤ helperCap F) ∧
          potential n t +
              (∑ F ∈ factors (n + 1) s \ factors n t, helperCap F) ≤
            potential (n + 1) s)
    (n : ℕ) (s : State n) :
    (∑ F ∈ factors n s,
      (regularSeeds H selected Gamma F).card) ≤ potential n s := by
  classical
  apply sum_count_le_of_phasePotential
    (fun F : RCN266.RegularIndex H =>
      (regularSeeds H selected Gamma F).card)
    (fun F : RCN266.RegularIndex H =>
      LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H F))
    State factors potential
  · intro F
    exact LocatorHybridCost.ownBound_le_ordinaryCostOf (hown F)
  · exact hbase
  · exact hstep

/-! ## Complete descent through one source phase

The rank-indexed interface above is convenient while constructing one
particular algebraic route.  Numerical prefix certificates use a different
view: keep applying the same source while it routes the current aggregate,
and stop at the first nonrouteable strict subaggregate.  The next two lemmas
are the finite-set induction engine for that view.

Crucially, a routed step must return a *strict* child.  Thus its algebraic
implementation may restart from a fresh source on that child; no claim about
mixed powers in the preceding source family is hidden in this bookkeeping.
-/

/-- Repeatedly remove a helper-charged complement while `routeable` holds.
At the terminal subaggregate the single shared `defect` bounds what remains
above the additive charge. -/
theorem sum_count_le_charge_add_defect_of_strict_routes
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (ambient : Finset A) (defect : ℕ)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      (∑ a ∈ ambient, charge a) + defect := by
  classical
  have aux : ∀ B : Finset A, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect := by
    intro B
    induction B using Finset.strongInduction with
    | H B ih =>
        intro hB
        by_cases hr : routeable B
        · obtain ⟨U, hUB, hexit⟩ := hroute B hB hr
          have hUsub : U ⊆ B := hUB.subset
          have hUambient : U ⊆ ambient := hUsub.trans hB
          have hUbound := ih U hUB hUambient
          let exited := B \ U
          have hexit' : (∑ a ∈ exited, count a) ≤
              (∑ a ∈ exited, charge a) := by
            simpa only [exited] using hexit
          have hsplit : B = U ∪ exited := by
            dsimp only [exited]
            exact (Finset.union_sdiff_of_subset hUsub).symm
          have hdisjoint : Disjoint U exited := by
            apply Finset.disjoint_left.mpr
            intro a hau had
            change a ∈ B \ U at had
            exact (Finset.mem_sdiff.mp had).2 hau
          calc
            (∑ a ∈ B, count a) =
                (∑ a ∈ U, count a) + (∑ a ∈ exited, count a) := by
              rw [hsplit, Finset.sum_union hdisjoint]
            _ ≤ ((∑ a ∈ U, charge a) + defect) +
                (∑ a ∈ exited, charge a) :=
              Nat.add_le_add hUbound hexit'
            _ = (∑ a ∈ B, charge a) + defect := by
              rw [hsplit, Finset.sum_union hdisjoint]
              omega
        · exact hterminal B hB hr
  exact aux ambient (fun _ ha => ha)

/-- One numerical phase transition.  `previous` is the already certified
bound before adding this source.  A nonrouteable terminal row bounds the
previous excess over the new additive charge, while a routeable row supplies
a strict child and helper-charged complement.  The resulting bound is the
minimum of retaining the previous certificate and using the new phase. -/
theorem sum_count_le_min_previous_onePhase
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (previous : Finset A → ℕ)
    (ambient : Finset A) (defect : ℕ)
    (hprevious : ∀ B, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ previous B)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      previous B ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      min (previous ambient) ((∑ a ∈ ambient, charge a) + defect) := by
  classical
  apply le_min
  · exact hprevious ambient (fun _ ha => ha)
  · apply sum_count_le_charge_add_defect_of_strict_routes
      count charge routeable ambient defect
    · intro B hB hnroute
      exact (hprevious B hB).trans (hterminal B hB hnroute)
    · exact hroute

end

end ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end PackedLocator_LocatorBatchProductRoute

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch. -/
section PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Unequal-pair parameters for a regular factor and an arbitrary helper
source.  Keeping the source parameters explicit lets all external locator
profiles share one factor-switch proof. -/
def helperPair (L YS S leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181392, leftY, leftR, leftZ, YS, S, L⟩

def HelperPairGates (L YS S leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair L YS S leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- For each regular irreducible factor, either it divides an entire source
kernel or one source witness is coprime to it and supplies the unequal-pair
count. -/
theorem divisor_or_helper_count
    (D L S m YS : ℕ) (hD : 0 < D) (hDa : D ≤ m * 181392)
    (hshape : D + S ≤ 131071 * (YS + 1))
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates L YS S leftY leftR leftZ) :
    (∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        (helperPair L YS S leftY leftR leftZ).regularCountCap := by
  classical
  by_cases hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K D 131071 L S v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K D 131071 L S :=
      reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
    have hQYS : wt residualYSWeights Q ≤ YS := by
      apply flag_box_ys_bound D 131071 L S YS (by decide) hshape Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      D 131071 L S hD).mp hQbox
    have hQY : Q.degreeOf 1 ≤ YS :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ S :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ L :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply regularSeeds_count_le_intersection
      (helperPair L YS S leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        norm_num [I, IRSProfile.Index])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, Nat.reduceSub] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      D 131071 L S m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hDa.trans (Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch
end PackedLocator_LocatorGenericHelperFactorSwitch

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericPowerRoute. -/
section PackedLocator_LocatorGenericPowerRoute

/-!
# A generic arbitrary-power locator route

This file packages the three generic ingredients needed by the replacement
grid.  A source first supplies either an immediate helper-pair bound or a
common factor.  In the common-factor branch, arbitrary many high-band
projections select an `F`-adic stage.  The arbitrary contact and product
lemmas then make its terminal quotient vanish on every regular seed, and the
same unequal-pair count charges that stage.

There is no hard-coded maximum power and no source-specific arithmetic here.
-/

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open LocatorGenericHelperFactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Lower and upper cumulative-weight bounds for one factor cell. -/
structure PowerRouteBox where
  tLo : ℕ
  tHi : ℕ
  yLo : ℕ
  yHi : ℕ
  rLo : ℕ
  rHi : ℕ
  deriving DecidableEq

/-- The unequal-pair profile charged after removing `j` copies of a factor. -/
def stagePair (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) :
    UnequalParameters :=
  helperPair (L - j * b.tLo) (YS - j * b.yLo) (S - j * b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) : ℕ :=
  (stagePair L YS S b j).regularCountCap

/-- Maximum of the initial helper cost and every power-stage cost through
`k`.  Primitive recursion avoids a large finite computation in receipts. -/
def routeCost (L YS S : ℕ) (b : PowerRouteBox) : ℕ → ℕ
  | 0 => stageCost L YS S b 0
  | k + 1 => max (routeCost L YS S b k) (stageCost L YS S b (k + 1))

theorem stageCost_le_routeCost (L YS S : ℕ) (b : PowerRouteBox)
    {j k : ℕ} (hjk : j ≤ k) :
    stageCost L YS S b j ≤ routeCost L YS S b k := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      exact le_rfl
  | succ k ih =>
      rw [routeCost]
      by_cases hj : j ≤ k
      · exact (ih hj).trans (Nat.le_max_left _ _)
      · have hjeq : j = k + 1 := by omega
        subst j
        exact Nat.le_max_right _ _

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- The generic form of `count_le_stageCost`. -/
theorem regularSeeds_count_le_stageCost
    (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (F : RegularIndex H)
    (hFY : F.1.degreeOf 1 ≤ b.yHi)
    (hFR : F.1.degreeOf 2 ≤ b.rHi)
    (hFZ : F.1.degreeOf 3 ≤ b.tHi)
    (Q : P4)
    (hQT : wt residualTotalWeights Q ≤ L - j * b.tLo)
    (hQY : wt residualYSWeights Q ≤ YS - j * b.yLo)
    (hQR : wt residualSWeights Q ≤ S - j * b.rLo)
    (hrel : IsRelPrime F.1 Q)
    (hgates : HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
      (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost L YS S b j := by
  have hQY' : Q.degreeOf 1 ≤ (stagePair L YS S b j).rightY := by
    simpa only [stagePair, helperPair] using (degreeY_le_ysWeight Q).trans hQY
  have hQR' : Q.degreeOf 2 ≤ (stagePair L YS S b j).rightR := by
    simpa only [stagePair, helperPair] using (degreeR_le_sWeight Q).trans hQR
  have hQZ : Q.degreeOf 3 ≤ (stagePair L YS S b j).rightZ := by
    simpa only [stagePair, helperPair] using (degreeZ_le_totalWeight Q).trans hQT
  obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
    hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
  have hcount := regularSeeds_count_le_intersection
    (stagePair L YS S b j) H Q F hrel 2130706433
    (by simpa only [stagePair, helperPair] using hFY)
    (by simpa only [stagePair, helperPair] using hFR)
    (by simpa only [stagePair, helperPair] using hFZ)
    hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      norm_num [I, IRSProfile.Index])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    hdegree hagreement
    (by simpa only [stagePair, helperPair, UnequalParameters.errors,
      Nat.reduceSub] using hno)
    hQzero
  simpa only [stageCost] using hcount

private theorem quotient_nested
    (D L S m YS : ℕ) (hshape : D + S ≤ 131071 * (YS + 1))
    (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F ∣ reconstruct K D 131071 L S v.1) :
    ∃ q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4,
      Function.Injective q ∧
      (∀ v, reconstruct K D 131071 L S v.1 = F * q v) ∧
      (∀ v, q v ∈ nestedCoefficientBox K
        (D - wt (contactWeights 131071) F) 131071
        (L - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F)) := by
  let recon := kernelReconstructLinear (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  have hdivK : ∀ v, F ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) D 131071 L S m
      IRSProfile.domain u0 u1) F hF hdivK
  have hprod (v) : recon v = F * q v :=
    recon_eq_mul_quotientPolynomial recon F hdivK v
  have hproduct : ∀ v, reconstruct K D 131071 L S v.1 = F * q v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hprod v
  have hqbox : ∀ v, q v ∈ globalCoefficientBox K
      (D - wt (contactWeights 131071) F) 131071
      (L - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_box_of_full_divisor D 131071 L S m
      (wt (contactWeights 131071) F) (wt residualTotalWeights F)
      (wt residualSWeights F) IRSProfile.domain u0 u1 F hF hdivK
      le_rfl le_rfl le_rfl
  have hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (D - wt (contactWeights 131071) F) 131071
      (L - wt residualTotalWeights F)
      (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
    intro v
    have hqYS : wt residualYSWeights (q v) ≤
        YS - wt residualYSWeights F := by
      by_cases hv : v = 0
      · subst v
        simp [wt, MvPolynomial.weightedTotalDegree]
      · have hqv : q v ≠ 0 := by
          intro hz
          apply hv
          apply hqinj
          simpa only [map_zero] using hz
        have hsrc : wt residualYSWeights
            (reconstruct K D 131071 L S v.1) ≤ YS := by
          apply flag_box_ys_bound D 131071 L S YS (by decide) hshape
          exact reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
        have hmul := weightedTotalDegree_mul residualYSWeights F (q v) hF hqv
        rw [← hproduct v] at hmul
        simp only [wt] at hsrc ⊢
        omega
    intro d hd
    have hb := hqbox v hd
    have hy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hqYS
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
    simpa [residualYSWeights] using hy
  exact ⟨q, hqinj, hproduct, hqNested⟩

private theorem sub_one_then_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem sub_pair_then_mul (a x y j : ℕ) :
    a - x - y - j * x - j * y =
      a - (j + 1) * x - (j + 1) * y := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem reconstruct_mem_low_of_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (F Q : P4) (heq : reconstruct K D 131071 L S v.1 = F ^ j * Q)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) Q <
      Dlow - j * wt (contactWeights 131071) F) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [heq]
  have hmul := wt_mul_le (contactWeights 131071) (F ^ j) Q
  have hp := wt_pow_le (contactWeights 131071) F j
  omega

/-- One theorem replaces every source-specific `count_k2`, ..., `count_kN`
ladder.  The source arithmetic appears only in `hband`, `hgapLe`, capacity,
and positivity receipts. -/
theorem regularSeeds_count_le_arbitraryPowerRoute
    (D L S m YS gap delta k : ℕ) (b : PowerRouteBox)
    (hD : 0 < D) (hDa : D ≤ m * 181392)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hk : 1 ≤ k) (hkchar : k < 2130706433)
    (hband : powerBandBudget delta b.tLo b.yLo b.rLo
      (L - b.tLo) (YS - b.yLo) (S - b.rLo) k < gap)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * 181392 + j * (131071 - 1))
    (hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta)
    (hterminal : L - k * b.tLo < b.tLo ∨
      YS - k * b.yLo < b.yLo ∨ S - k * b.rLo < b.rLo)
    (hgates : ∀ j, j ≤ k →
      HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
        (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (F : RegularIndex H)
    (hFT : b.tLo ≤ wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1 ≤ b.tHi)
    (hFY : b.yLo ≤ wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1 ≤ b.yHi)
    (hFR : b.rLo ≤ wt residualSWeights F.1 ∧
      wt residualSWeights F.1 ≤ b.rHi)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost L YS S b k := by
  classical
  have hFspec := RCN167.positiveRFactors_spec H F.1 F.2
  have hF : F.1 ≠ 0 := hFspec.1.ne_zero
  have hFdegY : F.1.degreeOf 1 ≤ b.yHi :=
    (degreeY_le_ysWeight F.1).trans hFY.2
  have hFdegR : F.1.degreeOf 2 ≤ b.rHi :=
    (degreeR_le_sWeight F.1).trans hFR.2
  have hFdegZ : F.1.degreeOf 3 ≤ b.tHi :=
    (degreeZ_le_totalWeight F.1).trans hFT.2
  rcases divisor_or_helper_count D L S m YS hD hDa hshape
      selected Gamma hdegree hagreement hno F b.yHi b.rHi b.tHi
      hFdegY hFdegR hFdegZ (by
        simpa only [Nat.zero_mul, Nat.sub_zero] using
          hgates 0 (Nat.zero_le k)) with hdiv | hhelper
  · cases k with
    | zero => omega
    | succ steps =>
      obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
        quotient_nested D L S m YS hshape u0 u1 F.1 hF hdiv
      have hTstart : L - wt residualTotalWeights F.1 ≤ L - b.tLo :=
        Nat.sub_le_sub_left hFT.1 L
      have hYstart : YS - wt residualYSWeights F.1 ≤ YS - b.yLo :=
        Nat.sub_le_sub_left hFY.1 YS
      have hRstart : S - wt residualSWeights F.1 ≤ S - b.rLo :=
        Nat.sub_le_sub_left hFR.1 S
      have hbudgetMono := powerBandBudget_mono delta
        (wt residualTotalWeights F.1) (wt residualYSWeights F.1)
        (wt residualSWeights F.1)
        (L - wt residualTotalWeights F.1)
        (YS - wt residualYSWeights F.1) (S - wt residualSWeights F.1)
        b.tLo b.yLo b.rLo (L - b.tLo) (YS - b.yLo) (S - b.rLo)
        (steps + 1) hTstart hYstart hRstart hFT.1 hFY.1 hFR.1
      have hsource : powerBandBudget delta
          (wt residualTotalWeights F.1) (wt residualYSWeights F.1)
          (wt residualSWeights F.1)
          (L - wt residualTotalWeights F.1)
          (YS - wt residualYSWeights F.1)
          (S - wt residualSWeights F.1) (steps + 1) <
        Module.finrank K (ConstraintKernel (K := K) D 131071 L S m
          IRSProfile.domain u0 u1) := by
        exact (hbudgetMono.trans_lt (by
          simpa only [Nat.succ_eq_add_one] using hband)).trans_le hgapLe
      have hwidth : D - wt (contactWeights 131071) F.1 ≤
          (D - delta - wt (contactWeights 131071) F.1) + delta := by
        omega
      obtain ⟨j0, v, J, _hv, hJ, heq, hJbox, hnotTerminal⟩ :=
        exists_power_stage_of_bandBudget_succ steps
          (D - wt (contactWeights 131071) F.1)
          (D - delta - wt (contactWeights 131071) F.1)
          131071 delta
          (L - wt residualTotalWeights F.1)
          (YS - wt residualYSWeights F.1)
          (S - wt residualSWeights F.1)
          hwidth q hqinj hqNested F.1 hF hsource
      let j := j0.val + 1
      have hjpos : 1 ≤ j := by simp only [j]; omega
      have hjle : j ≤ Nat.succ steps := by
        simp only [j]
        omega
      have heqOriginal : reconstruct K D 131071 L S v.1 = F.1 ^ j * J := by
        calc
          reconstruct K D 131071 L S v.1 = F.1 * q v := hproduct v
          _ = F.1 * (F.1 ^ j0.val * J) := by rw [heq]
          _ = F.1 ^ j * J := by
            simp only [j, pow_succ', mul_assoc]
      have hweights := nested_mem_weights hJbox hJ
      have hJTactual : wt residualTotalWeights J ≤
          L - j * wt residualTotalWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.1
      have hJYactual : wt residualYSWeights J ≤
          YS - j * wt residualYSWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.2.1
      have hJRactual : wt residualSWeights J ≤
          S - j * wt residualSWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.2.2.1
      have hJT : wt residualTotalWeights J ≤ L - j * b.tLo :=
        hJTactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFT.1) L)
      have hJY : wt residualYSWeights J ≤ YS - j * b.yLo :=
        hJYactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFY.1) YS)
      have hJR : wt residualSWeights J ≤ S - j * b.rLo :=
        hJRactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFR.1) S)
      have hJcontact : wt (contactWeights 131071) J <
          D - j * delta - j * wt (contactWeights 131071) F.1 := by
        simpa only [j, sub_pair_then_mul] using hweights.2.2.2
      have hlow : reconstruct K D 131071 L S v.1 ∈
          globalCoefficientBox K (D - j * delta) 131071 L S :=
        reconstruct_mem_low_of_power u0 u1 v F.1 J heqOriginal hD
          (hlowpos j hjpos hjle) hJcontact
      have hrel : IsRelPrime F.1 J := by
        by_cases hjlt : j < Nat.succ steps
        · apply hFspec.1.isRelPrime_iff_not_dvd.mpr
          apply hnotTerminal
          simpa only [j, Nat.succ_eq_add_one] using hjlt
        · have hjeq : j = Nat.succ steps := by omega
          rcases hterminal with ht | hy | hr
          · apply isRelPrime_of_weight_lt residualTotalWeights F.1 J
              hFspec.1 hJ
            exact hJT.trans_lt (by rw [hjeq]; exact ht.trans_le hFT.1)
          · apply isRelPrime_of_weight_lt residualYSWeights F.1 J
              hFspec.1 hJ
            exact hJY.trans_lt (by rw [hjeq]; exact hy.trans_le hFY.1)
          · apply isRelPrime_of_weight_lt residualSWeights F.1 J
              hFspec.1 hJ
            exact hJR.trans_lt (by rw [hjeq]; exact hr.trans_le hFR.1)
      have hJzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
          RCN319.specialization K (selected gamma) gamma J = 0 := by
        intro gamma hgamma
        have hgammaG := regularSeeds_subset H selected Gamma F hgamma
        let support := (Finset.univ : Finset I).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)
        have hcard : 181392 ≤ support.card := hagreement gamma hgammaG
        have hcap : D - j * delta ≤
            (m - j) * support.card + j * (131071 - 1) :=
          (hcapacity j hjpos hjle).trans
            (Nat.add_le_add_right (Nat.mul_le_mul_left (m - j) hcard) _)
        have hvalues : ∀ i ∈ support,
            (selected gamma).eval (IRSProfile.domain i) =
              u0 i + gamma * u1 i := by
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
          j D (D - j * delta) 131071 L S m IRSProfile.domain u0 u1
          v hlow (selected gamma) gamma support hjpos (by decide)
          (hdegree gamma hgammaG) hcap hvalues
        rw [heqOriginal] at hder
        obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
        apply specialization_eq_zero_of_iteratePderivR_power_product
          j (selected gamma) gamma F.1 J
          (factorial_ne_zero_of_lt_char 2130706433 j
            (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
            (hjle.trans_lt hkchar))
          hFzero hregular hder
      have hstage := regularSeeds_count_le_stageCost L YS S b j u0 u1 H
        selected Gamma hdegree hagreement hno F hFdegY hFdegR hFdegZ J
        hJT hJY hJR hrel (hgates j hjle) hJzero
      exact hstage.trans (stageCost_le_routeCost L YS S b hjle)
  · have hzeroCost :
      (helperPair L YS S b.yHi b.rHi b.tHi).regularCountCap =
        stageCost L YS S b 0 := by
      simp only [stageCost, stagePair, Nat.zero_mul, Nat.sub_zero]
    rw [hzeroCost] at hhelper
    exact hhelper.trans (stageCost_le_routeCost L YS S b (Nat.zero_le k))

end

end ProximityPrize.SubmissionLower.LocatorGenericPowerRoute
end PackedLocator_LocatorGenericPowerRoute

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Oracle. -/
section PackedLocator_LocatorPhase6800Oracle

/-!
# Compact numerical oracle for the 6800 regular-factor phases

This module contains only the small, reusable interface of the numerical
certificate.  The generated receipt rows live in separate modules.  A raw
state `⟨z,v,r⟩` represents cumulative degrees
`(total, middle, slope) = (z+v+r,v+r,r)`.

The four source phases are, in order, R1200, C, Split500 and Split390.  Three
prefixes forget `z`.  The C prefix retains 304-wide buckets (offset 64) only
on the critical rectangle `r ≤ 17, v ≤ 64`; outside that rectangle it too
forgets `z`.  This is a sound weakening of the exact prefix recurrence.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Coefficients of an additive potential in cumulative coordinates. -/
structure Potential where
  totalCoeff : ℕ
  middleCoeff : ℕ
  slopeCoeff : ℕ
  deriving DecidableEq, Repr

def Potential.eval (q : Potential) (p : FlagDegree) : ℕ :=
  q.totalCoeff * total p + q.middleCoeff * middle p + q.slopeCoeff * p.all

theorem Potential.eval_add (q : Potential) (p₁ p₂ : FlagDegree) :
    q.eval (p₁ + p₂) = q.eval p₁ + q.eval p₂ := by
  simp only [Potential.eval, total, middle, add_zOnly, add_yz, add_all]
  ring

def initialAPotential : Potential :=
  ⟨5743475809, 6005121364168, 21911127063412⟩

def r1200Potential : Potential :=
  ⟨838198457457, 41455507273331, 186115326859727⟩

def sourceCPotential : Potential :=
  ⟨41132210671, 14335626014136, 66219052881273⟩

def split500Potential : Potential :=
  ⟨146029069163, 4437943401105, 19816600189433⟩

def split390Potential : Potential :=
  ⟨88144439190, 3188908333526, 14353416140113⟩

/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def sourceR1200 : SourceNumbers :=
  ⟨82100, 1660, 370, 19825077939631510⟩

def sourceC : SourceNumbers :=
  ⟨130000, 373, 81, 321495185604514⟩

def sourceSplit500 : SourceNumbers :=
  ⟨21000, 691, 155, 230574129441305⟩

def sourceSplit390 : SourceNumbers :=
  ⟨19500, 539, 120, 103687669979190⟩

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50322 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ s.band p < s.gap

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def exactRouteBox (p : FlagDegree) : PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

/-- The arithmetic interface required by the algebraic source adapter.  The
stage-cost and gate checks are deliberately separate from band thresholds. -/
structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

/-- Raw-to-cumulative flag constructor. -/
def rawFlag (r v z : ℕ) : FlagDegree := ⟨z, v, r⟩

@[simp] theorem rawFlag_all (r v z : ℕ) : (rawFlag r v z).all = r := rfl
@[simp] theorem rawFlag_middle (r v z : ℕ) : middle (rawFlag r v z) = r + v := by
  simp [rawFlag, middle, Nat.add_comm]
@[simp] theorem rawFlag_total (r v z : ℕ) : total (rawFlag r v z) = r + v + z := by
  simp [rawFlag, total, Nat.add_comm, Nat.add_left_comm]

/-- The C-prefix bucket used by the compact receipt. -/
def cBucket (z : ℕ) : ℕ := if z ≤ 64 then 0 else (z - 64 + 303) / 304

theorem cBucket_le_20 (z : ℕ) (hz : z ≤ 5964) : cBucket z ≤ 20 := by
  unfold cBucket
  split <;> omega

/-- Exact maximum additive A-potential available to a complementary raw flag
inside the wide cumulative box `(5964,153,33)`. -/
def initialAComplement (p : FlagDegree) : ℕ :=
  let t := 5964 - total p
  let y := 153 - middle p
  let r := 33 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAPotential.eval (rawFlag nr nv (t' - nv))

/-- The greedy complement is maximal for the A potential among all raw flags
that can be added to `p` inside the wide box. -/
theorem initialAPotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 5964)
    (hy : middle p + middle n ≤ 153)
    (hr : p.all + n.all ≤ 33) :
    initialAPotential.eval n ≤ initialAComplement p := by
  have hnpY : n.all ≤ middle n := by simp [middle]
  have hnpT : middle n ≤ total n := by simp [middle, total]
  have hppY : p.all ≤ middle p := by simp [middle]
  have hppT : middle p ≤ total p := by simp [middle, total]
  simp only [initialAComplement, Potential.eval, initialAPotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega

def sumFlag {ι : Type} (s : Finset ι) (p : ι → FlagDegree) : FlagDegree :=
  ⟨∑ i ∈ s, (p i).zOnly, ∑ i ∈ s, (p i).yz,
    ∑ i ∈ s, (p i).all⟩

@[simp] theorem sumFlag_all {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    (sumFlag s p).all = ∑ i ∈ s, (p i).all := rfl

@[simp] theorem sumFlag_middle {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    middle (sumFlag s p) = ∑ i ∈ s, middle (p i) := by
  simp only [sumFlag, middle, Finset.sum_add_distrib]

@[simp] theorem sumFlag_total {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    total (sumFlag s p) = ∑ i ∈ s, total (p i) := by
  simp only [sumFlag, total, Finset.sum_add_distrib]

theorem sum_initialAPotential_eval {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → FlagDegree) :
    (∑ i ∈ s, initialAPotential.eval (p i)) =
      initialAPotential.eval (sumFlag s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Aggregate direct-A helper ledger for the factors that leave the initial
split.  The exact greedy complement avoids the seven-trillion loss of three
independent cumulative-coordinate remainders. -/
theorem initialA_helpers_sum_le_complement
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 5964)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 153)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 33) :
    (∑ i ∈ s, helper i) ≤ initialAComplement universal := by
  calc
    (∑ i ∈ s, helper i) ≤ ∑ i ∈ s, initialAPotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi => hhelper i hi)
    _ = initialAPotential.eval (sumFlag s p) := sum_initialAPotential_eval s p
    _ ≤ initialAComplement universal := by
      apply initialAPotential_le_complement
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr

/-- A threshold row says at which `z` each source becomes routeable for fixed
positive slope `r` and residual middle coordinate `v`. -/
structure ThresholdReceipt where
  r : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : ℕ
  split500 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def thresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  let maxZ := 5964 - (r + v)
  if threshold = 0 then s.Routeable (rawFlag r v 0)
  else if threshold ≤ maxZ then
    ¬s.Routeable (rawFlag r v (threshold - 1)) ∧
      s.Routeable (rawFlag r v threshold)
  else threshold = maxZ + 1 ∧ ¬s.Routeable (rawFlag r v maxZ)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (thresholdBoundary s r v threshold) := by
  unfold thresholdBoundary
  infer_instance

def ThresholdReceipt.Valid (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 28 ∧ q.r + q.v ≤ 127 ∧
    thresholdBoundary sourceR1200 q.r q.v q.r1200 ∧
    thresholdBoundary LocatorPhase6800Oracle.sourceC q.r q.v q.sourceC ∧
    thresholdBoundary sourceSplit500 q.r q.v q.split500 ∧
    thresholdBoundary sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable q.Valid := by
  unfold ThresholdReceipt.Valid
  infer_instance

/-- A prefix row is the defect prefix after completing slope layer `afterR`.
`sourceC` has either 21 bucket entries (on the critical rectangle) or one
fully-z-forgotten entry. -/
structure PrefixReceipt where
  afterR : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : List ℕ
  split500 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def PrefixReceipt.ExpectedShape (q : PrefixReceipt) : Prop :=
  1 ≤ q.afterR ∧ q.afterR ≤ 27 ∧ q.afterR + 1 + q.v ≤ 127 ∧
    q.sourceC.length = (if q.afterR ≤ 17 ∧ q.v ≤ 64 then 21 else 1)

instance (q : PrefixReceipt) : Decidable q.ExpectedShape := by
  unfold PrefixReceipt.ExpectedShape
  infer_instance

/-! ## Compact exact base table

For fixed raw `(r,v)`, the ordinary partition maximum is stored explicitly at
`z=0,1,2`.  From `z=3` onward it is the maximum of affine carrier lines.  A
segment stores its value at its first integer, avoiding signed intercepts.
-/

structure BaseSegment where
  start : ℕ
  valueAtStart : ℕ
  slope : ℕ
  deriving DecidableEq, Repr

def BaseSegment.evalAt (q : BaseSegment) (z : ℕ) : ℕ :=
  q.valueAtStart + q.slope * (z - q.start)

structure BaseRow where
  r : ℕ
  v : ℕ
  z0 : ℕ
  z1 : ℕ
  z2 : ℕ
  segments : List BaseSegment
  deriving DecidableEq, Repr

def evalBaseSegments : List BaseSegment → ℕ → ℕ
  | [], _ => 0
  | q :: qs, z =>
      (qs.foldl (fun best next => if next.start ≤ z then next else best) q).evalAt z

def BaseRow.evalAt (q : BaseRow) (z : ℕ) : ℕ :=
  if z = 0 then q.z0
  else if z = 1 then q.z1
  else if z = 2 then q.z2
  else evalBaseSegments q.segments z

/-- Row order used by the generated array: increasing `r`, then increasing
`v`, over `1 ≤ r ≤ 28` and `r+v ≤ 127`. -/
def baseRowIndex (r v : ℕ) : ℕ :=
  (r - 1) * 128 - ((r - 1) * r) / 2 + v

def defaultBaseRow : BaseRow := ⟨0, 0, 0, 0, 0, []⟩

def lookupBaseRow (rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  (rows[baseRowIndex r v]?).getD defaultBaseRow

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def BaseRowsIndexed (rows : Array BaseRow) : Prop :=
  rows.size = 3178 ∧
    ∀ r ∈ (List.range 28).map (fun q => q + 1),
      ∀ v ∈ List.range (128 - r),
        let q := lookupBaseRow rows r v
        q.r = r ∧ q.v = v

instance (rows : Array BaseRow) : Decidable (BaseRowsIndexed rows) := by
  unfold BaseRowsIndexed
  infer_instance

def BaseRow.ExpectedShape (q : BaseRow) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 28 ∧ q.r + q.v ≤ 127 ∧
    q.segments ≠ [] ∧ q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start) ∧
    ∀ s ∈ q.segments, s.start ≤ 5964 - (q.r + q.v)

instance (q : BaseRow) : Decidable q.ExpectedShape := by
  unfold BaseRow.ExpectedShape
  infer_instance

/-- State-local form of the base certificate.  Unlike the legacy full-box
interface below, this preserves the aggregate flag needed by every phase
transition. -/
def StateLocalBaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree),
    (∀ i ∈ s, 1 ≤ (p i).all) →
    (sumFlag s p).all ≤ 28 → middle (sumFlag s p) ≤ 127 →
    total (sumFlag s p) ≤ 5964 →
    (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap (sumFlag s p)

/-- Componentwise raw containment used by the defect-prefix recurrence. -/
def RawBelow (q p : FlagDegree) : Prop :=
  q.all ≤ p.all ∧ q.yz ≤ p.yz ∧ q.zOnly ≤ p.zOnly

def RawStrictSlopeBelow (q p : FlagDegree) : Prop :=
  RawBelow q p ∧ q.all < p.all

/-- Semantic condition checked by one phase's prefix table.  At a routeable
parent, every strict nonrouteable stopping child is paid by the stored defect.
The algebraic batch engine turns precisely this condition into the phase cap.
-/
def PhaseDefectSound (previousCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p q, p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric recurrence represented by a checked phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p

/-- Abstract base certificate.  This isolates the discrete-convexity and the
two-coordinate unbounded knapsack proof from the algebraic phase consumer. -/
def BaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (p : ι → FlagDegree),
    (∀ i, 1 ≤ (p i).all) →
    (∑ i, (p i).all) ≤ 28 →
    (∑ i, middle (p i)) ≤ 127 →
    (∑ i, total (p i)) ≤ 5964 →
    (∑ i, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap ⟨5964 - 127, 127 - 28, 28⟩

/-- Consumer-facing abstraction: numerical receipt checking yields a narrow
phase cap, while the algebraic batch route supplies the phase transitions. -/
structure CheckedPhaseOracle where
  narrowCap : FlagDegree → ℕ
  baseCap : FlagDegree → ℕ
  baseSound : BaseOracleSound baseCap
  narrow_le : ∀ p, p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    narrowCap p ≤ 259262572379051168
  joint_le : ∀ p, p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    narrowCap p + initialAComplement p ≤ 259787835303351020

/-! ## Generic finite-set transition consumed by the batch route -/

/-- A prefix defect converts a strict batch split into the next phase bound.
This is the exact bookkeeping used by every one of the four source phases;
all source-specific algebra is confined to `hchild` and `hexit`. -/
theorem phase_split_le
    {ι : Type} [DecidableEq ι]
    (A U : Finset ι) (flag : ι → FlagDegree) (count : ι → ℕ)
    (q : Potential)
    (childCap defect parentPotential : ℕ)
    (hsub : U ⊆ A)
    (hchild : (∑ i ∈ U, count i) ≤ childCap)
    (hexit : ∀ i ∈ A \ U, count i ≤ q.eval (flag i))
    (hprefix : childCap ≤ (∑ i ∈ U, q.eval (flag i)) + defect)
    (hparent : (∑ i ∈ A, q.eval (flag i)) + defect ≤ parentPotential) :
    (∑ i ∈ A, count i) ≤ parentPotential := by
  have hdisjoint : Disjoint U (A \ U) := by
    apply Finset.disjoint_left.mpr
    intro i hiU hiD
    exact (Finset.mem_sdiff.mp hiD).2 hiU
  have hsplit : A = U ∪ (A \ U) := by
    exact (Finset.union_sdiff_of_subset hsub).symm
  rw [hsplit, Finset.sum_union hdisjoint]
  have hexitSum : (∑ i ∈ A \ U, count i) ≤
      ∑ i ∈ A \ U, q.eval (flag i) :=
    Finset.sum_le_sum (fun i hi => hexit i hi)
  have hcombined : (∑ i ∈ U, count i) + (∑ i ∈ A \ U, count i) ≤
      ((∑ i ∈ U, q.eval (flag i)) + (∑ i ∈ A \ U, q.eval (flag i))) +
        defect := by
    omega
  have hpotentialSplit : (∑ i ∈ A, q.eval (flag i)) =
      (∑ i ∈ U, q.eval (flag i)) +
        (∑ i ∈ A \ U, q.eval (flag i)) := by
    rw [Nat.add_comm]
    exact (Finset.sum_sdiff hsub).symm
  rw [hpotentialSplit] at hparent
  exact hcombined.trans hparent

def certifiedNarrowMaximum : ℕ := 259262572379051168
def certifiedJointMaximum : ℕ := 259787835303351020
def tightenedRegularAllowance : ℕ := 259789186450485880

theorem certifiedJoint_lt_allowance :
    certifiedJointMaximum < tightenedRegularAllowance := by decide

theorem certifiedJoint_slack :
    tightenedRegularAllowance - certifiedJointMaximum = 1351147134860 := by
  decide

/-- Arithmetic end of the initial-A ledger.  The two hypotheses are the only
set-dependent facts required from the structural bridge. -/
theorem initialA_sum_le_certifiedJoint
    (phaseSum helperSum : ℕ) (p : FlagDegree)
    (hphase : phaseSum ≤ certifiedNarrowMaximum)
    (hhelper : helperSum ≤ certifiedJointMaximum - certifiedNarrowMaximum) :
    phaseSum + helperSum ≤ certifiedJointMaximum := by
  unfold certifiedNarrowMaximum certifiedJointMaximum at *
  omega

end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex. -/
section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

open RCN095 LocatorFactorAggregate LocatorHybridCost

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOf ⟨z, v, r⟩

theorem hybridApplies_raw (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    HybridApplies (⟨z, v, r⟩ : FlagDegree) := by
  change 2 ≤ r ∧ r + 2 ≤ v + r
  omega

theorem padS_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) :
    padS (⟨z, v, r⟩ : FlagDegree) = r := by
  simp only [padS]
  omega

theorem padY_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
  simp only [padY, middle, padS_raw_hybrid r v z hr]
  omega

theorem padT_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
  simp only [padT, total, padY_raw_hybrid r v z hr hv]
  omega

theorem sharp_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    sharpTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + (2 * v - 1) * 131072,
        (2 * r - 1) * 131072⟩ := by
  unfold sharpTail
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem rational_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    rationalFlag (⟨z, v, r⟩ : FlagDegree) =
      ⟨131074 * z, 131074 * (v - 1) + 2, 131074 * (r - 2) + 3⟩ := by
  unfold rationalFlag
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem moving_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    movingFiber (⟨z, v, r⟩ : FlagDegree) = ⟨z, v, r + 1⟩ := by
  unfold movingFiber
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem hybridCost_raw_affine (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    2 * hybridCost (⟨z + 1, v, r⟩ : FlagDegree) =
      hybridCost ⟨z, v, r⟩ + hybridCost ⟨z + 2, v, r⟩ := by
  unfold hybridCost hybridCoordinate movingCut
  rw [sharp_raw_hybrid r v z hr hv,
    sharp_raw_hybrid r v (z + 1) hr hv,
    sharp_raw_hybrid r v (z + 2) hr hv,
    rational_raw_hybrid r v z hr hv,
    rational_raw_hybrid r v (z + 1) hr hv,
    rational_raw_hybrid r v (z + 2) hr hv,
    moving_raw_hybrid r v z hr hv,
    moving_raw_hybrid r v (z + 1) hr hv,
    moving_raw_hybrid r v (z + 2) hr hv]
  unfold flagMixed
  simp only [add_zOnly, add_yz, add_all]
  ring

theorem rawCost_affine_of_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  rw [rawCost, rawCost, rawCost]
  simp only [ordinaryCostOf, if_pos (hybridApplies_raw r v z hr hv),
    if_pos (hybridApplies_raw r v (z + 1) hr hv),
    if_pos (hybridApplies_raw r v (z + 2) hr hv)]
  exact hybridCost_raw_affine r v z hr hv

theorem paddedTail_raw_of_r_two_v_pos (r v z d : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    paddedTail (⟨z, v, r⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * v * d, 2 * (r - 1) * d⟩ := by
  unfold paddedTail
  have hs : padS (⟨z, v, r⟩ : FlagDegree) = r := by
    simp only [padS]
    omega
  have hy : padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
    simp only [padY, middle, hs]
    omega
  have ht : padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
    simp only [padT, total, hy]
    omega
  rw [hs, hy, ht]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_pos (r v z : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_pos r v z 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v z 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131073 hr hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_one (r z : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 1 (z + 1) = rawCost r 1 z + rawCost r 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 1, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 1 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos r 1 z hr (by decide)

theorem paddedTail_raw_of_r_one_v_two (v z d : ℕ) (hv : 2 ≤ v) :
    paddedTail (⟨z, v, 1⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * (v - 1) * d, 2 * d⟩ := by
  have hs : padS (⟨z, v, 1⟩ : FlagDegree) = 2 := by rfl
  have hy : padY (⟨z, v, 1⟩ : FlagDegree) = v + 1 := by
    unfold padY
    rw [hs]
    change max (v + 1) 3 = v + 1
    omega
  have ht : padT (⟨z, v, 1⟩ : FlagDegree) = v + 1 + z := by
    unfold padT
    rw [hy]
    change max (z + v + 1) (v + 1) = v + 1 + z
    omega
  change (⟨2 * (padT (⟨z, v, 1⟩ : FlagDegree) -
      padY ⟨z, v, 1⟩) * d,
    1 + 2 * (padY (⟨z, v, 1⟩ : FlagDegree) -
      padS ⟨z, v, 1⟩) * d,
    2 * (padS (⟨z, v, 1⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hz : v + 1 + z - (v + 1) = z := by omega
  have hvsub : v + 1 - 2 = v - 1 := by omega
  rw [hz, hvsub]

theorem paddedCost_raw_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, 1⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, 1⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, 1⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_one_v_two v z 131072 hv,
    paddedTail_raw_of_r_one_v_two v z 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131073 hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 1 v (z + 1) = rawCost 1 v z + rawCost 1 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, v, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 2 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_one_v_two v z hv

theorem paddedTail_raw_of_r_two_v_zero (r z d : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    paddedTail (⟨z, 0, r⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  have hs : padS (⟨z, 0, r⟩ : FlagDegree) = r := by
    unfold padS
    change max r 2 = r
    omega
  have hy : padY (⟨z, 0, r⟩ : FlagDegree) = r + 1 := by
    unfold padY middle
    rw [hs]
    change max (0 + r) (r + 1) = r + 1
    omega
  have ht : padT (⟨z, 0, r⟩ : FlagDegree) = r + z := by
    unfold padT total
    rw [hy]
    change max (z + 0 + r) (r + 1) = r + z
    omega
  change (⟨2 * (padT (⟨z, 0, r⟩ : FlagDegree) -
      padY ⟨z, 0, r⟩) * d,
    1 + 2 * (padY (⟨z, 0, r⟩ : FlagDegree) -
      padS ⟨z, 0, r⟩) * d,
    2 * (padS (⟨z, 0, r⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hzsub : r + z - (r + 1) = z - 1 := by omega
  rw [hzsub]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * paddedCost 131072 131073 (⟨z + 1, 0, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, 0, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, 0, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_zero r z 131072 hr hz,
    paddedTail_raw_of_r_two_v_zero r z 131073 hr hz,
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131073 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131073 hr (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * rawCost r 0 (z + 1) = rawCost r 0 z + rawCost r 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_zero r z hr hz

theorem paddedTail_raw_r_two_v_zero_boundary (r d : ℕ) (hr : 2 ≤ r) :
    paddedTail (⟨0, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ ∧
      paddedTail (⟨1, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  constructor
  · unfold paddedTail padT padY padS middle total
    simp only [Nat.zero_add]
    have hm : max r 2 = r := by omega
    rw [hm]
    have hm' : max r (r + 1) = r + 1 := by omega
    rw [hm']
    norm_num
  · simpa using paddedTail_raw_of_r_two_v_zero r 1 d hr (by decide)

theorem rawCost_convex_r_two_v_zero_boundary (r : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 0 1 ≤ rawCost r 0 0 + rawCost r 0 2 := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn 2)]
  unfold paddedCost
  rw [(paddedTail_raw_r_two_v_zero_boundary r 131072 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131072 hr).2,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).2,
    paddedTail_raw_of_r_two_v_zero r 2 131072 hr (by decide),
    paddedTail_raw_of_r_two_v_zero r 2 131073 hr (by decide)]
  unfold flagMixed
  ring_nf
  omega

theorem paddedTail_raw_r_one_v_one (z d : ℕ) (hz : 1 ≤ z) :
    paddedTail (⟨z, 1, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 2) 3 = z + 2 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_one (z : ℕ) :
    2 * rawCost 1 1 (z + 1) ≤ rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 2 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · have hzpos : 1 ≤ z := by omega
    have hEq : 2 * paddedCost 131072 131073
          (⟨z + 1, 1, 1⟩ : FlagDegree) =
        paddedCost 131072 131073 ⟨z, 1, 1⟩ +
          paddedCost 131072 131073 ⟨z + 2, 1, 1⟩ := by
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_one z 131072 hzpos,
        paddedTail_raw_r_one_v_one z 131073 hzpos,
        paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 1 = z := by omega
      have h2 : z + 2 - 1 = z + 1 := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 1) + 1 := by omega
      rw [hzsplit]
      simp only [Nat.add_sub_cancel]
      unfold flagMixed
      ring
    exact hEq.le

theorem paddedTail_raw_r_one_v_zero (z d : ℕ) (hz : 2 ≤ z) :
    paddedTail (⟨z, 0, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 2) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 1) 3 = z + 1 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_zero (z : ℕ) :
    2 * rawCost 1 0 (z + 1) ≤ rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 2 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz0 : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · by_cases hz1 : z = 1
    · subst z
      norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
    · have hz : 2 ≤ z := by omega
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_zero z 131072 hz,
        paddedTail_raw_r_one_v_zero z 131073 hz,
        paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 2 = z - 1 := by omega
      have h2 : z + 2 - 2 = z := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 2) + 2 := by omega
      rw [hzsplit]
      norm_num
      unfold flagMixed
      ring_nf
      exact le_rfl

theorem rawCost_discreteConvex (r v z : ℕ) (hr : 1 ≤ r) :
    2 * rawCost r v (z + 1) ≤ rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_convex_r_one_v_zero z
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_convex_r_one_v_one z
      · exact (rawCost_affine_of_r_one_v_two v z (by omega)).le
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      by_cases hz : z = 0
      · subst z
        exact rawCost_convex_r_two_v_zero_boundary r hr2
      · exact (rawCost_affine_of_r_two_v_zero r z hr2 (by omega)).le
    · by_cases hv1 : v = 1
      · subst v
        exact (rawCost_affine_of_r_two_v_one r z hr2).le
      · exact (rawCost_affine_of_hybrid r v z hr2 (by omega)).le

theorem rawBelow_of_z_le (r v z₁ z₂ : ℕ) (hz : z₁ ≤ z₂) :
    Below (⟨z₁, v, r⟩ : FlagDegree) ⟨z₂, v, r⟩ := by
  change r ≤ r ∧ v + r ≤ v + r ∧ z₁ + v + r ≤ z₂ + v + r
  omega

theorem rawCost_mono_z (r v : ℕ) : Monotone (rawCost r v) := by
  intro z₁ z₂ hz
  have hb := rawBelow_of_z_le r v z₁ z₂ hz
  by_cases ha : HybridApplies (⟨z₁, v, r⟩ : FlagDegree)
  · have ha' : HybridApplies (⟨z₂, v, r⟩ : FlagDegree) := by
      rcases ha with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_pos ha, if_pos ha']
    exact hybridCost_mono hb
  · have ha' : ¬ HybridApplies (⟨z₂, v, r⟩ : FlagDegree) := by
      intro h
      apply ha
      rcases h with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_neg ha, if_neg ha']
    exact paddedCost_mono 131072 131073 hb

def forwardDiff (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

theorem forwardDiff_mono_of_discreteConvex
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hconvex : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2)) (n : ℕ) :
    forwardDiff f n ≤ forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  have hc := hconvex n
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem move_one_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (a b : ℕ) (hcross : forwardDiff f a ≤ forwardDiff g b) :
    f (a + 1) + g b ≤ f a + g (b + 1) := by
  have hfa := hf (Nat.le_add_right a 1)
  have hgb := hg (Nat.le_add_right b 1)
  unfold forwardDiff at hcross
  omega

theorem transfer_all_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hdf : ∀ n, forwardDiff f n ≤ forwardDiff f (n + 1))
    (hdg : ∀ n, forwardDiff g n ≤ forwardDiff g (n + 1)) :
    ∀ a b, forwardDiff f a ≤ forwardDiff g b →
      f (a + 1) + g b ≤ f 0 + g (a + 1 + b) := by
  intro a
  induction a with
  | zero =>
      intro b hcross
      simpa only [Nat.zero_add, Nat.add_comm] using
        move_one_right f g hf hg 0 b hcross
  | succ a ih =>
      intro b hcross
      have hcross' : forwardDiff f a ≤ forwardDiff g (b + 1) :=
        (hdf a).trans (hcross.trans (hdg b))
      calc
        f (a + 1 + 1) + g b ≤ f (a + 1) + g (b + 1) :=
          move_one_right f g hf hg (a + 1) b hcross
        _ ≤ f 0 + g (a + 1 + (b + 1)) := ih (b + 1) hcross'
        _ = f 0 + g (a + 1 + 1 + b) := by
          rw [show a + 1 + (b + 1) = a + 1 + 1 + b by omega]

theorem two_discreteConvex_endpoint
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hcf : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2))
    (hcg : ∀ n, 2 * g (n + 1) ≤ g n + g (n + 2))
    (a b : ℕ) :
    f a + g b ≤ max (f (a + b) + g 0) (f 0 + g (a + b)) := by
  have hdf (n : ℕ) : forwardDiff f n ≤ forwardDiff f (n + 1) :=
    forwardDiff_mono_of_discreteConvex f hf hcf n
  have hdg (n : ℕ) : forwardDiff g n ≤ forwardDiff g (n + 1) :=
    forwardDiff_mono_of_discreteConvex g hg hcg n
  rcases a with _ | a
  · simpa only [Nat.zero_add] using
      (le_max_right (f b + g 0) (f 0 + g b))
  rcases b with _ | b
  · simpa only [Nat.add_zero] using
      (le_max_left (f (a + 1) + g 0) (f 0 + g (a + 1)))
  by_cases hcross : forwardDiff f a ≤ forwardDiff g (b + 1)
  · have h := transfer_all_right f g hf hg hdf hdg a (b + 1) hcross
    have h' : f (a + 1) + g (b + 1) ≤
        f 0 + g (a + 1 + (b + 1)) := h
    apply h'.trans
    apply le_max_of_le_right
    rfl
  · have hcross' : forwardDiff g b ≤ forwardDiff f (a + 1) :=
      (hdg b).trans ((Nat.lt_of_not_ge hcross).le.trans (hdf a))
    have h := transfer_all_right g f hg hf hdg hdf b (a + 1) hcross'
    have h' : f (a + 1) + g (b + 1) ≤
        f (b + 1 + (a + 1)) + g 0 := by
      simpa only [Nat.add_comm] using h
    have h'' : f (a + 1) + g (b + 1) ≤
        f ((a + 1) + (b + 1)) + g 0 := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    apply h''.trans
    apply le_max_of_le_left
    rfl

theorem rawCost_affine_r_one_v_one (z : ℕ) (hz : 1 ≤ z) :
    2 * rawCost 1 1 (z + 1) = rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 2 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_one z 131072 hz,
    paddedTail_raw_r_one_v_one z 131073 hz,
    paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_r_one_v_zero (z : ℕ) (hz : 2 ≤ z) :
    2 * rawCost 1 0 (z + 1) = rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridApplies (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 2 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_zero z 131072 hz,
    paddedTail_raw_r_one_v_zero z 131073 hz,
    paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 2 = z - 1 := by omega
  have h2 : z + 2 - 2 = z := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 2) + 2 := by omega
  rw [hzsplit]
  norm_num
  unfold flagMixed
  ring

theorem rawCost_affine_step_from_two (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 2 ≤ z) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_r_one_v_zero z hz
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_r_one_v_one z (by omega)
      · exact rawCost_affine_of_r_one_v_two v z (by omega)
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_of_r_two_v_zero r z hr2 (by omega)
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_of_r_two_v_one r z hr2
      · exact rawCost_affine_of_hybrid r v z hr2 (by omega)

theorem forwardDiff_eq_next_of_affine
    (f : ℕ → ℕ) (hmono : Monotone f)
    (n : ℕ) (hstep : 2 * f (n + 1) = f n + f (n + 2)) :
    forwardDiff f n = forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem affine_formula_from_three
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hstep : ∀ n, 2 ≤ n → 2 * f (n + 1) = f n + f (n + 2))
    (z : ℕ) (hz : 3 ≤ z) :
    f z = f 3 + (f 4 - f 3) * (z - 3) := by
  have hdiffStep (n : ℕ) (hn : 2 ≤ n) :
      forwardDiff f n = forwardDiff f (n + 1) :=
    forwardDiff_eq_next_of_affine f hmono n (hstep n hn)
  have hdiff : ∀ n, 3 ≤ n → forwardDiff f n = forwardDiff f 3 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hdiffStep n (by omega)).symm.trans ih
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hmn := hmono (Nat.le_add_right n 1)
      have hd := hdiff n hn
      have hd' : f (n + 1) - f n = f 4 - f 3 := by
        simpa only [forwardDiff, show 3 + 1 = 4 by decide] using hd
      calc
        f (n + 1) = f n + (f (n + 1) - f n) :=
          (Nat.add_sub_of_le hmn).symm
        _ = f n + (f 4 - f 3) := by rw [hd']
        _ = (f 3 + (f 4 - f 3) * (n - 3)) + (f 4 - f 3) := by
          rw [ih]
        _ = f 3 + (f 4 - f 3) * (n + 1 - 3) := by
          have hnsub : n + 1 - 3 = (n - 3) + 1 := by omega
          rw [hnsub]
          ring

theorem rawCost_affine_from_three (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    rawCost r v z = rawCost r v 3 +
      (rawCost r v 4 - rawCost r v 3) * (z - 3) := by
  exact affine_formula_from_three (rawCost r v) (rawCost_mono_z r v)
    (fun n hn => rawCost_affine_step_from_two r v n hr hn) z hz

end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex
end PackedLocator_LocatorOrdinaryZConvex

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration. -/
section PackedLocator_LocatorOrdinaryConcentration

/-!
# Concentrating ordinary-factor excess total degree

Discrete convexity lets all raw `z` weight in a finite nonempty family be
moved to one carrier without decreasing the upper bound.  This reduces the
three-coordinate ordinary partition problem to a two-coordinate zero-`z`
knapsack plus one carrier line.
-/

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration

open scoped BigOperators
open LocatorOrdinaryZConvex

set_option autoImplicit false

theorem exists_z_carrier
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (r v z : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i) (hne : s.Nonempty) :
    ∃ c ∈ s,
      (∑ i ∈ s, rawCost (r i) (v i) (z i)) ≤
        rawCost (r c) (v c) (∑ i ∈ s, z i) +
          ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        refine ⟨a, by simp, ?_⟩
        simp
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨c, hc, hbound⟩ := ih (fun i hi => hr i (by simp [hi])) hsne
        have hra : 1 ≤ r a := hr a (by simp)
        have hrc : 1 ≤ r c := hr c (by simp [hc])
        have hpair := two_discreteConvex_endpoint
          (rawCost (r a) (v a)) (rawCost (r c) (v c))
          (rawCost_mono_z (r a) (v a)) (rawCost_mono_z (r c) (v c))
          (fun n => rawCost_discreteConvex (r a) (v a) n hra)
          (fun n => rawCost_discreteConvex (r c) (v c) n hrc)
          (z a) (∑ i ∈ s, z i)
        have hpre :
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
              rawCost (r a) (v a) (z a) +
                (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := by
          rw [Finset.sum_insert ha]
          exact Nat.add_le_add_left hbound _
        by_cases hend :
            rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                rawCost (r c) (v c) 0 ≤
              rawCost (r a) (v a) 0 +
                rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)
        · refine ⟨c, by simp [hc], ?_⟩
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) := by
            exact hpair.trans (by simpa [max_eq_right hend])
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r c) (v c) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase c,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
              have hac : a ≠ c := fun h => ha (h ▸ hc)
              rw [Finset.erase_insert_of_ne hac, Finset.sum_insert]
              · ac_rfl
              · exact fun h => ha (Finset.mem_of_mem_erase h)
        · refine ⟨a, by simp, ?_⟩
          have hreverse :
              rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) +
                  rawCost (r a) (v a) 0 ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            omega
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            exact hpair.trans (by
              rw [max_eq_left]
              simpa [Nat.add_comm] using hreverse)
          have hzeros :
              rawCost (r c) (v c) 0 +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 =
                ∑ i ∈ s, rawCost (r i) (v i) 0 := by
            simpa only [Nat.add_comm] using
              (Finset.sum_erase_add s
                (fun i => rawCost (r i) (v i) 0) hc)
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r a) (v a) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase a,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha, Finset.erase_insert ha]
              rw [← hzeros]
              ac_rfl

end ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration
end PackedLocator_LocatorOrdinaryConcentration

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Audit. -/
section PackedLocator_LocatorPhase6800Audit

/-!
# Soundness utilities for the compact 6800 phase receipt

These lemmas are deliberately separate from the generated receipt data.  The
first records the correlated (rather than independent-maxima) initial-A
ledger.  The remaining lemmas justify interpreting a checked threshold row as
an exact routeability cutoff in the raw total coordinate.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Audit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The initial-A ledger has to retain the common aggregate `p`: the maximum
phase cost and maximum complementary A charge cannot be taken independently. -/
theorem initialA_sum_le_certifiedJoint_correlated
    (oracle : CheckedPhaseOracle)
    (phaseSum helperSum : ℕ) (p : FlagDegree)
    (hslope : p.all ≤ 28) (hmiddle : middle p ≤ 127)
    (htotal : total p ≤ 5964)
    (hphase : phaseSum ≤ oracle.narrowCap p)
    (hhelper : helperSum ≤ initialAComplement p) :
    phaseSum + helperSum ≤ certifiedJointMaximum := by
  exact (Nat.add_le_add hphase hhelper).trans
    (oracle.joint_le p hslope hmiddle htotal)

/-- Taking one more high-band projection only adds a nonnegative summand. -/
theorem powerBandBudget_le_succ
    (delta dT dY dS T YS S k : ℕ) :
    powerBandBudget delta dT dY dS T YS S k ≤
      powerBandBudget delta dT dY dS T YS S (k + 1) := by
  induction k generalizing T YS S with
  | zero =>
      simp only [powerBandBudget, Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      exact Nat.add_le_add_left
        (ih (T := T - dT) (YS := YS - dY) (S := S - dS)) _

/-- The cumulative high-band cost is monotone in the number of projections. -/
theorem powerBandBudget_mono_fuel
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudget delta dT dY dS T YS S k₁ ≤
      powerBandBudget delta dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudget delta dT dY dS T YS S k₁ ≤
            powerBandBudget delta dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudget delta dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudget_le_succ delta dT dY dS T YS S (k₁ + d)
        _ = powerBandBudget delta dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

/-- For fixed raw slope and middle coordinates, increasing `z` can only make
the source route easier: the residual total box and the fuel both decrease. -/
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have hr' : 1 ≤ r := by simpa only [rawFlag_all] using hr
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      powerBandBudget 50322 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50322 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50322
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50322 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50322 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50322 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · unfold SourceNumbers.band at hband ⊢
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
    exact (hsameFuel.trans hmoreFuel).trans_lt hband

/-- A valid threshold boundary is the exact routeability cutoff throughout
the benchmark raw-total interval. -/
theorem routeable_raw_iff_threshold
    (s : SourceNumbers) {r v threshold z : ℕ}
    (hsourceCap : 5964 ≤ s.totalCap)
    (hrv : r + v ≤ 5964) (hz : z ≤ 5964 - (r + v))
    (hboundary : thresholdBoundary s r v threshold) :
    s.Routeable (rawFlag r v z) ↔ threshold ≤ z := by
  unfold thresholdBoundary at hboundary
  by_cases hzero : threshold = 0
  · rw [if_pos hzero] at hboundary
    constructor
    · intro _
      omega
    · intro _
      apply routeable_raw_mono_z s (z₁ := 0) (z₂ := z)
      · omega
      · omega
      · exact hboundary
  · rw [if_neg hzero] at hboundary
    by_cases hin : threshold ≤ 5964 - (r + v)
    · rw [if_pos hin] at hboundary
      constructor
      · intro hroute
        by_contra hnot
        have hzprev : z ≤ threshold - 1 := by omega
        have hroutePrev := routeable_raw_mono_z s hzprev (by omega) hroute
        exact hboundary.1 hroutePrev
      · intro hthreshold
        exact routeable_raw_mono_z s hthreshold (by omega) hboundary.2
    · rw [if_neg hin] at hboundary
      constructor
      · intro hroute
        have hrouteMax := routeable_raw_mono_z s hz (by omega) hroute
        exact False.elim (hboundary.2 hrouteMax)
      · intro hthreshold
        omega

/-! ## Noncircular semantics of a prefix receipt -/

theorem sumFlag_rawBelow_of_subset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊆ A) :
    RawBelow (sumFlag U flag) (sumFlag A flag) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Finset.sum_le_sum_of_subset_of_nonneg hUA
      (fun _ _ _ ↦ Nat.zero_le _)

/-- A proper subfamily has strictly smaller raw slope when every factor has
positive slope.  This is the well-founded coordinate behind `afterR = r-1`. -/
theorem sumFlag_all_lt_of_ssubset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊂ A)
    (hpositive : ∀ i ∈ A, 1 ≤ (flag i).all) :
    (sumFlag U flag).all < (sumFlag A flag).all := by
  have hdiff : (A \ U).Nonempty := by
    exact Finset.sdiff_nonempty.mpr (fun hAU ↦ hUA.ne (Finset.Subset.antisymm hUA.subset hAU))
  obtain ⟨i, hi⟩ := hdiff
  have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
  have hiOne : 1 ≤ (flag i).all := hpositive i hiA
  have hiSum : (flag i).all ≤ ∑ j ∈ A \ U, (flag j).all := by
    exact Finset.single_le_sum
      (f := fun j ↦ (flag j).all) (fun _ _ ↦ Nat.zero_le _) hi
  have hsplit := Finset.sum_sdiff hUA.subset (f := fun j ↦ (flag j).all)
  simp only [sumFlag_all] at *
  omega

/-- Additivity of every numerical phase potential on a finite family. -/
theorem sum_potential_eval
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (flag : ι → FlagDegree) (q : Potential) :
    (∑ i ∈ s, q.eval (flag i)) = q.eval (sumFlag s flag) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Semantic content of one cumulative prefix table.  `terminal` checks only
actual nonrouteable states.  `monotone` records the cumulative max closure in
raw `r`, `v`, and `z`; neither field assumes the desired phase bound. -/
structure PrefixTableSound
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) (pref : FlagDegree → ℕ) : Prop where
  terminal : ∀ p, ¬ routeable p →
    previous p ≤ q.eval p + pref p
  monotone : ∀ {p₁ p₂}, RawBelow p₁ p₂ → pref p₁ ≤ pref p₂

/-- A parent of raw slope `r` queries the prefix after completing slope
`r-1`.  The subtraction is harmless at zero; routed nonempty products have
positive slope. -/
def parentDefect (pref : FlagDegree → ℕ) (parent : FlagDegree) : ℕ :=
  pref (rawFlag (parent.all - 1) parent.yz parent.zOnly)

/-- The value after adjoining one source phase. -/
def applyPhase (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ)
    (p : FlagDegree) : ℕ :=
  if routeable p then
    min (previous p) (q.eval p + parentDefect pref p)
  else previous p

/-- A cumulative prefix row bounds every nonrouteable strict child of its
parent.  This is the exact semantic fact needed by the algebraic batch split. -/
theorem terminal_le_parent_charge
    {previous pref : FlagDegree → ℕ} {q : Potential}
    {routeable : FlagDegree → Prop}
    (hrows : PrefixTableSound previous q routeable pref)
    {child parent : FlagDegree} (hbelow : RawBelow child parent)
    (hslope : child.all < parent.all) (hterminal : ¬ routeable child) :
    previous child ≤ q.eval child + parentDefect pref parent := by
  have hpred : RawBelow child
      (rawFlag (parent.all - 1) parent.yz parent.zOnly) := by
    rcases hbelow with ⟨hr, hv, hz⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [rawFlag_all]
      using (show child.all ≤ parent.all - 1 by omega)
    · simpa only [rawFlag] using hv
    · simpa only [rawFlag] using hz
  simpa only [parentDefect] using (hrows.terminal child hterminal).trans
    (Nat.add_le_add_left (hrows.monotone hpred) _)

/-- Soundness of one checked numerical phase.  The proof deliberately keeps
the previous bound state-local.  When the current aggregate routes, repeated
strict algebraic splits terminate at a nonrouteable subfamily covered by the
prefix table; exited factors are charged by the additive source potential. -/
theorem sum_count_le_applyPhase
    {ι : Type} [DecidableEq ι]
    (flag : ι → FlagDegree) (count : ι → ℕ)
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ)
    (ambient : Finset ι)
    (hpositive : ∀ i ∈ ambient, 1 ≤ (flag i).all)
    (hprevious : ∀ B, B ⊆ ambient →
      (∑ i ∈ B, count i) ≤ previous (sumFlag B flag))
    (hrows : PrefixTableSound previous q routeable pref)
    (hroute : ∀ B, B ⊆ ambient → routeable (sumFlag B flag) →
      ∃ U, U ⊂ B ∧
        (∑ i ∈ B \ U, count i) ≤
          ∑ i ∈ B \ U, q.eval (flag i)) :
    (∑ i ∈ ambient, count i) ≤
      applyPhase previous q routeable pref (sumFlag ambient flag) := by
  classical
  by_cases hr : routeable (sumFlag ambient flag)
  · rw [applyPhase, if_pos hr]
    apply le_min
    · exact hprevious ambient (fun _ hi ↦ hi)
    · have hcharged :=
        LocatorBatchProductRoute.sum_count_le_charge_add_defect_of_strict_routes
          count (fun i ↦ q.eval (flag i))
          (fun B ↦ routeable (sumFlag B flag)) ambient
          (parentDefect pref (sumFlag ambient flag))
          (fun B hB hn ↦ by
            have hprev := hprevious B hB
            by_cases hEq : B = ambient
            · subst B
              exact False.elim (hn hr)
            · have hproper : B ⊂ ambient :=
                (_root_.ssubset_iff_subset_ne).mpr ⟨hB, hEq⟩
              have hraw := sumFlag_rawBelow_of_subset flag hB
              have hslope := sumFlag_all_lt_of_ssubset flag hproper hpositive
              rw [sum_potential_eval B flag q]
              exact hprev.trans
                (terminal_le_parent_charge hrows hraw hslope hn))
          hroute
      rw [sum_potential_eval ambient flag q] at hcharged
      exact hcharged
  · rw [applyPhase, if_neg hr]
    exact hprevious ambient (fun _ hi ↦ hi)

/-- A threshold function is semantically checked by boundary receipts at
every raw `(r,v)` row. -/
def ThresholdTableSound (s : SourceNumbers)
    (threshold : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v, 1 ≤ r → r + v ≤ 127 →
    thresholdBoundary s r v (threshold r v)

theorem routeable_iff_of_thresholdTableSound
    (s : SourceNumbers) (threshold : ℕ → ℕ → ℕ)
    (hsourceCap : 5964 ≤ s.totalCap)
    (htable : ThresholdTableSound s threshold)
    (p : FlagDegree) (hr : 1 ≤ p.all)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    s.Routeable p ↔ threshold p.all p.yz ≤ p.zOnly := by
  have hry : p.all + p.yz ≤ 127 := by
    simpa only [middle, Nat.add_comm] using hy
  have hrz : p.zOnly ≤ 5964 - (p.all + p.yz) := by
    simp only [total] at ht
    omega
  have hryWide : p.all + p.yz ≤ 5964 := hry.trans (by decide)
  have h := routeable_raw_iff_threshold s hsourceCap
    (r := p.all) (v := p.yz) (z := p.zOnly)
    (hrv := hryWide) (hz := hrz)
    (hboundary := htable p.all p.yz hr hry)
  simpa only [rawFlag] using h

/-! ## State-local base semantics -/

/-- The zero-`z` two-coordinate table.  The zero-slope state represents the
empty family; positive-slope states are the `z = 0` entries of the base rows. -/
def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)

theorem baseZeroCap_eq_of_pos (rows : Array BaseRow) {r v : ℕ}
    (hr : 1 ≤ r) :
    baseZeroCap rows r v = baseTableCap rows (rawFlag r v 0) := by
  simp only [baseZeroCap, if_neg (Nat.ne_of_gt hr)]

/-- The sole semantic arithmetic condition required of the compact base
table.  It is finite on the benchmark box.  For every possible carrier
`(r,v)`, the row for the aggregate `(R,V)` dominates that carrier with all
remaining factors charged to the zero-`z` table. -/
def BaseCandidatesSound (rows : Array BaseRow) : Prop :=
  ∀ R V r v z,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 28 → R + V ≤ 127 →
    (r < R ∨ v = V) → R + V + z ≤ 5964 →
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z)

/-- Slope of the carrier's affine ordinary-cost tail, valid from `z = 3`. -/
def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

/-- Carrier line after adding the exact zero-`z` residual-table value. -/
def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

theorem carrierCost_eq_candidateLine
    (rows : Array BaseRow) (R V r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) =
      candidateLine rows R V r v z := by
  rw [LocatorOrdinaryZConvex.rawCost_affine_from_three r v z hr hz]
  unfold candidateLine candidateSlope
  omega

theorem candidateLine_shift
    (rows : Array BaseRow) (R V r v start z : ℕ)
    (hstart : 3 ≤ start) (hz : start ≤ z) :
    candidateLine rows R V r v z =
      candidateLine rows R V r v start + candidateSlope r v * (z - start) := by
  unfold candidateLine
  have hsplit : z - 3 = (start - 3) + (z - start) := by omega
  rw [hsplit, Nat.mul_add]
  omega

/-- Two affine natural-number functions ordered at the left endpoint remain
ordered when the lower function has no larger slope. -/
theorem affine_le_of_start_and_slope
    (a A m M d : ℕ) (ha : a ≤ A) (hm : m ≤ M) :
    a + m * d ≤ A + M * d := by
  exact Nat.add_le_add ha (Nat.mul_le_mul_right d hm)

/-- Endpoint domination suffices on a finite interval even when the candidate
line has the larger slope. -/
theorem affine_le_between
    (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A)
    (hend : a + m * finish ≤ A + M * finish) :
    a + m * d ≤ A + M * d := by
  by_cases hm : m ≤ M
  · exact affine_le_of_start_and_slope a A m M d hstart hm
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M + (m - M) = m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a + (m - M) * finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta : (m - M) * d ≤ (m - M) * finish :=
      Nat.mul_le_mul_left (m - M) hd
    rw [← hdecomp, Nat.add_mul]
    omega

theorem candidateLine_le_segment_of_start_and_slope
    (rows : Array BaseRow) (R V r v z : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hslope : candidateSlope r v ≤ s.slope) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  unfold BaseSegment.evalAt
  exact affine_le_of_start_and_slope _ _ _ _ _ hstart hslope

theorem candidateLine_le_segment_between
    (rows : Array BaseRow) (R V r v z finish : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z) (hzf : z ≤ finish)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hfinish : candidateLine rows R V r v finish ≤ s.evalAt finish) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  have hsf : s.start ≤ finish := hsz.trans hzf
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  rw [candidateLine_shift rows R V r v s.start finish hs3 hsf] at hfinish
  unfold BaseSegment.evalAt at hfinish ⊢
  apply affine_le_between _ _ _ _ _ _
  · exact Nat.sub_le_sub_right hzf s.start
  · exact hstart
  · exact hfinish

/-- Finite arithmetic checked for one aggregate row and one candidate
carrier.  Every generated row has one or two useful affine segments. -/
def CandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) : Prop :=
  let q := lookupBaseRow rows R V
  let zero := baseZeroCap rows (R - r) (V - v)
  LocatorOrdinaryZConvex.rawCost r v 0 + zero ≤ q.z0 ∧
  LocatorOrdinaryZConvex.rawCost r v 1 + zero ≤ q.z1 ∧
  LocatorOrdinaryZConvex.rawCost r v 2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
        candidateSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
        candidateLine rows R V r v (s₂.start - 1) ≤
          s₁.evalAt (s₂.start - 1) ∧
        candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
        candidateSlope r v ≤ s₂.slope
  | _ => False

instance (rows : Array BaseRow) (R V r v : ℕ) :
    Decidable (CandidateRowCheck rows R V r v) := by
  unfold CandidateRowCheck
  dsimp only
  generalize hq : lookupBaseRow rows R V = q
  cases hs : q.segments with
  | nil =>
      simp only [hs]
      infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil =>
          simp only [hs, ht]
          infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil =>
              simp only [hs, ht, hu]
              infer_instance
          | cons s₃ rest₃ =>
              simp only [hs, ht, hu]
              infer_instance

/-- One finite `R` layer of the carrier-row checker. -/
def CandidateRCheck (rows : Array BaseRow) (R : ℕ) : Prop :=
  ∀ V ∈ List.range (128 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

/-- Complete finite base-table checker.  Its executable domain has only the
2.443-million aggregate/carrier splits, not a `z` grid. -/
def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → CandidateRCheck rows R

instance (rows : Array BaseRow) : Decidable (BaseCandidateChecks rows) := by
  unfold BaseCandidateChecks
  infer_instance

theorem candidateRowCheck_sound
    (rows : Array BaseRow) (R V r v z : ℕ) (hr : 1 ≤ r)
    (hcheck : CandidateRowCheck rows R V r v) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z) := by
  let q := lookupBaseRow rows R V
  change LocatorOrdinaryZConvex.rawCost r v z +
      baseZeroCap rows (R - r) (V - v) ≤ q.evalAt z
  change
    LocatorOrdinaryZConvex.rawCost r v 0 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z0 ∧
      LocatorOrdinaryZConvex.rawCost r v 1 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z1 ∧
      LocatorOrdinaryZConvex.rawCost r v 2 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z2 ∧
      (match q.segments with
      | [s] =>
          s.start = 3 ∧
            candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
            candidateSlope r v ≤ s.slope
      | [s₁, s₂] =>
          s₁.start = 3 ∧ s₁.start < s₂.start ∧
            candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
            candidateLine rows R V r v (s₂.start - 1) ≤
              s₁.evalAt (s₂.start - 1) ∧
            candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
            candidateSlope r v ≤ s₂.slope
      | _ => False) at hcheck
  rcases hcheck with ⟨hzero, hone, htwo, hsegmentsSound⟩
  by_cases hz0 : z = 0
  · subst z
    simpa [BaseRow.evalAt] using hzero
  by_cases hz1 : z = 1
  · subst z
    simpa [BaseRow.evalAt] using hone
  by_cases hz2 : z = 2
  · subst z
    simpa [BaseRow.evalAt] using htwo
  have hz3 : 3 ≤ z := by omega
  rw [carrierCost_eq_candidateLine rows R V r v z hr hz3]
  cases hsegments : q.segments with
  | nil =>
      simp only [hsegments] at hsegmentsSound
  | cons s₁ tail =>
      cases htail : tail with
      | nil =>
          have hsound :
              s₁.start = 3 ∧
                candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                candidateSlope r v ≤ s₁.slope := by
            simpa only [hsegments, htail] using hsegmentsSound
          rcases hsound with ⟨hs₁Start, hlineStart, hslope⟩
          have hline := candidateLine_le_segment_of_start_and_slope
            rows R V r v z s₁ (by omega) (by omega) hlineStart hslope
          have heval : q.evalAt z = s₁.evalAt z := by
            simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail,
              hz0, hz1, hz2]
          rw [heval]
          exact hline
      | cons s₂ rest =>
          cases hrest : rest with
          | nil =>
              have hsound :
                  s₁.start = 3 ∧ s₁.start < s₂.start ∧
                    candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                    candidateLine rows R V r v (s₂.start - 1) ≤
                      s₁.evalAt (s₂.start - 1) ∧
                    candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
                    candidateSlope r v ≤ s₂.slope := by
                simpa only [hsegments, htail, hrest] using hsegmentsSound
              rcases hsound with
                ⟨hs₁Start, hs₁₂, hlineStart, hlineFinish,
                  hlineSecond, hslopeSecond⟩
              by_cases hs₂z : s₂.start ≤ z
              · have hline := candidateLine_le_segment_of_start_and_slope
                  rows R V r v z s₂ (by omega) hs₂z hlineSecond
                    hslopeSecond
                have heval : q.evalAt z = s₂.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
              · have hzf : z ≤ s₂.start - 1 := by omega
                have hline := candidateLine_le_segment_between
                  rows R V r v z (s₂.start - 1) s₁
                    (by omega) (by omega) hzf hlineStart hlineFinish
                have heval : q.evalAt z = s₁.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
          | cons s₃ rest₃ =>
              simp only [hsegments, htail, hrest] at hsegmentsSound

theorem baseCandidatesSound_of_checks
    (rows : Array BaseRow) (hchecks : BaseCandidateChecks rows) :
    BaseCandidatesSound rows := by
  intro R V r v z hr hrR hvV hR hRV hfits htotal
  have hRpos : 1 ≤ R := hr.trans hrR
  have hRcheck := hchecks R (List.mem_range.mpr (by omega)) hRpos
  have hVcheck := hRcheck V (List.mem_range.mpr (by omega))
  have hrcheck := hVcheck r (List.mem_range.mpr (by omega)) hr
  have hcheck := hrcheck v (List.mem_range.mpr (by omega)) hfits
  exact candidateRowCheck_sound rows R V r v z hr hcheck

theorem ordinaryCostOf_eq_rawCost (p : FlagDegree) :
    LocatorHybridCost.ordinaryCostOf p =
      LocatorOrdinaryZConvex.rawCost p.all p.yz p.zOnly := by
  cases p
  rfl

/-- The `z = 0` part of `BaseCandidatesSound` is exactly the Bellman
inequality needed to aggregate an arbitrary finite zero-`z` family. -/
theorem sum_rawCost_zero_le_baseZeroCap
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (r v : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ r i)
    (hrCap : (∑ i ∈ s, r i) ≤ 28)
    (hrvCap : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127) :
    (∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) ≤
      baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseZeroCap]
  | @insert a s ha ih =>
      have hra : 1 ≤ r a := hpositive a (by simp)
      have hRInsert : r a + (∑ i ∈ s, r i) ≤ 28 := by
        simpa only [Finset.sum_insert ha] using hrCap
      have hRVInsert :
          (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ 127 := by
        rw [Finset.sum_insert ha, Finset.sum_insert ha] at hrvCap
        omega
      have hsR : (∑ i ∈ s, r i) ≤ 28 := by
        omega
      have hsRV : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127 := by
        omega
      have ihBound := ih
        (fun i hi ↦ hpositive i (Finset.mem_insert_of_mem hi)) hsR hsRV
      have hfits : r a < r a + (∑ i ∈ s, r i) ∨
          v a = v a + (∑ i ∈ s, v i) := by
        by_cases hs : s.Nonempty
        · obtain ⟨i, hi⟩ := hs
          have hri : 1 ≤ r i :=
            hpositive i (Finset.mem_insert_of_mem hi)
          have hriSum : r i ≤ ∑ j ∈ s, r j :=
            Finset.single_le_sum (f := fun j ↦ r j)
              (fun _ _ ↦ Nat.zero_le _) hi
          left
          omega
        · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          subst s
          simp
      have hcandidate := hrows
        (r a + ∑ i ∈ s, r i) (v a + ∑ i ∈ s, v i)
        (r a) (v a) 0 hra (by omega) (by omega)
        hRInsert hRVInsert hfits
        (by omega)
      have hposSum : 1 ≤ r a + ∑ i ∈ s, r i := by omega
      calc
        (∑ i ∈ insert a s,
            LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) =
            LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
        _ ≤ LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) :=
            Nat.add_le_add_left ihBound _
        _ ≤ baseTableCap rows
              (rawFlag (r a + ∑ i ∈ s, r i)
                (v a + ∑ i ∈ s, v i) 0) := by
            simpa only [Nat.add_sub_cancel_left] using hcandidate
        _ = baseZeroCap rows (∑ i ∈ insert a s, r i)
              (∑ i ∈ insert a s, v i) := by
            simp only [Finset.sum_insert ha, baseZeroCap,
              if_neg (Nat.ne_of_gt hposSum)]

/-- A checked carrier table gives the genuinely state-local base oracle.  The
proof first concentrates all `z` on one factor, bounds the remaining zero-`z`
family by the same Bellman table, and finally applies that carrier's row. -/
theorem stateLocalBaseOracleSound_of_candidates
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows) :
    StateLocalBaseOracleSound (baseTableCap rows) := by
  intro ι inst s p hpositive hrCap hyCap htCap
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨c, hc, hconcentrate⟩ :=
      LocatorOrdinaryConcentration.exists_z_carrier s
        (fun i ↦ (p i).all) (fun i ↦ (p i).yz) (fun i ↦ (p i).zOnly)
        hpositive hs
    have hzero := sum_rawCost_zero_le_baseZeroCap rows hrows (s.erase c)
      (fun i ↦ (p i).all) (fun i ↦ (p i).yz)
      (fun i hi ↦ hpositive i (Finset.mem_of_mem_erase hi))
      (by
        have hsub : s.erase c ⊆ s := Finset.erase_subset c s
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
        exact hle.trans hrCap)
      (by
        have hsub : s.erase c ⊆ s := Finset.erase_subset c s
        have hrle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
        have hvle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).yz)
        have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
          rw [sumFlag_middle] at hyCap
          simp only [middle, Finset.sum_add_distrib] at hyCap
          omega
        omega)
    have hcR : (p c).all ≤ ∑ i ∈ s, (p i).all := by
      exact Finset.single_le_sum (f := fun i ↦ (p i).all)
        (fun _ _ ↦ Nat.zero_le _) hc
    have hcV : (p c).yz ≤ ∑ i ∈ s, (p i).yz := by
      exact Finset.single_le_sum (f := fun i ↦ (p i).yz)
        (fun _ _ ↦ Nat.zero_le _) hc
    have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
      rw [sumFlag_middle] at hyCap
      simp only [middle, Finset.sum_add_distrib] at hyCap
      omega
    have htotal : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) +
        (∑ i ∈ s, (p i).zOnly) ≤ 5964 := by
      rw [sumFlag_total] at htCap
      simp only [total, middle, Finset.sum_add_distrib] at htCap
      omega
    have hrErase := Finset.sum_erase_add s (fun i ↦ (p i).all) hc
    have hvErase := Finset.sum_erase_add s (fun i ↦ (p i).yz) hc
    have hfits :
        (p c).all < ∑ i ∈ s, (p i).all ∨
          (p c).yz = ∑ i ∈ s, (p i).yz := by
      by_cases hrest : (s.erase c).Nonempty
      · obtain ⟨i, hi⟩ := hrest
        have hiS : i ∈ s := Finset.mem_of_mem_erase hi
        have hri : 1 ≤ (p i).all := hpositive i hiS
        have hriSum : (p i).all ≤ ∑ j ∈ s.erase c, (p j).all :=
          Finset.single_le_sum (f := fun j ↦ (p j).all)
            (fun _ _ ↦ Nat.zero_le _) hi
        left
        omega
      · have hrest0 : s.erase c = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hrest
        right
        rw [hrest0] at hvErase
        simp only [Finset.sum_empty] at hvErase
        omega
    have hcandidate := hrows
      (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
      (p c).all (p c).yz (∑ i ∈ s, (p i).zOnly)
      (hpositive c hc) hcR hcV hrCap hmiddle hfits htotal
    have hzero' :
        (∑ i ∈ s.erase c,
            LocatorOrdinaryZConvex.rawCost (p i).all (p i).yz 0) ≤
          baseZeroCap rows
            ((∑ i ∈ s, (p i).all) - (p c).all)
            ((∑ i ∈ s, (p i).yz) - (p c).yz) := by
      simpa only [show (∑ i ∈ s, (p i).all) - (p c).all =
          ∑ i ∈ s.erase c, (p i).all by omega,
        show (∑ i ∈ s, (p i).yz) - (p c).yz =
          ∑ i ∈ s.erase c, (p i).yz by omega] using hzero
    have hcostEq :
        (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) =
          ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost
            (p i).all (p i).yz (p i).zOnly := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ordinaryCostOf_eq_rawCost (p i)
    have hflagEq : sumFlag s p =
        rawFlag (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
          (∑ i ∈ s, (p i).zOnly) := rfl
    rw [hcostEq, hflagEq]
    exact hconcentrate.trans ((Nat.add_le_add_left hzero' _).trans hcandidate)
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end ProximityPrize.SubmissionLower.LocatorPhase6800Audit
end PackedLocator_LocatorPhase6800Audit

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPowerRoute. -/
section PackedLocator_LocatorBatchPowerRoute

/-!
# Counting consumer for shared regular-product power routes

`LocatorBatchProductRoute` selects the first strict post-projection factor
subset.  This file turns that algebraic stage into the helper bounds used by
the numerical phase recursion.  Source-specific gaps and receipt arithmetic
remain parameters here and are instantiated in the phase bridge.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
  LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The exact cell box of a regular factor.  With this box `stageCost` is the
actual unequal-pair charge after the displayed number of source quotients. -/
def exactRouteBox {H : P4} (F : RegularIndex H) : PowerRouteBox where
  tLo := wt residualTotalWeights F.1
  tHi := wt residualTotalWeights F.1
  yLo := wt residualYSWeights F.1
  yHi := wt residualYSWeights F.1
  rLo := wt residualSWeights F.1
  rHi := wt residualSWeights F.1

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- Multiplying the low terminal quotient by the removed batch power returns
an original source row in the derivative-contact box. -/
theorem reconstruct_mem_low_of_batch_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J : P4)
    (heq : P ^ j * J = reconstruct K D 131071 L S v.1)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) J <
      Dlow - j * wt (contactWeights 131071) P) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have hmul := wt_mul_le (contactWeights 131071) (P ^ j) J
  have hp := wt_pow_le (contactWeights 131071) P j
  omega

/-- Convert a selected batch exit into per-factor helper charges.  The
consumer retains the complementary product in every helper, so no internal
collision locus is charged. -/
theorem counts_of_batchExitStage
    (D L S m YS delta fuel : ℕ)
    (hD : 0 < D) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181392 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (A : Finset (RegularIndex H))
    (q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hproduct : ∀ v,
      reconstruct K D 131071 L S v.1 = regularProduct H A * q v)
    (hexit : HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) (regularProduct H A))
      131071 delta
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) H A q)
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgates : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let P := regularProduct H A
  change HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) P) 131071 delta
      (L - wt residualTotalWeights P) (YS - wt residualYSWeights P)
      (S - wt residualSWeights P) H A q at hexit
  obtain ⟨e, U, v, J, hUA, hv, hJ, heq, hbox, havoid⟩ := hexit
  let j := e.val + 1
  have hj : 1 ≤ j := by simp only [j]; omega
  have hjle : j ≤ fuel := by simp only [j]; omega
  have hjchar : j < 2130706433 := hjle.trans_lt hfuelChar
  have heqOriginal : P ^ j * J =
      reconstruct K D 131071 L S v.1 := by
    calc
      P ^ j * J = P * (P ^ e.val * J) := by
        simp only [j, pow_succ']
        ring
      _ = P * q v := by rw [heq]
      _ = reconstruct K D 131071 L S v.1 := (hproduct v).symm
  change J ∈ nestedCoefficientBox K
      (D - delta - wt (contactWeights 131071) P - e.val * delta -
        e.val * wt (contactWeights 131071) P) 131071
      (L - wt residualTotalWeights P - e.val * wt residualTotalWeights P)
      (YS - wt residualYSWeights P - e.val * wt residualYSWeights P)
      (S - wt residualSWeights P - e.val * wt residualSWeights P) at hbox
  have hweights := nested_mem_weights hbox hJ
  have hJT : wt residualTotalWeights J ≤
      L - j * wt residualTotalWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.1
  have hJY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.1
  have hJS : wt residualSWeights J ≤
      S - j * wt residualSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.2.1
  have hJcontact : wt (contactWeights 131071) J <
      D - j * delta - j * wt (contactWeights 131071) P := by
    have hc := hweights.2.2.2
    simp only [j, Nat.sub_sub, Nat.add_mul, one_mul] at hc ⊢
    omega
  have hlow : reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K (D - j * delta) 131071 L S :=
    reconstruct_mem_low_of_batch_power u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT : j * wt residualTotalWeights P ≤ L :=
    (Nat.mul_le_mul_right (wt residualTotalWeights P) hjle).trans hfeasible.1
  have hPY : j * wt residualYSWeights P ≤ YS :=
    (Nat.mul_le_mul_right (wt residualYSWeights P) hjle).trans hfeasible.2.1
  have hPS : j * wt residualSWeights P ≤ S :=
    (Nat.mul_le_mul_right (wt residualSWeights P) hjle).trans hfeasible.2.2
  refine ⟨U, hUA, ?_⟩
  intro F hFU
  have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFU)
  have hQbounds := liftedHelper_residual_bounds H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma QF = 0 := by
    exact batch_helper_zero_on_regularSeeds j D (D - j * delta) 131071
      L S m 181392 2130706433
      (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage := regularSeeds_count_le_stageCost L YS S
    (exactRouteBox F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
    (degreeZ_le_totalWeight F.1) QF
    (by simpa only [exactRouteBox] using hQbounds.1)
    (by simpa only [exactRouteBox] using hQbounds.2.1)
    (by simpa only [exactRouteBox] using hQbounds.2.2)
    hrel (by simpa only [exactRouteBox] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

/-- A complete algebraic step for one fresh source.  Stage zero uses the
existing divisor-or-helper switch.  If the entire batch product divides the
source, it is removed once and the shared product-power selector finds a
later strict exit.  `hcharge` is the sole interface to the additive numerical
potential used by a phase receipt. -/
theorem exists_strict_helper_split_of_batch_source
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181392)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181392 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hband : powerBandBudget delta
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hwidth :
          D - wt (contactWeights 131071) (regularProduct H A) ≤
            (D - delta -
              wt (contactWeights 131071) (regularProduct H A)) + delta := by
        omega
      have hsource : powerBandBudget delta
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hband.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudget_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) hwidth q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))

end

end ProximityPrize.SubmissionLower.LocatorBatchPowerRoute
end PackedLocator_LocatorBatchPowerRoute

/-! Packed from ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic. -/
section PackedLocator_LocatorFastKernelArithmetic

/-!
# Kernel-cheap arithmetic for large locator sources

The contact-rank bound is definitionally a sum of nested `Finset.range` sums.
For the larger replacement sources, evaluating that definition directly would
expand hundreds of millions of summands.  This file closes each rectangular
block symbolically and leaves only one primitive recursion over the contact
rows.  It also provides a primitive-recursive evaluator for coefficient
counts after the weighted cutoff has removed the long zero tail.
-/

namespace ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Number of entries in a rectangular block, weighted by the descending
affine function `L + 1 - offset - i - j`. -/
def rectangularCount (ni nj offset L : ℕ) : ℕ :=
  ni * nj * (L + 1 - offset) -
    (nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2))

private theorem pairIndexSum (ni nj : ℕ) :
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
      nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
  calc
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
        ∑ i ∈ Finset.range ni,
          (nj * i + nj * (nj - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    _ = nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

theorem rectangularSum_eq_rectangularCount (ni nj offset L : ℕ)
    (hbound : offset + (ni - 1) + (nj - 1) ≤ L) :
    (∑ i ∈ Finset.range ni,
      ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) =
      rectangularCount ni nj offset L := by
  have hpoint : ∀ i ∈ Finset.range ni, ∀ j ∈ Finset.range nj,
      (L + 1 - offset - i - j) + (i + j) = L + 1 - offset := by
    intro i hi j hj
    have hil : i ≤ ni - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hjl : j ≤ nj - 1 := by
      have := Finset.mem_range.mp hj
      omega
    omega
  have hadd :
      (∑ i ∈ Finset.range ni,
        ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
          (∑ i ∈ Finset.range ni,
            ∑ j ∈ Finset.range nj, (i + j)) =
        ni * nj * (L + 1 - offset) := by
    calc
      _ = ∑ i ∈ Finset.range ni,
          ((∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
            ∑ j ∈ Finset.range nj, (i + j)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ Finset.range ni,
          ∑ j ∈ Finset.range nj,
            ((L + 1 - offset - i - j) + (i + j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_add_distrib.symm
      _ = ∑ i ∈ Finset.range ni,
          ∑ _j ∈ Finset.range nj, (L + 1 - offset) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i hi j hj
      _ = ni * nj * (L + 1 - offset) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
          ring
  rw [pairIndexSum] at hadd
  unfold rectangularCount
  omega

theorem blockInputCount_eq_rectangularCount (M L s : ℕ)
    (hbound : M + s ≤ L) :
    blockInputCount M L s = rectangularCount (M + 1) (s + 1) 0 L := by
  simpa only [blockInputCount, Nat.zero_add, Nat.sub_zero] using
    rectangularSum_eq_rectangularCount (M + 1) (s + 1) 0 L (by omega)

theorem blockKernelLowerBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    blockKernelLowerBound M L s h =
      rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL : h ≤ L := by omega
      have hshape : M - h + (s - h) ≤ L - h := by omega
      have heq : blockKernelLowerBound M L s h =
          blockInputCount (M - h) (L - h) (s - h) := by
        have hMr : M + 1 - h = M - h + 1 := by omega
        have hsr : s + 1 - h = s - h + 1 := by omega
        have hLr : L + 1 - h = L - h + 1 := by omega
        unfold blockKernelLowerBound blockInputCount
        rw [hMr, hsr, hLr]
      rw [heq, blockInputCount_eq_rectangularCount _ _ _ hshape]
      have hMr : M + 1 - h = M - h + 1 := by omega
      have hsr : s + 1 - h = s - h + 1 := by omega
      have hLr : L + 1 - h = L - h + 1 := by omega
      unfold rectangularCount
      rw [hMr, hsr, hLr]
      simp only [Nat.sub_zero]
    · have hz : s + 1 - h = 0 := by omega
      simp [blockKernelLowerBound, rectangularCount, hz]
  · have hz : M + 1 - h = 0 := by omega
    simp [blockKernelLowerBound, rectangularCount, hz]

theorem contactRankBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    contactRankBound M L s h =
      rectangularCount (M + 1) (s + 1) 0 L -
        rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  unfold contactRankBound
  rw [blockInputCount_eq_rectangularCount M L s hbound,
    blockKernelLowerBound_eq_rectangularCount M L s h hbound]

/-- The same local rank as `RCN119.localRankBound`, but every rectangular
block is closed and the sole remaining sum uses primitive recursion. -/
def fastLocalRankBound (m L s : ℕ) : ℕ :=
  kernelSumRange (fun r =>
    let M := min r L
    let h := min (r + 1) (m - r)
    rectangularCount (M + 1) (s + 1) 0 L -
      rectangularCount (M + 1 - h) (s + 1 - h) h L) m

theorem localRankBound_eq_fastLocalRankBound (m L s : ℕ)
    (hshape : m + s ≤ L + 1) :
    localRankBound m L s = fastLocalRankBound m L s := by
  unfold localRankBound fastLocalRankBound
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  have hb : min r L + s ≤ L := by
    have hm : min r L ≤ r := Nat.min_le_left _ _
    omega
  exact contactRankBound_eq_rectangularCount
    (min r L) L s (min (r + 1) (m - r)) hb

/-- Coefficient count with the weighted zero tail removed and both finite sums
represented by primitive recursion. -/
def fastCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (fun i =>
    kernelSumRange (fun j =>
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) (s + 1)) cutoff

theorem coefficientCount_eq_fastCoefficientCount
    (D w L s cutoff : ℕ) (hcutoff : cutoff ≤ L + 1)
    (hweight : D ≤ w * cutoff) :
    coefficientCount D w L s = fastCoefficientCount D w L s cutoff := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    D w L s cutoff hcutoff hweight]
  unfold fastCoefficientCount
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [kernelSumRange_eq]

/-! The primitive evaluator above is already much cheaper than the original
nested `Finset` computation, but it still performs `cutoff * (s + 1)` steps.
The inner summand is quadratic, so the following evaluator closes each row and
performs only `cutoff` primitive steps. -/

private def triangularCount (n : ℕ) : ℕ := n * (n - 1) / 2

private def squareCount (n : ℕ) : ℕ :=
  n * (n - 1) * (2 * n - 1) / 6

private theorem kernelSumRange_id (n : ℕ) :
    kernelSumRange (fun j => j) n = triangularCount n := by
  rw [kernelSumRange_eq, Finset.sum_range_id]
  rfl

private theorem kernelSumRange_square_mul_six (n : ℕ) :
    kernelSumRange (fun j => j * j) n * 6 =
      n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, Nat.add_mul, ih]
      cases n with
      | zero => decide
      | succ k =>
          have h1 : k + 1 - 1 = k := by omega
          have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          have h3 : k + 1 + 1 - 1 = k + 1 := by omega
          have h4 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
          rw [h1, h2, h3, h4]
          ring

private theorem kernelSumRange_square (n : ℕ) :
    kernelSumRange (fun j => j * j) n = squareCount n := by
  unfold squareCount
  rw [← kernelSumRange_square_mul_six n,
    Nat.mul_div_cancel _ (by decide : 0 < 6)]

private theorem finset_sum_range_square (n : ℕ) :
    (∑ j ∈ Finset.range n, j * j) = squareCount n := by
  rw [← kernelSumRange_eq, kernelSumRange_square]

/-- Closed value of `sum_{j<N} (A-j)*(B-c*j)` when neither subtraction
truncates on that range. -/
private def quadraticDescendingCount (A B c N : ℕ) : ℕ :=
  N * (A * B) + c * squareCount N -
    (A * c + B) * triangularCount N

private theorem descendingProduct_add_cross (A B c j : ℕ)
    (hjA : j ≤ A) (hjB : c * j ≤ B) :
    (A - j) * (B - c * j) + (A * c + B) * j =
      A * B + c * (j * j) := by
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hjA, Nat.cast_sub hjB]
  ring

private theorem descendingProductSum_eq_quadraticDescendingCount
    (A B c N : ℕ) (hA : N - 1 ≤ A) (hB : c * (N - 1) ≤ B) :
    (∑ j ∈ Finset.range N, (A - j) * (B - c * j)) =
      quadraticDescendingCount A B c N := by
  have hsum :
      (∑ j ∈ Finset.range N, (A - j) * (B - c * j)) +
          (∑ j ∈ Finset.range N, (A * c + B) * j) =
        ∑ j ∈ Finset.range N, (A * B + c * (j * j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N - 1 := by
      have := Finset.mem_range.mp hj
      omega
    exact descendingProduct_add_cross A B c j (hjN.trans hA)
      ((Nat.mul_le_mul_left c hjN).trans hB)
  have hlinear :
      (∑ j ∈ Finset.range N, (A * c + B) * j) =
        (A * c + B) * triangularCount N := by
    rw [← Finset.mul_sum, Finset.sum_range_id]
    rfl
  have hright :
      (∑ j ∈ Finset.range N, (A * B + c * (j * j))) =
        N * (A * B) + c * squareCount N := by
    have hconstant :
        (∑ _j ∈ Finset.range N, A * B) = N * (A * B) := by
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    have hsquare :
        (∑ j ∈ Finset.range N, c * (j * j)) = c * squareCount N := by
      rw [← Finset.mul_sum, finset_sum_range_square]
    rw [Finset.sum_add_distrib, hconstant, hsquare]
  rw [hlinear, hright] at hsum
  unfold quadraticDescendingCount
  omega

/-- Closed form for one coefficient-count row.  `J` is the last index before
either descending factor becomes truncated, so all later terms are zero. -/
def closedCoefficientRow (D w L s i : ℕ) : ℕ :=
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s (min (L - i) (B / c))
  quadraticDescendingCount A B c (J + 1)

theorem coefficientRow_eq_closedCoefficientRow
    (D w L s i : ℕ) (hw : 2 ≤ w) :
    (∑ j ∈ Finset.range (s + 1),
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
      closedCoefficientRow D w L s i := by
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s (min (L - i) (B / c))
  have hc : 0 < c := by simp only [c]; omega
  have hJs : J ≤ s := Nat.min_le_left _ _
  have hJL : J ≤ L - i :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have hJdiv : J ≤ B / c :=
    (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  have hJB : c * J ≤ B := by
    have h := (Nat.le_div_iff_mul_le hc).mp hJdiv
    simpa only [Nat.mul_comm] using h
  have hsmall :
      (∑ j ∈ Finset.range (J + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
        quadraticDescendingCount A B c (J + 1) := by
    have hA : J + 1 - 1 ≤ A := by simp only [A]; omega
    have hB : c * (J + 1 - 1) ≤ B := by
      simpa only [Nat.add_sub_cancel] using hJB
    simpa only [A, B, c] using
      descendingProductSum_eq_quadraticDescendingCount A B c (J + 1) hA hB
  have hsubset : Finset.range (J + 1) ⊆ Finset.range (s + 1) :=
    Finset.range_mono (by omega)
  have htrim :
      (∑ j ∈ Finset.range (J + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        (L + 1 - i - j) * (D - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro j hjfull hjnot
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hjfull
      omega
    by_cases hjL : j ≤ L - i
    · by_cases hjB : c * j ≤ B
      · have hjdiv : j ≤ B / c :=
          (Nat.le_div_iff_mul_le hc).mpr (by
            simpa only [Nat.mul_comm] using hjB)
        have hjJ : j ≤ J := by
          simp only [J]
          exact le_min hjs (le_min hjL hjdiv)
        exact (hjnot (Finset.mem_range.mpr (by omega))).elim
      · have hz : D - w * i - (w - 1) * j = 0 := by
          simp only [B, c] at hjB
          omega
        simp only [hz, Nat.mul_zero]
    · have hz : L + 1 - i - j = 0 := by omega
      simp only [hz, Nat.zero_mul]
  calc
    (∑ j ∈ Finset.range (s + 1),
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) =
        ∑ j ∈ Finset.range (J + 1),
          (L + 1 - i - j) * (D - w * i - (w - 1) * j) := htrim.symm
    _ = quadraticDescendingCount A B c (J + 1) := hsmall
    _ = closedCoefficientRow D w L s i := by
      rfl

/-- Coefficient count with a closed inner row and one primitive outer sum. -/
def fastClosedCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (closedCoefficientRow D w L s) cutoff

theorem coefficientCount_eq_fastClosedCoefficientCount
    (D w L s cutoff : ℕ) (hw : 2 ≤ w)
    (hcutoff : cutoff ≤ L + 1) (hweight : D ≤ w * cutoff) :
    coefficientCount D w L s =
      fastClosedCoefficientCount D w L s cutoff := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    D w L s cutoff hcutoff hweight]
  unfold fastClosedCoefficientCount
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact coefficientRow_eq_closedCoefficientRow D w L s i hw

/-! ## Constant-time coefficient count in the one-residue regime

For the large power sources used by the 6800 locator, write `D = q*w+r`.
Their entire slope range satisfies `r+s <= w`.  Hence, in slope row `j`,
the nonzero weighted columns are exactly `0,...,q-j`.  Reflecting those
columns and summing the resulting quadratic gives a linear combination of
`choose (q+1-j) 1`, `choose (q+1-j) 2`, and `choose (q+1-j) 3`.
The hockey-stick identity then closes the remaining slope sum.  Numerical
evaluation below uses descending factorials, so its cost depends only on the
fixed indices `2,3,4`, rather than on `q` or `s`.
-/

private theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        2 * (n + n.choose 2) + (n + 1) =
            (2 * n.choose 2 + n) + (2 * n + 1) := by ring
        _ = n * n + (2 * n + 1) := by rw [ih]
        _ = (n + 1) * (n + 1) := by ring

private theorem kernelSumRange_square_eq_choose (n : ℕ) :
    kernelSumRange (fun i => i * i) n =
      2 * n.choose 3 + n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, ih, Nat.choose_succ_succ,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [← two_mul_choose_two_add n]
      ring

private theorem finset_sum_range_square_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range n, i * i) =
      2 * n.choose 3 + n.choose 2 := by
  rw [← kernelSumRange_eq, kernelSumRange_square_eq_choose]

private theorem sum_increasingProduct_eq_choose (U C w N : ℕ) :
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
      N * (U * C) + (U * w + C) * N.choose 2 +
        w * (2 * N.choose 3 + N.choose 2) := by
  calc
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
        ∑ h ∈ Finset.range N,
          (U * C + (U * w + C) * h + w * (h * h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = N * (U * C) + (U * w + C) * N.choose 2 +
          w * (2 * N.choose 3 + N.choose 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_id,
        finset_sum_range_square_eq_choose, ← Nat.choose_two_right]

private theorem three_mul_choose_three_add_two_mul_choose_two (n : ℕ) :
    3 * n.choose 3 + 2 * n.choose 2 = n * n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        3 * (n.choose 2 + n.choose 3) +
              2 * (n + n.choose 2) =
            (3 * n.choose 3 + 2 * n.choose 2) +
              (2 * n.choose 2 + n) + (n.choose 2 + n) := by ring
        _ = n * n.choose 2 + n * n + (n.choose 2 + n) := by
          rw [ih, two_mul_choose_two_add]
        _ = (n + 1) * (n + n.choose 2) := by ring

private theorem oneResidueRow_algebra
    (U C w r j q N wm T V : ℕ)
    (hC : C = r + j) (hN : N + j = q + 1) (hw : wm + 2 = w)
    (hsq : 2 * T + N = N * N)
    (hcub : 3 * V + 2 * T = N * T) :
    N * (U * C) + (U * w + C) * T + w * (2 * V + T) =
      U * (r + q) * N +
        (U * wm + r + q + (wm + 1)) * T +
          (2 * wm + 1) * V := by
  have hCz : (C : ℤ) = (r : ℤ) + j := by exact_mod_cast hC
  have hNz : (N : ℤ) + j = (q : ℤ) + 1 := by exact_mod_cast hN
  have hwz : (wm : ℤ) + 2 = w := by exact_mod_cast hw
  have hsqz : 2 * (T : ℤ) + N = N * N := by exact_mod_cast hsq
  have hcubz : 3 * (V : ℤ) + 2 * T = N * T := by exact_mod_cast hcub
  have hqz : (q : ℤ) = N + j - 1 := by linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [hCz, ← hwz, hqz]
  linear_combination (U : ℤ) * hsqz + hcubz

/-- The three binomial coefficients of one slope row after reflecting its
weighted columns. -/
private def oneResidueCoefficientRow (q r w L j : ℕ) : ℕ :=
  let U := L + 1 - q
  let N := q + 1 - j
  U * (r + q) * N.choose 1 +
    (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
      (2 * (w - 2) + 1) * N.choose 3

private theorem coefficientColumn_eq_oneResidueCoefficientRow
    (q r w L j : ℕ) (hw : 2 ≤ w) (hj : j ≤ q)
    (hL : q ≤ L) (hres : r + j ≤ w) :
    (∑ i ∈ Finset.range (q + 1),
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) =
      oneResidueCoefficientRow q r w L j := by
  let N := q + 1 - j
  let U := L + 1 - q
  let C := r + j
  have hNpos : 0 < N := by simp only [N]; omega
  have hNq : N ≤ q + 1 := by simp only [N]; omega
  have hsubset : Finset.range N ⊆ Finset.range (q + 1) :=
    Finset.range_mono hNq
  have htrim :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ i ∈ Finset.range (q + 1),
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro i hi hinot
    have hiq : i ≤ q := by
      have := Finset.mem_range.mp hi
      omega
    have hiN : N ≤ i := by
      by_contra hni
      exact hinot (Finset.mem_range.mpr (by omega))
    have hij : q + 1 ≤ i + j := by simp only [N] at hiN; omega
    have hr : r ≤ w - j := by omega
    have hmul : w * (q + 1) ≤ w * (i + j) :=
      Nat.mul_le_mul_left w hij
    have hwj : w * j - j = (w - 1) * j := by
      symm
      rw [Nat.sub_mul]
      simp only [Nat.one_mul]
    have hweight : q * w + r ≤ w * i + (w - 1) * j := by
      calc
        q * w + r ≤ q * w + (w - j) := Nat.add_le_add_left hr _
        _ = w * (q + 1) - j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
          omega
        _ ≤ w * (i + j) - j := Nat.sub_le_sub_right hmul j
        _ = w * i + (w - 1) * j := by
          have hjwj : j ≤ w * j :=
            Nat.le_mul_of_pos_left j (by omega)
          rw [Nat.mul_add, Nat.add_sub_assoc hjwj, hwj]
    have hz : q * w + r - w * i - (w - 1) * j = 0 := by
      rw [Nat.sub_sub]
      exact Nat.sub_eq_zero_of_le hweight
    simp only [hz, Nat.mul_zero]
  have hreflect :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ h ∈ Finset.range N, (U + h) * (C + w * h) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) N]
    apply Finset.sum_congr rfl
    intro h hh
    have hhN : h < N := Finset.mem_range.mp hh
    have hidx : N - 1 - h = q - j - h := by
      simp only [N]
      omega
    have hqsplit : q = (q - j - h) + j + h := by omega
    have hwj : w * j = (w - 1) * j + j := by
      have hw' : w - 1 + 1 = w := by omega
      calc
        w * j = (w - 1 + 1) * j := by rw [hw']
        _ = (w - 1) * j + j := by ring
    have htotal :
        q * w + r = w * (q - j - h) + (w - 1) * j +
          (r + j + w * h) := by
      calc
        q * w + r = ((q - j - h) + j + h) * w + r := by rw [← hqsplit]
        _ = w * (q - j - h) + w * j + w * h + r := by ring
        _ = w * (q - j - h) + (w - 1) * j +
            (r + j + w * h) := by rw [hwj]; ring
    have hfirst : L + 1 - (N - 1 - h) - j = U + h := by
      simp only [N, U]
      omega
    have hsecond :
        q * w + r - w * (N - 1 - h) - (w - 1) * j =
          C + w * h := by
      rw [hidx]
      simp only [C]
      omega
    rw [hfirst, hsecond]
  have hsum := sum_increasingProduct_eq_choose U C w N
  have hNj : N + j = q + 1 := by simp only [N]; omega
  have hwsub : w - 2 + 2 = w := by omega
  have hsq := two_mul_choose_two_add N
  have hcub := three_mul_choose_three_add_two_mul_choose_two N
  rw [← htrim, hreflect, hsum]
  change N * (U * C) + (U * w + C) * N.choose 2 +
      w * (2 * N.choose 3 + N.choose 2) =
    U * (r + q) * N.choose 1 +
      (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
        (2 * (w - 2) + 1) * N.choose 3
  simp only [Nat.choose_one_right]
  exact oneResidueRow_algebra
    (U := U) (C := C) (w := w) (r := r) (j := j) (q := q)
    (N := N) (wm := w - 2) (T := N.choose 2) (V := N.choose 3)
    (by rfl) hNj hwsub hsq hcub

private theorem sum_range_choose_descending_add (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) +
        (N - s).choose (k + 1) = (N + 1).choose (k + 1) := by
  induction s with
  | zero =>
      simp only [Nat.sub_zero, Finset.range_one, Finset.sum_singleton]
      exact (Nat.choose_succ_succ' N k).symm
  | succ s ih =>
      have hs' : s ≤ N := by omega
      rw [Finset.sum_range_succ]
      have hold := ih hs'
      have hpred : N - s = (N - (s + 1)) + 1 := by omega
      have hp := Nat.choose_succ_succ' (N - (s + 1)) k
      rw [← hpred] at hp
      omega

private theorem sum_range_choose_descending (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) =
      (N + 1).choose (k + 1) - (N - s).choose (k + 1) := by
  have h := sum_range_choose_descending_add N s k hs
  omega

/-- `Nat.choose` evaluated through a descending factorial.  In this file it
is used only at indices at most four, so closed source receipts do not recurse
through a thousand Pascal rows. -/
def smallChoose (n k : ℕ) : ℕ :=
  n.descFactorial k / Nat.factorial k

private theorem choose_eq_smallChoose (n k : ℕ) :
    n.choose k = smallChoose n k := by
  simpa only [smallChoose] using
    Nat.choose_eq_descFactorial_div_factorial n k

/-- Constant-time coefficient count for `D=q*w+r` when the complete slope
range remains in the first residue regime. -/
def oneResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  c1 * (smallChoose (q + 2) 2 - smallChoose (q + 1 - s) 2) +
    c2 * (smallChoose (q + 2) 3 - smallChoose (q + 1 - s) 3) +
      c3 * (smallChoose (q + 2) 4 - smallChoose (q + 1 - s) 4)

theorem coefficientCount_eq_oneResidueCoefficientCount
    (q r w L s : ℕ) (hw : 2 ≤ w) (hsq : s ≤ q)
    (hL : q ≤ L) (hres : r + s ≤ w) :
    coefficientCount (q * w + r) w L s =
      oneResidueCoefficientCount q r w L s := by
  have hcutoff : q + 1 ≤ L + 1 := by omega
  have hweight : q * w + r ≤ w * (q + 1) := by
    have hrw : r ≤ w := by omega
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
    omega
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (q * w + r) w L s (q + 1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows :
      (∑ j ∈ Finset.range (s + 1),
        ∑ i ∈ Finset.range (q + 1),
          (L + 1 - i - j) *
            (q * w + r - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        oneResidueCoefficientRow q r w L j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    exact coefficientColumn_eq_oneResidueCoefficientRow q r w L j hw
      (hjs.trans hsq) hL ((Nat.add_le_add_left hjs r).trans hres)
  rw [hrows]
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  have h1 := sum_range_choose_descending (q + 1) s 1 (by omega)
  have h2 := sum_range_choose_descending (q + 1) s 2 (by omega)
  have h3 := sum_range_choose_descending (q + 1) s 3 (by omega)
  unfold oneResidueCoefficientRow
  change (∑ j ∈ Finset.range (s + 1),
      (c1 * (q + 1 - j).choose 1 +
        c2 * (q + 1 - j).choose 2 +
          c3 * (q + 1 - j).choose 3)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  unfold oneResidueCoefficientCount
  rw [← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose]

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-- A numerical nullity receipt for any source profile gives the dimension
needed by the arbitrary-power route, uniformly in the two received words. -/
theorem challengeConstraintKernel_finrank_lower_bound_of_numeric
    (D L s m gap : ℕ) (u0 u1 : I → K)
    (hnumeric : gap ≤ coefficientCount D 131071 L s -
      262144 * localRankBound m L s) :
    gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    (K := K) D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hnumeric.trans hlo'

end ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
end PackedLocator_LocatorFastKernelArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Parameters. -/
section PackedLocator_LocatorR1200Parameters

/-! Shared, reduction-cheap definitions for the 1200-contact locator source. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the R1200 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 82100
  let h := min (r + 1) (1200 - r)
  rectangularCount (M + 1) (370 + 1) 0 82100 -
    rectangularCount (M + 1 - h) (370 + 1 - h) h 82100

end ProximityPrize.SubmissionLower.LocatorR1200Parameters
end PackedLocator_LocatorR1200Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Coefficient. -/
section PackedLocator_LocatorR1200Coefficient

/-! Constant-time coefficient-count receipt for the R1200 source. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 217670400 131071 82100 370 =
      4337453593087735190 := by
  change coefficientCount (1660 * 131071 + 92540) 131071 82100 370 =
    4337453593087735190
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1660 92540 131071 82100 370 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorR1200Coefficient
end PackedLocator_LocatorR1200Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankA. -/
section PackedLocator_LocatorR1200RankA

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 63196733600 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 187580342432 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 311866695840 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 436055793824 := by decide

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 560147636384 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankB. -/
section PackedLocator_LocatorR1200RankB

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 684142223520 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 808039555232 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 64, rankRow (448 + i)) = 931839631520 := by decide

theorem chunk_512 :
    (∑ i ∈ Finset.range 64, rankRow (512 + i)) = 1055542452384 := by decide

theorem chunk_576 :
    (∑ i ∈ Finset.range 64, rankRow (576 + i)) = 1179148017824 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankC. -/
section PackedLocator_LocatorR1200RankC

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_640 :
    (∑ i ∈ Finset.range 64, rankRow (640 + i)) = 1302656327840 := by decide

theorem chunk_704 :
    (∑ i ∈ Finset.range 64, rankRow (704 + i)) = 1426067382432 := by decide

theorem chunk_768 :
    (∑ i ∈ Finset.range 64, rankRow (768 + i)) = 1549268140176 := by decide

theorem chunk_832 :
    (∑ i ∈ Finset.range 64, rankRow (832 + i)) = 1574048718272 := by decide

theorem chunk_896 :
    (∑ i ∈ Finset.range 64, rankRow (896 + i)) = 1455328904640 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankC

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankD. -/
section PackedLocator_LocatorR1200RankD

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_960 :
    (∑ i ∈ Finset.range 64, rankRow (960 + i)) = 1251326569920 := by decide

theorem chunk_1024 :
    (∑ i ∈ Finset.range 64, rankRow (1024 + i)) = 962142377408 := by decide

theorem chunk_1088 :
    (∑ i ∈ Finset.range 64, rankRow (1088 + i)) = 587876990400 := by decide

theorem chunk_1152 :
    (∑ i ∈ Finset.range 48, rankRow (1152 + i)) = 144171197072 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankD

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Rank. -/
section PackedLocator_LocatorR1200Rank

/-! Assembly of the separately checked R1200 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 1200 82100 370 = 16470445690720 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 1200, rankRow r) = _
  rw [Finset.sum_range_add rankRow 1152 48,
    Finset.sum_range_add rankRow 1088 64,
    Finset.sum_range_add rankRow 1024 64,
    Finset.sum_range_add rankRow 960 64,
    Finset.sum_range_add rankRow 896 64,
    Finset.sum_range_add rankRow 832 64,
    Finset.sum_range_add rankRow 768 64,
    Finset.sum_range_add rankRow 704 64,
    Finset.sum_range_add rankRow 640 64,
    Finset.sum_range_add rankRow 576 64,
    Finset.sum_range_add rankRow 512 64,
    Finset.sum_range_add rankRow 448 64,
    Finset.sum_range_add rankRow 384 64,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192, chunk_256,
    chunk_320, chunk_384, chunk_448, chunk_512, chunk_576,
    chunk_640, chunk_704, chunk_768, chunk_832, chunk_896,
    chunk_960, chunk_1024, chunk_1088, chunk_1152]

theorem localRankBound_exact :
    localRankBound 1200 82100 370 = 16470445690720 := by
  rw [localRankBound_eq_fastLocalRankBound 1200 82100 370 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Source. -/
section PackedLocator_LocatorR1200Source

/-! Semantic kernel source backed by the isolated R1200 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Source

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 217670400 131071 82100 370 1200
    IRSProfile.domain u0 u1

theorem weighted_exact : 1200 * 181392 = 217670400 := by
  decide

theorem shape : 217670400 + 370 ≤ 131071 * (1660 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 217670400 131071 82100 370 -
      262144 * localRankBound 1200 82100 370 =
        19825077939631510 := by
  rw [LocatorR1200Coefficient.coefficientCount_exact,
    LocatorR1200Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    19825077939631510 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    217670400 82100 370 1200 19825077939631510 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorR1200Source
end PackedLocator_LocatorR1200Source

/-! Packed from ProximityPrize.SubmissionLower.LocatorChainArithmetic. -/
section PackedLocator_LocatorChainArithmetic

/-! A small, independently checkable receipt for the asymmetric derivative-chain cost. -/

namespace ProximityPrize.SubmissionLower.LocatorChainArithmetic

open RCN260

/-- In every nonterminal derivative-chain stage `j >= 1`, the left polynomial
has `R`-degree at most `32`, while the original factor on the right may still
have `R`-degree `33`. -/
def chainStage : UnequalParameters :=
  ⟨262144, 131071, 181392, 153, 32, 10381, 153, 33, 10381⟩

theorem chainStage_exact : chainStage.regularCountCap = 211479108682951 := by
  decide

end ProximityPrize.SubmissionLower.LocatorChainArithmetic
end PackedLocator_LocatorChainArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorArithmetic. -/
section PackedLocator_LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302 RCN318 RCN260 LocatorFastKernelArithmetic
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80752
def agreements:ℕ:=181392
def gap:ℕ:=50321
def prime:ℕ:=2130706433
def budget:ℕ:=274980723472028131
def LA:ℕ:=130000
def LB:ℕ:=10381
def LCap:ℕ:=5968
def yB:ℕ:=153
def sB:ℕ:=33
def yC:ℕ:=373
def sC:ℕ:=81
def yT:ℕ:=250
def sT:ℕ:=56
def weightedA:ℕ:=16688064
def weightedC:ℕ:=48975840
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=20134512
def weightedTCap:ℕ:=32831952
def fixedRegularCap:ℕ:=259787835303351020
theorem kernelA_rank:localRankBound 92 130000 28=12271362702:=by
  rw [localRankBound_eq_fastLocalRankBound 92 130000 28 (by decide)]
  decide
theorem kernelC_rank:localRankBound 270 130000 81=296615133081:=by
  rw [localRankBound_eq_fastLocalRankBound 270 130000 81 (by decide)]
  decide
theorem kernelB_rank:localRankBound 111 10381 33=1669841677:=by
  rw [localRankBound_eq_fastLocalRankBound 111 10381 33 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 181 5968 56=4181070327:=by
  rw [localRankBound_eq_fastLocalRankBound 181 5968 56 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 16688064 131071 130000 28 -
      262144 * localRankBound 92 130000 28=19682753357:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    16688064 131071 130000 28 128 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 48975840 131071 130000 81 -
      262144 * localRankBound 270 130000 81=321495185604514:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    48975840 131071 130000 81 374 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 20134512 131071 10381 33 -
      262144 * localRankBound 111 10381 33=7792307:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    20134512 131071 10381 33 154 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 32831952 131071 5968 56 -
      262144 * localRankBound 181 5968 56=786110180:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    32831952 131071 5968 56 251 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 32831952 131071 3 56 <
    coefficientCount 32831952 131071 5968 56 -
      262144 * localRankBound 181 5968 56:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedB,5964,sB⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yT,sT,LCap⟩
def chainStage:UnequalParameters:=
  ⟨n,w,agreements,yB,sB-1,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
def fixedSingularCap:ℕ:=
  CommonShearTightPrototype.countCap fixedSingular
theorem fixedSingular_exact:fixedSingularCap=7928559416753516:=by decide
theorem residualStage_exact:residualStage.regularCountCap=385018957438443:=by decide
theorem chainStage_exact:chainStage.regularCountCap=211479108682951:=by
  simpa [chainStage, LocatorChainArithmetic.chainStage, n, w, agreements,
    yB, sB, LB] using LocatorChainArithmetic.chainStage_exact
theorem tailSingular_exact:tailSingular.countCap=3253740279290:=by decide
structure SingularGates (P:TightParameters):Prop where
  s_pos:1 ≤ P.s
  s_small:P.s < prime
  w_pos:1 ≤ P.w
  w_small:P.w < prime
  kD:P.w < P.kappa * P.D
  algebraic_pos:1 ≤ P.algebraicCap
  implicit_small:P.implicitYCap < prime
  algebraic_small:P.algebraicCap < prime
  mixed_small:2 * P.implicitYCap * P.algebraicCap < prime
  wa:P.w < P.a
  an:P.a ≤ P.n
theorem tail_singular_gates:SingularGates tailSingular:=by constructor <;> decide
structure ChainGates:Prop where
  qY:(tailSingular.D - 1) / w ≤ chainStage.leftY
  qR:tailSingular.s ≤ chainStage.leftR
  qZ:tailSingular.L ≤ chainStage.leftZ
  leftR_pos:1 ≤ chainStage.leftR
  leftY_small:chainStage.leftY < prime
  leftR_small:chainStage.leftR < prime
  leftZ_small:chainStage.leftZ < prime
  rightR_pos:1 ≤ chainStage.rightR
  rightY_small:chainStage.rightY < prime
  rightR_small:chainStage.rightR < prime
  rightZ_small:chainStage.rightZ < prime
  mixedY_small:chainStage.mixedCost.y < prime
  mixedR_small:chainStage.mixedCost.r < prime
  mixedZ_small:chainStage.mixedCost.z < prime
theorem chain_gates:ChainGates:=by constructor <;> decide
def ledger:ℕ:=fixedRegularCap + fixedSingularCap +
  residualStage.regularCountCap +
  (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap
theorem ledger_exact:ledger=274979372324893271:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10336383
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
theorem radius_floor:
    ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors:=by
  norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    errors,IRSProfile.Index]
theorem radius_admissible:
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_radius_integer:
    (23218049:ℕ)^128 * 2^68 ≤ 33554432^128:=by decide
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      (1:ℝ≥0)/2^(68:ℕ):=by
  have hsub:(1 - radius:ℝ≥0) =23218049/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ (1:ℝ≥0)/2^(68:ℕ)
  rw [hsub,div_pow,div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6800:=by
  calc
    (1 - radius)^IRSProfile.repetitions ≤ (1:ℝ≥0)/2^(68:ℕ):=radius_power_bound
    _=claimedError 6800:=by
      unfold claimedError
      norm_num [NNReal.rpow_neg, NNReal.rpow_natCast]
end
end LocatorArithmetic
end ProximityPrize.SubmissionLower
end PackedLocator_LocatorArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceCGap. -/
section PackedLocator_LocatorSourceCGap

namespace ProximityPrize.SubmissionLower.LocatorSourceCGap

open ProximityPrize.Benchmark
open LocatorArithmetic
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

theorem finrank_lower_bound (u0 u1 : I → K) :
    321495185604514 ≤ Module.finrank K
      (ConstraintKernel (K := K) 48975840 131071 130000 81 270
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    48975840 131071 130000 81 270 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact LocatorArithmetic.kernelC_nullity ▸ hlo'

end

end ProximityPrize.SubmissionLower.LocatorSourceCGap
end PackedLocator_LocatorSourceCGap

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Parameters. -/
section PackedLocator_LocatorSplit500Parameters

/-! Shared, reduction-cheap definitions for the 500-contact split source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the Split500 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 21000
  let h := min (r + 1) (500 - r)
  rectangularCount (M + 1) (155 + 1) 0 21000 -
    rectangularCount (M + 1 - h) (155 + 1 - h) h 21000

end ProximityPrize.SubmissionLower.LocatorSplit500Parameters
end PackedLocator_LocatorSplit500Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Coefficient. -/
section PackedLocator_LocatorSplit500Coefficient

/-! Constant-time coefficient-count receipt for the Split500 source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 90696000 131071 21000 155 = 80552687771609625 := by
  change coefficientCount (691 * 131071 + 125939) 131071 21000 155 =
    80552687771609625
  rw [coefficientCount_eq_oneResidueCoefficientCount
    691 125939 131071 21000 155 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit500Coefficient
end PackedLocator_LocatorSplit500Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankA. -/
section PackedLocator_LocatorSplit500RankA

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 6782443200 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 20111163072 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 33398988480 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 46645919424 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankB. -/
section PackedLocator_LocatorSplit500RankB

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 59851955904 := by decide

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 69107989600 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 53769638208 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 52, rankRow (448 + i)) = 16736449392 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Rank. -/
section PackedLocator_LocatorSplit500Rank

/-! Assembly of the separately checked Split500 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 500 21000 155 = 306404547280 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 500, rankRow r) = _
  rw [Finset.sum_range_add rankRow 448 52,
    Finset.sum_range_add rankRow 384 64,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192,
    chunk_256, chunk_320, chunk_384, chunk_448]

theorem localRankBound_exact :
    localRankBound 500 21000 155 = 306404547280 := by
  rw [localRankBound_eq_fastLocalRankBound 500 21000 155 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Source. -/
section PackedLocator_LocatorSplit500Source

/-! Semantic kernel source backed by the isolated Split500 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Source

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 90696000 131071 21000 155 500
    IRSProfile.domain u0 u1

theorem weighted_exact : 500 * 181392 = 90696000 := by
  decide

theorem shape : 90696000 + 155 ≤ 131071 * (691 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 90696000 131071 21000 155 -
      262144 * localRankBound 500 21000 155 = 230574129441305 := by
  rw [LocatorSplit500Coefficient.coefficientCount_exact,
    LocatorSplit500Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    230574129441305 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    90696000 21000 155 500 230574129441305 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSplit500Source
end PackedLocator_LocatorSplit500Source

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Parameters. -/
section PackedLocator_LocatorSplit390Parameters

/-! Shared, reduction-cheap definitions for the 390-contact split source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the Split390 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 19500
  let h := min (r + 1) (390 - r)
  rectangularCount (M + 1) (120 + 1) 0 19500 -
    rectangularCount (M + 1 - h) (120 + 1 - h) h 19500

end ProximityPrize.SubmissionLower.LocatorSplit390Parameters
end PackedLocator_LocatorSplit390Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Coefficient. -/
section PackedLocator_LocatorSplit390Coefficient

/-! Constant-time coefficient-count receipt for the Split390 source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 70742880 131071 19500 120 = 35454114385401910 := by
  change coefficientCount (539 * 131071 + 95611) 131071 19500 120 =
    35454114385401910
  rw [coefficientCount_eq_oneResidueCoefficientCount
    539 95611 131071 19500 120 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit390Coefficient
end PackedLocator_LocatorSplit390Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankA. -/
section PackedLocator_LocatorSplit390RankA

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open scoped BigOperators
open LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 4887625600 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 14491176832 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 24063008640 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 33603121024 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankB. -/
section PackedLocator_LocatorSplit390RankB

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open scoped BigOperators
open LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 37791122159 := by decide

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 19811668800 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 6, rankRow (384 + i)) = 203453075 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Rank. -/
section PackedLocator_LocatorSplit390Rank

/-! Assembly of the separately checked Split390 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 390 19500 120 = 134851176130 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 390, rankRow r) = _
  rw [Finset.sum_range_add rankRow 384 6,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192,
    chunk_256, chunk_320, chunk_384]

theorem localRankBound_exact :
    localRankBound 390 19500 120 = 134851176130 := by
  rw [localRankBound_eq_fastLocalRankBound 390 19500 120 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390Rank

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Source. -/
section PackedLocator_LocatorSplit390Source

/-! Semantic kernel source backed by the isolated Split390 receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Source

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 70742880 131071 19500 120 390
    IRSProfile.domain u0 u1

theorem weighted_exact : 390 * 181392 = 70742880 := by
  decide

theorem shape : 70742880 + 120 ≤ 131071 * (539 + 1) := by
  decide

theorem nullity_exact :
    coefficientCount 70742880 131071 19500 120 -
      262144 * localRankBound 390 19500 120 = 103687669979190 := by
  rw [LocatorSplit390Coefficient.coefficientCount_exact,
    LocatorSplit390Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    103687669979190 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    70742880 19500 120 390 103687669979190 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSplit390Source
end PackedLocator_LocatorSplit390Source

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPhase6800. -/
section PackedLocator_LocatorBatchPhase6800

/-!
# Semantic batch phases for the 6800 certificate

This module identifies a finset's cumulative flag with the three exact
weights of its squarefree regular product and connects the numerical
`SourceNumbers.Routeable` predicate to the shared batch source theorem.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPhase6800

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute LocatorBatchPowerRoute
  LocatorGenericHelperFactorSwitch LocatorPhase6800Oracle

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/-- Additive flag of a finite batch of regular factors. -/
def regularAggregateFlag (H : P4) (A : Finset (RegularIndex H)) : FlagDegree :=
  sumFlag A (regularCumulativeFlag H)

private theorem regularProduct_weight_eq_sum
    (weights : Fin 4 → ℕ) (H : P4) (A : Finset (RegularIndex H)) :
    wt weights (regularProduct H A) = ∑ F ∈ A, wt weights F.1 := by
  have h := weightedTotalDegree_prod_eq weights A
    (fun F : RegularIndex H => F.1)
    (fun F _hF => regularFactor_ne_zero H F)
  simpa only [regularProduct, wt] using h

theorem regularAggregateFlag_all (H : P4) (A : Finset (RegularIndex H)) :
    (regularAggregateFlag H A).all =
      wt residualSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_all]
  calc
    (∑ F ∈ A, (regularCumulativeFlag H F).all) =
        ∑ F ∈ A, wt residualSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).1
    _ = wt residualSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualSWeights H A).symm

theorem regularAggregateFlag_middle (H : P4)
    (A : Finset (RegularIndex H)) :
    middle (regularAggregateFlag H A) =
      wt residualYSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_middle]
  calc
    (∑ F ∈ A, middle (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualYSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.1
    _ = wt residualYSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualYSWeights H A).symm

theorem regularAggregateFlag_total (H : P4)
    (A : Finset (RegularIndex H)) :
    total (regularAggregateFlag H A) =
      wt residualTotalWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_total]
  calc
    (∑ F ∈ A, total (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualTotalWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.2
    _ = wt residualTotalWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualTotalWeights H A).symm

theorem regularAggregateFlag_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    (regularAggregateFlag H A).all ≤ (regularAggregateFlag H B).all ∧
      middle (regularAggregateFlag H A) ≤
        middle (regularAggregateFlag H B) ∧
      total (regularAggregateFlag H A) ≤
        total (regularAggregateFlag H B) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨Finset.sum_le_sum_of_subset hAB,
    Finset.sum_le_sum_of_subset hAB, Finset.sum_le_sum_of_subset hAB⟩

theorem regularAggregateFlag_all_lt_of_ssubset (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊂ B) :
    (regularAggregateFlag H A).all < (regularAggregateFlag H B).all := by
  have hnBA : ¬ B ⊆ A := by
    intro hBA
    exact hAB.ne (Finset.Subset.antisymm hAB.subset hBA)
  simp only [Finset.subset_iff, not_forall, _root_.not_imp] at hnBA
  obtain ⟨F, hFB, hFA⟩ := hnBA
  simp only [regularAggregateFlag, sumFlag_all]
  exact Finset.sum_lt_sum_of_subset hAB.subset hFB hFA
    (regularCumulativeFlag_positive H F)
    (fun _ _ _ => Nat.zero_le _)

private theorem sourceFuel_pos (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) (ht : total p ≤ s.totalCap)
    (hy : middle p ≤ s.middleCap) (hs : p.all ≤ s.slopeCap) :
    1 ≤ s.fuel p := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem sourceFuel_feasible (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.fuel p * total p ≤ s.totalCap ∧
      s.fuel p * middle p ≤ s.middleCap ∧
      s.fuel p * p.all ≤ s.slopeCap := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) :
    a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem sourceFuel_terminal (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.totalCap - s.fuel p * total p < total p ∨
      s.middleCap - s.fuel p * middle p < middle p ∨
      s.slopeCap - s.fuel p * p.all < p.all := by
  have hall : 0 < p.all := by omega
  have hmiddle : 0 < middle p := hall.trans_le (all_le_middle p)
  have htotal : 0 < total p := hmiddle.trans_le (middle_le_total p)
  unfold SourceNumbers.fuel
  by_cases hT : s.totalCap / total p ≤
      min (s.middleCap / middle p) (s.slopeCap / p.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle p ≤ s.slopeCap / p.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle p) hmiddle
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap p.all hr

/-- A numerical route for an aggregate flag supplies the strict algebraic
split required by the phase recursion. -/
theorem routeable_exists_strict_helper_split
    (sound : PhaseSourceSound) (D m : ℕ)
    (hweighted : D = m * 181392)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 28)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 127)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 5964) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        sound.potential.eval (regularCumulativeFlag H F) := by
  classical
  let p := regularAggregateFlag H A
  have hr : 1 ≤ p.all := hroute.1
  have hA : A.Nonempty := by
    by_contra hzero
    have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p, regularAggregateFlag, sumFlag] at hr
  have hfuel : 1 ≤ sound.source.fuel p :=
    sourceFuel_pos sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP := sourceFuel_feasible sound.source p hr
  have hterminalP := sourceFuel_terminal sound.source p hr
  have hfuelSlope : sound.source.fuel p ≤ sound.source.slopeCap := by
    calc
      sound.source.fuel p ≤ sound.source.slopeCap / p.all :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ sound.source.slopeCap := Nat.div_le_self _ _
  have hfuelM : sound.source.fuel p ≤ m := hfuelSlope.trans hslopeM
  have hfuelChar : sound.source.fuel p < 2130706433 :=
    hfuelM.trans_lt hmChar
  have hlowpos : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      0 < D - j * 50322 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50322 ≤
        (m - j) * 181392 + j * (131071 - 1) := by
    intro j _hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield : A.card < ENat.card K := by
    have hcard : A.card ≤ p.all := by
      calc
        A.card = ∑ F ∈ A, 1 := by simp
        _ ≤ ∑ F ∈ A, (regularCumulativeFlag H F).all :=
          Finset.sum_le_sum (fun F _ => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
        _ = p.all := by simp only [p, regularAggregateFlag, sumFlag_all]
    calc
      (A.card : ENat) ≤ (28 : ℕ) := by
        exact_mod_cast hcard.trans hnarrowS
      _ < ENat.card K := by
        rw [ENat.card_eq_coe_fintype_card, RCN183.field_cardinality]
        norm_num
  have factor_le_aggregate (F : RegularIndex H) (hFA : F ∈ A) :
      (regularCumulativeFlag H F).all ≤ p.all ∧
      middle (regularCumulativeFlag H F) ≤ middle p ∧
      total (regularCumulativeFlag H F) ≤ total p := by
    have hsub : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p, regularAggregateFlag, sumFlag, middle, total] using
      regularAggregateFlag_mono H hsub
  have factorFuel (F : RegularIndex H) (hFA : F ∈ A) (j : ℕ)
      (hj : j ≤ sound.source.fuel p) :
      j ≤ sound.source.fuel (regularCumulativeFlag H F) := by
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hFm : 1 ≤ middle (regularCumulativeFlag H F) :=
      hFr.trans (all_le_middle _)
    have hFt : 1 ≤ total (regularCumulativeFlag H F) :=
      hFm.trans (middle_le_total _)
    have hjT : j * total (regularCumulativeFlag H F) ≤
        sound.source.totalCap := by
      calc
        j * total (regularCumulativeFlag H F) ≤ j * total p :=
          Nat.mul_le_mul_left j hle.2.2
        _ ≤ sound.source.fuel p * total p :=
          Nat.mul_le_mul_right (total p) hj
        _ ≤ sound.source.totalCap := hfeasibleP.1
    have hjY : j * middle (regularCumulativeFlag H F) ≤
        sound.source.middleCap := by
      calc
        j * middle (regularCumulativeFlag H F) ≤ j * middle p :=
          Nat.mul_le_mul_left j hle.2.1
        _ ≤ sound.source.fuel p * middle p :=
          Nat.mul_le_mul_right (middle p) hj
        _ ≤ sound.source.middleCap := hfeasibleP.2.1
    have hjS : j * (regularCumulativeFlag H F).all ≤
        sound.source.slopeCap := by
      calc
        j * (regularCumulativeFlag H F).all ≤ j * p.all :=
          Nat.mul_le_mul_left j hle.1
        _ ≤ sound.source.fuel p * p.all :=
          Nat.mul_le_mul_right p.all hj
        _ ≤ sound.source.slopeCap := hfeasibleP.2.2
    unfold SourceNumbers.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      HelperPairGates
        (sound.source.totalCap - j * wt residualTotalWeights F.1)
        (sound.source.middleCap - j * wt residualYSWeights F.1)
        (sound.source.slopeCap - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageGates (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [hR, hY, hT] using hs
  have hcharge : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      LocatorGenericPowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (LocatorBatchPowerRoute.exactRouteBox F) j ≤
          sound.potential.eval (regularCumulativeFlag H F) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageCost_le (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [LocatorBatchPowerRoute.exactRouteBox,
      LocatorPhase6800Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181392 := hweighted.le
  apply exists_strict_helper_split_of_batch_source D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50322 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using
        hroute.2.2.2.2
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hterminalP
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

/-! ## State-local phase semantics

The numerical receipt is indexed by the exact aggregate raw flag.  These
lemmas keep that state intact while the algebraic route repeatedly replaces a
routeable batch by a strict universal sub-batch.
-/

/-- Raw-coordinate monotonicity of the aggregate flag. -/
theorem regularAggregateFlag_raw_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    RawBelow (regularAggregateFlag H A) (regularAggregateFlag H B) := by
  refine ⟨?_, ?_, ?_⟩
  · change (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).all
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).yz) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).yz
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).zOnly) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).zOnly
    exact Finset.sum_le_sum_of_subset hAB

/-- An additive phase potential commutes with aggregation. -/
theorem sum_phasePotential_eval (q : Potential) (H : P4)
    (A : Finset (RegularIndex H)) :
    (∑ F ∈ A, q.eval (regularCumulativeFlag H F)) =
      q.eval (regularAggregateFlag H A) := by
  simp only [Potential.eval, Finset.sum_add_distrib, ← Finset.mul_sum,
    regularAggregateFlag, sumFlag_total, sumFlag_middle, sumFlag_all]

/-- State-local regular-seed bound used between consecutive source phases. -/
def StateLocalRegularBound (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H),
    (regularAggregateFlag H A).all ≤ 28 →
    middle (regularAggregateFlag H A) ≤ 127 →
    total (regularAggregateFlag H A) ≤ 5964 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- Ambient-scoped form needed after the initial A split.  Only factors in
the A-universal set have the narrow ordinary bound. -/
def StateLocalRegularBoundOn (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (ambient : Finset (RegularIndex H))
    (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H), A ⊆ ambient →
    (regularAggregateFlag H A).all ≤ 28 →
    middle (regularAggregateFlag H A) ≤ 127 →
    total (regularAggregateFlag H A) ≤ 5964 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- The state-local ordinary base restricted to an ambient factor set. -/
theorem stateLocalRegularBoundOn_of_base
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H)) (baseCap : FlagDegree → ℕ)
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap) :
    StateLocalRegularBoundOn H selected Gamma ambient baseCap := by
  classical
  intro A hAambient hs hy ht
  calc
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
        ∑ F ∈ A,
          LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H F) :=
      Finset.sum_le_sum (fun F hFA =>
        LocatorHybridCost.ownBound_le_ordinaryCostOf
          (hown F (hAambient hFA)))
    _ ≤ baseCap (regularAggregateFlag H A) := by
      simpa only [regularAggregateFlag] using
        hbase A (regularCumulativeFlag H)
          (fun F _hF => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F))) hs hy ht

/-- The state-local ordinary partition oracle starts the four phase chain. -/
theorem stateLocalRegularBound_of_base
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (baseCap : FlagDegree → ℕ)
    (hown : ∀ F, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap) :
    StateLocalRegularBound H selected Gamma baseCap := by
  classical
  intro A hs hy ht
  calc
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
        ∑ F ∈ A,
          LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H F) :=
      Finset.sum_le_sum (fun F _hF =>
        LocatorHybridCost.ownBound_le_ordinaryCostOf (hown F))
    _ ≤ baseCap (regularAggregateFlag H A) := by
      simpa only [regularAggregateFlag] using
        hbase A (regularCumulativeFlag H)
          (fun F _hF => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F))) hs hy ht

/-- Concrete kernel realization of one numerical source. -/
structure PhaseKernelRealization (sound : PhaseSourceSound)
    (u0 u1 : I → K) where
  D : ℕ
  m : ℕ
  weighted : D = m * 181392
  shape : D + sound.source.slopeCap ≤
    131071 * (sound.source.middleCap + 1)
  slope_le_m : sound.source.slopeCap ≤ m
  m_lt_char : m < 2130706433
  gap_le_finrank : sound.source.gap ≤ Module.finrank K
    (ConstraintKernel (K := K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)

/-- One source phase preserves a state-local bound according to the numeric
cap equation.  The only recursive calls are on strict factor subsets, hence
the receipt defect is queried at a strict raw-slope child of the parent. -/
theorem stateLocalRegularBoundOn_onePhase
    (sound : PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (previousCap nextCap defect : FlagDegree → ℕ)
    (hprevious : StateLocalRegularBoundOn H selected Gamma ambient previousCap)
    (hdefect : PhaseDefectSound previousCap sound.source
      sound.potential defect)
    (hcap : PhaseCapEquation previousCap nextCap sound.source
      sound.potential defect) :
    StateLocalRegularBoundOn H selected Gamma ambient nextCap := by
  classical
  intro A hAambient hs hy ht
  let p := regularAggregateFlag H A
  have hpreviousA :
      (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤ previousCap p :=
    hprevious A hAambient hs hy ht
  have hcapP := hcap p hs hy ht
  by_cases hrouteP : sound.source.Routeable p
  · have hphase :
        (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
          min (previousCap p)
            ((∑ F ∈ A,
              sound.potential.eval (regularCumulativeFlag H F)) + defect p) := by
      apply sum_count_le_min_previous_onePhase
        (fun F : RegularIndex H =>
          (regularSeeds H selected Gamma F).card)
        (fun F : RegularIndex H =>
          sound.potential.eval (regularCumulativeFlag H F))
        (fun B : Finset (RegularIndex H) =>
          sound.source.Routeable (regularAggregateFlag H B))
        (fun B : Finset (RegularIndex H) =>
          previousCap (regularAggregateFlag H B)) A (defect p)
      · intro B hBA
        have hmono := regularAggregateFlag_mono H hBA
        exact hprevious B (hBA.trans hAambient)
          (hmono.1.trans hs) (hmono.2.1.trans hy)
          (hmono.2.2.trans ht)
      · intro B hBA hnrouteB
        have hne : B ≠ A := by
          intro hBAeq
          subst B
          exact hnrouteB hrouteP
        have hproper : B ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hBA, hne⟩
        have hd := hdefect p (regularAggregateFlag H B) hs hy ht
          ⟨regularAggregateFlag_raw_mono H hBA,
            regularAggregateFlag_all_lt_of_ssubset H hproper⟩ hnrouteB
        rw [← sum_phasePotential_eval sound.potential H B] at hd
        exact hd
      · intro B hBA hrouteB
        have hmono := regularAggregateFlag_mono H hBA
        obtain ⟨U, hUB, hexit⟩ :=
          routeable_exists_strict_helper_split sound kernel.D kernel.m
            kernel.weighted kernel.shape kernel.slope_le_m kernel.m_lt_char
            u0 u1 H selected Gamma hdegree hagreement hno
            kernel.gap_le_finrank B hrouteB
            (hmono.1.trans hs) (hmono.2.1.trans hy)
            (hmono.2.2.trans ht)
        refine ⟨U, hUB, ?_⟩
        exact Finset.sum_le_sum (fun F hFU => hexit F hFU)
    rw [hcapP, if_pos hrouteP]
    simpa only [p, sum_phasePotential_eval] using hphase
  · rw [hcapP, if_neg hrouteP]
    exact hpreviousA

/-- Unscoped convenience corollary. -/
theorem stateLocalRegularBound_onePhase
    (sound : PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (previousCap nextCap defect : FlagDegree → ℕ)
    (hprevious : StateLocalRegularBound H selected Gamma previousCap)
    (hdefect : PhaseDefectSound previousCap sound.source
      sound.potential defect)
    (hcap : PhaseCapEquation previousCap nextCap sound.source
      sound.potential defect) :
    StateLocalRegularBound H selected Gamma nextCap := by
  have hpreviousOn : StateLocalRegularBoundOn H selected Gamma
      (Finset.univ : Finset (RegularIndex H)) previousCap := by
    intro A _hA hs hy ht
    exact hprevious A hs hy ht
  have hnext := stateLocalRegularBoundOn_onePhase sound u0 u1 kernel H
    selected Gamma (Finset.univ : Finset (RegularIndex H)) hdegree
    hagreement hno previousCap nextCap defect hpreviousOn hdefect hcap
  intro A hs hy ht
  exact hnext A (fun _ _ ↦ Finset.mem_univ _) hs hy ht

end

end ProximityPrize.SubmissionLower.LocatorBatchPhase6800
end PackedLocator_LocatorBatchPhase6800

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound. -/
section PackedLocator_LocatorPhase6800SourceSound

/-! Analytic helper-cost and gate bounds for the four 6800 phase sources. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    (helperPair L₁ Y₁ S₁ leftY leftR leftZ).regularCountCap ≤
      (helperPair L₂ Y₂ S₂ leftY leftR leftZ).regularCountCap := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.agreement P₂.agreement := by
    refine ⟨?_, ?_, ?_⟩
    · exact max_le_max le_rfl (Nat.add_le_add_left
        (Nat.mul_le_mul_left (2 * 131071) hY) 1)
    · exact max_le_max le_rfl (Nat.mul_le_mul_left 131071
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hS) 1))
    · exact max_le_max le_rfl (Nat.add_le_add_right
        (Nat.mul_le_mul_left (2 * 131071) hL) 1)
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.agreement P₁.mixedCost ≤
      dot P₂.agreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : P₁.regularNumerator ≤ P₂.regularNumerator := by
    unfold UnequalParameters.regularNumerator
    exact Nat.add_le_add (Nat.mul_le_mul_left (P₁.n - P₁.w) hdot)
      (Nat.mul_le_mul_left ((P₁.errors + 1) * P₁.gap) hm.2.2)
  exact Nat.div_le_div_right hnum

theorem stageCost_le_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ) :
    stageCost L YS S (exactRouteBox p) j ≤
      stageCost L YS S (exactRouteBox p) 0 := by
  apply helperPair_regularCountCap_mono_right
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le L (j * total p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le YS (j * middle p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le S (j * p.all)

theorem helperPair_gates_of_right_le
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hgate : HelperPairGates L₂ Y₂ S₂ leftY leftR leftZ) :
    HelperPairGates L₁ Y₁ S₁ leftY leftR leftZ := by
  rcases hgate with ⟨hr, hy, hs, hz, hmy, hmr, hmz⟩
  refine ⟨hr, hy, hs, hz, ?_, ?_, ?_⟩
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
      (Nat.mul_le_mul_left leftZ hS)).trans_lt hmy
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
      (Nat.mul_le_mul_left leftZ hY)).trans_lt hmr
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
      (Nat.mul_le_mul_left leftR hY)).trans_lt hmz

theorem stageGates_of_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ)
    (hgate : HelperPairGates L YS S (middle p) p.all (total p)) :
    HelperPairGates (L - j * total p) (YS - j * middle p)
      (S - j * p.all) (middle p) p.all (total p) := by
  apply helperPair_gates_of_right_le
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact hgate

private theorem r1200_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    stageCost 82100 1660 370 (exactRouteBox p) 0 ≤
      r1200Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 435155721 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 96861469 := by omega
  have haz : 262142 * total p + 1 ≤ 21521858201 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, r1200Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem sourceC_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    stageCost 130000 373 81 (exactRouteBox p) 0 ≤
      sourceCPotential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 97778967 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 21102431 := by omega
  have haz : 262142 * total p + 1 ≤ 34078460001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, sourceCPotential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split500_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    stageCost 21000 691 155 (exactRouteBox p) 0 ≤
      split500Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 181140123 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 40500939 := by omega
  have haz : 262142 * total p + 1 ≤ 5504982001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split500Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split390_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    stageCost 19500 539 120 (exactRouteBox p) 0 ≤
      split390Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 141294539 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 31325969 := by omega
  have haz : 262142 * total p + 1 ≤ 5111769001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split390Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem r1200_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    HelperPairGates 82100 1660 370 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem sourceC_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    HelperPairGates 130000 373 81 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem split500_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    HelperPairGates 21000 691 155 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem split390_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 28)
    (hy : middle p ≤ 127) (ht : total p ≤ 5964) :
    HelperPairGates 19500 539 120 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def r1200Sound : PhaseSourceSound where
  source := sourceR1200
  potential := r1200Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 82100 1660 370 p j).trans
      (r1200_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 82100 1660 370 p j
      (r1200_stageZero_gates p hr hs hy ht)

def sourceCSound : PhaseSourceSound where
  source := sourceC
  potential := sourceCPotential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 130000 373 81 p j).trans
      (sourceC_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 130000 373 81 p j
      (sourceC_stageZero_gates p hr hs hy ht)

def split500Sound : PhaseSourceSound where
  source := sourceSplit500
  potential := split500Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 21000 691 155 p j).trans
      (split500_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 21000 691 155 p j
      (split500_stageZero_gates p hr hs hy ht)

def split390Sound : PhaseSourceSound where
  source := sourceSplit390
  potential := split390Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 19500 539 120 p j).trans
      (split390_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 19500 539 120 p j
      (split390_stageZero_gates p hr hs hy ht)

/-! The initial A split is wider than A in the middle/slope coordinates, so
its two agreement maxima are handled explicitly rather than by source
dominance. -/

private theorem initialA_highY_highR_int (t y r : ℤ)
    (ht : y ≤ t) (hylo : 127 ≤ y) (hyhi : y ≤ 153)
    (hrlo : 28 ≤ r) (hrhi : r ≤ 33) :
    962072674248 * t * y + 4363686772482 * t * r +
        8933531975160000 * y * r ≤
      291199285900886 * t + 179347533724169920 * y +
        535310011405551430 * r + 50320 := by
  have hcT : 0 ≤ 291199285900886 - 962072674248 * y -
      4363686772482 * r := by omega
  have hpT : 0 ≤ (t - y) * (291199285900886 - 962072674248 * y -
      4363686772482 * r) := mul_nonneg (by omega) hcT
  have hcR : 0 ≤ 8937895661932482 * y - 535310011405551430 := by
    omega
  have hpR : 0 ≤ (33 - r) *
      (8937895661932482 * y - 535310011405551430) :=
    mul_nonneg (by omega) hcR
  have hpY : 0 ≤ 12 * (153 - y) *
      (80172722854 * y + 9621585079405087) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
  nlinarith

private theorem initialA_highY_lowR_int (t y r : ℤ)
    (ht : y ≤ t) (hylo : 127 ≤ y) (hyhi : y ≤ 153)
    (hrhi : r ≤ 27) :
    962072674248 * t * y + 4466765987580000 * y * r ≤
      169016056271390 * t + 54278086071929920 * y +
        535310011405551430 * r + 50320 := by
  have hcT : 0 ≤ 169016056271390 - 962072674248 * y := by omega
  have hpT : 0 ≤ (t - y) * (169016056271390 - 962072674248 * y) :=
    mul_nonneg (by omega) hcT
  have hcR : 0 ≤ 4466765987580000 * y - 535310011405551430 := by
    omega
  have hpR : 0 ≤ (27 - r) *
      (4466765987580000 * y - 535310011405551430) :=
    mul_nonneg (by omega) hcR
  have hpY : 0 ≤ 6 * (153 - y) *
      (160345445708 * y + 11050462775936439) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by positivity)
  nlinarith

private theorem initialA_lowY_highR_int (t y r : ℤ)
    (ht : y ≤ t) (hyr : r ≤ y) (hrlo : 28 ≤ r) (hrhi : r ≤ 33) :
    4363686772482 * t * r + 4466765987580000 * y * r +
        31969269017108570 * r ≤
      169016056271390 * t + 179347533724169920 * y + 50320 := by
  have hcT : 0 ≤ 169016056271390 - 4363686772482 * r := by omega
  have hpT : 0 ≤ (t - y) * (169016056271390 - 4363686772482 * r) :=
    mul_nonneg (by omega) hcT
  have hcY : 0 ≤ 179516549780441310 - 4471129674352482 * r := by
    omega
  have hpY : 0 ≤ (y - r) *
      (179516549780441310 - 4471129674352482 * r) :=
    mul_nonneg (by omega) hcY
  have hpR : 0 ≤ 2 * (33 - r) * (2235564837176241 * r - 754850417) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
  nlinarith

/- Keep the casts and the truncated predecessor `2 * r - 1` out of the main
   helper definition.  These three fixed branch lemmas elaborate much faster
   than normalizing that definition after all maxima have been split. -/
private theorem initialA_highY_highR_nat (t y r : ℕ)
    (ht : y ≤ t) (hylo : 127 ≤ y) (hyhi : y ≤ 153)
    (hrlo : 28 ≤ r) (hrhi : r ≤ 33) :
    131073 *
          ((1 + 262142 * y) * (r * 130000 + t * 28) +
            131071 * (2 * r - 1) * (y * 130000 + t * 127) +
            34078460001 * (y * 28 + r * 127)) +
        4063571713 * (y * 28 + r * 127) ≤
      (5743475809 * t + 6005121364168 * y + 21911127063412 * r) *
          50321 + 50320 := by
  have hi := initialA_highY_highR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hylo) (by exact_mod_cast hyhi)
    (by exact_mod_cast hrlo) (by exact_mod_cast hrhi)
  have hn :
      962072674248 * t * y + 4363686772482 * t * r +
          8933531975160000 * y * r ≤
        291199285900886 * t + 179347533724169920 * y +
          535310011405551430 * r + 50320 := by
    exact_mod_cast hi
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  nlinarith

private theorem initialA_highY_lowR_nat (t y r : ℕ)
    (ht : y ≤ t) (hylo : 127 ≤ y) (hyhi : y ≤ 153)
    (hrhi : r ≤ 27) (hrlo : 1 ≤ r) :
    131073 *
          ((1 + 262142 * y) * (r * 130000 + t * 28) +
            7208905 * (y * 130000 + t * 127) +
            34078460001 * (y * 28 + r * 127)) +
        4063571713 * (y * 28 + r * 127) ≤
      (5743475809 * t + 6005121364168 * y + 21911127063412 * r) *
          50321 + 50320 := by
  have hi := initialA_highY_lowR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hylo) (by exact_mod_cast hyhi)
    (by exact_mod_cast hrhi)
  have hn :
      962072674248 * t * y + 4466765987580000 * y * r ≤
        169016056271390 * t + 54278086071929920 * y +
          535310011405551430 * r + 50320 := by
    exact_mod_cast hi
  nlinarith

private theorem initialA_lowY_highR_nat (t y r : ℕ)
    (ht : y ≤ t) (hyr : r ≤ y) (hrlo : 28 ≤ r) (hrhi : r ≤ 33) :
    131073 *
          (33292035 * (r * 130000 + t * 28) +
            131071 * (2 * r - 1) * (y * 130000 + t * 127) +
            34078460001 * (y * 28 + r * 127)) +
        4063571713 * (y * 28 + r * 127) ≤
      (5743475809 * t + 6005121364168 * y + 21911127063412 * r) *
          50321 + 50320 := by
  have hi := initialA_lowY_highR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hyr)
    (by exact_mod_cast hrlo) (by exact_mod_cast hrhi)
  have hn :
      4363686772482 * t * r + 4466765987580000 * y * r +
          31969269017108570 * r ≤
        169016056271390 * t + 179347533724169920 * y + 50320 := by
    exact_mod_cast hi
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  nlinarith

theorem initialAHelperCap_le_potential (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 153) (ht : total p ≤ 5964) :
    (helperPair 130000 127 28 (middle p) p.all (total p)).regularCountCap ≤
      initialAPotential.eval p := by
  have haz : 262142 * total p + 1 ≤ 34078460001 := by omega
  have hry : p.all ≤ middle p := by simp [middle]
  have hyt : middle p ≤ total p := by simp [middle, total]
  simp only [helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, initialAPotential]
  rw [max_eq_right haz]
  by_cases hay : 33292035 ≤ 1 + 262142 * middle p
  · rw [max_eq_left hay]
    by_cases har : 7208905 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hrlo : 28 ≤ p.all := by omega
      have hylo : 127 ≤ middle p := by omega
      exact initialA_highY_highR_nat (total p) (middle p) p.all hyt hylo hy
        hrlo hs
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hylo : 127 ≤ middle p := by omega
      have hr27 : p.all ≤ 27 := by omega
      exact initialA_highY_lowR_nat (total p) (middle p) p.all hyt hylo hy
        hr27 hr
  · rw [max_eq_right (Nat.le_of_not_ge hay)]
    by_cases har : 7208905 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hrlo : 28 ≤ p.all := by omega
      exact initialA_lowY_highR_nat (total p) (middle p) p.all hyt hry hrlo hs
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      ring_nf
      omega

end ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound
end PackedLocator_LocatorPhase6800SourceSound

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Kernels. -/
section PackedLocator_LocatorPhase6800Kernels

/-!
# Concrete kernel realizations and four-phase chain

The analytic source records are paired here with their actual constraint
kernels and isolated finrank receipts.  The final theorem composes the four
state-local transitions while leaving only the compact receipt's cap
equations and defect inequalities as hypotheses.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Kernels

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorBatchPhase6800 LocatorPhase6800Oracle
  LocatorPhase6800SourceSound

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def r1200Kernel (u0 u1 : I → K) :
    PhaseKernelRealization r1200Sound u0 u1 where
  D := 217670400
  m := 1200
  weighted := LocatorR1200Source.weighted_exact.symm
  shape := by
    simpa only [r1200Sound, sourceR1200] using LocatorR1200Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      217670400 82100 370 1200 19825077939631510 u0 u1 (by
        rw [LocatorR1200Source.nullity_exact])

def sourceCKernel (u0 u1 : I → K) :
    PhaseKernelRealization sourceCSound u0 u1 where
  D := 48975840
  m := 270
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      48975840 130000 81 270 321495185604514 u0 u1 (by
        rw [LocatorArithmetic.kernelC_nullity])

def split500Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split500Sound u0 u1 where
  D := 90696000
  m := 500
  weighted := LocatorSplit500Source.weighted_exact.symm
  shape := by
    simpa only [split500Sound, sourceSplit500] using
      LocatorSplit500Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      90696000 21000 155 500 230574129441305 u0 u1 (by
        rw [LocatorSplit500Source.nullity_exact])

def split390Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split390Sound u0 u1 where
  D := 70742880
  m := 390
  weighted := LocatorSplit390Source.weighted_exact.symm
  shape := by
    simpa only [split390Sound, sourceSplit390] using
      LocatorSplit390Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      70742880 19500 120 390 103687669979190 u0 u1 (by
        rw [LocatorSplit390Source.nullity_exact])

/-- Concrete composition of the four fresh-source phases. -/
theorem stateLocalRegularBoundOn_fourPhases
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (baseCap rCap cCap f500Cap s390Cap : FlagDegree → ℕ)
    (rDefect cDefect f500Defect s390Defect : FlagDegree → ℕ)
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap)
    (hrDefect : PhaseDefectSound baseCap sourceR1200
      r1200Potential rDefect)
    (hrCap : PhaseCapEquation baseCap rCap sourceR1200
      r1200Potential rDefect)
    (hcDefect : PhaseDefectSound rCap sourceC
      sourceCPotential cDefect)
    (hcCap : PhaseCapEquation rCap cCap sourceC
      sourceCPotential cDefect)
    (hfDefect : PhaseDefectSound cCap sourceSplit500
      split500Potential f500Defect)
    (hfCap : PhaseCapEquation cCap f500Cap sourceSplit500
      split500Potential f500Defect)
    (hsDefect : PhaseDefectSound f500Cap sourceSplit390
      split390Potential s390Defect)
    (hsCap : PhaseCapEquation f500Cap s390Cap sourceSplit390
      split390Potential s390Defect) :
    StateLocalRegularBoundOn H selected Gamma ambient s390Cap := by
  have h0 : StateLocalRegularBoundOn H selected Gamma ambient baseCap :=
    stateLocalRegularBoundOn_of_base H selected Gamma ambient
      baseCap hown hbase
  have hR : StateLocalRegularBoundOn H selected Gamma ambient rCap :=
    stateLocalRegularBoundOn_onePhase
      (sound := r1200Sound) (u0 := u0) (u1 := u1)
      (kernel := r1200Kernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := baseCap)
      (nextCap := rCap) (defect := rDefect) (hprevious := h0)
      (hdefect := by simpa only [r1200Sound] using hrDefect)
      (hcap := by simpa only [r1200Sound] using hrCap)
  have hC : StateLocalRegularBoundOn H selected Gamma ambient cCap :=
    stateLocalRegularBoundOn_onePhase
      (sound := sourceCSound) (u0 := u0) (u1 := u1)
      (kernel := sourceCKernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := rCap)
      (nextCap := cCap) (defect := cDefect) (hprevious := hR)
      (hdefect := by simpa only [sourceCSound] using hcDefect)
      (hcap := by simpa only [sourceCSound] using hcCap)
  have hF : StateLocalRegularBoundOn H selected Gamma ambient f500Cap :=
    stateLocalRegularBoundOn_onePhase
      (sound := split500Sound) (u0 := u0) (u1 := u1)
      (kernel := split500Kernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := cCap)
      (nextCap := f500Cap) (defect := f500Defect) (hprevious := hC)
      (hdefect := by simpa only [split500Sound] using hfDefect)
      (hcap := by simpa only [split500Sound] using hfCap)
  exact stateLocalRegularBoundOn_onePhase
    (sound := split390Sound) (u0 := u0) (u1 := u1)
    (kernel := split390Kernel u0 u1) (H := H) (selected := selected)
    (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
    (hagreement := hagreement) (hno := hno) (previousCap := f500Cap)
    (nextCap := s390Cap) (defect := s390Defect) (hprevious := hF)
    (hdefect := by simpa only [split390Sound] using hsDefect)
    (hcap := by simpa only [split390Sound] using hsCap)

end

end ProximityPrize.SubmissionLower.LocatorPhase6800Kernels
end PackedLocator_LocatorPhase6800Kernels

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedStage. -/
section PackedLocator_LocatorFixedStage
namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80752
def agreements:ℕ:=181392
def gap:ℕ:=50321
def prime:ℕ:=2130706433
def weightedCap:ℕ:=16688064
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
    identityCurveDegree flag a b s w=
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
def identitySlackZ (b s:ℕ):ℕ:=
  6212162461750991 + 6916118343057408 * b + 11057568778490432 * s +
    3458059171528704 * s ^ 2 + 6916118343057408 * b * s
def identitySlackYZ (a b s:ℕ):ℕ:=
  2050121026118780 + 6916118343057408 * a + 6916118343057408 * b +
    8282874488068958 * s + 3458059171528704 * s ^ 2 +
    6916118343057408 * a * s + 6916118343057408 * b * s
def identitySlackAll (a b s:ℕ):ℕ:=
  2733491120997483 + 11057568778490432 * a + 8282874488068958 * b +
    3458059171528704 * b ^ 2 + 8282874488068958 * s +
    3458059171528704 * s ^ 2 + 6916118343057408 * a * b +
    6916118343057408 * a * s + 6916118343057408 * b * s
def identitySlack (flag:FlagDegree) (a b s:ℕ):ℕ:=
  flag.zOnly * identitySlackZ b s + flag.yz * identitySlackYZ a b s +
    flag.all * identitySlackAll a b s
theorem identity_budget_exact (flag:FlagDegree) (a b s:ℕ) :
    gap * flagMixed flag (firstTail a b s) (secondTail a b s) =
      (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
        identitySlack flag a b s:=by
  rw [identityDegree_linear]
  norm_num [firstTail,secondTail,tail_support_formula,w,n,errors,gap,
    identitySlack,identitySlackZ,identitySlackYZ,identitySlackAll,flagMixed] <;>
    ring
theorem identity_budget (flag:FlagDegree) (a b s:ℕ) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
theorem tangent_gate (a b s:ℕ) :
    errors + 1 ≤ (secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
    have h:=Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 28) (hY:b + s + 3 ≤ 127) (hT:a + b + s + 3 ≤ 5964)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 28) (hY:b + s + 3 ≤ 127)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 252:=by omega
  have hs:2 * (s + 2) - 1 ≤ 55:=by omega
  have hfS:flag.all ≤ 28:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 127:=hfy.trans hY
  calc
    _ ≤ (1 + w * 252) * 28 + 127 * (55 * w) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _ < prime:=by norm_num [w,prime]
theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 28) (hY:b + s + 3 ≤ 127)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 252:=by omega
  have hs:2 * (s + 2) - 2 ≤ 54:=by omega
  have hfS:flag.all ≤ 28:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 127:=hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 252) * 28 + 127 * (54 * (w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
    _ < prime:=by norm_num [w,prime]
def FixedStageBound (D a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements + errors →
    (∀ gamma ∈ Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (D a b s:ℕ)
    (hDlow:w + 1 ≤ D) (hDhigh:D ≤ weightedCap)
    (hS:s + 2 ≤ 28) (hY:b + s + 3 ≤ 127) (hT:a + b + s + 3 ≤ 5964) :
    FixedStageBound D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D < prime:=hDhigh.trans_lt (by norm_num [weightedCap,prime])
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider:=actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
      apply identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes] <;> norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card * gap=Gamma.card * (agreements - w):=rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            identityCurveDegree flag a b s w:=hinc
        _= (n - w) * (errors + 1) * identityCurveDegree flag a b s w:=by
          rw [hnodes] <;> norm_num [n,agreements,errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          identity_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some
end
end ProximityPrize.SubmissionLower.LocatorFixedStage
end PackedLocator_LocatorFixedStage

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixed. -/
section PackedLocator_LocatorFixed
namespace ProximityPrize.SubmissionLower.LocatorFixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def padA (p:FlagDegree):ℕ:=padT p - padY p
def padB (p:FlagDegree):ℕ:=padY p - padS p - 1
def padSlope (p:FlagDegree):ℕ:=padS p - 2
theorem pad_sums (p:FlagDegree) :
    padSlope p + 2=padS p ∧
    padB p + padSlope p + 3=padY p ∧
    padA p + padB p + padSlope p + 3=padT p:=by
  have hs:2 ≤ padS p:=le_max_right _ _
  have hy:padS p + 1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  dsimp [padA,padB,padSlope]
  omega
theorem padded_tail_eq (p:FlagDegree) (d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support (padA p) (padB p) (padSlope p)) d=
      paddedTail p d:=by
  have hc:=pad_sums p
  have hs:2 ≤ padS p:=le_max_right _ _
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,
    RCN198.support,hc.1,hc.2.1,hc.2.2,paddedTail]
  have he:2 * padS p - 2=2 * (padS p - 1):=by omega
  rw [he]
theorem own_support (F:P4) :
    ResidualSupportData
      (RCN198.support (padA (originalCumulativeFlag F))
        (padB (originalCumulativeFlag F)) (padSlope (originalCumulativeFlag F))) F:=by
  have hc:=originalCumulativeFlag_cumulative F
  have hp:=pad_sums (originalCumulativeFlag F)
  refine ⟨?_, ?_, ?_⟩
  · change wt residualSWeights F ≤ padSlope (originalCumulativeFlag F) + 2
    rw [hp.1, ← hc.1]
    exact le_max_left _ _
  · change wt residualYSWeights F ≤
      padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
    rw [hp.2.1, ← hc.2.1]
    exact le_max_left _ _
  · change wt residualTotalWeights F ≤ padA (originalCumulativeFlag F) +
      padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
    rw [hp.2.2, ← hc.2.2]
    exact le_max_left _ _
theorem own_box (F:P4) (D w L s:ℕ)
    (hbox:F ∈ RCN174.globalCoefficientBox K D w L s) :
    F ∈ RCN174.globalCoefficientBox K D w
      (padA (originalCumulativeFlag F) + padB (originalCumulativeFlag F) +
        padSlope (originalCumulativeFlag F) + 3)
      (padSlope (originalCumulativeFlag F) + 2):=by
  have hs:=(own_support F).s_weight
  have ht:=(own_support F).total_weight
  intro d hd
  have hds:=(MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
  have hdt:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
  rw [weight_fin4] at hds hdt
  simp only [residualSWeights,residualTotalWeights,RCN198.support,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at hds hdt
  exact ⟨by omega,hds, (hbox hd).2.2⟩
theorem factor_support {P:ResidualSupportParameters} (Q:P4) (hQ:Q ≠ 0)
    (HQ:ResidualSupportData P Q) (R:RegularIndex Q) :
    ResidualSupportData P R.1:=by
  have hd:=(RCN167.positiveRFactors_spec Q R.1 R.2).2.1
  exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩
theorem own_parameter_caps (p:FlagDegree)
    (hs:p.all ≤ 28) (hy:middle p ≤ 127) (ht:total p ≤ 5964) :
    padSlope p + 2 ≤ 28 ∧ padB p + padSlope p + 3 ≤ 127 ∧
      padA p + padB p + padSlope p + 3 ≤ 5964:=by
  have hp:=pad_sums p
  have hps:padS p ≤ 28:=max_le hs (by decide)
  have hpy:padY p ≤ 127:=max_le hy (by omega)
  have hpt:padT p ≤ 5964:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem regular_factor_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:P.s ≤ 28) (hY:P.ys ≤ 127) (hT:P.total ≤ 5964)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (R:RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R):=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  let p:=regularCumulativeFlag Q R
  let a:=padA p
  let b:=padB p
  let s:=padSlope p
  have hRdata:=directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < 2130706433:=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox:=own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:=own_support R.1
  have hRwhole:=factor_support Q hQ HQ R
  have hc:=originalCumulativeFlag_cumulative R.1
  have hparam:s + 2 ≤ 28 ∧ b + s + 3 ≤ 127 ∧ a + b + s + 3 ≤ 5964:=by
    apply own_parameter_caps p
    · exact hRwhole.s_weight.trans hS
    · simpa only [p,middle,regularCumulativeFlag,hc.2.1] using
        hRwhole.ys_weight.trans hY
    · simpa only [p,total,regularCumulativeFlag,hc.2.2] using
        hRwhole.total_weight.trans hT
  have hsolutions:∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073):=by
    let S0:=regularGeometricResidualStageOfSupport (RCN198.support a b s) Q selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S:=reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub:geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
    have hnodes:S.nodes.card=181392 + 80752:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181392 ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,S0,ResidualStage.agreementFiber,ResidualStage.Agrees,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf:=geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount:=LocatorFixedStage.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [LocatorFixedStage.firstTail,LocatorFixedStage.secondTail,
      LocatorFixedStage.w,Nat.reduceAdd,geometricCumulativeFlag,
      a,b,s,padded_tail_eq] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073):=Finset.sum_le_sum (fun g _=> hstage g)
    _ ≤ paddedCost 131072 131073 p:=by
      have hb:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2
def regularCost (T YS S:ℕ):ℕ:=
  paddedCost 131072 131073 (cap T YS S)
theorem regular_sum_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:P.s ≤ 28) (hY:P.ys ≤ 127) (hT:P.total ≤ 5964)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752) :
    (∑ R:RegularIndex Q, (regularSeeds Q selected Gamma R).card) ≤
      regularCost P.total P.ys P.s:=by
  have hb:=regularCumulativeFlag_budgets Q hQ HQ
  have hc:=cap_cumulative P.total P.ys P.s P.s_le_ys P.ys_le_total
  have hcost:=merge_padded_costs 131072 131073 (regularCumulativeFlag Q)
    (cap P.total P.ys P.s)
    (by simpa only [hc.1] using hb.1)
    (by rw [hc.2.1]; simpa only [middle] using hb.2.1)
    (by rw [hc.2.2]; simpa only [total] using hb.2.2)
  exact (Finset.sum_le_sum (fun R _=>
    regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R)).trans hcost
def profile (D T S:ℕ):RCN276.Profile:=
  ⟨262144,131071,181392,D,T,S⟩
def singularProfile (D T S:ℕ):RCN318.TightParameters:=
  ⟨262144,131071,181392,D,T,S⟩
def equationCost (D T YS S:ℕ):ℕ:=
  regularCost T YS S + CommonShearTightPrototype.countCap (singularProfile D T S)
structure SingularGates (P:RCN318.TightParameters):Prop where
  s_pos:1 ≤ P.s
  s_small:P.s < 2130706433
  w_pos:1 ≤ P.w
  w_small:P.w < 2130706433
  kD:P.w < P.kappa * P.D
  algebraic_pos:1 ≤ P.algebraicCap
  implicit_small:P.implicitYCap < 2130706433
  algebraic_small:P.algebraicCap < 2130706433
  wa:P.w < P.a
  an:P.a ≤ P.n
theorem singular_gates (D T S:ℕ)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hTpos:1 ≤ T) (hT:T ≤ 5964)
    (hSpos:1 ≤ S) (hS:S ≤ 28) :
    SingularGates (singularProfile D T S):=by
  have hkpos:1 ≤ 2*S-1:=by omega
  have hk:2*S-1 ≤ 55:=by omega
  have hDle:D ≤ (2*S-1)*D:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right D hkpos
  have hnum:(2*S-1)*D-1 ≤ 917843519:=by
    have hp:=Nat.mul_le_mul hk hDhigh
    norm_num at hp
    omega
  have hiy:((2*S-1)*D-1)/131071 ≤ 7002:=
    (Nat.div_le_div_right hnum).trans (by decide)
  have halgpos:1 ≤ (2*S-1)*T:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hkpos hTpos
  have halg:(2*S-1)*T ≤ 328020:=by
    have hp:=Nat.mul_le_mul hk hT
    norm_num at hp
    exact hp
  refine ⟨hSpos, ?_,by change 1 ≤ 131071; decide,
    by change 131071 < 2130706433; decide, ?_,halgpos, ?_, ?_,
    by change 131071 < 181392; decide,by change 181392 ≤ 262144; decide⟩
  · exact hS.trans_lt (by decide)
  · change 131071 < (2*S-1)*D
    omega
  · exact hiy.trans_lt (by decide)
  · exact halg.trans_lt (by decide)
theorem fixed_count_le
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:P.s ≤ 28) (hY:P.ys ≤ 127) (hT:P.total ≤ 5964)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma Q=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752) :
    Gamma.card ≤ equationCost D P.total P.ys P.s:=by
  have hg:=singular_gates D P.total P.s hDlow hDhigh
    (P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)) hT P.one_le_s hS
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (profile D P.total P.s) Q hQ hbox hg.s_pos hg.s_small hg.w_pos hg.kD
    hg.algebraic_pos hg.algebraic_small selected Gamma hsolution
  have hreg:=regular_sum_count D P hDlow hDhigh hS hY hT
    Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno
  have hsing:=CommonShearTightPrototype.singularSeeds_count_le_countCap
    (singularProfile D P.total P.s) Q hQ hbox
    hg.s_pos hg.s_small hg.w_pos hg.w_small hg.kD hg.algebraic_pos
    hg.implicit_small hg.algebraic_small hg.wa hg.an
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18)) =262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [singularProfile,RCN318.TightParameters.errors,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hreg hsing)
end
end ProximityPrize.SubmissionLower.LocatorFixed
end PackedLocator_LocatorFixed

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridIdentity. -/
section PackedLocator_LocatorHybridIdentity

/-!
# The identity branch is dominated by the hybrid cost

On the hybrid branch (`padB ≥ 1`) the identity-curve count
`(n - w) * (errors + 1) * identityCurveDegree flag a b s w / gap` is at most the
hybrid Bezout bound.  This is an exact polynomial identity with a
subtraction-free slack, in the style of `LocatorFixedStage.identity_budget_exact`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridIdentity

open RCN095 RCN146 LocatorFactorAggregate LocatorHybridCost LocatorFixedStage RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Subtraction-free tails in the support coordinates `a, b, s` with `b = b' + 1`. -/
def sharpABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 1) * 131072, (2 * s + 3) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def hybABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 65536, 196608⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩
def hybridCostABS (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (sharpABS a b s) (hybABS a b s) +
    131072 * flagMixed flag (mfibABS a b s) (mcutABS a b s)

theorem tails_eq (p : FlagDegree) :
    sharpTail p = sharpABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    hybridCoordinate p = hybABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingFiber p = mfibABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingCut p = mcutABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := pad_bounds p
  generalize hS : padS p = sP at h ⊢
  generalize hY : padY p = yP at h ⊢
  generalize hT : padT p = tP at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : 2 * (yP - sP) - 1 = 2 * (yP - sP - 1) + 1 := by omega
    have e2 : 2 * sP - 1 = 2 * (sP - 2) + 3 := by omega
    simp only [sharpTail, sharpABS, hS, hY, hT, e1, e2]
  · simp only [hybridCoordinate, rationalFlag, hybABS, rationalABS, hS, hY, hT]
  · have e1 : yP - sP = yP - sP - 1 + 1 := by omega
    have e2 : sP + 1 = sP - 2 + 3 := by omega
    simp only [movingFiber, mfibABS, hS, hY, hT, FlagDegree.mk.injEq]
    exact ⟨trivial, e1, e2⟩
  · simp only [movingCut, rationalFlag, mcutABS, rationalABS, hS, hY, hT]

theorem hybridCost_eq_abs (p : FlagDegree) (flag : FlagDegree) :
    flagMixed flag (sharpTail p) (hybridCoordinate p) +
        131072 * flagMixed flag (movingFiber p) (movingCut p) =
      hybridCostABS flag (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := tails_eq p
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  rfl

/-- Slack polynomials for `errors = 80752` (`b = b' + 1`). -/
def hybridSlackZ (a b s : ℕ) : ℕ :=
  21341336229092192 + 15380268060709440 * s + 9509728678445056 * b +
    2593564165668864 * s ^ 2 + 5187128331337728 * b * s
def hybridSlackYZ (a b s : ℕ) : ℕ :=
  17179294793459981 + 12605573770287966 * s + 9509728678445056 * b + 9509728678445056 * a +
    2593564165668864 * s ^ 2 + 5187128331337728 * b * s + 5187128331337728 * a * s
def hybridSlackAll (a b s : ℕ) : ℕ :=
  16203652236582857 + 12605573770287966 * s + 12605573770287966 * b + 15380268060709440 * a +
    2593564165668864 * s ^ 2 + 5187128331337728 * b * s + 2593564165668864 * b ^ 2 +
    5187128331337728 * a * s + 5187128331337728 * a * b
def hybridSlack (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * hybridSlackZ a b s + flag.yz * hybridSlackYZ a b s +
    flag.all * hybridSlackAll a b s

theorem hybrid_identity_exact (flag : FlagDegree) (a b s : ℕ) :
    gap * hybridCostABS flag a (b + 1) s =
      (n - w) * (errors + 1) * identityCurveDegree flag a (b + 1) s w +
        hybridSlack flag a b s := by
  rw [identityDegree_linear]
  norm_num [hybridCostABS, sharpABS, hybABS, rationalABS, mfibABS, mcutABS, w, n, errors, gap,
    hybridSlack, hybridSlackZ, hybridSlackYZ, hybridSlackAll, flagMixed,
    add_zOnly, add_yz, add_all]
  ring

theorem identity_le_hybrid (flag : FlagDegree) (a b s : ℕ) (hb : 1 ≤ b) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * hybridCostABS flag a b s := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [hybrid_identity_exact]
  exact Nat.le_add_right _ _

end ProximityPrize.SubmissionLower.LocatorHybridIdentity
end PackedLocator_LocatorHybridIdentity

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCells. -/
section PackedLocator_LocatorHybridCells
/-
LOCATOR HYBRID CELLS (port of ContactRouterCellCosts6750Research + the pure
flag arithmetic of ContactHybridTailProvider6751Research §1 from pr359).

Cells are parameterised by (t y r) with the atoms
  a = cellA t y = t - y,  b = cellB y r = y - r - 1,  s = cellS r = r - 2,
so that (for 2 ≤ r < y ≤ t) t = a+b+s+3, y = b+s+3, r = s+2 and the stage
support is `support a b s`.  `w` is the Locator's `RCN327.w = 131071`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Cell atoms and flags -/

def cellA (t y : Nat) : Nat := t - y
def cellB (y r : Nat) : Nat := y - r - 1
def cellS (r : Nat) : Nat := r - 2

def cellSupport (t y r : Nat) : ResidualSupportParameters :=
  support (cellA t y) (cellB y r) (cellS r)

def cellFixedFlag (t y r : Nat) : FlagDegree :=
  surfaceFlag (cellA t y) (cellB y r) (cellS r)

def cellFirstTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellSharpTail (t y r : Nat) : FlagDegree :=
  sharpResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellSecondTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 2)

def cellDirection (t y r : Nat) : FlagDegree :=
  RCN206.directionFlag (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r : Nat) : FlagDegree :=
  ⟨(w + 1) * cellA t y + (cellDirection t y r).zOnly,
    (w + 1) * cellB y r + (cellDirection t y r).yz + 1,
    (w + 1) * cellS r + (cellDirection t y r).all⟩

def cellHybridCoordinate (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, (w + 1) / 2, 3 * ((w + 1) / 2)⟩

def cellMovingFiber (t y r : Nat) : FlagDegree :=
  RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r)

def cellMovingCut (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, w + 1, 2 * (w + 1)⟩

def cellHybridCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellSharpTail t y r)
      (cellHybridCoordinate t y r) +
    (w + 1) * flagMixed (cellFixedFlag t y r) (cellMovingFiber t y r)
      (cellMovingCut t y r)

def cellDelayedCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellFirstTail t y r)
    (cellSecondTail t y r)

def cellRegularCost (t y r : Nat) : Nat :=
  if r + 2 ≤ y then cellHybridCost t y r else cellDelayedCost t y r

def cellTail1 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellSharpTail t y r else cellFirstTail t y r

def cellTail2 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellHybridCoordinate t y r else cellSecondTail t y r

def cellCostOf (f : FlagDegree) (t y r : Nat) : Nat :=
  if r + 2 ≤ y then
    flagMixed f (cellSharpTail t y r) (cellHybridCoordinate t y r) +
      (w + 1) * flagMixed f (cellMovingFiber t y r) (cellMovingCut t y r)
  else flagMixed f (cellFirstTail t y r) (cellSecondTail t y r)

theorem cellRegularCost_eq_cellCostOf (t y r : Nat) :
    cellRegularCost t y r = cellCostOf (cellFixedFlag t y r) t y r := by
  unfold cellRegularCost cellCostOf cellHybridCost cellDelayedCost
  split_ifs <;> rfl

theorem sum_cellCostOf_le_of_cumulative {J : Type*} [Fintype J]
    (f : J → FlagDegree) (p : FlagDegree) (t y r : Nat)
    (hs : (∑ i, (f i).all) ≤ p.all)
    (hm : (∑ i, ((f i).yz + (f i).all)) ≤ p.yz + p.all)
    (ht : (∑ i, ((f i).zOnly + (f i).yz + (f i).all)) ≤
      p.zOnly + p.yz + p.all) :
    (∑ i, cellCostOf (f i) t y r) ≤ cellCostOf p t y r := by
  unfold cellCostOf
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht)
      (Nat.mul_le_mul_left _
        (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht))
  · exact sum_flagMixed_le_of_cumulative f p _ _ hs hm ht

/-! ### Pure flag arithmetic (pr359 §1)

All lemmas are subtraction-free: they are stated over the cell atoms
a = cellA t y, b = cellB y r, s = cellS r. -/

/-- z-cumulative absorption: sharp.all ≤ (mult • hybrid).all.
    sharp.all = (2s+3)·d with d = (w+1)+delay; hybrid.all = (w+1)s+(2s+3)+3((w+1)/2). -/
theorem sharp_absorbs_all (_a _b s delay mult : ℕ)
    (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    (2 * s + 3) * (131072 + delay) ≤
      mult * (131072 * s + (2 * s + 3) + 196608) := by
  calc
    (2 * s + 3) * (131072 + delay) ≤ (2 * s + 3) * (131072 + mult) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (65536 * (2 * s + 3)) + mult * (2 * s + 3) := by ring
    _ ≤ mult * (65536 * (2 * s + 3)) + mult * (2 * s + 3) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hm2) _
    _ = mult * (131072 * s + (2 * s + 3) + 196608) := by ring

/-- yz-cumulative absorption:
    sharp.(yz+all) = 1+(2(b+s)+4)·d; hybrid.(yz+all) = 131072(b+s)+2(b+s)+5+262144. -/
theorem sharp_absorbs_ysall (_a b s delay mult : ℕ)
    (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    1 + (2 * (b + s) + 4) * (131072 + delay) ≤
      mult * (131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
  have h1 : 1 + (2 * (b + s) + 4) * (131072 + delay) ≤
      1 + (2 * (b + s) + 4) * (131072 + mult) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have h2 : 2 * (65536 * (2 * (b + s) + 4)) ≤
      mult * (65536 * (2 * (b + s) + 4)) :=
    Nat.mul_le_mul_right _ hm2
  have hm1 : 1 ≤ mult := by omega
  calc
    1 + (2 * (b + s) + 4) * (131072 + delay) ≤
        1 + (2 * (b + s) + 4) * (131072 + mult) := h1
    _ = 1 + 2 * (65536 * (2 * (b + s) + 4)) + mult * (2 * (b + s) + 4) := by
      ring
    _ ≤ 1 + mult * (65536 * (2 * (b + s) + 4)) + mult * (2 * (b + s) + 4) :=
      Nat.add_le_add_right (Nat.add_le_add_left h2 _) _
    _ = mult * (131072 * (b + s) + 2 * (b + s) + 4 + 262144) + 1 := by ring
    _ ≤ mult * (131072 * (b + s) + 2 * (b + s) + 4 + 262144) + mult :=
      Nat.add_le_add_left (by omega : (1:ℕ) ≤ mult) _
    _ = mult * (131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by ring

/-- total-cumulative absorption: adds the z-column 131074·a on the hybrid side
    against 2a·d on the sharp side. -/
theorem sharp_absorbs_total (a b s delay mult : ℕ)
    (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
  have h1 : 1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
      1 + (2 * a + 2 * (b + s) + 4) * (131072 + mult) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have h2 : 2 * (65536 * (2 * a + 2 * (b + s) + 4)) ≤
      mult * (65536 * (2 * a + 2 * (b + s) + 4)) :=
    Nat.mul_le_mul_right _ hm2
  calc
    1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
        1 + (2 * a + 2 * (b + s) + 4) * (131072 + mult) := h1
    _ = 1 + 2 * (65536 * (2 * a + 2 * (b + s) + 4)) +
        mult * (2 * a + 2 * (b + s) + 4) := by ring
    _ ≤ 1 + mult * (65536 * (2 * a + 2 * (b + s) + 4)) +
        mult * (2 * a + 2 * (b + s) + 4) :=
      Nat.add_le_add_right (Nat.add_le_add_left h2 _) _
    _ = mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 4 + 262144) +
        1 := by ring
    _ ≤ mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 4 + 262144) +
        mult := Nat.add_le_add_left (by omega : (1:ℕ) ≤ mult) _
    _ = mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
      ring

/-- center + (w+1) • ⟨a,b,s⟩ = cellRational (as flags), the identity that folds the
    moving engine's k·wc(⟨a,b,s⟩) term into the rational weightedCost. -/
theorem center_add_smul_eq_cellRational (t y r : Nat) :
    center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) =
      cellRational t y r := by
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  simp only [center, direction, unitYZFlag, cellDirection,
    RCN206.directionFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  congr 1 <;> ring

theorem flag_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g; simp_all

/-- cellMovingCut = center + (w+1) • surfaceFlag — the flag under which
    exists_firstTail_cut_budgets bounds the movingCost sum. -/
theorem cellMovingCut_eq_center_add (t y r : Nat) :
    cellMovingCut t y r =
      center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • RCN206.surfaceFlag (cellA t y) (cellB y r) (cellS r) := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
      cellDirection, RCN206.directionFlag, RCN206.surfaceFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

/-- rational ≤ hybrid coordinate-wise (hybrid = rational + ⟨0,(w+1)/2,3((w+1)/2)⟩). -/
theorem cellRational_le_hybrid (t y r : Nat) :
    (cellRational t y r).zOnly ≤ (cellHybridCoordinate t y r).zOnly ∧
    (cellRational t y r).yz ≤ (cellHybridCoordinate t y r).yz ∧
    (cellRational t y r).all ≤ (cellHybridCoordinate t y r).all := by
  simp only [cellHybridCoordinate, add_zOnly, add_yz, add_all]
  omega

/-- weightedCost is monotone under coordinate-wise flag dominance. -/
theorem weightedCost_mono
    {Omega : Type} [Field Omega]
    {G T H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
      surfaceFlag firstTailFlag)
    (C : RegularComponent Omega G T H)
    {f g : FlagDegree}
    (hz : f.zOnly ≤ g.zOnly) (hy : f.yz ≤ g.yz) (ha : f.all ≤ g.all) :
    B.weightedCost f C ≤ B.weightedCost g C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  gcongr

/-! ### Numeric gates for the cell coordinates -/

/-- The rational coordinate's yz-column in closed form. -/
theorem cellRational_yz (t y r : Nat) :
    (cellRational t y r).yz = 131074 * cellB y r + 2 := by
  simp only [cellRational, cellDirection, RCN206.directionFlag, w]
  omega

/-- The hybrid coordinate's yz-column in closed form. -/
theorem cellHybridCoordinate_yz (t y r : Nat) :
    (cellHybridCoordinate t y r).yz = 131074 * cellB y r + 65538 := by
  simp only [cellHybridCoordinate, add_yz, cellRational_yz, w]

/-- In the hybrid branch `r + 2 ≤ y` the atom `b = cellB y r` is positive, so any
    error cap below 131075 passes the rational gate. -/
theorem rationalGate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellRational t y r).yz := by
  rw [cellRational_yz]
  have hB : 1 ≤ cellB y r := by
    simp only [cellB]
    omega
  have := Nat.mul_le_mul_left 131074 hB
  omega

theorem tangentGate_of_rationalGate (t y r errorCap : Nat)
    (h : errorCap + 1 ≤ (cellRational t y r).yz) :
    errorCap + 1 ≤ (cellHybridCoordinate t y r).yz :=
  h.trans (cellRational_le_hybrid t y r).2.1

/-! ### Closed forms in the atoms (a, b, s) = (cellA t y, cellB y r, cellS r)

These match the subtraction-free shapes `sharpABS / rationalABS / hybABS /
mfibABS / mcutABS` used elsewhere in the Locator, so the hybrid bound can be
rewritten into that form by `hybridBound_eq`. -/

theorem cellSharpTail_eq (t y r : Nat) :
    cellSharpTail t y r =
      ⟨2 * cellA t y * 131072, 1 + (2 * cellB y r + 1) * 131072,
        (2 * cellS r + 3) * 131072⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellSharpTail, sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w] <;> omega

theorem cellRational_eq (t y r : Nat) :
    cellRational t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellRational, cellDirection, RCN206.directionFlag, w] <;> omega

theorem cellHybridCoordinate_eq (t y r : Nat) :
    cellHybridCoordinate t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 65536, 196608⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, w] <;> omega

theorem cellMovingFiber_eq (t y r : Nat) :
    cellMovingFiber t y r = ⟨cellA t y, cellB y r + 1, cellS r + 3⟩ := rfl

theorem cellMovingCut_eq (t y r : Nat) :
    cellMovingCut t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 131072, 262144⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellMovingCut, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, w] <;> omega

/-- The hybrid bound in closed (a, b, s)-form. -/
theorem hybridBound_eq (flag : FlagDegree) (t y r : Nat) :
    flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) =
      flagMixed flag
          ⟨2 * cellA t y * 131072, 1 + (2 * cellB y r + 1) * 131072,
            (2 * cellS r + 3) * 131072⟩
          (⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 65536, 196608⟩) +
        131072 * flagMixed flag ⟨cellA t y, cellB y r + 1, cellS r + 3⟩
          (⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 131072, 262144⟩) := by
  simp only [cellSharpTail_eq, cellHybridCoordinate_eq, cellMovingFiber_eq,
    cellMovingCut_eq, w]

end
end ProximityPrize.SubmissionLower.LocatorHybridCells
end PackedLocator_LocatorHybridCells

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProvider. -/
section PackedLocator_LocatorHybridTailProvider
/-
LOCATOR HYBRID TAIL PROVIDER (port of ContactHybridTailProvider6751Research, pr359).

Covers the `r + 2 ≤ y` ("hybrid second-surface") branch of `cellRegularCost`.
The delayed branch keeps the Locator's reduced-tail discharge (Q2.lean) verbatim.

§0 defines the *bounded* provider `HybridTailMultiplicityProvider`: it is
pr359's refactored `DelayedTailMultiplicityProvider` (an extra
`divisorBound` optParam and a single field `cost_sum_le : ∑ cost ≤ divisorBound`
in place of `cost_le`/`divisor_le`), kept as a NEW structure so that the
existing B3.lean structure and its constructors (Q2.lean, GZ.lean) stay
untouched.  `stage_card_le_divisorBound` is the generalized
`stage_card_le_flagMixed`.

Conclusion shape of §3:

  Nonempty (HybridTailMultiplicityProvider
    (tailFlag1 := cellSharpTail t y r) (tailFlag2 := cellHybridCoordinate t y r) S
    (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r)
      + (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)))

Caller-side obligations (discharged in LocatorHybridTailRealization.lean):
  B            : sharp unit family (activeNestedUnitFamily on T1 in the sharp
                 flag DIRECTLY — no congruent-cut transport)
  budget/hcost/hmovingSum : outputs of exists_firstTail_cut_budgets
  hresultants  : sharp-family certificate (activeNestedWeightedCertificate on T1)
  htangent     : the tangent count vs B.yzCost
  htangentGate / hrationalGate : numeric gates errors+1 ≤ hybrid.yz / rational.yz
                 (rational.yz = 131074·b + 2 ≥ 131076 whenever b ≥ 1, i.e. r+2 ≤ y).
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ### 0. The bounded provider (pr359's refactored DelayedTailMultiplicityProvider) -/

section BoundedProvider
variable {K0 Omega Iota : Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi : Polynomial K0 →+* Omega} {Gamma0 : Finset K0} {x0 : Iota → K0}
  {pchar errorCap d : ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2 : FlagDegree}
  {support0 : RCN275.ResidualSupportParameters}

structure HybridTailMultiplicityProvider
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound : optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily : PrimeFlagBudgetFamily
    (G := S.G) (T := globalTailCut phi S.F (d + 1))
    (H := regularitySurface phi S.F) flag0 tailFlag1
  multiplicity : FirstTailComponent S → ℕ
  cost : FirstTailComponent S → ℕ
  one_le_multiplicity : ∀ C, 1 ≤ multiplicity C
  tangentYZGate : errorCap + 1 ≤ tailFlag2.yz
  cost_sum_le : (∑ C, cost C) ≤ divisorBound
  componentBound : ∀ C,
    (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
      (regularitySurface phi S.F) Gamma0
      (selectedPoint phi S.selected) C).card ≤ cost C
  dichotomy : ∀ C,
    (∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
      globalTailCut phi S.F (d + 1 + delay) ∉ C.1) ∨
    ((∀ delay, globalTailCut phi S.F (d + 1 + delay) ∈ C.1) ∧
      (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
        (regularitySurface phi S.F) Gamma0
        (selectedPoint phi S.selected) C).card ≤
          (errorCap + 1) * budgetFamily.yzCost C)

/-- The generalized `stage_card_le_flagMixed`: any bounded provider bounds the
seed count by its `divisorBound`. -/
theorem stage_card_le_divisorBound
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound : ℕ}
    (P : HybridTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S divisorBound) :
    Gamma0.card ≤ divisorBound := by
  classical
  let T1 := globalTailCut phi S.F (d + 1)
  let H := regularitySurface phi S.F
  let point := selectedPoint phi S.selected
  have hG : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G = 0 := S.on_component
  have hT1 : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    exact selectedPoint_evaluation phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover : Gamma0.card ≤
      ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card :=
    card_le_sum_componentSeeds Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card ≤ ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card := hcover
    _ ≤ ∑ C : RegularComponent Omega S.G T1 H, P.cost C :=
      Finset.sum_le_sum (fun C _ ↦ P.componentBound C)
    _ ≤ divisorBound := P.cost_sum_le

end BoundedProvider

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 1. L1 — the delayed cut lands in mult • hybrid (mult ≥ 2)

Direct containment (no mod-G reduction): the (w+1+delay)-th tail cut lies in the
sharp flag at degree w+1+delay, and the three cumulative absorptions of
LocatorHybridCells push that into `mult • cellHybridCoordinate` whenever
1 ≤ delay ≤ mult and 2 ≤ mult. -/

theorem laterTail_in_hybridFlag
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinate t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  -- globalTailCut is definitionally surfaceMap of the agreement numerator with
  -- the tail selector, so the sharp containment applies directly.
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  -- rewrite the sharp cumulative sums into the subtraction-free atom form
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  -- hybrid cumulative sums in atom form
  have hhallV : (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3) + 196608) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_all, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_yz, add_all, nsmul_yz, nsmul_all, w]
    norm_num
    ring
  have hhtotV : (mult • cellHybridCoordinate t y r).zOnly +
      (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, w]
    norm_num
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all (cellA t y) (cellB y r) (cellS r) delay mult hdm hm2)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)

/-! ### 2. L2 — the multiplicity-1 moving count

For a component whose (w+2)-cut is proper, the seeds are bounded by
wc(rational) + (w+1)·movingCost, via the filteredCut decomposition of the (w+2)
cut and the MovingPoleBudget zero bound at C := center, k := w+1. -/

set_option maxHeartbeats 20000000 in
theorem component_hybrid_moving_card_le
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y) (_hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + 1) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hR : S.F.degreeOf 2 ≤ cellS r + 2 := by
    have h := Hsupport.coordinate_bounds.2.1
    simpa only [cellSupport, cellS, RCN198.support] using h
  have hYR : wt ![0, 1, 1, 0] S.F ≤ cellB y r + cellS r + 3 := by
    have h := Hsupport.ys_weight
    simpa only [residualYSWeights, cellSupport, cellB, cellS, RCN198.support] using h
  have hAll : wt ![0, 1, 1, 1] S.F ≤ cellA t y + cellB y r + cellS r + 3 := by
    have h := Hsupport.total_weight
    simpa only [residualTotalWeights, cellSupport, cellA, cellB, cellS,
      RCN198.support] using h
  obtain ⟨Bc, cf, heq, hcoeff, hclass⟩ :=
    globalTailCut_certificate (polynomialEmbedding K)
      (cellA t y) (cellB y r) (cellS r) S.F hR hYR hAll
      (w + 1) (Nat.le_add_left 1 w)
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (w + 1) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (w + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (w + 1)
      (center (cellA t y) (cellB y r) (cellS r)) Bc cf hHnot hA hcoeff hclass
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (filteredCut (w + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F))) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + 1)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + 1)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

/-! ### 3. The hybrid provider from a local DVR family -/

theorem exists_hybridTailMultiplicityProvider_of_localDVR
    (t y r : Nat) (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag
      (cellSharpTail t y r))
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))
    (htangentGate : stageErrorCap + 1 ≤ (cellHybridCoordinate t y r).yz)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C)) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  have hry : r < y := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  -- weightedCost over budget = weightedCost over B (cost equalities)
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  -- the piecewise cost
  let cost : FirstTailComponent S → ℕ := fun C =>
    if 2 ≤ multiplicity C then
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C
    else
      B.weightedCost (cellRational t y r) C +
        (w + 1) * (budget C).movingCost
  -- pointwise: cost C ≤ mult C * wc(hybrid) + (w+1) * movingCost C
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C +
        (w + 1) * (budget C).movingCost := by
    intro C
    by_cases hm : 2 ≤ multiplicity C
    · simp only [cost, if_pos hm]
      exact Nat.le_add_right _ _
    · simp only [cost, if_neg hm]
      have hmono := weightedCost_mono B C
        (cellRational_le_hybrid t y r).1
        (cellRational_le_hybrid t y r).2.1
        (cellRational_le_hybrid t y r).2.2
      have h1 : B.weightedCost (cellRational t y r) C ≤
          multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C := by
        calc B.weightedCost (cellRational t y r) C ≤
            B.weightedCost (cellHybridCoordinate t y r) C := hmono
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      omega
  -- the component bound
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 2 ≤ multiplicity C
      · -- mult ≥ 2: cut with the delayed cut inside mult • hybrid
        have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F
                (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma w (w + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod C.1
            (multiplicity C • cellHybridCoordinate t y r)
            (globalTailCut (polynomialEmbedding K) S.F
              (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F
            (w + 1 + delay),
            laterTail_in_hybridFlag t y r hr2 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        have hscale : B.weightedCost
            (multiplicity C • cellHybridCoordinate t y r) C =
            multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C := by
          simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly,
            nsmul_yz, nsmul_all]
          ring
        simp only [cost, if_pos hm]
        rw [hscale] at hcount
        exact hcount
      · -- mult = 1: delay must be 1; use the moving engine
        have hm1 : multiplicity C = 1 := by
          have := hone C
          omega
        have hdelay1 : delay = 1 := by
          have h2 : delay ≤ 1 := by rw [← hm1]; exact hdelayMu
          omega
        subst hdelay1
        have hcount := component_hybrid_moving_card_le t y r hr2 hry hyt
          S C (budget C) (base C) htail
        simp only [cost, if_neg hm]
        simp only [hwcEq] at hcount
        -- fold wc(center) + (w+1)·wc(⟨a,b,s⟩) into wc(rational)
        have hfold : B.weightedCost
              (center (cellA t y) (cellB y r) (cellS r)) C +
            (w + 1) *
              (B.weightedCost
                (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) C +
                (budget C).movingCost) =
            B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := by
          have hid := center_add_smul_eq_cellRational t y r
          simp only [← hid, PrimeFlagBudgetFamily.weightedCost, add_zOnly,
            add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
          ring
        omega
    · -- tangent branch
      have hcount := htangent C htangentBranch
      by_cases hm : 2 ≤ multiplicity C
      · simp only [cost, if_pos hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinate t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinate t y r) C
              (stageErrorCap + 1) htangentGate
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      · simp only [cost, if_neg hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellRational t y r) C :=
            yzCost_mul_le_weightedCost B (cellRational t y r) C
              (stageErrorCap + 1) hrationalGate
          _ ≤ B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := Nat.le_add_right _ _
  -- the sum bound: certificate + moving sum
  have hsum : (∑ C, cost C) ≤
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    calc (∑ C, cost C) ≤
        ∑ C, (multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C +
          (w + 1) * (budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C, multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C) +
          (w + 1) * (∑ C, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ flagMixed flag (cellSharpTail t y r)
            (cellHybridCoordinate t y r) +
          (w + 1) *
            flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
        Nat.add_le_add
          (hresultants.divisor_le B multiplicity)
          (Nat.mul_le_mul_left _ hmovingSum)
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := cost
    one_le_multiplicity := hone
    tangentYZGate := htangentGate
    cost_sum_le := hsum
    componentBound := hbound
    dichotomy := providerDichotomy }⟩

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end PackedLocator_LocatorHybridTailProvider

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedHybrid. -/
section PackedLocator_LocatorFixedHybrid

/-!
# Hybrid second-surface bound for a regular factor

When the padded cumulative flag `p` of a regular factor satisfies
`2 ≤ p.all ∧ p.all + 2 ≤ middle p`, the factor's seeds are bounded by
`hybridCost p` instead of the padded two-tail cost.  The identity branch is
dominated through `identity_le_hybrid`; the proper-first-tail branch uses a
`HybridTailMultiplicityProvider` on the cell `(padT p, padY p, padS p)`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedHybrid
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open LocatorFactorAggregate LocatorHybridCost LocatorHybridIdentity LocatorHybridCells
  LocatorHybridTailProvider LocatorFixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem flagDegree_ext {f g:FlagDegree} (h1:f.zOnly=g.zOnly) (h2:f.yz=g.yz)
    (h3:f.all=g.all) : f=g:=by
  cases f; cases g
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  rfl

theorem cellSupport_eq (p:FlagDegree) :
    cellSupport (padT p) (padY p) (padS p)=
      RCN198.support (padA p) (padB p) (padSlope p):=rfl

theorem cellSupport_fields (p:FlagDegree) :
    (cellSupport (padT p) (padY p) (padS p)).s=padS p ∧
    (cellSupport (padT p) (padY p) (padS p)).ys=padY p ∧
    (cellSupport (padT p) (padY p) (padS p)).total=padT p:=by
  have h:=pad_sums p
  simp only [cellSupport_eq,RCN198.support]
  exact ⟨h.1,h.2.1,h.2.2⟩

theorem cell_tails_eq (p:FlagDegree) :
    cellSharpTail (padT p) (padY p) (padS p)=sharpTail p ∧
    cellHybridCoordinate (padT p) (padY p) (padS p)=hybridCoordinate p ∧
    cellMovingFiber (padT p) (padY p) (padS p)=movingFiber p ∧
    cellMovingCut (padT p) (padY p) (padS p)=movingCut p:=by
  have hf:=cellSupport_fields p
  have hb:=pad_bounds p
  refine ⟨?_,?_,?_,?_⟩
  · apply flagDegree_ext <;>
      simp only [cellSharpTail,sharpResidualAgreementFlag,sharpAgreementDirection,
        hf.1,hf.2.1,hf.2.2,sharpTail,RCN327.w,Nat.reduceAdd]
  · apply flagDegree_ext <;>
      simp only [cellHybridCoordinate,cellRational,cellDirection,RCN206.directionFlag,
        cellA,cellB,cellS,hybridCoordinate,rationalFlag,add_zOnly,add_yz,add_all,
        RCN327.w,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingFiber,RCN206.fiberFlag,cellA,cellB,cellS,movingFiber] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingCut,cellRational,cellDirection,RCN206.directionFlag,
        cellA,cellB,cellS,movingCut,rationalFlag,add_zOnly,add_yz,add_all,
        RCN327.w,Nat.reduceAdd,Nat.reduceMul] <;> omega

/-- The hybrid Bezout bound of a stage with flag `flag` on the padded cell of `p`. -/
def hybridBound (flag p:FlagDegree):ℕ:=
  flagMixed flag (sharpTail p) (hybridCoordinate p) +
    131072 * flagMixed flag (movingFiber p) (movingCut p)

theorem hybridBound_eq_abs (flag p:FlagDegree) :
    hybridBound flag p=hybridCostABS flag (padA p) (padB p) (padSlope p):=
  hybridCost_eq_abs p flag

/-- The proper-first-tail obligation: a hybrid provider on the cell of `p`. -/
def ProviderHyp (D:ℕ) (p:FlagDegree):Prop:=
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  ∀ {Gamma:Finset K} {flag:FlagDegree}
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80752 flag 131071 (cellSupport (padT p) (padY p) (padS p))),
    S.nodes.card=181392 + 80752 →
    (∀ gamma ∈ Gamma,181392 ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p) →
    (flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) →
    ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1) →
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1:=cellSharpTail (padT p) (padY p) (padS p))
      (tailFlag2:=cellHybridCoordinate (padT p) (padY p) (padS p)) S
      (flagMixed flag (cellSharpTail (padT p) (padY p) (padS p))
          (cellHybridCoordinate (padT p) (padY p) (padS p)) +
        (RCN327.w + 1) * flagMixed flag (cellMovingFiber (padT p) (padY p) (padS p))
          (cellMovingCut (padT p) (padY p) (padS p))))

/-- The realization: providers exist on every admissible hybrid cell. -/
def Realization (D:ℕ):Prop:=
  ∀ p:FlagDegree,padS p ≤ 28 → padY p ≤ 127 → padT p ≤ 5964 → padS p + 2 ≤ padY p →
    ProviderHyp D p

theorem hybridStageBound (D:ℕ) (p:FlagDegree)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:padS p ≤ 28) (hY:padY p ≤ 127) (hT:padT p ≤ 5964)
    (hhyb:padS p + 2 ≤ padY p)
    (hprov:ProviderHyp D p)
    {Gamma:Finset K} {flag:FlagDegree}
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80752 flag 131071 (cellSupport (padT p) (padY p) (padS p)))
    (hnodes:S.nodes.card=181392 + 80752)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤ (S.agreementFiber gamma).card)
    (hbox:S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p))
    (hflag:flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) :
    Gamma.card ≤ hybridBound flag p:=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  have hps:=pad_sums p
  have hS':padSlope p + 2 ≤ 28:=by omega
  have hY':padB p + padSlope p + 3 ≤ 127:=by omega
  have hT':padA p + padB p + padSlope p + 3 ≤ 5964:=by omega
  have hb1:1 ≤ padB p:=by omega
  have hDchar:D < 2130706433:=by omega
  have hflag':flag.all ≤ padSlope p + 2 ∧
      flag.yz + flag.all ≤ padB p + padSlope p + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ padA p + padB p + padSlope p + 3:=by
    refine ⟨?_,?_,?_⟩ <;> omega
  have hflagChar:=LocatorFixedStage.flag_characteristic (padA p) (padB p) (padSlope p)
    flag hS' hY' hT' hflag'
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (RCN327.w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (RCN327.w + 1) S.G).mp hTail
    have hbox':S.F ∈ RCN174.globalCoefficientBox K D 131071
        (padA p + padB p + padSlope p + 3) (padSlope p + 2):=by
      rw [hps.2.2,hps.1]; exact hbox
    have hprovider:=actual_identityCurveCountProvider
      (a:=padA p) (b:=padB p) (s:=padSlope p) S 181392 hnodes hagreement
      (by norm_num) hTailNumerator D (padA p + padB p + padSlope p + 3) (padSlope p + 2)
      (by norm_num) hDlow hDchar hbox' hflagChar
      (LocatorFixedStage.identity_mixed_gate (padB p) (padSlope p) flag hS' hY'
        hflag'.1 hflag'.2.1)
    have hpositive:1 ≤ identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=by
      apply LocatorFixedStage.identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S 181392
      (identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071) hprovider hagreement
      (by norm_num) (by rw [hnodes]; norm_num) hpositive
    have hscaled:Gamma.card * 50321 ≤
        50321 * hybridCostABS flag (padA p) (padB p) (padSlope p):=by
      calc
        Gamma.card * 50321=Gamma.card * (181392 - 131071):=rfl
        _ ≤ (S.nodes.card - 131071) * (80752 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=hinc
        _= (262144 - 131071) * (80752 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=by
          rw [hnodes]
        _ ≤ 50321 * hybridCostABS flag (padA p) (padB p) (padSlope p):=
          identity_le_hybrid flag (padA p) (padB p) (padSlope p) hb1
    rw [hybridBound_eq_abs]
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num:0 < 50321)
    simpa only [Nat.mul_comm] using hscaled
  · obtain ⟨P⟩:=hprov S hnodes hagreement hbox hflag hTail
    have h:=stage_card_le_divisorBound S P
    have hct:=cell_tails_eq p
    rw [hct.1,hct.2.1,hct.2.2.1,hct.2.2.2] at h
    simpa only [hybridBound,RCN327.w,Nat.reduceAdd] using h

theorem regular_factor_count_hybrid
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:P.s ≤ 28) (hY:P.ys ≤ 127) (hT:P.total ≤ 5964)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (R:RegularIndex Q)
    (hhyb:HybridApplies (regularCumulativeFlag Q R))
    (hreal:Realization D) :
    (regularSeeds Q selected Gamma R).card ≤ hybridCost (regularCumulativeFlag Q R):=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  set p:=regularCumulativeFlag Q R with hp
  have hRdata:=directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < 2130706433:=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox0:R.1 ∈ RCN174.globalCoefficientBox K D 131071
      (padA p + padB p + padSlope p + 3) (padSlope p + 2):=
    own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:ResidualSupportData (RCN198.support (padA p) (padB p) (padSlope p)) R.1:=
    own_support R.1
  have hRwhole:=factor_support Q hQ HQ R
  have hc:=originalCumulativeFlag_cumulative R.1
  have hps:=pad_sums p
  have hRbox:R.1 ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p):=by
    rw [← hps.2.2,← hps.1]; exact hRbox0
  have h1:p.all ≤ 28:=hRwhole.s_weight.trans hS
  have h2:middle p ≤ 127:=by
    simpa only [hp,middle,regularCumulativeFlag,hc.2.1] using hRwhole.ys_weight.trans hY
  have h3:total p ≤ 5964:=by
    simpa only [hp,total,regularCumulativeFlag,hc.2.2] using hRwhole.total_weight.trans hT
  have hpS:padS p ≤ 28:=max_le h1 (by decide)
  have hpY:padY p ≤ 127:=max_le h2 (by omega)
  have hpT:padT p ≤ 5964:=max_le h3 (by omega)
  have hpSeq:padS p=p.all:=max_eq_left hhyb.1
  have hpYeq:padY p=middle p:=max_eq_left (by rw [hpSeq]; exact hhyb.2.trans' (by omega))
  have hhyb':padS p + 2 ≤ padY p:=by rw [hpSeq,hpYeq]; exact hhyb.2
  have hprov:ProviderHyp D p:=hreal p hpS hpY hpT hhyb'
  have hsolutions:∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        hybridBound (geometricCumulativeFlag K g) p:=by
    let S0:=regularGeometricResidualStageOfSupport
      (RCN198.support (padA p) (padB p) (padSlope p)) Q selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S:=reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub:geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
    have hnodes:S.nodes.card=181392 + 80752:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181392 ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,S0,ResidualStage.agreementFiber,ResidualStage.Agrees,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf:=geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hf1:(geometricCumulativeFlag K g).all ≤ padSlope p + 2:=hf.1
    have hf2:(geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤
        padB p + padSlope p + 3:=hf.2.1
    have hf3:(geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all ≤ padA p + padB p + padSlope p + 3:=hf.2.2
    have hf':(geometricCumulativeFlag K g).all ≤ padS p ∧
        (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤ padY p ∧
        (geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
          (geometricCumulativeFlag K g).all ≤ padT p:=by
      refine ⟨?_,?_,?_⟩ <;> omega
    have hcount:=hybridStageBound D p hDlow hDhigh hpS hpY hpT hhyb' hprov
      (S:=S) hnodes hag hRbox hf'
    simpa only [geometricCumulativeFlag] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        hybridBound (geometricCumulativeFlag K g) p:=Finset.sum_le_sum (fun g _=> hstage g)
    _ ≤ hybridCost p:=by
      have hb:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact merge_hybrid_costs (geometricCumulativeFlag K) p hb.1 hb.2.1 hb.2.2

end
end ProximityPrize.SubmissionLower.LocatorFixedHybrid
end PackedLocator_LocatorFixedHybrid

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorReplacement. -/
section PackedLocator_LocatorFactorReplacement
namespace ProximityPrize.SubmissionLower.LocatorFactorReplacement
open scoped BigOperators
open RCN095 LocatorFactorAggregate
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def remainingCap (T YS S:ℕ) (p:FlagDegree):FlagDegree :=
  cap (T - total p) (min (YS - middle p) (T - total p))
    (min (S - p.all) (min (YS - middle p) (T - total p)))
def remainingCost (T YS S d e:ℕ) (p:FlagDegree):ℕ :=
  if (remainingCap T YS S p).all = 0 then 0
  else paddedCost d e (remainingCap T YS S p)
def cellCost (T YS S d e:ℕ) (p:FlagDegree) (q:ℕ):ℕ :=
  min (paddedCost d e p) q + remainingCost T YS S d e p
def Bad (T d e bound:ℕ) (p:FlagDegree):Prop :=
  bound * total p < T * paddedCost d e p
theorem remainingCap_cumulative (T YS S:ℕ) (p:FlagDegree) :
    (remainingCap T YS S p).all =
        min (S - p.all) (min (YS - middle p) (T - total p)) ∧
      middle (remainingCap T YS S p) = min (YS - middle p) (T - total p) ∧
      total (remainingCap T YS S p) = T - total p:=by
  exact cap_cumulative _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _)
theorem sum_erase_le_sub {I:Type*} [Fintype I] [DecidableEq I]
    (f:I → ℕ) (B:ℕ) (h:(∑ i, f i) ≤ B) (i:I) :
    (∑ j ∈ Finset.univ.erase i, f j) ≤ B - f i:=by
  have heq:=Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  omega
theorem remaining_cumulative {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (T YS S:ℕ) (i:I)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T) :
    (∑ j ∈ Finset.univ.erase i, (p j).all) ≤ (remainingCap T YS S (p i)).all ∧
      (∑ j ∈ Finset.univ.erase i, middle (p j)) ≤ middle (remainingCap T YS S (p i)) ∧
      (∑ j ∈ Finset.univ.erase i, total (p j)) ≤ total (remainingCap T YS S (p i)):=by
  have hrs:=sum_erase_le_sub (fun j => (p j).all) S hs i
  have hys:=sum_erase_le_sub (fun j => middle (p j)) YS hy i
  have hts:=sum_erase_le_sub (fun j => total (p j)) T ht i
  have hry:(∑ j ∈ Finset.univ.erase i, (p j).all) ≤
      ∑ j ∈ Finset.univ.erase i, middle (p j) :=
    Finset.sum_le_sum (fun j _ => all_le_middle (p j))
  have hyt:(∑ j ∈ Finset.univ.erase i, middle (p j)) ≤
      ∑ j ∈ Finset.univ.erase i, total (p j) :=
    Finset.sum_le_sum (fun j _ => middle_le_total (p j))
  have hc:=remainingCap_cumulative T YS S (p i)
  rw [hc.1, hc.2.1, hc.2.2]
  exact ⟨le_min hrs (le_min (hry.trans hys) ((hry.trans hyt).trans hts)),
    le_min hys (hyt.trans hts), hts⟩
theorem sum_others_le_remainingCost {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (count:I → ℕ) (T YS S d e:ℕ) (i:I)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T)
    (hstage:∀ j, count j ≤ paddedCost d e (p j))
    (hzero:∀ j, (p j).all = 0 → count j = 0) :
    (∑ j ∈ Finset.univ.erase i, count j) ≤ remainingCost T YS S d e (p i):=by
  have hc:=remaining_cumulative p T YS S i hs hy ht
  by_cases hz:(remainingCap T YS S (p i)).all = 0
  · rw [remainingCost, if_pos hz]
    have hrs:(∑ j ∈ Finset.univ.erase i, (p j).all) ≤ 0:=by
      simpa only [hz] using hc.1
    have hcount:(∑ j ∈ Finset.univ.erase i, count j) = 0:=by
      apply Finset.sum_eq_zero
      intro j hj
      apply hzero j
      have hji:(p j).all ≤ ∑ k ∈ Finset.univ.erase i, (p k).all :=
        Finset.single_le_sum (f:=fun k => (p k).all)
          (fun k _ => Nat.zero_le (p k).all) hj
      omega
    exact hcount.le
  · rw [remainingCost, if_neg hz]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, paddedCost d e (p j) :=
        Finset.sum_le_sum (fun j _ => hstage j)
      _ ≤ paddedCost d e (remainingCap T YS S (p i)) :=
        merge_padded_costs_finset (Finset.univ.erase i) d e p _ hc.1 hc.2.1 hc.2.2
theorem sum_le_cellCost {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (count:I → ℕ) (T YS S d e:ℕ) (i:I) (q:ℕ)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T)
    (hstage:∀ j, count j ≤ paddedCost d e (p j))
    (hzero:∀ j, (p j).all = 0 → count j = 0)
    (hrepl:count i ≤ q) :
    (∑ j, count j) ≤ cellCost T YS S d e (p i) q:=by
  have hi:=le_min (hstage i) hrepl
  have hr:=sum_others_le_remainingCost p count T YS S d e i hs hy ht hstage hzero
  calc
    _ = count i + ∑ j ∈ Finset.univ.erase i, count j :=
      (Finset.add_sum_erase Finset.univ count (Finset.mem_univ i)).symm
    _ ≤ min (paddedCost d e (p i)) q + remainingCost T YS S d e (p i) :=
      Nat.add_le_add hi hr
    _ = cellCost T YS S d e (p i) q:=rfl
theorem high_unique {I:Type*} [Fintype I] [DecidableEq I] (p:I → FlagDegree)
    (hs:(∑ i, (p i).all) ≤ 14) {i j:I}
    (hi:8 ≤ (p i).all) (hj:8 ≤ (p j).all):i = j:=by
  by_contra hne
  have hjmem:j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩
  have hrest:=sum_erase_le_sub (fun k => (p k).all) 14 hs i
  have hjrest:(p j).all ≤ ∑ k ∈ Finset.univ.erase i, (p k).all :=
    Finset.single_le_sum (f:=fun k => (p k).all)
      (fun k _ => Nat.zero_le (p k).all) hjmem
  omega
theorem aggregate_of_rate_and_cells {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T YS S d e lowR bound:ℕ)
    (hT:0 < T)
    (hs:(∑ i, (p i).all) ≤ S)
    (hy:(∑ i, middle (p i)) ≤ YS)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrate:∀ i, (p i).all ≤ lowR → T * paddedCost d e (p i) ≤ bound * total (p i))
    (hrepl:∀ i, lowR < (p i).all → count i ≤ q i)
    (hcell:∀ i, lowR < (p i).all → cellCost T YS S d e (p i) (q i) ≤ bound) :
    (∑ i, count i) ≤ bound:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  by_cases hh:∃ i, lowR < (p i).all
  · obtain ⟨i, hi⟩:=hh
    exact (sum_le_cellCost p count T YS S d e i (q i) hs hy ht hstage hzero
      (hrepl i hi)).trans (hcell i hi)
  · have hlo (i:I):(p i).all ≤ lowR:=by
      have hn:¬ lowR < (p i).all:=fun hi => hh ⟨i, hi⟩
      omega
    have hscaled:T * (∑ i, count i) ≤ T * bound:=by
      calc
        _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
        _ ≤ ∑ i, T * paddedCost d e (p i) :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left T (hstage i))
        _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hrate i (hlo i))
        _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
        _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
        _ = T * bound:=by ring
    exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_of_bad_cells {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T YS S d e bound:ℕ)
    (hT:0 < T)
    (hs:(∑ i, (p i).all) ≤ S)
    (hy:(∑ i, middle (p i)) ≤ YS)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrepl:∀ i, Bad T d e bound (p i) → count i ≤ q i)
    (hcell:∀ i, Bad T d e bound (p i) →
      cellCost T YS S d e (p i) (q i) ≤ bound) :
    (∑ i, count i) ≤ bound:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  by_cases hh:∃ i, Bad T d e bound (p i)
  · obtain ⟨i, hi⟩:=hh
    exact (sum_le_cellCost p count T YS S d e i (q i) hs hy ht hstage hzero
      (hrepl i hi)).trans (hcell i hi)
  · have hrate (i:I):T * paddedCost d e (p i) ≤ bound * total (p i):=by
      have hn:¬ Bad T d e bound (p i):=fun hi => hh ⟨i, hi⟩
      dsimp only [Bad] at hn
      omega
    have hscaled:T * (∑ i, count i) ≤ T * bound:=by
      calc
        _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
        _ ≤ ∑ i, T * paddedCost d e (p i) :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left T (hstage i))
        _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hrate i)
        _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
        _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
        _ = T * bound:=by ring
    exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_of_rate_replacements {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T d e bound:ℕ)
    (hT:0 < T)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hrepl:∀ i, Bad T d e bound (p i) → count i ≤ q i)
    (hqrate:∀ i, Bad T d e bound (p i) →
      T * q i ≤ bound * total (p i)) :
    (∑ i, count i) ≤ bound:=by
  have hone (i:I):T * count i ≤ bound * total (p i):=by
    by_cases hbad:Bad T d e bound (p i)
    · exact (Nat.mul_le_mul_left T (hrepl i hbad)).trans (hqrate i hbad)
    · have hordinary:T * paddedCost d e (p i) ≤ bound * total (p i):=by
        unfold Bad at hbad
        omega
      exact (Nat.mul_le_mul_left T (hstage i)).trans hordinary
  have hscaled:T * (∑ i, count i) ≤ T * bound:=by
    calc
      _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hone i)
      _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
      _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
      _ = T * bound:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_6751 {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ)
    (hs:(∑ i, (p i).all) ≤ 14)
    (hy:(∑ i, middle (p i)) ≤ 64)
    (ht:(∑ i, total (p i)) ≤ 1698)
    (hstage:∀ i, count i ≤ paddedCost 131072 131073 (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrepl:∀ i, 8 ≤ (p i).all → count i ≤ q i)
    (hcell:∀ i, 8 ≤ (p i).all →
      cellCost 1698 64 14 131072 131073 (p i) (q i) ≤ 266000000000000000) :
    (∑ i, count i) ≤ 266000000000000000:=by
  classical
  refine aggregate_of_rate_and_cells p count q 1698 64 14 131072 131073 7
    266000000000000000 (by decide) hs hy ht hstage hzero ?_ ?_ ?_
  · intro i hi
    have hyi:middle (p i) ≤ 64 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy
    have hti:total (p i) ≤ 1698 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht
    exact (rate_bound_6751_low (p i) hi hyi hti).trans
      (Nat.mul_le_mul_right (total (p i))
        (by decide:261420997282933785 ≤ 266000000000000000))
  · intro i hi
    exact hrepl i (by omega)
  · intro i hi
    exact hcell i (by omega)
/-- Ordinary-route badness for an arbitrary ordinary cost function. -/
def BadCost (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ) (p:FlagDegree):Prop :=
  bound * total p < T * cost p
theorem aggregate_of_rate_replacements_cost {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ)
    (hT:0 < T)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ cost (p i))
    (hrepl:∀ i, BadCost T cost bound (p i) → count i ≤ q i)
    (hqrate:∀ i, BadCost T cost bound (p i) →
      T * q i ≤ bound * total (p i)) :
    (∑ i, count i) ≤ bound:=by
  have hone (i:I):T * count i ≤ bound * total (p i):=by
    by_cases hbad:BadCost T cost bound (p i)
    · exact (Nat.mul_le_mul_left T (hrepl i hbad)).trans (hqrate i hbad)
    · have hordinary:T * cost (p i) ≤ bound * total (p i):=by
        unfold BadCost at hbad
        omega
      exact (Nat.mul_le_mul_left T (hstage i)).trans hordinary
  have hscaled:T * (∑ i, count i) ≤ T * bound:=by
    calc
      _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hone i)
      _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
      _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
      _ = T * bound:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hT

/-! A multiresource replacement ledger.  The scalar rate above charges every
factor only against its total-degree contribution.  For a strongly anisotropic
factor this can discard nearly all of the global middle- and slope-degree
information.  The potential below charges against all three additive degree
budgets, so a costly factor with large middle degree is automatically scarce. -/

def degreePotential (aT aY aS : ℕ) (p : FlagDegree) : ℕ :=
  aT * total p + aY * middle p + aS * p.all

def BadPotential (aT aY aS : ℕ) (cost : FlagDegree → ℕ)
    (p : FlagDegree) : Prop :=
  degreePotential aT aY aS p < cost p

theorem aggregate_of_potential_replacements_cost {I : Type*} [Fintype I]
    (p : I → FlagDegree) (count q : I → ℕ)
    (T YS S aT aY aS : ℕ) (cost : FlagDegree → ℕ)
    (hs : (∑ i, (p i).all) ≤ S)
    (hy : (∑ i, middle (p i)) ≤ YS)
    (ht : (∑ i, total (p i)) ≤ T)
    (hstage : ∀ i, count i ≤ cost (p i))
    (hrepl : ∀ i, BadPotential aT aY aS cost (p i) → count i ≤ q i)
    (hqpotential : ∀ i, BadPotential aT aY aS cost (p i) →
      q i ≤ degreePotential aT aY aS (p i)) :
    (∑ i, count i) ≤ aT * T + aY * YS + aS * S := by
  have hone (i : I) : count i ≤ degreePotential aT aY aS (p i) := by
    by_cases hbad : BadPotential aT aY aS cost (p i)
    · exact (hrepl i hbad).trans (hqpotential i hbad)
    · exact (hstage i).trans (by
        unfold BadPotential at hbad
        omega)
  calc
    (∑ i, count i) ≤ ∑ i, degreePotential aT aY aS (p i) :=
      Finset.sum_le_sum (fun i _ => hone i)
    _ = aT * (∑ i, total (p i)) +
        aY * (∑ i, middle (p i)) + aS * (∑ i, (p i).all) := by
      simp only [degreePotential, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ aT * T + aY * YS + aS * S :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left aT ht)
        (Nat.mul_le_mul_left aY hy)) (Nat.mul_le_mul_left aS hs)

end ProximityPrize.SubmissionLower.LocatorFactorReplacement
end PackedLocator_LocatorFactorReplacement

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedConsumer. -/
section PackedLocator_LocatorFixedConsumer
namespace ProximityPrize.SubmissionLower.LocatorFixedConsumer
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN275 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
def wholeSupport:ResidualSupportParameters:=
  ⟨28,127,5964,by decide,by decide,by decide,by decide⟩

/-- The selected TCap/B gcd is wider in the middle and slope coordinates
than `wholeSupport`.  It is nevertheless a valid carrier for the initial
A-source split; only the factors in the universal child are later charged by
the narrow fixed-phase argument. -/
def wideSupport:ResidualSupportParameters:=
  ⟨33,153,5964,by decide,by decide,by decide,by decide⟩

/-- Regular allowance used by the initial A-source split. -/
abbrev initialRegularCap:ℕ:=LocatorArithmetic.fixedRegularCap

/-- Pure bookkeeping for the initial A-source split.  `U` is the set of
factors universal on the current A kernel.  The universal child is bounded
in aggregate by `phaseCap`; every factor outside it is charged by its direct
A-helper cap.  No claim about divisibility is hidden in this lemma. -/
theorem initial_A_regularSeeds_sum_le
    (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (U:Finset (RegularIndex H)) (phaseCap:ℕ)
    (helperCap:RegularIndex H → ℕ)
    (hphase:(∑ F ∈ U,(regularSeeds H selected Gamma F).card) ≤ phaseCap)
    (hhelper:∀ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
      (regularSeeds H selected Gamma F).card ≤ helperCap F)
    (hledger:phaseCap+
      (∑ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,helperCap F) ≤
        initialRegularCap) :
    (∑ F:RegularIndex H,(regularSeeds H selected Gamma F).card) ≤
      initialRegularCap:=by
  classical
  have hsplit:(Finset.univ:Finset (RegularIndex H)) =
      U ∪ ((Finset.univ:Finset (RegularIndex H)) \ U):=by
    ext F
    simp only [Finset.mem_univ,Finset.mem_union,Finset.mem_sdiff,true_and]
    tauto
  have hdisjoint:Disjoint U
      ((Finset.univ:Finset (RegularIndex H)) \ U):=by
    apply Finset.disjoint_left.mpr
    intro F hFU hFd
    exact (Finset.mem_sdiff.mp hFd).2 hFU
  change (∑ F ∈ (Finset.univ:Finset (RegularIndex H)),
    (regularSeeds H selected Gamma F).card) ≤ initialRegularCap
  rw [hsplit,Finset.sum_union hdisjoint]
  exact (Nat.add_le_add hphase
    (Finset.sum_le_sum (fun F hF=>hhelper F hF))).trans hledger

/-- Cover/singular wrapper for the wide selected gcd.  The regular term is
supplied by `initial_A_regularSeeds_sum_le`; the singular argument legitimately
uses the full B contact/slope box and does not require the narrow A caps. -/
theorem wide_fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 20134512 131071 5964 33)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (hregular:(∑ F:RegularIndex H,
      (regularSeeds H selected Gamma F).card) ≤ initialRegularCap) :
    Gamma.card ≤ initialRegularCap+LocatorArithmetic.fixedSingularCap:=by
  have hspos:1 ≤ LocatorArithmetic.fixedSingular.s:=by decide
  have hssmall:LocatorArithmetic.fixedSingular.s < 2130706433:=by decide
  have hwpos:1 ≤ LocatorArithmetic.fixedSingular.w:=by decide
  have hwsmall:LocatorArithmetic.fixedSingular.w < 2130706433:=by decide
  have hkD:LocatorArithmetic.fixedSingular.w <
      LocatorArithmetic.fixedSingular.kappa*LocatorArithmetic.fixedSingular.D:=by
    decide
  have halgpos:1 ≤ LocatorArithmetic.fixedSingular.algebraicCap:=by decide
  have himpsmall:LocatorArithmetic.fixedSingular.implicitYCap < 2130706433:=by
    decide
  have halgsmall:LocatorArithmetic.fixedSingular.algebraicCap < 2130706433:=by
    decide
  have hwa:LocatorArithmetic.fixedSingular.w <
      LocatorArithmetic.fixedSingular.a:=by decide
  have han:LocatorArithmetic.fixedSingular.a ≤
      LocatorArithmetic.fixedSingular.n:=by decide
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 20134512 5964 33) H hH hbox
    hspos hssmall hwpos hkD halgpos halgsmall
    selected Gamma hsolution
  have hsing:=CommonShearTightPrototype.singularSeeds_count_le_countCap
    LocatorArithmetic.fixedSingular H hH hbox
    hspos hssmall hwpos hwsmall hkD halgpos himpsmall halgsmall hwa han
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18))=262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [LocatorArithmetic.fixedSingular,
          RCN318.TightParameters.errors, LocatorArithmetic.n,
          LocatorArithmetic.w, LocatorArithmetic.agreements,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hregular hsing)
end
end ProximityPrize.SubmissionLower.LocatorFixedConsumer
end PackedLocator_LocatorFixedConsumer

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailRealization. -/
section PackedLocator_LocatorHybridTailRealization
/-
LOCATOR HYBRID TAIL REALIZATION (port of ContactHybridTailRealization6751Research,
pr359) — the sharp analogue of Q2.lean's
`exists_delayedTailMultiplicityProvider_of_reducedGeneral`.

DESIGN (all signatures checked against this tree):
  * The sharp geometry is built NATIVELY over the T1-components (T1 = the
    (w+1)-th global tail cut) from the sharp-flag containment `firstCut_in_sharp`;
    no transport of the reduced geometry along regularComponentEquiv is needed.
  * The fixed powers come from reducedStage_activeFixedPowers applied AT THE
    TRIVIAL CONGRUENCE Tred := T1 (S.G ∣ T1 - T1 by simp): the congruence
    machinery collapses, and transportedMultiplicity at the self-congruence is
    the identity (funext + Subtype.ext rfl, `transportedMultiplicity_self`), so
    the certificate is stated for the local multiplicities directly.
  * The certificate is activeNestedWeightedCertificate on T1 directly —
    NO ofCongruentCut, NO transport.
  * budget/hcost/hmovingSum come from exists_firstTail_cut_budgets with
    E := AlgebraicClosure (RatFunc (GenericField K)).
  * The stage is loosened with loosenStageGeneral (no support-cap hypotheses,
    as in Q2.lean).
  * htangentGate is derived from hrationalGate (rational ≤ hybrid coordinate-
    wise); hrationalGate itself follows from `rationalGate_of_le` for any error
    cap with errorCap + 1 ≤ 131076, since b ≥ 1 in the hybrid branch r + 2 ≤ y.
  * hmix / hmixedSharp / hflagChar stay hypotheses (numeric, discharged where
    the prime is concrete).

KNOWN RISK SITES of the pr359 draft, and how they resolve here:
  (R1) the AdaptiveNestedProjectionDataActive constructor: obtained through
       exists_adaptiveNestedProjectionDataActive, no manual field list.
  (R2) the E-instances: Algebra (GenericField K) (AlgebraicClosure (RatFunc _))
       is found by typeclass search; CharP E p is supplied by
       charP_of_injective_algebraMap.
  (R3) defeq frictions cellSupport ↔ support / cellSharpTail ↔
       sharpResidualAgreementFlag: both are definitional (delta), `exact` works.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealization
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

/-! ### 1. Trivial congruence and transport-collapse -/

theorem firstCut_sub_self_dvd
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r)) :
    S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
      globalTailCut (polynomialEmbedding K) S.F (w + 1) := by
  simp

theorem transportedMultiplicity_self
    {G T H : MvPolynomial (Fin 3) (GenericField K)}
    (h : G ∣ T - T)
    (mult : RegularComponent (GenericField K) G T H → ℕ) :
    transportedMultiplicity h mult = mult := by
  funext C
  exact congrArg mult (Subtype.ext rfl)

/-! ### 2. Native sharp geometry over the T1-components -/

section Geometry

variable (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap
    flag w (cellSupport t y r))

theorem firstCut_in_sharp :
    PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
    (w + 1) (tailSelector (w + 1)) 0 0 0

structure SharpActiveGeometry where
  base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1
  hactive : ∀ C : FirstTailComponent S,
    KaehlerDifferential.D (GenericField K)
        (CoordinateField (GenericField K) C.1)
        (coordinate (GenericField K) C.1 0) ≠ 0 ∨
      KaehlerDifferential.D (GenericField K)
        (CoordinateField (GenericField K) C.1)
        (coordinate (GenericField K) C.1 2) ≠ 0
  hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2
  data : AdaptiveNestedProjectionDataActive base hactive
    (residualStage_pderiv_one_ne_zero_of_support S)

theorem exists_sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    Nonempty (SharpActiveGeometry S) := by
  classical
  have hGflag : PolynomialInFlag flag S.G := S.flag_support
  have hTflag : PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) :=
    firstCut_in_sharp S
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hTY' : (globalTailCut (polynomialEmbedding K) S.F
      (w + 1)).degreeOf 0 ≤
      1 + (w + 1) * (2 * (cellB y r + cellS r + 3) - 2) := by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys (cellSupport t y r) hsy (w + 1)
  have hTS' : (globalTailCut (polynomialEmbedding K) S.F
      (w + 1)).degreeOf 1 ≤
      (2 * (cellS r + 2) - 1) * (w + 1) := by
    apply hTS.trans_eq
    rfl
  have hGdegree : ∀ j : Fin 3, S.G.degreeOf j < p := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ : coordinateMixedDegree (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) 2 < p := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixedSharp
  let choiceData : ∀ C : FirstTailComponent S,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) p
      S.G_dvd_surface S.irreducible_G hfirstProper S.y_dependent
      hGdegree hmixedZ C
  let base : ∀ C : FirstTailComponent S,
      SeparableLiteralCoordinate C.1 := fun C ↦ (choiceData C).choose
  have hbaseIndex : ∀ C : FirstTailComponent S,
      (base C).index = 0 ∨ (base C).index = 2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : FirstTailComponent S,
      KaehlerDifferential.D (GenericField K)
          (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 0) ≠ 0 ∨
        KaehlerDifferential.D (GenericField K)
          (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 2) ≠ 0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  have hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate (GenericField K)
      C.1 2 htr p S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      S.irreducible_G
      (regularComponent_G_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      (regularComponent_T_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      hfirstProper hGdegree hmixedZ
  exact ⟨⟨base, hactive, hZ,
    Classical.choice (exists_adaptiveNestedProjectionDataActive base hactive
      (residualStage_pderiv_one_ne_zero_of_support S))⟩⟩

noncomputable def sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) : SharpActiveGeometry S :=
  Classical.choice
    (exists_sharpActiveGeometry S hfirstProper hflagChar hmixedSharp)

/-! ### 3. The sharp unit family and budget family -/

noncomputable def sharpUnitFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    AdaptiveUnitProjectionFamily
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
      flag (cellSharpTail t y r) :=
  activeNestedUnitFamily
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))).2
      (firstCut_in_sharp S))

noncomputable def sharpBudgetFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    PrimeFlagBudgetFamily
      (G := S.G)
      (T := globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F)
      flag (cellSharpTail t y r) :=
  (sharpUnitFamily S hfirstProper hflagChar hmixedSharp).toPrimeFlagBudgetFamily

/-! ### 4. The certificate on T1 directly -/

theorem sharpWeightedResultants
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    RegularComponentWeightedInertiaResultantCertificate
      (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp)
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C) := by
  have h0 := firstCut_sub_self_dvd S
  have powers := reducedStage_activeFixedPowers
    (loosenStageGeneral S) hfirstProper
    (globalTailCut (polynomialEmbedding K) S.F (w + 1)) h0
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
  exact activeNestedWeightedCertificate
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))).2
      (firstCut_in_sharp S))
    _ powers

end Geometry

/-! ### 5. The realization -/

theorem exists_hybridTailMultiplicityProvider_realized
    (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  haveI : CharP (AlgebraicClosure (RatFunc (GenericField K))) p :=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget, hcost, hz, hyz, hall, hmov⟩ :=
    exists_firstTail_cut_budgets
      (E := AlgebraicClosure (RatFunc (GenericField K)))
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (cellA t y) (cellB y r) (cellS r) w (by norm_num [RCN327.w])
      rfl
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
      (sharpUnitFamily S hfirstProper hflagChar hmixedSharp)
      p hmix
  have hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    have hcut := cellMovingCut_eq_center_add t y r
    have hfib : cellMovingFiber t y r =
        RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r) := rfl
    rw [hfib, hcut]
    exact hmov
  have htangentGate : stageErrorCap + 1 ≤
      (cellHybridCoordinate t y r).yz :=
    tangentGate_of_rationalGate t y r stageErrorCap hrationalGate
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).zCost C ∧
      (budget C).yzCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C ∧
      (budget C).allCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).allCost C :=
    hcost
  exact exists_hybridTailMultiplicityProvider_of_localDVR
    t y r hr2 hb hyt S hfirstProper
    (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    budget hcost' hmovingSum htangentGate hrationalGate htangent
    (sharpWeightedResultants S hfirstProper hflagChar hmixedSharp)

/-- The hybrid fixed-stage seed bound: `Gamma.card ≤ cellHybridCost`-shaped
bound with the stage's own `flag`. -/
theorem hybrid_stage_card_le
    (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C) :
    Gamma.card ≤
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
  stage_card_le_divisorBound S
    (exists_hybridTailMultiplicityProvider_realized hr2 hb hyt S hfirstProper
      hflagChar hmixedSharp hmix hrationalGate htangent).some

/-! ### 6. Positivity of the sharp yz-cost (for tangent-count consumers) -/

theorem sharpUnitFamily_one_le_yzCost
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (C : FirstTailComponent S) :
    1 ≤ (sharpUnitFamily S hfirstProper hflagChar hmixedSharp
      ).toPrimeFlagBudgetFamily.yzCost C := by
  let A := sharpActiveGeometry S hfirstProper hflagChar hmixedSharp
  let U := sharpUnitFamily S hfirstProper hflagChar hmixedSharp
  change 1 ≤ coordinateDegree (GenericField K)
    (CoordinateField (GenericField K) C.1) (U.yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  have hproj : U.yzProjection C = coordinateOfGate
      (affineU (GenericField K) C.1 A.data.lam) (A.data.uGate C) := rfl
  rw [hproj, coordinateOfGate_value]
  exact A.data.uTranscendental C

end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealization
end PackedLocator_LocatorHybridTailRealization

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridGates. -/
section PackedLocator_LocatorHybridGates

/-! Numeric characteristic gates for the hybrid provider on the fixed stage
(`s + 2 ≤ 28`, `b + s + 3 ≤ 127`, `a + b + s + 3 ≤ 5964`, prime `2130706433`). -/

namespace ProximityPrize.SubmissionLower.LocatorHybridGates
open RCN095 LocatorHybridCells

theorem sharp_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 28) (hY:b + s + 3 ≤ 127)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) < 2130706433:=by
  have hy:2 * (b + s + 3) - 2 ≤ 252:=by omega
  have hs:2 * (s + 2) - 1 ≤ 55:=by omega
  have hfS:flag.all ≤ 28:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 127:=hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 252) * 28 + 127 * (55 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433:=by norm_num [RCN327.w]

theorem product_gate (a b s:ℕ) (flag:FlagDegree)
    (hT:a + b + s + 3 ≤ 5964)
    (hft:flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < 2130706433:=by
  have h1:flag.zOnly + flag.yz + flag.all ≤ 5964:=hft.trans hT
  have h2:a + b + s + 4 ≤ 5965:=by omega
  calc
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) ≤ 2 * 5964 * 5965 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433:=by norm_num

theorem rational_gate (t y r:ℕ) (hb:r + 2 ≤ y) :
    80752 + 1 ≤ (cellRational t y r).yz:=
  rationalGate_of_le t y r 80752 hb (by norm_num)

end ProximityPrize.SubmissionLower.LocatorHybridGates
end PackedLocator_LocatorHybridGates

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridRealize. -/
section PackedLocator_LocatorHybridRealize

/-! The hybrid provider exists on every admissible cell of the fixed stage. -/

namespace ProximityPrize.SubmissionLower.LocatorHybridRealize
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCells LocatorHybridTailProvider
  LocatorHybridTailRealization LocatorHybridGates LocatorFixed LocatorFixedHybrid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem realization:Realization 16688064:=by
  intro p hS hY hT hhyb
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  unfold ProviderHyp
  intro Gamma flag S hnodes hagreement hbox hflag hTail
  have hps:=pad_sums p
  have hpb:=pad_bounds p
  have hr2:2 ≤ padS p:=hpb.1
  have hyt:padY p ≤ padT p:=hpb.2.2
  have hflagChar:flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433:=by
    refine ⟨?_,?_,?_⟩ <;> omega
  have hmixedSharp:=sharp_mixed_gate (padB p) (padSlope p) flag
    (by omega) (by omega) (by omega) (by omega)
  have hmix:=product_gate (padA p) (padB p) (padSlope p) flag (by omega) (by omega)
  have hrat:=rational_gate (padT p) (padY p) (padS p) hhyb
  have htangent:∀ C:FirstTailComponent S,
      (∀ delay,globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80752 + 1) * (sharpBudgetFamily S hTail hflagChar hmixedSharp).yzCost C:=by
    intro C hall
    exact tangent_component_card_le S C hTail
      ((sharpActiveGeometry S hTail hflagChar hmixedSharp).base C)
      181392 16688064 (padT p) (padS p) hnodes hagreement
      (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) (by norm_num)
      hbox (sharpBudgetFamily S hTail hflagChar hmixedSharp)
      (sharpUnitFamily_one_le_yzCost S hTail hflagChar hmixedSharp C) hall
      ((sharpUnitFamily S hTail hflagChar hmixedSharp).toAdaptiveUnitPoleBudget.yzPole C)
  exact exists_hybridTailMultiplicityProvider_realized hr2 hhyb hyt S hTail hflagChar
    hmixedSharp hmix hrat htangent
end
end ProximityPrize.SubmissionLower.LocatorHybridRealize
end PackedLocator_LocatorHybridRealize

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedOwnBound. -/
section PackedLocator_LocatorFixedOwnBound

/-! Per-factor bounds on the fixed stage: padded always, hybrid when it applies. -/

namespace ProximityPrize.SubmissionLower.LocatorFixedOwnBound
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open LocatorFactorAggregate LocatorHybridCost LocatorFixed LocatorFixedHybrid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

/-- Both per-factor bounds: padded always, hybrid when it applies. -/
theorem regular_factor_own_bound
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 16688064)
    (hS:P.s ≤ 28) (hY:P.ys ≤ 127) (hT:P.total ≤ 5964)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (R:RegularIndex Q) (hreal:Realization D) :
    OwnBound (regularSeeds Q selected Gamma R).card (regularCumulativeFlag Q R):=
  ⟨regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R,
    fun hhyb=> regular_factor_count_hybrid D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb hreal⟩
end
end ProximityPrize.SubmissionLower.LocatorFixedOwnBound
end PackedLocator_LocatorFixedOwnBound

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceArithmetic. -/
section PackedLocator_LocatorSourceArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
theorem kernelAmbient_nullity:
    coefficientCount 48975840 131071 130000 81 -
      262144 * localRankBound 270 130000 81=321495185604514:=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
end PackedLocator_LocatorSourceArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorSingletonSource. -/
section PackedLocator_LocatorSingletonSource

/-!
# A compact source for the terminal singleton locator cell

This source is small enough to fit inside the selected ambient coefficient
box, but its kernel nullity is just large enough for the `(5964, 50, 11)`
terminal route.  The local-rank receipt is split into short reductions so the
verifier never has to normalize all 153 contact rows in one expression.
-/

namespace ProximityPrize.SubmissionLower.LocatorSingletonSource

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 27752976 131071 7289 47 153
    IRSProfile.domain u0 u1

theorem weighted_exact : 153 * 181392 = 27752976 := by
  decide

theorem shape : 27752976 + 47 ≤ 131071 * (211 + 1) := by
  decide

theorem coefficientCount_exact :
    coefficientCount 27752976 131071 7289 47 = 811782277866964 := by
  change coefficientCount (211 * 131071 + 96995) 131071 7289 47 =
    811782277866964
  rw [coefficientCount_eq_oneResidueCoefficientCount
    211 96995 131071 7289 47 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

private def rankRow (r : ℕ) : ℕ :=
  let M := min r 7289
  let h := min (r + 1) (153 - r)
  rectangularCount (M + 1) (47 + 1) 0 7289 -
    rectangularCount (M + 1 - h) (47 + 1 - h) h 7289

private theorem rank_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 723390720 := by
  decide

private theorem rank_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 1979021408 := by
  decide

private theorem rank_128 :
    (∑ i ∈ Finset.range 25, rankRow (128 + i)) = 393026400 := by
  decide

private theorem fastLocalRankBound_exact :
    fastLocalRankBound 153 7289 47 = 3095438528 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 153, rankRow r) = _
  rw [Finset.sum_range_add rankRow 128 25,
    Finset.sum_range_add rankRow 64 64, rank_0, rank_64, rank_128]

theorem localRankBound_exact :
    localRankBound 153 7289 47 = 3095438528 := by
  rw [localRankBound_eq_fastLocalRankBound 153 7289 47 (by decide)]
  exact fastLocalRankBound_exact

theorem nullity_exact :
    coefficientCount 27752976 131071 7289 47 -
      262144 * localRankBound 153 7289 47 = 331640382932 := by
  rw [coefficientCount_exact, localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    331640382932 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    27752976 7289 47 153 331640382932 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSingletonSource
end PackedLocator_LocatorSingletonSource

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelection. -/
section PackedLocator_LocatorSelection
namespace ProximityPrize.SubmissionLower.LocatorSelection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
section GenericCoefficients
variable {E V:Type*} [Field E] [AddCommGroup V] [Module E V]
def polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) :
    V →ₗ[E] (CoefficientIndex D w L s → E) :=
  LinearMap.pi (fun c=> (MvPolynomial.lcoeff E (columnExponent c)).comp f)
@[simp] theorem polynomialCoefficientsLinear_apply (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (c:CoefficientIndex D w L s) :
    polynomialCoefficientsLinear D w L s f v c=
      MvPolynomial.coeff (columnExponent c) (f v):=by
  simp only [polynomialCoefficientsLinear,LinearMap.pi_apply,
    LinearMap.comp_apply,MvPolynomial.lcoeff_apply]
theorem reconstruct_polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (hbox:f v ∈ globalCoefficientBox E D w L s) :
    reconstruct E D w L s (polynomialCoefficientsLinear D w L s f v) =f v:=by
  let Q:globalCoefficientBox E D w L s:=⟨f v,hbox⟩
  have he:polynomialCoefficientsLinear D w L s f v=encodeBox Q:=by
    funext c
    exact polynomialCoefficientsLinear_apply D w L s f v c
  rw [he]
  exact reconstruct_encodeBox Q
theorem reconstruct_add_generic (D w L s:ℕ)
    (a b:CoefficientIndex D w L s → E) :
    reconstruct E D w L s (a + b) =
      reconstruct E D w L s a + reconstruct E D w L s b:=
  (reconstructLinear (K:=E) D w L s).map_add a b
end GenericCoefficients
section GenericJoin
variable {E U V:Type*} [Field E]
 [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
def joinLinear (A:Submodule E U) (f:V →ₗ[E] U):(A × V) →ₗ[E] U:=
  A.subtype.comp (LinearMap.fst E A V) + f.comp (LinearMap.snd E A V)
@[simp] theorem joinLinear_apply (A:Submodule E U) (f:V →ₗ[E] U)
    (v:A × V):joinLinear A f v=v.1.1 + f v.2:=by
  simp only [joinLinear,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,Submodule.subtype_apply]
variable {LeftRest RightRest:Type*} [AddCommGroup LeftRest] [Module E LeftRest]
 [AddCommGroup RightRest] [Module E RightRest]
def tripleLinear (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U) :
    (V × (LeftRest × RightRest)) →ₗ[E] U:=
  f.comp (LinearMap.fst E V (LeftRest × RightRest)) +
    g.comp ((LinearMap.fst E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest))) +
    h.comp ((LinearMap.snd E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest)))
@[simp] theorem tripleLinear_apply
    (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U)
    (v:V × (LeftRest × RightRest)) :
    tripleLinear f g h v=f v.1 + g v.2.1 + h v.2.2:=by
  simp only [tripleLinear,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply]
end GenericJoin
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid P4:=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 16688064 131071 130000 28 92 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 17413632 131071 130000 29 96 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 48975840 131071 130000 81 270 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 32831952 131071 5968 56 181 IRSProfile.domain u0 u1
abbrev SKernel (u0 u1:I → K) :=
  LocatorSingletonSource.Kernel u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20134512 131071 10381 33 111 IRSProfile.domain u0 u1
abbrev Ambient:=CoefficientIndex 48975840 131071 130000 81 → K
theorem gateC:Fintype.card I * localRankBound 270 130000 81 <
    coefficientCount 48975840 131071 130000 81:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorSourceArithmetic.kernelAmbient_nullity
  omega
theorem gateTCap:Fintype.card I * localRankBound 181 5968 56 <
    coefficientCount 32831952 131071 5968 56:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 111 10381 33 <
    coefficientCount 20134512 131071 10381 33:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem aBox_le_cBox:globalCoefficientBox K 16688064 131071 130000 28 ≤
    globalCoefficientBox K 48975840 131071 130000 81:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedA (u0 u1:I → K):AKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 16688064 131071 130000 28 92
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedA (u0 u1:I → K) (v:AKernel u0 u1) :
    reconstruct K 48975840 131071 130000 81 (embedA u0 u1 v) =
      reconstruct K 16688064 131071 130000 28 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 16688064 131071 130000 28 92
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 48975840 131071 130000 81:=by
    rw [kernelReconstructLinear_apply]
    exact aBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 16688064 131071 130000 28 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 16688064 131071 130000 28 92
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedA,kernelReconstructLinear_apply] using h
theorem auxBox_le_cBox:globalCoefficientBox K 17413632 131071 130000 29 ≤
    globalCoefficientBox K 48975840 131071 130000 81:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedAux (u0 u1:I → K):AuxKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 17413632 131071 130000 29 96
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedAux (u0 u1:I → K) (v:AuxKernel u0 u1) :
    reconstruct K 48975840 131071 130000 81 (embedAux u0 u1 v) =
      reconstruct K 17413632 131071 130000 29 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 17413632 131071 130000 29 96
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 48975840 131071 130000 81:=by
    rw [kernelReconstructLinear_apply]
    exact auxBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 17413632 131071 130000 29 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 17413632 131071 130000 29 96
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedAux,kernelReconstructLinear_apply] using h
theorem tcapBox_le_cBox:globalCoefficientBox K 32831952 131071 5968 56 ≤
    globalCoefficientBox K 48975840 131071 130000 81:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩
def embedTCap (u0 u1:I → K):TCapKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 32831952 131071 5968 56 181
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedTCap (u0 u1:I → K) (v:TCapKernel u0 u1) :
    reconstruct K 48975840 131071 130000 81 (embedTCap u0 u1 v) =
      reconstruct K 32831952 131071 5968 56 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 32831952 131071 5968 56 181
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 48975840 131071 130000 81:=by
    rw [kernelReconstructLinear_apply]
    exact tcapBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 32831952 131071 5968 56 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 32831952 131071 5968 56 181
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedTCap,kernelReconstructLinear_apply] using h
theorem sBox_le_cBox:globalCoefficientBox K 27752976 131071 7289 47 ≤
    globalCoefficientBox K 48975840 131071 130000 81:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩
def embedS (u0 u1:I → K):SKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 27752976 131071 7289 47 153
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedS (u0 u1:I → K) (v:SKernel u0 u1) :
    reconstruct K 48975840 131071 130000 81 (embedS u0 u1 v) =
      reconstruct K 27752976 131071 7289 47 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 27752976 131071 7289 47 153
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 48975840 131071 130000 81:=by
    rw [kernelReconstructLinear_apply]
    exact sBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 27752976 131071 7289 47 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 48975840 131071 130000 81
    (kernelReconstructLinear (K:=K) 27752976 131071 7289 47 153
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedS,kernelReconstructLinear_apply] using h
abbrev BaseJoinedDomain (u0 u1:I → K):=
  CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TCapKernel u0 u1))
def baseJoinedMap (u0 u1:I → K) : BaseJoinedDomain u0 u1 →ₗ[K] Ambient:=
  joinLinear (CKernel u0 u1)
    (tripleLinear (embedA u0 u1) (embedAux u0 u1) (embedTCap u0 u1))
@[simp] theorem baseJoinedMap_apply (u0 u1:I → K)
    (v:BaseJoinedDomain u0 u1) :
    baseJoinedMap u0 u1 v=
      v.1.1 +
        (embedA u0 u1 v.2.1 + embedAux u0 u1 v.2.2.1 +
        embedTCap u0 u1 v.2.2.2):=by
  simp only [baseJoinedMap,joinLinear_apply,tripleLinear_apply]
def joinedMap (u0 u1:I → K) :
    (BaseJoinedDomain u0 u1 × SKernel u0 u1) →ₗ[K] Ambient:=
  (baseJoinedMap u0 u1).comp
      (LinearMap.fst K (BaseJoinedDomain u0 u1) (SKernel u0 u1)) +
    (embedS u0 u1).comp
      (LinearMap.snd K (BaseJoinedDomain u0 u1) (SKernel u0 u1))
abbrev JoinedKernel (u0 u1:I → K):=LinearMap.range (joinedMap u0 u1)
@[simp] theorem joinedMap_apply (u0 u1:I → K)
    (v:BaseJoinedDomain u0 u1 × SKernel u0 u1) :
    joinedMap u0 u1 v=
      baseJoinedMap u0 u1 v.1 + embedS u0 u1 v.2:=by
  simp only [joinedMap,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply]
theorem reconstruct_baseJoinedMap (u0 u1:I → K)
    (v:BaseJoinedDomain u0 u1) :
    reconstruct K 48975840 131071 130000 81 (baseJoinedMap u0 u1 v) =
      reconstruct K 48975840 131071 130000 81 v.1.1 +
        (reconstruct K 16688064 131071 130000 28 v.2.1.1 +
          reconstruct K 17413632 131071 130000 29 v.2.2.1.1 +
          reconstruct K 32831952 131071 5968 56 v.2.2.2.1):=by
  rw [baseJoinedMap_apply,reconstruct_add_generic,reconstruct_add_generic,
    reconstruct_add_generic,reconstruct_embedA,reconstruct_embedAux,
    reconstruct_embedTCap]
theorem reconstruct_joinedMap (u0 u1:I → K)
    (v:BaseJoinedDomain u0 u1 × SKernel u0 u1) :
    reconstruct K 48975840 131071 130000 81 (joinedMap u0 u1 v) =
      (reconstruct K 48975840 131071 130000 81 v.1.1.1 +
        (reconstruct K 16688064 131071 130000 28 v.1.2.1.1 +
          reconstruct K 17413632 131071 130000 29 v.1.2.2.1.1 +
          reconstruct K 32831952 131071 5968 56 v.1.2.2.2.1)) +
        reconstruct K 27752976 131071 7289 47 v.2.1:=by
  rw [joinedMap_apply,reconstruct_add_generic,reconstruct_baseJoinedMap,
    reconstruct_embedS]
def includeC (u0 u1:I → K) (v:CKernel u0 u1):JoinedKernel u0 u1:=
  ⟨v.1, ⟨((v, (0, (0,0))),0),by
    simp only [joinedMap_apply,baseJoinedMap_apply,map_zero,zero_add,add_zero]⟩⟩
def includeA (u0 u1:I → K) (v:AKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedA u0 u1 v, ⟨((0, (v, (0,0))),0),by
    simp only [joinedMap_apply,baseJoinedMap_apply,ZeroMemClass.coe_zero,map_zero,
      zero_add,add_zero]⟩⟩
def includeAux (u0 u1:I → K) (v:AuxKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedAux u0 u1 v, ⟨((0, (0, (v,0))),0),by
    simp only [joinedMap_apply,baseJoinedMap_apply,ZeroMemClass.coe_zero,map_zero,
      zero_add,add_zero]⟩⟩
def includeTCap (u0 u1:I → K) (v:TCapKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedTCap u0 u1 v, ⟨((0, (0, (0,v))),0),by
    simp only [joinedMap_apply,baseJoinedMap_apply,ZeroMemClass.coe_zero,map_zero,
      zero_add,add_zero]⟩⟩
def includeS (u0 u1:I → K) (v:SKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedS u0 u1 v, ⟨((0, (0, (0,0))),v),by
    simp only [joinedMap_apply,baseJoinedMap_apply,ZeroMemClass.coe_zero,map_zero,
      zero_add,add_zero]⟩⟩
theorem joined_universal (u0 u1:I → K) (v:JoinedKernel u0 u1)
    (gamma:K) (P:Polynomial K) (points:Finset I)
    (hP:P.natDegree ≤ 131071) (hcard:181392 ≤ points.card)
    (hvalues:∀ i ∈ points,
      P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (reconstruct K 48975840 131071 130000 81 v.1) =0:=by
  obtain ⟨z,hz⟩:=v.2
  rw [← hz,reconstruct_joinedMap,map_add,map_add,map_add,map_add]
  have hc:=specialization_eq_zero_of_agreements K
    48975840 131071 130000 81 270 181392 IRSProfile.domain u0 u1
    z.1.1.1 z.1.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have ha:=specialization_eq_zero_of_agreements K
    16688064 131071 130000 28 92 181392 IRSProfile.domain u0 u1
    z.1.2.1.1 z.1.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have haux:=specialization_eq_zero_of_agreements K
    17413632 131071 130000 29 96 181392 IRSProfile.domain u0 u1
    z.1.2.2.1.1 z.1.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have htcap:=specialization_eq_zero_of_agreements K
    32831952 131071 5968 56 181 181392 IRSProfile.domain u0 u1
    z.1.2.2.2.1 z.1.2.2.2.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have hs:=specialization_eq_zero_of_agreements K
    27752976 131071 7289 47 153 181392 IRSProfile.domain u0 u1
    z.2.1 z.2.2 (by decide) (by decide) P gamma points hP hcard hvalues
  rw [specialization_eq_ordinary] at ha haux hc htcap hs
  simp only [hc,ha,haux,htcap,hs,zero_add]
private theorem gcd_mul_right_plain_associated
    (P H q:P4) (hc:IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
    have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
    have hcop:IsRelPrime (gcd P (H * q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
    (H q P:P4) (hc:IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
    have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
    have hcop:IsRelPrime (gcd (H * q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)
structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ globalCoefficientBox K 32831952 131071 5968 56
  QB_flag:QB ∈ globalCoefficientBox K 20134512 131071 10381 33
  common_divides_TCap:∀ v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 32831952 131071 5968 56 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 20134512 131071 10381 33 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181392 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaT,htT,hkT⟩:=exists_nonzero_kernel_array (I:=I)
    K 32831952 131071 5968 56 181 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 20134512 131071 10381 33 111 IRSProfile.domain u0 u1 gateB
  let vT0:TCapKernel u0 u1:=⟨thetaT,LinearMap.mem_ker.mpr hkT⟩
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (TCapKernel u0 u1):=⟨⟨vT0,0,by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT:=Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Module.Finite.finite_basis bT
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=bT.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HT:=commonGCD (TCapKernel u0 u1) bT
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHT:HT ≠ 0:=commonGCD_ne_zero (TCapKernel u0 u1) bT
  have hHB:HB ≠ 0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB ∈ globalCoefficientBox K 20134512 131071 10381 33:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 20134512 10381 33
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA:=commonQuotientLinear (TCapKernel u0 u1) bT hHT vA
  let QA:=submoduleReconstructLinear (TCapKernel u0 u1) vA
  have hQAeq:QA=HT * qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (TCapKernel u0 u1)) HT
    (commonDivisorProof (TCapKernel u0 u1) bT) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (TCapKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ globalCoefficientBox K 32831952 131071 5968 56:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 32831952 131071 5968 56 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 32831952 5968 56
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB:=submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq:QB=HB * qB:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB:QB ≠ 0:=by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB ∈ globalCoefficientBox K 20134512 131071 10381 33:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 20134512 131071 10381 33 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HT HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HT qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHT:gcd QA QB ∣ HT:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_TCap:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    exact hHHT.trans (commonGCD_dvd (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        32831952 131071 5968 56 181 181392 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide) (by decide) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        20134512 131071 10381 33 111 181392 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.LocatorSelection
end PackedLocator_LocatorSelection

/-! Packed from ProximityPrize.SubmissionLower.LocatorCaps. -/
section PackedLocator_LocatorCaps
namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 16688064 131071 130000 28 92 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 32831952 131071 5968 56 181 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20134512 131071 10381 33 111 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 92 130000 28 <
    coefficientCount 16688064 131071 130000 28:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateTCap:Fintype.card I * localRankBound 181 5968 56 <
    coefficientCount 32831952 131071 5968 56:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 111 10381 33 <
    coefficientCount 20134512 131071 10381 33:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem full_divisor_mem_box (D w L s m:ℕ)
    (gate:Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1:I → K) (F:P4)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1) :
    F ∈ globalCoefficientBox K D w L s:=by
  classical
  obtain ⟨a,ha,hk⟩:=exists_nonzero_kernel_array (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a ≠ 0:=reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)
theorem full_A_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    F ∈ globalCoefficientBox K 16688064 131071 130000 28:=
  full_divisor_mem_box 16688064 131071 130000 28 92 gateA u0 u1 F hdiv
theorem full_TCap_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 32831952 131071 5968 56 v.1) :
    F ∈ globalCoefficientBox K 32831952 131071 5968 56:=
  full_divisor_mem_box 32831952 131071 5968 56 181 gateTCap u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    F ∈ globalCoefficientBox K 20134512 131071 10381 33:=
  full_divisor_mem_box 20134512 131071 10381 33 111 gateB u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    wt residualYSWeights F ≤ 127:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    16688064 131071 130000 28 (by decide)).mp hbox
  have hr:wt residualSWeights F ≤ 28:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:wt (contactWeights 131071) F ≤ 16688064:=by omega
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    wt residualSWeights F ≤ 28:=
  ((mem_flagGlobalCoefficientBox_iff F 16688064 131071 130000 28 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    wt residualSWeights F ≤ 33:=
  ((mem_flagGlobalCoefficientBox_iff F 20134512 131071 10381 33 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    wt residualYSWeights F ≤ 153:=by
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    20134512 131071 10381 33 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr:wt residualSWeights F ≤ 33:=hcaps.2.1
  have hc:wt (contactWeights 131071) F ≤ 20134512 - 1:=hcaps.2.2
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  omega
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 32831952 131071 5968 56 v.1) :
    wt residualTotalWeights F ≤ 5964:=by
  by_contra hnot
  have ht:5965 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        32831952 131071 5968 56 181 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          32831952 131071 5968 56 181 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 32831952 131071 3 56:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      32831952 131071 5968 56 181 0 5965 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 5968 - 5965=3 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    32831952 131071 5968 56 181 32831952 3 56
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelTCap_total_quotient_lt
end
end LocatorCaps
end ProximityPrize.SubmissionLower
end PackedLocator_LocatorCaps

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelectedCaps. -/
section PackedLocator_LocatorSelectedCaps
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 5964:=
  LocatorCaps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 153:=
  LocatorCaps.common_B_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 33:=
  LocatorCaps.common_B_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
end PackedLocator_LocatorSelectedCaps

/-! Packed from ProximityPrize.SubmissionLower.LocatorCover. -/
section PackedLocator_LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I:Type*} [CommRing R] [GCDMonoid R]
 [CommRing S] [IsDomain S]
local instance:DecidableEq S:=Classical.decEq S
local instance:DecidableEq I:=Classical.decEq I
theorem quotient_vanish (phi:R →+* S) (a b:R)
    (ha:phi a = 0) (hb:phi b = 0) (hg:phi (gcd12 a b) ≠ 0) :
    phi (quotientA a b) = 0 ∧ phi (quotientB a b) = 0:=by
  rw [a_eq_gcd12_mul_quotientA a b, map_mul] at ha
  rw [b_eq_gcd12_mul_quotientB a b, map_mul] at hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hg, (mul_eq_zero.mp hb).resolve_left hg⟩
def fixed (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) = 0)
def residual (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) ≠ 0)
theorem partition_card (phi:I → R →+* S) (seeds:Finset I) (a b:R) :
    (fixed phi seeds a b).card + (residual phi seeds a b).card = seeds.card:=by
  classical
  simpa only [fixed, residual] using
    Finset.card_filter_add_card_filter_not (s:=seeds)
      (fun i => phi i (gcd12 a b) = 0)
theorem fixed_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (i:I) (hi:i ∈ fixed phi seeds a b):phi i (gcd12 a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) = 0:=by
    simpa only [fixed, Finset.mem_filter] using hi
  exact hm.2
theorem residual_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (ha:∀ i ∈ seeds, phi i a = 0) (hb:∀ i ∈ seeds, phi i b = 0)
    (i:I) (hi:i ∈ residual phi seeds a b) :
    phi i (quotientA a b) = 0 ∧ phi i (quotientB a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) ≠ 0:=by
    simpa only [residual, Finset.mem_filter] using hi
  exact quotient_vanish (phi i) a b (ha i hm.1) (hb i hm.1) hm.2
end
end ProximityPrize.SubmissionLower.LocatorCover
end PackedLocator_LocatorCover

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedBridge. -/
section PackedLocator_LocatorFixedBridge

/-!
# Initial A-source bridge for the wide selected gcd

The selected TCap/B pair only puts its gcd in the wide box
`(total,ys,slope)=(5964,153,33)`.  Split its regular factors on the independent
A kernel.  Nonuniversal factors get the direct `pairCost(F,A)` bound;
universal factors inherit A's narrow `(ys,slope)=(127,28)` caps.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

/-- Exact direct helper charge for one factor exiting at the A source. -/
def initialAHelperCap (p:FlagDegree):ℕ:=
  (LocatorGenericHelperFactorSwitch.helperPair
    130000 127 28 (middle p) p.all (total p)).regularCountCap

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):LocatorCaps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 16688064 131071 130000 28 92
    IRSProfile.domain u0 u1

/-- Factors universal on the current A source. -/
def initialAUniversalFactors (u0 u1:I → K) (H:P4):
    Finset (RegularIndex H):=
  universalFactors H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1:I → K) (H:P4) (F:RegularIndex H):
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v:LocatorCaps.AKernel u0 u1,
        F.1 ∣ reconstruct K 16688064 131071 130000 28 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:LocatorCaps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 16688064 131071 130000 28 v.1:=by
  intro v
  have h:=universalProduct_dvd H
    (Finset.univ:Finset (RegularIndex H)) (initialAMap u0 u1) v
  simpa only [initialAUniversalFactors,initialAMap,
    kernelReconstructLinear_apply] using h

/-- The same universal product divides the selected carrier. -/
theorem initialAUniversalProduct_dvd_carrier
    (u0 u1:I → K) (H:P4):
    regularProduct H (initialAUniversalFactors u0 u1 H) ∣ H:=
  regularProduct_dvd_carrier H (initialAUniversalFactors u0 u1 H)

private theorem degreeY_le_ysWeight (Q:P4):
    Q.degreeOf (1:Fin 4) ≤ wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0 ≤ wt residualYSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q:P4):
    Q.degreeOf (3:Fin 4) ≤ wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1 ≤ wt residualTotalWeights Q at h
  omega

private theorem initialA_helper_gates (p:FlagDegree)
    (hr:1 ≤ p.all) (hs:p.all ≤ 33)
    (hy:middle p ≤ 153) (ht:total p ≤ 5964):
    LocatorGenericHelperFactorSwitch.HelperPairGates
      130000 127 28 (middle p) p.all (total p):=by
  unfold LocatorGenericHelperFactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*130000+total p*28 < 2130706433 ∧
    middle p*130000+total p*127 < 2130706433 ∧
    middle p*28+p.all*127 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData LocatorFixedConsumer.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=LocatorFixed.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 33:=by
    simpa only [regularCumulativeFlag,hc.1,LocatorFixedConsumer.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 153:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      LocatorFixedConsumer.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 5964:=by
    simpa only [regularCumulativeFlag,total,hc.2.2,
      LocatorFixedConsumer.wideSupport] using hFsupport.total_weight
  have hr:1 ≤ (regularCumulativeFlag H F).all:=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
  have hFY:F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,middle,hc.2.1]
    exact degreeY_le_ysWeight F.1
  have hFR:F.1.degreeOf 2 ≤ (regularCumulativeFlag H F).all:=by
    rw [regularCumulativeFlag,originalCumulativeFlag_all]
  have hFZ:F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,total,hc.2.2]
    exact degreeZ_le_totalWeight F.1
  rcases LocatorGenericHelperFactorSwitch.divisor_or_helper_count
      16688064 130000 28 92 127 (by decide) (by decide) (by decide)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount

/-- An A-universal factor has a narrow own-bound even though the whole
selected gcd is wide. -/
theorem initialA_universal_ownBound
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hTotal:wt residualTotalWeights H ≤ 5964)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F):=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:LocatorCaps.AKernel u0 u1,
      F.1 ∣ reconstruct K 16688064 131071 130000 28 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=LocatorCaps.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    16688064 131071 130000 28 (by decide)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 5964:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 127:=
    LocatorCaps.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 28:=
    LocatorCaps.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 16688064 131071 5964 28:=
    (mem_flagGlobalCoefficientBox_iff F.1
      16688064 131071 5964 28 (by decide)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 16688064 131071 5964 28 F.1 hFflag
  have hFsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hown:=LocatorFixedOwnBound.regular_factor_own_bound 16688064
    LocatorFixedConsumer.wholeSupport (by decide) (by decide)
    (by decide) (by decide) (by decide)
    F.1 hF.1.ne_zero hFbox hFsupport selected Gamma u0 u1
    hdegree hagreement hno Fself LocatorHybridRealize.realization
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hown

/-! ## Wide selected-gcd bridge with a replaceable numerical receipt -/

/-- Algebraic bridge to the phase-potential certificate.  `hphase` bounds
the A-universal child; `hledger` combines it with the exact direct-A charges
of all factors that exit at this first split. -/
theorem gcd_fixed_count_le_of_initial_phase
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (phaseCap:ℕ)
    (hphase:
      let H:P4:=gcd12 S.QA S.QB
      let phi:K → P4 →+* Polynomial K:=
        fun gamma=>(specialization K (selected gamma) gamma).toRingHom
      let Delta:=LocatorCover.fixed phi Gamma S.QA S.QB
      let U:=initialAUniversalFactors u0 u1 H
      (∑ F ∈ U,(regularSeeds H selected Delta F).card) ≤ phaseCap)
    (hledger:
      let H:P4:=gcd12 S.QA S.QB
      let U:=initialAUniversalFactors u0 u1 H
      phaseCap+(∑ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
        initialAHelperCap (regularCumulativeFlag H F)) ≤
          LocatorFixedConsumer.initialRegularCap):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap+
        LocatorArithmetic.fixedSingularCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+* Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  let U:=initialAUniversalFactors u0 u1 H
  have hH:H ≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hBflag:H ∈ globalCoefficientBox K 20134512 131071 10381 33:=
    LocatorCaps.full_B_divisor_mem_box u0 u1 H hH S.common_divides_B
  have hBcaps:=(mem_flagGlobalCoefficientBox_iff H
    20134512 131071 10381 33 (by decide)).mp hBflag
  have hT:wt residualTotalWeights H ≤ 5964:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 153:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 33:=S.common_slope_le
  have hflag:H ∈ globalCoefficientBox K 20134512 131071 5964 33:=
    (mem_flagGlobalCoefficientBox_iff H
      20134512 131071 5964 33 (by decide)).mpr ⟨hT,hS,hBcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 20134512 131071 5964 33 H hflag
  have hwide:ResidualSupportData LocatorFixedConsumer.wideSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma ∈ Gamma ∧ (phi gamma) (gcd12 S.QA S.QB)=0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma ∈ Delta,(selected gamma).natDegree ≤ 131071:=
    fun gamma hg=>hdegree gamma (hsub hg)
  have hagreementD:∀ gamma ∈ Delta,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80752:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80752 hsub hno
  have hN:∀ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
      (regularSeeds H selected Delta F).card ≤
        initialAHelperCap (regularCumulativeFlag H F):=by
    intro F hFN
    apply initialA_nonuniversal_count u0 u1 H hH hwide selected Delta
      hdegreeD hagreementD hnoD F
    exact (Finset.mem_sdiff.mp hFN).2
  have hreg:(∑ F:RegularIndex H,
      (regularSeeds H selected Delta F).card) ≤
        LocatorFixedConsumer.initialRegularCap:=by
    apply LocatorFixedConsumer.initial_A_regularSeeds_sum_le H selected Delta
      U phaseCap (fun F => initialAHelperCap (regularCumulativeFlag H F))
    · simpa only [H,phi,Delta,U] using hphase
    · exact hN
    · simpa only [H,U] using hledger
  exact LocatorFixedConsumer.wide_fixed_count_le H hH hbox selected Delta u0 u1
    hsolution hdegreeD hagreementD hnoD hreg

end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
end PackedLocator_LocatorFixedBridge

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Bridge. -/
section PackedLocator_LocatorPhase6800Bridge

/-!
# Correlated initial-A bridge for the 6800 phase certificate

This file turns a state-local narrow phase bound into the exact two-piece
ledger required by `LocatorFixedBridge`.  The aggregate flag of the
A-universal factors is retained in both terms; no independent maxima are
taken.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Bridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN259 RCN260 RCN266 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchProductRoute
  LocatorBatchPhase6800 LocatorPhase6800Oracle LocatorFixedBridge

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

private theorem whole_regular_total_le
    (H : P4) (hH : H ≠ 0) (T : ℕ)
    (hT : wt residualTotalWeights H ≤ T) :
    total (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))) ≤ T := by
  rw [regularAggregateFlag_total]
  exact (weightedTotalDegree_le_of_dvd residualTotalWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hT

private theorem whole_regular_middle_le
    (H : P4) (hH : H ≠ 0) (YS : ℕ)
    (hYS : wt residualYSWeights H ≤ YS) :
    middle (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))) ≤ YS := by
  rw [regularAggregateFlag_middle]
  exact (weightedTotalDegree_le_of_dvd residualYSWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hYS

private theorem whole_regular_all_le
    (H : P4) (hH : H ≠ 0) (S : ℕ)
    (hS : wt residualSWeights H ≤ S) :
    (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))).all ≤ S := by
  rw [regularAggregateFlag_all]
  exact (weightedTotalDegree_le_of_dvd residualSWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hS

/-- Structural completion of the initial A split.  The numerical proof only
has to provide a state-local phase cap, the analytic A-helper majorant, and
the correlated final ledger at the same aggregate flag. -/
theorem gcd_fixed_count_le_of_stateLocalPhase
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (phaseCap : FlagDegree → ℕ)
    (hphase :
      let H : P4 := gcd12 S.QA S.QB
      let phi : K → P4 →+* Polynomial K :=
        fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
      let Delta := LocatorCover.fixed phi Gamma S.QA S.QB
      let U := initialAUniversalFactors u0 u1 H
      StateLocalRegularBoundOn H selected Delta U phaseCap)
    (hAhelper : ∀ p : FlagDegree,
      1 ≤ p.all → p.all ≤ 33 → middle p ≤ 153 → total p ≤ 5964 →
      initialAHelperCap p ≤ initialAPotential.eval p)
    (hjoint : ∀ p : FlagDegree,
      p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
      phaseCap p + initialAComplement p ≤
        LocatorFixedConsumer.initialRegularCap) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap +
        LocatorArithmetic.fixedSingularCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  let A := (Finset.univ : Finset (RegularIndex H))
  let N := A \ U
  let p := regularAggregateFlag H U
  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hUsub : U ⊆ A := fun _ _ ↦ Finset.mem_univ _
  have hPne : regularProduct H U ≠ 0 := regularProduct_ne_zero H U
  have hdivA : ∀ v : LocatorCaps.AKernel u0 u1,
      regularProduct H U ∣
        reconstruct K 16688064 131071 130000 28 v.1 := by
    simpa only [U] using initialAUniversalProduct_dvd u0 u1 H
  have hpS : p.all ≤ 28 := by
    simp only [p, regularAggregateFlag_all]
    exact LocatorCaps.common_A_slope_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpY : middle p ≤ 127 := by
    simp only [p, regularAggregateFlag_middle]
    exact LocatorCaps.common_A_ys_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpT : total p ≤ 5964 := by
    simp only [p, regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H U) H
      (initialAUniversalProduct_dvd_carrier u0 u1 H) hH).trans
        S.common_total_le
  have hwholeT : total (regularAggregateFlag H A) ≤ 5964 := by
    simpa only [H, A] using
      whole_regular_total_le H hH 5964 S.common_total_le
  have hwholeY : middle (regularAggregateFlag H A) ≤ 153 := by
    simpa only [H, A] using
      whole_regular_middle_le H hH 153 S.common_ys_le
  have hwholeS : (regularAggregateFlag H A).all ≤ 33 := by
    simpa only [H, A] using
      whole_regular_all_le H hH 33 S.common_slope_le
  have hsplitT := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => total (regularCumulativeFlag H F))
  have hsplitY := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => middle (regularCumulativeFlag H F))
  have hsplitS := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => (regularCumulativeFlag H F).all)
  have hcomplementT : total p +
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 5964 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        5964 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 5964
    omega
  have hcomplementY : middle p +
      (∑ F ∈ N, middle (regularCumulativeFlag H F)) ≤ 153 := by
    have hpEq : middle p =
        ∑ F ∈ U, middle (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_middle]
    have hwhole : (∑ F ∈ A, middle (regularCumulativeFlag H F)) ≤
        153 := by
      simpa only [regularAggregateFlag, sumFlag_middle] using hwholeY
    rw [hpEq]
    change (∑ F ∈ U, middle (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, middle (regularCumulativeFlag H F)) ≤ 153
    omega
  have hcomplementS : p.all +
      (∑ F ∈ N, (regularCumulativeFlag H F).all) ≤ 33 := by
    have hpEq : p.all =
        ∑ F ∈ U, (regularCumulativeFlag H F).all := by
      simp only [p, regularAggregateFlag, sumFlag_all]
    have hwhole : (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤ 33 := by
      simpa only [regularAggregateFlag, sumFlag_all] using hwholeS
    rw [hpEq]
    change (∑ F ∈ U, (regularCumulativeFlag H F).all) +
      (∑ F ∈ A \ U, (regularCumulativeFlag H F).all) ≤ 33
    omega
  have hNpotential : ∀ F ∈ N,
      initialAHelperCap (regularCumulativeFlag H F) ≤
        initialAPotential.eval (regularCumulativeFlag H F) := by
    intro F hFN
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFN).1
    have hsingle : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    have hmono := regularAggregateFlag_mono H hsingle
    have hr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    apply hAhelper (regularCumulativeFlag H F) hr
    · simpa [regularAggregateFlag, sumFlag] using hmono.1.trans hwholeS
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.1.trans hwholeY
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.2.trans hwholeT
  have hhelperSum :
      (∑ F ∈ N, initialAHelperCap (regularCumulativeFlag H F)) ≤
        initialAComplement p := by
    exact initialA_helpers_sum_le_complement N (regularCumulativeFlag H)
      (fun F ↦ initialAHelperCap (regularCumulativeFlag H F)) p
      hNpotential hcomplementT hcomplementY hcomplementS
  have hphaseU :
      (∑ F ∈ U, (regularSeeds H selected Delta F).card) ≤ phaseCap p := by
    have hp := hphase U (fun _ hFU ↦ hFU) hpS hpY hpT
    simpa only [H, phi, Delta, p, U] using hp
  apply gcd_fixed_count_le_of_initial_phase u0 u1 S selected Gamma
    hdegree hagreement hno (phaseCap p)
  · simpa only [H, phi, Delta, U, p] using hphaseU
  · have hfinal := Nat.add_le_add_left hhelperSum (phaseCap p)
    exact (hfinal.trans (hjoint p hpS hpY hpT))

end

end ProximityPrize.SubmissionLower.LocatorPhase6800Bridge
end PackedLocator_LocatorPhase6800Bridge

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Composition. -/
section PackedLocator_LocatorPhase6800Composition

/-!
# Final composition interface for the 6800 regular-factor certificate

The generated files only need to instantiate `PhasePrefixCertificate`.
Everything from those state-local tables through the four fresh-source
algebraic phases and the correlated initial-A split is composed here.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Composition

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180
  RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchPhase6800
  LocatorPhase6800Oracle LocatorPhase6800Audit LocatorPhase6800Kernels
  LocatorPhase6800SourceSound LocatorPhase6800Bridge LocatorFixedBridge

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

def afterR1200 (base pref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase base r1200Potential sourceR1200.Routeable pref

def afterSourceC (base rPref cPref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase (afterR1200 base rPref) sourceCPotential
    sourceC.Routeable cPref

def afterSplit500 (base rPref cPref fPref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSourceC base rPref cPref) split500Potential
    sourceSplit500.Routeable fPref

def afterSplit390 (base rPref cPref fPref sPref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSplit500 base rPref cPref fPref) split390Potential
    sourceSplit390.Routeable sPref

/-- Semantic payload produced by the compact generated receipt. -/
structure PhasePrefixCertificate where
  baseCap : FlagDegree → ℕ
  rPrefix : FlagDegree → ℕ
  cPrefix : FlagDegree → ℕ
  f500Prefix : FlagDegree → ℕ
  s390Prefix : FlagDegree → ℕ
  baseSound : StateLocalBaseOracleSound baseCap
  rRows : PrefixTableSound baseCap r1200Potential
    sourceR1200.Routeable rPrefix
  cRows : PrefixTableSound (afterR1200 baseCap rPrefix) sourceCPotential
    sourceC.Routeable cPrefix
  f500Rows : PrefixTableSound (afterSourceC baseCap rPrefix cPrefix)
    split500Potential sourceSplit500.Routeable f500Prefix
  s390Rows : PrefixTableSound
    (afterSplit500 baseCap rPrefix cPrefix f500Prefix)
    split390Potential sourceSplit390.Routeable s390Prefix
  joint : ∀ p : FlagDegree,
    p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    afterSplit390 baseCap rPrefix cPrefix f500Prefix s390Prefix p +
      initialAComplement p ≤ LocatorFixedConsumer.initialRegularCap

private theorem defectSound_of_prefix
    (previous pref : FlagDegree → ℕ) (q : Potential) (s : SourceNumbers)
    (hrows : PrefixTableSound previous q s.Routeable pref) :
    PhaseDefectSound previous s q (parentDefect pref) := by
  intro parent child _hs _hy _ht hstrict hterminal
  exact terminal_le_parent_charge hrows hstrict.1 hstrict.2 hterminal

private theorem capEquation_applyPhase
    (previous pref : FlagDegree → ℕ) (q : Potential) (s : SourceNumbers) :
    PhaseCapEquation previous
      (applyPhase previous q s.Routeable pref) s q (parentDefect pref) := by
  intro p _hs _hy _ht
  rfl

/-- Four checked prefix tables give the state-local phase bound on exactly
the ambient factors supplied by the initial A split. -/
theorem PhasePrefixCertificate.stateLocalBoundOn
    (cert : PhasePrefixCertificate)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    StateLocalRegularBoundOn H selected Gamma ambient
      (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix
        cert.f500Prefix cert.s390Prefix) := by
  apply stateLocalRegularBoundOn_fourPhases u0 u1 H selected Gamma ambient
    hdegree hagreement hno cert.baseCap
    (afterR1200 cert.baseCap cert.rPrefix)
    (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix)
    (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
    (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.s390Prefix)
    (parentDefect cert.rPrefix) (parentDefect cert.cPrefix)
    (parentDefect cert.f500Prefix) (parentDefect cert.s390Prefix)
    hown cert.baseSound
  · exact defectSound_of_prefix cert.baseCap cert.rPrefix r1200Potential
      sourceR1200 cert.rRows
  · exact capEquation_applyPhase cert.baseCap cert.rPrefix r1200Potential
      sourceR1200
  · exact defectSound_of_prefix
      (afterR1200 cert.baseCap cert.rPrefix) cert.cPrefix sourceCPotential
      sourceC cert.cRows
  · exact capEquation_applyPhase
      (afterR1200 cert.baseCap cert.rPrefix) cert.cPrefix sourceCPotential
      sourceC
  · exact defectSound_of_prefix
      (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix) cert.f500Prefix
      split500Potential sourceSplit500 cert.f500Rows
  · exact capEquation_applyPhase
      (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix) cert.f500Prefix
      split500Potential sourceSplit500
  · exact defectSound_of_prefix
      (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
      cert.s390Prefix split390Potential sourceSplit390 cert.s390Rows
  · exact capEquation_applyPhase
      (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
      cert.s390Prefix split390Potential sourceSplit390

/-- End-to-end fixed-part theorem.  Once the generated receipt constructs a
`PhasePrefixCertificate`, no algebraic or combinatorial premises remain. -/
theorem gcd_fixed_count_le_of_certificate
    (cert : PhasePrefixCertificate)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap +
        LocatorArithmetic.fixedSingularCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hsub : Delta ⊆ Gamma := by
    intro gamma hgamma
    have hm : gamma ∈ Gamma ∧
        phi gamma (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hgamma
    exact hm.1
  have hdegreeD : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
  have hagreementD : ∀ gamma ∈ Delta, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hsub hgamma)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80752 :=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80752 hsub hno
  have hown : ∀ F ∈ U, LocatorHybridCost.OwnBound
      (regularSeeds H selected Delta F).card
      (regularCumulativeFlag H F) := by
    intro F hFU
    exact initialA_universal_ownBound u0 u1 H hH S.common_total_le
      selected Delta hdegreeD hagreementD hnoD F hFU
  have hphase := cert.stateLocalBoundOn u0 u1 H selected Delta U
    hdegreeD hagreementD hnoD hown
  apply gcd_fixed_count_le_of_stateLocalPhase u0 u1 S selected Gamma
    hdegree hagreement hno
    (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.s390Prefix)
  · simpa only [H, phi, Delta, U] using hphase
  · intro p hr hs hy ht
    simpa only [initialAHelperCap] using
      initialAHelperCap_le_potential p hr hs hy ht
  · exact cert.joint

end

end ProximityPrize.SubmissionLower.LocatorPhase6800Composition
end PackedLocator_LocatorPhase6800Composition

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore. -/
section PackedLocator_LocatorPhase6800ReceiptCellCore

/-! Lightweight predicates for independently checked receipt cells. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore

open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

def defaultThreshold : ThresholdReceipt := ⟨0, 0, 0, 0, 0, 0⟩
def defaultPrefix : PrefixReceipt := ⟨0, 0, 0, [], 0, 0⟩

/-- It is enough for the stored cutoff to be outside the benchmark row, or
for the source to be routeable at the cutoff.  Routeability is monotone in
the raw `z` coordinate, so no false-boundary computation is needed. -/
def SourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  5964 - (r + v) < threshold ∨ s.Routeable (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (SourceThresholdSufficient s r v threshold) := by
  unfold SourceThresholdSufficient
  infer_instance

def ThresholdSufficient (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 28 ∧ q.r + q.v ≤ 127 ∧
    SourceThresholdSufficient sourceR1200 q.r q.v q.r1200 ∧
    SourceThresholdSufficient LocatorPhase6800Oracle.sourceC q.r q.v q.sourceC ∧
    SourceThresholdSufficient sourceSplit500 q.r q.v q.split500 ∧
    SourceThresholdSufficient sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable (ThresholdSufficient q) := by
  unfold ThresholdSufficient
  infer_instance

def ThresholdAtOf (row : ℕ → ThresholdReceipt) (R V : ℕ) : Prop :=
  let q := row V
  q.r = R ∧ q.v = V ∧ ThresholdSufficient q

instance (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    Decidable (ThresholdAtOf row R V) := by
  unfold ThresholdAtOf
  infer_instance

def prefixSentinel : ℕ := 1000000000000000000000

def rCoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).r1200
def f500CoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).split500
def s390CoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).split390

def cAtOf (row : ℕ → PrefixReceipt) (v bucket : ℕ) : ℕ :=
  let q := row v
  if q.sourceC.length = 1 then q.sourceC.head?.getD prefixSentinel
  else (q.sourceC[bucket]?).getD prefixSentinel

def PrefixCoreAtOf (row nextRow : ℕ → PrefixReceipt) (R V : ℕ) : Prop :=
  rCoreOf row V ≤ prefixSentinel ∧
  f500CoreOf row V ≤ prefixSentinel ∧
  s390CoreOf row V ≤ prefixSentinel ∧
  (∀ b ∈ List.range 21, cAtOf row V b ≤ prefixSentinel) ∧
  (R + 1 ≤ 27 ∧ R + 1 + 1 + V ≤ 127 →
    rCoreOf row V ≤ rCoreOf nextRow V ∧
    f500CoreOf row V ≤ f500CoreOf nextRow V ∧
    s390CoreOf row V ≤ s390CoreOf nextRow V ∧
    ∀ b ∈ List.range 21, cAtOf row V b ≤ cAtOf nextRow V b) ∧
  (R + 1 + (V + 1) ≤ 127 →
    rCoreOf row V ≤ rCoreOf row (V + 1) ∧
    f500CoreOf row V ≤ f500CoreOf row (V + 1) ∧
    s390CoreOf row V ≤ s390CoreOf row (V + 1) ∧
    ∀ b ∈ List.range 21, cAtOf row V b ≤ cAtOf row (V + 1) b) ∧
  (∀ b ∈ List.range 20, cAtOf row V b ≤ cAtOf row V (b + 1))

instance (row nextRow : ℕ → PrefixReceipt) (R V : ℕ) :
    Decidable (PrefixCoreAtOf row nextRow R V) := by
  unfold PrefixCoreAtOf
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore
end PackedLocator_LocatorPhase6800ReceiptCellCore

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01. -/
section PackedLocator_LocatorPhase6800ReceiptRowData01

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨1, 0, 4254, 5964, 3634, 4069⟩
  | 1 => ⟨1, 1, 4235, 5963, 3621, 4053⟩
  | 2 => ⟨1, 2, 4216, 5962, 3609, 4038⟩
  | 3 => ⟨1, 3, 4197, 5961, 3596, 4022⟩
  | 4 => ⟨1, 4, 4178, 5960, 3583, 4006⟩
  | 5 => ⟨1, 5, 4158, 5959, 3570, 3990⟩
  | 6 => ⟨1, 6, 4138, 5958, 3556, 3974⟩
  | 7 => ⟨1, 7, 4117, 5957, 3543, 3958⟩
  | 8 => ⟨1, 8, 4097, 5956, 3529, 3941⟩
  | 9 => ⟨1, 9, 4075, 5955, 3516, 3924⟩
  | 10 => ⟨1, 10, 4054, 5954, 3502, 3907⟩
  | 11 => ⟨1, 11, 4034, 5953, 3488, 3890⟩
  | 12 => ⟨1, 12, 4013, 5952, 3473, 3872⟩
  | 13 => ⟨1, 13, 3992, 5951, 3459, 3856⟩
  | 14 => ⟨1, 14, 3970, 5950, 3446, 3840⟩
  | 15 => ⟨1, 15, 3948, 5949, 3433, 3825⟩
  | 16 => ⟨1, 16, 3926, 5948, 3420, 3811⟩
  | 17 => ⟨1, 17, 3903, 5947, 3408, 3797⟩
  | 18 => ⟨1, 18, 3880, 5946, 3396, 3783⟩
  | 19 => ⟨1, 19, 3857, 5945, 3384, 3770⟩
  | 20 => ⟨1, 20, 3834, 5944, 3372, 3756⟩
  | 21 => ⟨1, 21, 3811, 5943, 3360, 3742⟩
  | 22 => ⟨1, 22, 3787, 5942, 3348, 3728⟩
  | 23 => ⟨1, 23, 3763, 5941, 3335, 3713⟩
  | 24 => ⟨1, 24, 3738, 5940, 3323, 3698⟩
  | 25 => ⟨1, 25, 3713, 5939, 3310, 3683⟩
  | 26 => ⟨1, 26, 3687, 5938, 3297, 3668⟩
  | 27 => ⟨1, 27, 3661, 5937, 3283, 3652⟩
  | 28 => ⟨1, 28, 3635, 5936, 3270, 3636⟩
  | 29 => ⟨1, 29, 3609, 5935, 3256, 3620⟩
  | 30 => ⟨1, 30, 3582, 5934, 3242, 3603⟩
  | 31 => ⟨1, 31, 3554, 5933, 3228, 3586⟩
  | 32 => ⟨1, 32, 3526, 5932, 3214, 3569⟩
  | 33 => ⟨1, 33, 3497, 5931, 3199, 3552⟩
  | 34 => ⟨1, 34, 3468, 5930, 3184, 3534⟩
  | 35 => ⟨1, 35, 3439, 5929, 3169, 3515⟩
  | 36 => ⟨1, 36, 3408, 5928, 3153, 3497⟩
  | 37 => ⟨1, 37, 3376, 5927, 3138, 3478⟩
  | 38 => ⟨1, 38, 3345, 5926, 3121, 3458⟩
  | 39 => ⟨1, 39, 3312, 5925, 3105, 3438⟩
  | 40 => ⟨1, 40, 3279, 5924, 3088, 3418⟩
  | 41 => ⟨1, 41, 3244, 5923, 3071, 3397⟩
  | 42 => ⟨1, 42, 3208, 5922, 3054, 3376⟩
  | 43 => ⟨1, 43, 3172, 5921, 3036, 3355⟩
  | 44 => ⟨1, 44, 3134, 5920, 3018, 3332⟩
  | 45 => ⟨1, 45, 3094, 5919, 3000, 3310⟩
  | 46 => ⟨1, 46, 3054, 5918, 2981, 3287⟩
  | 47 => ⟨1, 47, 3011, 5917, 2962, 3263⟩
  | 48 => ⟨1, 48, 2966, 5916, 2942, 3239⟩
  | 49 => ⟨1, 49, 2919, 5915, 2923, 3214⟩
  | 50 => ⟨1, 50, 2869, 5914, 2905, 3188⟩
  | 51 => ⟨1, 51, 2816, 5913, 2888, 3165⟩
  | 52 => ⟨1, 52, 2760, 5912, 2870, 3143⟩
  | 53 => ⟨1, 53, 2700, 5911, 2852, 3120⟩
  | 54 => ⟨1, 54, 2636, 5910, 2833, 3097⟩
  | 55 => ⟨1, 55, 2567, 5909, 2814, 3072⟩
  | 56 => ⟨1, 56, 2495, 5908, 2794, 3047⟩
  | 57 => ⟨1, 57, 2419, 5907, 2773, 3021⟩
  | 58 => ⟨1, 58, 2338, 5906, 2752, 2994⟩
  | 59 => ⟨1, 59, 2253, 5905, 2730, 2966⟩
  | 60 => ⟨1, 60, 2165, 5904, 2708, 2937⟩
  | 61 => ⟨1, 61, 2072, 5903, 2685, 2906⟩
  | 62 => ⟨1, 62, 1975, 5902, 2661, 2875⟩
  | 63 => ⟨1, 63, 1873, 5901, 2636, 2842⟩
  | 64 => ⟨1, 64, 1768, 5900, 2611, 2808⟩
  | 65 => ⟨1, 65, 1659, 5899, 2584, 2772⟩
  | 66 => ⟨1, 66, 1545, 5898, 2557, 2735⟩
  | 67 => ⟨1, 67, 1427, 4935, 2530, 2696⟩
  | 68 => ⟨1, 68, 1306, 3900, 2502, 2656⟩
  | 69 => ⟨1, 69, 1180, 2829, 2474, 2614⟩
  | 70 => ⟨1, 70, 1050, 1721, 2443, 2570⟩
  | 71 => ⟨1, 71, 915, 580, 2412, 2523⟩
  | 72 => ⟨1, 72, 777, 0, 2379, 2474⟩
  | 73 => ⟨1, 73, 635, 0, 2344, 2422⟩
  | 74 => ⟨1, 74, 488, 0, 2307, 2369⟩
  | 75 => ⟨1, 75, 338, 0, 2269, 2313⟩
  | 76 => ⟨1, 76, 183, 0, 2229, 2255⟩
  | 77 => ⟨1, 77, 23, 0, 2187, 2195⟩
  | 78 => ⟨1, 78, 0, 0, 2143, 2133⟩
  | 79 => ⟨1, 79, 0, 0, 2098, 2068⟩
  | 80 => ⟨1, 80, 0, 0, 2050, 2001⟩
  | 81 => ⟨1, 81, 0, 0, 2001, 1931⟩
  | 82 => ⟨1, 82, 0, 0, 1950, 1858⟩
  | 83 => ⟨1, 83, 0, 0, 1897, 1782⟩
  | 84 => ⟨1, 84, 0, 0, 1843, 1704⟩
  | 85 => ⟨1, 85, 0, 0, 1787, 1623⟩
  | 86 => ⟨1, 86, 0, 0, 1729, 1540⟩
  | 87 => ⟨1, 87, 0, 0, 1669, 1455⟩
  | 88 => ⟨1, 88, 0, 0, 1607, 1369⟩
  | 89 => ⟨1, 89, 0, 0, 1543, 1282⟩
  | 90 => ⟨1, 90, 0, 0, 1477, 1193⟩
  | 91 => ⟨1, 91, 0, 0, 1409, 1101⟩
  | 92 => ⟨1, 92, 0, 0, 1338, 1007⟩
  | 93 => ⟨1, 93, 0, 0, 1267, 910⟩
  | 94 => ⟨1, 94, 0, 0, 1193, 810⟩
  | 95 => ⟨1, 95, 0, 0, 1119, 707⟩
  | 96 => ⟨1, 96, 0, 0, 1042, 602⟩
  | 97 => ⟨1, 97, 0, 0, 965, 494⟩
  | 98 => ⟨1, 98, 0, 0, 886, 383⟩
  | 99 => ⟨1, 99, 0, 0, 805, 269⟩
  | 100 => ⟨1, 100, 0, 0, 723, 153⟩
  | 101 => ⟨1, 101, 0, 0, 638, 34⟩
  | 102 => ⟨1, 102, 0, 0, 550, 0⟩
  | 103 => ⟨1, 103, 0, 0, 460, 0⟩
  | 104 => ⟨1, 104, 0, 0, 368, 0⟩
  | 105 => ⟨1, 105, 0, 0, 274, 0⟩
  | 106 => ⟨1, 106, 0, 0, 177, 0⟩
  | 107 => ⟨1, 107, 0, 0, 77, 0⟩
  | 108 => ⟨1, 108, 0, 0, 0, 0⟩
  | 109 => ⟨1, 109, 0, 0, 0, 0⟩
  | 110 => ⟨1, 110, 0, 0, 0, 0⟩
  | 111 => ⟨1, 111, 0, 0, 0, 0⟩
  | 112 => ⟨1, 112, 0, 0, 0, 0⟩
  | 113 => ⟨1, 113, 0, 0, 0, 0⟩
  | 114 => ⟨1, 114, 0, 0, 0, 0⟩
  | 115 => ⟨1, 115, 0, 0, 0, 0⟩
  | 116 => ⟨1, 116, 0, 0, 0, 0⟩
  | 117 => ⟨1, 117, 0, 0, 0, 0⟩
  | 118 => ⟨1, 118, 0, 0, 0, 0⟩
  | 119 => ⟨1, 119, 0, 0, 0, 0⟩
  | 120 => ⟨1, 120, 0, 0, 0, 0⟩
  | 121 => ⟨1, 121, 0, 0, 0, 0⟩
  | 122 => ⟨1, 122, 0, 0, 0, 0⟩
  | 123 => ⟨1, 123, 0, 0, 0, 0⟩
  | 124 => ⟨1, 124, 0, 0, 0, 0⟩
  | 125 => ⟨1, 125, 0, 0, 0, 0⟩
  | 126 => ⟨1, 126, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨1, 0, 0, [0, 81015763878161, 214748052781569, 348480341684977, 482212630588385, 615944919491793, 749677208395201, 883409497298609, 1017141786202017, 1150874075105425, 1284606364008833, 1418338652912241, 1552070941815649, 1685803230719057, 1819535519622465, 1953267808525873, 2087000097429281, 2220732386332689, 2354464675236097, 2488196964139505, 2542305752083976], 1192423094599509, 1409488059038290⟩
  | 1 => ⟨1, 1, 0, [0, 117560527460718, 293074576986718, 468588626512718, 644102676038718, 819616725564718, 995130775090718, 1170644824616718, 1346158874142718, 1521672923668718, 1697186973194718, 1872701022720718, 2048215072246718, 2223729121772718, 2399243171298718, 2574757220824718, 2750271270350718, 2925785319876718, 3101299369402718, 3276813418928718, 3347249978277968], 1681360374771096, 1898979758717780⟩
  | 2 => ⟨1, 2, 0, [0, 154380171047371, 371675981195963, 588971791344555, 806267601493147, 1023563411641739, 1240859221790331, 1458155031938923, 1675450842087515, 1892746652236107, 2110042462384699, 2327338272533291, 2544634082681883, 2761929892830475, 2979225702979067, 3196521513127659, 3413817323276251, 3631113133424843, 3848408943573435, 4065704753722027, 4152194204471960], 2167608986884212, 2385840674968772⟩
  | 3 => ⟨1, 3, 1031217918783514, [0, 292699256146472, 635340348162840, 977981440179208, 1320622532195576, 1663263624211944, 2005904716228312, 2348545808244680, 2691186900261048, 3033827992277416, 3376469084293784, 3719110176310152, 4061751268326520, 4404392360342888, 4607271954299948, 4607271954299948, 4607271954299948, 4607271954299948, 4644122806209674, 4886430945232618, 4982078894846938], 3638348921685687, 3857135029278150⟩
  | 4 => ⟨1, 4, 2706288470223185, [0, 431430661251717, 899417035135861, 1367403409020005, 1835389782904149, 2303376156788293, 2771362530672437, 3239348904556581, 3707335278440725, 4175321652324869, 4643308026209013, 5111294400093157, 5579280773977301, 6047267147861445, 6295115194556666, 6295115194556666, 6295115194556666, 6295115194556666, 6295115194556666, 6295115194556666, 6295115194556666], 5098780856333562, 5318121383433928⟩
  | 5 => ⟨1, 5, 4364948498814709, [0, 570574386363106, 1163906042115026, 1757237697866946, 2350569353618866, 2943901009370786, 3537232665122706, 4130564320874626, 4723895976626546, 5317227632378466, 5910559288130386, 6503890943882306, 7097222599634226, 7690554255386146, 7965750845718451, 7965750845718451, 7965750845718451, 7965750845718451, 7965750845718451, 7965750845718451, 7965750845718451], 6548904790827837, 6768799737436106⟩
  | 6 => ⟨1, 6, 6007528047166617, [0, 710130431480639, 1428807369100335, 2147484306720031, 2866161244339727, 3584838181959423, 4303515119579119, 5022192057198815, 5740868994818511, 6459545932438207, 7178222870057903, 7896899807677599, 8615576745297295, 9334253682916991, 9620306016640620, 9620306016640620, 9620306016640620, 9620306016640620, 9620306016640620, 9620306016640620, 9620306016640620], 7986461553153255, 8206853034639454⟩
  | 7 => ⟨1, 7, 7632047792645802, [6076577116844, 850098796604316, 1694121016091788, 2538143235579260, 3382165455066732, 4226187674554204, 5070209894041676, 5914232113529148, 6758254333016620, 7602276552504092, 8446298771991564, 9290320991479036, 10134343210966508, 10978365430453980, 11256004318443280, 11256004318443280, 11256004318443280, 11256004318443280, 11256004318443280, 11256004318443280, 11256004318443280], 9415557167334186, 9636503068328288⟩
  | 8 => ⟨1, 8, 9242054060512334, [21111980378889, 990479481734137, 1959846983089385, 2929214484444633, 3898581985799881, 4867949487155129, 5837316988510377, 6806684489865625, 7776051991220873, 8745419492576121, 9714786993931369, 10684154495286617, 11653521996641865, 12622889497997113, 12877986208880073, 12877986208880073, 12877986208880073, 12877986208880073, 12877986208880073, 12877986208880073, 12877986208880073], 10831260969333972, 11052703405206004⟩
  | 9 => ⟨1, 9, 10830371922848460, [36559703647078, 1131272486870102, 2225985270093126, 3320698053316150, 4415410836539174, 5510123619762198, 6604836402985222, 7699549186208246, 8794261969431270, 9888974752654294, 10983687535877318, 12078400319100342, 13173113102323366, 14267825885546390, 14476685561292888, 14476685561292888, 14476685561292888, 14476685561292888, 14476685561292888, 14476685561292888, 14476685561292888], 12239328263201559, 12461325118581494⟩
  | 10 => ⟨1, 10, 12404176307571933, [52419746921411, 1272477812012211, 2492535877103011, 3712593942193811, 4932652007284611, 6152710072375411, 7372768137466211, 8592826202557011, 9812884267647811, 11032942332738611, 12253000397829411, 13473058462920211, 14693116528011011, 15913174593101811, 16061668502339836, 16061668502339836, 16061668502339836, 16061668502339836, 16061668502339836, 16061668502339836, 16061668502339836], 13633179104875713, 13855672495133578⟩
  | 11 => ⟨1, 11, 13964704174701185, [68692110201888, 1414095457160464, 2759498804119040, 4104902151077616, 5450305498036192, 6795708844994768, 8141112191953344, 9486515538911920, 10831918885870496, 12177322232829072, 13522725579787648, 14868128926746224, 16213532273704800, 17558935620663376, 17634171992039349, 17634171992039349, 17634171992039349, 17634171992039349, 17634171992039349, 17634171992039349, 17634171992039349], 15015897306383979, 15238887231519774⟩
  | 12 => ⟨1, 12, 15505110638926994, [85376793488509, 1556125422314861, 3026874051141213, 4497622679967565, 5968371308793917, 7439119937620269, 8909868566446621, 10380617195272973, 11851365824099325, 13322114452925677, 14792863081752029, 16263611710578381, 17734360339404733, 19185757012588633, 19185757012588633, 19185757012588633, 19185757012588633, 19185757012588633, 19185757012588633, 19185757012588633, 19185757012588633], 16382749775674236, 16606178351057988⟩
  | 13 => ⟨1, 13, 17028611982900899, [102473796781274, 1698567707475402, 3294661618169530, 4890755528863658, 6486849439557786, 8082943350251914, 9679037260946042, 11275131171640170, 12871225082334298, 14467318993028426, 16063412903722554, 17659506814416682, 19255600725110810, 20720436912886013, 20720436912886013, 20720436912886013, 20720436912886013, 20720436912886013, 20720436912886013, 20720436912886013, 20720436912886013], 17742790376844582, 17966715487106264⟩
  | 14 => ⟨1, 14, 18530342643946785, [119983120080183, 1841422312642087, 3562861505203991, 5284300697765895, 7005739890327799, 8727179082889703, 10448618275451607, 12170057468013511, 13891496660575415, 15612935853137319, 17334375045699223, 19055814238261127, 20777253430823031, 22232549064008588, 22232549064008588, 22232549064008588, 22232549064008588, 22232549064008588, 22232549064008588, 22232549064008588, 22232549064008588], 19097256069913449, 19321735599683034⟩
  | 15 => ⟨1, 15, 20014343544728479, [137904763385236, 1984689237814916, 3831473712244596, 5678258186674276, 7525042661103956, 9371827135533636, 11218611609963316, 13065396084392996, 14912180558822676, 16758965033252356, 18605749507682036, 20452533982111716, 22299318456541396, 23726931454866971, 23726931454866971, 23726931454866971, 23726931454866971, 23726931454866971, 23726931454866971, 23726931454866971, 23726931454866971], 20441413762828716, 20666447712106204⟩
  | 16 => ⟨1, 16, 21480614685245981, [156238726696433, 2128368482993889, 4100498239291345, 6072627995588801, 8044757751886257, 10016887508183713, 11989017264481169, 13961147020778625, 15933276777076081, 17905406533373537, 19877536289670993, 21849666045968449, 23821795802265905, 25203584085461162, 25203584085461162, 25203584085461162, 25203584085461162, 25203584085461162, 25203584085461162, 25203584085461162, 25203584085461162], 21775263455590383, 22000851824375774⟩
  | 17 => ⟨1, 17, 22923053542804744, [174985010013774, 2272460048179006, 4369935086344238, 6467410124509470, 8564885162674702, 10662360200839934, 12759835239005166, 14857310277170398, 16954785315335630, 19052260353500862, 21149735391666094, 23247210429831326, 25344685467996558, 26655607366849828, 26655607366849828, 26655607366849828, 26655607366849828, 26655607366849828, 26655607366849828, 26655607366849828, 26655607366849828], 23105599840281291, 23331800513204558⟩
  | 18 => ⟨1, 18, 24346938000087027, [194143613337259, 2416963933370267, 4639784253403275, 6862604573436283, 9085424893469291, 11308245213502299, 13531065533535307, 15753885853568315, 17976706173601323, 20199526493634331, 22422346813667339, 24645167133700347, 26867987453733355, 28089076247962014, 28089076247962014, 28089076247962014, 28089076247962014, 28089076247962014, 28089076247962014, 28089076247962014, 28089076247962014], 24426452864830887, 24653265841892030⟩
  | 19 => ⟨1, 19, 25752268057092830, [213714536666888, 2561880138567672, 4910045740468456, 7258211342369240, 9606376944270024, 11954542546170808, 14302708148071592, 16650873749972376, 18999039351873160, 21347204953773944, 23695370555674728, 26043536157575512, 28391701759476296, 29503990728797720, 29503990728797720, 29503990728797720, 29503990728797720, 29503990728797720, 29503990728797720, 29503990728797720, 29503990728797720], 25737822529239171, 25965247810438190⟩
  | 20 => ⟨1, 20, 27139043713822153, [233697780002661, 2707208663771221, 5180719547539781, 7654230431308341, 10127741315076901, 12601252198845461, 15074763082614021, 17548273966382581, 20021784850151141, 22495295733919701, 24968806617688261, 27442317501456821, 29915828385225381, 30900350809356946, 30900350809356946, 30900350809356946, 30900350809356946, 30900350809356946, 30900350809356946, 30900350809356946, 30900350809356946], 27039708833506143, 27267746418843038⟩
  | 21 => ⟨1, 21, 28507264970274996, [254093343344578, 2852949508980914, 5451805674617250, 8050661840253586, 10649518005889922, 13248374171526258, 15847230337162594, 18446086502798930, 21044942668435266, 23643798834071602, 26242654999707938, 28841511165344274, 31440367330980610, 32278156489639692, 32278156489639692, 32278156489639692, 32278156489639692, 32278156489639692, 32278156489639692, 32278156489639692, 32278156489639692], 28332111777631803, 28560761667106574⟩
  | 22 => ⟨1, 22, 29848767703726092, [274901226692639, 2999102674196751, 5723304121700863, 8447505569204975, 11171707016709087, 13895908464213199, 16620109911717311, 19344311359221423, 22068512806725535, 24792714254229647, 27516915701733759, 30241117149237871, 32965318596741983, 33628446580673905, 33628446580673905, 33628446580673905, 33628446580673905, 33628446580673905, 33628446580673905, 33628446580673905, 33628446580673905], 29615031361616151, 29844293555228798⟩
  | 23 => ⟨1, 23, 31170891396888420, [296121430046844, 3145668159418732, 5995214888790620, 8844761618162508, 11694308347534396, 14543855076906284, 17393401806278172, 20242948535650060, 23092495265021948, 25942041994393836, 28791588723765724, 31641135453137612, 34490682182509500, 34959357631419350, 34959357631419350, 34959357631419350, 34959357631419350, 34959357631419350, 34959357631419350, 34959357631419350, 34959357631419350], 30879198973339482, 31109015586460032⟩
  | 24 => ⟨1, 24, 32464647287024425, [317753953407193, 3292645964646857, 6267537975886521, 9242429987126185, 12217321998365849, 15192214009605513, 18167106020845177, 21141998032084841, 24116890043324505, 27091782054564169, 30066674065803833, 33041566077043497, 36016458088283161, 36261103812891686, 36261103812891686, 36261103812891686, 36261103812891686, 36261103812891686, 36261103812891686, 36261103812891686, 36261103812891686], 32142739517035062, 32373168434293488⟩
  | 25 => ⟨1, 25, 33738199496859374, [339798796773686, 3440036089881126, 6540273382988566, 9640510676096006, 12740747969203446, 15840985262310886, 18941222555418326, 22041459848525766, 25141697141633206, 28241934434740646, 31342171727848086, 34442409020955526, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966, 37542646314062966], 33386703448457337, 33617686785223666⟩
  | 26 => ⟨1, 26, 34981734623643424, [362255960146323, 3587838535121539, 6813421110096755, 10039003685071971, 13264586260047187, 16490168835022403, 19715751409997619, 22941333984972835, 26166916559948051, 29392499134923267, 32618081709898483, 35843664284873699, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561, 38793374665936561], 34620359379726012, 34851897136000244⟩
  | 27 => ⟨1, 27, 36204241430114130, [385125443525104, 3736053300368096, 7086981157211088, 10437909014054080, 13788836870897072, 17139764727740064, 20490692584583056, 23841620441426048, 27192548298269040, 30543476155112032, 33894404011955024, 37245331868798016, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812, 40023074697496812], 35832789418696806, 36064823709848968⟩
  | 28 => ⟨1, 28, 37405719916271492, [408407246910029, 3884680385620797, 7360953524331565, 10837226663042333, 14313499801753101, 17789772940463869, 21266046079174637, 24742319217885405, 28218592356596173, 31694865495306941, 35171138634017709, 38647411772728477, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719, 41231746408743719], 37045417029652137, 37278005740312202⟩
  | 29 => ⟨1, 29, 38586170082115510, [432101370301098, 4033719790879642, 7635338211458186, 11236956632036730, 14838575052615274, 18440193473193818, 22041811893772362, 25643430314350906, 29245048734929450, 32846667155507994, 36448285576086538, 40049903996665082, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282, 42419389799677282], 38235994108297299, 38469079353835294⟩
  | 30 => ⟨1, 30, 39734129244871765, [456207813698311, 4183171516144631, 7910135218590951, 11637098921037271, 15364062623483591, 19091026325929911, 22817990028376231, 26544953730822551, 30271917433268871, 33998881135715191, 37725844838161511, 41452808540607831, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296, 43573745121276296], 39415438546776573, 39649020327192498⟩
  | 31 => ⟨1, 31, 40848360444521825, [480726577101668, 4333035561415764, 8185344545729860, 12037653530043956, 15889962514358052, 19742271498672148, 23594580482986244, 27446889467300340, 31299198451614436, 35151507435928532, 39003816420242628, 42856125404556724, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329, 44693575413522329], 40583750345089959, 40817828660383814⟩
  | 32 => ⟨1, 32, 41939914043833965, [505657660511169, 4483311926693041, 8460966192874913, 12438620459056785, 16416274725238657, 20393928991420529, 24371583257602401, 28349237523784273, 32326891789966145, 36304546056148017, 40282200322329889, 44259854588511761, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442, 45790728105430442], 41740929503237457, 41975504353409242⟩
  | 33 => ⟨1, 33, 42996090400015334, [531001063926814, 4634000611976462, 8737000160026110, 12839999708075758, 16942999256125406, 21045998804175054, 25148998352224702, 29251997900274350, 33354997448323998, 37457996996373646, 41560996544423294, 45663996092472942, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998, 46851706487960998], 42873584209037922, 43108597709457664⟩
  | 34 => ⟨1, 34, 44028764515846495, [556756787348603, 4785101617266027, 9013446447183451, 13241791277100875, 17470136107018299, 21698480936935723, 25926825766853147, 30155170596770571, 34383515426687995, 38611860256605419, 42840205086522843, 47068549916440267, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346, 47889182630141346], 43994281634660211, 44229733785327910⟩
  | 35 => ⟨1, 35, 45037936391327448, [582924830776536, 4936614942561736, 9290305054346936, 13643995166132136, 17997685277917336, 22351375389702536, 26705065501487736, 31058755613272936, 35412445725058136, 39766135836843336, 44119825948628536, 48473516060413736, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486, 48903156531971486], 45103021780104324, 45338912581019980⟩
  | 36 => ⟨1, 36, 45995732820835627, [609505194210613, 5088540587863589, 9567575981516565, 14046611375169541, 18525646768822517, 23004682162475493, 27483717556128469, 31962752949781445, 36441788343434421, 40920823737087397, 45399859130740373, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280, 49864160855335280], 46185175873170684, 46421447439704324⟩
  | 37 => ⟨1, 37, 46914028807151595, [636497877650834, 5240878553171586, 9845259228692338, 14449639904213090, 19054020579733842, 23658401255254594, 28262781930775346, 32867162606296098, 37471543281816850, 42075923957337602, 46680304632858354, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077, 50784867669260077], 47269589138252301, 47506299355033898⟩
  | 38 => ⟨1, 38, 47821109875904062, [663902881097199, 5393628838485727, 10123354795874255, 14853080753262783, 19582806710651311, 24312532668039839, 29042258625428367, 33771984582816895, 38501710540205423, 43231436497593951, 47961162454982479, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159, 51695156631868159], 48311138298732012, 48548171396501620⟩
  | 39 => ⟨1, 39, 48672692298622315, [691720204549708, 5546791443806012, 10401862683062316, 15256933922318620, 20112005161574924, 24967076400831228, 29822147640087532, 34677218879343836, 39532290118600140, 44387361357856444, 49242432597112748, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455, 52548352815948455], 49354946631226980, 49592360494614572⟩
  | 40 => ⟨1, 40, 49497473920941208, [719949848008361, 5700366369132441, 10680782890256521, 15661199411380601, 20641615932504681, 25622032453628761, 30602448974752841, 35582865495876921, 40563282017001001, 45543698538125081, 50524115059249161, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391, 53374748199629391], 50369694991307331, 50607431735682934⟩
  | 41 => ⟨1, 41, 50263458337176735, [748591811473158, 5854353614465014, 10960115417456870, 16065877220448726, 21171639023440582, 26277400826432438, 31383162629424294, 36488924432416150, 41594686235408006, 46700448038399862, 51806209841391718, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389, 54140752244733389], 51370836791184930, 51608896416548544⟩
  | 42 => ⟨1, 42, 50984582150140179, [777646094944099, 6008753179803731, 11239860264663363, 16470967349522995, 21702074434382627, 26933181519242259, 32164288604101891, 37395395688961523, 42626502773821155, 47857609858680787, 53088716943540419, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518, 54861098620318518], 52358372030859777, 52596754537211402⟩
  | 43 => ⟨1, 43, 51676431242667399, [807112698421184, 6163565065148592, 11520017431876000, 16876469798603408, 22232922165330816, 27589374532058224, 32945826898785632, 38302279265513040, 43658731632240448, 49015183998967856, 54371636365695264, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423, 55552170275467423], 53314785698089287, 53553433200798950⟩
  | 44 => ⟨1, 44, 52304535289037525, [836991621904413, 6318789270499597, 11800586919094781, 17282384567689965, 22764182216285149, 28245979864880333, 33727777513475517, 39209575162070701, 44691372810665885, 50173170459261069, 55654968107856253, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662, 56177902751965662], 54256768165103757, 54495680664171458⟩
  | 45 => ⟨1, 45, 52866420369213693, [867282865393786, 6474425795856746, 12081568726319706, 17688711656782666, 23295854587245626, 28902997517708586, 34510140448171546, 40117283378634506, 45724426309097466, 51331569239560426, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371, 56735822129776371], 55184319431903187, 55423496927328926⟩
  | 46 => ⟨1, 46, 53395732168904485, [897986428889303, 6630474641220039, 12362962853550775, 18095451065881511, 23827939278212247, 29560427490542983, 35292915702873719, 41025403915204455, 46757892127535191, 52490380339865927, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704, 57261168227101704], 56078687526226560, 56318072133380364⟩
  | 47 => ⟨1, 47, 53837054319473300, [929102312390964, 6786935806589476, 12644769300787988, 18502602794986500, 24360436289185012, 30218269783383524, 36076103277582036, 41933936771780548, 47791770265979060, 53649603760177572, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702, 57696133476564702], 56957799780322605, 57197391499204474⟩
  | 48 => ⟨1, 48, 54205560383749853, [960630515898769, 6943809291965057, 12926988068031345, 18910166844097633, 24893345620163921, 30876524396230209, 36859703172296497, 42842881948362785, 48826060724429073, 54809239500495361, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866, 58056688507241866], 57802079581918017, 58041820527897978⟩
  | 49 => ⟨1, 49, 54498776441697280, [992571039412718, 7101095097346782, 13209619155280846, 19318143213214910, 25426667271148974, 31535191329083038, 37643715387017102, 43752239444951166, 49860763502885230, 55969287560819294, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332, 58340359399096332], 58570312106435466, 58810028625623600⟩
  | 50 => ⟨1, 50, 54694519490381418, [1024923882932811, 7258793222734651, 13492662562536491, 19726531902338331, 25960401242140171, 32194270581942011, 38428139921743851, 44662009261545691, 50895878601347531, 57129747941149371, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151, 58524166082947151], 58769156418965424, 59007285626352460⟩
  | 51 => ⟨1, 51, 54789078649746971, [1057689046459048, 7416903668128664, 13776118289798280, 20135332911467896, 26494547533137512, 32853762154807128, 39212976776476744, 45572191398146360, 51931406019815976, 58290620641485592, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 52 => ⟨1, 52, 54789078649746971, [1090866529991429, 7575426433528821, 14059986337066213, 20544546240603605, 27029106144140997, 33513666047678389, 39998225951215781, 46482785854753173, 52967345758290565, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 53 => ⟨1, 53, 54789078649746971, [1124456333529954, 7734361518935122, 14344266704340290, 20954171889745458, 27564077075150626, 34173982260555794, 40783887445960962, 47393792631366130, 54003697816771298, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 54 => ⟨1, 54, 54789078649746971, [1158458457074623, 7893708924347567, 14628959391620511, 21364209858893455, 28099460326166399, 34834710793439343, 41569961260712287, 48305211727985231, 55040462195258175, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 55 => ⟨1, 55, 54789078649746971, [1192872900625436, 8053468649766156, 14914064398906876, 21774660148047596, 28635255897188316, 35495851646329036, 42356447395469756, 49217043144610476, 56077638893751196, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 56 => ⟨1, 56, 54789078649746971, [1227699664182393, 8213640695190889, 15199581726199385, 22185522757207881, 29171463788216377, 36157404819224873, 43143345850233369, 50129286881241865, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 57 => ⟨1, 57, 54789078649746971, [1262938747745494, 8374225060621766, 15485511373498038, 22596797686374310, 29708083999250582, 36819370312126854, 43930656625003126, 51041942937879398, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 58 => ⟨1, 58, 54789078649746971, [1298590151314739, 8535221746058787, 15771853340802835, 23008484935546883, 30245116530290931, 37481748125034979, 44718379719779027, 51955011314523075, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 59 => ⟨1, 59, 54789078649746971, [1334653874890128, 8696630751501952, 16058607628113776, 23420584504725600, 30782561381337424, 38144538257949248, 45506515134561072, 52868492011172896, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 60 => ⟨1, 60, 54789078649746971, [1371129918471661, 8858452076951261, 16345774235430861, 23833096393910461, 31320418552390061, 38807740710869661, 46295062869349261, 53092763250074161, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 61 => ⟨1, 61, 54789078649746971, [1408018282059338, 9020685722406714, 16633353162754090, 24246020603101466, 31858688043448842, 39471355483796218, 47084022924143594, 53092763250074161, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 62 => ⟨1, 62, 54789078649746971, [1445318965653159, 9183331687868311, 16921344410083463, 24659357132298615, 32397369854513767, 40135382576728919, 47873395298944071, 53092763250074161, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 63 => ⟨1, 63, 54789078649746971, [1483031969253124, 9346389973336052, 17209747977418980, 25073105981501908, 32936463985584836, 40799821989667764, 48249319046167380, 53092763250074161, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 64 => ⟨1, 64, 54789078649746971, [1521157292859233, 9509860578809937, 17498563864760641, 25487267150711345, 33475970436662049, 41464673722612753, 48249319046167380, 53092763250074161, 57069267773888463, 58577343306416664, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027, 58604397678739027], 58864740334011915, 59101108575707934⟩
  | 65 => ⟨1, 65, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 66 => ⟨1, 66, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 67 => ⟨1, 67, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 68 => ⟨1, 68, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 69 => ⟨1, 69, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 70 => ⟨1, 70, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 71 => ⟨1, 71, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 72 => ⟨1, 72, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 73 => ⟨1, 73, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 74 => ⟨1, 74, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 75 => ⟨1, 75, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 76 => ⟨1, 76, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 77 => ⟨1, 77, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 78 => ⟨1, 78, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 79 => ⟨1, 79, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 80 => ⟨1, 80, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 81 => ⟨1, 81, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 82 => ⟨1, 82, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 83 => ⟨1, 83, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 84 => ⟨1, 84, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 85 => ⟨1, 85, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 86 => ⟨1, 86, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 87 => ⟨1, 87, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 88 => ⟨1, 88, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 89 => ⟨1, 89, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 90 => ⟨1, 90, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 91 => ⟨1, 91, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 92 => ⟨1, 92, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 93 => ⟨1, 93, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 94 => ⟨1, 94, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 95 => ⟨1, 95, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 96 => ⟨1, 96, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 97 => ⟨1, 97, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 98 => ⟨1, 98, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 99 => ⟨1, 99, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 100 => ⟨1, 100, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 101 => ⟨1, 101, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 102 => ⟨1, 102, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 103 => ⟨1, 103, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 104 => ⟨1, 104, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 105 => ⟨1, 105, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 106 => ⟨1, 106, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 107 => ⟨1, 107, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 108 => ⟨1, 108, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 109 => ⟨1, 109, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 110 => ⟨1, 110, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 111 => ⟨1, 111, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 112 => ⟨1, 112, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 113 => ⟨1, 113, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 114 => ⟨1, 114, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 115 => ⟨1, 115, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 116 => ⟨1, 116, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 117 => ⟨1, 117, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 118 => ⟨1, 118, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 119 => ⟨1, 119, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 120 => ⟨1, 120, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 121 => ⟨1, 121, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 122 => ⟨1, 122, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 123 => ⟨1, 123, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 124 => ⟨1, 124, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | 125 => ⟨1, 125, 54789078649746971, [58604397678739027], 58864740334011915, 59101108575707934⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01
end PackedLocator_LocatorPhase6800ReceiptRowData01

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02. -/
section PackedLocator_LocatorPhase6800ReceiptRowData02

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨2, 0, 4169, 5963, 3578, 4000⟩
  | 1 => ⟨2, 1, 4149, 5962, 3565, 3984⟩
  | 2 => ⟨2, 2, 4130, 5961, 3552, 3968⟩
  | 3 => ⟨2, 3, 4109, 5960, 3539, 3952⟩
  | 4 => ⟨2, 4, 4089, 5959, 3526, 3935⟩
  | 5 => ⟨2, 5, 4068, 5958, 3512, 3919⟩
  | 6 => ⟨2, 6, 4048, 5957, 3498, 3902⟩
  | 7 => ⟨2, 7, 4028, 5956, 3484, 3885⟩
  | 8 => ⟨2, 8, 4008, 5955, 3470, 3868⟩
  | 9 => ⟨2, 9, 3987, 5954, 3457, 3852⟩
  | 10 => ⟨2, 10, 3966, 5953, 3444, 3837⟩
  | 11 => ⟨2, 11, 3945, 5952, 3431, 3823⟩
  | 12 => ⟨2, 12, 3923, 5951, 3419, 3809⟩
  | 13 => ⟨2, 13, 3901, 5950, 3407, 3795⟩
  | 14 => ⟨2, 14, 3878, 5949, 3395, 3782⟩
  | 15 => ⟨2, 15, 3855, 5948, 3383, 3769⟩
  | 16 => ⟨2, 16, 3833, 5947, 3372, 3755⟩
  | 17 => ⟨2, 17, 3811, 5946, 3360, 3741⟩
  | 18 => ⟨2, 18, 3788, 5945, 3348, 3727⟩
  | 19 => ⟨2, 19, 3764, 5944, 3336, 3713⟩
  | 20 => ⟨2, 20, 3741, 5943, 3323, 3699⟩
  | 21 => ⟨2, 21, 3716, 5942, 3311, 3684⟩
  | 22 => ⟨2, 22, 3691, 5941, 3298, 3669⟩
  | 23 => ⟨2, 23, 3666, 5940, 3285, 3654⟩
  | 24 => ⟨2, 24, 3641, 5939, 3272, 3638⟩
  | 25 => ⟨2, 25, 3616, 5938, 3258, 3622⟩
  | 26 => ⟨2, 26, 3590, 5937, 3245, 3606⟩
  | 27 => ⟨2, 27, 3564, 5936, 3231, 3590⟩
  | 28 => ⟨2, 28, 3536, 5935, 3217, 3573⟩
  | 29 => ⟨2, 29, 3509, 5934, 3202, 3556⟩
  | 30 => ⟨2, 30, 3481, 5933, 3188, 3538⟩
  | 31 => ⟨2, 31, 3453, 5932, 3173, 3521⟩
  | 32 => ⟨2, 32, 3424, 5931, 3158, 3503⟩
  | 33 => ⟨2, 33, 3394, 5930, 3143, 3484⟩
  | 34 => ⟨2, 34, 3364, 5929, 3127, 3465⟩
  | 35 => ⟨2, 35, 3333, 5928, 3111, 3446⟩
  | 36 => ⟨2, 36, 3302, 5927, 3095, 3426⟩
  | 37 => ⟨2, 37, 3270, 5926, 3078, 3406⟩
  | 38 => ⟨2, 38, 3236, 5925, 3061, 3386⟩
  | 39 => ⟨2, 39, 3202, 5924, 3044, 3365⟩
  | 40 => ⟨2, 40, 3167, 5923, 3027, 3344⟩
  | 41 => ⟨2, 41, 3131, 5922, 3009, 3322⟩
  | 42 => ⟨2, 42, 3093, 5921, 2991, 3300⟩
  | 43 => ⟨2, 43, 3055, 5920, 2972, 3277⟩
  | 44 => ⟨2, 44, 3014, 5919, 2953, 3254⟩
  | 45 => ⟨2, 45, 2972, 5918, 2935, 3230⟩
  | 46 => ⟨2, 46, 2929, 5917, 2917, 3206⟩
  | 47 => ⟨2, 47, 2882, 5916, 2899, 3181⟩
  | 48 => ⟨2, 48, 2834, 5915, 2883, 3159⟩
  | 49 => ⟨2, 49, 2782, 5914, 2865, 3138⟩
  | 50 => ⟨2, 50, 2727, 5913, 2847, 3116⟩
  | 51 => ⟨2, 51, 2669, 5912, 2829, 3093⟩
  | 52 => ⟨2, 52, 2606, 5911, 2810, 3070⟩
  | 53 => ⟨2, 53, 2540, 5910, 2791, 3045⟩
  | 54 => ⟨2, 54, 2469, 5909, 2771, 3020⟩
  | 55 => ⟨2, 55, 2394, 5908, 2750, 2994⟩
  | 56 => ⟨2, 56, 2315, 5907, 2729, 2967⟩
  | 57 => ⟨2, 57, 2232, 5906, 2707, 2939⟩
  | 58 => ⟨2, 58, 2145, 5905, 2685, 2910⟩
  | 59 => ⟨2, 59, 2053, 5904, 2662, 2880⟩
  | 60 => ⟨2, 60, 1958, 5903, 2638, 2849⟩
  | 61 => ⟨2, 61, 1858, 5902, 2613, 2816⟩
  | 62 => ⟨2, 62, 1755, 5901, 2588, 2783⟩
  | 63 => ⟨2, 63, 1647, 5900, 2562, 2747⟩
  | 64 => ⟨2, 64, 1535, 5888, 2536, 2711⟩
  | 65 => ⟨2, 65, 1419, 4905, 2510, 2674⟩
  | 66 => ⟨2, 66, 1299, 3887, 2483, 2635⟩
  | 67 => ⟨2, 67, 1175, 2833, 2454, 2594⟩
  | 68 => ⟨2, 68, 1046, 1744, 2425, 2550⟩
  | 69 => ⟨2, 69, 914, 622, 2393, 2505⟩
  | 70 => ⟨2, 70, 777, 0, 2361, 2456⟩
  | 71 => ⟨2, 71, 636, 0, 2327, 2406⟩
  | 72 => ⟨2, 72, 491, 0, 2291, 2353⟩
  | 73 => ⟨2, 73, 342, 0, 2253, 2298⟩
  | 74 => ⟨2, 74, 189, 0, 2214, 2240⟩
  | 75 => ⟨2, 75, 32, 0, 2173, 2181⟩
  | 76 => ⟨2, 76, 0, 0, 2130, 2120⟩
  | 77 => ⟨2, 77, 0, 0, 2085, 2056⟩
  | 78 => ⟨2, 78, 0, 0, 2038, 1990⟩
  | 79 => ⟨2, 79, 0, 0, 1990, 1921⟩
  | 80 => ⟨2, 80, 0, 0, 1940, 1850⟩
  | 81 => ⟨2, 81, 0, 0, 1888, 1776⟩
  | 82 => ⟨2, 82, 0, 0, 1834, 1699⟩
  | 83 => ⟨2, 83, 0, 0, 1778, 1620⟩
  | 84 => ⟨2, 84, 0, 0, 1721, 1537⟩
  | 85 => ⟨2, 85, 0, 0, 1663, 1453⟩
  | 86 => ⟨2, 86, 0, 0, 1602, 1367⟩
  | 87 => ⟨2, 87, 0, 0, 1539, 1279⟩
  | 88 => ⟨2, 88, 0, 0, 1474, 1190⟩
  | 89 => ⟨2, 89, 0, 0, 1407, 1099⟩
  | 90 => ⟨2, 90, 0, 0, 1337, 1006⟩
  | 91 => ⟨2, 91, 0, 0, 1266, 910⟩
  | 92 => ⟨2, 92, 0, 0, 1193, 812⟩
  | 93 => ⟨2, 93, 0, 0, 1118, 710⟩
  | 94 => ⟨2, 94, 0, 0, 1042, 606⟩
  | 95 => ⟨2, 95, 0, 0, 965, 500⟩
  | 96 => ⟨2, 96, 0, 0, 886, 390⟩
  | 97 => ⟨2, 97, 0, 0, 806, 278⟩
  | 98 => ⟨2, 98, 0, 0, 724, 163⟩
  | 99 => ⟨2, 99, 0, 0, 641, 46⟩
  | 100 => ⟨2, 100, 0, 0, 555, 0⟩
  | 101 => ⟨2, 101, 0, 0, 466, 0⟩
  | 102 => ⟨2, 102, 0, 0, 376, 0⟩
  | 103 => ⟨2, 103, 0, 0, 283, 0⟩
  | 104 => ⟨2, 104, 0, 0, 187, 0⟩
  | 105 => ⟨2, 105, 0, 0, 90, 0⟩
  | 106 => ⟨2, 106, 0, 0, 0, 0⟩
  | 107 => ⟨2, 107, 0, 0, 0, 0⟩
  | 108 => ⟨2, 108, 0, 0, 0, 0⟩
  | 109 => ⟨2, 109, 0, 0, 0, 0⟩
  | 110 => ⟨2, 110, 0, 0, 0, 0⟩
  | 111 => ⟨2, 111, 0, 0, 0, 0⟩
  | 112 => ⟨2, 112, 0, 0, 0, 0⟩
  | 113 => ⟨2, 113, 0, 0, 0, 0⟩
  | 114 => ⟨2, 114, 0, 0, 0, 0⟩
  | 115 => ⟨2, 115, 0, 0, 0, 0⟩
  | 116 => ⟨2, 116, 0, 0, 0, 0⟩
  | 117 => ⟨2, 117, 0, 0, 0, 0⟩
  | 118 => ⟨2, 118, 0, 0, 0, 0⟩
  | 119 => ⟨2, 119, 0, 0, 0, 0⟩
  | 120 => ⟨2, 120, 0, 0, 0, 0⟩
  | 121 => ⟨2, 121, 0, 0, 0, 0⟩
  | 122 => ⟨2, 122, 0, 0, 0, 0⟩
  | 123 => ⟨2, 123, 0, 0, 0, 0⟩
  | 124 => ⟨2, 124, 0, 0, 0, 0⟩
  | 125 => ⟨2, 125, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨2, 0, 0, [0, 101850868270806, 319146837803558, 536442807336310, 753738776869062, 971034746401814, 1188330715934566, 1405626685467318, 1622922655000070, 1840218624532822, 2057514594065574, 2274810563598326, 2492106533131078, 2709402502663830, 2926698472196582, 3143994441729334, 3361290411262086, 3578586380794838, 3795882350327590, 4013178319860342, 4100382623422828], 2132784381780447, 2353377910687612⟩
  | 1 => ⟨2, 1, 0, [0, 138807952383797, 397885682539141, 656963412694485, 916041142849829, 1175118873005173, 1434196603160517, 1693274333315861, 1952352063471205, 2211429793626549, 2470507523781893, 2729585253937237, 2988662984092581, 3247740714247925, 3506818444403269, 3765896174558613, 4024973904713957, 4284051634869301, 4543129365024645, 4802207095179989, 4905326849616820], 2610863895498762, 2832011843913830⟩
  | 2 => ⟨2, 2, 2632580493672252, [0, 388371557546246, 864195478140294, 1340019398734342, 1815843319328390, 2291667239922438, 2767491160516486, 3243315081110534, 3719139001704582, 4194962922298630, 4670786842892678, 5146610763486726, 5622434684080774, 6098258604674822, 6275127364632478, 6275127364632478, 6275127364632478, 6275127364632478, 6275127364632478, 6275127364632478, 6275127364632478], 5129923135294486, 5351625503217457⟩
  | 3 => ⟨2, 3, 4975636394090769, [0, 590850910605670, 1244248588914150, 1897646267222630, 2551043945531110, 3204441623839590, 3857839302148070, 4511236980456550, 5164634658765030, 5818032337073510, 6471430015381990, 7124827693690470, 7778225371998950, 8431623050307430, 8629361821374470, 8629361821374470, 8629361821374470, 8629361821374470, 8629361821374470, 8629361821374470, 8629361821374470], 7174884923357749, 7397141710788623⟩
  | 4 => ⟨2, 4, 7296679594610300, [0, 793914387868102, 1624885823891014, 2455857259913926, 3286828695936838, 4117800131959750, 4948771567982662, 5779743004005574, 6610714440028486, 7441685876051398, 8272657312074310, 9103628748097222, 9934600184120134, 10765571620143046, 10962380644464262, 10962380644464262, 10962380644464262, 10962380644464262, 10962380644464262, 10962380644464262, 10962380644464262], 9205243606345812, 9428054813284589⟩
  | 5 => ⟨2, 5, 9592421434585169, [0, 997561989333542, 2006107183070886, 3014652376808230, 4023197570545574, 5031742764282918, 6040287958020262, 7048833151757606, 8057378345494950, 9065923539232294, 10074468732969638, 11083013926706982, 12091559120444326, 13100104314181670, 13269301040762606, 13269301040762606, 13269301040762606, 13269301040762606, 13269301040762606, 13269301040762606, 13269301040762606], 11217786498243031, 11441094240059738⟩
  | 6 => ⟨2, 6, 11867318823067068, [15674763550214, 1201793715001990, 2387912666453766, 3574031617905542, 4760150569357318, 5946269520809094, 7132388472260870, 8318507423712646, 9504626375164422, 10690745326616198, 11876864278067974, 13062983229519750, 14249102180971526, 15435221132423302, 15556174051814766, 15556174051814766, 15556174051814766, 15556174051814766, 15556174051814766, 15556174051814766, 15556174051814766], 13214558036659034, 13438362313353671⟩
  | 7 => ⟨2, 7, 14119435367631655, [42916855707238, 1406609564873446, 2770302274039654, 4133994983205862, 5497687692372070, 6861380401538278, 8225073110704486, 9588765819870694, 10952458529036902, 12316151238203110, 13679843947369318, 15043536656535526, 16407229365701734, 17770922074867942, 17820266218949614, 17820266218949614, 17820266218949614, 17820266218949614, 17820266218949614, 17820266218949614, 17820266218949614], 15195558221593821, 15419859033166388⟩
  | 8 => ⟨2, 8, 16348771068278930, [70743072067270, 1612009538947910, 3153276005828550, 4694542472709190, 6235808939589830, 7777075406470470, 9318341873351110, 10859608340231750, 12400874807112390, 13942141273993030, 15483407740873670, 17024674207754310, 18565940674634950, 20061577542167150, 20061577542167150, 20061577542167150, 20061577542167150, 20061577542167150, 20061577542167150, 20061577542167150, 20061577542167150], 17160787053047392, 17385584399497889⟩
  | 9 => ⟨2, 9, 18550468911569511, [99153412630310, 1817993637225382, 3536833861820454, 5255674086415526, 6974514311010598, 8693354535605670, 10412194760200742, 12131034984795814, 13849875209390886, 15568715433985958, 17287555658581030, 19006395883176102, 20725236107771174, 22274453941781206, 22274453941781206, 22274453941781206, 22274453941781206, 22274453941781206, 22274453941781206, 22274453941781206, 22274453941781206], 19115793713847423, 19341145479805823⟩
  | 10 => ⟨2, 10, 20728217662536764, [128147877396358, 2024561859705862, 3920975842015366, 5817389824324870, 7713803806634374, 9610217788943878, 11506631771253382, 13403045753562886, 15299459735872390, 17195873718181894, 19092287700491398, 20988701682800902, 22885115665110406, 24463381249071934, 24463381249071934, 24463381249071934, 24463381249071934, 24463381249071934, 24463381249071934, 24463381249071934, 24463381249071934], 21056197269572254, 21282103455038557⟩
  | 11 => ⟨2, 11, 22882017321180689, [157726466365414, 2231714206389350, 4305701946413286, 6379689686437222, 8453677426461158, 10527665166485094, 12601652906509030, 14675640646532966, 16749628386556902, 18823616126580838, 20897603866604774, 22971591606628710, 25045579346652646, 26628359464039334, 26628359464039334, 26628359464039334, 26628359464039334, 26628359464039334, 26628359464039334, 26628359464039334, 26628359464039334], 22981997720221885, 23208458325196091⟩
  | 12 => ⟨2, 12, 25005258501452880, [187889179537478, 2439450677275846, 4691012175014214, 6942573672752582, 9194135170490950, 11445696668229318, 13697258165967686, 15948819663706054, 18200381161444422, 20451942659182790, 22703504156921158, 24955065654659526, 27206627152397894, 28761982134388214, 28761982134388214, 28761982134388214, 28761982134388214, 28761982134388214, 28761982134388214, 28761982134388214, 28761982134388214], 24900496621233016, 25127569530345098⟩
  | 13 => ⟨2, 13, 27103382340995727, [218636016912550, 2647771272365350, 5076906527818150, 7506041783270950, 9935177038723750, 12364312294176550, 14793447549629350, 17222582805082150, 19651718060534950, 22080853315987750, 24509988571440550, 26939123826893350, 29368259082346150, 30870487464007750, 30870487464007750, 30870487464007750, 30870487464007750, 30870487464007750, 30870487464007750, 30870487464007750, 30870487464007750], 26805560665574963, 27033245878824921⟩
  | 14 => ⟨2, 14, 29168611205354808, [249966978490630, 2856675991657862, 5463385004825094, 8070094017992326, 10676803031159558, 13283512044326790, 15890221057494022, 18496930070661254, 21103639083828486, 23710348096995718, 26317057110162950, 28923766123330182, 31530475136497414, 32945300752196734, 32945300752196734, 32945300752196734, 32945300752196734, 32945300752196734, 32945300752196734, 32945300752196734, 32945300752196734], 28697189853247726, 28925487370635560⟩
  | 15 => ⟨2, 15, 31207554480578529, [281882064271718, 3066164835153382, 5850447606035046, 8634730376916710, 11419013147798374, 14203295918680038, 16987578689561702, 19771861460443366, 22556144231325030, 25340427002206694, 28124709773088358, 30908992543970022, 33693275314851686, 34993828451250358, 34993828451250358, 34993828451250358, 34993828451250358, 34993828451250358, 34993828451250358, 34993828451250358, 34993828451250358], 30575384184251305, 30804294005777015⟩
  | 16 => ⟨2, 16, 33229158049527328, [314381274255814, 3276237802851910, 6238094331448006, 9199950860044102, 12161807388640198, 15123663917236294, 18085520445832390, 21047376974428486, 24009233503024582, 26971090031620678, 29932946560216774, 32894803088812870, 35856659617408966, 37025813510275846, 37025813510275846, 37025813510275846, 37025813510275846, 37025813510275846, 37025813510275846, 37025813510275846, 37025813510275846], 32449781710834432, 32679361721127991⟩
  | 17 => ⟨2, 17, 35225644277746783, [347464608442918, 3486894894753446, 6626325181063974, 9765755467374502, 12905185753685030, 16044616039995558, 19184046326306086, 22323476612616614, 25462906898927142, 28602337185237670, 31741767471548198, 34881197757858726, 38020628044169254, 39032681228571990, 39032681228571990, 39032681228571990, 39032681228571990, 39032681228571990, 39032681228571990, 39032681228571990, 39032681228571990], 34301690452702651, 34531882767134086⟩
  | 18 => ⟨2, 18, 37186899033970440, [381132066833030, 3698136110857990, 7015140154882950, 10332144198907910, 13649148242932870, 16966152286957830, 20283156330982790, 23600160375007750, 26917164419032710, 30234168463057670, 33551172507082630, 36868176551107590, 40185180595132550, 41003520408625550, 41003520408625550, 41003520408625550, 41003520408625550, 41003520408625550, 41003520408625550, 41003520408625550, 41003520408625550], 36140164337901686, 36370968956470997⟩
  | 19 => ⟨2, 19, 39111169945589275, [415383649426150, 3909961451165542, 7404539252904934, 10899117054644326, 14393694856383718, 17888272658123110, 21382850459862502, 24877428261601894, 28372006063341286, 31866583865080678, 35361161666820070, 38855739468559462, 42350317270298854, 42936578677827502, 42936578677827502, 42936578677827502, 42936578677827502, 42936578677827502, 42936578677827502, 42936578677827502, 42936578677827502], 37965203366431537, 38196620289138724⟩
  | 20 => ⟨2, 20, 41019269399339204, [450219356222278, 4122370915676102, 7794522475129926, 11466674034583750, 15138825594037574, 18810977153491398, 22483128712945222, 26155280272399046, 29827431831852870, 33499583391306694, 37171734950760518, 40843886510214342, 44516038069668166, 44854262555407334, 44854262555407334, 44854262555407334, 44854262555407334, 44854262555407334, 44854262555407334, 44854262555407334, 44854262555407334], 39764832989231440, 39996804331446530⟩
  | 21 => ⟨2, 21, 42877350256202817, [485639187221414, 4335364504389670, 8185089821557926, 12034815138726182, 15884540455894438, 19734265773062694, 23583991090230950, 27433716407399206, 31283441724567462, 35133167041735718, 38982892358903974, 42832617676072230, 46682342993240486, 46720333703607278, 46720333703607278, 46720333703607278, 46720333703607278, 46720333703607278, 46720333703607278, 46720333703607278, 46720333703607278], 41562418180219915, 41795001826572881⟩
  | 22 => ⟨2, 22, 44706809027119038, [521643142423558, 4548942217306246, 8576241292188934, 12603540367071622, 16630839441954310, 20658138516836998, 24685437591719686, 28712736666602374, 32740035741485062, 36767334816367750, 40794633891250438, 44821932966133126, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830, 48557782765859830], 43333425717072426, 43566563782933295⟩
  | 23 => ⟨2, 23, 46507645712087867, [558231221828710, 4763104054425830, 8967976887022950, 13172849719620070, 17377722552217190, 21582595384814310, 25787468217411430, 29992341050008550, 34197213882605670, 38402086715202790, 42606959547799910, 46811832380397030, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990, 50366609742164990], 45089830148849737, 45323522634218509⟩
  | 24 => ⟨2, 24, 48279860311109304, [595403425436870, 4977850015748422, 9360296606059974, 13742743196371526, 18125189786683078, 22507636376994630, 26890082967306182, 31272529557617734, 35654976147929286, 40037422738240838, 44419869328552390, 48802315918863942, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758, 52146814632522758], 46831631475551848, 47065878380428523⟩
  | 25 => ⟨2, 25, 50023452824183349, [633159753248038, 5193180101274022, 9753200449300006, 14313220797325990, 18873241145351974, 23433261493377958, 27993281841403942, 32553302189429926, 37113322537455910, 41673342885481894, 46233363233507878, 50793383581533862, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134, 53898397436933134], 48543934527102955, 48778677966857560⟩
  | 26 => ⟨2, 26, 51723636126419484, [671500205262214, 5409094311002630, 10146688416743046, 14884282522483462, 19621876628223878, 24359470733964294, 29097064839704710, 33834658945445126, 38572253051185542, 43309847156925958, 48047441262666374, 52785035368406790, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814, 55605773964258814], 50255945519451658, 50491243378714166⟩
  | 27 => ⟨2, 27, 53394029094302211, [710424781479398, 5625592644934246, 10540760508389094, 15455928371843942, 20371096235298790, 25286264098753638, 30201431962208486, 35116599825663334, 40031767689118182, 44946935552573030, 49862103416027878, 54777271279482726, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086, 57283360157231086], 51937289988243341, 52173084382383779⟩
  | 28 => ⟨2, 28, 55002720981238462, [749933481899590, 5842675103068870, 10935416724238150, 16028158345407430, 21120899966576710, 26213641587745990, 31306383208915270, 36399124830084550, 41491866451253830, 46584608072423110, 51677349693592390, 56770091314761670, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310, 58897651136763310], 53602863103553808, 53839154032572176⟩
  | 29 => ⟨2, 29, 56595825534508815, [790026306522790, 6060341685406502, 11330657064290214, 16600972443173926, 21871287822057638, 27141603200941350, 32411918579825062, 37682233958708774, 42952549337592486, 48222864716476198, 53493180095359910, 58763495474243622, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422, 60497151848876422], 55235433198495223, 55472162777761548⟩
  | 30 => ⟨2, 30, 58140847883317194, [830703255348998, 6278592391947142, 11726481528545286, 17174370665143430, 22622259801741574, 28070148938339718, 33518038074937862, 38965927211536006, 44413816348134150, 49861705484732294, 55309594621330438, 60757483757928582, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774, 62047773290280774], 56868879482640250, 57106105596784505⟩
  | 31 => ⟨2, 31, 59653743400960133, [871964328378214, 6497427222690790, 12122890117003366, 17748353011315942, 23373815905628518, 28999278799941094, 34624741694253670, 40250204588566246, 45875667482878822, 51501130377191398, 57126593271503974, 62752056165816550, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686, 63566267900519686], 58468154498010209, 58705819262402421⟩
  | 32 => ⟨2, 32, 61116220217329066, [913809525610438, 6716846177637446, 12519882829664454, 18322919481691462, 24125956133718470, 29928992785745478, 35732029437772486, 41535066089799494, 47338102741826502, 53141139393853510, 58944176045880518, 64747212697907526, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806, 65033546743237806], 60050489911492936, 60288593326133105⟩
  | 33 => ⟨2, 33, 62526525959814969, [956238847045670, 6936849256787110, 12917459666528550, 18898070076269990, 24878680486011430, 30859290895752870, 36839901305494310, 42820511715235750, 48801122124977190, 54781732534718630, 60762342944460070, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110, 66447857445826110], 61615885723088431, 61854427787976557⟩
  | 34 => ⟨2, 34, 63902368374323400, [999252292683910, 7157436460139782, 13315620627595654, 19473804795051526, 25631988962507398, 31790173129963270, 37948357297419142, 44106541464875014, 50264725632330886, 56422909799786758, 62581093967242630, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942, 67827704820436942], 63144189644893818, 63383112475399928⟩
  | 35 => ⟨2, 35, 65223703218136769, [1042849862525158, 7378607787695462, 13714365712865766, 20050123638036070, 26385881563206374, 32721639488376678, 39057397413546982, 45393155338717286, 51728913263887590, 58064671189057894, 64400429114228198, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926, 69152247558105926], 64654385716405957, 64893689312530051⟩
  | 36 => ⟨2, 36, 66509406485566650, [1087031556569414, 7600363239454150, 14113694922338886, 20627026605223622, 27140358288108358, 33653689970993094, 40167021653877830, 46680353336762566, 53193685019647302, 59707016702532038, 66220348385416774, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422, 70441158719391422], 66146473937624848, 66386158299366926⟩
  | 37 => ⟨2, 37, 67738265685489437, [1131797374816678, 7822702815415846, 14513608256015014, 21204513696614182, 27895419137213350, 34586324577812518, 41277230018411686, 47968135459010854, 54659040899610022, 61349946340209190, 68040851780808358, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038, 71672428746923038], 67598549648038591, 67838556890768680⟩
  | 38 => ⟨2, 38, 68886731829969492, [1177147317266950, 8045626515580550, 14914105713894150, 21782584912207750, 28651064110521350, 35519543308834950, 42388022507148550, 49256501705462150, 56124980903775750, 62993460102089350, 69861939300402950, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350, 72821711586518350], 69031349259753070, 69271679383471170⟩
  | 39 => ⟨2, 39, 69996061652848011, [1223081383920230, 8269134339948262, 15315187295976294, 22361240252004326, 29407293208032358, 36453346164060390, 43499399120088422, 50545452076116454, 57591505032144486, 64637557988172518, 71683610944200550, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126, 73931858104512126], 70444872772768285, 70685525777474396⟩
  | 40 => ⟨2, 40, 71043290290392364, [1269599574776518, 8493226288518982, 15716853002261446, 22940479716003910, 30164106429746374, 37387733143488838, 44611359857231302, 51834986570973766, 59058613284716230, 66282239998458694, 73505866712201158, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950, 74979106370924950], 71839120187084236, 72080096072778358⟩
  | 41 => ⟨2, 41, 72026665369993527, [1316701889835814, 8717902361292710, 16119102832749606, 23520303304206502, 30921503775663398, 38322704247120294, 45723904718577190, 53125105190034086, 60526305661490982, 67927506132947878, 75328706604404774, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798, 75961704013147798], 73189850345376991, 73431091227429151⟩
  | 42 => ⟨2, 42, 72920301406903830, [1364388329098118, 8943162558269446, 16521936787440774, 24100711016612102, 31679485245783430, 39258259474954758, 46837033704126086, 54415807933297414, 61994582162468742, 69573356391640070, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214, 76852968480186214], 74520136156564466, 74761642034974664⟩
  | 43 => ⟨2, 43, 73770128128588533, [1412658892563430, 9169006879449190, 16925354866334950, 24681702853220710, 32438050840106470, 40194398826992230, 47950746813877990, 55707094800763750, 63463442787649510, 71219790774535270, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030, 77700423631999030], 75804568214916713, 76046281205054976⟩
  | 44 => ⟨2, 44, 74500241453413650, [1461513580231750, 9395435324831942, 17329357069432134, 25263278814032326, 33197200558632518, 41131122303232710, 49065044047832902, 56998965792433094, 64932887537033286, 72866809281633478, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902, 78425774188211902], 77067387677757664, 77309307779623992⟩
  | 45 => ⟨2, 45, 75157155233047449, [1510952392103078, 9622447894417702, 17733943396732326, 25845438899046950, 33956934401361574, 42068429903676198, 50179925405990822, 58291420908305446, 66402916410620070, 74514411912934694, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670, 79077128132986670], 78335172199223283, 78577357297447649⟩
  | 46 => ⟨2, 46, 75739117094880906, [1560975328177414, 9850044588206470, 18139113848235526, 26428183108264582, 34717252368293638, 43006321628322694, 51295390888351750, 59584460148380806, 67873529408409862, 76162598668438918, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310, 79652733093714310], 79582512373583622, 79824962468166026⟩
  | 47 => ⟨2, 47, 76163213466843939, [1611582388454758, 10078225406198246, 18544868423941734, 27011511441685222, 35478154459428710, 43944797477172198, 52411440494915686, 60878083512659174, 69344726530402662, 77811369548146150, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382, 80067284299584382], 80337727857625021, 80579458909855922⟩
  | 48 => ⟨2, 48, 76505348430570534, [1662773572935110, 10306990348393030, 18951207123850950, 27595423899308870, 36239640674766790, 44883857450224710, 53528074225682630, 62172291001140550, 70816507776598470, 79460724552056390, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230, 80399077030971230], 80684348423974024, 80924607933663773⟩
  | 49 => ⟨2, 49, 76679103668772561, [1714548881618470, 10536339414790822, 19358129947963174, 28179920481135526, 37001711014307878, 45823501547480230, 54645292080652582, 63467082613824934, 72288873146997286, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366, 80559301771846366], 80859820587245283, 81098377015873988⟩
  | 50 => ⟨2, 50, 76706275796776634, [1766908314504838, 10766272605391622, 19765636896278406, 28765001187165190, 37764365478051974, 46763729768938758, 55763094059825542, 64762458350712326, 73761822641599110, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 51 => ⟨2, 51, 76706275796776634, [1819851871594214, 10996789920195430, 20173727968796646, 29350666017397862, 38527604065999078, 47704542114600294, 56881480163201510, 66058418211802726, 75235356260403942, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 52 => ⟨2, 52, 76706275796776634, [1873379552886598, 11227891359202246, 20582403165517894, 29936914971833542, 39291426778149190, 48645938584464838, 58000450390780486, 67354962197096134, 76709474003411782, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 53 => ⟨2, 53, 76706275796776634, [1927491358381990, 11459576922412070, 20991662486442150, 30523748050472230, 40055833614502310, 49587919178532390, 59120004742562470, 68652090306592550, 78184175870622630, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 54 => ⟨2, 54, 76706275796776634, [1982187288080390, 11691846609824902, 21401505931569414, 31111165253313926, 40820824575058438, 50530483896802950, 60240143218547462, 69949802540291974, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 55 => ⟨2, 55, 76706275796776634, [2037467341981798, 11924700421440742, 21811933500899686, 31699166580358630, 41586399659817574, 51473632739276518, 61360865818735462, 71248098898194406, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 56 => ⟨2, 56, 76706275796776634, [2093331520086214, 12158138357259590, 22222945194432966, 32287752031606342, 42352558868779718, 52417365705953094, 62482172543126470, 72546979380299846, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 57 => ⟨2, 57, 76706275796776634, [2149779822393638, 12392160417281446, 22634541012169254, 32876921607057062, 43119302201944870, 53361682796832678, 63604063391720486, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 58 => ⟨2, 58, 76706275796776634, [2206812248904070, 12626766601506310, 23046720954108550, 33466675306710790, 43886629659313030, 54306584011915270, 64726538364517510, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 59 => ⟨2, 59, 76706275796776634, [2264428799617510, 12861956909934182, 23459485020250854, 34057013130567526, 44654541240884198, 55252069351200870, 65849597461517542, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 60 => ⟨2, 60, 76706275796776634, [2322629474533958, 13097731342565062, 23872833210596166, 34647935078627270, 45423036946658374, 56198138814689478, 66973240682720582, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 61 => ⟨2, 61, 76706275796776634, [2381414273653414, 13334089899398950, 24286765525144486, 35239441150890022, 46192116776635558, 57144792402381094, 66980583342606526, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 62 => ⟨2, 62, 76706275796776634, [2440783196975878, 13571032580435846, 24701281963895814, 35831531347355782, 46961780730815750, 58092030114275718, 66980583342606526, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 63 => ⟨2, 63, 76706275796776634, [2500736244501350, 13808559385675750, 25116382526850150, 36424205668024550, 47732028809198950, 59039851950373350, 66980583342606526, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 64 => ⟨2, 64, 76706275796776634, [2561273416229830, 14046670315118662, 25532067214007494, 37017464112896326, 48502861011785158, 59039851950373350, 66980583342606526, 73846443986608294, 78765151135033702, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190, 80570552203783190], 80886633132153706, 81123312825831448⟩
  | 65 => ⟨2, 65, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 66 => ⟨2, 66, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 67 => ⟨2, 67, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 68 => ⟨2, 68, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 69 => ⟨2, 69, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 70 => ⟨2, 70, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 71 => ⟨2, 71, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 72 => ⟨2, 72, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 73 => ⟨2, 73, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 74 => ⟨2, 74, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 75 => ⟨2, 75, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 76 => ⟨2, 76, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 77 => ⟨2, 77, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 78 => ⟨2, 78, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 79 => ⟨2, 79, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 80 => ⟨2, 80, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 81 => ⟨2, 81, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 82 => ⟨2, 82, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 83 => ⟨2, 83, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 84 => ⟨2, 84, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 85 => ⟨2, 85, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 86 => ⟨2, 86, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 87 => ⟨2, 87, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 88 => ⟨2, 88, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 89 => ⟨2, 89, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 90 => ⟨2, 90, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 91 => ⟨2, 91, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 92 => ⟨2, 92, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 93 => ⟨2, 93, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 94 => ⟨2, 94, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 95 => ⟨2, 95, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 96 => ⟨2, 96, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 97 => ⟨2, 97, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 98 => ⟨2, 98, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 99 => ⟨2, 99, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 100 => ⟨2, 100, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 101 => ⟨2, 101, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 102 => ⟨2, 102, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 103 => ⟨2, 103, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 104 => ⟨2, 104, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 105 => ⟨2, 105, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 106 => ⟨2, 106, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 107 => ⟨2, 107, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 108 => ⟨2, 108, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 109 => ⟨2, 109, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 110 => ⟨2, 110, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 111 => ⟨2, 111, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 112 => ⟨2, 112, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 113 => ⟨2, 113, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 114 => ⟨2, 114, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 115 => ⟨2, 115, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 116 => ⟨2, 116, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 117 => ⟨2, 117, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 118 => ⟨2, 118, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 119 => ⟨2, 119, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 120 => ⟨2, 120, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 121 => ⟨2, 121, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 122 => ⟨2, 122, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 123 => ⟨2, 123, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | 124 => ⟨2, 124, 76706275796776634, [80570552203783190], 80886633132153706, 81123312825831448⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02
end PackedLocator_LocatorPhase6800ReceiptRowData02

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03. -/
section PackedLocator_LocatorPhase6800ReceiptRowData03

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨3, 0, 4077, 5962, 3520, 3927⟩
  | 1 => ⟨3, 1, 4058, 5961, 3507, 3911⟩
  | 2 => ⟨3, 2, 4038, 5960, 3493, 3894⟩
  | 3 => ⟨3, 3, 4018, 5959, 3479, 3878⟩
  | 4 => ⟨3, 4, 3998, 5958, 3466, 3862⟩
  | 5 => ⟨3, 5, 3978, 5957, 3453, 3847⟩
  | 6 => ⟨3, 6, 3958, 5956, 3440, 3832⟩
  | 7 => ⟨3, 7, 3937, 5955, 3428, 3818⟩
  | 8 => ⟨3, 8, 3915, 5954, 3416, 3805⟩
  | 9 => ⟨3, 9, 3894, 5953, 3404, 3792⟩
  | 10 => ⟨3, 10, 3872, 5952, 3392, 3779⟩
  | 11 => ⟨3, 11, 3850, 5951, 3381, 3766⟩
  | 12 => ⟨3, 12, 3828, 5950, 3370, 3752⟩
  | 13 => ⟨3, 13, 3806, 5949, 3358, 3739⟩
  | 14 => ⟨3, 14, 3784, 5948, 3346, 3725⟩
  | 15 => ⟨3, 15, 3761, 5947, 3334, 3711⟩
  | 16 => ⟨3, 16, 3738, 5946, 3322, 3697⟩
  | 17 => ⟨3, 17, 3714, 5945, 3310, 3682⟩
  | 18 => ⟨3, 18, 3690, 5944, 3297, 3668⟩
  | 19 => ⟨3, 19, 3666, 5943, 3284, 3653⟩
  | 20 => ⟨3, 20, 3642, 5942, 3272, 3637⟩
  | 21 => ⟨3, 21, 3618, 5941, 3258, 3622⟩
  | 22 => ⟨3, 22, 3593, 5940, 3245, 3606⟩
  | 23 => ⟨3, 23, 3567, 5939, 3231, 3590⟩
  | 24 => ⟨3, 24, 3541, 5938, 3218, 3574⟩
  | 25 => ⟨3, 25, 3514, 5937, 3204, 3557⟩
  | 26 => ⟨3, 26, 3488, 5936, 3189, 3540⟩
  | 27 => ⟨3, 27, 3461, 5935, 3175, 3523⟩
  | 28 => ⟨3, 28, 3433, 5934, 3160, 3505⟩
  | 29 => ⟨3, 29, 3405, 5933, 3145, 3487⟩
  | 30 => ⟨3, 30, 3376, 5932, 3130, 3469⟩
  | 31 => ⟨3, 31, 3346, 5931, 3114, 3450⟩
  | 32 => ⟨3, 32, 3317, 5930, 3099, 3431⟩
  | 33 => ⟨3, 33, 3286, 5929, 3083, 3412⟩
  | 34 => ⟨3, 34, 3255, 5928, 3066, 3392⟩
  | 35 => ⟨3, 35, 3222, 5927, 3050, 3372⟩
  | 36 => ⟨3, 36, 3190, 5926, 3033, 3351⟩
  | 37 => ⟨3, 37, 3156, 5925, 3015, 3330⟩
  | 38 => ⟨3, 38, 3121, 5924, 2998, 3309⟩
  | 39 => ⟨3, 39, 3085, 5923, 2980, 3287⟩
  | 40 => ⟨3, 40, 3048, 5922, 2962, 3265⟩
  | 41 => ⟨3, 41, 3010, 5921, 2943, 3242⟩
  | 42 => ⟨3, 42, 2970, 5920, 2925, 3218⟩
  | 43 => ⟨3, 43, 2929, 5919, 2908, 3194⟩
  | 44 => ⟨3, 44, 2886, 5918, 2892, 3172⟩
  | 45 => ⟨3, 45, 2841, 5917, 2875, 3151⟩
  | 46 => ⟨3, 46, 2793, 5916, 2858, 3130⟩
  | 47 => ⟨3, 47, 2743, 5915, 2840, 3109⟩
  | 48 => ⟨3, 48, 2689, 5914, 2822, 3087⟩
  | 49 => ⟨3, 49, 2632, 5913, 2804, 3064⟩
  | 50 => ⟨3, 50, 2571, 5912, 2785, 3040⟩
  | 51 => ⟨3, 51, 2506, 5911, 2766, 3016⟩
  | 52 => ⟨3, 52, 2436, 5910, 2746, 2991⟩
  | 53 => ⟨3, 53, 2363, 5909, 2725, 2965⟩
  | 54 => ⟨3, 54, 2285, 5908, 2704, 2938⟩
  | 55 => ⟨3, 55, 2204, 5907, 2682, 2910⟩
  | 56 => ⟨3, 56, 2118, 5906, 2660, 2881⟩
  | 57 => ⟨3, 57, 2028, 5905, 2637, 2851⟩
  | 58 => ⟨3, 58, 1934, 5904, 2613, 2820⟩
  | 59 => ⟨3, 59, 1836, 5903, 2588, 2788⟩
  | 60 => ⟨3, 60, 1734, 5902, 2563, 2754⟩
  | 61 => ⟨3, 61, 1628, 5901, 2538, 2719⟩
  | 62 => ⟨3, 62, 1517, 5778, 2513, 2685⟩
  | 63 => ⟨3, 63, 1403, 4807, 2488, 2649⟩
  | 64 => ⟨3, 64, 1284, 3800, 2461, 2610⟩
  | 65 => ⟨3, 65, 1161, 2760, 2433, 2570⟩
  | 66 => ⟨3, 66, 1035, 1685, 2403, 2527⟩
  | 67 => ⟨3, 67, 904, 577, 2373, 2483⟩
  | 68 => ⟨3, 68, 769, 0, 2341, 2435⟩
  | 69 => ⟨3, 69, 629, 0, 2307, 2386⟩
  | 70 => ⟨3, 70, 486, 0, 2272, 2334⟩
  | 71 => ⟨3, 71, 339, 0, 2235, 2279⟩
  | 72 => ⟨3, 72, 187, 0, 2197, 2222⟩
  | 73 => ⟨3, 73, 32, 0, 2156, 2164⟩
  | 74 => ⟨3, 74, 0, 0, 2114, 2103⟩
  | 75 => ⟨3, 75, 0, 0, 2070, 2040⟩
  | 76 => ⟨3, 76, 0, 0, 2024, 1975⟩
  | 77 => ⟨3, 77, 0, 0, 1976, 1908⟩
  | 78 => ⟨3, 78, 0, 0, 1927, 1838⟩
  | 79 => ⟨3, 79, 0, 0, 1875, 1765⟩
  | 80 => ⟨3, 80, 0, 0, 1822, 1690⟩
  | 81 => ⟨3, 81, 0, 0, 1767, 1612⟩
  | 82 => ⟨3, 82, 0, 0, 1710, 1531⟩
  | 83 => ⟨3, 83, 0, 0, 1652, 1448⟩
  | 84 => ⟨3, 84, 0, 0, 1592, 1362⟩
  | 85 => ⟨3, 85, 0, 0, 1531, 1274⟩
  | 86 => ⟨3, 86, 0, 0, 1467, 1184⟩
  | 87 => ⟨3, 87, 0, 0, 1401, 1094⟩
  | 88 => ⟨3, 88, 0, 0, 1333, 1001⟩
  | 89 => ⟨3, 89, 0, 0, 1262, 907⟩
  | 90 => ⟨3, 90, 0, 0, 1190, 809⟩
  | 91 => ⟨3, 91, 0, 0, 1115, 709⟩
  | 92 => ⟨3, 92, 0, 0, 1039, 606⟩
  | 93 => ⟨3, 93, 0, 0, 962, 501⟩
  | 94 => ⟨3, 94, 0, 0, 883, 393⟩
  | 95 => ⟨3, 95, 0, 0, 803, 282⟩
  | 96 => ⟨3, 96, 0, 0, 722, 168⟩
  | 97 => ⟨3, 97, 0, 0, 640, 52⟩
  | 98 => ⟨3, 98, 0, 0, 555, 0⟩
  | 99 => ⟨3, 99, 0, 0, 468, 0⟩
  | 100 => ⟨3, 100, 0, 0, 379, 0⟩
  | 101 => ⟨3, 101, 0, 0, 287, 0⟩
  | 102 => ⟨3, 102, 0, 0, 193, 0⟩
  | 103 => ⟨3, 103, 0, 0, 97, 0⟩
  | 104 => ⟨3, 104, 0, 0, 0, 0⟩
  | 105 => ⟨3, 105, 0, 0, 0, 0⟩
  | 106 => ⟨3, 106, 0, 0, 0, 0⟩
  | 107 => ⟨3, 107, 0, 0, 0, 0⟩
  | 108 => ⟨3, 108, 0, 0, 0, 0⟩
  | 109 => ⟨3, 109, 0, 0, 0, 0⟩
  | 110 => ⟨3, 110, 0, 0, 0, 0⟩
  | 111 => ⟨3, 111, 0, 0, 0, 0⟩
  | 112 => ⟨3, 112, 0, 0, 0, 0⟩
  | 113 => ⟨3, 113, 0, 0, 0, 0⟩
  | 114 => ⟨3, 114, 0, 0, 0, 0⟩
  | 115 => ⟨3, 115, 0, 0, 0, 0⟩
  | 116 => ⟨3, 116, 0, 0, 0, 0⟩
  | 117 => ⟨3, 117, 0, 0, 0, 0⟩
  | 118 => ⟨3, 118, 0, 0, 0, 0⟩
  | 119 => ⟨3, 119, 0, 0, 0, 0⟩
  | 120 => ⟨3, 120, 0, 0, 0, 0⟩
  | 121 => ⟨3, 121, 0, 0, 0, 0⟩
  | 122 => ⟨3, 122, 0, 0, 0, 0⟩
  | 123 => ⟨3, 123, 0, 0, 0, 0⟩
  | 124 => ⟨3, 124, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨3, 0, 3181575986338306, [0, 401208330801023, 931867823771535, 1462527316742047, 1993186809712559, 2523846302683071, 3054505795653583, 3585165288624095, 4115824781594607, 4646484274565119, 5177143767535631, 5707803260506143, 6238462753476655, 6769122246447167, 6873857672691347, 6873857672691347, 6873857672691347, 6873857672691347, 6873857672691347, 6873857672691347, 6873857672691347], 5701017469363665, 5925023793479268⟩
  | 1 => ⟨3, 1, 4238235220251341, [0, 489774136731618, 1103997150947314, 1718220165163010, 2332443179378706, 2946666193594402, 3560889207810098, 4175112222025794, 4789335236241490, 5403558250457186, 6017781264672882, 6632004278888578, 7246227293104274, 7860450307319970, 7943289595421429, 7943289595421429, 7943289595421429, 7943289595421429, 7943289595421429, 7943289595421429, 7943289595421429], 6640620497376204, 6865181240999710⟩
  | 2 => ⟨3, 2, 7537933053382598, [0, 784662026617271, 1652193100874487, 2519724175131703, 3387255249388919, 4254786323646135, 5122317397903351, 5989848472160567, 6857379546417783, 7724910620674999, 8592441694932215, 9459972769189431, 10327503843446647, 11195034917703863, 11254963051122947, 11254963051122947, 11254963051122947, 11254963051122947, 11254963051122947, 11254963051122947, 11254963051122947], 9521556759859918, 9746614038361354⟩
  | 3 => ⟨3, 3, 11046501295226085, [0, 1102385701149211, 2241500211747675, 3380614722346139, 4519729232944603, 5658843743543067, 6797958254141531, 7937072764739995, 9076187275338459, 10215301785936923, 11354416296535387, 12493530807133851, 13632645317732315, 14771759828330779, 14775506915536695, 14775506915536695, 14775506915536695, 14775506915536695, 14775506915536695, 14775506915536695, 14775506915536695], 12588959710315549, 12814513523694915⟩
  | 4 => ⟨3, 4, 14520228240960004, [10304795308351, 1421002742248063, 2831700689187775, 4242398636127487, 5653096583067199, 7063794530006911, 8474492476946623, 9885190423886335, 11295888370826047, 12706586317765759, 14117284264705471, 15527982211645183, 16938680158584895, 18261209483840875, 18261209483840875, 18261209483840875, 18261209483840875, 18261209483840875, 18261209483840875, 18261209483840875, 18261209483840875], 15636777320378892, 15862885553266161⟩
  | 5 => ⟨3, 5, 17959113890584355, [58231766632867, 1740513149913827, 3422794533194787, 5105075916475747, 6787357299756707, 8469638683037667, 10151920066318627, 11834201449599587, 13516482832880547, 15198764216161507, 16881045599442467, 18563326982723427, 20245608366004387, 21712070756035487, 21712070756035487, 21712070756035487, 21712070756035487, 21712070756035487, 21712070756035487, 21712070756035487, 21712070756035487], 18662260766269435, 18888923418664607⟩
  | 6 => ⟨3, 6, 21363158244099138, [107052104524295, 2060916924146503, 4014781743768711, 5968646563390919, 7922511383013127, 9876376202635335, 11830241022257543, 13784105841879751, 15737970661501959, 17691835481124167, 19645700300746375, 21599565120368583, 23553429939990791, 25128090732120531, 25128090732120531, 25128090732120531, 25128090732120531, 25128090732120531, 25128090732120531, 25128090732120531, 25128090732120531], 21665410047987178, 21892627119890253⟩
  | 7 => ⟨3, 7, 24725837814277575, [156765808982635, 2382214064946091, 4607662320909547, 6833110576873003, 9058558832836459, 11284007088799915, 13509455344763371, 15734903600726827, 17960351856690283, 20185800112653739, 22411248368617195, 24636696624580651, 26862144880544107, 28501948858622443, 28501948858622443, 28501948858622443, 28501948858622443, 28501948858622443, 28501948858622443, 28501948858622443, 28501948858622443], 24653440822147193, 24881270198188144⟩
  | 8 => ⟨3, 8, 28044472501418930, [207372880007887, 2704404572312591, 5201436264617295, 7698467956921999, 10195499649226703, 12692531341531407, 15189563033836111, 17686594726140815, 20183626418445519, 22680658110750223, 25177689803054927, 27674721495359631, 30171753187664335, 31830965035840487, 31830965035840487, 31830965035840487, 31830965035840487, 31830965035840487, 31830965035840487, 31830965035840487, 31830965035840487], 27620924165268232, 27849365845447059⟩
  | 9 => ⟨3, 9, 31333002646543671, [258873317600051, 3027488446246003, 5796103574891955, 8564718703537907, 11333333832183859, 14101948960829811, 16870564089475763, 19639179218121715, 22407794346767667, 25176409475413619, 27945024604059571, 30713639732705523, 33482254861351475, 35130673737288703, 35130673737288703, 35130673737288703, 35130673737288703, 35130673737288703, 35130673737288703, 35130673737288703, 35130673737288703], 30567860077350295, 30796914061666998⟩
  | 10 => ⟨3, 10, 34575701175497506, [311267121759127, 3351465686746327, 6391664251733527, 9431862816720727, 12472061381707927, 15512259946695127, 18552458511682327, 21592657076669527, 24632855641656727, 27673054206643927, 30713252771631127, 33753451336618327, 36793649901605527, 38383753756319227, 38383753756319227, 38383753756319227, 38383753756319227, 38383753756319227, 38383753756319227, 38383753756319227, 38383753756319227], 33494248558393382, 33723914846847961⟩
  | 11 => ⟨3, 11, 37779984942074125, [364554292485115, 3676336293813563, 6988118295142011, 10299900296470459, 13611682297798907, 16923464299127355, 20235246300455803, 23547028301784251, 26858810303112699, 30170592304441147, 33482374305769595, 36794156307098043, 40105938308426491, 41598419012972535, 41598419012972535, 41598419012972535, 41598419012972535, 41598419012972535, 41598419012972535, 41598419012972535, 41598419012972535], 36410878731280213, 36641215208502641⟩
  | 12 => ⟨3, 12, 40945853946273528, [418734829778015, 4002100267447711, 7585465705117407, 11168831142787103, 14752196580456799, 18335562018126495, 21918927455796191, 25502292893465887, 29085658331135583, 32669023768805279, 36252389206474975, 39835754644144671, 43419120081814367, 44774669507248627, 44774669507248627, 44774669507248627, 44774669507248627, 44774669507248627, 44774669507248627, 44774669507248627, 44774669507248627], 39308748206261892, 39539754872252169⟩
  | 13 => ⟨3, 13, 44073308188095715, [473808733637827, 4328757607648771, 8183706481659715, 12038655355670659, 15893604229681603, 19748553103692547, 23603501977703491, 27458450851714435, 31313399725725379, 35168348599736323, 39023297473747267, 42878246347758211, 46733195221769155, 47912505239147503, 47912505239147503, 47912505239147503, 47912505239147503, 47912505239147503, 47912505239147503, 47912505239147503, 47912505239147503], 42175281127321875, 42406900097450028⟩
  | 14 => ⟨3, 14, 47162347667540686, [529776004064551, 4656308314416743, 8782840624768935, 12909372935121127, 17035905245473319, 21162437555825511, 25288969866177703, 29415502176529895, 33542034486882087, 37668566797234279, 41795099107586471, 45921631417938663, 50048163728290855, 51011926208669163, 51011926208669163, 51011926208669163, 51011926208669163, 51011926208669163, 51011926208669163, 51011926208669163, 51011926208669163], 45021266617342882, 45253497891608911⟩
  | 15 => ⟨3, 15, 50199301964846367, [586636641058187, 4984752387751627, 9382868134445067, 13780983881138507, 18179099627831947, 22577215374525387, 26975331121218827, 31373446867912267, 35771562614605707, 40169678361299147, 44567794107992587, 48965909854686027, 53364025601379467, 54058464929804747, 54058464929804747, 54058464929804747, 54058464929804747, 54058464929804747, 54058464929804747, 54058464929804747, 54058464929804747], 47846704676324913, 48079548254728818⟩
  | 16 => ⟨3, 16, 53196054766641008, [644390644618735, 5314089827653423, 9983789010688111, 14653488193722799, 19323187376757487, 23992886559792175, 28662585742826863, 33332284925861551, 38001984108896239, 42671683291930927, 47341382474965615, 52011081658000303, 56680780841034991, 57064802155429291, 57064802155429291, 57064802155429291, 57064802155429291, 57064802155429291, 57064802155429291, 57064802155429291, 57064802155429291], 50651595304267968, 50885051186809749⟩
  | 17 => ⟨3, 17, 56137148920028711, [703038014746195, 5644320634122131, 10585603253498067, 15526885872874003, 20468168492249939, 25409451111625875, 30350733731001811, 35292016350377747, 40233298969753683, 45174581589129619, 50115864208505555, 55057146827881491, 59998429447257427, 60014683666400111, 60014683666400111, 60014683666400111, 60014683666400111, 60014683666400111, 60014683666400111, 60014683666400111, 60014683666400111], 53435938501172047, 53670006687851704⟩
  | 18 => ⟨3, 18, 59036254844771550, [762578751440567, 5975444807157751, 11188310862874935, 16401176918592119, 21614042974309303, 26826909030026487, 32039775085743671, 37252641141460855, 42465507197178039, 47678373252895223, 52891239308612407, 58104105364329591, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067, 62922576948726067], 56182691578186046, 56417314184373606⟩
  | 19 => ⟨3, 19, 61893372540869525, [823012854701851, 6307462346760283, 11791911838818715, 17276361330877147, 22760810822935579, 28245260314994011, 33729709807052443, 39214159299110875, 44698608791169307, 50183058283227739, 55667507775286171, 61151957267344603, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159, 65788482002407159], 58907110491027245, 59142287516722708⟩
  | 20 => ⟨3, 20, 64708502008322636, [884340324530047, 6640373252929727, 12396406181329407, 18152439109729087, 23908472038128767, 29664504966528447, 35420537894928127, 41176570823327807, 46932603751727487, 52688636680127167, 58444669608526847, 64200702536926527, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387, 68612398827443387], 61628024661680572, 61863813991513911⟩
  | 21 => ⟨3, 21, 67481643247130883, [946561160925155, 6974177525666083, 13001793890407011, 19029410255147939, 25057026619888867, 31084642984629795, 37112259349370723, 43139875714111651, 49167492078852579, 55195108443593507, 61222724808334435, 67250341173075363, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751, 71394327423834751], 64288945824191243, 64525231688902512⟩
  | 22 => ⟨3, 22, 70192872271563808, [1009675363887175, 7308875164969351, 13608074966051527, 19907274767133703, 26206474568215879, 32505674369298055, 38804874170380231, 45104073971462407, 51403273772544583, 57702473573626759, 64001673374708935, 70300873175791111, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007, 74113546739604007], 66946362244514042, 67183202528733214⟩
  | 23 => ⟨3, 23, 72839508981920675, [1073682933416107, 7644466170839531, 14215249408262955, 20786032645686379, 27356815883109803, 33927599120533227, 40498382357956651, 47069165595380075, 53639948832803499, 60210732070226923, 66781515307650347, 73352298545073771, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419, 76767376675050419], 69559934978978377, 69797271798075479⟩
  | 24 => ⟨3, 24, 75440583997365030, [1138583869511951, 7980950543276623, 14823317217041295, 21665683890805967, 28508050564570639, 35350417238335311, 42192783912099983, 49035150585864655, 55877517259629327, 62719883933393999, 69562250607158671, 76404617280923343, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319, 79375644915584319], 72171789704388664, 72409680942993669⟩
  | 25 => ⟨3, 25, 77973493232465679, [1204378172174707, 8318328282280627, 15432278392386547, 22546228502492467, 29660178612598387, 36774128722704307, 43888078832810227, 51002028942916147, 58115979053022067, 65229929163127987, 72343879273233907, 79457829383339827, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727, 81914950309527727], 74738014010806663, 74976401784289598⟩
  | 26 => ⟨3, 26, 80482551491518098, [1271065841404375, 8656599387851543, 16042132934298711, 23427666480745879, 30813200027193047, 38198733573640215, 45584267120087383, 52969800666534551, 60355334212981719, 67740867759428887, 75126401305876055, 82511934852323223, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691, 84431201793669691], 77255927798531638, 77494754222262530⟩
  | 27 => ⟨3, 27, 82921657237092987, [1338646877200955, 8995763859989371, 16652880842777787, 24309997825566203, 31967114808354619, 39624231791143035, 47281348773931451, 54938465756719867, 62595582739508283, 70252699722296699, 77909816705085115, 85566933687873531, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339, 86876703698087339], 79773016943769477, 80012339902378299⟩
  | 28 => ⟨3, 28, 85288130369489610, [1407121279564447, 9335821698694111, 17264522117823775, 25193222536953439, 33121922956083103, 41050623375212767, 48979323794342431, 56908024213472095, 64836724632601759, 72765425051731423, 80694125470861087, 88622825889990751, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935, 89248775923079935], 82240008837180468, 82479770446037247⟩
  | 29 => ⟨3, 29, 87605468340706073, [1476489048494851, 9676772903965763, 17877056759436675, 26077340614907587, 34277624470378499, 42477908325849411, 50678192181320323, 58878476036791235, 67078759892262147, 75279043747733059, 83479327603203971, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371, 91571712986892371], 84681093100151011, 84921293359255747⟩
  | 30 => ⟨3, 30, 89846600232476622, [1546750183992167, 10018617475804327, 18490484767616487, 26962352059428647, 35434219351240807, 43906086643052967, 52377953934865127, 60849821226677287, 69321688518489447, 77793555810301607, 86265423102113767, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107, 93817646905012107], 87096269732681106, 87336908642033799⟩
  | 31 => ⟨3, 31, 92008845945100521, [1617904686056395, 10361355414209803, 19104806142363211, 27848256870516619, 36591707598670027, 45335158326823435, 54078609054976843, 62822059783130251, 71565510511283659, 80308961239437067, 89052411967590475, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407, 95983897577738407], 89456882280549793, 89697901955520470⟩
  | 32 => ⟨3, 32, 94147240681676190, [1689952554687535, 10704986719182191, 19720020883676847, 28735055048171503, 37750089212666159, 46765123377160815, 55780157541655471, 64795191706150127, 73810225870644783, 82825260035139439, 91840294199634095, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263, 98127094340663263], 91819350285632080, 92060808610850714⟩
  | 33 => ⟨3, 33, 96175211488004895, [1762893789885587, 11049511390721491, 20336128991557395, 29622746592393299, 38909364193229203, 48195981794065107, 57482599394901011, 66769216995736915, 76055834596572819, 85342452197408723, 94629069798244627, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583, 100158273040847583], 94125467472919135, 94367306563755753⟩
  | 34 => ⟨3, 34, 98148686933751968, [1836728391650551, 11394929428827703, 20953130466004855, 30511331503182007, 40069532540359159, 49627733577536311, 59185934614713463, 68744135651890615, 78302336689067767, 87860537726244919, 97418738763422071, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271, 102134956380450271], 96372553742710222, 96614715714534851⟩
  | 35 => ⟨3, 35, 100004591516716781, [1911456359982427, 11741240833500827, 21571025307019227, 31400809780537627, 41230594254056027, 51060378727574427, 60890163201092827, 70719947674611227, 80549732148129627, 90379516621648027, 100209301095166427, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127, 103992474724777127], 98622388836281821, 98864931573724434⟩
  | 36 => ⟨3, 36, 101834858390499540, [1987077694881215, 12088445604740863, 22189813514600511, 32291181424460159, 42392549334319807, 52493917244179455, 62595285154039103, 72696653063898751, 82798020973758399, 92899388883618047, 103000756793477695, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715, 105825152426168715], 100811406279223628, 101054271897654252⟩
  | 37 => ⟨3, 37, 103542194202098567, [2063592396346915, 12436543742547811, 22809495088748707, 33182446434949603, 43555397781150499, 53928349127351395, 64301300473552291, 74674251819753187, 85047203165954083, 95420154512154979, 105793105858355875, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999, 107533304932882999], 102936925971834907, 103180056586623569⟩
  | 38 => ⟨3, 38, 105155456602913440, [2141000464379527, 12785535246921671, 23430070029463815, 34074604812005959, 44719139594548103, 55363674377090247, 66008209159632391, 76652743942174535, 87297278724716679, 97941813507258823, 108586348289800967, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343, 109146586962566343], 105066087854793610, 105309541350570283⟩
  | 39 => ⟨3, 39, 106671965493243423, [2219301898979051, 13135420117862443, 24051538336745835, 34967656555629227, 45883774774512619, 56799892993396011, 67716011212279403, 78632129431162795, 89548247650046187, 100464365868929579, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011, 110662318415518011], 107129965254287961, 107373683746422672⟩
  | 40 => ⟨3, 40, 108089040773387780, [2298496700145487, 13486198355370127, 24673900010594767, 35861601665819407, 47049303321044047, 58237004976268687, 69424706631493327, 80612408286717967, 91800109941942607, 102987811597167247, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267, 112077819192037267], 109162574823940392, 109406558312433141⟩
  | 41 => ⟨3, 41, 109404002343645775, [2378584867878835, 13837869959444723, 25297155051010611, 36756440142576499, 48215725234142387, 59675010325708275, 71134295417274163, 82593580508840051, 94052865600405939, 105512150691971827, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375, 113390409192423375], 111126326443860823, 111370517044081637⟩
  | 42 => ⟨3, 42, 110576378787247974, [2459566402179095, 14190434930086231, 25921303457993367, 37652171985900503, 49383040513807639, 61113909041714775, 72844777569621911, 84575646097529047, 96306514625436183, 108037383153343319, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115, 114558819933660115], 113095506987262502, 113339962583841354⟩
  | 43 => ⟨3, 43, 111639494588428515, [2541441303046267, 14543893267294651, 26546345231543035, 38548797195791419, 50551249160039803, 62553701124288187, 74556153088536571, 86558605052784955, 98561057017033339, 110563508981281723, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411, 115617172966228411], 115072796553846165, 115317575031413028⟩
  | 44 => ⟨3, 44, 112551091597284140, [2624209570480351, 14898244971069983, 27172280371659615, 39446315772249247, 51720351172838879, 63994386573428511, 76268421974018143, 88542457374607775, 100816492775197407, 113090528175787039, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219, 116522413073978219], 116819253925767652, 117064065861172661⟩
  | 45 => ⟨3, 45, 113305809614413377, [2707871204481347, 15253490041412227, 27799108878343107, 40344727715273987, 52890346552204867, 65435965389135747, 77981584226066627, 90527203062997507, 103072821899928387, 115618440736859267, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067, 117269180057508067], 117580534053684179, 117824048100437955⟩
  | 46 => ⟨3, 46, 113856923657078408, [2792426205049255, 15609628478321383, 28426830751593511, 41244033024865639, 54061235298137767, 66878437571409895, 79695639844682023, 92512842117954151, 105330044391226279, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351, 117809951867833351], 118136133698971618, 118378176203184242⟩
  | 47 => ⟨3, 47, 114238651576080283, [2877874572184075, 15966660281797451, 29055445991410827, 42144231701024203, 55233017410637579, 68321803120250955, 81410588829864331, 94499374539477707, 107588160249091083, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907, 118179743422001907], 118520962881819313, 118761418074230839⟩
  | 48 => ⟨3, 48, 114359330139077190, [2964216305885807, 16324585451840431, 29684954597795055, 43045323743749679, 56405692889704303, 69766062035658927, 83126431181613551, 96486800327568175, 109847169473522799, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 49 => ⟨3, 49, 114359330139077190, [3051451406154451, 16683403988450323, 30315356570746195, 43947309153042067, 57579261735337939, 71211214317633811, 84843166899929683, 98475119482225555, 112107072064521427, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 50 => ⟨3, 50, 114359330139077190, [3139579872990007, 17043115891627127, 30946651910264247, 44850187928901367, 58753723947538487, 72657259966175607, 86560795984812727, 100464332003449847, 114367868022086967, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 51 => ⟨3, 51, 114359330139077190, [3228601706392475, 17403721161370843, 31578840616349211, 45753960071327579, 59929079526305947, 74104198981284315, 88279318436262683, 102454437891241051, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 52 => ⟨3, 52, 114359330139077190, [3318516906361855, 17765219797681471, 32211922689001087, 46658625580320703, 61105328471640319, 75552031362959935, 89998734254279551, 104445437145599167, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 53 => ⟨3, 53, 114359330139077190, [3409325472898147, 18127611800559011, 32845898128219875, 47564184455880739, 62282470783541603, 77000757111202467, 91719043438863331, 106437329766524195, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 54 => ⟨3, 54, 114359330139077190, [3501027406001351, 18490897170003463, 33480766934005575, 48470636698007687, 63460506462009799, 78450376226011911, 93440245990014023, 108430115754016135, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 55 => ⟨3, 55, 114359330139077190, [3593622705671467, 18855075906014827, 34116529106358187, 49377982306701547, 64639435507044907, 79900888707388267, 95162341907731627, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 56 => ⟨3, 56, 114359330139077190, [3687111371908495, 19220148008593103, 34753184645277711, 50286221281962319, 65819257918646927, 81352294555331535, 96885331192016143, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 57 => ⟨3, 57, 114359330139077190, [3781493404712435, 19586113477738291, 35390733550764147, 51195353623790003, 66999973696815859, 82804593769841715, 98609213842867571, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 58 => ⟨3, 58, 114359330139077190, [3876768804083287, 19952972313450391, 36029175822817495, 52105379332184599, 68181582841551703, 84257786350918807, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 59 => ⟨3, 59, 114359330139077190, [3972937570021051, 20320724515729403, 36668511461437755, 53016298407146107, 69364085352854459, 85711872298562811, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 60 => ⟨3, 60, 114359330139077190, [4069999702525727, 20689370084575327, 37308740466624927, 53928110848674527, 70547481230724127, 87166851612773727, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 61 => ⟨3, 61, 114359330139077190, [4167955201597315, 21058909019988163, 37949862838379011, 54840816656769859, 71731770475160707, 88622724293551555, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 62 => ⟨3, 62, 114359330139077190, [4266804067235815, 21429341321967911, 38591878576700007, 55754415831432103, 72916953086164199, 88622724293551555, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 63 => ⟨3, 63, 114359330139077190, [4366546299441227, 21800666990514571, 39234787681587915, 56668908372661259, 74103029063734603, 88622724293551555, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 64 => ⟨3, 64, 114359330139077190, [4467181898213551, 22172886025628143, 39878590153042735, 57584294280457327, 75289998407871919, 88622724293551555, 100333989860285911, 110423795108074987, 116629557346219419, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351, 118285297355178351], 118641974031108864, 118880610373199400⟩
  | 65 => ⟨3, 65, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 66 => ⟨3, 66, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 67 => ⟨3, 67, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 68 => ⟨3, 68, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 69 => ⟨3, 69, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 70 => ⟨3, 70, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 71 => ⟨3, 71, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 72 => ⟨3, 72, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 73 => ⟨3, 73, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 74 => ⟨3, 74, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 75 => ⟨3, 75, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 76 => ⟨3, 76, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 77 => ⟨3, 77, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 78 => ⟨3, 78, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 79 => ⟨3, 79, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 80 => ⟨3, 80, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 81 => ⟨3, 81, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 82 => ⟨3, 82, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 83 => ⟨3, 83, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 84 => ⟨3, 84, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 85 => ⟨3, 85, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 86 => ⟨3, 86, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 87 => ⟨3, 87, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 88 => ⟨3, 88, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 89 => ⟨3, 89, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 90 => ⟨3, 90, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 91 => ⟨3, 91, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 92 => ⟨3, 92, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 93 => ⟨3, 93, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 94 => ⟨3, 94, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 95 => ⟨3, 95, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 96 => ⟨3, 96, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 97 => ⟨3, 97, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 98 => ⟨3, 98, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 99 => ⟨3, 99, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 100 => ⟨3, 100, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 101 => ⟨3, 101, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 102 => ⟨3, 102, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 103 => ⟨3, 103, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 104 => ⟨3, 104, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 105 => ⟨3, 105, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 106 => ⟨3, 106, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 107 => ⟨3, 107, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 108 => ⟨3, 108, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 109 => ⟨3, 109, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 110 => ⟨3, 110, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 111 => ⟨3, 111, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 112 => ⟨3, 112, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 113 => ⟨3, 113, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 114 => ⟨3, 114, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 115 => ⟨3, 115, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 116 => ⟨3, 116, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 117 => ⟨3, 117, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 118 => ⟨3, 118, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 119 => ⟨3, 119, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 120 => ⟨3, 120, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 121 => ⟨3, 121, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 122 => ⟨3, 122, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | 123 => ⟨3, 123, 114359330139077190, [118285297355178351], 118641974031108864, 118880610373199400⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03
end PackedLocator_LocatorPhase6800ReceiptRowData03

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData04. -/
section PackedLocator_LocatorPhase6800ReceiptRowData04

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData04

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨4, 0, 3985, 5961, 3460, 3854⟩
  | 1 => ⟨4, 1, 3965, 5960, 3447, 3839⟩
  | 2 => ⟨4, 2, 3945, 5959, 3435, 3825⟩
  | 3 => ⟨4, 3, 3924, 5958, 3423, 3812⟩
  | 4 => ⟨4, 4, 3903, 5957, 3411, 3799⟩
  | 5 => ⟨4, 5, 3882, 5956, 3400, 3786⟩
  | 6 => ⟨4, 6, 3860, 5955, 3389, 3774⟩
  | 7 => ⟨4, 7, 3839, 5954, 3377, 3761⟩
  | 8 => ⟨4, 8, 3818, 5953, 3366, 3748⟩
  | 9 => ⟨4, 9, 3797, 5952, 3355, 3734⟩
  | 10 => ⟨4, 10, 3775, 5951, 3343, 3721⟩
  | 11 => ⟨4, 11, 3753, 5950, 3331, 3707⟩
  | 12 => ⟨4, 12, 3730, 5949, 3319, 3693⟩
  | 13 => ⟨4, 13, 3707, 5948, 3307, 3679⟩
  | 14 => ⟨4, 14, 3683, 5947, 3295, 3664⟩
  | 15 => ⟨4, 15, 3660, 5946, 3282, 3649⟩
  | 16 => ⟨4, 16, 3637, 5945, 3269, 3634⟩
  | 17 => ⟨4, 17, 3613, 5944, 3257, 3619⟩
  | 18 => ⟨4, 18, 3589, 5943, 3243, 3604⟩
  | 19 => ⟨4, 19, 3564, 5942, 3230, 3588⟩
  | 20 => ⟨4, 20, 3539, 5941, 3217, 3572⟩
  | 21 => ⟨4, 21, 3513, 5940, 3203, 3556⟩
  | 22 => ⟨4, 22, 3488, 5939, 3189, 3539⟩
  | 23 => ⟨4, 23, 3462, 5938, 3175, 3522⟩
  | 24 => ⟨4, 24, 3435, 5937, 3160, 3505⟩
  | 25 => ⟨4, 25, 3408, 5936, 3146, 3487⟩
  | 26 => ⟨4, 26, 3380, 5935, 3131, 3470⟩
  | 27 => ⟨4, 27, 3352, 5934, 3115, 3451⟩
  | 28 => ⟨4, 28, 3324, 5933, 3100, 3433⟩
  | 29 => ⟨4, 29, 3295, 5932, 3084, 3414⟩
  | 30 => ⟨4, 30, 3265, 5931, 3068, 3395⟩
  | 31 => ⟨4, 31, 3234, 5930, 3052, 3375⟩
  | 32 => ⟨4, 32, 3203, 5929, 3036, 3355⟩
  | 33 => ⟨4, 33, 3171, 5928, 3019, 3335⟩
  | 34 => ⟨4, 34, 3139, 5927, 3002, 3314⟩
  | 35 => ⟨4, 35, 3105, 5926, 2984, 3293⟩
  | 36 => ⟨4, 36, 3070, 5925, 2967, 3271⟩
  | 37 => ⟨4, 37, 3035, 5924, 2949, 3249⟩
  | 38 => ⟨4, 38, 2998, 5923, 2931, 3226⟩
  | 39 => ⟨4, 39, 2960, 5922, 2914, 3203⟩
  | 40 => ⟨4, 40, 2921, 5921, 2898, 3181⟩
  | 41 => ⟨4, 41, 2880, 5920, 2882, 3160⟩
  | 42 => ⟨4, 42, 2838, 5919, 2866, 3141⟩
  | 43 => ⟨4, 43, 2793, 5918, 2849, 3120⟩
  | 44 => ⟨4, 44, 2746, 5917, 2832, 3099⟩
  | 45 => ⟨4, 45, 2697, 5916, 2814, 3077⟩
  | 46 => ⟨4, 46, 2644, 5915, 2796, 3055⟩
  | 47 => ⟨4, 47, 2588, 5914, 2777, 3032⟩
  | 48 => ⟨4, 48, 2528, 5913, 2758, 3008⟩
  | 49 => ⟨4, 49, 2464, 5912, 2738, 2984⟩
  | 50 => ⟨4, 50, 2396, 5911, 2718, 2958⟩
  | 51 => ⟨4, 51, 2324, 5910, 2698, 2932⟩
  | 52 => ⟨4, 52, 2248, 5909, 2676, 2905⟩
  | 53 => ⟨4, 53, 2168, 5908, 2655, 2877⟩
  | 54 => ⟨4, 54, 2083, 5907, 2632, 2849⟩
  | 55 => ⟨4, 55, 1995, 5906, 2609, 2819⟩
  | 56 => ⟨4, 56, 1902, 5905, 2585, 2788⟩
  | 57 => ⟨4, 57, 1806, 5904, 2561, 2756⟩
  | 58 => ⟨4, 58, 1705, 5903, 2537, 2722⟩
  | 59 => ⟨4, 59, 1600, 5902, 2513, 2690⟩
  | 60 => ⟨4, 60, 1491, 5603, 2489, 2656⟩
  | 61 => ⟨4, 61, 1378, 4640, 2463, 2620⟩
  | 62 => ⟨4, 62, 1261, 3643, 2437, 2582⟩
  | 63 => ⟨4, 63, 1140, 2611, 2409, 2543⟩
  | 64 => ⟨4, 64, 1014, 1545, 2380, 2501⟩
  | 65 => ⟨4, 65, 885, 447, 2350, 2457⟩
  | 66 => ⟨4, 66, 751, 0, 2318, 2411⟩
  | 67 => ⟨4, 67, 614, 0, 2285, 2362⟩
  | 68 => ⟨4, 68, 472, 0, 2250, 2311⟩
  | 69 => ⟨4, 69, 326, 0, 2214, 2257⟩
  | 70 => ⟨4, 70, 176, 0, 2176, 2201⟩
  | 71 => ⟨4, 71, 22, 0, 2137, 2143⟩
  | 72 => ⟨4, 72, 0, 0, 2095, 2083⟩
  | 73 => ⟨4, 73, 0, 0, 2052, 2020⟩
  | 74 => ⟨4, 74, 0, 0, 2007, 1956⟩
  | 75 => ⟨4, 75, 0, 0, 1960, 1890⟩
  | 76 => ⟨4, 76, 0, 0, 1911, 1821⟩
  | 77 => ⟨4, 77, 0, 0, 1860, 1749⟩
  | 78 => ⟨4, 78, 0, 0, 1807, 1675⟩
  | 79 => ⟨4, 79, 0, 0, 1753, 1598⟩
  | 80 => ⟨4, 80, 0, 0, 1696, 1519⟩
  | 81 => ⟨4, 81, 0, 0, 1639, 1438⟩
  | 82 => ⟨4, 82, 0, 0, 1579, 1353⟩
  | 83 => ⟨4, 83, 0, 0, 1519, 1266⟩
  | 84 => ⟨4, 84, 0, 0, 1456, 1177⟩
  | 85 => ⟨4, 85, 0, 0, 1391, 1085⟩
  | 86 => ⟨4, 86, 0, 0, 1324, 993⟩
  | 87 => ⟨4, 87, 0, 0, 1255, 899⟩
  | 88 => ⟨4, 88, 0, 0, 1184, 802⟩
  | 89 => ⟨4, 89, 0, 0, 1110, 703⟩
  | 90 => ⟨4, 90, 0, 0, 1034, 601⟩
  | 91 => ⟨4, 91, 0, 0, 957, 497⟩
  | 92 => ⟨4, 92, 0, 0, 878, 390⟩
  | 93 => ⟨4, 93, 0, 0, 798, 280⟩
  | 94 => ⟨4, 94, 0, 0, 717, 168⟩
  | 95 => ⟨4, 95, 0, 0, 635, 53⟩
  | 96 => ⟨4, 96, 0, 0, 551, 0⟩
  | 97 => ⟨4, 97, 0, 0, 465, 0⟩
  | 98 => ⟨4, 98, 0, 0, 377, 0⟩
  | 99 => ⟨4, 99, 0, 0, 287, 0⟩
  | 100 => ⟨4, 100, 0, 0, 194, 0⟩
  | 101 => ⟨4, 101, 0, 0, 99, 0⟩
  | 102 => ⟨4, 102, 0, 0, 2, 0⟩
  | 103 => ⟨4, 103, 0, 0, 0, 0⟩
  | 104 => ⟨4, 104, 0, 0, 0, 0⟩
  | 105 => ⟨4, 105, 0, 0, 0, 0⟩
  | 106 => ⟨4, 106, 0, 0, 0, 0⟩
  | 107 => ⟨4, 107, 0, 0, 0, 0⟩
  | 108 => ⟨4, 108, 0, 0, 0, 0⟩
  | 109 => ⟨4, 109, 0, 0, 0, 0⟩
  | 110 => ⟨4, 110, 0, 0, 0, 0⟩
  | 111 => ⟨4, 111, 0, 0, 0, 0⟩
  | 112 => ⟨4, 112, 0, 0, 0, 0⟩
  | 113 => ⟨4, 113, 0, 0, 0, 0⟩
  | 114 => ⟨4, 114, 0, 0, 0, 0⟩
  | 115 => ⟨4, 115, 0, 0, 0, 0⟩
  | 116 => ⟨4, 116, 0, 0, 0, 0⟩
  | 117 => ⟨4, 117, 0, 0, 0, 0⟩
  | 118 => ⟨4, 118, 0, 0, 0, 0⟩
  | 119 => ⟨4, 119, 0, 0, 0, 0⟩
  | 120 => ⟨4, 120, 0, 0, 0, 0⟩
  | 121 => ⟨4, 121, 0, 0, 0, 0⟩
  | 122 => ⟨4, 122, 0, 0, 0, 0⟩
  | 123 => ⟨4, 123, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨4, 0, 8616877634594976, [0, 853261636655148, 1822629934931196, 2791998233207244, 3761366531483292, 4730734829759340, 5700103128035388, 6669471426311436, 7638839724587484, 8608208022863532, 9577576321139580, 10546944619415628, 11516312917691676, 12383642447728140, 12383642447728140, 12383642447728140, 12383642447728140, 12383642447728140, 12383642447728140, 12383642447728140, 12383642447728140], 10571511626559153, 10798814976623248⟩
  | 1 => ⟨4, 1, 10164417371723142, [0, 993848484409491, 2088562064553315, 3183275644697139, 4277989224840963, 5372702804984787, 6467416385128611, 7562129965272435, 8656843545416259, 9751557125560083, 10846270705703907, 11940984285847731, 13035697865991555, 13943157807426567, 13943157807426567, 13943157807426567, 13943157807426567, 13943157807426567, 13943157807426567, 13943157807426567, 13943157807426567], 11950922648542332, 12178780418114330⟩
  | 2 => ⟨4, 2, 13423949554323926, [0, 1296196817160812, 2649444723708012, 4002692630255212, 5355940536802412, 6709188443349612, 8062436349896812, 9415684256444012, 10768932162991212, 12122180069538412, 13475427976085612, 14828675882632812, 16181923789180012, 17214665612597612, 17214665612597612, 17214665612597612, 17214665612597612, 17214665612597612, 17214665612597612, 17214665612597612, 17214665612597612], 14828564903662678, 15057034977372552⟩
  | 3 => ⟨4, 3, 18027842044506891, [10633034013908, 1729474055529172, 3448315077044436, 5167156098559700, 6885997120074964, 8604838141590228, 10323679163105492, 12042520184620756, 13761361206136020, 15480202227651284, 17199043249166548, 18917884270681812, 20636725292197076, 21829736659104052, 21829736659104052, 21829736659104052, 21829736659104052, 21829736659104052, 21829736659104052, 21829736659104052, 21829736659104052], 18892243684277945, 19121326062125695⟩
  | 4 => ⟨4, 4, 22582427568526400, [79519766345020, 2163953902828348, 4248388039311676, 6332822175795004, 8417256312278332, 10501690448761660, 12586124585244988, 14670558721728316, 16754992858211644, 18839426994694972, 20923861131178300, 23008295267661628, 25092729404144956, 26395500739447036, 26395500739447036, 26395500739447036, 26395500739447036, 26395500739447036, 26395500739447036, 26395500739447036, 26395500739447036], 22928262459484444, 23157957141470070⟩
  | 5 => ⟨4, 5, 27087706126382453, [149609107606948, 2599636359058340, 5049663610509732, 7499690861961124, 9949718113412516, 12399745364863908, 14849772616315300, 17299799867766692, 19749827119218084, 22199854370669476, 24649881622120868, 27099908873572260, 29549936125023652, 30911957853626564, 30911957853626564, 30911957853626564, 30911957853626564, 30911957853626564, 30911957853626564, 30911957853626564, 30911957853626564], 26944575632592931, 27174940503346406⟩
  | 6 => ⟨4, 6, 31535212875221772, [220901057799692, 3036521424219148, 5852141790638604, 8667762157058060, 11483382523477516, 14299002889896972, 17114623256316428, 19930243622735884, 22745863989155340, 25561484355574796, 28377104721994252, 31192725088413708, 34008345454833164, 35369846092542572, 35369846092542572, 35369846092542572, 35369846092542572, 35369846092542572, 35369846092542572, 35369846092542572, 35369846092542572], 30935634018154282, 31166669077675606⟩
  | 7 => ⟨4, 7, 35940674891820097, [293395616923252, 3474609098310772, 6655822579698292, 9837036061085812, 13018249542473332, 16199463023860852, 19380676505248372, 22561889986635892, 25743103468023412, 28924316949410932, 32105530430798452, 35286743912185972, 38467957393573492, 39786486665464372, 39786486665464372, 39786486665464372, 39786486665464372, 39786486665464372, 39786486665464372, 39786486665464372, 39786486665464372], 34891077994996109, 35122725358655309⟩
  | 8 => ⟨4, 8, 40296829942254966, [367092784977628, 3913899381333212, 7460705977688796, 11007512574044380, 14554319170399964, 18101125766755548, 21647932363111132, 25194738959466716, 28741545555822300, 32288352152177884, 35835158748533468, 39381965344889052, 42928771941244636, 44153820272222716, 44153820272222716, 44153820272222716, 44153820272222716, 44153820272222716, 44153820272222716, 44153820272222716, 44153820272222716], 38830424196532372, 39062741748959421⟩
  | 9 => ⟨4, 9, 44603678026526379, [441992561962820, 4354392273286468, 8266791984610116, 12179191695933764, 16091591407257412, 20003991118581060, 23916390829904708, 27828790541228356, 31741190252552004, 35653589963875652, 39565989675199300, 43478389386522948, 47390789097846596, 48471846912817604, 48471846912817604, 48471846912817604, 48471846912817604, 48471846912817604, 48471846912817604, 48471846912817604, 48471846912817604], 42744515610521499, 42977503351716397⟩
  | 10 => ⟨4, 10, 48847943866057794, [518094947878828, 4796087774170540, 9074080600462252, 13352073426753964, 17630066253045676, 21908059079337388, 26186051905629100, 30464044731920812, 34742037558212524, 39020030384504236, 43298023210795948, 47576016037087660, 51854008863379372, 52726494242425708, 52726494242425708, 52726494242425708, 52726494242425708, 52726494242425708, 52726494242425708, 52726494242425708, 52726494242425708], 46619384788998654, 46852984834331428⟩
  | 11 => ⟨4, 11, 53040497521564121, [595399942725652, 5238985883985428, 9882571825245204, 14526157766504980, 19169743707764756, 23813329649024532, 28456915590284308, 33100501531544084, 37744087472803860, 42387673414063636, 47031259355323412, 51674845296583188, 56318431237842964, 56929429388008724, 56929429388008724, 56929429388008724, 56929429388008724, 56929429388008724, 56929429388008724, 56929429388008724, 56929429388008724], 50466593962067041, 50700806311537691⟩
  | 12 => ⟨4, 12, 57165658496607186, [673907546503292, 5683086602731132, 10692265658958972, 15701444715186812, 20710623771414652, 25719802827642492, 30728981883870332, 35738160940098172, 40747339996326012, 45756519052553852, 50765698108781692, 55774877165009532, 60784056221237372, 61064174786881692, 61064174786881692, 61064174786881692, 61064174786881692, 61064174786881692, 61064174786881692, 61064174786881692, 61064174786881692], 54286143129726660, 54520967783335186⟩
  | 13 => ⟨4, 13, 61236702069763531, [753617759211748, 6128389930407652, 11503162101603556, 16877934272799460, 22252706443995364, 27627478615191268, 33002250786387172, 38377022957583076, 43751795128778980, 49126567299974884, 54501339471170788, 59876111642366692, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940, 65144802783867940], 58078032291977511, 58313469249723913⟩
  | 14 => ⟨4, 14, 65235542526733350, [834530580851020, 6574895867014988, 12315261153178956, 18055626439342924, 23795991725506892, 29536357011670860, 35276722297834828, 41017087583998796, 46757452870162764, 52497818156326732, 58238183442490700, 63978548728654668, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876, 69152430598420876], 61842261448819594, 62078310710703872⟩
  | 15 => ⟨4, 15, 69197148687185439, [916646011421108, 7022604412553140, 13128562813685172, 19234521214817204, 25340479615949236, 31446438017081268, 37552396418213300, 43658354819345332, 49764313220477364, 55870271621609396, 61976230022741428, 68082188423873460, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868, 73123621182702868], 65558850107633993, 65795453789026174⟩
  | 16 => ⟨4, 16, 73104637445750808, [999964050922012, 7471515567022108, 13943067083122204, 20414618599222300, 26886170115322396, 33357721631422492, 39829273147522588, 46300824663622684, 52772376179722780, 59243927695822876, 65715479211922972, 72187030728023068, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140, 77040694365098140], 69245373543177992, 69482531644078076⟩
  | 17 => ⟨4, 17, 76936315261337203, [1084484699353732, 7921629330421892, 14758773961490052, 21595918592558212, 28433063223626372, 35270207854694532, 42107352485762692, 48944497116830852, 55781641747899012, 62618786378967172, 69455931010035332, 76293075641103492, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652, 80881159538267652], 72924217465932139, 73161987870970099⟩
  | 18 => ⟨4, 18, 80711470457175246, [1170207956716268, 8372945702752492, 15575683448788716, 22778421194824940, 29981158940861164, 37183896686897388, 44386634432933612, 51589372178969836, 58792109925006060, 65994847671042284, 73197585417078508, 80400323163114732, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812, 84665102091688812], 76528224744454790, 76766491684370680⟩
  | 19 => ⟨4, 19, 84406004274311051, [1257133823009620, 8825464684013908, 16393795545018196, 23962126406022484, 31530457267026772, 39098788128031060, 46667118989035348, 54235449850039636, 61803780711043924, 69372111572048212, 76940442433052500, 84508773294056788, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948, 88367626200160948], 80124552510187589, 80363373869611382⟩
  | 20 => ⟨4, 20, 88041610253836872, [1345262298233788, 9279186274206140, 17213110250178492, 25147034226150844, 33080958202123196, 41014882178095548, 48948806154067900, 56882730130040252, 64816654106012604, 72750578081984956, 80684502057957308, 88618426033929660, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100, 92011222471023100], 83690815052649988, 83930190831581684⟩
  | 21 => ⟨4, 21, 91591784418937191, [1434593382388772, 9734110473329188, 18033627564269604, 26333144655210020, 34632661746150436, 42932178837090852, 51231695928031268, 59531213018971684, 67830730109912100, 76130247200852516, 84429764291792932, 92729281382733348, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964, 95568589861212964], 87199816225638175, 87439688539447801⟩
  | 22 => ⟨4, 22, 95108332114312228, [1525127075474572, 10190237281383052, 18855347487291532, 27520457693200012, 36185567899108492, 44850678105016972, 53515788310925452, 62180898516833932, 70846008722742412, 79511118928650892, 88176229134559372, 96841339340467852, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332, 99093127847924332], 90676346957494330, 90916715806181886⟩
  | 23 => ⟨4, 23, 98537042777400131, [1616863377491188, 10647566698367732, 19678270019244276, 28708973340120820, 37739676660997364, 46770379981873908, 55801083302750452, 64831786623626996, 73862489944503540, 82893193265380084, 91923896586256628, 100954599907133172, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780, 102529031736101780], 94120407248218453, 94361272631783939⟩
  | 24 => ⟨4, 24, 101874308581408452, [1709802288438620, 11106098724283228, 20502395160127836, 29898691595972444, 39294988031817052, 48691284467661660, 58087580903506268, 67483877339350876, 76880173775195484, 86276470211040092, 95672766646884700, 105069063082729308, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860, 105872693698952860], 97501193124814284, 97742497158627727⟩
  | 25 => ⟨4, 25, 105147836112083525, [1803943808316868, 11565833359129540, 21327722909942212, 31089612460754884, 40851502011567556, 50613391562380228, 60375281113192900, 70137170664005572, 79899060214818244, 89660949765630916, 99422839316443588, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692, 109152617388470692], 100879109924343527, 101120910493034900⟩
  | 26 => ⟨4, 26, 108325108347955752, [1899287937125932, 12026770602906668, 22154253268687404, 32281735934468140, 42409218600248876, 52536701266029612, 62664183931810348, 72791666597591084, 82919149263371820, 93046631929152556, 103174114594933292, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892, 112335488716938892], 104191347091882846, 104433586310822176⟩
  | 27 => ⟨4, 27, 111436237092633099, [1995834674865812, 12488910455614612, 22981986236363412, 33475062017112212, 43968137797861012, 54461213578609812, 64954289359358612, 75447365140107412, 85940440920856212, 96433516701605012, 106926592482353812, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212, 115452216554212212], 107434296800639793, 107676916785197107⟩
  | 28 => ⟨4, 28, 114481222346115566, [2093584021536508, 12952252917253372, 23810921812970236, 34669590708687100, 45528259604403964, 56386928500120828, 67245597395837692, 78104266291554556, 88962935187271420, 99821604082988284, 110680272978705148, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652, 118502800900290652], 110675580041260968, 110918638676066239⟩
  | 29 => ⟨4, 29, 117423939260141107, [2192535977138020, 13416797987822948, 24641059998507876, 35865322009192804, 47089584019877732, 58313846030562660, 69538108041247588, 80762370051932516, 91986632062617444, 103210894073302372, 114435156083987300, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380, 121450319840665380], 113845170605238139, 114088610005661394⟩
  | 30 => ⟨4, 30, 120260780007917274, [2292690541670348, 13882545667323340, 25472400792976332, 37062255918629324, 48652111044282316, 60241966169935308, 71831821295588300, 83421676421241292, 95011531546894284, 106601386672547276, 118191241798200268, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948, 124291165548543948], 116977480292360014, 117221300458401253⟩
  | 31 => ⟨4, 31, 122988136762651619, [2394047715133492, 14349495955754548, 26304944196375604, 38260392436996660, 50215840677617716, 62171288918238772, 74126737158859828, 86082185399480884, 98037633640101940, 109993081880722996, 121948530121344052, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908, 127021730197133908], 120072509102626593, 120316710034285816⟩
  | 32 => ⟨4, 32, 125642134372606188, [2496607497527452, 14817648853116572, 27138690208705692, 39459731564294812, 51780772919883932, 64101814275473052, 76422855631062172, 88743896986651292, 101064938342240412, 113385979697829532, 125707021053418652, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092, 129678935700944092], 123130257036037876, 123374838733315083⟩
  | 33 => ⟨4, 33, 128181837553795671, [2600369888852228, 15287004359409412, 27973638829966596, 40660273300523780, 53346907771080964, 66033542241638148, 78720176712195332, 91406811182752516, 104093445653309700, 116780080123866884, 129466714594424068, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404, 132221049709742404], 126109096639220259, 126354001217485477⟩
  | 34 => ⟨4, 34, 130645776372343746, [2705334889107820, 15757562474633068, 28809790060158316, 41862017645683564, 54914245231208812, 67966472816734060, 81018700402259308, 94070927987784556, 107123155573309804, 120175383158835052, 133227610744360300, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308, 134687399355899308], 129048250147685714, 129293477606938943⟩
  | 35 => ⟨4, 35, 132947269824556529, [2811502498294228, 16229323198787540, 29647143899280852, 43064964599774164, 56482785300267476, 69900606000760788, 83318426701254100, 96736247401747412, 110154068102240724, 123571888802734036, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348, 136989709503227348], 131903684890199005, 132149177345810272⟩
  | 36 => ⟨4, 36, 135123645367626882, [2918872716411452, 16702286531872828, 30485700347334204, 44269114162795580, 58052527978256956, 71835941793718332, 85619355609179708, 99402769424641084, 113186183240102460, 126969597055563836, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172, 139166104675166172], 134762263600299788, 135008078936899066⟩
  | 37 => ⟨4, 37, 137217040894470931, [3027445543459492, 17176452473888932, 31325459404318372, 45474466334747812, 59623473265177252, 73772480195606692, 87921487126036132, 102070494056465572, 116219500986895012, 130368507917324452, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692, 141259519830878692], 137534718326586775, 137780798659544091⟩
  | 38 => ⟨4, 38, 139133559747809896, [3137220979438348, 17651821024835852, 32166421070233356, 46681021115630860, 61195621161028364, 75710221206425868, 90224821251823372, 104739421297220876, 119254021342618380, 133768621388015884, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556, 143174464180592556], 140265081740295202, 140511427069610556⟩
  | 39 => ⟨4, 39, 140914137211629087, [3248199024348020, 18128392184713588, 33008585345079156, 47888778505444724, 62768971665810292, 77649164826175860, 92529357986541428, 107409551146906996, 122289744307272564, 137169937467638132, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860, 144952670074539860], 143002196948383569, 143248865158686934⟩
  | 40 => ⟨4, 40, 142555165459136056, [3360379678188508, 18606165953522140, 33851952228855772, 49097738504189404, 64343524779523036, 79589311054856668, 94835097330190300, 110080883605523932, 125326669880857564, 140572456156191196, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156, 146590529685928156], 145749671777644324, 145996720753565673⟩
  | 41 => ⟨4, 41, 144002480508106517, [3473762940959812, 19085142331261508, 34696521721563204, 50307901111864900, 65919280502166596, 81530659892468292, 97142039282769988, 112753418673071684, 128364798063373380, 143976177453675076, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372, 148033081966286372], 148357369080409519, 148604683052688906⟩
  | 42 => ⟨4, 42, 145300625469318228, [3588348812661932, 19565321317931692, 35542293823201452, 51519266328471212, 67496238833740972, 83473211339010732, 99450183844280492, 115427156349550252, 131404128854820012, 147381101360089772, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052, 149325667092639052], 149664152660573402, 149910342398091475⟩
  | 43 => ⟨4, 43, 146340069769391801, [3704137293294868, 20046702913532692, 36389268533770516, 52731834154008340, 69074399774246164, 85416965394483988, 101759531014721812, 118102096634959636, 134444662255197460, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236, 150357160359113236], 150710159071434265, 150955050920301105⟩
  | 44 => ⟨4, 44, 147164153910174178, [3821128382858620, 20529287118064508, 37237445853270396, 53945604588476284, 70653763323682172, 87361922058888060, 104070080794093948, 120778239529299836, 137486398264505724, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652, 151171699333802652], 151539420984227344, 151782899175183005⟩
  | 45 => ⟨4, 45, 147765662238080463, [3939322081353188, 21013073931527140, 38086825781701092, 55160577631875044, 72234329482048996, 89308081332222948, 106381833182396900, 123455585032570852, 140529336882744804, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404, 151762068363122404], 152144722745367743, 152386671509152279⟩
  | 46 => ⟨4, 46, 148024240699353924, [4058718388778572, 21498063353920588, 38937408319062604, 56376753284204620, 73816098249346636, 91255443214488652, 108694788179630668, 126134133144772684, 143573478109914700, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 47 => ⟨4, 47, 148024240699353924, [4179317305134772, 21984255385244852, 39789193465354932, 57594131545465012, 75399069625575092, 93204007705685172, 111008945785795252, 128813883865905332, 146618821946015412, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 48 => ⟨4, 48, 148024240699353924, [4301118830421788, 22471650025499932, 40642181220578076, 58812712415656220, 76983243610734364, 95153774805812508, 113324306000890652, 131494837195968796, 149665368391046940, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 49 => ⟨4, 49, 148024240699353924, [4424122964639620, 22960247274685828, 41496371584732036, 60032495894778244, 78568620204824452, 97104744514870660, 115640868824916868, 134176993134963076, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 50 => ⟨4, 50, 148024240699353924, [4548329707788268, 23450047132802540, 42351764557816812, 61253481982831084, 80155199407845356, 99056916832859628, 117958634257873900, 136860351682888172, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 51 => ⟨4, 51, 148024240699353924, [4673739059867732, 23941049599850068, 43208360139832404, 62475670679814740, 81742981219797076, 101010291759779412, 120277602299761748, 139544912839744084, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 52 => ⟨4, 52, 148024240699353924, [4800351020878012, 24433254675828412, 44066158330778812, 63699061985729212, 83331965640679612, 102964869295630012, 122597772950580412, 142230676605530812, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 53 => ⟨4, 53, 148024240699353924, [4928165590819108, 24926662360737572, 44925159130656036, 64923655900574500, 84922152670492964, 104920649440411428, 124919146210329892, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 54 => ⟨4, 54, 148024240699353924, [5057182769691020, 25421272654577548, 45785362539464076, 66149452424350604, 86513542309237132, 106877632194123660, 127241722079010188, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 55 => ⟨4, 55, 148024240699353924, [5187402557493748, 25917085557348340, 46646768557202932, 67376451557057524, 88106134556912116, 108835817556766708, 129565500556621300, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 56 => ⟨4, 56, 148024240699353924, [5318824954227292, 26414101069049948, 47509377183872604, 68604653298695260, 89699929413517916, 110795205528340572, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 57 => ⟨4, 57, 148024240699353924, [5451449959891652, 26912319189682372, 48373188419473092, 69834057649263812, 91294926879054532, 112755796108845252, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 58 => ⟨4, 58, 148024240699353924, [5585277574486828, 27411739919245612, 49238202264004396, 71064664608763180, 92891126953521964, 114717589298280748, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 59 => ⟨4, 59, 148024240699353924, [5720307798012820, 27912363257739668, 50104418717466516, 72296474177193364, 94488529636920212, 116680585096647060, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 60 => ⟨4, 60, 148024240699353924, [5856540630469628, 28414189205164540, 50971837779859452, 73529486354554364, 96087134929249276, 117888152810282814, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 61 => ⟨4, 61, 148024240699353924, [5993976071857252, 28917217761520228, 51840459451183204, 74763701140846180, 97686942830509156, 117916069757788795, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 62 => ⟨4, 62, 148024240699353924, [6132614122175692, 29421448926806732, 52710283731437772, 75999118536068812, 99287953340699852, 117943986705294776, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 63 => ⟨4, 63, 148024240699353924, [6272454781424948, 29926882701024052, 53581310620623156, 77235738540222260, 100890166459821364, 117971903652800757, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 64 => ⟨4, 64, 148024240699353924, [6413498049605020, 30433519084172188, 54453540118739356, 78473561153306524, 102493582187873692, 117971903652800757, 131890481643163228, 143273029759037956, 150700972371879268, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188, 152006319260822188], 152404325962322142, 152644513760415661⟩
  | 65 => ⟨4, 65, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 66 => ⟨4, 66, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 67 => ⟨4, 67, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 68 => ⟨4, 68, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 69 => ⟨4, 69, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 70 => ⟨4, 70, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 71 => ⟨4, 71, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 72 => ⟨4, 72, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 73 => ⟨4, 73, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 74 => ⟨4, 74, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 75 => ⟨4, 75, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 76 => ⟨4, 76, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 77 => ⟨4, 77, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 78 => ⟨4, 78, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 79 => ⟨4, 79, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 80 => ⟨4, 80, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 81 => ⟨4, 81, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 82 => ⟨4, 82, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 83 => ⟨4, 83, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 84 => ⟨4, 84, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 85 => ⟨4, 85, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 86 => ⟨4, 86, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 87 => ⟨4, 87, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 88 => ⟨4, 88, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 89 => ⟨4, 89, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 90 => ⟨4, 90, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 91 => ⟨4, 91, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 92 => ⟨4, 92, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 93 => ⟨4, 93, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 94 => ⟨4, 94, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 95 => ⟨4, 95, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 96 => ⟨4, 96, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 97 => ⟨4, 97, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 98 => ⟨4, 98, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 99 => ⟨4, 99, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 100 => ⟨4, 100, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 101 => ⟨4, 101, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 102 => ⟨4, 102, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 103 => ⟨4, 103, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 104 => ⟨4, 104, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 105 => ⟨4, 105, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 106 => ⟨4, 106, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 107 => ⟨4, 107, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 108 => ⟨4, 108, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 109 => ⟨4, 109, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 110 => ⟨4, 110, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 111 => ⟨4, 111, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 112 => ⟨4, 112, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 113 => ⟨4, 113, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 114 => ⟨4, 114, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 115 => ⟨4, 115, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 116 => ⟨4, 116, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 117 => ⟨4, 117, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 118 => ⟨4, 118, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 119 => ⟨4, 119, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 120 => ⟨4, 120, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 121 => ⟨4, 121, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | 122 => ⟨4, 122, 148024240699353924, [152006319260822188], 152404325962322142, 152644513760415661⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData04
end PackedLocator_LocatorPhase6800ReceiptRowData04

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData05. -/
section PackedLocator_LocatorPhase6800ReceiptRowData05

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData05

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨5, 0, 3886, 5960, 3405, 3791⟩
  | 1 => ⟨5, 1, 3865, 5959, 3394, 3779⟩
  | 2 => ⟨5, 2, 3845, 5958, 3383, 3766⟩
  | 3 => ⟨5, 3, 3824, 5957, 3372, 3753⟩
  | 4 => ⟨5, 4, 3804, 5956, 3361, 3740⟩
  | 5 => ⟨5, 5, 3783, 5955, 3349, 3727⟩
  | 6 => ⟨5, 6, 3761, 5954, 3338, 3714⟩
  | 7 => ⟨5, 7, 3739, 5953, 3326, 3700⟩
  | 8 => ⟨5, 8, 3717, 5952, 3314, 3686⟩
  | 9 => ⟨5, 9, 3694, 5951, 3302, 3672⟩
  | 10 => ⟨5, 10, 3672, 5950, 3290, 3658⟩
  | 11 => ⟨5, 11, 3649, 5949, 3278, 3644⟩
  | 12 => ⟨5, 12, 3627, 5948, 3265, 3629⟩
  | 13 => ⟨5, 13, 3604, 5947, 3253, 3614⟩
  | 14 => ⟨5, 14, 3580, 5946, 3240, 3599⟩
  | 15 => ⟨5, 15, 3556, 5945, 3227, 3583⟩
  | 16 => ⟨5, 16, 3531, 5944, 3213, 3567⟩
  | 17 => ⟨5, 17, 3506, 5943, 3200, 3551⟩
  | 18 => ⟨5, 18, 3482, 5942, 3186, 3535⟩
  | 19 => ⟨5, 19, 3457, 5941, 3172, 3518⟩
  | 20 => ⟨5, 20, 3431, 5940, 3158, 3502⟩
  | 21 => ⟨5, 21, 3404, 5939, 3144, 3484⟩
  | 22 => ⟨5, 22, 3377, 5938, 3129, 3467⟩
  | 23 => ⟨5, 23, 3351, 5937, 3114, 3449⟩
  | 24 => ⟨5, 24, 3323, 5936, 3099, 3431⟩
  | 25 => ⟨5, 25, 3295, 5935, 3084, 3413⟩
  | 26 => ⟨5, 26, 3267, 5934, 3068, 3394⟩
  | 27 => ⟨5, 27, 3237, 5933, 3052, 3375⟩
  | 28 => ⟨5, 28, 3208, 5932, 3036, 3355⟩
  | 29 => ⟨5, 29, 3178, 5931, 3020, 3335⟩
  | 30 => ⟨5, 30, 3146, 5930, 3003, 3315⟩
  | 31 => ⟨5, 31, 3114, 5929, 2986, 3295⟩
  | 32 => ⟨5, 32, 3082, 5928, 2969, 3274⟩
  | 33 => ⟨5, 33, 3049, 5927, 2951, 3252⟩
  | 34 => ⟨5, 34, 3014, 5926, 2934, 3230⟩
  | 35 => ⟨5, 35, 2979, 5925, 2918, 3208⟩
  | 36 => ⟨5, 36, 2943, 5924, 2902, 3186⟩
  | 37 => ⟨5, 37, 2905, 5923, 2886, 3166⟩
  | 38 => ⟨5, 38, 2866, 5922, 2870, 3147⟩
  | 39 => ⟨5, 39, 2825, 5921, 2854, 3127⟩
  | 40 => ⟨5, 40, 2783, 5920, 2838, 3107⟩
  | 41 => ⟨5, 41, 2739, 5919, 2821, 3086⟩
  | 42 => ⟨5, 42, 2693, 5918, 2803, 3065⟩
  | 43 => ⟨5, 43, 2644, 5917, 2785, 3043⟩
  | 44 => ⟨5, 44, 2592, 5916, 2767, 3020⟩
  | 45 => ⟨5, 45, 2537, 5915, 2748, 2997⟩
  | 46 => ⟨5, 46, 2478, 5914, 2729, 2973⟩
  | 47 => ⟨5, 47, 2415, 5913, 2709, 2948⟩
  | 48 => ⟨5, 48, 2348, 5912, 2689, 2923⟩
  | 49 => ⟨5, 49, 2277, 5911, 2668, 2897⟩
  | 50 => ⟨5, 50, 2202, 5910, 2647, 2870⟩
  | 51 => ⟨5, 51, 2123, 5909, 2625, 2842⟩
  | 52 => ⟨5, 52, 2040, 5908, 2602, 2813⟩
  | 53 => ⟨5, 53, 1953, 5907, 2579, 2783⟩
  | 54 => ⟨5, 54, 1861, 5906, 2555, 2752⟩
  | 55 => ⟨5, 55, 1766, 5905, 2533, 2720⟩
  | 56 => ⟨5, 56, 1666, 5904, 2510, 2689⟩
  | 57 => ⟨5, 57, 1563, 5903, 2487, 2657⟩
  | 58 => ⟨5, 58, 1455, 5362, 2462, 2624⟩
  | 59 => ⟨5, 59, 1344, 4406, 2437, 2588⟩
  | 60 => ⟨5, 60, 1228, 3414, 2410, 2551⟩
  | 61 => ⟨5, 61, 1108, 2387, 2382, 2512⟩
  | 62 => ⟨5, 62, 984, 1327, 2354, 2471⟩
  | 63 => ⟨5, 63, 856, 234, 2324, 2427⟩
  | 64 => ⟨5, 64, 724, 0, 2292, 2382⟩
  | 65 => ⟨5, 65, 588, 0, 2260, 2334⟩
  | 66 => ⟨5, 66, 447, 0, 2226, 2284⟩
  | 67 => ⟨5, 67, 303, 0, 2190, 2231⟩
  | 68 => ⟨5, 68, 155, 0, 2153, 2176⟩
  | 69 => ⟨5, 69, 2, 0, 2114, 2119⟩
  | 70 => ⟨5, 70, 0, 0, 2073, 2059⟩
  | 71 => ⟨5, 71, 0, 0, 2030, 1997⟩
  | 72 => ⟨5, 72, 0, 0, 1986, 1933⟩
  | 73 => ⟨5, 73, 0, 0, 1940, 1867⟩
  | 74 => ⟨5, 74, 0, 0, 1892, 1799⟩
  | 75 => ⟨5, 75, 0, 0, 1842, 1728⟩
  | 76 => ⟨5, 76, 0, 0, 1790, 1655⟩
  | 77 => ⟨5, 77, 0, 0, 1736, 1580⟩
  | 78 => ⟨5, 78, 0, 0, 1680, 1502⟩
  | 79 => ⟨5, 79, 0, 0, 1622, 1421⟩
  | 80 => ⟨5, 80, 0, 0, 1563, 1338⟩
  | 81 => ⟨5, 81, 0, 0, 1503, 1253⟩
  | 82 => ⟨5, 82, 0, 0, 1441, 1164⟩
  | 83 => ⟨5, 83, 0, 0, 1377, 1074⟩
  | 84 => ⟨5, 84, 0, 0, 1311, 981⟩
  | 85 => ⟨5, 85, 0, 0, 1243, 887⟩
  | 86 => ⟨5, 86, 0, 0, 1173, 791⟩
  | 87 => ⟨5, 87, 0, 0, 1101, 692⟩
  | 88 => ⟨5, 88, 0, 0, 1026, 591⟩
  | 89 => ⟨5, 89, 0, 0, 950, 488⟩
  | 90 => ⟨5, 90, 0, 0, 871, 382⟩
  | 91 => ⟨5, 91, 0, 0, 791, 273⟩
  | 92 => ⟨5, 92, 0, 0, 709, 162⟩
  | 93 => ⟨5, 93, 0, 0, 627, 48⟩
  | 94 => ⟨5, 94, 0, 0, 543, 0⟩
  | 95 => ⟨5, 95, 0, 0, 458, 0⟩
  | 96 => ⟨5, 96, 0, 0, 371, 0⟩
  | 97 => ⟨5, 97, 0, 0, 282, 0⟩
  | 98 => ⟨5, 98, 0, 0, 191, 0⟩
  | 99 => ⟨5, 99, 0, 0, 97, 0⟩
  | 100 => ⟨5, 100, 0, 0, 1, 0⟩
  | 101 => ⟨5, 101, 0, 0, 0, 0⟩
  | 102 => ⟨5, 102, 0, 0, 0, 0⟩
  | 103 => ⟨5, 103, 0, 0, 0, 0⟩
  | 104 => ⟨5, 104, 0, 0, 0, 0⟩
  | 105 => ⟨5, 105, 0, 0, 0, 0⟩
  | 106 => ⟨5, 106, 0, 0, 0, 0⟩
  | 107 => ⟨5, 107, 0, 0, 0, 0⟩
  | 108 => ⟨5, 108, 0, 0, 0, 0⟩
  | 109 => ⟨5, 109, 0, 0, 0, 0⟩
  | 110 => ⟨5, 110, 0, 0, 0, 0⟩
  | 111 => ⟨5, 111, 0, 0, 0, 0⟩
  | 112 => ⟨5, 112, 0, 0, 0, 0⟩
  | 113 => ⟨5, 113, 0, 0, 0, 0⟩
  | 114 => ⟨5, 114, 0, 0, 0, 0⟩
  | 115 => ⟨5, 115, 0, 0, 0, 0⟩
  | 116 => ⟨5, 116, 0, 0, 0, 0⟩
  | 117 => ⟨5, 117, 0, 0, 0, 0⟩
  | 118 => ⟨5, 118, 0, 0, 0, 0⟩
  | 119 => ⟨5, 119, 0, 0, 0, 0⟩
  | 120 => ⟨5, 120, 0, 0, 0, 0⟩
  | 121 => ⟨5, 121, 0, 0, 0, 0⟩
  | 122 => ⟨5, 122, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨5, 0, 15363039266579195, [0, 1458423105839325, 2991845491288685, 4525267876738045, 6058690262187405, 7592112647636765, 9125535033086125, 10658957418535485, 12192379803984845, 13725802189434205, 15259224574883565, 16792646960332925, 18326069345782285, 19198707742764980, 19198707742764980, 19198707742764980, 19198707742764980, 19198707742764980, 19198707742764980, 19198707742764980, 19198707742764980], 16696377635923192, 16927267435085644⟩
  | 1 => ⟨5, 1, 17360914704221172, [0, 1651443315423560, 3351992743363288, 5052542171303016, 6753091599242744, 8453641027182472, 10154190455122200, 11854739883061928, 13555289311001656, 15255838738941384, 16956388166881112, 18656937594820840, 20357487022760568, 21207761736730432, 21207761736730432, 21207761736730432, 21207761736730432, 21207761736730432, 21207761736730432, 21207761736730432, 21207761736730432], 18507882843065313, 18739442830995614⟩
  | 2 => ⟨5, 2, 20166498947727252, [0, 1923285171540773, 3856259589004773, 5789234006468773, 7722208423932773, 9655182841396773, 11588157258860773, 13521131676324773, 15454106093788773, 17387080511252773, 19320054928716773, 21253029346180773, 23186003763644773, 24025321602806773, 24025321602806773, 24025321602806773, 24025321602806773, 24025321602806773, 24025321602806773, 24025321602806773, 24025321602806773], 21033509754060802, 21265739930758952⟩
  | 3 => ⟨5, 3, 25794378821181561, [79848005050577, 2472425216109457, 4865002427168337, 7257579638227217, 9650156849286097, 12042734060344977, 14435311271403857, 16827888482462737, 19220465693521617, 21613042904580497, 24005620115639377, 26398197326698257, 28790774537757137, 29664380032584557, 29664380032584557, 29664380032584557, 29664380032584557, 29664380032584557, 29664380032584557, 29664380032584557, 29664380032584557], 26063742734608097, 26296643100074096⟩
  | 4 => ⟨5, 4, 31368857896373504, [170897107319101, 3023077111972861, 5875257116626621, 8727437121280381, 11579617125934141, 14431797130587901, 17283977135241661, 20136157139895421, 22988337144549181, 25840517149202941, 28692697153856701, 31544877158510461, 34397057163164221, 35250834730346761, 35250834730346761, 35250834730346761, 35250834730346761, 35250834730346761, 35250834730346761, 35250834730346761, 35250834730346761], 31062226837966272, 31295797392200120⟩
  | 5 => ⟨5, 5, 36874277814955493, [263458060882345, 3575240859130985, 6887023657379625, 10198806455628265, 13510589253876905, 16822372052125545, 20134154850374185, 23445937648622825, 26757720446871465, 30069503245120105, 33381286043368745, 36693068841617385, 40004851639866025, 40767433205252225, 40767433205252225, 40767433205252225, 40767433205252225, 40767433205252225, 40767433205252225, 40767433205252225, 40767433205252225], 36018172938631159, 36252355797002883⟩
  | 6 => ⟨5, 6, 42306103023043368, [357530865740309, 4128916457583829, 7900302049427349, 11671687641270869, 15443073233114389, 19214458824957909, 22985844416801429, 26757230008644949, 30528615600488469, 34300001192331989, 38071386784175509, 41842772376019029, 45614157967862549, 46209639903416789, 46209639903416789, 46209639903416789, 46209639903416789, 46209639903416789, 46209639903416789, 46209639903416789, 46209639903416789], 40951647436316374, 41186500483455947⟩
  | 7 => ⟨5, 7, 47672918625458283, [453115521892993, 4684103907331393, 8915092292769793, 13146080678208193, 17377069063646593, 21608057449084993, 25839045834523393, 30070034219961793, 34301022605400193, 38532010990838593, 42762999376276993, 46993987761715393, 51224976147153793, 51586836995908393, 51586836995908393, 51586836995908393, 51586836995908393, 51586836995908393, 51586836995908393, 51586836995908393, 51586836995908393], 45839560228718861, 46075025579996310⟩
  | 8 => ⟨5, 8, 52974724622200238, [550212029340397, 5240803208373677, 9931394387406957, 14621985566440237, 19312576745473517, 24003167924506797, 28693759103540077, 33384350282573357, 38074941461606637, 42765532640639917, 47456123819673197, 52146714998706477, 56837306177739757, 56899024482727037, 56899024482727037, 56899024482727037, 56899024482727037, 56899024482727037, 56899024482727037, 56899024482727037, 56899024482727037], 50692700441342788, 50928778096758113⟩
  | 9 => ⟨5, 9, 58195376651974479, [648820388082521, 5799014360710681, 10949208333338841, 16099402305967001, 21249596278595161, 26399790251223321, 31549984223851481, 36700178196479641, 41850372169107801, 47000566141735961, 52150760114364121, 57300954086992281, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181, 62129260936331181], 55511068074188155, 55747758033741356⟩
  | 10 => ⟨5, 10, 63365651586075794, [748940598119365, 6358737364342405, 11968534130565445, 17578330896788485, 23188127663011525, 28797924429234565, 34407721195457605, 40017517961680645, 45627314727903685, 51237111494126725, 56846908260349765, 62456705026572805, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185, 67309917360509185], 60294663127254962, 60531965390946039⟩
  | 11 => ⟨5, 11, 68451748850619955, [850572659450929, 6919972219268849, 12989371779086769, 19058771338904689, 25128170898722609, 31197570458540529, 37266970018358449, 43336369578176369, 49405769137994289, 55475168697812209, 61544568257630129, 67613967817448049, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249, 72405599048883249], 65043485600543209, 65281400168372162⟩
  | 12 => ⟨5, 12, 73490492722080630, [953716572077213, 7482718925490013, 14011721278902813, 20540723632315613, 27069725985728413, 33598728339141213, 40127730692554013, 46656733045966813, 53185735399379613, 59714737752792413, 66243740106205213, 72772742459618013, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613, 77454724410420613], 69736163409485688, 69974632396822544⟩
  | 13 => ⟨5, 13, 78442035221394711, [1058372335998217, 8046977483005897, 15035582630013577, 22024187777021257, 29012792924028937, 36001398071036617, 42990003218044297, 49978608365051977, 56967213512059657, 63955818659067337, 70944423806075017, 77933028953082697, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597, 82415851333564597], 74413928871922095, 74653010163396827⟩
  | 14 => ⟨5, 14, 83301840794678038, [1164539951213941, 8612747891816501, 16060955832419061, 23509163773021621, 30957371713624181, 38405579654226741, 45853787594829301, 53301995535431861, 60750203476034421, 68198411416636981, 75646619357239541, 83094827297842101, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041, 87284444264431041], 79032525967423294, 79272161678405929⟩
  | 15 => ⟨5, 15, 88090589357109525, [1272219417724385, 9180030151921825, 17087840886119265, 24995651620316705, 32903462354514145, 40811273088711585, 48719083822909025, 56626894557106465, 64534705291303905, 72442516025501345, 80350326759698785, 88258137493896225, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645, 92081980184445645], 83613326780556493, 83853516911047031⟩
  | 16 => ⟨5, 16, 92781553588331378, [1381410735529549, 9748824263321869, 18116237791114189, 26483651318906509, 34851064846698829, 43218478374491149, 51585891902283469, 59953305430075789, 68320718957868109, 76688132485660429, 85055546013452749, 93422959541245069, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829, 96780934707003829], 88128911821575604, 88369598486944072⟩
  | 17 => ⟨5, 17, 97398437106111951, [1492113904629433, 10319130226016633, 19146146547403833, 27973162868791033, 36800179190178233, 45627195511565433, 54454211832952633, 63281228154339833, 72108244475727033, 80935260797114233, 89762277118501433, 98589293439888633, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733, 101405808516120733], 92632608218678083, 92873849303554454⟩
  | 18 => ⟨5, 18, 101970990933398478, [1604328925024037, 10890948040006117, 20177567154988197, 29464186269970277, 38750805384952357, 48037424499934437, 57324043614916517, 66610662729898597, 75897281844880677, 85183900959862757, 94470520074844837, 103757139189826917, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377, 105987149700990377], 97068065141077034, 97309802760831335⟩
  | 19 => ⟨5, 19, 106441224875591211, [1718055796713361, 11464277705290321, 21210499613867281, 30956721522444241, 40702943431021201, 50449165339598161, 60195387248175121, 69941609156752081, 79687831065329041, 89434052973906001, 99180274882482961, 108926496791059921, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441, 110465373934519441], 101462702078518545, 101704936233150776⟩
  | 20 => ⟨5, 20, 110804603378805990, [1833294519697405, 12039119221869245, 22244943924041085, 32450768626212925, 42656593328384765, 52862418030556605, 63068242732728445, 73274067434900285, 83479892137072125, 93685716839243965, 103891541541415805, 114097366243587645, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765, 114835945662823765], 105816519031002616, 106059249720512777⟩
  | 21 => ⟨5, 21, 115056590889158655, [1950045093976169, 12615472589742889, 23280900085509609, 33946327581276329, 44611755077043049, 55277182572809769, 65942610068576489, 76608037564343209, 87273465060109929, 97938892555876649, 108604320051643369, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189, 119094329332019189], 110129515998529247, 110372743222917338⟩
  | 22 => ⟨5, 22, 119228450280891160, [2068307519549653, 13193337808911253, 24318368098272853, 35443398387634453, 46568428676996053, 57693458966357653, 68818489255719253, 79943519545080853, 91068549834442453, 102193580123804053, 113318610413165653, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453, 123272584882594453], 114365202383584030, 114608868258220078⟩
  | 23 => ⟨5, 23, 123357491833424339, [2188081796417857, 13772714879374337, 25357347962330817, 36941981045287297, 48526614128243777, 60111247211200257, 71695880294156737, 83280513377113217, 94865146460069697, 106449779543026177, 118034412625982657, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177, 127408819660217177], 118557045081091933, 118801149605975938⟩
  | 24 => ⟨5, 24, 127331784708495690, [2309367924580781, 14353603801132141, 26397839677683501, 38442075554234861, 50486311430786221, 62530547307337581, 74574783183888941, 86619019060440301, 98663254936991661, 110707490813543021, 122751726690094381, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501, 131388711627884501], 122705044091052956, 122949587266184918⟩
  | 25 => ⟨5, 25, 131222925762357441, [2432165904038425, 14936004574184665, 27439843244330905, 39943681914477145, 52447520584623385, 64951359254769625, 77455197924915865, 89959036595062105, 102462875265208345, 114966713935354585, 127470552605500825, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225, 135285451774342225], 126809199413467099, 127054181238847018⟩
  | 26 => ⟨5, 26, 135030914995009592, [2556475734790789, 15519917198531909, 28483358662273029, 41446800126014149, 54410241589755269, 67373683053496389, 80337124517237509, 93300565980978629, 106264007444719749, 119227448908460869, 132190890372201989, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349, 139099040099590349], 130826973045641074, 131072335636638977⟩
  | 27 => ⟨5, 27, 138669037037252715, [2682297416837873, 16105341674173873, 29528385931509873, 42951430188845873, 56374474446181873, 69797518703517873, 83220562960853873, 96643607218189873, 110066651475525873, 123489695732861873, 136912739990197873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873, 142741167101935873], 134797879287678729, 135043622644294616⟩
  | 28 => ⟨5, 28, 142262829389001792, [2809630950179677, 16692278001110557, 30574925052041437, 44457572102972317, 58340219153903197, 72222866204834077, 86105513255764957, 99988160306695837, 113870807357626717, 127753454408557597, 141636101459488477, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137, 146339761480034137], 138721918139580064, 138968042261813935⟩
  | 29 => ⟨5, 29, 145724064829762675, [2938476334816201, 17280726179341961, 31622976023867721, 45965225868393481, 60307475712919241, 74649725557445001, 88991975401970761, 103334225246496521, 117676475091022281, 132018724935548041, 146360974780073801, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421, 149805001880897421], 142599089601345079, 142845594489196934⟩
  | 30 => ⟨5, 30, 149000314567167330, [3068833570747445, 17870686208868085, 32672538846988725, 47474391485109365, 62276244123230005, 77078096761350645, 91879949399471285, 106681802037591925, 121483654675712565, 136285507313833205, 151087359951953845, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905, 153083662445910905], 146380808265101606, 146627636033941472⟩
  | 31 => ⟨5, 31, 152181317673004625, [3200702657973409, 18462158089688929, 33723613521404449, 48985068953119969, 64246524384835489, 79507979816551009, 94769435248266529, 110030890679982049, 125292346111697569, 140553801543413089, 155815256975128609, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029, 156267076379357029], 150112635836132373, 150359786485960250⟩
  | 32 => ⟨5, 32, 155267074147274560, [3334083596494093, 19055141821804493, 34776200047114893, 50497258272425293, 66218316497735693, 81939374723046093, 97660432948356493, 113381491173666893, 129102549398977293, 144823607624287693, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793, 159355243681235793], 153794572314437380, 154042045845253268⟩
  | 33 => ⟨5, 33, 158205155197609101, [3468976386309497, 19649637405214777, 35830298424120057, 52010959443025337, 68191620461930617, 84372281480835897, 100552942499741177, 116733603518646457, 132914264537551737, 149094925556457017, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377, 162294938492932377], 157373496738260299, 157621235265434225⟩
  | 34 => ⟨5, 34, 160937084626461334, [3605381027419621, 20245644839919781, 36885908652419941, 53526172464920101, 70166436277420261, 86806700089920421, 103446963902420581, 120087227714920741, 136727491527420901, 153367755339921061, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081, 165026887550653081], 160954139179819066, 161202200587981003⟩
  | 35 => ⟨5, 35, 163564696315977887, [3743297519824465, 20843164125919505, 37943030732014545, 55042897338109585, 72142763944204625, 89242630550299665, 106342497156394705, 123442363762489745, 140542230368584785, 157642096974679825, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105, 167654518869038105], 164541035192997841, 164789477366777762⟩
  | 36 => ⟨5, 36, 166031025919906566, [3882725863524029, 21442195263213949, 39001664662903869, 56561134062593789, 74120603462283709, 91680072861973629, 109239542261663549, 126799011661353469, 144358481061043389, 161917950460733309, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469, 170120071035588469], 168081063816040296, 168329886755438201⟩
  | 37 => ⟨5, 37, 168273061686816297, [4023666058518313, 22042738251803113, 40061810445087913, 58080882638372713, 76099954831657513, 94119027024942313, 112138099218227113, 130157171411511913, 148176243604796713, 166195315798081513, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313, 172359735232626313], 171574225048946431, 171823428753962320⟩
  | 38 => ⟨5, 38, 170341720557780394, [4166118104807317, 22644793091686997, 41123468078566677, 59602143065446357, 78080818052326037, 96559493039205717, 115038168026085397, 133516843012965077, 151995517999844757, 170474192986724437, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737, 174425225467471737], 174777798018796534, 175027150950910515⟩
  | 39 => ⟨5, 39, 172170967078778343, [4310082002391041, 23248359782865601, 42186637563340161, 61124915343814721, 80063193124289281, 99001470904763841, 117939748685238401, 136878026465712961, 155816304246187521, 174754582026662081, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441, 176249709219857441], 176616375328134949, 176864661910117589⟩
  | 40 => ⟨5, 40, 173814741893472898, [4455557751269485, 23853438325338925, 43251318899408365, 62649199473477805, 82047080047547245, 101444960621616685, 120842841195686125, 140240721769755565, 159638602343825005, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965, 177887924199692965], 178268788761781676, 178515951109003002⟩
  | 41 => ⟨5, 41, 175203985845254105, [4602545351442649, 24460028719106969, 44317512086771289, 64174995454435609, 84032478822099929, 103889962189764249, 123747445557428569, 143604928925092889, 163462412292757209, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569, 179270014184121569], 179665286993738467, 179911209336938533⟩
  | 42 => ⟨5, 42, 176329627826353644, [4751044802910533, 25068130964169733, 45385217125428933, 65702303286688133, 86019389447947333, 106336475609206533, 126653561770465733, 146970647931724933, 167287734092984133, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933, 180386908065374933], 180796798916237002, 181041365486155862⟩
  | 43 => ⟨5, 43, 177115049423687961, [4901056105673137, 25677745060527217, 46454434015381297, 67231122970235377, 88007811925089457, 108784500879943537, 129561189834797617, 150337878789651697, 171114567744505777, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717, 181161190364122717], 181586013946805433, 181829051089553168⟩
  | 44 => ⟨5, 44, 177546643975604576, [5052579259730461, 26288871008179421, 47525162756628381, 68761454505077341, 89997746253526301, 111234038001975261, 132470329750424221, 153706621498873181, 174942913247322141, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441, 181579254418712441], 182019325423791280, 182260659485477971⟩
  | 45 => ⟨5, 45, 177610804820451009, [5205614265082505, 26901508807126345, 48597403349170185, 70293297891214025, 91989192433257865, 113685086975301705, 135380981517345545, 157076876059389385, 178772770601433225, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 46 => ⟨5, 46, 177610804820451009, [5360161121729269, 27515658457367989, 49671155793006709, 71826653128645429, 93982150464284149, 116137647799922869, 138293145135561589, 160448642471200309, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 47 => ⟨5, 47, 177610804820451009, [5516219829670753, 28131319958904353, 50746420088137953, 73361520217371553, 95976620346605153, 118591720475838753, 141206820605072353, 163821920734305953, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 48 => ⟨5, 48, 177610804820451009, [5673790388906957, 28748493311735437, 51823196234563917, 74897899157392397, 97972602080220877, 121047305003049357, 144122007925877837, 167196710848706317, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 49 => ⟨5, 49, 177610804820451009, [5832872799437881, 29367178515861241, 52901484232284601, 76435789948707961, 99970095665131321, 123504401381554681, 147038707097978041, 170573012814401401, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 50 => ⟨5, 50, 177610804820451009, [5993467061263525, 29987375571281765, 53981284081300005, 77975192591318245, 101969101101336485, 125963009611354725, 149956918121372965, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 51 => ⟨5, 51, 177610804820451009, [6155573174383889, 30609084477997009, 55062595781610129, 79516107085223249, 103969618388836369, 128423129692449489, 152876640996062609, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 52 => ⟨5, 52, 177610804820451009, [6319191138798973, 31232305236006973, 56145419333214973, 81058533430422973, 105971647527630973, 130884761624838973, 155797875722046973, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 53 => ⟨5, 53, 177610804820451009, [6484320954508777, 31857037845311657, 57229754736114537, 82602471626917417, 107975188517720297, 133347905408523177, 158720622299326057, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 54 => ⟨5, 54, 177610804820451009, [6650962621513301, 32483282305911061, 58315601990308821, 84147921674706581, 109980241359104341, 135812561043502101, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 55 => ⟨5, 55, 177610804820451009, [6819116139812545, 33111038617805185, 59402961095797825, 85694883573790465, 111986806051783105, 138278728529775745, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 56 => ⟨5, 56, 177610804820451009, [6988781509406509, 33740306780994029, 60491832052581549, 87243357324169069, 113994882595756589, 140746407867344109, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 57 => ⟨5, 57, 177610804820451009, [7159958730295193, 34371086795477593, 61582214860659993, 88793342925842393, 116004470991024793, 143215599056207193, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 58 => ⟨5, 58, 177610804820451009, [7332647802478597, 35003378661255877, 62674109520033157, 90344840378810437, 118015571237587717, 145686302096364997, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 59 => ⟨5, 59, 177610804820451009, [7506848725956721, 35637182378328881, 63767516030701041, 91897849683073201, 120028183335445361, 148158516987817521, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 60 => ⟨5, 60, 177610804820451009, [7682561500729565, 36272497946696605, 64862434392663645, 93452370838630685, 122042307284597725, 150632243730564765, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 61 => ⟨5, 61, 177610804820451009, [7859786126797129, 36909325366359049, 65958864605920969, 95008403845482889, 124057943085044809, 151728793539549964, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 62 => ⟨5, 62, 177610804820451009, [8038522604159413, 37547664637316213, 67056806670473013, 96565948703629813, 126075090736786613, 151728793539549964, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 63 => ⟨5, 63, 177610804820451009, [8218770932816417, 37547664637316213, 67056806670473013, 96565948703629813, 126075090736786613, 151728793539549964, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 64 => ⟨5, 64, 177610804820451009, [8218770932816417, 37547664637316213, 67056806670473013, 96565948703629813, 126075090736786613, 151728793539549964, 159265588125389541, 173950826631391205, 181219421223361609, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625, 181627493567491625], 182083126685542063, 182322584012277791⟩
  | 65 => ⟨5, 65, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 66 => ⟨5, 66, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 67 => ⟨5, 67, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 68 => ⟨5, 68, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 69 => ⟨5, 69, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 70 => ⟨5, 70, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 71 => ⟨5, 71, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 72 => ⟨5, 72, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 73 => ⟨5, 73, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 74 => ⟨5, 74, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 75 => ⟨5, 75, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 76 => ⟨5, 76, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 77 => ⟨5, 77, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 78 => ⟨5, 78, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 79 => ⟨5, 79, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 80 => ⟨5, 80, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 81 => ⟨5, 81, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 82 => ⟨5, 82, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 83 => ⟨5, 83, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 84 => ⟨5, 84, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 85 => ⟨5, 85, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 86 => ⟨5, 86, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 87 => ⟨5, 87, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 88 => ⟨5, 88, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 89 => ⟨5, 89, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 90 => ⟨5, 90, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 91 => ⟨5, 91, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 92 => ⟨5, 92, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 93 => ⟨5, 93, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 94 => ⟨5, 94, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 95 => ⟨5, 95, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 96 => ⟨5, 96, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 97 => ⟨5, 97, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 98 => ⟨5, 98, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 99 => ⟨5, 99, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 100 => ⟨5, 100, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 101 => ⟨5, 101, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 102 => ⟨5, 102, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 103 => ⟨5, 103, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 104 => ⟨5, 104, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 105 => ⟨5, 105, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 106 => ⟨5, 106, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 107 => ⟨5, 107, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 108 => ⟨5, 108, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 109 => ⟨5, 109, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 110 => ⟨5, 110, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 111 => ⟨5, 111, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 112 => ⟨5, 112, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 113 => ⟨5, 113, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 114 => ⟨5, 114, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 115 => ⟨5, 115, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 116 => ⟨5, 116, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 117 => ⟨5, 117, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 118 => ⟨5, 118, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 119 => ⟨5, 119, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 120 => ⟨5, 120, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | 121 => ⟨5, 121, 177610804820451009, [181627493567491625], 182083126685542063, 182322584012277791⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData05
end PackedLocator_LocatorPhase6800ReceiptRowData05

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData06. -/
section PackedLocator_LocatorPhase6800ReceiptRowData06

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData06

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨6, 0, 3784, 5959, 3354, 3731⟩
  | 1 => ⟨6, 1, 3763, 5958, 3343, 3718⟩
  | 2 => ⟨6, 2, 3742, 5957, 3331, 3705⟩
  | 3 => ⟨6, 3, 3720, 5956, 3320, 3691⟩
  | 4 => ⟨6, 4, 3698, 5955, 3308, 3677⟩
  | 5 => ⟨6, 5, 3676, 5954, 3296, 3664⟩
  | 6 => ⟨6, 6, 3655, 5953, 3284, 3649⟩
  | 7 => ⟨6, 7, 3633, 5952, 3272, 3635⟩
  | 8 => ⟨6, 8, 3610, 5951, 3259, 3621⟩
  | 9 => ⟨6, 9, 3588, 5950, 3247, 3606⟩
  | 10 => ⟨6, 10, 3564, 5949, 3234, 3591⟩
  | 11 => ⟨6, 11, 3540, 5948, 3221, 3575⟩
  | 12 => ⟨6, 12, 3517, 5947, 3208, 3560⟩
  | 13 => ⟨6, 13, 3493, 5946, 3195, 3544⟩
  | 14 => ⟨6, 14, 3469, 5945, 3181, 3528⟩
  | 15 => ⟨6, 15, 3445, 5944, 3167, 3512⟩
  | 16 => ⟨6, 16, 3419, 5943, 3153, 3495⟩
  | 17 => ⟨6, 17, 3394, 5942, 3139, 3478⟩
  | 18 => ⟨6, 18, 3368, 5941, 3125, 3461⟩
  | 19 => ⟨6, 19, 3342, 5940, 3110, 3444⟩
  | 20 => ⟨6, 20, 3315, 5939, 3095, 3426⟩
  | 21 => ⟨6, 21, 3288, 5938, 3080, 3408⟩
  | 22 => ⟨6, 22, 3261, 5937, 3065, 3390⟩
  | 23 => ⟨6, 23, 3232, 5936, 3049, 3371⟩
  | 24 => ⟨6, 24, 3204, 5935, 3034, 3352⟩
  | 25 => ⟨6, 25, 3175, 5934, 3018, 3332⟩
  | 26 => ⟨6, 26, 3145, 5933, 3001, 3313⟩
  | 27 => ⟨6, 27, 3114, 5932, 2985, 3293⟩
  | 28 => ⟨6, 28, 3084, 5931, 2968, 3272⟩
  | 29 => ⟨6, 29, 3052, 5930, 2951, 3251⟩
  | 30 => ⟨6, 30, 3019, 5929, 2934, 3230⟩
  | 31 => ⟨6, 31, 2986, 5928, 2918, 3208⟩
  | 32 => ⟨6, 32, 2952, 5927, 2903, 3187⟩
  | 33 => ⟨6, 33, 2916, 5926, 2888, 3167⟩
  | 34 => ⟨6, 34, 2880, 5925, 2872, 3149⟩
  | 35 => ⟨6, 35, 2842, 5924, 2857, 3130⟩
  | 36 => ⟨6, 36, 2803, 5923, 2840, 3110⟩
  | 37 => ⟨6, 37, 2763, 5922, 2824, 3090⟩
  | 38 => ⟨6, 38, 2721, 5921, 2807, 3070⟩
  | 39 => ⟨6, 39, 2677, 5920, 2790, 3049⟩
  | 40 => ⟨6, 40, 2632, 5919, 2772, 3027⟩
  | 41 => ⟨6, 41, 2583, 5918, 2754, 3005⟩
  | 42 => ⟨6, 42, 2532, 5917, 2735, 2982⟩
  | 43 => ⟨6, 43, 2477, 5916, 2717, 2959⟩
  | 44 => ⟨6, 44, 2419, 5915, 2697, 2935⟩
  | 45 => ⟨6, 45, 2357, 5914, 2677, 2910⟩
  | 46 => ⟨6, 46, 2291, 5913, 2657, 2884⟩
  | 47 => ⟨6, 47, 2221, 5912, 2636, 2858⟩
  | 48 => ⟨6, 48, 2146, 5911, 2614, 2830⟩
  | 49 => ⟨6, 49, 2068, 5910, 2592, 2802⟩
  | 50 => ⟨6, 50, 1986, 5909, 2570, 2773⟩
  | 51 => ⟨6, 51, 1900, 5908, 2547, 2743⟩
  | 52 => ⟨6, 52, 1810, 5907, 2526, 2713⟩
  | 53 => ⟨6, 53, 1716, 5906, 2504, 2684⟩
  | 54 => ⟨6, 54, 1617, 5905, 2481, 2653⟩
  | 55 => ⟨6, 55, 1515, 5885, 2457, 2621⟩
  | 56 => ⟨6, 56, 1409, 4994, 2432, 2588⟩
  | 57 => ⟨6, 57, 1298, 4078, 2407, 2553⟩
  | 58 => ⟨6, 58, 1184, 3110, 2381, 2516⟩
  | 59 => ⟨6, 59, 1065, 2088, 2353, 2477⟩
  | 60 => ⟨6, 60, 943, 1029, 2325, 2436⟩
  | 61 => ⟨6, 61, 816, 0, 2295, 2393⟩
  | 62 => ⟨6, 62, 685, 0, 2264, 2348⟩
  | 63 => ⟨6, 63, 551, 0, 2232, 2301⟩
  | 64 => ⟨6, 64, 412, 0, 2199, 2252⟩
  | 65 => ⟨6, 65, 269, 0, 2164, 2200⟩
  | 66 => ⟨6, 66, 122, 0, 2127, 2146⟩
  | 67 => ⟨6, 67, 0, 0, 2088, 2089⟩
  | 68 => ⟨6, 68, 0, 0, 2048, 2031⟩
  | 69 => ⟨6, 69, 0, 0, 2005, 1969⟩
  | 70 => ⟨6, 70, 0, 0, 1962, 1905⟩
  | 71 => ⟨6, 71, 0, 0, 1916, 1840⟩
  | 72 => ⟨6, 72, 0, 0, 1869, 1772⟩
  | 73 => ⟨6, 73, 0, 0, 1820, 1702⟩
  | 74 => ⟨6, 74, 0, 0, 1768, 1630⟩
  | 75 => ⟨6, 75, 0, 0, 1715, 1555⟩
  | 76 => ⟨6, 76, 0, 0, 1660, 1478⟩
  | 77 => ⟨6, 77, 0, 0, 1603, 1399⟩
  | 78 => ⟨6, 78, 0, 0, 1544, 1317⟩
  | 79 => ⟨6, 79, 0, 0, 1484, 1232⟩
  | 80 => ⟨6, 80, 0, 0, 1422, 1146⟩
  | 81 => ⟨6, 81, 0, 0, 1359, 1056⟩
  | 82 => ⟨6, 82, 0, 0, 1294, 965⟩
  | 83 => ⟨6, 83, 0, 0, 1227, 871⟩
  | 84 => ⟨6, 84, 0, 0, 1158, 775⟩
  | 85 => ⟨6, 85, 0, 0, 1087, 678⟩
  | 86 => ⟨6, 86, 0, 0, 1013, 577⟩
  | 87 => ⟨6, 87, 0, 0, 938, 474⟩
  | 88 => ⟨6, 88, 0, 0, 860, 369⟩
  | 89 => ⟨6, 89, 0, 0, 781, 261⟩
  | 90 => ⟨6, 90, 0, 0, 699, 150⟩
  | 91 => ⟨6, 91, 0, 0, 616, 37⟩
  | 92 => ⟨6, 92, 0, 0, 532, 0⟩
  | 93 => ⟨6, 93, 0, 0, 447, 0⟩
  | 94 => ⟨6, 94, 0, 0, 361, 0⟩
  | 95 => ⟨6, 95, 0, 0, 273, 0⟩
  | 96 => ⟨6, 96, 0, 0, 182, 0⟩
  | 97 => ⟨6, 97, 0, 0, 89, 0⟩
  | 98 => ⟨6, 98, 0, 0, 0, 0⟩
  | 99 => ⟨6, 99, 0, 0, 0, 0⟩
  | 100 => ⟨6, 100, 0, 0, 0, 0⟩
  | 101 => ⟨6, 101, 0, 0, 0, 0⟩
  | 102 => ⟨6, 102, 0, 0, 0, 0⟩
  | 103 => ⟨6, 103, 0, 0, 0, 0⟩
  | 104 => ⟨6, 104, 0, 0, 0, 0⟩
  | 105 => ⟨6, 105, 0, 0, 0, 0⟩
  | 106 => ⟨6, 106, 0, 0, 0, 0⟩
  | 107 => ⟨6, 107, 0, 0, 0, 0⟩
  | 108 => ⟨6, 108, 0, 0, 0, 0⟩
  | 109 => ⟨6, 109, 0, 0, 0, 0⟩
  | 110 => ⟨6, 110, 0, 0, 0, 0⟩
  | 111 => ⟨6, 111, 0, 0, 0, 0⟩
  | 112 => ⟨6, 112, 0, 0, 0, 0⟩
  | 113 => ⟨6, 113, 0, 0, 0, 0⟩
  | 114 => ⟨6, 114, 0, 0, 0, 0⟩
  | 115 => ⟨6, 115, 0, 0, 0, 0⟩
  | 116 => ⟨6, 116, 0, 0, 0, 0⟩
  | 117 => ⟨6, 117, 0, 0, 0, 0⟩
  | 118 => ⟨6, 118, 0, 0, 0, 0⟩
  | 119 => ⟨6, 119, 0, 0, 0, 0⟩
  | 120 => ⟨6, 120, 0, 0, 0, 0⟩
  | 121 => ⟨6, 121, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨6, 0, 23285109287548755, [0, 2217105058359698, 4439926812850146, 6662748567340594, 8885570321831042, 11108392076321490, 13331213830811938, 15554035585302386, 17776857339792834, 19999679094283282, 22222500848773730, 24445322603264178, 26668144357754626, 27187290228046803, 27187290228046803, 27187290228046803, 27187290228046803, 27187290228046803, 27187290228046803, 27187290228046803, 27187290228046803], 24028619615783991, 24263327402564692⟩
  | 1 => ⟨6, 1, 25698603270412284, [31240392176561, 2462970949779969, 4894701507383377, 7326432064986785, 9758162622590193, 12189893180193601, 14621623737797009, 17053354295400417, 19485084853003825, 21916815410607233, 24348545968210641, 26780276525814049, 29212007083417457, 29611962767233807, 29611962767233807, 29611962767233807, 29611962767233807, 29611962767233807, 29611962767233807, 29611962767233807, 29611962767233807], 26248733938529016, 26484111914077566⟩
  | 2 => ⟨6, 2, 27664181428438852, [59525725113442, 2666236332121058, 5272946939128674, 7879657546136290, 10486368153143906, 13093078760151522, 15699789367159138, 18306499974166754, 20913210581174370, 23519921188181986, 26126631795189602, 28733342402197218, 31340053009204834, 31588719481583850, 31588719481583850, 31588719481583850, 31588719481583850, 31588719481583850, 31588719481583850, 31588719481583850, 31588719481583850], 28071965801966098, 28307956081652524⟩
  | 3 => ⟨6, 3, 34232953350773811, [171225346024658, 3331548425253970, 6491871504483282, 9652194583712594, 12812517662941906, 15972840742171218, 19133163821400530, 22293486900629842, 25453809979859154, 28614133059088466, 31774456138317778, 34934779217547090, 38095102296776402, 38167872893995498, 38167872893995498, 38167872893995498, 38167872893995498, 38167872893995498, 38167872893995498, 38167872893995498, 38167872893995498], 34027950167511241, 34264610635965516⟩
  | 4 => ⟨6, 4, 40723418245787938, [284746060594498, 3998681612045506, 7712617163496514, 11426552714947522, 15140488266398530, 18854423817849538, 22568359369300546, 26282294920751554, 29996230472202562, 33710166023653570, 37424101575104578, 41138037126555586, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314, 44668719279086314], 39933579569822420, 40170852342414571⟩
  | 5 => ⟨6, 5, 47135576113481233, [400087868822962, 4667635892495666, 8935183916168370, 13202731939841074, 17470279963513778, 21737827987186482, 26005376010859186, 30272924034531890, 34540472058204594, 38808020081877298, 43075568105550002, 47343116129222706, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298, 51091258636856298], 45797323817985247, 46035208894715274⟩
  | 6 => ⟨6, 6, 53484488968185510, [517250770710050, 5338411266604450, 10159571762498850, 14980732258393250, 19801892754287650, 24623053250182050, 29444213746076450, 34265374241970850, 39086534737865250, 43907695233759650, 48728855729654050, 53550016225548450, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050, 57451350047884050], 51619182911999722, 51857680292867625⟩
  | 7 => ⟨6, 7, 59741853874895765, [636234766255762, 6011007734371858, 11385780702487954, 16760553670604050, 22135326638720146, 27510099606836242, 32884872574952338, 38259645543068434, 43634418511184530, 49009191479300626, 54383964447416722, 59758737415532818, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994, 63719096444670994], 57399156851865845, 57638266536871624⟩
  | 8 => ⟨6, 8, 65902207552636126, [757039855460098, 6685425295797890, 12613810736135682, 18542196176473474, 24470581616811266, 30398967057149058, 36327352497486850, 42255737937824642, 48184123378162434, 54112508818500226, 60040894258838018, 65969279699175810, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258, 69889034546241258], 63117849266546260, 63357513371059942⟩
  | 9 => ⟨6, 9, 72001137311046093, [879666038323058, 7361663950882546, 13843661863442034, 20325659776001522, 26807657688561010, 33289655601120498, 39771653513679986, 46253651426239474, 52735649338798962, 59217647251358450, 65699645163917938, 72181643076477426, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914, 75998345794727914], 68812231804457055, 69052508213108613⟩
  | 10 => ⟨6, 10, 77977067264202608, [1004113314844642, 8039723699625826, 15075334084407010, 22110944469188194, 29146554853969378, 36182165238750562, 43217775623531746, 50253386008312930, 57288996393094114, 64324606777875298, 71360217162656482, 78395827547437666, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546, 81983063105467546], 74441690629864894, 74682521458024355⟩
  | 11 => ⟨6, 11, 83867405815403795, [1130381685024850, 8719604542027730, 16308827399030610, 23898050256033490, 31487273113036370, 39076495970039250, 46665718827042130, 54254941684045010, 61844164541047890, 69433387398050770, 77022610255053650, 84611833112056530, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850, 87882189014251850], 80025622113807133, 80267007361474497⟩
  | 12 => ⟨6, 12, 89698141540933212, [1258471148863682, 9401306478088258, 17544141807312834, 25686977136537410, 33829812465761986, 41972647794986562, 50115483124211138, 58258318453435714, 66401153782660290, 74543989111884866, 82686824441109442, 90829659770334018, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170, 93722509163611170], 85564026256283772, 85805965923459039⟩
  | 13 => ⟨6, 13, 95419118381882367, [1388381706361138, 10084829507807410, 18781277309253682, 27477725110699954, 36174172912146226, 44870620713592498, 53567068515038770, 62263516316485042, 70959964117931314, 79656411919377586, 88352859720823858, 97049307522270130, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442, 99452273362143442], 91056903057294811, 91299397143977981⟩
  | 14 => ⟨6, 14, 101054503820876194, [1520113357517218, 10770173631185186, 20020233904853154, 29270294178521122, 38520354452189090, 47770414725857058, 57020474999525026, 66270535273192994, 75520595546860962, 84770655820528930, 94020716094196898, 103270776367864866, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386, 105096446158720386], 96473929583851150, 96716920205412250⟩
  | 15 => ⟨6, 15, 106604297857914693, [1653666102331922, 11457338848221586, 21261011594111250, 31064684340000914, 40868357085890578, 50672029831780242, 60475702577669906, 70279375323559570, 80083048069449234, 89886720815338898, 99690393561228562, 109494066307118226, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002, 110655027553342002], 101841786581624641, 102085273738063671⟩
  | 16 => ⟨6, 16, 112001954591161756, [1789039940805250, 12146325158916610, 22503610377027970, 32860895595139330, 43218180813250690, 53575466031362050, 63932751249473410, 74290036467584770, 84647321685696130, 95004606903807490, 105361892121918850, 115719177340030210, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610, 116059877511678610], 107160474050615284, 107404457741932244⟩
  | 17 => ⟨6, 17, 117341829592395673, [1926234872937202, 12837132563270258, 23748030253603314, 34658927943936370, 45569825634269426, 56480723324602482, 67391621014935538, 78302518705268594, 89213416395601650, 100124314085934706, 111035211776267762, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858, 121407742804248858], 112429991990823079, 112674472217017969⟩
  | 18 => ⟨6, 18, 122555555866121712, [2065250898727778, 13529761061282530, 24994271223837282, 36458781386392034, 47923291548946786, 59387801711501538, 70852311874056290, 82316822036611042, 93781332199165794, 105245842361720546, 116710352524275298, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442, 126628662303064442], 117650340402248026, 117895317163320846⟩
  | 19 => ⟨6, 19, 127676406363257927, [2206088018176978, 14224210652953426, 26242333287729874, 38260455922506322, 50278578557282770, 62296701192059218, 74314823826835666, 86332946461612114, 98351069096388562, 110369191731165010, 122387314365941458, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202, 131756706025290202], 122782090883607905, 123027506294928682⟩
  | 20 => ⟨6, 20, 132663823758251768, [2348746231284802, 14920481338282946, 27492216445281090, 40063951552279234, 52635686659277378, 65207421766275522, 77779156873273666, 90350891980271810, 102922627087269954, 115494362194268098, 128066097301266242, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802, 136750519579126802], 127861029648867688, 128106883710436422⟩
  | 21 => ⟨6, 21, 137554723189338537, [2493225538051250, 15618573117271090, 28743920696490930, 41869268275710770, 54994615854930610, 68119963434150450, 81245311013370290, 94370658592590130, 107496006171809970, 120621353751029810, 133746701330249650, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330, 141647815169056330], 132887156698027375, 133133449409844066⟩
  | 22 => ⟨6, 22, 142349104656518234, [2639525938476322, 16318485989917858, 29997446041359394, 43676406092800930, 57355366144242466, 71034326195684002, 84713286247125538, 98392246298567074, 112071206350008610, 125750166401450146, 139429126452891682, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786, 146448592795078786], 137860472031086966, 138107203393151614⟩
  | 23 => ⟨6, 23, 146954926946734015, [2787647432560018, 17020219956223250, 31252792479886482, 45485365003549714, 59717937527212946, 73950510050876178, 88183082574539410, 102415655098202642, 116648227621865874, 130880800145529106, 145113372669192338, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754, 151059217111643754], 142734262872129745, 142981374999812377⟩
  | 24 => ⟨6, 24, 151504788598595274, [2937590020302338, 17723775016187266, 32509960012072194, 47296145007957122, 62082330003842050, 76868514999726978, 91654699995611906, 106440884991496834, 121227069987381762, 136013254983266690, 150799439979151618, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986, 155614677856100986], 147600133679330520, 147847684457261109⟩
  | 25 => ⟨6, 25, 155904827305386543, [3089353701703282, 18429151169809906, 33768948637916530, 49108746106023154, 64448543574129778, 79788341042236402, 95128138510343026, 110467935978449650, 125807733446556274, 141147530914662898, 156487328382769522, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442, 160019518589241442], 152362837807197235, 152610769350745808⟩
  | 26 => ⟨6, 26, 160149579786131950, [3242938476762850, 19136348417091170, 35029758357419490, 50923168297747810, 66816578238076130, 82709988178404450, 98603398118732770, 114496808059061090, 130390217999389410, 146283627939717730, 162177037880046050, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250, 164268276030089250], 157016911974754018, 157265166399290602⟩
  | 27 => ⟨6, 27, 164233582759855623, [3398344345481042, 19845366758031058, 36292389170581074, 52739411583131090, 69186433995681106, 85633456408231122, 102080478820781138, 118527501233331154, 134974523645881170, 151421546058431186, 167868568470981202, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538, 168355486897668538], 161664887202127421, 161913522392281989⟩
  | 28 => ⟨6, 28, 168261625095224774, [3555571307857858, 20556206192629570, 37556841077401282, 54557475962172994, 71558110846944706, 88558745731716418, 105559380616488130, 122560015501259842, 139560650386031554, 156561285270803266, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090, 172387534193140090], 166200590281873644, 166449548353016223⟩
  | 29 => ⟨6, 29, 172068328567774777, [3714619363893298, 21268866720886706, 38823114077880114, 56377361434873522, 73931608791866930, 91485856148860338, 109040103505853746, 126594350862847154, 144148598219840562, 161702845576833970, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922, 176196648493298922], 170676197270885275, 170925478223015865⟩
  | 30 => ⟨6, 30, 175701534877692678, [3875488513587362, 21983348342802466, 40091208172017570, 58199068001232674, 76306927830447778, 94414787659662882, 112522647488877986, 130630507318093090, 148738367147308194, 166846226976523298, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866, 179831468564578866], 175091708169162314, 175341312002280915⟩
  | 31 => ⟨6, 31, 179216370099800019, [4038178756940050, 22699651058376850, 41361123359813650, 60022595661250450, 78684067962687250, 97345540264124050, 116007012565560850, 134668484866997650, 153329957168434450, 171991429469871250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250, 183347917548048250], 179508404501890469, 179758389100627054⟩
  | 32 => ⟨6, 32, 182550423784640762, [4202690093951362, 23417774867609858, 42632859641268354, 61847944414926850, 81063029188585346, 100278113962243842, 119493198735902338, 138708283509560834, 157923368283219330, 177138453056877826, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250, 186682787928004250], 183931749550045612, 184182172799030154⟩
  | 33 => ⟨6, 33, 185634001108124373, [4369022524621298, 24137719770501490, 43906417016381682, 63675114262261874, 83443811508142066, 103212508754022258, 122981205999902450, 142749903245782642, 162518600491662834, 182287297737543026, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546, 189765587814109546], 188302282882100659, 188553144781333158⟩
  | 34 => ⟨6, 34, 188588280781845680, [4537176048949858, 24859485767051746, 45181795485153634, 65504105203255522, 85826414921357410, 106148724639459298, 126471034357561186, 146793344075663074, 167115653793764962, 187437963511866850, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538, 192719090050452538], 192553259691894030, 192804502356744513⟩
  | 35 => ⟨6, 35, 191277515344940863, [4707150666937042, 25583072857260626, 46458995047584210, 67334917237907794, 88210839428231378, 109086761618554962, 129962683808878546, 150838605999202130, 171714528189525714, 192590450379849298, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834, 195405953043675834], 195787860000787201, 196038673046436046⟩
  | 36 => ⟨6, 36, 193760473059548712, [4878946378582850, 26308481041128130, 47738015703673410, 69167550366218690, 90597085028763970, 112026619691309250, 133456154353854530, 154885689016399810, 176315223678945090, 197744758341490370, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010, 197885742122165010], 198281532842512104, 198531395307289554⟩
  | 37 => ⟨6, 37, 196031690644693355, [5052563183887282, 27035710318654258, 49018857453421234, 71002004588188210, 92985151722955186, 114968298857722162, 136951445992489138, 158934593127256114, 180917740262023090, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194, 200152994004944194], 200562773385385507, 200811627384661589⟩
  | 38 => ⟨6, 38, 198012367807991138, [5228001082850338, 27764760689839010, 50301520296827682, 72838279903816354, 95375039510805026, 117911799117793698, 140448558724782370, 162985318331771042, 185522077938759714, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946, 202128111333382946], 202552089167635462, 202799818932150230⟩
  | 39 => ⟨6, 39, 199691577987490317, [5405260075472018, 28495632154682386, 51586004233892754, 74676376313103122, 97766748392313490, 120857120471523858, 143947492550734226, 167037864629944594, 190128236709154962, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522, 203800167545529522], 204238553627310225, 204485043387803733⟩
  | 40 => ⟨6, 40, 201135373819964178, [5584340161752322, 29228324713184386, 52872309264616450, 76516293816048514, 100160278367480578, 123804262918912642, 147448247470344706, 171092232021776770, 194736216573208834, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994, 205236012344403994], 205688911570571376, 205934103442413651⟩
  | 41 => ⟨6, 41, 202101891147285887, [5765241341691250, 29962838365345010, 54160435388998770, 78358032412652530, 102555629436306290, 126753226459960050, 150950823483613810, 175148420507267570, 199346017530921330, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170, 206191390373139170], 206659222331127199, 206902884775798349⟩
  | 42 => ⟨6, 42, 202730519617636512, [5947963615288802, 30699173111164258, 55450382607039714, 80201592102915170, 104952801598790626, 129704011094666082, 154455220590541538, 179206430086416994, 203957639582292450, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690, 206807285412409690], 207290259895935350, 207532277144175429⟩
  | 43 => ⟨6, 43, 202845447709662505, [6132506982544978, 31437328950642130, 56742150918739282, 82046972886836434, 107351794854933586, 132656616823030738, 157961438791127890, 183266260759225042, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 44 => ⟨6, 44, 202845447709662505, [6318871443459778, 32177305883778626, 58035740324097474, 83894174764416322, 109752609204735170, 135611043645054018, 161469478085372866, 187327912525691714, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 45 => ⟨6, 45, 202845447709662505, [6507056998033202, 32919103910573746, 59331150823114290, 85743197735654834, 112155244648195378, 138567291560735922, 164979338473276466, 191391385385817010, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 46 => ⟨6, 46, 202845447709662505, [6697063646265250, 33662723031027490, 60628382415789730, 87594041800551970, 114559701185314210, 141525360570076450, 168491019954838690, 195456679339600930, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 47 => ⟨6, 47, 202845447709662505, [6888891388155922, 34408163245139858, 61927435102123794, 89446706959107730, 116965978816091666, 144485250673075602, 172004522530059538, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 48 => ⟨6, 48, 202845447709662505, [7082540223705218, 35155424552910850, 63228308882116482, 91301193211322114, 119374077540527746, 147446961869733378, 175519846198939010, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 49 => ⟨6, 49, 202845447709662505, [7278010152913138, 35904506954340466, 64531003755767794, 93157500557195122, 121783997358622450, 150410494160049778, 179036990961477106, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 50 => ⟨6, 50, 202845447709662505, [7475301175779682, 36655410449428706, 65835519723077730, 95015628996726754, 124195738270375778, 153375847544024802, 182555956817673826, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 51 => ⟨6, 51, 202845447709662505, [7674413292304850, 37408135038175570, 67141856784046290, 96875578529917010, 126609300275787730, 156343022021658450, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 52 => ⟨6, 52, 202845447709662505, [7875346502488642, 38162680720581058, 68450014938673474, 98737349156765890, 129024683374858306, 159312017592950722, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 53 => ⟨6, 53, 202845447709662505, [8078100806331058, 38919047496645170, 69759994186959282, 100600940877273394, 131441887567587506, 162282834257901618, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 54 => ⟨6, 54, 202845447709662505, [8282676203832098, 39677235366367906, 71071794528903714, 102466353691439522, 133860912853975330, 165255472016511138, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 55 => ⟨6, 55, 202845447709662505, [8489072694991762, 40437244329749266, 72385415964506770, 104333587599264274, 136281759234021778, 168229930868779282, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 56 => ⟨6, 56, 202845447709662505, [8697290279810050, 41199074386789250, 73700858493768450, 106202642600747650, 138704426707726850, 171206210814706050, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 57 => ⟨6, 57, 202845447709662505, [8907328958286962, 41962725537487858, 75018122116688754, 108073518695889650, 141128915275090546, 174184311854291442, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 58 => ⟨6, 58, 202845447709662505, [9119188730422498, 42728197781845090, 76337206833267682, 109946215884690274, 143555224936112866, 177164233987535458, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 59 => ⟨6, 59, 202845447709662505, [9332869596216658, 43495491119860946, 77658112643505234, 111820734167149522, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 60 => ⟨6, 60, 202845447709662505, [9548371555669442, 44264605551535426, 78980839547401410, 113697073543267394, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 61 => ⟨6, 61, 202845447709662505, [9548371555669442, 44264605551535426, 78980839547401410, 113697073543267394, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 62 => ⟨6, 62, 202845447709662505, [9548371555669442, 44264605551535426, 78980839547401410, 113697073543267394, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 63 => ⟨6, 63, 202845447709662505, [9548371555669442, 44264605551535426, 78980839547401410, 113697073543267394, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 64 => ⟨6, 64, 202845447709662505, [9548371555669442, 44264605551535426, 78980839547401410, 113697073543267394, 145983355690793810, 180145977214438098, 186076743767529170, 199523794387043474, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434, 206906291808368434], 207404828404865693, 207644968918154809⟩
  | 65 => ⟨6, 65, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 66 => ⟨6, 66, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 67 => ⟨6, 67, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 68 => ⟨6, 68, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 69 => ⟨6, 69, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 70 => ⟨6, 70, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 71 => ⟨6, 71, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 72 => ⟨6, 72, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 73 => ⟨6, 73, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 74 => ⟨6, 74, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 75 => ⟨6, 75, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 76 => ⟨6, 76, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 77 => ⟨6, 77, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 78 => ⟨6, 78, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 79 => ⟨6, 79, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 80 => ⟨6, 80, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 81 => ⟨6, 81, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 82 => ⟨6, 82, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 83 => ⟨6, 83, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 84 => ⟨6, 84, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 85 => ⟨6, 85, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 86 => ⟨6, 86, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 87 => ⟨6, 87, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 88 => ⟨6, 88, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 89 => ⟨6, 89, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 90 => ⟨6, 90, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 91 => ⟨6, 91, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 92 => ⟨6, 92, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 93 => ⟨6, 93, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 94 => ⟨6, 94, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 95 => ⟨6, 95, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 96 => ⟨6, 96, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 97 => ⟨6, 97, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 98 => ⟨6, 98, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 99 => ⟨6, 99, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 100 => ⟨6, 100, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 101 => ⟨6, 101, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 102 => ⟨6, 102, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 103 => ⟨6, 103, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 104 => ⟨6, 104, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 105 => ⟨6, 105, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 106 => ⟨6, 106, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 107 => ⟨6, 107, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 108 => ⟨6, 108, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 109 => ⟨6, 109, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 110 => ⟨6, 110, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 111 => ⟨6, 111, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 112 => ⟨6, 112, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 113 => ⟨6, 113, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 114 => ⟨6, 114, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 115 => ⟨6, 115, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 116 => ⟨6, 116, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 117 => ⟨6, 117, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 118 => ⟨6, 118, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 119 => ⟨6, 119, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | 120 => ⟨6, 120, 202845447709662505, [206906291808368434], 207404828404865693, 207644968918154809⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData06
end PackedLocator_LocatorPhase6800ReceiptRowData06

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData07. -/
section PackedLocator_LocatorPhase6800ReceiptRowData07

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData07

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def threshold : ℕ → ThresholdReceipt
  | 0 => ⟨7, 0, 3674, 5958, 3299, 3666⟩
  | 1 => ⟨7, 1, 3653, 5957, 3287, 3652⟩
  | 2 => ⟨7, 2, 3632, 5956, 3276, 3638⟩
  | 3 => ⟨7, 3, 3610, 5955, 3263, 3624⟩
  | 4 => ⟨7, 4, 3588, 5954, 3251, 3610⟩
  | 5 => ⟨7, 5, 3565, 5953, 3239, 3595⟩
  | 6 => ⟨7, 6, 3542, 5952, 3226, 3580⟩
  | 7 => ⟨7, 7, 3519, 5951, 3213, 3565⟩
  | 8 => ⟨7, 8, 3496, 5950, 3200, 3550⟩
  | 9 => ⟨7, 9, 3473, 5949, 3187, 3534⟩
  | 10 => ⟨7, 10, 3450, 5948, 3174, 3518⟩
  | 11 => ⟨7, 11, 3425, 5947, 3160, 3502⟩
  | 12 => ⟨7, 12, 3401, 5946, 3146, 3486⟩
  | 13 => ⟨7, 13, 3376, 5945, 3132, 3469⟩
  | 14 => ⟨7, 14, 3351, 5944, 3118, 3452⟩
  | 15 => ⟨7, 15, 3326, 5943, 3104, 3435⟩
  | 16 => ⟨7, 16, 3300, 5942, 3089, 3417⟩
  | 17 => ⟨7, 17, 3273, 5941, 3074, 3400⟩
  | 18 => ⟨7, 18, 3246, 5940, 3059, 3382⟩
  | 19 => ⟨7, 19, 3219, 5939, 3044, 3363⟩
  | 20 => ⟨7, 20, 3192, 5938, 3028, 3345⟩
  | 21 => ⟨7, 21, 3164, 5937, 3013, 3326⟩
  | 22 => ⟨7, 22, 3135, 5936, 2997, 3306⟩
  | 23 => ⟨7, 23, 3105, 5935, 2980, 3286⟩
  | 24 => ⟨7, 24, 3076, 5934, 2964, 3266⟩
  | 25 => ⟨7, 25, 3045, 5933, 2947, 3246⟩
  | 26 => ⟨7, 26, 3014, 5932, 2931, 3225⟩
  | 27 => ⟨7, 27, 2982, 5931, 2916, 3204⟩
  | 28 => ⟨7, 28, 2949, 5930, 2901, 3184⟩
  | 29 => ⟨7, 29, 2916, 5929, 2887, 3165⟩
  | 30 => ⟨7, 30, 2881, 5928, 2871, 3147⟩
  | 31 => ⟨7, 31, 2846, 5927, 2856, 3129⟩
  | 32 => ⟨7, 32, 2809, 5926, 2840, 3110⟩
  | 33 => ⟨7, 33, 2772, 5925, 2824, 3091⟩
  | 34 => ⟨7, 34, 2733, 5924, 2808, 3071⟩
  | 35 => ⟨7, 35, 2692, 5923, 2791, 3050⟩
  | 36 => ⟨7, 36, 2650, 5922, 2774, 3030⟩
  | 37 => ⟨7, 37, 2606, 5921, 2756, 3008⟩
  | 38 => ⟨7, 38, 2561, 5920, 2738, 2986⟩
  | 39 => ⟨7, 39, 2512, 5919, 2720, 2964⟩
  | 40 => ⟨7, 40, 2461, 5918, 2701, 2940⟩
  | 41 => ⟨7, 41, 2407, 5917, 2682, 2917⟩
  | 42 => ⟨7, 42, 2349, 5916, 2662, 2892⟩
  | 43 => ⟨7, 43, 2287, 5915, 2642, 2867⟩
  | 44 => ⟨7, 44, 2222, 5914, 2622, 2841⟩
  | 45 => ⟨7, 45, 2152, 5913, 2601, 2814⟩
  | 46 => ⟨7, 46, 2079, 5912, 2579, 2787⟩
  | 47 => ⟨7, 47, 2002, 5911, 2557, 2759⟩
  | 48 => ⟨7, 48, 1920, 5910, 2536, 2729⟩
  | 49 => ⟨7, 49, 1835, 5909, 2515, 2701⟩
  | 50 => ⟨7, 50, 1746, 5908, 2494, 2673⟩
  | 51 => ⟨7, 51, 1653, 5907, 2471, 2644⟩
  | 52 => ⟨7, 52, 1556, 5906, 2448, 2613⟩
  | 53 => ⟨7, 53, 1454, 5380, 2425, 2581⟩
  | 54 => ⟨7, 54, 1349, 4492, 2400, 2548⟩
  | 55 => ⟨7, 55, 1240, 3585, 2374, 2513⟩
  | 56 => ⟨7, 56, 1127, 2657, 2348, 2476⟩
  | 57 => ⟨7, 57, 1010, 1680, 2320, 2438⟩
  | 58 => ⟨7, 58, 888, 646, 2292, 2398⟩
  | 59 => ⟨7, 59, 763, 0, 2262, 2355⟩
  | 60 => ⟨7, 60, 634, 0, 2232, 2311⟩
  | 61 => ⟨7, 61, 500, 0, 2201, 2264⟩
  | 62 => ⟨7, 62, 362, 0, 2168, 2215⟩
  | 63 => ⟨7, 63, 221, 0, 2134, 2164⟩
  | 64 => ⟨7, 64, 75, 0, 2097, 2110⟩
  | 65 => ⟨7, 65, 0, 0, 2059, 2054⟩
  | 66 => ⟨7, 66, 0, 0, 2019, 1996⟩
  | 67 => ⟨7, 67, 0, 0, 1977, 1936⟩
  | 68 => ⟨7, 68, 0, 0, 1934, 1873⟩
  | 69 => ⟨7, 69, 0, 0, 1888, 1808⟩
  | 70 => ⟨7, 70, 0, 0, 1842, 1741⟩
  | 71 => ⟨7, 71, 0, 0, 1793, 1671⟩
  | 72 => ⟨7, 72, 0, 0, 1743, 1600⟩
  | 73 => ⟨7, 73, 0, 0, 1690, 1526⟩
  | 74 => ⟨7, 74, 0, 0, 1636, 1449⟩
  | 75 => ⟨7, 75, 0, 0, 1580, 1370⟩
  | 76 => ⟨7, 76, 0, 0, 1521, 1289⟩
  | 77 => ⟨7, 77, 0, 0, 1461, 1206⟩
  | 78 => ⟨7, 78, 0, 0, 1399, 1120⟩
  | 79 => ⟨7, 79, 0, 0, 1336, 1032⟩
  | 80 => ⟨7, 80, 0, 0, 1272, 941⟩
  | 81 => ⟨7, 81, 0, 0, 1206, 849⟩
  | 82 => ⟨7, 82, 0, 0, 1137, 754⟩
  | 83 => ⟨7, 83, 0, 0, 1067, 658⟩
  | 84 => ⟨7, 84, 0, 0, 995, 558⟩
  | 85 => ⟨7, 85, 0, 0, 921, 456⟩
  | 86 => ⟨7, 86, 0, 0, 844, 351⟩
  | 87 => ⟨7, 87, 0, 0, 766, 243⟩
  | 88 => ⟨7, 88, 0, 0, 685, 133⟩
  | 89 => ⟨7, 89, 0, 0, 603, 20⟩
  | 90 => ⟨7, 90, 0, 0, 518, 0⟩
  | 91 => ⟨7, 91, 0, 0, 433, 0⟩
  | 92 => ⟨7, 92, 0, 0, 346, 0⟩
  | 93 => ⟨7, 93, 0, 0, 259, 0⟩
  | 94 => ⟨7, 94, 0, 0, 169, 0⟩
  | 95 => ⟨7, 95, 0, 0, 77, 0⟩
  | 96 => ⟨7, 96, 0, 0, 0, 0⟩
  | 97 => ⟨7, 97, 0, 0, 0, 0⟩
  | 98 => ⟨7, 98, 0, 0, 0, 0⟩
  | 99 => ⟨7, 99, 0, 0, 0, 0⟩
  | 100 => ⟨7, 100, 0, 0, 0, 0⟩
  | 101 => ⟨7, 101, 0, 0, 0, 0⟩
  | 102 => ⟨7, 102, 0, 0, 0, 0⟩
  | 103 => ⟨7, 103, 0, 0, 0, 0⟩
  | 104 => ⟨7, 104, 0, 0, 0, 0⟩
  | 105 => ⟨7, 105, 0, 0, 0, 0⟩
  | 106 => ⟨7, 106, 0, 0, 0, 0⟩
  | 107 => ⟨7, 107, 0, 0, 0, 0⟩
  | 108 => ⟨7, 108, 0, 0, 0, 0⟩
  | 109 => ⟨7, 109, 0, 0, 0, 0⟩
  | 110 => ⟨7, 110, 0, 0, 0, 0⟩
  | 111 => ⟨7, 111, 0, 0, 0, 0⟩
  | 112 => ⟨7, 112, 0, 0, 0, 0⟩
  | 113 => ⟨7, 113, 0, 0, 0, 0⟩
  | 114 => ⟨7, 114, 0, 0, 0, 0⟩
  | 115 => ⟨7, 115, 0, 0, 0, 0⟩
  | 116 => ⟨7, 116, 0, 0, 0, 0⟩
  | 117 => ⟨7, 117, 0, 0, 0, 0⟩
  | 118 => ⟨7, 118, 0, 0, 0, 0⟩
  | 119 => ⟨7, 119, 0, 0, 0, 0⟩
  | 120 => ⟨7, 120, 0, 0, 0, 0⟩
  | _ => defaultThreshold

def prefixData : ℕ → PrefixReceipt
  | 0 => ⟨7, 0, 32190945603349303, [92153408823099, 3129719814222411, 6167286219621723, 9204852625021035, 12242419030420347, 15279985435819659, 18317551841218971, 21355118246618283, 24392684652017595, 27430251057416907, 30467817462816219, 33505383868215531, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326, 36153262478185326], 32453681275027238, 32691975510906296⟩
  | 1 => ⟨7, 1, 34977176850795408, [140586738349998, 3428843707484862, 6717100676619726, 10005357645754590, 13293614614889454, 16581871584024318, 19870128553159182, 23158385522294046, 26446642491428910, 29734899460563774, 33023156429698638, 36311413398833502, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906, 38950672281954906], 35050252335147280, 35289158875164214⟩
  | 2 => ⟨7, 2, 35760591733078554, [150903066087523, 3525359541265571, 6899816016443619, 10274272491621667, 13648728966799715, 17023185441977763, 20397641917155811, 23772098392333859, 27146554867511907, 30521011342689955, 33895467817868003, 37269924293046051, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527, 39745265720561527], 35863014614228086, 36102591343012869⟩
  | 3 => ⟨7, 3, 43192218589056693, [285074299300055, 4307152925326615, 8329231551353175, 12351310177379735, 16373388803406295, 20395467429432855, 24417546055459415, 28439624681485975, 32461703307512535, 36483781933539095, 40505860559565655, 44527939185592215, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355, 47187274066616355], 42676854477343141, 42916985625635827⟩
  | 4 => ⟨7, 4, 50532240996066128, [421375868535115, 5091076645410187, 9760777422285259, 14430478199160331, 19100178976035403, 23769879752910475, 28439580529785547, 33109281306660619, 37778982083535691, 42448682860410763, 47118383637285835, 51788084414160907, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479, 54537677963702479], 49452691900855172, 49693435353285734⟩
  | 5 => ⟨7, 5, 57763964826512449, [559807773792703, 5877130701516287, 11194453629239871, 16511776556963455, 21829099484687039, 27146422412410623, 32463745340134207, 37781068267857791, 43098391195581375, 48415714123304959, 53733037051028543, 59050359978752127, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703, 61778986217978703], 56179531595849059, 56420887352417497⟩
  | 6 => ⟨7, 6, 64899823535945010, [700370015072819, 6665315093644915, 12630260172217011, 18595205250789107, 24560150329361203, 30525095407933299, 36490040486505395, 42454985565077491, 48419930643649587, 54384875722221683, 60349820800793779, 66314765879365875, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167, 68924429351241167], 62837856929319570, 63079767105395911⟩
  | 7 => ⟨7, 7, 71939817124363811, [843062592375463, 7455629821796071, 14068197051216679, 20680764280637287, 27293331510057895, 33905898739478503, 40518465968899111, 47131033198319719, 53743600427740327, 60356167657160935, 66968734886581543, 73581302116002151, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871, 75974007363489871], 69442923862226881, 69685388457811125⟩
  | 8 => ⟨7, 8, 78883945591768852, [987885505700635, 8248074885969755, 15508264266238875, 22768453646507995, 30028643026777115, 37288832407046235, 44549021787315355, 51809211167584475, 59069400547853595, 66329589928122715, 73589779308391835, 80849968688660955, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815, 82927720254724815], 75994732394570992, 76237751409663139⟩
  | 9 => ⟨7, 9, 85732208938160133, [1134838755048335, 9042650286165967, 16950461817283599, 24858273348401231, 32766084879518863, 40673896410636495, 48581707941754127, 56489519472871759, 64397331003989391, 72305142535107023, 80212954066224655, 88120765597342287, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999, 89785568024945999], 82493282526351903, 82736855960951953⟩
  | 10 => ⟨7, 10, 92484607163537654, [1283922340418563, 9839356022384707, 18394789704350851, 26950223386316995, 35505657068283139, 44061090750249283, 52616524432215427, 61171958114181571, 69727391796147715, 78282825478113859, 86838259160080003, 95393692842046147, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423, 96547550674153423], 88938574257569614, 89182702111677567⟩
  | 11 => ⟨7, 11, 99082187980442259, [1435136261811319, 10638192094625975, 19841247927440631, 29044303760255287, 38247359593069943, 47450415425884599, 56653471258699255, 65856527091513911, 75059582924328567, 84262638757143223, 93465694589957879, 102668750422772535, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359, 103153121782394359], 95300439275106253, 95545063664092136⟩
  | 12 => ⟨7, 12, 105606988811995098, [1588480519226603, 11439158502889771, 21289836486552939, 31140514470216107, 40991192453879275, 50841870437542443, 60692548421205611, 70543226404868779, 80393904388531947, 90244582372195115, 100095260355858283, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315, 109686709971530315], 101604785220034636, 101849906143898449⟩
  | 13 => ⟨7, 13, 111997927034714487, [1743955112664415, 12242255247176095, 22740555381687775, 33238855516199455, 43737155650711135, 54235455785222815, 64733755919734495, 75232056054246175, 85730356188757855, 96228656323269535, 106726956457781215, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035, 116085638485586035], 107851612092354763, 108097229551096506⟩
  | 14 => ⟨7, 14, 118284478792330004, [1901560042124755, 13047482327484947, 24193404612845139, 35339326898205331, 46485249183565523, 57631171468925715, 68777093754285907, 79923016039646099, 91068938325006291, 102214860610366483, 113360782895726675, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883, 122380180534537883], 114040919892066634, 114287033885686307⟩
  | 15 => ⟨7, 15, 124466644084841649, [2061295307607623, 13854839743816327, 25648384180025031, 37441928616233735, 49235473052442439, 61029017488651143, 72822561924859847, 84616106361068551, 96409650797277255, 108203195233485959, 119996739669694663, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859, 128570336118385859], 120172708619170249, 120419319147667852⟩
  | 16 => ⟨7, 16, 130504295088407204, [2223160909113019, 14664327496170235, 27105494083227451, 39546660670284667, 51987827257341883, 64428993844399099, 76870160431456315, 89311327018513531, 101752493605570747, 114193660192627963, 126634826779685179, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959, 134615180347040959], 126206158280435096, 126453207459180656⟩
  | 17 => ⟨7, 17, 136391040794959085, [2387156846640943, 15475945584546671, 28564734322452399, 41653523060358127, 54742311798263855, 67831100536169583, 80919889274075311, 94008678011981039, 107097466749886767, 120186255487792495, 133275044225698223, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599, 140508322212435599], 132177828197046631, 132425316026040148⟩
  | 18 => ⟨7, 18, 142164878692316982, [2553283120191395, 16289694008945635, 30026104897699875, 43762515786454115, 57498926675208355, 71235337563962595, 84971748452716835, 98708159341471075, 112444570230225315, 126180981118979555, 139917392007733795, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255, 146288556268636255], 138087718369004854, 138335644848246328⟩
  | 19 => ⟨7, 19, 147825808780480895, [2721539729764375, 17105572769367127, 31489605808969879, 45873638848572631, 60257671888175383, 74641704927778135, 89025737967380887, 103409771006983639, 117793804046586391, 132177837086189143, 146561870125791895, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927, 151955882515642927], 143935828796309765, 144184193925799196⟩
  | 20 => ⟨7, 20, 153373831059450824, [2891926675359883, 17923581865811147, 32955237056262411, 47986892246713675, 63018547437164939, 78050202627616203, 93081857818067467, 108113513008518731, 123145168198969995, 138176823389421259, 153208478579872523, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615, 157510300953455615], 149672818141640740, 149921564036748155⟩
  | 21 => ⟨7, 21, 158758166025271911, [3064443956977919, 18743721298277695, 34422998639577471, 50102275980877247, 65781553322177023, 81460830663476799, 97140108004776575, 112819385346076351, 128498662687376127, 144177940028675903, 159857217369975679, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675, 162900235011872675], 155395238743616499, 155644423288971871⟩
  | 22 => ⟨7, 22, 163972422669876572, [3239091574618483, 19565991066766771, 35892890558915059, 52219790051063347, 68546689543211635, 84873589035359923, 101200488527508211, 117527388019656499, 133854287511804787, 150181187003953075, 166508086496101363, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523, 168119293682826523], 161002277591573266, 161251842902546622⟩
  | 23 => ⟨7, 23, 169010209985197223, [3415869528281575, 20390391171278375, 37364912814275175, 54339434457271975, 71313956100268775, 88288477743265575, 105262999386262375, 122237521029259175, 139212042672255975, 156186564315252775, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575, 173161085958249575], 166487543677443457, 166737431869404824⟩
  | 24 => ⟨7, 24, 173979477987211164, [3594777817967195, 21216921611812507, 38839065405657819, 56461209199503131, 74083352993348443, 91705496787193755, 109327640581039067, 126949784374884379, 144571928168729691, 162194071962575003, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703, 178135155986612703], 171960371355980960, 172210640313560311⟩
  | 25 => ⟨7, 25, 178708715139851069, [3775816443675343, 22045582388369167, 40315348333062991, 58585114277756815, 76854880222450639, 95124646167144463, 113394412111838287, 131664178056532111, 149933944001225935, 168203709945919759, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223, 182867601033108223], 177307165600386831, 177557757438954193⟩
  | 26 => ⟨7, 26, 183308001795116766, [3958985405406019, 22876373500948355, 41793761596490691, 60711149692033027, 79628537787575363, 98545925883117699, 117463313978660035, 136380702074202371, 155298090169744707, 174215478265287043, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535, 187470095582229535], 182645782109505070, 182896754713690416⟩
  | 27 => ⟨7, 27, 187713776432918229, [4144284703159223, 23709294949550071, 43274305195940919, 62839315442331767, 82404325688722615, 101969335935113463, 121534346181504311, 141099356427895159, 160664366674286007, 180229376920676855, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827, 191878281047639827], 187982611891403261, 188234023145836564⟩
  | 28 => ⟨7, 28, 191919648045187874, [4331714336934955, 24544346734174315, 44756979131413675, 64969611528653035, 85182243925892395, 105394876323131755, 125607508720371115, 145820141117610475, 166032773514849835, 186245405912089195, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515, 196085766421271515], 193257661928648140, 193509511833329400⟩
  | 29 => ⟨7, 29, 195987047815993199, [4521274306733215, 25381528854821087, 46241783402908959, 67102037950996831, 87962292499084703, 108822547047172575, 129682801595260447, 150543056143348319, 171403310691436191, 192263565239524063, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883, 200154779953438883], 198539446582763083, 198791793022322273⟩
  | 30 => ⟨7, 30, 199776070689018984, [4712964612554003, 26220841311490387, 47728718010426771, 69236594709363155, 90744471408299539, 112252348107235923, 133760224806172307, 155268101505108691, 176775978204045075, 198283854902981459, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139, 203943822455333139], 203622422769177962, 203875149974355136⟩
  | 31 => ⟨7, 31, 203418100376490337, [4906785254397319, 27062284104182215, 49217782953967111, 71373281803752007, 93528780653536903, 115684279503321799, 137839778353106695, 159995277202891591, 182150776052676487, 204306274902461383, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963, 207585871771672963], 207984383236778585, 208236970245903986⟩
  | 32 => ⟨7, 32, 206764710478001926, [5102736232263163, 27905857232896571, 50708978233529979, 73512099234163387, 96315220234796795, 119118341235430203, 141921462236063611, 164724583236697019, 187527704237330427, 210330825237963835, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451, 210930907369559451], 211343092804183816, 211594845001697768⟩
  | 33 => ⟨7, 33, 209955806049868971, [5300817546151535, 28751560697633455, 52202303849115375, 75653047000597295, 99103790152079215, 122554533303561135, 146005276455043055, 169456019606524975, 192906762758006895, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395, 214120428437801395], 214546287841944503, 214797205227847006⟩
  | 34 => ⟨7, 34, 212834439347596028, [5501029196062435, 29599394498392867, 53697759800723299, 77796125103053731, 101894490405384163, 125992855707714595, 150091221010045027, 174189586312375459, 198287951614705891, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779, 216995893099409779], 217435636266788614, 217685603071819722⟩
  | 35 => ⟨7, 35, 215387828355047929, [5703371181995863, 30449358635174807, 55195346088353751, 79941333541532695, 104687320994711639, 129433308447890583, 154179295901069527, 178925283354248471, 203671270807427415, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435, 219544519338249435], 219998356062580981, 220247256517480748⟩
  | 36 => ⟨7, 36, 217685925600382284, [5907843503951819, 31301453107979275, 56695062712006731, 82088672316034187, 107482281920061643, 132875891524089099, 158269501128116555, 183663110732144011, 209056720336171467, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759, 221837056748724759], 222305091926867508, 222552868147005961⟩
  | 37 => ⟨7, 37, 219637475195216203, [6114446161930303, 32155677916806271, 58196909671682239, 84238141426558207, 110279373181434175, 136320604936310143, 162361836691186111, 188403068446062079, 214444300200938047, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075, 223781452376206075], 224263895801877011, 224510432017994204⟩
  | 38 => ⟨7, 38, 221316690339752352, [6323179155931315, 33012033061655795, 59700886967380275, 86389740873104755, 113078594778829235, 139767448684553715, 166456302590278195, 193145156496002675, 219834010401727155, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835, 225452716487142835], 225949673057200450, 226194911384666410⟩
  | 39 => ⟨7, 39, 222449803368842061, [6534042485954855, 33870518542527847, 61206994599100839, 88543470655673831, 115879946712246823, 143216422768819815, 170552898825392807, 197889374881965799, 225225850938538791, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011, 226574690217646011], 227086579519524273, 227330288419819108⟩
  | 40 => ⟨7, 40, 223193762026980774, [6747036152000923, 34731134359422427, 62715232566843931, 90699330774265435, 118683428981686939, 146667527189108443, 174651625396529947, 202635723603951451, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619, 227305915444704619], 227832947272120512, 228075010975984276⟩
  | 41 => ⟨7, 41, 223442398073627905, [6962160154069519, 35593880512339535, 64225600870609551, 92857321228879567, 121489041587149583, 150120761945419599, 178752482303689615, 207384202661959631, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 42 => ⟨7, 42, 223442398073627905, [7179414492160643, 36458757001279171, 65738099510397699, 95017442019516227, 124296784528634755, 153576127037753283, 182855469546871811, 212134812055990339, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 43 => ⟨7, 43, 223442398073627905, [7398799166274295, 37325763826241335, 67252728486208375, 97179693146175415, 127106657806142455, 157033622466109495, 186960587126076535, 216887551786043575, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 44 => ⟨7, 44, 223442398073627905, [7620314176410475, 38194900987226027, 68769487798041579, 99344074608857131, 129918661419672683, 160493248230488235, 191067835041303787, 221642421852119339, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 45 => ⟨7, 45, 223442398073627905, [7843959522569183, 39066168484233247, 70288377445897311, 101510586407561375, 132732795369225439, 163955004330889503, 195177213292553567, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 46 => ⟨7, 46, 223442398073627905, [8069735204750419, 39939566317262995, 71809397429775571, 103679228542288147, 135549059654800723, 167418890767313299, 199288721879825875, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 47 => ⟨7, 47, 223442398073627905, [8297641222954183, 40815094486315271, 73332547749676359, 105850001013037447, 138367454276398535, 170884907539759623, 203402360803120711, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 48 => ⟨7, 48, 223442398073627905, [8527677577180475, 41692752991390075, 74857828405599675, 108022903819809275, 141187979234018875, 174353054648228475, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 49 => ⟨7, 49, 223442398073627905, [8759844267429295, 42572541832487407, 76385239397545519, 110197936962603631, 144010634527661743, 177823332092719855, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 50 => ⟨7, 50, 223442398073627905, [8994141293700643, 43454461009607267, 77914780725513891, 112375100441420515, 146835420157327139, 181295739873233763, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 51 => ⟨7, 51, 223442398073627905, [9230568655994519, 44338510522749655, 79446452389504791, 114554394256259927, 149662336123015063, 184770277989770199, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 52 => ⟨7, 52, 223442398073627905, [9469126354310923, 45224690371914571, 80980254389518219, 116735818407121867, 152491382424725515, 188246946442329163, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 53 => ⟨7, 53, 223442398073627905, [9709814388649855, 46113000557102015, 82516186725554175, 118919372894006335, 155322559062458495, 191725745230910655, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 54 => ⟨7, 54, 223442398073627905, [9952632759011315, 47003441078311987, 84054249397612659, 121105057716913331, 158155866036214003, 195206674355514675, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 55 => ⟨7, 55, 223442398073627905, [10197581465395303, 47896011935544487, 85594442405693671, 123292872875842855, 160991303345992039, 198689733816141223, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 56 => ⟨7, 56, 223442398073627905, [10444660507801819, 48790713128799515, 87136765749797211, 125482818370794907, 163828870991792603, 202174923612790299, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 57 => ⟨7, 57, 223442398073627905, [10693869886230863, 49687544658077071, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 58 => ⟨7, 58, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 59 => ⟨7, 59, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 60 => ⟨7, 60, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 61 => ⟨7, 61, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 62 => ⟨7, 62, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 63 => ⟨7, 63, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 64 => ⟨7, 64, 223442398073627905, [10945209600682435, 50586506523377155, 88681219429923279, 127674894201769487, 166668568973615695, 205662243745461903, 207518130062438075, 222188532229782675, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287, 227539426861531287], 228081915905060287, 228322160758603061⟩
  | 65 => ⟨7, 65, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 66 => ⟨7, 66, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 67 => ⟨7, 67, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 68 => ⟨7, 68, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 69 => ⟨7, 69, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 70 => ⟨7, 70, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 71 => ⟨7, 71, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 72 => ⟨7, 72, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 73 => ⟨7, 73, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 74 => ⟨7, 74, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 75 => ⟨7, 75, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 76 => ⟨7, 76, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 77 => ⟨7, 77, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 78 => ⟨7, 78, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 79 => ⟨7, 79, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 80 => ⟨7, 80, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 81 => ⟨7, 81, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 82 => ⟨7, 82, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 83 => ⟨7, 83, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 84 => ⟨7, 84, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 85 => ⟨7, 85, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 86 => ⟨7, 86, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 87 => ⟨7, 87, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 88 => ⟨7, 88, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 89 => ⟨7, 89, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 90 => ⟨7, 90, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 91 => ⟨7, 91, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 92 => ⟨7, 92, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 93 => ⟨7, 93, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 94 => ⟨7, 94, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 95 => ⟨7, 95, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 96 => ⟨7, 96, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 97 => ⟨7, 97, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 98 => ⟨7, 98, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 99 => ⟨7, 99, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 100 => ⟨7, 100, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 101 => ⟨7, 101, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 102 => ⟨7, 102, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 103 => ⟨7, 103, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 104 => ⟨7, 104, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 105 => ⟨7, 105, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 106 => ⟨7, 106, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 107 => ⟨7, 107, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 108 => ⟨7, 108, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 109 => ⟨7, 109, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 110 => ⟨7, 110, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 111 => ⟨7, 111, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 112 => ⟨7, 112, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 113 => ⟨7, 113, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 114 => ⟨7, 114, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 115 => ⟨7, 115, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 116 => ⟨7, 116, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 117 => ⟨7, 117, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 118 => ⟨7, 118, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | 119 => ⟨7, 119, 223442398073627905, [227539426861531287], 228081915905060287, 228322160758603061⟩
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData07
end PackedLocator_LocatorPhase6800ReceiptRowData07
