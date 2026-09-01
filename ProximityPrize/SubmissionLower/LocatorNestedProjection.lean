import ProximityPrize.SubmissionLower.L1
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

/-- Kernel-cheap range summation.  Unlike `Finset.sum`, this unfolds through
plain natural-number recursion, without a `Multiset` quotient traversal. -/
def kernelSumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => kernelSumRange f n + f n

theorem kernelSumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [kernelSumRange]
  | succ k ih => rw [kernelSumRange, ih, Finset.sum_range_succ]

theorem finset_sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) =
      (m + 1) * a - (m + 1) * m / 2 := by
  have hadd :
      (∑ r ∈ Finset.range (m + 1), (a - r)) +
          (∑ r ∈ Finset.range (m + 1), r) = (m + 1) * a := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ r ∈ Finset.range (m + 1), (a - r) + r = a := by
      intro r hr
      have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range,
      Nat.nsmul_eq_mul]
  have hgauss : (∑ r ∈ Finset.range (m + 1), r) * 2 = (m + 1) * m :=
    Finset.sum_range_id_mul_two (m + 1)
  omega

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
