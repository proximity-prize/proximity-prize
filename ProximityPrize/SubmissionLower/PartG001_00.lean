import ProximityPrize.SubmissionLower.PartG000

section Compact_PackedLocatorTail
/-! Packed: amortised derivative-chain caps. -/
section PackedLocator_ChainAmort

/-!
# Amortised chain caps

The derivative chain over an irreducible factor `F` of `R`-degree `d` charges its
level `j` to the coprime pair `(d_R^j F, F)`, whose LEFT `R`-degree is at most
`d - j` (`dR_R_degree_le`); the RIGHT factor is `F` itself and does not descend.
With a monotone level cap, `capSum cap d` is superadditive, so a family of factors
whose `R`-degrees sum to at most `s` costs at most `capSum cap s`.

Each factor also carries ONE slope-free tail, and there is one further global
`R`-free tail.  Charging the chain at its `k = 1` maximum and the tails at their
`k = s` maximum double-counts: with `tail <= cap 1` the augmented allowance
`capSumT cap tail d = capSum cap d + tail` is still superadditive, so chains and
tails together cost `capSum cap s + tail`, and the global tail brings the total to
`capSum cap s + 2 * tail` in place of `capSum cap s + (s+1) * tail`.
-/


open Finset

namespace ChainAmort

/-- The amortised chain cap: the sum of the per-level caps below `d`. -/
def capSum (cap : ℕ → ℕ) (d : ℕ) : ℕ := ∑ t ∈ Finset.Ico 1 d, cap t

@[simp] theorem capSum_zero (cap : ℕ → ℕ) : capSum cap 0 = 0 := by
  simp [capSum]

@[simp] theorem capSum_one (cap : ℕ → ℕ) : capSum cap 1 = 0 := by
  simp [capSum]

theorem capSum_succ (cap : ℕ → ℕ) {d : ℕ} (hd : 1 ≤ d) :
    capSum cap (d + 1) = capSum cap d + cap d := by
  simp [capSum, Finset.sum_Ico_succ_top hd]

theorem capSum_mono (cap : ℕ → ℕ) : Monotone (capSum cap) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

/-- With a monotone level cap, the amortised sum is superadditive. -/
theorem capSum_superadditive (cap : ℕ → ℕ) (hmono : Monotone cap) (a b : ℕ) :
    capSum cap a + capSum cap b ≤ capSum cap (a + b) := by
  induction b with
  | zero => simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simpa using capSum_mono cap (Nat.le_succ a)
      · rw [capSum_succ cap hk, ← Nat.add_assoc,
          show a + (k + 1) = (a + k) + 1 by omega,
          capSum_succ cap (by omega : 1 ≤ a + k)]
        exact Nat.add_le_add ih (hmono (by omega))

/-- Summed over a family whose total does not exceed `s`. -/
theorem sum_capSum_le_sum {ι : Type*} [DecidableEq ι] (cap : ℕ → ℕ) (hmono : Monotone cap)
    (T : Finset ι) (d : ι → ℕ) :
    ∑ i ∈ T, capSum cap (d i) ≤ capSum cap (∑ i ∈ T, d i) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert x T hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact le_trans (Nat.add_le_add_left ih _) (capSum_superadditive cap hmono _ _)

/-- Summed over a family whose total does not exceed `s`. -/
theorem sum_capSum_le {ι : Type*} [DecidableEq ι] (cap : ℕ → ℕ) (hmono : Monotone cap)
    (T : Finset ι) (d : ι → ℕ) (s : ℕ) (h : ∑ i ∈ T, d i ≤ s) :
    ∑ i ∈ T, capSum cap (d i) ≤ capSum cap s :=
  le_trans (sum_capSum_le_sum cap hmono T d) (capSum_mono cap h)

end ChainAmort

namespace ChainAmort

/-- Reflection: summing the level caps down from `d` is the same as summing them up. -/
theorem sum_Ico_reflect (cap : ℕ → ℕ) (d : ℕ) :
    ∑ j ∈ Finset.Ico 1 d, cap (d - j) = capSum cap d := by
  classical
  unfold capSum
  refine Finset.sum_nbij' (fun j => d - j) (fun t => d - t) ?_ ?_ ?_ ?_ ?_ <;>
    intro x hx <;> simp only [Finset.mem_Ico] at hx ⊢ <;> omega

/-- The amortised chain bound in the shape the derivative chain produces:
each factor `i` contributes levels `j ∈ [1, c i)` charged at `cap (d i - j)`. -/
theorem chain_sum_bound {ι : Type*} [DecidableEq ι] (cap : ℕ → ℕ) (hmono : Monotone cap)
    (T : Finset ι) (d c : ι → ℕ) (s : ℕ)
    (hc : ∀ i ∈ T, c i ≤ d i) (hs : ∑ i ∈ T, d i ≤ s) :
    ∑ i ∈ T, ∑ j ∈ Finset.Ico 1 (c i), cap (d i - j) ≤ capSum cap s := by
  classical
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (sum_capSum_le cap hmono T d s hs)
  calc ∑ j ∈ Finset.Ico 1 (c i), cap (d i - j)
      ≤ ∑ j ∈ Finset.Ico 1 (d i), cap (d i - j) :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl (hc i hi))
    _ = capSum cap (d i) := sum_Ico_reflect cap (d i)

end ChainAmort

namespace ChainAmort

/-- One factor's chain levels, charged against its own degree. -/
theorem chain_row_le (cap : ℕ → ℕ) (d c : ℕ) (hc : c ≤ d) :
    ∑ j ∈ Finset.Ico 1 c, cap (d - j) ≤ capSum cap d := by
  calc ∑ j ∈ Finset.Ico 1 c, cap (d - j)
      ≤ ∑ j ∈ Finset.Ico 1 d, cap (d - j) :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hc)
    _ = capSum cap d := sum_Ico_reflect cap d

/-- Each factor carries its own chain AND its own tail.  With
`tail ≤ cap 1` the augmented allowance is still superadditive, so a family of factors
whose degrees sum to `s` costs at most `capSum cap s + tail` in chains-plus-tails —
and the single global R-free tail adds one more, giving `+ 2 * tail` in place of
`+ (s+1) * tail`. -/
def capSumT (cap : ℕ → ℕ) (tail d : ℕ) : ℕ := capSum cap d + tail

theorem capSumT_mono (cap : ℕ → ℕ) (tail : ℕ) {a b : ℕ} (h : a ≤ b) :
    capSumT cap tail a ≤ capSumT cap tail b :=
  Nat.add_le_add_right (capSum_mono cap h) _

theorem capSumT_superadditive (cap : ℕ → ℕ) (hmono : Monotone cap) (tail : ℕ)
    (htail : tail ≤ cap 1) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    capSumT cap tail a + capSumT cap tail b ≤ capSumT cap tail (a + b) := by
  unfold capSumT
  induction b with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have h0 : capSum cap (0 + 1) = 0 := by simp [capSum]
        have h1 : capSum cap (a + (0 + 1)) = capSum cap a + cap a := by
          simpa using capSum_succ cap ha
        have h2 : tail ≤ cap a := le_trans htail (hmono ha)
        omega
      · have h1 : capSum cap (k + 1) = capSum cap k + cap k := capSum_succ cap hk
        have h2 : capSum cap (a + (k + 1)) = capSum cap (a + k) + cap (a + k) := by
          rw [show a + (k + 1) = (a + k) + 1 by omega]
          exact capSum_succ cap (by omega)
        have h3 : cap k ≤ cap (a + k) := hmono (by omega)
        have h4 := ih hk
        omega

/-- Chains and tails charged together over the factor family. -/
theorem sum_capSumT_le {ι : Type*} [DecidableEq ι] (cap : ℕ → ℕ) (hmono : Monotone cap)
    (tail : ℕ) (htail : tail ≤ cap 1)
    (T : Finset ι) (d : ι → ℕ) (s : ℕ)
    (hpos : ∀ i ∈ T, 1 ≤ d i) (h : ∑ i ∈ T, d i ≤ s) :
    ∑ i ∈ T, capSumT cap tail (d i) ≤ capSumT cap tail s := by
  classical
  have key : ∀ (T : Finset ι), (∀ i ∈ T, 1 ≤ d i) → T.Nonempty →
      ∑ i ∈ T, capSumT cap tail (d i) ≤ capSumT cap tail (∑ i ∈ T, d i) := by
    intro T
    induction T using Finset.induction with
    | empty => intro _ hne; exact absurd hne (by simp)
    | insert x T hx ih =>
        intro hp _
        rcases T.eq_empty_or_nonempty with rfl | hne
        · simp
        · rw [Finset.sum_insert hx, Finset.sum_insert hx]
          have hsum : 1 ≤ ∑ i ∈ T, d i := by
            obtain ⟨y, hy⟩ := hne
            exact le_trans (hp y (Finset.mem_insert_of_mem hy))
              (Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) hy)
          refine le_trans (Nat.add_le_add_left
            (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)) hne) _) ?_
          exact capSumT_superadditive cap hmono tail htail
            (hp x (Finset.mem_insert_self x T)) hsum
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [capSumT]
  · exact le_trans (key T hpos hne) (capSumT_mono cap tail h)

end ChainAmort

namespace ChainGroupMaj
open ProximityPrize.SubmissionLower.RCN260 ProximityPrize.SubmissionLower.RCN294

/-- Per-level pair parameters of a chain group with total slope `r`, Y-degree `y` and
zc-degree `zc` at the 6803 profile (`n = 262144, w = 131071, a = 181363`): level `t` charges
the pair `(d_R^{r-t} F, F)` with LEFT slope `t` and RIGHT slope `r`. -/
def chainGroupAt (zc r y t : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363, y, max 1 (min t r), zc, y, max 1 r, zc⟩

def coefA (zc r y : ℕ) : ℕ :=
  131073 * ((1 + 2 * 131071 * y) * (zc * r) +
    131071 * (2 * r - 1) * (2 * zc * y) +
    (2 * 131071 * zc + 1) * (y * r)) +
  (80781 + 1) * 50292 * (y * r)

def coefB (zc y : ℕ) : ℕ :=
  131073 * ((1 + 2 * 131071 * y) * zc + (2 * 131071 * zc + 1) * y) +
  (80781 + 1) * 50292 * y

/-- Closed-form majorant of `ChainAmort.capSum (fun t => (chainGroupAt zc r y t).regularCountCap) r`. -/
def chainMaj (zc r y : ℕ) : ℕ :=
  ((r - 1) * coefA zc r y + coefB zc y * (∑ t ∈ Finset.Ico 1 r, t)) / 50292

theorem chainGroupAt_gap (zc r y t : ℕ) : (chainGroupAt zc r y t).gap = 50292 := by
  change (181363 - 131071 : ℕ) = 50292
  decide +kernel










/-- The gate facts a chain-group parameter family supplies to `fixed_chain_count_le_split`. -/
structure Gates (P : UnequalParameters) (zc r y : ℕ) : Prop where
  gap_pos : 0 < P.gap
  leftY_ge : y ≤ P.leftY
  rightY_ge : y ≤ P.rightY
  rightR_ge : r ≤ P.rightR
  leftZ_ge : zc ≤ P.leftZ
  rightZ_ge : zc ≤ P.rightZ
  leftR_pos : 1 ≤ P.leftR
  leftY_small : P.leftY < 2130706433
  leftR_small : P.leftR < 2130706433
  leftZ_small : P.leftZ < 2130706433
  mixedY_small : P.mixedCost.y < 2130706433
  mixedR_small : P.mixedCost.r < 2130706433
  mixedZ_small : P.mixedCost.z < 2130706433
  n_eq : P.n = 262144
  w_eq : P.w = 131071
  a_eq : P.a = 181363
  errors_eq : P.errors = 80781



/-- Residual-branch majorant at the 6802 profile, charged at slope `33 - d` where `d` is a
lower bound on the slope of the common divisor: the residual stage pair, the amortised
residual chain (closed form at `zc = LB = 14915`) and two slope-`1` tails. -/
def residMaj6802 (d : ℕ) : ℕ :=
  (⟨262144, 131071, 181363, 153, max 1 (33 - d), 14915, 250, 56, 6680⟩ :
    UnequalParameters).regularCountCap +
    chainMaj 14915 (33 - d) 153 + 2 * 4677667475173


end ChainGroupMaj

end PackedLocator_ChainAmort

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


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

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

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
def nodeFactor (x:K):P4 K:=MvPolynomial.X 0 - MvPolynomial.C x
def locator (nodes:I → K):P4 K:=∏ i:I, nodeFactor (nodes i)
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
end
end ProximityPrize.SubmissionLower.LocatorContact
end PackedLocator_LocatorContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

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
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorLowQuotient

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

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


end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I



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
end LinearDichotomy
end
end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance
end Compact_PackedLocatorTail
