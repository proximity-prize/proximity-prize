import ProximityPrize.SubmissionLower.GoldBranch6N4
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_5
open K1_14 (Shape slots shapeSum)
open P1_7 (contactPower)
def kept (U v g r : ℕ) : ℕ :=
  if r ≤ g then slots U (r*v) else 0
end P1_7_5
end
section
namespace P1_7_5
noncomputable section
open Polynomial Finset MvPolynomial
open K1_14 (FX Jet Equation Shape SeedBound shapeSum slots triangle)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_mul seedDegree_pow)
open P1_7 (contactPower)
open private flatten flatten_mem_bidegree from ProximityPrize.SubmissionLower.Fast069
open private gradeMap mem_filtered finrank_le_grades from ProximityPrize.SubmissionLower.Fast069
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
private theorem rank_joint_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a U yspent spent : ℕ} (hyspent : yspent ≤ g.natDegree) (hspent : spent ≤ seedDegree g)
    (hC : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧ SeedBound c U ∧ g ∣ c) :
    Module.rank FX C ≤ (↑((a - yspent) * slots U spent) : Cardinal) := by
  have hquot : ∀ c ∈ C, c ≠ 0 → ∃ q : Equation,
      c = g * q ∧ q.natDegree < a - yspent ∧ spent + seedDegree q ≤ U := by
    intro c hc hn
    obtain ⟨hY, hU, q, rfl⟩ := hC c hc hn
    have hq : q ≠ 0 := right_ne_zero_of_mul hn
    refine ⟨q, rfl, ?_, ?_⟩
    · rw [Polynomial.natDegree_mul hg hq] at hY
      omega
    · have h := (seedDegree_le_iff _ _).mpr hU
      rw [seedDegree_mul hg hq] at h
      omega
  by_cases h : 0 < a - yspent ∧ spent ≤ U
  · let B := restrictBidegree (Fin 2) FX (a - yspent - 1) (U - spent)
    let m : B →ₗ[FX] Equation :=
      (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
    have hm : C ≤ LinearMap.range m := by
      intro c hc
      by_cases hn : c = 0
      · rw [hn]
        exact (LinearMap.range m).zero_mem
      · obtain ⟨q, rfl, hq, hqU⟩ := hquot c hc hn
        refine ⟨⟨flatten q, flatten_mem_bidegree (by omega) (by omega)⟩, ?_⟩
        change g * flatten.symm (flatten q) = g * q
        rw [AlgEquiv.symm_apply_apply]
    have hB : Module.finrank FX B = (a-yspent) * slots U spent := by
      rw [MvPolynomial.finrank_restrictBidegree, slots, ite_eq_left h.2]
      simp [Nat.choose_two_right, triangle, Nat.mul_comm (U-spent+2),
        show a-yspent-1+1 = a-yspent by omega]
    calc
      _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hm
      _ ≤ Module.rank FX B := rank_range_le m
      _ = _ := by rw [← Module.finrank_eq_rank, hB]
  · have hc : C = ⊥ := by
      apply bot_unique
      intro c hmem
      rw [Submodule.mem_bot]
      by_contra hn
      obtain ⟨q, _, hq, hqU⟩ := hquot c hmem hn
      exact h ⟨by omega, by omega⟩
    rw [hc]
    simp
private theorem gradeCapacity_eq (k B W j U r E v : ℕ) (hk : 0 < k) (he : 0 < E) :
    (gradeWidth k B W j - r*E) * slots U (r*v) =
      ∑ q ∈ Ico j (B+1), if q*k ≤ W+j then kept U v ((q-j)/E) r else 0 := by
  have hq (q : ℕ) : q*k ≤ W+j ↔ q < (W+j)/k + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]
  have hr (q : ℕ) : r ≤ (q-j)/E ↔ r*E ≤ q-j := Nat.le_div_iff_mul_le he
  have hI : (Ico j (B+1)).filter (fun q => q*k ≤ W+j ∧ r ≤ (q-j)/E) =
      Ico (j + r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, hq, hr, lt_min_iff]
    omega
  simp_rw [kept, ← ite_and]
  rw [← sum_filter, hI, sum_const, Nat.nsmul_eq_mul, Nat.card_Ico, gradeWidth, Nat.sub_sub]
end
end P1_7_5
end
section
namespace P1_7_5
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1 (agreement)
open P1_7 (jointGain)
open private slots_antitone sum_slot_drops sum_interval power_threshold from ProximityPrize.SubmissionLower.Fast072
private theorem position_sum (top step t j U v g : ℕ) (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then
      kept U v g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
      slots U (g*v) * (top+j-t-step*(j+g))) =
    triangle U * (top+j-t) := by
  let A := kept U v g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone A := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [A, kept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        slots_antitone U (Nat.mul_le_mul_right v hab)
    · simp [A, kept, hb]
  have hmin (l : ℕ) : A (min (g+1) l) = A l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A, kept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (A a - A (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
        slots U (g*v) * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [A, kept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [A, kept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then A (L W) else 0) + _ = _
  have hzero : A 0 = triangle U := by simp [A, kept, slots]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops A hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]
end P1_7_5
end
