import ProximityPrize.SubmissionLower.HighCore82258ScheduleData

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option maxRecDepth 18000

namespace HighCore82258_3
open HighCore82258 (Band)
open P1_7_4 (pairMinSeed pairMinOrdinate sharedBound)

private def grid (limit i:ℕ):ℕ:=i*limit/4

private theorem in_cell (n x : ℕ) (hx : x ≤ n) :
    ∃ i:Fin 4,grid n i.val≤x ∧ x≤grid n (i.val+1):=by
  by_cases h1:x≤grid n 1
  · exact ⟨0,by simp [grid],h1⟩
  by_cases h2:x≤grid n 2
  · exact ⟨1,Nat.le_of_lt (Nat.lt_of_not_ge h1),h2⟩
  by_cases h3:x≤grid n 3
  · exact ⟨2,Nat.le_of_lt (Nat.lt_of_not_ge h2),h3⟩
  · have h4 : grid n 4 = n := by unfold grid; omega
    exact ⟨3,Nat.le_of_lt (Nat.lt_of_not_ge h3),h4.symm ▸ hx⟩

private theorem grid_le (n i : ℕ) (hi : i ≤ 4) : grid n i ≤ n := by
  unfold grid
  calc
    i*n/4≤4*n/4:=Nat.div_le_div_right (Nat.mul_le_mul_right n hi)
    _=n:=by omega

private def mixedThresholdTable : Band → List (List ℕ)
  | .h2367 => [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[4,5,7,8,5,6,8,10,6,7,9,12,7,8,10,12],[5,6,8,10,7,8,10,13,8,9,11,14,9,10,12,15],[7,8,11,14,9,11,14,17,10,12,15,18,12,13,16,19],[9,12,15,19,12,14,19,23,14,16,21,25,16,18,21,26],[14,18,21,24,16,21,24,27,21,25,28,30,26,31,34,37],[11,14,18,23,14,17,23,28,17,20,24,29,20,22,26,32],[13,17,22,28,18,21,28,34,21,24,30,36,24,27,32,39],[12,17,20,22,15,19,22,25,19,23,25,27,24,28,31,33]]

  | .h2430 | .h2429 | .h2429B => []
private def chosen (b : Band) (i : ℕ) (x z : Fin 4) : ℕ :=
  ((((mixedThresholdTable b)[i]?).getD [])[4*x.val+z.val]?).getD 1

private def checks (b : Band) (i : Fin (laterCount b+1)) (x z : Fin 4) : Prop :=
  let S:=stageAt b i.val
  let a:=S.free.shape
  let c:=S.moving.shape
  let r:=chosen b i.val x z
  match mixedCap b i.val with
  | none => True
  | some cap => 0 < r ∧ r ≤ S.reserve+1 ∧
      ∀ growSeed growOrdinate : Bool,
        sharedBound a c
          (grid (pairMinSeed a c) (x.val+if growSeed then 1 else 0))
          (grid (pairMinOrdinate a c) (z.val+if growOrdinate then 1 else 0))
          r (S.reserve+1) true 2≤cap

private instance (b : Band) (i : Fin (laterCount b+1)) (x z : Fin 4) :
    Decidable (checks b i x z):=by unfold checks; split <;> infer_instance

private theorem checked (b : Band) (i : Fin (laterCount b+1)) :
    ∀ x z:Fin 4,checks b i x z:=by
  cases b <;> fin_cases i <;> decide +kernel

theorem adapted_mixed_bound {m : Mass} (b : Band) (i : Fin (laterCount b+1)) {cap : ℚ}
    (hc:mixedCap b i.val=some cap) {x z:ℕ}
    (hx:x≤pairMinSeed (stageAt b i.val).free.shape (stageAt b i.val).moving.shape)
    (hz:z≤pairMinOrdinate (stageAt b i.val).free.shape (stageAt b i.val).moving.shape)
    (hm : ∀ r, 0 < r → r ≤ (stageAt b i.val).reserve+1 →
      ∀ k, m k ≤ sharedBound (stageAt b i.val).free.shape (stageAt b i.val).moving.shape
          x z r ((stageAt b i.val).reserve+1) true k) :
    m 2≤cap:=by
  let S:=stageAt b i.val
  let a:=S.free.shape
  let c:=S.moving.shape
  obtain ⟨seedCell,hxl,hxu⟩:=in_cell (pairMinSeed a c) x hx
  obtain ⟨ordinateCell,hzl,hzu⟩:=in_cell (pairMinOrdinate a c) z hz
  have hx' : seedCell.val+1≤4:=seedCell.isLt
  have hz' : ordinateCell.val+1≤4:=ordinateCell.isLt
  have cert:=checked b i seedCell ordinateCell
  unfold checks at cert
  rw [hc] at cert
  obtain ⟨hr0,hr,he⟩:=cert
  refine (hm _ hr0 hr 2).trans (P1_7_4_2.shared_mixed_box a c hxl hxu
    (grid_le _ _ hx') hzl hzu (grid_le _ _ hz') ?_)
  intro u hu v hv
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · simpa using he false false
  · simpa using he false true
  · simpa using he true false
  · simpa using he true true
end HighCore82258_3
