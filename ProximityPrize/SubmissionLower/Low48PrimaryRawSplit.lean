import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace Low48PrimaryPivot.RawClosed
open Finset K1_13_2 K1_13_2_2 K1_13_2_3
open scoped BigOperators
open private columnsAt targetAt target_eq from ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

def firstCross (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0,lo,_ => lo
  | fuel+1,lo,hi => if hi≤lo then lo else
    let mid := (lo+hi)/2
    if p mid then firstCross p fuel lo mid else firstCross p fuel (mid+1) hi

theorem cross_spec (p : ℕ → Bool) (fuel lo hi : ℕ) (h : lo≤hi) (hn : hi-lo<2^fuel) :
    let k:= firstCross p fuel lo hi
    lo≤k ∧ k≤hi ∧ (k=lo ∨ p (k-1)=false) ∧ (k=hi ∨ p k=true) := by
  induction fuel generalizing lo hi with
  | zero => simp only [pow_zero] at hn; simp [firstCross, show hi=lo by omega]
  | succ f ih =>
    rw [pow_succ] at hn
    simp only [firstCross]
    split
    · rename_i he; simp [show hi=lo by omega]
    · rename_i he
      let mid:=(lo+hi)/2
      have hm : lo≤mid ∧ mid<hi := by dsimp [mid]; omega
      change (let k:=if p mid=true then firstCross p f lo mid else firstCross p f (mid+1) hi; _) 
      split
      · rename_i hp
        obtain ⟨a,b,c,e⟩:=ih lo mid hm.1 (by dsimp [mid]; omega)
        exact ⟨a, b.trans hm.2.le, c, Or.inr (e.elim (fun eq => eq ▸ hp) id)⟩
      · rename_i hp
        obtain ⟨a,b,c,e⟩:=ih (mid+1) hi (by omega) (by dsimp [mid]; omega)
        refine ⟨(show lo≤mid+1 by omega).trans a,b,Or.inr ?_,e⟩
        rcases c with c|c
        · rw [c]; simpa using hp
        · exact c

theorem target_nonneg {g o : ℕ} (hg : 1650≤g) (hlo : 3000≤g+o) (hhi : g+o<4650) :
    0≤targetAt g o := by
  rw [← target_eq g o hg hlo hhi, ← K1_13_2_2_4.proof K1_13_2_2_2.proof]
  positivity

private theorem target_mono_order {d l u c a b : ℤ} (hab : a≤b) :
    targetCount ⟨d,l,u,c,a⟩ ≤ targetCount ⟨d,l,u,c,b⟩ := by
  rw [← K1_13_2_2_4.proof K1_13_2_2_2.proof, ← K1_13_2_2_4.proof K1_13_2_2_2.proof]
  apply Int.ofNat_le.mpr; apply card_le_card
  intro e he; rw [mem_targetColumns] at he ⊢
  change _ ∧ _ ∧ (e.weight contactWeight : ℤ)<a at he
  change _ ∧ _ ∧ (e.weight contactWeight : ℤ)<b
  exact ⟨he.1, he.2.1, he.2.2.trans_le hab⟩

theorem target_anti {g h o : ℕ} (gh : g≤h) (hg : 1650≤g) (hlo : 3000≤g+o) (hhi : h+o<4650) :
    targetAt h o≤targetAt g o := by
  rw [← target_eq g o hg hlo (by omega), ← target_eq h o (by omega) (by omega) hhi]
  apply target_mono_order
  exact sub_le_sub_right (sub_le_sub_left (Int.ofNat_le.mpr gh) 4650) _

def laneLen (n r : ℕ) := (n+23-r)/24

theorem sum_lanes (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, f i = ∑ r ∈ range 24, ∑ j ∈ range (laneLen n r), f (r+24*j) := by
  classical
  rw [sum_sigma']
  refine sum_bij' (fun i _ => ⟨i%24,i/24⟩) (fun v _ => v.1+24*v.2) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range] at hi; simp only [mem_sigma,mem_range,laneLen]; omega
  · rintro ⟨r,i⟩ hi; simp only [mem_sigma,mem_range,laneLen] at hi; simp only [mem_range]; omega
  · intro i hi; dsimp; omega
  · rintro ⟨r,i⟩ hi; simp only [mem_sigma,mem_range] at hi
    dsimp; congr <;> omega
  · intro i hi; dsimp; congr 1; omega

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lo n : ℕ) :
    ((List.range' lo n).map f).sum = ∑ i ∈ range n, f (lo+i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range'_concat, Finset.sum_range_succ, ih]

end Low48PrimaryPivot.RawClosed
