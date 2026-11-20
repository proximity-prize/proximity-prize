import ProximityPrize.SubmissionLower.Koala6844ReceiptsSchedule
import ProximityPrize.SubmissionLower.Koala6844ReceiptsBridge
import ProximityPrize.SubmissionLower.Koala6844VirtualShortWeightedCount
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessArithmetic

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
open Koala6844VirtualShort (weightedRectangle_eq_sum weightedRectangle_mono SeedlessRectangle card_seedlessRectangle)

set_option autoImplicit false
set_option maxHeartbeats 2800000

private theorem sum_cubic_shift (n : Nat) (a b c d : Int) :
    12 * (∑ i ∈ Finset.range n, (a+b*((i : Int)+1)+c*((i : Int)+1)^2+d*((i : Int)+1)^3)) =
    12*a*n+6*b*n*((n : Int)+1)+2*c*n*((n : Int)+1)*(2*(n : Int)+1)+
      3*d*(n : Int)^2*((n : Int)+1)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

private theorem sum_fin_twice (n : Nat) :
    2 * (∑ i : Fin n, (i.val : Int)) = (n : Int)*((n : Int)-1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => (i : Int))]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

private theorem weightedRectangle_of_full (a b z h : Nat) (hz : h ≤ z) (hfull : a+b ≤ h+2) :
    12 * (weightedRectangle a b z h : Int) =
      6*(a : Int)*b*(2*(z : Int)+2-a-b) := by
  have hsum : (weightedRectangle a b z h : Int) =
      ∑ i : Fin a, ∑ j : Fin b, ((z : Int)-i.val-j.val) := by
    rw [weightedRectangle_eq_sum a b z h hz]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hji : i.val+j.val ≤ h := by have hi := i.isLt; have hj := j.isLt; omega
    have hiz : i.val ≤ z := by omega
    have hjz : j.val ≤ z-i.val := by omega
    rw [ite_eq_left hji, Nat.cast_sub hjz, Nat.cast_sub hiz]
  rw [hsum]
  have hflatten : (∑ i : Fin a, ∑ j : Fin b, ((z : Int)-i.val-j.val)) =
      (a : Int)*b*z-(b : Int)*(∑ i : Fin a, (i.val : Int))-
        (a : Int)*(∑ j : Fin b, (j.val : Int)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hflatten]
  linear_combination (-6*(b : Int)) * sum_fin_twice a + (-6*(a : Int)) * sum_fin_twice b

private theorem order_no_second_jet (m t : Nat) : localKernelOrder m t 0 0 = m-t := by
  unfold localKernelOrder
  simp only [Nat.sub_zero]
  exact max_eq_right (by omega)

private theorem firstJetRankRow_unfold (src : SourceShape) (t : Nat) (hs : src.s = 0) :
    ordinaryRankRow src t 0 =
      weightedRectangle (t+1) (src.B+1) (src.L+1) src.U -
        if src.m-t ≤ t ∧ src.m-t ≤ src.B ∧ src.m-t ≤ src.U then
          weightedRectangle (t+1-(src.m-t)) (src.B+1-(src.m-t))
            (src.L+1-(src.m-t)) (src.U-(src.m-t))
        else 0 := by
  unfold ordinaryRankRow
  simp only [hs, Nat.sub_zero, Nat.mul_zero, Nat.add_zero, order_no_second_jet]
  split_ifs <;> omega

private theorem ordinary_firstJetRow_twice (src : SourceShape) (t : Nat)
    (hs : src.s = 0) (ht : t < src.m) (hU : src.m+src.B ≤ src.U) (hL : src.U ≤ src.L) :
    12 * (ordinaryRankRow src t 0 : Int) =
      6*((src.B : Int)+1)*((t : Int)+1)*(2*(src.L : Int)+3-src.B-((t : Int)+1)) -
        if src.m-t ≤ min src.B (src.m/2) then
          6*((src.m : Int)+1-2*((src.m : Int)-t))*((src.B : Int)+1-((src.m : Int)-t))*
            (2*(src.L : Int)+2-src.m-src.B+((src.m : Int)-t))
        else 0 := by
  rw [firstJetRankRow_unfold src t hs]
  have hbase := weightedRectangle_of_full (t+1) (src.B+1) (src.L+1) src.U (by omega) (by omega)
  have hc : (src.m-t ≤ t ∧ src.m-t ≤ src.B ∧ src.m-t ≤ src.U) ↔
      src.m-t ≤ min src.B (src.m/2) := by omega
  by_cases hk : src.m-t ≤ min src.B (src.m/2)
  · rw [ite_eq_left (hc.mpr hk),ite_eq_left hk]
    let k := src.m-t
    have hkt : k ≤ t := (hc.mpr hk).1
    have hkB : k ≤ src.B := (hc.mpr hk).2.1
    have hkU : k ≤ src.U := (hc.mpr hk).2.2
    have hkL : k ≤ src.L := hkU.trans hL
    have hmono := weightedRectangle_mono
      (a := t+1) (b := src.B+1) (z := src.L+1) (h := src.U)
      (a' := t+1-k) (b' := src.B+1-k) (z' := src.L+1-k) (h' := src.U-k)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [Nat.cast_sub hmono, mul_sub,hbase]
    have hremoved := weightedRectangle_of_full (t+1-k) (src.B+1-k)
      (src.L+1-k) (src.U-k) (by omega) (by omega)
    change _ - 12 * (weightedRectangle (t+1-k) (src.B+1-k) (src.L+1-k) (src.U-k) : Int) = _
    rw [hremoved]
    have he : (k : Int) = (src.m : Int)-t := Nat.cast_sub (by omega)
    push_cast [Nat.cast_sub (show k ≤ t+1 by omega), Nat.cast_sub (show k ≤ src.B+1 by omega),
      Nat.cast_sub (show k ≤ src.L+1 by omega), he]
    ring
  · rw [ite_eq_right (fun h => hk (hc.mp h)),ite_eq_right hk,Nat.sub_zero,hbase]
    push_cast
    ring

private def ordinaryBase (B L : Nat) (u : Int) : Int :=
  6*((B : Int)+1)*u*(2*(L : Int)+3-B-u)

private def ordinaryRemoved (m B L : Nat) (d : Int) : Int :=
  6*((m : Int)+1-2*d)*((B : Int)+1-d)*(2*(L : Int)+2-m-B+d)

private theorem base_sum (m B L : Nat) :
    (∑ t ∈ Finset.range m, ordinaryBase B L ((t : Int)+1)) =
      ((B : Int)+1)*(m : Int)*((m : Int)+1)*
        (6*((L+1 : Nat) : Int)-2*((m-1 : Nat) : Int)-3*B) := by
  have hpoly := sum_cubic_shift m 0 (2*(L : Int)+3-B) (-1) 0
  have hfactor : 2 * (∑ t ∈ Finset.range m, ordinaryBase B L ((t : Int)+1)) =
      ((B : Int)+1) * (12 * (∑ t ∈ Finset.range m,
        (0+(2*(L : Int)+3-B)*((t : Int)+1)+(-1)*((t : Int)+1)^2+0*((t : Int)+1)^3))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold ordinaryBase
    ring
  rw [hpoly] at hfactor
  have hscaled : 2 * (∑ t ∈ Finset.range m, ordinaryBase B L ((t : Int)+1)) =
      2 * (((B : Int)+1)*(m : Int)*((m : Int)+1)*
         (6*((L+1 : Nat) : Int)-2*((m-1 : Nat) : Int)-3*B)) := by
    rw [hfactor]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  omega

private theorem removed_sum (m B L k : Nat) :
    let p0 : Int := (m+1)*(B+1)
    let p1 : Int := -((m+2*B+3 : Nat) : Int)
    let c : Int := 2*(L : Int)+2-m-B
    (∑ d ∈ Finset.range k, ordinaryRemoved m B L ((d : Int)+1)) =
      6*p0*c*k + 3*(p0+p1*c)*k*(k+1 : Nat) +
      (p1+2*c)*k*(k+1 : Nat)*(2*k+1 : Nat) + 3*k*k*(k+1 : Nat)^2 := by
  let p0 : Int := (m+1)*(B+1)
  let p1 : Int := -((m+2*B+3 : Nat) : Int)
  let c : Int := 2*(L : Int)+2-m-B
  have hpoly := sum_cubic_shift k (p0*c) (p0+p1*c) (p1+2*c) 2
  have hfactor : 2 * (∑ d ∈ Finset.range k, ordinaryRemoved m B L ((d : Int)+1)) =
      12 * (∑ d ∈ Finset.range k,
        (p0*c+(p0+p1*c)*((d : Int)+1)+(p1+2*c)*((d : Int)+1)^2+2*((d : Int)+1)^3)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold ordinaryRemoved p0 p1 c
    push_cast
    ring
  rw [hpoly] at hfactor
  change (∑ d ∈ Finset.range k, ordinaryRemoved m B L ((d : Int)+1)) = _
  have hscaled : 2 * (∑ d ∈ Finset.range k, ordinaryRemoved m B L ((d : Int)+1)) =
      2 * (6*p0*c*k + 3*(p0+p1*c)*k*(k+1 : Nat) +
        (p1+2*c)*k*(k+1 : Nat)*(2*k+1 : Nat) + 3*k*k*(k+1 : Nat)^2) := by
    rw [hfactor]
    push_cast
    ring
  exact mul_left_cancel₀ (by norm_num : (2 : Int) ≠ 0) hscaled

private theorem reverse_firstJet_removed (m k : Nat) (hkm : k ≤ m) (P : Int → Int) :
    (∑ t ∈ Finset.range m, if m-t ≤ k then P ((m : Int)-t) else 0) =
      ∑ d ∈ Finset.range k, P ((d : Int)+1) := by
  calc
    _ = ∑ t ∈ Finset.range m, (if m-(m-1-t) ≤ k then P ((m : Int)-(m-1-t : Nat)) else 0) := by
      symm
      exact Finset.sum_range_reflect (fun t => if m-t ≤ k then P ((m : Int)-t) else 0) m
    _ = ∑ t ∈ Finset.range m, (if t+1 ≤ k then P ((t : Int)+1) else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have hn : m-(m-1-t) = t+1 := by omega
      have hi : (m : Int)-(m-1-t : Nat) = (t : Int)+1 := by
        rw [Nat.cast_sub (show t ≤ m-1 by omega), Nat.cast_sub (show 1 ≤ m by omega)]
        push_cast
        ring
      rw [hn,hi]
    _ = _ := by
      rw [← Finset.sum_filter]
      have hf : (Finset.range m).filter (fun t => t+1 ≤ k) = Finset.range k := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hf]

private theorem ordinaryFirstJetRank_as_sum (src : SourceShape) (hs : src.s = 0) :
    ordinaryRankBound src = ∑ t ∈ Finset.range src.m, ordinaryRankRow src t 0 := by
  unfold ordinaryRankBound
  rw [sumRange_eq_finset_range]
  apply Finset.sum_congr rfl
  intro t _
  simp [hs,sumRange]

theorem ordinaryFirstJetRankTwelve_eq (src : SourceShape) (hs : src.s = 0)
    (hU : src.m+src.B ≤ src.U) (hL : src.U ≤ src.L) :
    12*(ordinaryRankBound src : Int) = firstJetRankTwelve src.m src.B src.L := by
  rw [ordinaryFirstJetRank_as_sum src hs]
  push_cast
  rw [Finset.mul_sum]
  let k := min src.B (src.m/2)
  have hrows : (∑ t ∈ Finset.range src.m, 12 * (ordinaryRankRow src t 0 : Int)) =
      ∑ t ∈ Finset.range src.m, (ordinaryBase src.B src.L ((t : Int)+1) -
        if src.m-t ≤ k then ordinaryRemoved src.m src.B src.L ((src.m : Int)-t) else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact ordinary_firstJetRow_twice src t hs (Finset.mem_range.mp ht) hU hL
  rw [hrows, Finset.sum_sub_distrib,base_sum,
    reverse_firstJet_removed src.m k (by omega),removed_sum]
  rfl

private theorem seedlessRectangle_of_full (a b h : Nat) (hfull : a+b ≤ h+2) :
    seedlessRectangle a b h = a*b := by
  let e : SeedlessRectangle a b h ≃ Fin a × Fin b :=
    ⟨Subtype.val, fun p => ⟨p, by
      have h₁ := p.1.isLt
      have h₂ := p.2.isLt
      omega⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← card_seedlessRectangle, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

private theorem subtract_rank_at_succ (m B L : Nat) :
    firstJetRankTwelve m B (L + 1) - firstJetRankTwelve m B L = firstJetRankSlopeTwelve m B := by
  unfold firstJetRankSlopeTwelve firstJetRankTwelve
  push_cast
  ring

private def seedlessFirstJetRow (m B U t : Nat) : Nat :=
  seedlessRectangle (t+1) (B+1) U -
    if m-t ≤ t ∧ m-t ≤ B ∧ m-t ≤ U then
      seedlessRectangle (t+1-(m-t)) (B+1-(m-t)) (U-(m-t)) else 0

private theorem seedlessFirstJetRow_eq_difference (m B U t : Nat) (ht : t < m) (hU : m+B ≤ U) :
    let lo : SourceShape := ⟨m,B,0,U,U,0,1,0⟩
    let hi : SourceShape := ⟨m,B,0,U,U+1,0,1,0⟩
    12*(seedlessFirstJetRow m B U t : Int) =
      12*(ordinaryRankRow hi t 0 : Int)-12*(ordinaryRankRow lo t 0 : Int) := by
  dsimp only
  rw [ordinary_firstJetRow_twice _ _ rfl ht hU (Nat.le_succ U),
    ordinary_firstJetRow_twice _ _ rfl ht hU (Nat.le_refl U)]
  dsimp only
  unfold seedlessFirstJetRow
  have hc : (m-t ≤ t ∧ m-t ≤ B ∧ m-t ≤ U) ↔ m-t ≤ min B (m/2) := by omega
  rw [seedlessRectangle_of_full _ _ _ (by omega)]
  by_cases hk : m-t ≤ min B (m/2)
  · simp only [ite_eq_left (hc.mpr hk), ite_eq_left hk]
    let k := m-t
    have hkt : k ≤ t := (hc.mpr hk).1
    have hkB : k ≤ B := (hc.mpr hk).2.1
    have hkU : k ≤ U := (hc.mpr hk).2.2
    rw [seedlessRectangle_of_full _ _ _ (by omega)]
    rw [Nat.cast_sub (Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..))]
    have he : (k : Int) = (m : Int)-t := Nat.cast_sub (by omega)
    change 12*((((t+1)*(B+1) : Nat) : Int)-(((t+1-k)*(B+1-k) : Nat) : Int)) = _
    push_cast [Nat.cast_sub (show k ≤ t+1 by omega), Nat.cast_sub (show k ≤ B+1 by omega), he]
    ring
  · simp only [ite_eq_right hk, ite_eq_right (fun h => hk (hc.mp h)), Nat.sub_zero]
    push_cast
    ring

theorem auxiliaryFirstJetRankTwelve_eq (src : SourceShape) (j : Nat) (hs : src.s = 0)
    (hj : j ≤ src.U) (hU : src.m+src.B ≤ src.U) :
    12*(auxiliaryRankSlice src j : Int) = firstJetRankSlopeTwelve (src.m-j) src.B := by
  by_cases hjm : j ≤ src.m
  · let m := src.m-j
    let U := src.U-j
    let lo : SourceShape := ⟨m,src.B,0,U,U,0,1,0⟩
    let hi : SourceShape := ⟨m,src.B,0,U,U+1,0,1,0⟩
    have hsmall : m+src.B ≤ U := by dsimp only [m,U]; omega
    have hsum : auxiliaryRankSlice src j = ∑ t ∈ Finset.range m, seedlessFirstJetRow m src.B U t := by
      unfold auxiliaryRankSlice
      rw [ite_eq_left hj, sumRange_eq_finset_range]
      apply Finset.sum_congr rfl
      intro t _
      simp only [hs, zero_min, Nat.zero_add, sumRange, List.range_one, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, Nat.sub_zero, Nat.mul_zero, order_no_second_jet]
      unfold seedlessFirstJetRow
      let k := m-t
      let all := seedlessRectangle (t+1) (src.B+1) U
      change (if k ≤ t ∧ k ≤ src.B then
          if k ≤ U then all-seedlessRectangle (t-k+1) (src.B+1-k) (U-k) else all
        else all) = all - (if k ≤ t ∧ k ≤ src.B ∧ k ≤ U then
          seedlessRectangle (t+1-k) (src.B+1-k) (U-k) else 0)
      by_cases hkt : k ≤ t ∧ k ≤ src.B
      · have hkU : k ≤ U := by dsimp only [k]; omega
        have hboth : k ≤ t ∧ k ≤ src.B ∧ k ≤ U := ⟨hkt.1,hkt.2,hkU⟩
        simp only [ite_eq_left hkt, ite_eq_left hkU, ite_eq_left hboth]
        rw [show t-k+1 = t+1-k by omega]
      · simp only [ite_eq_right hkt, ite_eq_right (fun h : k ≤ t ∧ k ≤ src.B ∧ k ≤ U => hkt ⟨h.1,h.2.1⟩),Nat.sub_zero]

    have hHi := ordinaryFirstJetRankTwelve_eq hi rfl hsmall (Nat.le_succ U)
    have hLo := ordinaryFirstJetRankTwelve_eq lo rfl hsmall (Nat.le_refl U)
    change 12*(ordinaryRankBound hi : Int) = firstJetRankTwelve m src.B (U+1) at hHi
    change 12*(ordinaryRankBound lo : Int) = firstJetRankTwelve m src.B U at hLo
    change _ = firstJetRankSlopeTwelve m src.B
    rw [← subtract_rank_at_succ m src.B U, ← hHi, ← hLo,
      hsum, ordinaryFirstJetRank_as_sum hi rfl, ordinaryFirstJetRank_as_sum lo rfl]
    change 12*((∑ t ∈ Finset.range m, seedlessFirstJetRow m src.B U t : Nat) : Int) =
      12*((∑ t ∈ Finset.range m, ordinaryRankRow hi t 0 : Nat) : Int)-
      12*((∑ t ∈ Finset.range m, ordinaryRankRow lo t 0 : Nat) : Int)
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    exact seedlessFirstJetRow_eq_difference m src.B U t (Finset.mem_range.mp ht) hsmall
  · have hm : src.m-j=0 := by omega
    simp [auxiliaryRankSlice, hj, hm, sumRange, firstJetRankSlopeTwelve, firstJetRankTwelve]

end ProximityPrize.SubmissionLower.Koala6844Receipts
