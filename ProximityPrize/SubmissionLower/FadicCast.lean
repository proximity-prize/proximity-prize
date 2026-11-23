import ProximityPrize.SubmissionLower.FadicChunkRaw

set_option autoImplicit false
set_option Elab.async false

namespace FadicGate

open Finset
open scoped BigOperators
open K1_13_2 (cappedCount cumulative denominator)

/-! ### The chunked chain -/

theorem rPrefix_cast (f : ℕ → ℕ) (n : ℕ) : ((rPrefix f n : ℕ) : ℤ) = ∑ k ∈ range n, (f k : ℤ) := by
  induction n with
  | zero => simp [rPrefix]
  | succ n ih =>
    rw [rPrefix,sum_range_succ, ← ih]
    rfl

theorem rSegHi_eq (base h m k : ℕ) : rSegHi base h m k = segHi base h m k := by
  unfold rSegHi segHi
  rw [rMin_eq]
  rfl

theorem rLowSeg_cast (J T Θ base h m k : ℕ) :
    ((rLowSeg J T Θ base h m k:ℕ):ℤ)=lowSeg J T Θ base h m k:=by
  unfold rLowSeg rLowSegAux lowSeg lowDeg
  rw [cond_ble,rSegHi_eq,rMin_eq]
  show ((if 26*segHi base h m k≤Θ then rCapped (min (segLo base h k) ((Θ - 26*segHi base h m k) / 25)) J T else 0:ℕ):ℤ)=_
  by_cases hc:26*segHi base h m k≤Θ
  · rw [if_pos hc,if_pos hc,rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem rHighSeg_cast (J T Θ base h m k : ℕ) :
    ((rHighSeg J T Θ base h m k:ℕ):ℤ)=highSeg J T Θ base h m k:=by
  unfold rHighSeg rHighSegAux highSeg highDeg
  rw [cond_ble,rSegHi_eq,rMin_eq]
  show ((if 26*segLo base h k≤Θ then rCapped (min (segHi base h m k) ((Θ - 26*segLo base h k) / 25)) J T else 0:ℕ):ℤ)=_
  by_cases hc:26*segLo base h k≤Θ
  · rw [if_pos hc,if_pos hc,rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem rSegSumLow_cast (J T Θ base h m : ℕ) :
    ((rSegSumLow J T Θ base h m:ℕ):ℤ)=segSumLow J T Θ base h m:=by
  unfold rSegSumLow segSumLow
  show ((h * rPrefix (rLowSeg J T Θ base h m) (m / h) + (m % h) * rLowSeg J T Θ base h m (m / h) : ℕ)
    : ℤ)=_
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_mul,rPrefix_cast,rLowSeg_cast]
  simp only [rLowSeg_cast]

theorem rSegSumHigh_cast (J T Θ base h m : ℕ) :
    ((rSegSumHigh J T Θ base h m:ℕ):ℤ)=segSumHigh J T Θ base h m:=by
  unfold rSegSumHigh segSumHigh
  show ((h * rPrefix (rHighSeg J T Θ base h m) (m / h) + (m % h) * rHighSeg J T Θ base h m (m / h) : ℕ)
    : ℤ)=_
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_mul,rPrefix_cast,rHighSeg_cast]
  simp only [rHighSeg_cast]

theorem rFlatLo_eq (B J : ℕ) : rFlatLo B J = flatLo B J := by
  unfold rFlatLo flatLo
  rw [rMin_eq]

theorem rFlatHi_eq (B J Θ : ℕ) : rFlatHi B J Θ = flatHi B J Θ := by
  unfold rFlatHi flatHi
  rw [cond_ble,rMax_eq,rMin_eq,rFlatLo_eq]
  rfl

private theorem ends_one {base m k : ℕ} (hk : k < m) :
    segLo base 1 k = base+k ∧ segHi base 1 m k = base+k := by
  have hm : k ≤ m-1 := by omega
  simp [segLo,segHi,min_eq_left hm]

private theorem segLow_one (J T theta base m : ℕ) :
    segSumLow J T theta base 1 m = ∑ k ∈ range m, term J T theta (base+k) := by
  unfold segSumLow
  simp only [Nat.cast_one,one_mul,Nat.div_one,Nat.mod_one,Nat.cast_zero,zero_mul,add_zero]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hl,hh⟩ := ends_one (base := base) (mem_range.mp hk)
  rw [lowSeg,lowDeg,hl,hh,term,padGrade]

private theorem segHigh_one (J T theta base m : ℕ) :
    segSumHigh J T theta base 1 m = ∑ k ∈ range m, term J T theta (base+k) := by
  unfold segSumHigh
  simp only [Nat.cast_one,one_mul,Nat.div_one,Nat.mod_one,Nat.cast_zero,zero_mul,add_zero]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hl,hh⟩ := ends_one (base := base) (mem_range.mp hk)
  rw [highSeg,highDeg,hl,hh,term,padGrade]

private theorem fastLow_one (B J T theta : ℕ) :
    fastLow B J T theta 1 = boxCount B J T theta := by
  rw [← fastCount_eq]
  unfold fastLow fastCount
  rw [segLow_one,segLow_one,intPrefix_eq,intPrefix_eq]
  simp only [zero_add]

private theorem fastHigh_one (B J T theta : ℕ) :
    fastHigh B J T theta 1 = boxCount B J T theta := by
  rw [← fastCount_eq]
  unfold fastHigh fastCount
  rw [segHigh_one,segHigh_one,intPrefix_eq,intPrefix_eq]
  simp only [zero_add]

theorem rFastLow_cast (B J T Θ h : ℕ) : ((rFastLow B J T Θ h : ℕ) : ℤ) = fastLow B J T Θ h := by
  by_cases hh : h=1
  · subst h
    rw [rFastLow,ite_eq_left rfl,rExactBox_cast,fastLow_one]
  · rw [rFastLow,ite_eq_right hh]
    unfold rFastLowAux fastLow
    rw [rFlatLo_eq,rFlatHi_eq]
    simp only [Nat.add_eq,Nat.mul_eq,Nat.sub_eq]
    push_cast
    rw [rSegSumLow_cast,rSegSumLow_cast,rCapped_cast]

theorem rFastHigh_cast (B J T Θ h : ℕ) : ((rFastHigh B J T Θ h : ℕ) : ℤ) = fastHigh B J T Θ h := by
  by_cases hh : h=1
  · subst h
    rw [rFastHigh,ite_eq_left rfl,rExactBox_cast,fastHigh_one]
  · rw [rFastHigh,ite_eq_right hh]
    unfold rFastHighAux fastHigh
    rw [rFlatLo_eq,rFlatHi_eq]
    simp only [Nat.add_eq,Nat.mul_eq,Nat.sub_eq]
    push_cast
    rw [rSegSumHigh_cast,rSegSumHigh_cast,rCapped_cast]

theorem rDepthB_eq (σb xb r a : ℕ) : rDepthB σb xb r a = depthB σb xb r a := by
  unfold rDepthB depthB
  rw [rMin_eq]
  rfl

theorem rDepthJ_eq (σj xj r a : ℕ) : rDepthJ σj xj r a = depthJ σj xj r a := by
  unfold rDepthJ depthJ
  rw [rMin_eq]
  rfl

theorem rDepthΘ_eq (xb xj a:ℕ):rDepthΘ xb xj a=depthΘ xb xj a:=rfl

theorem ble_true (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b := by
  rw [Nat.ble_eq]

theorem rDepthOK_iff (xb xj r a : ℕ) : rDepthOK xb xj r a = true ↔ DepthOK xb xj r a := by
  unfold rDepthOK DepthOK
  simp only [Bool.and_eq_true,ble_true,Nat.mul_eq,Nat.add_eq]
  omega

theorem natSub_cast (a b : ℕ) : ((a - b : ℕ) : ℤ) = max 0 ((a : ℤ) - (b : ℤ)) := by
  by_cases h:b≤a
  · rw [Nat.cast_sub h,max_eq_right (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), max_eq_left (by omega)]
    rfl

theorem rMultHigh_cast (h σb σj σt bl bh jl jh r a : ℕ) :
    ((rMultHighAux h σt bl jl r a (rDepthB σb bh r a) (rDepthJ σj jh r a) (rDepthΘ bh jh a) : ℕ) : ℤ) =
      multHigh h σb σj σt bl bh jl jh r a:=by
  unfold rMultHighAux multHigh
  rw [rDepthB_eq,rDepthJ_eq,rDepthΘ_eq]
  by_cases hg:bl≤depthB σb bh r a ∧ jl≤depthJ σj jh r a ∧ 26*bl≤depthΘ bh jh a
  · have hb : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a))=true:=by
      simp only [Bool.and_eq_true,ble_true,Nat.mul_eq]
      exact ⟨⟨hg.1,hg.2.1⟩,hg.2.2⟩
    rw [hb,if_pos hg]
    show ((rFastHigh _ _ _ _ h:ℕ):ℤ)=_
    rw [rFastHigh_cast]
    rfl
  · have hb : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a))=false:=by
      cases hc : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a))
      · rfl
      · simp only [Bool.and_eq_true, ble_true, Nat.mul_eq] at hc
        exact absurd ⟨hc.1.1,hc.1.2,hc.2⟩ hg
    rw [hb,if_neg hg]
    rfl

theorem rDepthLow_cast (h σb σj σt bl bh jl jh r a : ℕ) :
    ((rDepthLow h σb σj σt bl bh jl jh r a:ℕ):ℤ)=depthLow h σb σj σt bl bh jl jh r a:=by
  unfold rDepthLow depthLow
  by_cases hok:DepthOK bh jh r a
  · rw [(rDepthOK_iff bh jh r a).mpr hok, if_pos hok]
    show ((rDepthLowAux h σt bl jl r a _ _ _:ℕ):ℤ)=_
    unfold rDepthLowAux
    simp only [Nat.sub_eq]
    rw [natSub_cast,rMultHigh_cast,rFastLow_cast,rDepthB_eq,rDepthJ_eq,rDepthΘ_eq]
    rfl
  · have hb : rDepthOK bh jh r a = false := by
      cases hc:rDepthOK bh jh r a
      · rfl
      · exact absurd ((rDepthOK_iff bh jh r a).mp hc) hok
    rw [hb,if_neg hok]
    rfl

theorem rFadicLow_cast (h σb σj σt bl bh jl jh r : ℕ) :
    ((rFadicLow h σb σj σt bl bh jl jh r:ℕ):ℤ)=fadicLow h σb σj σt bl bh jl jh r:=by
  unfold rFadicLow fadicLow
  rw [rPrefix_cast]
  simp only [rDepthLow_cast]
  rfl

theorem rPlainLow_cast (h σb σj σt r : ℕ) :
    ((rPlainLow h σb σj σt r:ℕ):ℤ)=plainLow h σb σj σt r:=by
  unfold rPlainLow plainLow
  rw [rMin_eq,rMin_eq,rFastLow_cast]
  rfl

theorem rIsFull_iff (σb σj σt r : ℕ) : rIsFull σb σj σt r = true ↔ IsFull σb σj σt r := by
  unfold rIsFull IsFull
  simp only [Bool.and_eq_true,ble_true,Nat.mul_eq]
  tauto

/-- **The raw certificate value is the checked certified loss.** -/
theorem rCertLoss_cast (S h σb σj σt bl bh jl jh i : ℕ) :
    ((rCertLoss S h σb σj σt bl bh jl jh i:ℕ):ℤ)=certLoss S h σb σj σt bl bh jl jh i:=by
  unfold rCertLoss certLoss
  by_cases hf:IsFull σb σj σt (i+1)
  · rw [(rIsFull_iff σb σj σt (Nat.add i 1)).mpr hf, if_pos hf]
    rfl
  · have hb : rIsFull σb σj σt (Nat.add i 1) = false := by
      cases hc:rIsFull σb σj σt (Nat.add i 1)
      · rfl
      · exact absurd ((rIsFull_iff σb σj σt (Nat.add i 1)).mp hc) hf
    rw [hb,if_neg hf]
    show (((S - rMax (rPlainLow h σb σj σt (i+1)) (rFadicLow h σb σj σt bl bh jl jh (i+1)):ℕ)):ℤ)=_
    rw [natSub_cast,rMax_eq,Nat.cast_max,rPlainLow_cast,rFadicLow_cast]

end FadicGate

#print axioms FadicGate.rCapped_cast
#print axioms FadicGate.rCertLoss_cast
