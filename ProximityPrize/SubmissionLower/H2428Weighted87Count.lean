import ProximityPrize.SubmissionLower.FadicCast

set_option autoImplicit false

namespace H2428Weighted87Count

open K1_13_2 (cappedCount cumulative denominator)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open private K1_13_2_2_3.cappedColumns K1_13_2_2_3.mem_cappedColumns K1_13_2_2_3.capped_card
  from ProximityPrize.SubmissionLower.Fast068
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open private sumGrade sumOld from ProximityPrize.SubmissionLower.PrimaryTaperColumns

/-- Jet exponents in a box with the linear taper. -/
def taperBox (B J T Θ : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e ≤ B ∧ Finsupp.weight oldWeight e ≤ J ∧ e 3 ≤ T ∧
    8*Finsupp.weight gradeWeight e+7*(e 1+e 2+e 3)≤Θ}

theorem taperBox_finite (B J T Θ : ℕ) : (taperBox B J T Θ).Finite :=
  (Finsupp.finite_of_nat_weight_le gradeWeight (fun j => by simp [gradeWeight]) B).subset
    (fun _ h => h.1)

theorem taperBox_mono {B J T Θ B' J' T' Θ' : ℕ} (hB : B ≤ B') (hJ : J ≤ J') (hT : T ≤ T')
    (hΘ:Θ≤Θ'):taperBox B J T Θ ⊆ taperBox B' J' T' Θ' :=
  fun _ h => ⟨h.1.trans hB,h.2.1.trans hJ,h.2.2.1.trans hT,h.2.2.2.trans hΘ⟩

/-- The largest non-`Y₀` degree allowed at grade `q`. -/
def padGrade (Θ q:ℕ):ℕ:=min q ((Θ - 8*q) / 7)

/-- The count at one grade. -/
def term (J T Θ q : ℕ) : ℤ :=
  if 8*q≤Θ then cappedCount (padGrade Θ q) J T else 0

/-- The exact number of exponents in `taperBox B J T Θ`. -/
def boxCount (B J T Θ:ℕ):ℤ := ∑ q ∈ range (B+1),term J T Θ q

private noncomputable def grid (B J T Θ : ℕ) : Finset (Σ _ : ℕ, JetExp) :=
  ((range (B+1)).filter fun q => 8*q≤Θ).sigma fun q => cappedColumns (padGrade Θ q) J T

private noncomputable def pad (Θ : ℕ) (x : Σ _ : ℕ, JetExp) : JetExp :=
  x.2+Finsupp.single 0 (x.1 - padGrade Θ x.1)

private theorem grid_mem {B J T Θ : ℕ} {q : ℕ} {m : JetExp} (hx : (⟨q, m⟩ : Σ _ : ℕ, JetExp) ∈ grid B J T Θ) :
    q ≤ B ∧ 8 * q ≤ Θ ∧ Finsupp.weight gradeWeight m = padGrade Θ q ∧
      Finsupp.weight oldWeight m≤J ∧ m 3≤T:=by
  obtain ⟨hq,hm⟩:=mem_sigma.mp hx
  obtain ⟨hr,hΘ⟩:=mem_filter.mp hq
  obtain ⟨hj,ht⟩:=mem_cappedColumns.mp hm
  obtain ⟨hg,hi⟩:=mem_cumulativeColumns.mp hj
  refine ⟨Nat.lt_succ_iff.mp (mem_range.mp hr),hΘ, ?_, ?_, ?_⟩
  · exact_mod_cast hg
  · exact_mod_cast hi
  · exact_mod_cast ht

private theorem pad_apply_zero (Θ q : ℕ) (m : JetExp) :
    pad Θ ⟨q,m⟩ 0=m 0+(q - padGrade Θ q):=by simp [pad]

private theorem pad_apply_ne (Θ q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) :
    pad Θ ⟨q,m⟩ i=m i:=by simp [pad,Finsupp.single_eq_of_ne hi]

private theorem pad_grade {B J T Θ : ℕ} {q : ℕ} {m : JetExp}
    (hx:(⟨q,m⟩:Σ _:ℕ,JetExp) ∈ grid B J T Θ) :
    Finsupp.weight gradeWeight (pad Θ ⟨q,m⟩)=q:=by
  obtain ⟨_,_,hg,_,_⟩:=grid_mem hx
  have hle:padGrade Θ q≤q:=min_le_left _ _
  rw [sumGrade, pad_apply_zero, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
    pad_apply_ne _ _ _ 3 (by decide)]
  rw [sumGrade] at hg
  omega

private theorem pad_mem {B J T Θ : ℕ} {x : Σ _ : ℕ, JetExp} (hx : x ∈ grid B J T Θ) :
    pad Θ x ∈ (taperBox_finite B J T Θ).toFinset:=by
  obtain ⟨q,m⟩:=x
  obtain ⟨hq,hΘ,hg,hi,ht⟩:=grid_mem hx
  have hgrade:=pad_grade hx
  have hdiv:(Θ - 8*q) / 7*7≤Θ - 8*q:=Nat.div_mul_le_self _ _
  have hpg:padGrade Θ q≤(Θ - 8*q) / 7:=min_le_right _ _
  apply (taperBox_finite B J T Θ).mem_toFinset.mpr
  refine ⟨hgrade.le.trans hq, ?_, ?_, ?_⟩
  · rw [sumOld, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
      pad_apply_ne _ _ _ 3 (by decide), ← sumOld]
    exact hi
  · rw [pad_apply_ne _ _ _ 3 (by decide)]
    exact ht
  · rw [hgrade, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
      pad_apply_ne _ _ _ 3 (by decide)]
    rw [sumGrade] at hg
    omega

private theorem pad_injOn (B J T Θ : ℕ) :
    Set.InjOn (pad Θ) (grid B J T Θ:Set (Σ _:ℕ,JetExp)):=by
  intro x hx y hy hxy
  obtain ⟨q,m⟩:=x
  obtain ⟨q', m'⟩:=y
  have eQ : q = q' :=
    (pad_grade hx).symm.trans ((congrArg (fun e : JetExp => Finsupp.weight gradeWeight e) hxy).trans
      (pad_grade hy))
  subst q'
  have em : m = m' := by
    apply add_right_cancel (b:=Finsupp.single (0:Fin 4) (q - padGrade Θ q))
    exact hxy
  subst m'
  rfl

private theorem pad_surj {B J T Θ : ℕ} {e : JetExp} (he : e ∈ taperBox B J T Θ) :
    ∃ x ∈ grid B J T Θ,pad Θ x=e:=by
  obtain ⟨hB,hJ,hT,hΘ⟩:=he
  set q:=Finsupp.weight gradeWeight e with hq
  have hsum:=sumGrade e
  have hold:=sumOld e
  have h26:8*q≤Θ:=le_trans (Nat.le_add_right _ _) hΘ
  have hd : e 1 + e 2 + e 3 ≤ padGrade Θ q := by
    apply le_min
    · omega
    · apply (Nat.le_div_iff_mul_le (by decide : 0 < 7)).mpr
      omega
  have hpq:padGrade Θ q≤q:=min_le_left _ _
  let m:JetExp:=e - Finsupp.single 0 (q - padGrade Θ q)
  have m0:m 0=e 0 - (q - padGrade Θ q):=by simp [m]
  have mi (i:Fin 4) (hi:i≠0):m i=e i:=by simp [m,Finsupp.single_eq_of_ne hi]
  have hmg : Finsupp.weight gradeWeight m = padGrade Θ q := by
    rw [sumGrade,m0,mi 1 (by decide),mi 2 (by decide),mi 3 (by decide)]
    omega
  have hmo : Finsupp.weight oldWeight m = Finsupp.weight oldWeight e := by
    rw [sumOld,sumOld,mi 1 (by decide),mi 2 (by decide),mi 3 (by decide)]
  refine ⟨⟨q,m⟩, ?_, ?_⟩
  · apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hB),h26⟩, ?_⟩
    apply mem_cappedColumns.mpr
    refine ⟨mem_cumulativeColumns.mpr ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hmg
    · rw [hmo]
      exact_mod_cast hJ
    · rw [mi 3 (by decide)]
      exact_mod_cast hT
  · ext i
    by_cases hi:i=0
    · subst hi
      rw [pad_apply_zero,m0]
      omega
    · rw [pad_apply_ne _ _ _ i hi,mi i hi]

/-- **Exact count.** -/
theorem taperBox_card (B J T Θ : ℕ) :
    (((taperBox_finite B J T Θ).toFinset.card:ℕ):ℤ)=boxCount B J T Θ:=by
  classical
  have himage : (taperBox_finite B J T Θ).toFinset = (grid B J T Θ).image (pad Θ) := by
    ext e
    constructor
    · intro he
      obtain ⟨x,hx,rfl⟩:=pad_surj ((taperBox_finite B J T Θ).mem_toFinset.mp he)
      exact mem_image_of_mem _ hx
    · intro he
      obtain ⟨x,hx,rfl⟩:=mem_image.mp he
      exact pad_mem hx
  rw [himage,card_image_of_injOn (pad_injOn B J T Θ)]
  unfold grid boxCount
  rw [card_sigma,Nat.cast_sum,sum_filter]
  refine sum_congr rfl fun q _ => ?_
  unfold term
  split
  · exact capped_card K1_13_2_2_2.proof _ _ _
  · rfl

open FadicGate (cappedCount_mono cappedCount_nonneg segLo segHi seg_bounds sum_div_block
  rCapped rCapped_cast rPrefix rPrefix_cast)

def highSeg (J Θ B k : ℕ) : ℤ :=
  let lo:=segLo 0 4 k
  let hi:=segHi 0 4 (B+1) k
  if 8*lo≤Θ then cappedCount (min hi ((Θ-8*lo)/7):ℕ) J 550 else 0

theorem term_le (J Θ B i : ℕ) (hi : i < B+1) :
    term J 550 Θ i≤highSeg J Θ B (i/4):=by
  have ⟨hl,hu⟩:=seg_bounds (base:=0) (h:=4) (m:=B+1) (by decide) hi
  simp only [Nat.zero_add] at hl hu
  unfold highSeg term padGrade
  dsimp only
  by_cases hc:8*i≤Θ
  · rw [if_pos hc, if_pos ((Nat.mul_le_mul_left 8 hl).trans hc)]
    exact cappedCount_mono (min_le_min hu (Nat.div_le_div_right (by omega))) (J:ℤ) 550
  · rw [if_neg hc]
    split
    · exact cappedCount_nonneg _ _ _
    · exact le_rfl

def rawSeg (J Θ B k : ℕ) : ℕ :=
  let lo:=segLo 0 4 k
  let hi:=segHi 0 4 (B+1) k
  if 8*lo≤Θ then rCapped (min hi ((Θ-8*lo)/7)) J 550 else 0

private theorem rawSeg_cast (J Θ B k : ℕ) :
    (rawSeg J Θ B k:ℤ)=highSeg J Θ B k:=by
  unfold rawSeg highSeg
  dsimp only
  by_cases hc:8*segLo 0 4 k≤Θ
  · rw [if_pos hc, if_pos hc]
    exact rCapped_cast _ _ 550
  · simp [hc]

def rawCount (B J Θ : ℕ) : ℕ :=
  4*rPrefix (rawSeg J Θ B) ((B+1)/4)+((B+1)%4)*rawSeg J Θ B ((B+1)/4)

theorem boxCount_toNat_le (B J Θ : ℕ) :
    (boxCount B J 550 Θ).toNat≤rawCount B J Θ:=by
  have h : boxCount B J 550 Θ ≤ (rawCount B J Θ : ℤ) := by
    unfold boxCount
    calc
      _ ≤ ∑ i ∈ range (B+1), highSeg J Θ B (i/4) :=
        sum_le_sum fun i hi => term_le J Θ B i (mem_range.mp hi)
      _ = _ := by
        rw [sum_div_block _ (by decide:0 < 4)]
        simp only [rawCount,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,rPrefix_cast,rawSeg_cast]
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat h

#print axioms taperBox_card
#print axioms boxCount_toNat_le
end H2428Weighted87Count
