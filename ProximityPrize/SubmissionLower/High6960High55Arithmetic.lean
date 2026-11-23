import ProximityPrize.SubmissionLower.HighCore82268TerminalArithmetic

set_option autoImplicit false

namespace High6960High55Arithmetic
open Finset
open K1_14 (Shape shapeSum slots triangle)
open scoped BigOperators
open private slots_anti rise_of_convex from ProximityPrize.SubmissionLower.UpperBranch6
open private surplus_convex run_sum from ProximityPrize.SubmissionLower.HighCore82268TerminalArithmetic

abbrev donor:ℕ:=179876
abbrev agreement:ℕ:=179827
abbrev Bank:=HighCore82268.Bank
abbrev debit:=HighCore82268.debit

def raw (A : ℕ) (s : Shape) (h q j t : ℕ) : ℕ :=
  s.m*A+j - q*(131071-h) - 2*h*t

def pairGain (A : ℕ) (s : Shape) (h E v q j : ℕ) : ℕ :=
  let g:=(q-j)/E
  let c:=fun a => slots s.U (a*v)
  (∑ a ∈ range g, (c a - c (a+1)) * raw A s h q j (j+a)) +
    c g*raw A s h q j (j+g)

def gain (A : ℕ) (s : Shape) (h E v : ℕ) : ℕ :=
  shapeSum s (pairGain A s h E v)

theorem donor_gain (s : Shape) (h E v : ℕ) :
    gain donor s h E v=HighCore82268.jointGain h s E v:=rfl

private theorem raw_loss (s : Shape) (h q j t : ℕ) :
    raw donor s h q j t≤raw agreement s h q j t+49*s.m:=by
  change s.m*179876+j-q*(131071-h)-2*h*t ≤
    s.m*179827+j-q*(131071-h)-2*h*t+49*s.m
  omega

private theorem weights_telescope (c : ℕ → ℕ) (hc : Antitone c) (g : ℕ) :
    (∑ a ∈ range g,(c a - c (a+1)))+c g=c 0:=by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [sum_range_succ]
    have h : c (g + 1) ≤ c g := hc (Nat.le_succ g)
    omega

private theorem pair_loss (s : Shape) (h E v q j : ℕ) :
    pairGain donor s h E v q j ≤
      pairGain agreement s h E v q j+triangle s.U*(49*s.m):=by
  let c:=fun a => slots s.U (a*v)
  let g:=(q-j)/E
  let R:=fun A a => raw A s h q j (j+a)
  let δ:=49*s.m
  have hc : Antitone c :=
    fun _ _ hab => slots_anti s.U (Nat.mul_le_mul_right v hab)
  have ht:=weights_telescope c hc g
  have hzero:c 0=triangle s.U:=by simp [c,slots]
  change (∑ a ∈ range g, (c a - c (a+1))*R donor a) + c g*R donor g ≤
    (∑ a ∈ range g, (c a - c (a+1))*R agreement a) +
      c g*R agreement g+triangle s.U*δ
  calc
    _ ≤ (∑ a ∈ range g, (c a - c (a+1))*(R agreement a+δ)) +
          c g*(R agreement g+δ):=by
      exact Nat.add_le_add
        (sum_le_sum fun a _ => Nat.mul_le_mul_left _ (raw_loss s h q j (j+a)))
        (Nat.mul_le_mul_left _ (raw_loss s h q j (j+g)))
    _ = _ := by
      simp only [Nat.mul_add,sum_add_distrib, ← sum_mul]
      rw [← hzero, ← ht]
      ring

def ambient (s : Shape) : ℕ :=
  s.J*(s.J-1)/2+s.J+(s.B+1-s.J)*(s.J+1)

private theorem shape_constant (s : Shape) (hs : s.J ≤ s.B) (c : ℕ) :
    shapeSum s (fun _ _ => c)=ambient s*c:=by
  unfold shapeSum
  simp only [sum_const,card_range,smul_eq_mul]
  rw [← sum_mul]
  have hsum:=sum_range_add (fun q => min q s.J+1) s.J (s.B+1-s.J)
  rw [Nat.add_sub_of_le (Nat.le_succ_of_le hs)] at hsum
  have hp : (∑ q ∈ range s.J, (min q s.J+1)) = s.J*(s.J-1)/2+s.J := by
    trans ∑ q ∈ range s.J,(q+1)
    · exact sum_congr rfl fun q hq => by
        rw [min_eq_left (Nat.le_of_lt (mem_range.mp hq))]
    · simp only [sum_add_distrib,sum_range_id,sum_const,card_range,smul_eq_mul,mul_one]
  have ht : (∑ q ∈ range (s.B+1-s.J), (min (s.J+q) s.J+1)) =
      (s.B+1-s.J)*(s.J+1):=by
    calc
      _ = ∑ q ∈ range (s.B+1-s.J), (s.J+1) := by
        exact sum_congr rfl fun q _ => by rw [min_eq_right (Nat.le_add_right s.J q)]
      _=_:=by simp [smul_eq_mul]
  simp only [hsum,hp,ht,ambient]

def discount (s:Shape):ℕ:=ambient s*(triangle s.U*(49*s.m))

theorem gain_loss (s : Shape) (hs : s.J ≤ s.B) (h E v : ℕ) :
    HighCore82268.jointGain h s E v≤gain agreement s h E v+discount s:=by
  rw [← donor_gain]
  unfold gain
  calc
    _ ≤ shapeSum s (fun q j => pairGain agreement s h E v q j + triangle s.U*(49*s.m)) := by
      unfold shapeSum
      exact sum_le_sum fun q _ => sum_le_sum fun j _ => pair_loss s h E v q j
    _ = _ := by
      have h :
          shapeSum s (fun q j => pairGain agreement s h E v q j + triangle s.U*(49*s.m)) =
            shapeSum s (pairGain agreement s h E v) +
              shapeSum s (fun _ _ => triangle s.U*(49*s.m)):=by
        simp only [shapeSum,sum_add_distrib]
      simp only [h,shape_constant s hs,discount]

private theorem affine_lower {f : ℕ → ℤ} {lo h : ℕ}
    (hl:lo≤h) (hc : ∀ n < h,f (n+1)+f (n+1)≤f n+f (n+2)) :
    f lo+((h:ℤ)-lo)*(f (lo+1)-f lo)≤f h:=by
  let D:=f (lo+1)-f lo
  let g:=fun n:ℕ => f n-(n:ℤ)*D
  have hconv : ∀ n < h, g (n+1)+g (n+1) ≤ g n+g (n+2) := by
    intro n hn
    have hc' := hc n hn
    simp only [g,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    linarith only [hc']
  have hstep : g lo ≤ g (lo+1) := by
    simp only [g,D,Nat.cast_add,Nat.cast_one]
    ring_nf <;> exact le_rfl
  have hh:=(rise_of_convex hconv hl hstep).1
  dsimp only [g,D] at hh
  linarith only [hh]

open HighCore82268TerminalArithmetic (surplus)

/-- Two old terminal receipts suffice to bound the same test throughout a new band. -/
theorem terminal_transfer {lo first h E v : ℕ} {b : Bank}
    (hj:b.shape.J≤b.shape.B)
    (hlo:lo≤first) (hfirst:first≤h) (hh:h < 131071)
    (hrise:surplus lo b E v≤surplus (lo+1) b E v)
    (hbudget : (discount b.shape : ℤ) <
      surplus lo b E v+((first:ℤ)-lo)*(surplus (lo+1) b E v-surplus lo b E v)) :
    debit h b < gain agreement b.shape h E v:=by
  have hloh:=hlo.trans hfirst
  have hconv : ∀ n < h,
      surplus (n+1) b E v+surplus (n+1) b E v≤surplus n b E v+surplus (n+2) b E v :=
    fun n hn => surplus_convex n b E v (by omega)
  have hlower:=affine_lower hloh hconv
  have hdelta:0≤surplus (lo+1) b E v-surplus lo b E v:=sub_nonneg.mpr hrise
  have hmul : ((first : ℤ)-lo)*(surplus (lo+1) b E v-surplus lo b E v) ≤
      ((h:ℤ)-lo)*(surplus (lo+1) b E v-surplus lo b E v) :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right (by exact_mod_cast hfirst) _) hdelta
  have hgt : (discount b.shape : ℤ) < surplus h b E v := by
    linarith only [hbudget,hlower,hmul]
  have hloss:=gain_loss b.shape hj h E v
  have hcast : (HighCore82268.jointGain h b.shape E v : ℤ) ≤
      (gain agreement b.shape h E v:ℤ)+discount b.shape:=by exact_mod_cast hloss
  unfold surplus at hgt
  have hstrict : (debit h b : ℤ) < gain agreement b.shape h E v := by
    linarith only [hgt,hcast]
  exact_mod_cast hstrict

open HighCore82268TerminalArithmetic
  (Parts runRow boundary orderEnd blockSurplus blockSurplus_eq scaledDebit phaseBlock)
open private scan_sum from ProximityPrize.SubmissionLower.PortHighBase

/-- Keep the two signed values that the original run receipt used for its comparisons. -/
theorem receipt_values {b : Bank} {lo E v n last count : ℕ} {left next cost costNext : ℤ}
    (parts:Parts (runRow b.shape lo E v n) last 0 count left next)
    (hn:b.shape.J+orderEnd b.shape E v=n) (hc:count≤b.shape.B+1)
    (hJ:b.shape.J < 2*lo)
    (hb:boundary b.shape lo n count=n)
    (hbNext:boundary b.shape (lo+1) n count=n)
    (hl:6*scaledDebit b.shape b.nodeRows b.poleMoment lo=cost)
    (hr:6*scaledDebit b.shape b.nodeRows b.poleMoment (lo+1)=costNext)
    (hlo:lo < 131071) (hwidth:b.shape.J≤131071-(lo+1)) (hE:0 < E) :
    1440*surplus lo b E v=left-cost ∧ 1440*surplus (lo+1) b E v=next-costNext:=by
  have hleft:=scan_sum (runRow b.shape lo E v n) 0 count false
  have hnext:=scan_sum (runRow b.shape lo E v n) 0 count true
  rw [parts.scan_eq] at hleft hnext
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add,runRow] at hleft hnext
  rw [run_sum b.shape lo E v n count hc hJ hb] at hleft
  rw [run_sum b.shape (lo+1) E v n count hc (by omega) hbNext] at hnext
  have hraw :
      6*blockSurplus b.shape b.nodeRows b.poleMoment lo E v=left-cost ∧
      6*blockSurplus b.shape b.nodeRows b.poleMoment (lo+1) E v=next-costNext:=by
    unfold blockSurplus
    rw [hn]
    omega
  rw [blockSurplus_eq b lo E v (by omega) (by omega) hE,
    blockSurplus_eq b (lo+1) E v (by omega) hwidth hE] at hraw
  exact ⟨by linarith only [hraw.1],by linarith only [hraw.2]⟩

theorem terminal_transfer_of_values {lo first h E v : ℕ} {b : Bank} {z z' : ℤ}
    (hj:b.shape.J≤b.shape.B) (hlo:lo≤first) (hfirst:first≤h) (hh:h < 131071)
    (hv:1440*surplus lo b E v=z ∧ 1440*surplus (lo+1) b E v=z')
    (hrise:z≤z')
    (hbudget:1440*(discount b.shape:ℤ) < z+((first:ℤ)-lo)*(z'-z)) :
    debit h b < gain agreement b.shape h E v:=by
  apply terminal_transfer hj hlo hfirst hh
  · linarith only [hv.1,hv.2,hrise]
  · have hstep : ((first : ℤ)-lo)*(z'-z) =
        1440*(((first:ℤ)-lo)*(surplus (lo+1) b E v-surplus lo b E v)):=by
      rw [← hv.1, ← hv.2]
      ring
    rw [hstep, ← hv.1] at hbudget
    linarith only [hbudget]

end High6960High55Arithmetic
