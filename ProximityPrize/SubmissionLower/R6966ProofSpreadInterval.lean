import ProximityPrize.SubmissionLower.R6966ProofSpreadGain
import ProximityPrize.SubmissionLower.R6966ProofSpreadWindow
import ProximityPrize.SubmissionLower.R6966ProofSpreadBucket
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowIntervals

set_option Elab.async false

namespace Research6966.SpreadInterval
open Finset
open K1_14 (Shape)
open K1_14_4 (gradeWidth)
open KoalaRect (area rectPower rectDebit)
open PadeCutoff (capacity)
open HelperWindowPrefix (volume)
open HelperWindowGrouping (sumCount sumCount_eq)
set_option maxHeartbeats 1100000

abbrev D : ℕ := 131071

def maxOrder (s : Shape) (e : ℕ) : ℕ := s.J+s.B/e+1

def upperCut (N h k : ℕ) : ℕ := N-2*h*(k-1)-1

def lowerBox (B N h k : ℕ) : ℕ := min B ((N-2*h*k)/(D-h))

def upperBox (B J N h k : ℕ) : ℕ := min B ((upperCut N h k+J)/(D-h))

def cost (s : Shape) (A e a n lo hi k : ℕ) : ℕ :=
  let N := s.m*A
  let B := upperBox s.B s.J N hi k
  let L := lowerBox s.B N lo k
  let W := SpreadWindow.boundary s.B s.J (D-hi) (upperCut N hi k)
  min (SpreadWindow.lex B s.J e k) (W-SpreadGain.lower L s.J a n k)

def costSum (s : Shape) (A e a n lo hi : ℕ) : ℕ :=
  sumCount (fun r => cost s A e a n lo hi (r+1)) (maxOrder s e)

def Positive (s : Shape) (A e a n nodes moment lo hi : ℕ) (U : Fin 2 → ℕ) : Prop :=
  let sums := costSum s A e a n lo hi
  rectDebit lo nodes moment U+area U*(2*lo)*sums < area U*volume (s.m*A) s.B s.J (D-lo) ∧
    rectDebit hi nodes moment U+area U*(2*hi)*sums < area U*volume (s.m*A) s.B s.J (D-hi)

instance (s : Shape) (A e a n nodes moment lo hi : ℕ) (U : Fin 2 → ℕ) :
    Decidable (Positive s A e a n nodes moment lo hi U) := by unfold Positive; infer_instance

private theorem payment_mono {q c lo hi : ℕ} (within : hi ≤ D) (step : lo ≤ hi) (rich : c ≤ q) :
    q*(D-hi)+hi*c ≤ q*(D-lo)+lo*c := by
  have equation : D-lo=(D-hi)+(hi-lo) := by omega
  have offset : hi*c=lo*c+(hi-lo)*c := by rw [← Nat.add_mul,Nat.add_sub_of_le step]
  have sparse : (hi-lo)*c ≤ q*(hi-lo) := by
    rw [Nat.mul_comm q]; exact Nat.mul_le_mul_left _ rich
  rw [equation,Nat.mul_add,offset]
  omega

private theorem payment_base {c h : ℕ} (ch : h≤D) : c*(D-h)+h*c=D*c := by
  rw [Nat.mul_comm h c,← Nat.mul_add,Nat.sub_add_cancel ch,Nat.mul_comm]

theorem cash_bound {N h hi W k q j : ℕ} (bound : 2*D*k<N)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<N)
    (weight : q*(D-h)≤W+j) :
    q*(D-hi)≤upperCut N hi k+j := by
  let r := 2*(k-1)
  have inside' : W+h*r<N := by dsimp only [r]; rwa [show h*(2*(k-1))=2*h*(k-1) by ring]
  have final : q*(D-hi)+hi*r<N+j := by
    by_cases big : r≤q
    · have bill := payment_mono high.le height big
      omega
    · have low : q≤r := by omega
      have step := Nat.mul_le_mul_right (D-hi) low
      have base := payment_base (c:=r) high.le
      have top : D*r<N := by
        have rail : D*r≤2*D*k := by
          rw [show 2*D*k=D*(2*k) by ring]
          exact Nat.mul_le_mul_left D (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
        exact rail.trans_lt bound
      omega
  unfold upperCut
  have cut : hi*r=2*hi*(k-1) := by dsimp [r];ring
  rw [cut] at final
  have hfit : 2*hi*(k-1)<N := by
    have p : 2*hi*(k-1) ≤ 2*D*k :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 high.le) (Nat.sub_le _ _)
    exact p.trans_lt bound
  omega

private theorem b_lower {B N lo h hi k : ℕ} (height : lo≤h) (right : h≤hi) (hiD : hi<D)
    (bound : 2*D*k<N) : lowerBox B N lo k≤lowerBox B N h k := by
  let t := (N-2*lo*k)/(D-lo)
  have lp : 0<D-lo := by omega
  have hp : 0<D-h := by omega
  have first : 2*k * (D-lo)+lo*(2*k)=2*D*k := by
    rw [payment_base (by omega : lo≤D)]
    ring
  have paid : t*(D-lo)≤N-2*lo*k := Nat.div_mul_le_self .. 
  have meaningful : 2*k≤t := by
    apply (Nat.le_div_iff_mul_le lp).mpr
    have equal : lo*(2*k)=2*lo*k := by ring
    omega
  have atLo : t*(D-lo)+lo*(2*k)≤N := by
    have fit : 2*lo*k≤N := (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 (by omega : lo≤D))).trans bound.le
    have equal : lo*(2*k)=2*lo*k := by ring
    omega
  have atH := (payment_mono (by omega : h≤D) height meaningful).trans atLo
  have ht : t≤(N-2*h*k)/(D-h) := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [show h*(2*k)=2*h*k by ring] at atH
    omega
  exact min_le_min le_rfl ht

theorem grade_upper {s : Shape} {A h hi W k : ℕ} (bound : 2*D*k<s.m*A)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<s.m*A) :
    ∀ j≤s.J, gradeWidth (D-h) s.B W j ≤ upperBox s.B s.J (s.m*A) hi k+1-j := by
  intro j hj
  let b := min s.B ((W+j)/(D-h))
  have hpos : 0<D-h := by omega
  have hipos : 0<D-hi := by omega
  have fit : b*(D-h)≤W+j := (Nat.le_div_iff_mul_le hpos).mp (min_le_right ..)
  have lease := (cash_bound bound high height inside fit).trans (Nat.add_le_add_left hj _)
  have qb : b≤upperBox s.B s.J (s.m*A) hi k :=
    le_min (min_le_left _ _) ((Nat.le_div_iff_mul_le hipos).mpr lease)
  unfold gradeWidth
  rw [show min (s.B+1) ((W+j)/(D-h)+1)=b+1 by dsimp only [b];omega]
  exact Nat.sub_le_sub_right (Nat.succ_le_succ qb) _

private theorem window_upper {s : Shape} {A h hi W k : ℕ} (bound : 2*D*k<s.m*A)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<s.m*A)
    (narrow : s.J<D-hi) :
    (PadeFiltered.physicalWindow s.B s.J (D-h) W).card ≤
      SpreadWindow.boundary s.B s.J (D-hi) (upperCut (s.m*A) hi k) := by
  have wp : 0<D-h := by omega
  have wip : 0<D-hi := by omega
  rw [SpreadWindow.boundary_eq _ _ _ _ narrow]
  apply card_le_card
  intro t mem
  obtain ⟨insideBox,fit⟩ := mem_filter.mp mem
  apply mem_filter.mpr
  refine ⟨insideBox, ?_⟩
  apply (SpreadWindow.weight_iff (D-hi) t.1 t.2 _ wip).mpr
  exact cash_bound bound high height inside
    ((SpreadWindow.weight_iff (D-h) t.1 t.2 W wp).mp fit)

private theorem cost_at {s : Shape} {A h e a n lo hi W : ℕ} (U : Fin 2 → ℕ)
    (hp : 0<h) (left : lo≤h) (right : h≤hi) (hiD : hi<D) (narrow : s.J<D-hi)
    (ap : 0<a) (ep : 0<e) (full : 2*D*maxOrder s e<s.m*A)
    (hw : W<s.m*A) (valid : rectPower A h s W≤maxOrder s e) :
    capacity A h e a n s U W ≤ area U*cost s A e a n lo hi (rectPower A h s W) := by
  let k := rectPower A h s W
  have kp : 0<k := (show 0<1 by decide).trans_le (Nat.le_add_right _ _)
  have money : 2*D*k<s.m*A := (Nat.mul_le_mul_left _ valid).trans_lt full
  have radius : W+2*h*(k-1)<s.m*A := by
    have guard := K1_14_4.power_threshold (s.m*A) (2*h) W 0 (k-1) hw (by omega)
    simp only [Nat.zero_add,Nat.sub_zero] at guard
    exact guard.mp (show k-1<k by omega)
  have b_le := b_lower left right hiD money (B:=s.B)
  have graph := SpreadGain.lower_le _ _ s.J a n k ap b_le
  have box := window_upper money hiD right radius narrow
  have wp : 0 < D-h := by omega
  have lexical := SpreadWindow.rect_lex A h e k W _ s U wp ep rfl
    (grade_upper money hiD right radius)
  let L := SpreadWindow.lex (upperBox s.B s.J (s.m*A) hi k) s.J e k
  let G := SpreadWindow.boundary s.B s.J (D-hi) (upperCut (s.m*A) hi k)-
    SpreadGain.lower (lowerBox s.B (s.m*A) lo k) s.J a n k
  change capacity A h e a n s U W≤area U*min L G
  have graphCap :
      ((PadeFiltered.physicalWindow s.B s.J (D-h) W).card-
        PadeRank.gain a n k (lowerBox s.B (s.m*A) h k+1) (s.J+1))*area U ≤ G*area U := by
    apply Nat.mul_le_mul_right
    exact (Nat.sub_le_sub_right box _).trans (Nat.sub_le_sub_left graph _)
  rcases le_total L G with le|le
  · rw [min_eq_left le,Nat.mul_comm]
    exact (min_le_left _ _).trans lexical
  · rw [min_eq_right le,Nat.mul_comm]
    exact (min_le_right _ _).trans graphCap

/-- Every group of constant Hasse order has a common capacity bound at
all heights in the interval. The initial and final scalar comparisons
therefore exclude the actual native graph at every such height. -/
theorem excluded {s : Shape} {A e a n nodes moment lo hi h : ℕ} {U : Fin 2 → ℕ}
    (lp : 0<lo) (left : lo≤h) (right : h≤hi) (hiD : hi<D) (narrow : s.J<D-hi)
    (ap : 0<a) (ep : 0<e) (wide : s.B*(D-lo)≤s.m*A) (full : 2*D*maxOrder s e<s.m*A)
    (cert : Positive s A e a n nodes moment lo hi U) :
    PadeCutoff.excluded A h e a n s U nodes moment := by
  have hp := lp.trans_le left
  have cap := SpreadBucket.sum_capacity (s:=s) (A:=A) (e:=e) (a:=a) (n:=n)
    (U:=U) (K:=maxOrder s e) hp (cost s A e a n lo hi)
    (fun W hw valid => cost_at U hp left right hiD narrow ap ep full hw valid)
    (by
      intro W _ far
      have wp : 0 < D-h := by omega
      have z := SpreadWindow.rect_zero A h e W s U wp ep far
      simp [capacity,z])
  have rlo : volume (s.m*A) s.B s.J (D-lo) = SpreadBucket.raw s A lo := by
    rw [HelperWindowPrefix.volume_eq_shapeSum s _ _ (narrow.trans_le (Nat.sub_le_sub_left (left.trans right) _))]
    simp only [SpreadBucket.raw,Nat.mul_comm (D-lo)]
  have rhi : volume (s.m*A) s.B s.J (D-hi) = SpreadBucket.raw s A hi := by
    rw [HelperWindowPrefix.volume_eq_shapeSum s _ _ narrow]
    simp only [SpreadBucket.raw,Nat.mul_comm (D-hi)]
  have fast : ∑ W ∈ range (s.m*A), capacity A h e a n s U W ≤ area U*(2*h)*costSum s A e a n lo hi := by
    simpa only [costSum,sumCount_eq] using cap
  exact SpreadBucket.excluded_of_endpoints left right hiD.le wide fast
    (cert.1.trans_eq (congrArg (area U*·) rlo)) (cert.2.trans_eq (congrArg (area U*·) rhi))

#print axioms excluded
end Research6966.SpreadInterval
