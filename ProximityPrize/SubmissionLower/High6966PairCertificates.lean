import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960ChartImage
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.High6966WideHelper
set_option Elab.async false




set_option Elab.async false

namespace Lower6960.Pair6966
open Research6966.HelperWindowIntervals (cutoff bound positive)
open Research6966.HelperWindowPrefix (volume)
open Research6966.HelperAvoidance (debitAt triSlots)
open Lower6960.Wide6966Helper (bankAt)
open K1_14 (triangle shapeSum)
open Finset
structure Row where
  cap : ℕ
  degree : ℕ
  seed : ℕ
  wt : ℕ
def Row.shape (c:Row) := (bankAt c.cap).shape
def Row.span (c:Row) (lo hi:ℕ) : Prop :=
  let s:=c.shape
  triangle c.cap*1691195277312+hi*(2*(c.cap+1))*2213398351+
    bound s 179759 10 lo hi (c.degree+1) 2 (c.wt+128548) 57 (triSlots c.cap (c.seed+1)) <
    triangle c.cap*volume (cutoff s 179759 hi 10) s.B s.J (131071-lo)
instance (c:Row) (lo hi:ℕ) : Decidable (c.span lo hi) := by unfold Row.span; infer_instance
def Row.positive (c:Row) (h:ℕ) : Prop :=
  let s:=c.shape
  let N:=cutoff s 179759 h 10
  P1_7.debit h (bankAt c.cap) + ∑ W∈range N,
    debitAt s h N W (c.degree+1) 2 (c.wt+128548) (triSlots c.cap (c.seed+1)) <
    triangle c.cap*shapeSum s (fun q j=>N+j-q*(131071-h))
theorem Row.positive_of_span (c:Row) {lo hi h:ℕ} (hp:0<h) (hl:lo≤h) (hh:h≤hi)
    (ends:hi≤2522) (cert:c.span lo hi) : c.positive h := by
  have narrow : c.shape.J<131071-hi := by change 115<131071-hi; omega
  have tail : ∀ k>57,triSlots c.cap (c.seed+1) k=0 ∨ c.shape.B<k*(c.degree+1) ∨ c.shape.J<k*2 := by
    intro k hk
    exact Or.inr (Or.inr (by change 115<k*2;omega))
  have pay:=Research6966.HelperWindowIntervals.positive c.shape 179759 10 lo hi h (c.degree+1) 2 (c.wt+128548) 57
    (triangle c.cap) (2*(c.cap+1)) 1691195277312 2213398351 _ hp hl hh narrow tail cert
  unfold Row.positive P1_7.debit
  simpa only [bankAt,Row.shape,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using pay
def row0 : Row := ⟨8813,1,20,128548⟩
private theorem p0_0 : row0.span 2317 2370 := by decide +kernel
private theorem p0_1 : row0.span 2371 2522 := by decide +kernel
theorem ready0 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row0.positive h := by
  by_cases h0:h≤2370
  · exact Row.positive_of_span row0 (by omega) (by omega) h0 (by decide) p0_0
  exact Row.positive_of_span row0 (by omega) (by omega) hi (by decide) p0_1
def row1 : Row := ⟨8813,2,1,257097⟩
private theorem p1_0 : row1.span 2317 2317 := by decide +kernel
private theorem p1_1 : row1.span 2318 2320 := by decide +kernel
private theorem p1_2 : row1.span 2321 2330 := by decide +kernel
private theorem p1_3 : row1.span 2331 2362 := by decide +kernel
private theorem p1_4 : row1.span 2363 2466 := by decide +kernel
private theorem p1_5 : row1.span 2467 2522 := by decide +kernel
theorem ready1 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row1.positive h := by
  by_cases h0:h≤2317
  · exact Row.positive_of_span row1 (by omega) (by omega) h0 (by decide) p1_0
  by_cases h1:h≤2320
  · exact Row.positive_of_span row1 (by omega) (by omega) h1 (by decide) p1_1
  by_cases h2:h≤2330
  · exact Row.positive_of_span row1 (by omega) (by omega) h2 (by decide) p1_2
  by_cases h3:h≤2362
  · exact Row.positive_of_span row1 (by omega) (by omega) h3 (by decide) p1_3
  by_cases h4:h≤2466
  · exact Row.positive_of_span row1 (by omega) (by omega) h4 (by decide) p1_4
  exact Row.positive_of_span row1 (by omega) (by omega) hi (by decide) p1_5
def row2 : Row := ⟨8418,2,1,308303⟩
private theorem p2_0 : row2.span 2317 2317 := by decide +kernel
private theorem p2_1 : row2.span 2318 2320 := by decide +kernel
private theorem p2_2 : row2.span 2321 2329 := by decide +kernel
private theorem p2_3 : row2.span 2330 2358 := by decide +kernel
private theorem p2_4 : row2.span 2359 2452 := by decide +kernel
private theorem p2_5 : row2.span 2453 2522 := by decide +kernel
theorem ready2 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row2.positive h := by
  by_cases h0:h≤2317
  · exact Row.positive_of_span row2 (by omega) (by omega) h0 (by decide) p2_0
  by_cases h1:h≤2320
  · exact Row.positive_of_span row2 (by omega) (by omega) h1 (by decide) p2_1
  by_cases h2:h≤2329
  · exact Row.positive_of_span row2 (by omega) (by omega) h2 (by decide) p2_2
  by_cases h3:h≤2358
  · exact Row.positive_of_span row2 (by omega) (by omega) h3 (by decide) p2_3
  by_cases h4:h≤2452
  · exact Row.positive_of_span row2 (by omega) (by omega) h4 (by decide) p2_4
  exact Row.positive_of_span row2 (by omega) (by omega) hi (by decide) p2_5
def row3 : Row := ⟨8418,2,2,308232⟩
private theorem p3_0 : row3.span 2317 2322 := by decide +kernel
private theorem p3_1 : row3.span 2323 2342 := by decide +kernel
private theorem p3_2 : row3.span 2343 2406 := by decide +kernel
private theorem p3_3 : row3.span 2407 2522 := by decide +kernel
theorem ready3 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row3.positive h := by
  by_cases h0:h≤2322
  · exact Row.positive_of_span row3 (by omega) (by omega) h0 (by decide) p3_0
  by_cases h1:h≤2342
  · exact Row.positive_of_span row3 (by omega) (by omega) h1 (by decide) p3_1
  by_cases h2:h≤2406
  · exact Row.positive_of_span row3 (by omega) (by omega) h2 (by decide) p3_2
  exact Row.positive_of_span row3 (by omega) (by omega) hi (by decide) p3_3
def row4 : Row := ⟨8418,2,4,307568⟩
private theorem p4_0 : row4.span 2317 2333 := by decide +kernel
private theorem p4_1 : row4.span 2334 2389 := by decide +kernel
private theorem p4_2 : row4.span 2390 2522 := by decide +kernel
theorem ready4 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row4.positive h := by
  by_cases h0:h≤2333
  · exact Row.positive_of_span row4 (by omega) (by omega) h0 (by decide) p4_0
  by_cases h1:h≤2389
  · exact Row.positive_of_span row4 (by omega) (by omega) h1 (by decide) p4_1
  exact Row.positive_of_span row4 (by omega) (by omega) hi (by decide) p4_2
def row5 : Row := ⟨8418,2,9,305624⟩
private theorem p5_0 : row5.span 2317 2362 := by decide +kernel
private theorem p5_1 : row5.span 2363 2513 := by decide +kernel
private theorem p5_2 : row5.span 2514 2522 := by decide +kernel
theorem ready5 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row5.positive h := by
  by_cases h0:h≤2362
  · exact Row.positive_of_span row5 (by omega) (by omega) h0 (by decide) p5_0
  by_cases h1:h≤2513
  · exact Row.positive_of_span row5 (by omega) (by omega) h1 (by decide) p5_1
  exact Row.positive_of_span row5 (by omega) (by omega) hi (by decide) p5_2
def row6 : Row := ⟨8418,2,16,300794⟩
private theorem p6_0 : row6.span 2317 2401 := by decide +kernel
private theorem p6_1 : row6.span 2402 2522 := by decide +kernel
theorem ready6 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row6.positive h := by
  by_cases h0:h≤2401
  · exact Row.positive_of_span row6 (by omega) (by omega) h0 (by decide) p6_0
  exact Row.positive_of_span row6 (by omega) (by omega) hi (by decide) p6_1
def row7 : Row := ⟨8418,2,26,289021⟩
private theorem p7_0 : row7.span 2317 2455 := by decide +kernel
private theorem p7_1 : row7.span 2456 2522 := by decide +kernel
theorem ready7 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row7.positive h := by
  by_cases h0:h≤2455
  · exact Row.positive_of_span row7 (by omega) (by omega) h0 (by decide) p7_0
  exact Row.positive_of_span row7 (by omega) (by omega) hi (by decide) p7_1
def row8 : Row := ⟨8418,2,41,278153⟩
private theorem p8_0 : row8.span 2317 2522 := by decide +kernel
theorem ready8 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row8.positive h := by
  exact Row.positive_of_span row8 (by omega) (by omega) hi (by decide) p8_0
def row9 : Row := ⟨8418,2,51,257143⟩
private theorem p9_0 : row9.span 2317 2522 := by decide +kernel
theorem ready9 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row9.positive h := by
  exact Row.positive_of_span row9 (by omega) (by omega) hi (by decide) p9_0
def row10 : Row := ⟨8418,2,71,257143⟩
private theorem p10_0 : row10.span 2317 2522 := by decide +kernel
theorem ready10 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row10.positive h := by
  exact Row.positive_of_span row10 (by omega) (by omega) hi (by decide) p10_0
def row11 : Row := ⟨8418,3,1,385646⟩
private theorem p11_0 : row11.span 2317 2356 := by decide +kernel
private theorem p11_1 : row11.span 2357 2488 := by decide +kernel
private theorem p11_2 : row11.span 2489 2522 := by decide +kernel
theorem ready11 {h:ℕ} (lo:2317≤h) (hi:h≤2522) : row11.positive h := by
  by_cases h0:h≤2356
  · exact Row.positive_of_span row11 (by omega) (by omega) h0 (by decide) p11_0
  by_cases h1:h≤2488
  · exact Row.positive_of_span row11 (by omega) (by omega) h1 (by decide) p11_1
  exact Row.positive_of_span row11 (by omega) (by omega) hi (by decide) p11_2
def row : Fin 12 → Row := ![row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11]
theorem ready (i:Fin 12) {h:ℕ} (lo:2317≤h) (hi:h≤2522) : (row i).positive h := by
  fin_cases i
  · exact ready0 lo hi
  · exact ready1 lo hi
  · exact ready2 lo hi
  · exact ready3 lo hi
  · exact ready4 lo hi
  · exact ready5 lo hi
  · exact ready6 lo hi
  · exact ready7 lo hi
  · exact ready8 lo hi
  · exact ready9 lo hi
  · exact ready10 lo hi
  · exact ready11 lo hi
#print axioms ready
end Lower6960.Pair6966
