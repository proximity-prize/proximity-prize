import ProximityPrize.SubmissionLower.R6966ProofHelperKnownPrime
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate
import ProximityPrize.SubmissionLower.High6966WideHelper

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
  triangle c.cap*777085255680+hi*(2*(c.cap+1))*779461982+
    bound s 179769 10 lo hi (c.degree+1) 2 (c.wt+128571) 44 (triSlots c.cap (c.seed+1)) <
    triangle c.cap*volume (cutoff s 179769 hi 10) s.B s.J (131071-lo)
instance (c:Row) (lo hi:ℕ) : Decidable (c.span lo hi) := by unfold Row.span; infer_instance
def Row.positive (c:Row) (h:ℕ) : Prop :=
  let s:=c.shape
  let N:=cutoff s 179769 h 10
  P1_7.debit h (bankAt c.cap) + ∑ W∈range N,
    debitAt s h N W (c.degree+1) 2 (c.wt+128571) (triSlots c.cap (c.seed+1)) <
    triangle c.cap*shapeSum s (fun q j=>N+j-q*(131071-h))
theorem Row.positive_of_span (c:Row) {lo hi h:ℕ} (hp:0<h) (hl:lo≤h) (hh:h≤hi)
    (ends:hi≤2499) (cert:c.span lo hi) : c.positive h := by
  have narrow : c.shape.J<131071-hi := by change 89<131071-hi; omega
  have tail : ∀ k>44,triSlots c.cap (c.seed+1) k=0 ∨ c.shape.B<k*(c.degree+1) ∨ c.shape.J<k*2 := by
    intro k hk
    exact Or.inr (Or.inr (by change 89<k*2;omega))
  have pay:=Research6966.HelperWindowIntervals.positive c.shape 179769 10 lo hi h (c.degree+1) 2 (c.wt+128571) 44
    (triangle c.cap) (2*(c.cap+1)) 777085255680 779461982 _ hp hl hh narrow tail cert
  unfold Row.positive P1_7.debit
  simpa only [bankAt,Row.shape,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using pay
def row0 : Row := ⟨15000,1,20,128571⟩
private theorem p0_0 : row0.span 2330 2332 := by decide +kernel
private theorem p0_1 : row0.span 2333 2342 := by decide +kernel
private theorem p0_2 : row0.span 2343 2376 := by decide +kernel
private theorem p0_3 : row0.span 2377 2490 := by decide +kernel
private theorem p0_4 : row0.span 2491 2499 := by decide +kernel
theorem ready0 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row0.positive h := by
  by_cases h0:h≤2332
  · exact Row.positive_of_span row0 (by omega) (by omega) h0 (by decide) p0_0
  by_cases h1:h≤2342
  · exact Row.positive_of_span row0 (by omega) (by omega) h1 (by decide) p0_1
  by_cases h2:h≤2376
  · exact Row.positive_of_span row0 (by omega) (by omega) h2 (by decide) p0_2
  by_cases h3:h≤2490
  · exact Row.positive_of_span row0 (by omega) (by omega) h3 (by decide) p0_3
  exact Row.positive_of_span row0 (by omega) (by omega) hi (by decide) p0_4
def row1 : Row := ⟨15000,2,1,257143⟩
private theorem p1_0 : row1.span 2330 2341 := by decide +kernel
private theorem p1_1 : row1.span 2342 2382 := by decide +kernel
private theorem p1_2 : row1.span 2383 2499 := by decide +kernel
theorem ready1 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row1.positive h := by
  by_cases h0:h≤2341
  · exact Row.positive_of_span row1 (by omega) (by omega) h0 (by decide) p1_0
  by_cases h1:h≤2382
  · exact Row.positive_of_span row1 (by omega) (by omega) h1 (by decide) p1_1
  exact Row.positive_of_span row1 (by omega) (by omega) hi (by decide) p1_2
def row2 : Row := ⟨13200,2,1,308328⟩
private theorem p2_0 : row2.span 2330 2332 := by decide +kernel
private theorem p2_1 : row2.span 2333 2342 := by decide +kernel
private theorem p2_2 : row2.span 2343 2376 := by decide +kernel
private theorem p2_3 : row2.span 2377 2490 := by decide +kernel
private theorem p2_4 : row2.span 2491 2499 := by decide +kernel
theorem ready2 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row2.positive h := by
  by_cases h0:h≤2332
  · exact Row.positive_of_span row2 (by omega) (by omega) h0 (by decide) p2_0
  by_cases h1:h≤2342
  · exact Row.positive_of_span row2 (by omega) (by omega) h1 (by decide) p2_1
  by_cases h2:h≤2376
  · exact Row.positive_of_span row2 (by omega) (by omega) h2 (by decide) p2_2
  by_cases h3:h≤2490
  · exact Row.positive_of_span row2 (by omega) (by omega) h3 (by decide) p2_3
  exact Row.positive_of_span row2 (by omega) (by omega) hi (by decide) p2_4
def row3 : Row := ⟨13200,2,2,308232⟩
private theorem p3_0 : row3.span 2330 2335 := by decide +kernel
private theorem p3_1 : row3.span 2336 2356 := by decide +kernel
private theorem p3_2 : row3.span 2357 2426 := by decide +kernel
private theorem p3_3 : row3.span 2427 2499 := by decide +kernel
theorem ready3 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row3.positive h := by
  by_cases h0:h≤2335
  · exact Row.positive_of_span row3 (by omega) (by omega) h0 (by decide) p3_0
  by_cases h1:h≤2356
  · exact Row.positive_of_span row3 (by omega) (by omega) h1 (by decide) p3_1
  by_cases h2:h≤2426
  · exact Row.positive_of_span row3 (by omega) (by omega) h2 (by decide) p3_2
  exact Row.positive_of_span row3 (by omega) (by omega) hi (by decide) p3_3
def row4 : Row := ⟨13200,2,4,307568⟩
private theorem p4_0 : row4.span 2330 2341 := by decide +kernel
private theorem p4_1 : row4.span 2342 2382 := by decide +kernel
private theorem p4_2 : row4.span 2383 2499 := by decide +kernel
theorem ready4 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row4.positive h := by
  by_cases h0:h≤2341
  · exact Row.positive_of_span row4 (by omega) (by omega) h0 (by decide) p4_0
  by_cases h1:h≤2382
  · exact Row.positive_of_span row4 (by omega) (by omega) h1 (by decide) p4_1
  exact Row.positive_of_span row4 (by omega) (by omega) hi (by decide) p4_2
def row5 : Row := ⟨13200,2,9,305624⟩
private theorem p5_0 : row5.span 2330 2355 := by decide +kernel
private theorem p5_1 : row5.span 2356 2443 := by decide +kernel
private theorem p5_2 : row5.span 2444 2499 := by decide +kernel
theorem ready5 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row5.positive h := by
  by_cases h0:h≤2355
  · exact Row.positive_of_span row5 (by omega) (by omega) h0 (by decide) p5_0
  by_cases h1:h≤2443
  · exact Row.positive_of_span row5 (by omega) (by omega) h1 (by decide) p5_1
  exact Row.positive_of_span row5 (by omega) (by omega) hi (by decide) p5_2
def row6 : Row := ⟨13200,2,16,300794⟩
private theorem p6_0 : row6.span 2330 2374 := by decide +kernel
private theorem p6_1 : row6.span 2375 2499 := by decide +kernel
theorem ready6 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row6.positive h := by
  by_cases h0:h≤2374
  · exact Row.positive_of_span row6 (by omega) (by omega) h0 (by decide) p6_0
  exact Row.positive_of_span row6 (by omega) (by omega) hi (by decide) p6_1
def row7 : Row := ⟨13200,2,26,289021⟩
private theorem p7_0 : row7.span 2330 2400 := by decide +kernel
private theorem p7_1 : row7.span 2401 2499 := by decide +kernel
theorem ready7 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row7.positive h := by
  by_cases h0:h≤2400
  · exact Row.positive_of_span row7 (by omega) (by omega) h0 (by decide) p7_0
  exact Row.positive_of_span row7 (by omega) (by omega) hi (by decide) p7_1
def row8 : Row := ⟨13200,2,41,278153⟩
private theorem p8_0 : row8.span 2330 2442 := by decide +kernel
private theorem p8_1 : row8.span 2443 2499 := by decide +kernel
theorem ready8 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row8.positive h := by
  by_cases h0:h≤2442
  · exact Row.positive_of_span row8 (by omega) (by omega) h0 (by decide) p8_0
  exact Row.positive_of_span row8 (by omega) (by omega) hi (by decide) p8_1
def row9 : Row := ⟨13200,2,51,257143⟩
private theorem p9_0 : row9.span 2330 2469 := by decide +kernel
private theorem p9_1 : row9.span 2470 2499 := by decide +kernel
theorem ready9 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row9.positive h := by
  by_cases h0:h≤2469
  · exact Row.positive_of_span row9 (by omega) (by omega) h0 (by decide) p9_0
  exact Row.positive_of_span row9 (by omega) (by omega) hi (by decide) p9_1
def row10 : Row := ⟨13200,2,71,257143⟩
private theorem p10_0 : row10.span 2330 2499 := by decide +kernel
theorem ready10 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row10.positive h := by
  exact Row.positive_of_span row10 (by omega) (by omega) hi (by decide) p10_0
def row11 : Row := ⟨13200,3,1,385715⟩
private theorem p11_0 : row11.span 2330 2377 := by decide +kernel
private theorem p11_1 : row11.span 2378 2499 := by decide +kernel
theorem ready11 {h:ℕ} (lo:2330≤h) (hi:h≤2499) : row11.positive h := by
  by_cases h0:h≤2377
  · exact Row.positive_of_span row11 (by omega) (by omega) h0 (by decide) p11_0
  exact Row.positive_of_span row11 (by omega) (by omega) hi (by decide) p11_1
def row : Fin 12 → Row := ![row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11]
theorem ready (i:Fin 12) {h:ℕ} (lo:2330≤h) (hi:h≤2499) : (row i).positive h := by
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
end Lower6960.Pair6966
