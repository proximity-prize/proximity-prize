import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960FreeSource
import ProximityPrize.SubmissionLower.R6960FreeSource6960

-- merged module R6960RescueSourceArithmetic
section Merged_R6960RescueSourceArithmetic
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.RescueSource
open Finset
open K1_14 (Shape slots)
open P1_7_6 (Quad intervalProduct intervalProduct_eq)
open P1_7_1_3 (evaluate evaluate_eq)
open HelperSource (column column_eq phaseLayer compressedPhase)
open K1_14_2_1 (twice_sum_linear)
def triangularWidth (C D L H U : ℕ) : ℤ :=
  intervalProduct (Quad.ofLines U (-1) (2*(C : ℤ)-D*((U : ℤ)-1)) (2-(D : ℤ)))
    ⟨1,0,0⟩ L (min H U)
private theorem twice_width_row (C D j U : ℕ) (hj : j≤U) :
    2*(∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) =
      ((U : ℤ)-j)*(2*C-D*((U : ℤ)-1)+(2-(D : ℤ))*j) := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.cast_add]
  have he (a : ℕ) : (C : ℤ)+j-D*((j : ℤ)+a) = ((C : ℤ)+j-D*(j : ℤ))+(-(D : ℤ))*a := by ring
  simp_rw [he, twice_sum_linear, Nat.cast_sub hj]
  ring
private theorem triangularWidth_eq (C D L H U : ℕ) :
    triangularWidth C D L H U =
      120*(∑ j ∈ Ico L H, ∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) := by
  unfold triangularWidth
  rw [← intervalProduct_eq]
  have hs : (Ico L (min H U)) ⊆ Ico L H := fun j hj =>
    mem_Ico.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.trans_le (min_le_left _ _)⟩
  rw [← sum_subset hs (f := fun j => ∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) (by
    intro j hj hnot
    have hU : U≤j := by
      simp only [mem_Ico, lt_min_iff] at hj hnot
      omega
    rw [Ico_eq_empty_of_le hU, sum_empty])]
  have hr :
      (∑ j ∈ Ico L (min H U),
        (Quad.ofLines U (-1) (2*(C : ℤ)-D*((U : ℤ)-1)) (2-(D : ℤ))).eval ↑j *
          (⟨1,0,0⟩ : Quad).eval ↑j) =
      ∑ j ∈ Ico L (min H U), 2*(∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) := by
    apply sum_congr rfl
    intro j hj
    have hu := (mem_Ico.mp hj).2.trans_le (min_le_right H U)
    rw [twice_width_row C D j U hu.le, Quad.eval_ofLines]
    simp [Quad.eval, sub_eq_add_neg]
  rw [hr, ← mul_sum]
  ring
private theorem division_split (C D j : ℕ) (hd : 0<D) (hj : j<D) :
    (C-1+j)/D =
      if j < D-(C-1)%D then (C-1)/D else (C-1)/D+1 := by
  let a := (C-1)/D
  let b := (C-1)%D
  have hb : b<D := Nat.mod_lt _ hd
  have he : b+D*a=C-1 := Nat.mod_add_div _ _
  change (C-1+j)/D = if j < D-b then a else a+1
  by_cases ht : j<D-b
  · rw [ite_eq_left ht]
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hd).2
      change C-1+j < (a+1)*D
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a D]
      omega
    · apply (Nat.le_div_iff_mul_le hd).2
      rw [Nat.mul_comm a D]
      omega
  · rw [ite_eq_right ht]
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hd).2
      change C-1+j < (a+2)*D
      rw [Nat.add_mul, Nat.mul_comm a D, Nat.two_mul]
      omega
    · apply (Nat.le_div_iff_mul_le hd).2
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a D]
      omega
private theorem clipped_column (C D j R : ℕ) (hc : 0<C) (hd : 0<D) :
    ((∑ q ∈ Ico j R, (C+j-q*D) : ℕ) : ℤ) =
      ∑ q ∈ Ico j (min R ((C-1+j)/D+1)), ((C : ℤ)+j-D*(q : ℤ)) := by
  have hs : Ico j (min R ((C-1+j)/D+1)) ⊆ Ico j R := fun q hq =>
    mem_Ico.mpr ⟨(mem_Ico.mp hq).1, (mem_Ico.mp hq).2.trans_le (min_le_left _ _)⟩
  have hw (q : ℕ) : q<(C-1+j)/D+1 ↔ q*D<C+j := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
    omega
  rw [← sum_subset hs (f := fun q => C+j-q*D) (by
    intro q hq hn
    have hless : ¬ q < (C-1+j)/D+1 := by
      intro h
      exact hn (mem_Ico.mpr ⟨(mem_Ico.mp hq).1, lt_min ((mem_Ico.mp hq).2) h⟩)
    exact Nat.sub_eq_zero_of_le (by have := mt (hw q).mpr hless; omega))]
  rw [Nat.cast_sum]
  apply sum_congr rfl
  intro q hq
  have hq' := (hw q).1 ((mem_Ico.mp hq).2.trans_le (min_le_right _ _))
  rw [Nat.cast_sub hq'.le]
  push_cast
  ring
private theorem sum_split (L H T : ℕ) (f : ℕ → ℤ) :
    (∑ j ∈ Ico L H, f j) =
      (∑ j ∈ Ico L (min H T), f j) + ∑ j ∈ Ico (max L T) H, f j := by
  have hl : (Ico L H).filter (· < T) = Ico L (min H T) := by
    ext j
    simp only [mem_filter, mem_Ico, lt_min_iff]
    tauto
  have hr : (Ico L H).filter (fun j => ¬ j < T) = Ico (max L T) H := by
    ext j
    simp only [mem_filter, mem_Ico, max_le_iff, not_lt]
    tauto
  rw [← hl, ← hr, sum_filter_add_sum_filter_not]
def layerWidth (C D L H R : ℕ) : ℤ :=
  let a := (C-1)/D+1
  let T := D-(C-1)%D
  triangularWidth C D L (min H T) (min R a) +
    triangularWidth C D (max L T) H (min R (a+1))
theorem layerWidth_eq (C D L H R : ℕ) (hc : 0<C) (hd : 0<D) (hH : H≤D) :
    layerWidth C D L H R =
      120*((∑ j ∈ Ico L H, ∑ q ∈ Ico j R, (C+j-q*D) : ℕ) : ℤ) := by
  unfold layerWidth
  simp only [triangularWidth_eq, Nat.cast_sum, clipped_column C D _ R hc hd, ← mul_add]
  congr 1
  let a := (C-1)/D+1
  let T := D-(C-1)%D
  rw [sum_split L H T]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    have ht : j<T := hj'.trans_le (min_le_right _ _)
    have hD : j<D := hj'.trans_le ((min_le_left _ _).trans hH)
    rw [division_split C D j hd hD, ite_eq_left ht]
  · apply sum_congr rfl
    intro j hj
    have ht : ¬ j<T := not_lt_of_ge ((le_max_right _ _).trans (mem_Ico.mp hj).1)
    have hD : j<D := (mem_Ico.mp hj).2.trans_le hH
    rw [division_split C D j hd hD, ite_eq_right ht]
def fastLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i+δ)*v) *
    ((layerWidth (s.m*A-2*h*(r+i)) (131071-h) ((i+δ)*d) (s.J+1) (s.B+1-(i+δ)*c)).toNat / 120)
theorem fastLayer_eq (s : Shape) (A h r d c v δ i : ℕ)
    (hJ : s.J<131071-h) (hi : 2*h*(r+i)<s.m*A) :
    fastLayer s A h r d c v δ i = phaseLayer s A h r d c v δ i := by
  unfold fastLayer phaseLayer
  rw [evaluate_eq, ← sum_Ico_eq_sum_range,
    layerWidth_eq _ _ _ _ _ (by omega) (by omega) (by omega)]
  have hc (n : ℕ) : (120*(n : ℤ)).toNat/120 = n := by
    have he : (120 : ℤ)*(n : ℤ) = ((120*n : ℕ) : ℤ) :=
      (Nat.cast_mul (α := ℤ) 120 n).symm
    rw [he, Int.toNat_natCast, Nat.mul_div_cancel_left _ (by decide)]
  rw [hc]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [column_eq]
  apply sum_congr rfl
  intro q _
  omega
def fastPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  evaluate (fastLayer s A h r d c v δ) (s.J/d+1)
theorem fastPhase_eq (s : Shape) (A h r d c v δ : ℕ)
    (hJ : s.J<131071-h) (hi : 2*h*(r+s.J/d)<s.m*A) :
    fastPhase s A h r d c v δ = compressedPhase s A h r d c v δ := by
  unfold fastPhase compressedPhase
  simp only [evaluate_eq]
  apply sum_congr rfl
  intro i hi'
  have hle : i≤s.J/d := Nat.le_of_lt_succ (mem_range.mp hi')
  exact fastLayer_eq s A h r d c v δ i hJ
    ((Nat.mul_le_mul_left (2*h) (Nat.add_le_add_left hle r)).trans_lt hi)
#print axioms fastPhase_eq
end Lower6960.RescueSource

end Merged_R6960RescueSourceArithmetic

-- merged module R6960RescueSource
section Merged_R6960RescueSource

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open P1_7 (Bank debit)
open P1_7_1_3 (evaluate evaluate_append)
open HelperSource (WidthGuard cutoffCount surplus)

def phaseBlock (f : ℕ→ℕ) (start len : ℕ) : ℕ :=
  evaluate (fun i => f (start+i)) len

theorem phaseBlock_append {f : ℕ→ℕ} {start next a b n x y z : ℕ}
    (ha : phaseBlock f start a=x) (hb : phaseBlock f next b=y)
    (hs : start+a=next) (hn : a+b=n) (hz : x+y=z) :
    phaseBlock f start n=z := by
  unfold phaseBlock at *
  rw [← hs] at hb
  exact evaluate_append ha (by simpa only [Nat.add_assoc] using hb) hn hz

theorem phase_of_block {s : K1_14.Shape} {A h r d c v δ n z : ℕ}
    (len : s.J/d+1=n) (block : phaseBlock (fastLayer s A h r d c v δ) 0 n=z) :
    fastPhase s A h r d c v δ=z := by
  unfold fastPhase
  rw [len]
  simpa only [phaseBlock, Nat.zero_add] using block

def fastSurplus (t : Bank) (h r c v : ℕ) : ℤ :=
  (fastPhase t.shape 179808 h r 1 c v 0 - fastPhase t.shape 179808 h r 1 c v 1 : ℕ) -
    (debit h t : ℤ)

theorem fastSurplus_eq (t : Bank) (h r c v : ℕ)
    (hJ : t.shape.J<131071-h) (hshift : 2*h*(r+t.shape.J)<t.shape.m*179808) :
    fastSurplus t h r c v = surplus t 179808 h r 1 c v := by
  unfold fastSurplus surplus
  rw [fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    HelperSource.gain_eq_compressed _ _ _ _ _ _ _ (by decide)]

structure Checked (t : Bank) (r c v : ℕ) : Prop where
  bank_ok : P3_7_1.BankOK t
  seed_ok : t.shape.U<K1.p
  reserve_ok : 2*r≤t.shape.B
  width_first : WidthGuard t 179808 2383 r
  first : 0<surplus t 179808 2383 r 1 c v
  next : surplus t 179808 2383 r 1 c v ≤ surplus t 179808 2384 r 1 c v

theorem checked_from_values (t : Bank) (r c v : ℕ) (hb : P3_7_1.BankOK t)
    (seed : t.shape.U<K1.p) (reserve : 2*r≤t.shape.B) (width : WidthGuard t 179808 2383 r)
    (slope : t.shape.J<131071-2384) (shift : 2*2384*(r+t.shape.J)<t.shape.m*179808)
    {a b x y : ℕ} (a0 : fastPhase t.shape 179808 2383 r 1 c v 0 = a)
    (a1 : fastPhase t.shape 179808 2383 r 1 c v 1 = b)
    (b0 : fastPhase t.shape 179808 2384 r 1 c v 0 = x)
    (b1 : fastPhase t.shape 179808 2384 r 1 c v 1 = y)
    (pos : 0<((a-b : ℕ) : ℤ)-(debit 2383 t : ℤ))
    (inc : ((a-b : ℕ) : ℤ)-(debit 2383 t : ℤ) ≤ ((x-y : ℕ) : ℤ)-(debit 2384 t : ℤ)) :
    Checked t r c v := by
  have h1 := fastSurplus_eq t 2383 r c v (by omega)
    ((Nat.mul_le_mul_right (r+t.shape.J) (by decide : 2*2383≤2*2384)).trans_lt shift)
  have h2 := fastSurplus_eq t 2384 r c v slope shift
  unfold fastSurplus at h1 h2
  rw [a0,a1] at h1
  rw [b0,b1] at h2
  refine ⟨hb,seed,reserve,width,?_,?_⟩
  · rwa [← h1]
  · rwa [← h1, ← h2]

def buffered (t : Bank) (h r : ℕ) : ℕ := cutoffCount t.shape 179808 h r-1

theorem Checked.width {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2383≤h) (hi : h≤33599) : WidthGuard t 179808 h r :=
  HelperSource.width_at_height t 179808 2383 h r lo (by omega) cert.reserve_ok cert.width_first

theorem Checked.cutoff_fit {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2383≤h) (hi : h≤33599) : buffered t h r+2*h*r<t.shape.m*179808 :=
  FreeSource.buffered_fit t 179808 h r (cert.width lo hi)

/-- Only the actual moving prime's lower degree bounds enter avoidance. -/
theorem Checked.avoids {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2383≤h) (hi : h≤33599) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 1≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (buffered t h r), ¬ G∣Q :=
  HelperSource.crt_avoiding_row Crt word t 179808 r 1 c v (by omega) (by omega) (by decide)
    cert.bank_ok.nodes cert.bank_ok.moment.1 cert.bank_ok.moment.2 cert.seed_ok
    (cert.width lo hi)
    (HelperSource.surplus_positive t 179808 2383 h r 1 c v lo (by omega) cert.first cert.next)
    irr seeded slope seed excess

#print axioms Checked.avoids

end Lower6960.RescueSource

end Merged_R6960RescueSource

-- merged module R6960RescueSourceSchedule
section Merged_R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

abbrev reserve := Lower6960.FreeSource.reserve

private def banks0 : List Bank :=
  [
    ⟨⟨900,1257,266,67442⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,76127⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,89004⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,111283⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,126942⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,108838⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1817,380,132537⟩,64827042824192,292013331876⟩,
    ⟨⟨1644,2285,480,142137⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,212053⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,159685⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,239531⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,326071⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4255,890,327412⟩,830225100570624,8759063388784⟩,
    ⟨⟨4281,5949,1250,393190⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,597484⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,648549⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,806579⟩,21862342000640000,675999454048899⟩
  ]

private def bank0 (i : Fin 17) : Bank := banks0.get ⟨i.val,i.isLt⟩

private def banks1 : List Bank :=
  [
    ⟨⟨900,1257,266,63949⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,72179⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,84433⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,105492⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,120520⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,103277⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1817,380,125841⟩,64827042824192,292013331876⟩,
    ⟨⟨1644,2285,480,134870⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,201192⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,151626⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,226270⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,308049⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4255,890,310905⟩,830225100570624,8759063388784⟩,
    ⟨⟨4281,5949,1250,373111⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,566976⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,615434⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,765394⟩,21862342000640000,675999454048899⟩
  ]

private def bank1 (i : Fin 17) : Bank := banks1.get ⟨i.val,i.isLt⟩

private def banks2 : List Bank :=
  [
    ⟨⟨900,1257,266,46655⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,52624⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,61757⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,76724⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,88589⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,75698⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1809,380,92866⟩,64827042824192,287901786632⟩,
    ⟨⟨1644,2285,480,98843⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,147246⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,111605⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,160507⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,218702⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4235,890,229594⟩,830225100570624,8627387690344⟩,
    ⟨⟨4281,5949,1250,273507⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,415662⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,451085⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,561149⟩,21862342000640000,675999454048899⟩
  ]

private def bank2 (i : Fin 17) : Bank := banks2.get ⟨i.val,i.isLt⟩

private def banks3 : List Bank :=
  [
    ⟨⟨650,907,192,24471⟩,8170644439040,18389221088⟩,
    ⟨⟨700,977,207,26982⟩,10208212418560,24758176234⟩,
    ⟨⟨750,1047,222,29525⟩,12559140782080,32653699308⟩,
    ⟨⟨800,1117,237,32096⟩,15245842841600,42302192650⟩,
    ⟨⟨998,1387,302,33334⟩,30044628975616,102461756220⟩,
    ⟨⟨1220,1696,370,36705⟩,54930349752320,229159736517⟩,
    ⟨⟨1302,1809,395,40914⟩,66768112975872,296724029248⟩,
    ⟨⟨1644,2285,498,48753⟩,134156626165760,753510622290⟩,
    ⟨⟨1927,2678,584,61701⟩,216034207334400,1421525065183⟩,
    ⟨⟨1505,2091,456,47729⟩,102969492373504,528831085877⟩,
    ⟨⟨1953,2726,570,74148⟩,218519657775104,1476869586813⟩,
    ⟨⟨2772,3870,809,103757⟩,624354479308800,5992280745484⟩,
    ⟨⟨3048,4235,924,96943⟩,854327964467200,8883701072242⟩,
    ⟨⟨4281,5949,1297,129168⟩,2364944629104640,34550690014738⟩,
    ⟨⟨6623,9203,2007,198583⟩,8754949968101376,197823002949183⟩,
    ⟨⟨6624,9204,2007,203831⟩,8757908515848192,197892215121891⟩,
    ⟨⟨9071,12604,2749,270589⟩,22490098892800000,695862530200649⟩
  ]

private def bank3 (i : Fin 17) : Bank := banks3.get ⟨i.val,i.isLt⟩

private def bankFamilies : List (Fin 17 → Bank) := [bank0,bank1,bank2,bank3]

def bank (rect : Fin 4) (i : Fin 17) : Bank := bankFamilies.get ⟨rect.val,rect.isLt⟩ i

def excess (rect : Fin 4) : ℕ := ([0,0,0,1] : List ℕ).get ⟨rect.val,rect.isLt⟩

def seed (rect : Fin 4) : ℕ := ([1,2,7,1] : List ℕ).get ⟨rect.val,rect.isLt⟩

def cutoff (h : ℕ) (rect : Fin 4) (i : Fin 17) : ℕ :=
  buffered (bank rect i) h (reserve i)

theorem shape_guards (rect : Fin 4) (i : Fin 17) :
    0<(bank rect i).shape.J ∧ (bank rect i).shape.J≤(bank rect i).shape.B ∧
      (bank rect i).shape.B<K1.p ∧ (bank rect i).shape.U<K1.p ∧
      (bank rect i).shape.m*179808<K1.p := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

end Lower6960.RescueSource

end Merged_R6960RescueSourceSchedule

-- merged module R6960RescueSourceReceipt0
section Merged_R6960RescueSourceReceipt0

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_907_192_part0 :
    blockEstimate 907 192 192 128 = 290411680 := by decide +kernel
private theorem moment_907_192_part1 :
    blockEstimate 907 192 320 128 = 1705328752 := by decide +kernel
private theorem moment_907_192_part2 :
    blockEstimate 907 192 448 128 = 3224576064 := by decide +kernel
private theorem moment_907_192_part3 :
    blockEstimate 907 192 576 128 = 3967672384 := by decide +kernel
private theorem moment_907_192_part4 :
    blockEstimate 907 192 704 128 = 3901268032 := by decide +kernel
private theorem moment_907_192_part5 :
    blockEstimate 907 192 832 128 = 3032779128 := by decide +kernel
private theorem moment_907_192_part6 :
    blockEstimate 907 192 960 128 = 1688215192 := by decide +kernel
private theorem moment_907_192_part7 :
    blockEstimate 907 192 1088 128 = 546427967 := by decide +kernel
private theorem moment_907_192_part8 :
    blockEstimate 907 192 1216 75 = 32541889 := by decide +kernel
private theorem moment_907_192_join0 :
    blockEstimate 907 192 192 256 = 1995740432 :=
  block_append moment_907_192_part0 moment_907_192_part1 rfl rfl rfl
private theorem moment_907_192_join1 :
    blockEstimate 907 192 448 256 = 7192248448 :=
  block_append moment_907_192_part2 moment_907_192_part3 rfl rfl rfl
private theorem moment_907_192_join2 :
    blockEstimate 907 192 192 512 = 9187988880 :=
  block_append moment_907_192_join0 moment_907_192_join1 rfl rfl rfl
private theorem moment_907_192_join3 :
    blockEstimate 907 192 704 256 = 6934047160 :=
  block_append moment_907_192_part4 moment_907_192_part5 rfl rfl rfl
private theorem moment_907_192_join4 :
    blockEstimate 907 192 1088 203 = 578969856 :=
  block_append moment_907_192_part7 moment_907_192_part8 rfl rfl rfl
private theorem moment_907_192_join5 :
    blockEstimate 907 192 960 331 = 2267185048 :=
  block_append moment_907_192_part6 moment_907_192_join4 rfl rfl rfl
private theorem moment_907_192_join6 :
    blockEstimate 907 192 704 587 = 9201232208 :=
  block_append moment_907_192_join3 moment_907_192_join5 rfl rfl rfl
private theorem moment_907_192_join7 :
    blockEstimate 907 192 192 1099 = 18389221088 :=
  block_append moment_907_192_join2 moment_907_192_join6 rfl rfl rfl

theorem moment_907_192 : momentEstimate 907 192 = 18389221088 := moment_907_192_join7

private theorem moment_1257_266_part0 :
    blockEstimate 1257 266 266 128 = 415627680 := by decide +kernel
private theorem moment_1257_266_part1 :
    blockEstimate 1257 266 394 128 = 2599438752 := by decide +kernel
private theorem moment_1257_266_part2 :
    blockEstimate 1257 266 522 128 = 5961006051 := by decide +kernel
private theorem moment_1257_266_part3 :
    blockEstimate 1257 266 650 128 = 8681797632 := by decide +kernel
private theorem moment_1257_266_part4 :
    blockEstimate 1257 266 778 128 = 10282874880 := by decide +kernel
private theorem moment_1257_266_part5 :
    blockEstimate 1257 266 906 128 = 10764072960 := by decide +kernel
private theorem moment_1257_266_part6 :
    blockEstimate 1257 266 1034 128 = 10125391872 := by decide +kernel
private theorem moment_1257_266_part7 :
    blockEstimate 1257 266 1162 128 = 8369214195 := by decide +kernel
private theorem moment_1257_266_part8 :
    blockEstimate 1257 266 1290 128 = 5801507064 := by decide +kernel
private theorem moment_1257_266_part9 :
    blockEstimate 1257 266 1418 128 = 3249804063 := by decide +kernel
private theorem moment_1257_266_part10 :
    blockEstimate 1257 266 1546 128 = 1234496544 := by decide +kernel
private theorem moment_1257_266_part11 :
    blockEstimate 1257 266 1674 115 = 158591749 := by decide +kernel
private theorem moment_1257_266_join0 :
    blockEstimate 1257 266 394 256 = 8560444803 :=
  block_append moment_1257_266_part1 moment_1257_266_part2 rfl rfl rfl
private theorem moment_1257_266_join1 :
    blockEstimate 1257 266 266 384 = 8976072483 :=
  block_append moment_1257_266_part0 moment_1257_266_join0 rfl rfl rfl
private theorem moment_1257_266_join2 :
    blockEstimate 1257 266 778 256 = 21046947840 :=
  block_append moment_1257_266_part4 moment_1257_266_part5 rfl rfl rfl
private theorem moment_1257_266_join3 :
    blockEstimate 1257 266 650 384 = 29728745472 :=
  block_append moment_1257_266_part3 moment_1257_266_join2 rfl rfl rfl
private theorem moment_1257_266_join4 :
    blockEstimate 1257 266 266 768 = 38704817955 :=
  block_append moment_1257_266_join1 moment_1257_266_join3 rfl rfl rfl
private theorem moment_1257_266_join5 :
    blockEstimate 1257 266 1162 256 = 14170721259 :=
  block_append moment_1257_266_part7 moment_1257_266_part8 rfl rfl rfl
private theorem moment_1257_266_join6 :
    blockEstimate 1257 266 1034 384 = 24296113131 :=
  block_append moment_1257_266_part6 moment_1257_266_join5 rfl rfl rfl
private theorem moment_1257_266_join7 :
    blockEstimate 1257 266 1546 243 = 1393088293 :=
  block_append moment_1257_266_part10 moment_1257_266_part11 rfl rfl rfl
private theorem moment_1257_266_join8 :
    blockEstimate 1257 266 1418 371 = 4642892356 :=
  block_append moment_1257_266_part9 moment_1257_266_join7 rfl rfl rfl
private theorem moment_1257_266_join9 :
    blockEstimate 1257 266 1034 755 = 28939005487 :=
  block_append moment_1257_266_join6 moment_1257_266_join8 rfl rfl rfl
private theorem moment_1257_266_join10 :
    blockEstimate 1257 266 266 1523 = 67643823442 :=
  block_append moment_1257_266_join4 moment_1257_266_join9 rfl rfl rfl

theorem moment_1257_266 : momentEstimate 1257 266 = 67643823442 := moment_1257_266_join10

private theorem receipt_0_0_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 0) 0 128 = 4574823181359651989335526 := by decide +kernel
private theorem receipt_0_0_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 0) 128 128 = 1499724916124336928289630 := by decide +kernel
private theorem receipt_0_0_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 0) 256 11 = 9313007218781531922085 := by decide +kernel
private theorem receipt_0_0_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 0) 128 139 = 1509037923343118460211715 :=
  phaseBlock_append receipt_0_0_2383_0_part1 receipt_0_0_2383_0_part2 rfl rfl rfl
private theorem receipt_0_0_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 0) 0 267 = 6083861104702770449547241 :=
  phaseBlock_append receipt_0_0_2383_0_part0 receipt_0_0_2383_0_join0 rfl rfl rfl

private theorem receipt_0_0_2383_0 : fastPhase (bank 0 0).shape 179808 2383 0 1 0 1 0 = 6083861104702770449547241 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2383_0_join1

private theorem receipt_0_0_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 1) 0 128 = 4548086974019124667340983 := by decide +kernel
private theorem receipt_0_0_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 1) 128 128 = 1478747480031420832213857 := by decide +kernel
private theorem receipt_0_0_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 1) 256 11 = 7755621507953989416576 := by decide +kernel
private theorem receipt_0_0_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 1) 128 139 = 1486503101539374821630433 :=
  phaseBlock_append receipt_0_0_2383_1_part1 receipt_0_0_2383_1_part2 rfl rfl rfl
private theorem receipt_0_0_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2383 0 1 0 1 1) 0 267 = 6034590075558499488971416 :=
  phaseBlock_append receipt_0_0_2383_1_part0 receipt_0_0_2383_1_join0 rfl rfl rfl

private theorem receipt_0_0_2383_1 : fastPhase (bank 0 0).shape 179808 2383 0 1 0 1 1 = 6034590075558499488971416 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2383_1_join1

private theorem receipt_0_0_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 0) 0 128 = 4574861638013577493012615 := by decide +kernel
private theorem receipt_0_0_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 0) 128 128 = 1499733692103348644215339 := by decide +kernel
private theorem receipt_0_0_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 0) 256 11 = 9313041915343288156826 := by decide +kernel
private theorem receipt_0_0_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 0) 128 139 = 1509046734018691932372165 :=
  phaseBlock_append receipt_0_0_2384_0_part1 receipt_0_0_2384_0_part2 rfl rfl rfl
private theorem receipt_0_0_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 0) 0 267 = 6083908372032269425384780 :=
  phaseBlock_append receipt_0_0_2384_0_part0 receipt_0_0_2384_0_join0 rfl rfl rfl

private theorem receipt_0_0_2384_0 : fastPhase (bank 0 0).shape 179808 2384 0 1 0 1 0 = 6083908372032269425384780 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2384_0_join1

private theorem receipt_0_0_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 1) 0 128 = 4548125244563828740135802 := by decide +kernel
private theorem receipt_0_0_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 1) 128 128 = 1478756151537949928816042 := by decide +kernel
private theorem receipt_0_0_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 1) 256 11 = 7755650515673432509426 := by decide +kernel
private theorem receipt_0_0_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 1) 128 139 = 1486511802053623361325468 :=
  phaseBlock_append receipt_0_0_2384_1_part1 receipt_0_0_2384_1_part2 rfl rfl rfl
private theorem receipt_0_0_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2384 0 1 0 1 1) 0 267 = 6034637046617452101461270 :=
  phaseBlock_append receipt_0_0_2384_1_part0 receipt_0_0_2384_1_join0 rfl rfl rfl

private theorem receipt_0_0_2384_1 : fastPhase (bank 0 0).shape 179808 2384 0 1 0 1 1 = 6034637046617452101461270 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2384_1_join1

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2383_0 receipt_0_0_2383_1 receipt_0_0_2384_0 receipt_0_0_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 0) 0 128 = 4105717548834872670676355 := by decide +kernel
private theorem receipt_1_0_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 0) 128 128 = 1340750563987928819139067 := by decide +kernel
private theorem receipt_1_0_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 0) 256 11 = 8301770322788164731322 := by decide +kernel
private theorem receipt_1_0_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 0) 128 139 = 1349052334310716983870389 :=
  phaseBlock_append receipt_1_0_2383_0_part1 receipt_1_0_2383_0_part2 rfl rfl rfl
private theorem receipt_1_0_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 0) 0 267 = 5454769883145589654546744 :=
  phaseBlock_append receipt_1_0_2383_0_part0 receipt_1_0_2383_0_join0 rfl rfl rfl

private theorem receipt_1_0_2383_0 : fastPhase (bank 1 0).shape 179808 2383 0 1 0 2 0 = 5454769883145589654546744 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2383_0_join1

private theorem receipt_1_0_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 1) 0 128 = 4081592739995854154076547 := by decide +kernel
private theorem receipt_1_0_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 1) 128 128 = 1321963187494167598206648 := by decide +kernel
private theorem receipt_1_0_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 1) 256 11 = 6913336913952541334658 := by decide +kernel
private theorem receipt_1_0_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 1) 128 139 = 1328876524408120139541306 :=
  phaseBlock_append receipt_1_0_2383_1_part1 receipt_1_0_2383_1_part2 rfl rfl rfl
private theorem receipt_1_0_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2383 0 1 0 2 1) 0 267 = 5410469264403974293617853 :=
  phaseBlock_append receipt_1_0_2383_1_part0 receipt_1_0_2383_1_join0 rfl rfl rfl

private theorem receipt_1_0_2383_1 : fastPhase (bank 1 0).shape 179808 2383 0 1 0 2 1 = 5410469264403974293617853 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2383_1_join1

private theorem receipt_1_0_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 0) 0 128 = 4105752065761381633742821 := by decide +kernel
private theorem receipt_1_0_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 0) 128 128 = 1340758410761563627583701 := by decide +kernel
private theorem receipt_1_0_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 0) 256 11 = 8301801251936909414126 := by decide +kernel
private theorem receipt_1_0_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 0) 128 139 = 1349060212013500536997827 :=
  phaseBlock_append receipt_1_0_2384_0_part1 receipt_1_0_2384_0_part2 rfl rfl rfl
private theorem receipt_1_0_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 0) 0 267 = 5454812277774882170740648 :=
  phaseBlock_append receipt_1_0_2384_0_part0 receipt_1_0_2384_0_join0 rfl rfl rfl

private theorem receipt_1_0_2384_0 : fastPhase (bank 1 0).shape 179808 2384 0 1 0 2 0 = 5454812277774882170740648 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2384_0_join1

private theorem receipt_1_0_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 1) 0 128 = 4081627088780413323899558 := by decide +kernel
private theorem receipt_1_0_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 1) 128 128 = 1321970940648842778690116 := by decide +kernel
private theorem receipt_1_0_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 1) 256 11 = 6913362771380898471823 := by decide +kernel
private theorem receipt_1_0_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 1) 128 139 = 1328884303420223677161939 :=
  phaseBlock_append receipt_1_0_2384_1_part1 receipt_1_0_2384_1_part2 rfl rfl rfl
private theorem receipt_1_0_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2384 0 1 0 2 1) 0 267 = 5410511392200637001061497 :=
  phaseBlock_append receipt_1_0_2384_1_part0 receipt_1_0_2384_1_join0 rfl rfl rfl

private theorem receipt_1_0_2384_1 : fastPhase (bank 1 0).shape 179808 2384 0 1 0 2 1 = 5410511392200637001061497 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2384_1_join1

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2383_0 receipt_1_0_2383_1 receipt_1_0_2384_0 receipt_1_0_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 0) 0 128 = 2156689797869150074731656 := by decide +kernel
private theorem receipt_2_0_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 0) 128 128 = 684597973864352619446164 := by decide +kernel
private theorem receipt_2_0_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 0) 256 11 = 4148689370338372882099 := by decide +kernel
private theorem receipt_2_0_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 0) 128 139 = 688746663234690992328263 :=
  phaseBlock_append receipt_2_0_2383_0_part1 receipt_2_0_2383_0_part2 rfl rfl rfl
private theorem receipt_2_0_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 0) 0 267 = 2845436461103841067059919 :=
  phaseBlock_append receipt_2_0_2383_0_part0 receipt_2_0_2383_0_join0 rfl rfl rfl

private theorem receipt_2_0_2383_0 : fastPhase (bank 2 0).shape 179808 2383 0 1 0 7 0 = 2845436461103841067059919 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2383_0_join1

private theorem receipt_2_0_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 1) 0 128 = 2143519934264760997377967 := by decide +kernel
private theorem receipt_2_0_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 1) 128 128 = 674878062948332951598303 := by decide +kernel
private theorem receipt_2_0_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 1) 256 11 = 3454264814301247374252 := by decide +kernel
private theorem receipt_2_0_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 1) 128 139 = 678332327762634198972555 :=
  phaseBlock_append receipt_2_0_2383_1_part1 receipt_2_0_2383_1_part2 rfl rfl rfl
private theorem receipt_2_0_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2383 0 1 0 7 1) 0 267 = 2821852262027395196350522 :=
  phaseBlock_append receipt_2_0_2383_1_part0 receipt_2_0_2383_1_join0 rfl rfl rfl

private theorem receipt_2_0_2383_1 : fastPhase (bank 2 0).shape 179808 2383 0 1 0 7 1 = 2821852262027395196350522 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2383_1_join1

private theorem receipt_2_0_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 0) 0 128 = 2156707943164882847859187 := by decide +kernel
private theorem receipt_2_0_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 0) 128 128 = 684601984519806173634091 := by decide +kernel
private theorem receipt_2_0_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 0) 256 11 = 4148704826932398851888 := by decide +kernel
private theorem receipt_2_0_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 0) 128 139 = 688750689346738572485979 :=
  phaseBlock_append receipt_2_0_2384_0_part1 receipt_2_0_2384_0_part2 rfl rfl rfl
private theorem receipt_2_0_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 0) 0 267 = 2845458632511621420345166 :=
  phaseBlock_append receipt_2_0_2384_0_part0 receipt_2_0_2384_0_join0 rfl rfl rfl

private theorem receipt_2_0_2384_0 : fastPhase (bank 2 0).shape 179808 2384 0 1 0 7 0 = 2845458632511621420345166 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2384_0_join1

private theorem receipt_2_0_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 1) 0 128 = 2143537986968927938771118 := by decide +kernel
private theorem receipt_2_0_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 1) 128 128 = 674882024966786260385954 := by decide +kernel
private theorem receipt_2_0_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 1) 256 11 = 3454277734165038594082 := by decide +kernel
private theorem receipt_2_0_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 1) 128 139 = 678336302700951298980036 :=
  phaseBlock_append receipt_2_0_2384_1_part1 receipt_2_0_2384_1_part2 rfl rfl rfl
private theorem receipt_2_0_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2384 0 1 0 7 1) 0 267 = 2821874289669879237751154 :=
  phaseBlock_append receipt_2_0_2384_1_part0 receipt_2_0_2384_1_join0 rfl rfl rfl

private theorem receipt_2_0_2384_1 : fastPhase (bank 2 0).shape 179808 2384 0 1 0 7 1 = 2821874289669879237751154 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2384_1_join1

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2383_0 receipt_2_0_2383_1 receipt_2_0_2384_0 receipt_2_0_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 0) 0 128 = 195076406283973666682272 := by decide +kernel
private theorem receipt_3_0_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 0) 128 65 = 21055840578718748287056 := by decide +kernel
private theorem receipt_3_0_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 0) 0 193 = 216132246862692414969328 :=
  phaseBlock_append receipt_3_0_2383_0_part0 receipt_3_0_2383_0_part1 rfl rfl rfl

private theorem receipt_3_0_2383_0 : fastPhase (bank 3 0).shape 179808 2383 0 1 1 1 0 = 216132246862692414969328 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2383_0_join0

private theorem receipt_3_0_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 1) 0 128 = 193293132998548131302688 := by decide +kernel
private theorem receipt_3_0_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 1) 128 65 = 20390209652210748123280 := by decide +kernel
private theorem receipt_3_0_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2383 0 1 1 1 1) 0 193 = 213683342650758879425968 :=
  phaseBlock_append receipt_3_0_2383_1_part0 receipt_3_0_2383_1_part1 rfl rfl rfl

private theorem receipt_3_0_2383_1 : fastPhase (bank 3 0).shape 179808 2383 0 1 1 1 1 = 213683342650758879425968 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2383_1_join0

private theorem receipt_3_0_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 0) 0 128 = 195077808297731058505120 := by decide +kernel
private theorem receipt_3_0_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 0) 128 65 = 21055902797897109948520 := by decide +kernel
private theorem receipt_3_0_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 0) 0 193 = 216133711095628168453640 :=
  phaseBlock_append receipt_3_0_2384_0_part0 receipt_3_0_2384_0_part1 rfl rfl rfl

private theorem receipt_3_0_2384_0 : fastPhase (bank 3 0).shape 179808 2384 0 1 1 1 0 = 216133711095628168453640 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2384_0_join0

private theorem receipt_3_0_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 1) 0 128 = 193294521285994644742944 := by decide +kernel
private theorem receipt_3_0_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 1) 128 65 = 20390270047499588061072 := by decide +kernel
private theorem receipt_3_0_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2384 0 1 1 1 1) 0 193 = 213684791333494232804016 :=
  phaseBlock_append receipt_3_0_2384_1_part0 receipt_3_0_2384_1_part1 rfl rfl rfl

private theorem receipt_3_0_2384_1 : fastPhase (bank 3 0).shape 179808 2384 0 1 1 1 1 = 213684791333494232804016 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2384_1_join0

theorem receipt_3_0 : Checked (bank 3 0) 0 1 1 := by
  refine checked_from_values (bank 3 0) 0 1 1
    (P3_7_1.checked (bank 3 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_907_192)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_0_2383_0 receipt_3_0_2383_1 receipt_3_0_2384_0 receipt_3_0_2384_1 (by decide +kernel) (by decide +kernel)

def group0_stage (i : Fin 1) : Fin 17 :=
  ⟨0+i.val, by have := i.isLt; omega⟩

theorem group0_checked (rect : Fin 4) (i : Fin 1) :
    Checked (bank rect (group0_stage i)) (reserve (group0_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_0
    · exact receipt_1_0
    · exact receipt_2_0
    · exact receipt_3_0

theorem group0_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group0_stage i)).shape
      (cutoff h rect (group0_stage i)), ¬ G∣Q :=
  (group0_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group0_avoids

end Lower6960.RescueSource

end Merged_R6960RescueSourceReceipt0
