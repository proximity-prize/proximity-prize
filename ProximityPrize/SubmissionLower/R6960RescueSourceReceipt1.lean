import ProximityPrize.SubmissionLower.Z6970CompactRankBlocks
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960FreeSource6960

set_option Elab.async false

-- merged module R6960RescueSourceReceipt0
section Merged_R6960RescueSourceReceipt0

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
  (fastPhase t.shape 179818 h r 1 c v 0 - fastPhase t.shape 179818 h r 1 c v 1 : ℕ) -
    (debit h t : ℤ)

theorem fastSurplus_eq (t : Bank) (h r c v : ℕ)
    (hJ : t.shape.J<131071-h) (hshift : 2*h*(r+t.shape.J)<t.shape.m*179818) :
    fastSurplus t h r c v = surplus t 179818 h r 1 c v := by
  unfold fastSurplus surplus
  rw [fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    HelperSource.gain_eq_compressed _ _ _ _ _ _ _ (by decide)]

structure Checked (t : Bank) (r c v : ℕ) : Prop where
  bank_ok : P3_7_1.BankOK t
  seed_ok : t.shape.U<K1.p
  reserve_ok : 2*r≤t.shape.B
  width_first : WidthGuard t 179818 2359 r
  first : 0<surplus t 179818 2359 r 1 c v
  next : surplus t 179818 2359 r 1 c v ≤ surplus t 179818 2360 r 1 c v

theorem checked_from_values (t : Bank) (r c v : ℕ) (hb : P3_7_1.BankOK t)
    (seed : t.shape.U<K1.p) (reserve : 2*r≤t.shape.B) (width : WidthGuard t 179818 2359 r)
    (slope : t.shape.J<131071-2360) (shift : 2*2360*(r+t.shape.J)<t.shape.m*179818)
    {a b x y : ℕ} (a0 : fastPhase t.shape 179818 2359 r 1 c v 0 = a)
    (a1 : fastPhase t.shape 179818 2359 r 1 c v 1 = b)
    (b0 : fastPhase t.shape 179818 2360 r 1 c v 0 = x)
    (b1 : fastPhase t.shape 179818 2360 r 1 c v 1 = y)
    (pos : 0<((a-b : ℕ) : ℤ)-(debit 2359 t : ℤ))
    (inc : ((a-b : ℕ) : ℤ)-(debit 2359 t : ℤ) ≤ ((x-y : ℕ) : ℤ)-(debit 2360 t : ℤ)) :
    Checked t r c v := by
  have h1 := fastSurplus_eq t 2359 r c v (by omega)
    ((Nat.mul_le_mul_right (r+t.shape.J) (by decide : 2*2359≤2*2360)).trans_lt shift)
  have h2 := fastSurplus_eq t 2360 r c v slope shift
  unfold fastSurplus at h1 h2
  rw [a0,a1] at h1
  rw [b0,b1] at h2
  refine ⟨hb,seed,reserve,width,?_,?_⟩
  · rwa [← h1]
  · rwa [← h1, ← h2]

def buffered (t : Bank) (h r : ℕ) : ℕ := cutoffCount t.shape 179818 h r-1

theorem Checked.width {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2359≤h) (hi : h≤33579) : WidthGuard t 179818 h r :=
  HelperSource.width_at_height t 179818 2359 h r lo (by omega) cert.reserve_ok cert.width_first

theorem Checked.cutoff_fit {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2359≤h) (hi : h≤33579) : buffered t h r+2*h*r<t.shape.m*179818 :=
  FreeSource.buffered_fit t 179818 h r (cert.width lo hi)

/-- Only the actual moving prime's lower degree bounds enter avoidance. -/
theorem Checked.avoids {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 1≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (buffered t h r), ¬ G∣Q :=
  HelperSource.crt_avoiding_row Crt word t 179818 r 1 c v (by omega) (by omega) (by decide)
    cert.bank_ok.nodes cert.bank_ok.moment.1 cert.bank_ok.moment.2 cert.seed_ok
    (cert.width lo hi)
    (HelperSource.surplus_positive t 179818 2359 h r 1 c v lo (by omega) cert.first cert.next)
    irr seeded slope seed excess

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
      (bank rect i).shape.m*179818<K1.p := by
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

theorem moment_907_192 : momentEstimate 907 192 = 18389221088 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 907 192) (start := 192)
    [
      (128,290411680), (128,1705328752), (128,3224576064), (128,3967672384), (128,3901268032),
      (128,3032779128), (128,1688215192), (128,546427967), (75,32541889)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1257_266 : momentEstimate 1257 266 = 67643823442 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1257 266) (start := 266)
    [
      (128,415627680), (128,2599438752), (128,5961006051), (128,8681797632), (128,10282874880),
      (128,10764072960), (128,10125391872), (128,8369214195), (128,5801507064), (128,3249804063),
      (128,1234496544), (115,158591749)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

private theorem receipt_0_0_2359_0 : fastPhase (bank 0 0).shape 179818 2359 0 1 0 1 0 = 6083513808890213983389710 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 0).shape 179818 2359 0 1 0 1 0) (start := 0)
      [
      (128,4574482928578234937401905), (128,1499717384194550763295090), (11,9313496117428282692715)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_0_2359_1 : fastPhase (bank 0 0).shape 179818 2359 0 1 0 1 1 = 6034243767922300586777083 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 0).shape 179818 2359 0 1 0 1 1) (start := 0)
      [
      (128,4547748052430614801419229), (128,1478739689166322366628403), (11,7756026325363418729451)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_0_2360_0 : fastPhase (bank 0 0).shape 179818 2360 0 1 0 1 0 = 6083561063400761895430415 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 0).shape 179818 2360 0 1 0 1 0) (start := 0)
      [
      (128,4574521374280425386474622), (128,1499726158340633296801470), (11,9313530779703212154323)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_0_2360_1 : fastPhase (bank 0 0).shape 179818 2360 0 1 0 1 1 = 6034290726240279911690214 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 0).shape 179818 2360 0 1 0 1 1) (start := 0)
      [
      (128,4547786312076072906133524), (128,1478748358862157641667099), (11,7756055302049363889591)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2359_0 receipt_0_0_2359_1 receipt_0_0_2360_0 receipt_0_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2359_0 : fastPhase (bank 1 0).shape 179818 2359 0 1 0 2 0 = 5454458094285322157665859 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 0).shape 179818 2359 0 1 0 2 0) (start := 0)
      [
      (128,4105412086646563950513933), (128,1340743801504935632885347), (11,8302206133822574266579)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_0_2359_1 : fastPhase (bank 1 0).shape 179818 2359 0 1 0 2 1 = 5410158374883212131388611 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 0).shape 179818 2359 0 1 0 2 1) (start := 0)
      [
      (128,4081288482773560244086273), (128,1321956194343683339544090), (11,6913697765968547758248)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_0_2360_0 : fastPhase (bank 1 0).shape 179818 2360 0 1 0 2 0 = 5454500477416080114645554 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 0).shape 179818 2360 0 1 0 2 0) (start := 0)
      [
      (128,4105446593743614683756607), (128,1340751646640060870709870), (11,8302237032404560179077)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_0_2360_1 : fastPhase (bank 1 0).shape 179818 2360 0 1 0 2 1 = 5410200491251586570018481 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 0).shape 179818 2360 0 1 0 2 1) (start := 0)
      [
      (128,4081322821776082979583225), (128,1321963945879772177866653), (11,6913723595731412568603)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2359_0 receipt_1_0_2359_1 receipt_1_0_2360_0 receipt_1_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2359_0 : fastPhase (bank 2 0).shape 179818 2359 0 1 0 7 0 = 2845272281986082077875128 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 0).shape 179818 2359 0 1 0 7 0) (start := 0)
      [
      (128,2156528963108692506472521), (128,684594411722011523098564), (11,4148907155378048304043)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_0_2359_1 : fastPhase (bank 2 0).shape 179818 2359 0 1 0 7 1 = 2821688603013920890913935 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 0).shape 179818 2359 0 1 0 7 1) (start := 0)
      [
      (128,2143359771772483794496225), (128,674874386130197821755453), (11,3454445111239274662257)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_0_2360_0 : fastPhase (bank 2 0).shape 179818 2360 0 1 0 7 0 = 2845294447376338889407043 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 0).shape 179818 2360 0 1 0 7 0) (start := 0)
      [
      (128,2156547103238348699166276), (128,684598421541304287776250), (11,4148922596685902464517)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_0_2360_1 : fastPhase (bank 2 0).shape 179818 2360 0 1 0 7 1 = 2821710624676792232246766 :=
  phase_of_block (n := 267) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 0).shape 179818 2360 0 1 0 7 1) (start := 0)
      [
      (128,2143377819336688390570404), (128,674878347322832612203605), (11,3454458017271229472757)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2359_0 receipt_2_0_2359_1 receipt_2_0_2360_0 receipt_2_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2359_0 : fastPhase (bank 3 0).shape 179818 2359 0 1 1 1 0 = 216123068822634589257840 :=
  phase_of_block (n := 193) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 0).shape 179818 2359 0 1 1 1 0) (start := 0)
      [
      (128,195066296290084298229920), (65,21056772532550291027920)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_0_2359_1 : fastPhase (bank 3 0).shape 179818 2359 0 1 1 1 1 = 213674232777911987552816 :=
  phase_of_block (n := 193) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 0).shape 179818 2359 0 1 1 1 1) (start := 0)
      [
      (128,193283125021467888320544), (65,20391107756444099232272)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_0_2360_0 : fastPhase (bank 3 0).shape 179818 2360 0 1 1 1 0 = 216124533055570342742152 :=
  phase_of_block (n := 193) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 0).shape 179818 2360 0 1 1 1 0) (start := 0)
      [
      (128,195067698303841690052768), (65,21056834751728652689384)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_0_2360_1 : fastPhase (bank 3 0).shape 179818 2360 0 1 1 1 1 = 213675681460647340930864 :=
  phase_of_block (n := 193) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 0).shape 179818 2360 0 1 1 1 1) (start := 0)
      [
      (128,193284513308914401760800), (65,20391168151732939170064)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_0 : Checked (bank 3 0) 0 1 1 := by
  refine checked_from_values (bank 3 0) 0 1 1
    (P3_7_1.checked (bank 3 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_907_192)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_0_2359_0 receipt_3_0_2359_1 receipt_3_0_2360_0 receipt_3_0_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group0_stage i)).shape
      (cutoff h rect (group0_stage i)), ¬ G∣Q :=
  (group0_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

end Lower6960.RescueSource

end Merged_R6960RescueSourceReceipt0

end Merged_R6960RescueSourceReceipt0

-- merged module R6960RescueSourceReceipt1
section Merged_R6960RescueSourceReceipt1

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

theorem moment_977_207 : momentEstimate 977 207 = 24758176234 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 977 207) (start := 207)
    [
      (128,315454880), (128,1893094372), (128,3762297344), (128,4827257344), (128,5019802112),
      (128,4339931648), (128,2905553180), (128,1377948994), (128,313825184), (32,3011176)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1047_222 : momentEstimate 1047 222 = 32653699308 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1047 222) (start := 222)
    [
      (128,340498080), (128,2075230592), (128,4311457024), (128,5736373504), (128,6225960192),
      (128,5780217088), (128,4419886184), (128,2600283532), (128,1026138287), (117,137654825)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1117_237 : momentEstimate 1117 237 = 42302192650 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1117 237) (start := 237)
    [
      (128,365541280), (128,2252469787), (128,4866007104), (128,6688972864), (128,7513694272),
      (128,7340171328), (128,6168649768), (128,4198892547), (128,2189402175), (128,679563600),
      (74,38827925)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1326_281 : momentEstimate 1326 281 = 83828003187 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1326 281) (start := 281)
    [
      (128,440313120), (128,2769958176), (128,6492999306), (128,9717503424), (128,11761980864),
      (128,12623664576), (128,12302554560), (128,10798650816), (128,8203180395), (128,5254501290),
      (128,2634292110), (128,787344864), (71,41059686)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1327_281 : momentEstimate 1327 281 = 84031339757 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1327 281) (start := 281)
    [
      (128,440670880), (128,2772429472), (128,6499499186), (128,9728620992), (128,11777718720),
      (128,12644022720), (128,12327532992), (128,10828249536), (128,8234870103), (128,5281874916),
      (128,2654626290), (128,798423904), (72,42800046)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1341_282 : momentEstimate 1341 282 = 87154749585 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1341 282) (start := 282)
    [
      (128,445679520), (128,2807027616), (128,6595706731), (128,9903134464), (128,12026730240),
      (128,12963337984), (128,12712957696), (128,11275589376), (128,8711118963), (128,5697061300),
      (128,2967083923), (128,974195776), (87,75125996)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1387_302 : momentEstimate 1387 302 = 102461756220 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1387 302) (start := 302)
    [
      (128,462136480), (128,2920707232), (128,6982836384), (128,10787226624), (128,13338903552),
      (128,14619706368), (128,14629635072), (128,13368689664), (128,10858832125), (128,7630480965),
      (128,4503008202), (128,1955193296), (128,402271696), (25,2128560)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem moment_1392_291 : momentEstimate 1392 291 = 100699468110 :=
  CompactRank6970.from_blocks (f := P1_7_1_3.offsetEstimate 1392 291) (start := 291)
    [
      (128,463925280), (128,2933063712), (128,6972032551), (128,10645366912), (128,13102016640),
      (128,14333929600), (128,14341105792), (128,13123545216), (128,10691106230), (128,7487810802),
      (128,4379387141), (128,1864956928), (128,360231936), (19,989370)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel)

private theorem receipt_0_1_2359_0 : fastPhase (bank 0 1).shape 179818 2359 1 1 0 1 0 = 9630041052607449243566952 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) (start := 0)
      [
      (128,6989556470554152313187762), (128,2569453358232007299224508), (26,71031223821289631154682)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_1_2359_1 : fastPhase (bank 0 1).shape 179818 2359 1 1 0 1 1 = 9556188074924366487844704 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) (start := 0)
      [
      (128,6951392110925555682999894), (128,2539068053159057657481840), (26,65727910839753147362970)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_1_2360_0 : fastPhase (bank 0 1).shape 179818 2360 1 1 0 1 0 = 9630115593855094601061475 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) (start := 0)
      [
      (128,6989615393361176373693772), (128,2569468697750383108115600), (26,71031502743535119252103)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_1_2360_1 : fastPhase (bank 0 1).shape 179818 2360 1 1 0 1 1 = 9556262174263828951027799 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) (start := 0)
      [
      (128,6951450767402923269798494), (128,2539083237026679457810724), (26,65728169834226223418581)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2359_0 receipt_0_1_2359_1 receipt_0_1_2360_0 receipt_0_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2359_0 : fastPhase (bank 1 1).shape 179818 2359 1 1 0 2 0 = 8634562712494634148136069 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) (start := 0)
      [
      (128,6273149874890332774876773), (128,2298050520603025514484402), (26,63362317001275858774894)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_1_2359_1 : fastPhase (bank 1 1).shape 179818 2359 1 1 0 2 1 = 8568169612977548360271997 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) (start := 0)
      [
      (128,6238720230268266661564996), (128,2270818961800344647620431), (26,58630420908937051086570)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_1_2360_0 : fastPhase (bank 1 1).shape 179818 2360 1 1 0 2 0 = 8634629570336281279258705 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) (start := 0)
      [
      (128,6273202762990029977365852), (128,2298064241534916172134870), (26,63362565811335129757983)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_1_2360_1 : fastPhase (bank 1 1).shape 179818 2360 1 1 0 2 1 = 8568236072917162742300922 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) (start := 0)
      [
      (128,6238772877817258354497015), (128,2270832543161982016441378), (26,58630651937922371362529)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2359_0 receipt_1_1_2359_1 receipt_1_1_2360_0 receipt_1_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2359_0 : fastPhase (bank 2 1).shape 179818 2359 1 1 0 7 0 = 4503863838941338244778664 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) (start := 0)
      [
      (128,3295365720445289968729833), (128,1176679356610874884915077), (26,31818761885173391133754)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_1_2359_1 : fastPhase (bank 2 1).shape 179818 2359 1 1 0 7 1 = 4468566237615262605586582 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) (start := 0)
      [
      (128,3276602951785875525195781), (128,1162525085081616677356446), (26,29438200747770403034355)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_1_2360_0 : fastPhase (bank 2 1).shape 179818 2360 1 1 0 7 0 = 4503898796496702043112980 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) (start := 0)
      [
      (128,3295393521141176667007117), (128,1176686388518480657468175), (26,31818886837044718637688)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_1_2360_1 : fastPhase (bank 2 1).shape 179818 2360 1 1 0 7 1 = 4468600981224495458999817 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) (start := 0)
      [
      (128,3276630620310554930884440), (128,1162532044161480271343428), (26,29438316752460256771949)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2359_0 receipt_2_1_2359_1 receipt_2_1_2360_0 receipt_2_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2359_0 : fastPhase (bank 3 1).shape 179818 2359 1 1 1 1 0 = 353655276104630608184076 :=
  phase_of_block (n := 208) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 0) (start := 0)
      [
      (128,308235561449937969831648), (80,45419714654692638352428)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_1_2359_1 : fastPhase (bank 3 1).shape 179818 2359 1 1 1 1 1 = 349935777080447830839996 :=
  phase_of_block (n := 208) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 1) (start := 0)
      [
      (128,305691935680484873975904), (80,44243841399962956864092)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_1_2360_0 : fastPhase (bank 3 1).shape 179818 2360 1 1 1 1 0 = 353657661009444585093300 :=
  phase_of_block (n := 208) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 0) (start := 0)
      [
      (128,308237801832621057127200), (80,45419859176823527966100)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_1_2360_1 : fastPhase (bank 3 1).shape 179818 2360 1 1 1 1 1 = 349938138490303142086164 :=
  phase_of_block (n := 208) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 1) (start := 0)
      [
      (128,305694156027453311414304), (80,44243982462849830671860)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2359_0 receipt_3_1_2359_1 receipt_3_1_2360_0 receipt_3_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2359_0 : fastPhase (bank 0 2).shape 179818 2359 2 1 0 1 0 = 13735995035288070815613627 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) (start := 0)
      [
      (128,9940485494045992698716960), (128,3686750391603879716358841),
      (27,108759149638198400537826)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_2_2359_1 : fastPhase (bank 0 2).shape 179818 2359 2 1 0 1 1 = 13631174883727371983503788 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) (start := 0)
      [
      (128,9886599975618448504911840), (128,3643646926273448063304909),
      (27,100927981835475415287039)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_2_2360_0 : fastPhase (bank 0 2).shape 179818 2360 2 1 0 1 0 = 13736100343552555515413778 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) (start := 0)
      [
      (128,9940568359606589947290720), (128,3686772402412006693291662),
      (27,108759581533958874831396)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_2_2360_1 : fastPhase (bank 0 2).shape 179818 2360 2 1 0 1 1 = 13631279568092119076642662 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) (start := 0)
      [
      (128,9886682468488037008368480), (128,3643668715614093731360721),
      (27,100928383989988336913461)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2359_0 receipt_0_2_2359_1 receipt_0_2_2360_0 receipt_0_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2359_0 : fastPhase (bank 1 2).shape 179818 2359 2 1 0 2 0 = 12333723414899549515762197 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) (start := 0)
      [
      (128,8933205445991058848594400), (128,3303288777072867313637731), (27,97229191835623353530066)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_2_2359_1 : fastPhase (bank 1 2).shape 179818 2359 2 1 0 2 1 = 12239391385803929730885286 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) (start := 0)
      [
      (128,8884564830069180295307104), (128,3264599839682703193085127), (27,90226716052046242493055)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_2_2360_0 : fastPhase (bank 1 2).shape 179818 2360 2 1 0 2 0 = 12333817998620620531254778 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) (start := 0)
      [
      (128,8933279920146598458304800), (128,3303308500527085206210642), (27,97229577946936866739336)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_2_2360_1 : fastPhase (bank 1 2).shape 179818 2360 2 1 0 2 1 = 12239485407303003016325277 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) (start := 0)
      [
      (128,8884638967472443593066720), (128,3264619364261856969339978), (27,90227075568702453918579)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2359_0 receipt_1_2_2359_1 receipt_1_2_2360_0 receipt_1_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2359_0 : fastPhase (bank 2 2).shape 179818 2359 2 1 0 7 0 = 6492821146593186459260925 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) (start := 0)
      [
      (128,4731370394192367036278304), (128,1711887346130013048172219), (27,49563406270806374810402)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_2_2359_1 : fastPhase (bank 2 2).shape 179818 2359 2 1 0 7 1 = 6442346711393495526558154 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) (start := 0)
      [
      (128,4704782399618221053563488), (128,1691576208554396431753101), (27,45988103220878041241565)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_2_2360_0 : fastPhase (bank 2 2).shape 179818 2360 2 1 0 7 0 = 6492871037755978604946040 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) (start := 0)
      [
      (128,4731409859476842104467104), (128,1711897575175709321443338), (27,49563603103427179035598)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_2_2360_1 : fastPhase (bank 2 2).shape 179818 2360 2 1 0 7 1 = 6442396298863998305923746 :=
  phase_of_block (n := 283) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) (start := 0)
      [
      (128,4704821679538491044789280), (128,1691586332852969076824997), (27,45988286472538184309469)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2359_0 receipt_2_2_2359_1 receipt_2_2_2360_0 receipt_2_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2359_0 : fastPhase (bank 3 2).shape 179818 2359 2 1 1 1 0 = 558368513191187748771512 :=
  phase_of_block (n := 223) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 0) (start := 0)
      [
      (128,469547617856445800596512), (95,88820895334741948175000)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_2_2359_1 : fastPhase (bank 3 2).shape 179818 2359 2 1 1 1 1 = 552889345626826915416241 :=
  phase_of_block (n := 223) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 1) (start := 0)
      [
      (128,466016763621493559639200), (95,86872582005333355777041)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_2_2360_0 : fastPhase (bank 3 2).shape 179818 2360 2 1 1 1 0 = 558372263384573831488120 :=
  phase_of_block (n := 223) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 0) (start := 0)
      [
      (128,469551067788544996513056), (95,88821195596028834975064)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_2_2360_1 : fastPhase (bank 3 2).shape 179818 2360 2 1 1 1 1 = 552893061368425065209054 :=
  phase_of_block (n := 223) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 1) (start := 0)
      [
      (128,466020185180048051541280), (95,86872876188377013667774)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2359_0 receipt_3_2_2359_1 receipt_3_2_2360_0 receipt_3_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2359_0 : fastPhase (bank 0 3).shape 179818 2359 3 1 0 1 0 = 20590630853382715040133328 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) (start := 0)
      [
      (128,14940717151171454928642004), (128,5497817419396684296881982),
      (26,152096282814575814609342)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_3_2359_1 : fastPhase (bank 0 3).shape 179818 2359 3 1 0 1 1 = 20432838317806511310329168 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) (start := 0)
      [
      (128,14859256973095353653084696), (128,5432840050510719708464142),
      (26,140741294200437948780330)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_3_2360_0 : fastPhase (bank 0 3).shape 179818 2360 3 1 0 1 0 = 20590789089745404932984231 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) (start := 0)
      [
      (128,14940842291962092423972752), (128,5497849926737097161750638),
      (26,152096871046215347260841)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_3_2360_1 : fastPhase (bank 0 3).shape 179818 2360 3 1 0 1 1 = 20432995618731633800543708 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) (start := 0)
      [
      (128,14859381549652646478755660), (128,5432872228638161682560637),
      (26,140741840440825639227411)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2359_0 receipt_0_3_2359_1 receipt_0_3_2360_0 receipt_0_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2359_0 : fastPhase (bank 1 3).shape 179818 2359 3 1 0 2 0 = 18470410449504050877866293 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) (start := 0)
      [
      (128,13411219630965347011863043), (128,4923233420331083604867183),
      (26,135957398207620261136067)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_3_2359_1 : fastPhase (bank 1 3).shape 179818 2359 3 1 0 2 1 = 18328610802752786976668082 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) (start := 0)
      [
      (128,13337839842034019138679906), (128,4864965370004846706232881),
      (26,125805590713921131755295)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_3_2360_0 : fastPhase (bank 1 3).shape 179818 2360 3 1 0 2 0 = 18470552424577799536550643 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) (start := 0)
      [
      (128,13411331967810385400626725), (128,4923262532742658029290649),
      (26,135957924024756106633269)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_3_2360_1 : fastPhase (bank 1 3).shape 179818 2360 3 1 0 2 1 = 18328751936276248949849622 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) (start := 0)
      [
      (128,13337951670200290222039968), (128,4864994187087415839336975),
      (26,125806078988542888472679)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2359_0 receipt_1_3_2359_1 receipt_1_3_2360_0 receipt_1_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2359_0 : fastPhase (bank 2 3).shape 179818 2359 3 1 0 7 0 = 9644442856132997806753779 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) (start := 0)
      [
      (128,7036797562219460142489219), (128,2538463226756481026406318), (26,69182067157056637858242)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_3_2359_1 : fastPhase (bank 2 3).shape 179818 2359 3 1 0 7 1 = 9569427338429385644526193 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) (start := 0)
      [
      (128,6997306986666192574638061), (128,2508110425734950074222822), (26,64009926028242995665310)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_3_2360_0 : fastPhase (bank 2 3).shape 179818 2360 3 1 0 7 0 = 9644517112362138248557776 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) (start := 0)
      [
      (128,7036856530953689350304924), (128,2538478246679152071894503), (26,69182334729296826358349)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_3_2360_1 : fastPhase (bank 2 3).shape 179818 2360 3 1 0 7 1 = 9569501145939597610980143 :=
  phase_of_block (n := 282) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) (start := 0)
      [
      (128,6997365680067591637400174), (128,2508125291401237805989080), (26,64010174470768167590889)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2359_0 receipt_2_3_2359_1 receipt_2_3_2360_0 receipt_2_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2359_0 : fastPhase (bank 3 3).shape 179818 2359 3 1 1 1 0 = 854638317776162520604290 :=
  phase_of_block (n := 238) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 0) (start := 0)
      [
      (128,693256944092452864938144), (110,161381373683709655666146)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_3_2359_1 : fastPhase (bank 3 3).shape 179818 2359 3 1 1 1 1 = 846778400647457918642849 :=
  phase_of_block (n := 238) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 1) (start := 0)
      [
      (128,688469362908471684705440), (110,158309037738986233937409)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_3_2360_0 : fastPhase (bank 3 3).shape 179818 2360 3 1 1 1 0 = 854644037429466495970024 :=
  phase_of_block (n := 238) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 0) (start := 0)
      [
      (128,693262089929402240069088), (110,161381947500064255900936)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_3_2360_1 : fastPhase (bank 3 3).shape 179818 2360 3 1 1 1 1 = 846784071078435523458131 :=
  phase_of_block (n := 238) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 1) (start := 0)
      [
      (128,688474469592966809314400), (110,158309601485468714143731)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2359_0 receipt_3_3_2359_1 receipt_3_3_2360_0 receipt_3_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2359_0 : fastPhase (bank 0 4).shape 179818 2359 4 1 0 1 0 = 31848728948298841697130334 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) (start := 0)
      [
      (128,22565421200238256272617173), (128,8863021353129825510321267),
      (36,420286394930759914191894)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_4_2359_1 : fastPhase (bank 0 4).shape 179818 2359 4 1 0 1 1 = 31613334413113404125792443 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) (start := 0)
      [
      (128,22447890277258017435753375), (128,8768112400620694197003638),
      (36,397331735234692493035430)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_4_2360_0 : fastPhase (bank 0 4).shape 179818 2360 4 1 0 1 0 = 31848972916253239267001857 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) (start := 0)
      [
      (128,22565610110918244587888050), (128,8863074707442011546840869),
      (36,420288097892983132272938)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_0_4_2360_1 : fastPhase (bank 0 4).shape 179818 2360 4 1 0 1 1 = 31613576984696677805138544 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) (start := 0)
      [
      (128,22448078372069395707711201), (128,8768165262285059233001445),
      (36,397333350342222864425898)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2359_0 receipt_0_4_2359_1 receipt_0_4_2360_0 receipt_0_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2359_0 : fastPhase (bank 1 4).shape 179818 2359 4 1 0 2 0 = 28661441097410756309334940 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) (start := 0)
      [
      (128,20320057162515937008827685), (128,7964315043826819215542671),
      (36,377068891068000084964584)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_4_2359_1 : fastPhase (bank 1 4).shape 179818 2359 4 1 0 2 1 = 28449258175417851689705271 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) (start := 0)
      [
      (128,20213877503287247192287695), (128,7878910237951993428407078),
      (36,356470434178611069010498)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_4_2360_0 : fastPhase (bank 1 4).shape 179818 2360 4 1 0 2 0 = 28661660694653315649203877 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) (start := 0)
      [
      (128,20320227284285611769883756), (128,7964362991439742258405591),
      (36,377070418927961620914530)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_1_4_2360_1 : fastPhase (bank 1 4).shape 179818 2360 4 1 0 2 1 = 28449476512751359066630665 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) (start := 0)
      [
      (128,20214046887447694181479011), (128,7878957742104033372411584),
      (36,356471883199631512740070)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2359_0 receipt_1_4_2359_1 receipt_1_4_2360_0 receipt_1_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2359_0 : fastPhase (bank 2 4).shape 179818 2359 4 1 0 7 0 = 15307605996981316071440128 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) (start := 0)
      [
      (128,10902134642734390192312161), (128,4208515286625877493666197),
      (36,196956067621048385461770)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_4_2359_1 : fastPhase (bank 2 4).shape 179818 2359 4 1 0 7 1 = 15192949699025063764064874 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) (start := 0)
      [
      (128,10843841659343934771037815), (128,4162927254397855985872565),
      (36,186180785283273007154494)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_4_2360_0 : fastPhase (bank 2 4).shape 179818 2360 4 1 0 7 0 = 15307723451619651547049220 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) (start := 0)
      [
      (128,10902225949691677847154648), (128,4208540636210614839753661),
      (36,196956865717358860140911)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_2_4_2360_1 : fastPhase (bank 2 4).shape 179818 2360 4 1 0 7 1 = 15193066468116701094587823 :=
  phase_of_block (n := 292) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) (start := 0)
      [
      (128,10843932559280213801643615), (128,4162952366706731367212957),
      (36,186181542129755925731251)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2359_0 receipt_2_4_2359_1 receipt_2_4_2360_0 receipt_2_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2359_0 : fastPhase (bank 3 4).shape 179818 2359 4 1 1 1 0 = 2300624992170228171286144 :=
  phase_of_block (n := 303) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) (start := 0)
      [
      (128,1606812472231854683252224), (128,648821466586642278778368), (47,44991053351731209255552)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_4_2359_1 : fastPhase (bank 3 4).shape 179818 2359 4 1 1 1 1 = 2283915246710472648482076 :=
  phase_of_block (n := 303) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) (start := 0)
      [
      (128,1598548139179997170745216), (128,642293128139180915908480), (47,43073979391294561828380)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_4_2360_0 : fastPhase (bank 3 4).shape 179818 2360 4 1 1 1 0 = 2300640171507159228692460 :=
  phase_of_block (n := 303) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) (start := 0)
      [
      (128,1606824829549627218324000), (128,648824211343548582582816), (47,44991130613983427785644)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

private theorem receipt_3_4_2360_1 : fastPhase (bank 3 4).shape 179818 2360 4 1 1 1 1 = 2283930323062566775184140 :=
  phase_of_block (n := 303) (by decide +kernel)
    (CompactRank6970.from_blocks (f := fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) (start := 0)
      [
      (128,1598560425070048209435680), (128,642295844414875562978336), (47,43074053577643002770124)] (by repeat' first | (apply And.intro) | (exact True.intro) | (decide +kernel)) (by decide +kernel) (by decide +kernel))

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2359_0 receipt_3_4_2359_1 receipt_3_4_2360_0 receipt_3_4_2360_1 (by decide +kernel) (by decide +kernel)

def group1_stage (i : Fin 4) : Fin 17 :=
  ⟨1+i.val, by have := i.isLt; omega⟩

theorem group1_checked (rect : Fin 4) (i : Fin 4) :
    Checked (bank rect (group1_stage i)) (reserve (group1_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_1
    · exact receipt_1_1
    · exact receipt_2_1
    · exact receipt_3_1
  · fin_cases rect
    · exact receipt_0_2
    · exact receipt_1_2
    · exact receipt_2_2
    · exact receipt_3_2
  · fin_cases rect
    · exact receipt_0_3
    · exact receipt_1_3
    · exact receipt_2_3
    · exact receipt_3_3
  · fin_cases rect
    · exact receipt_0_4
    · exact receipt_1_4
    · exact receipt_2_4
    · exact receipt_3_4

theorem group1_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

end Lower6960.RescueSource

end Merged_R6960RescueSourceReceipt1
