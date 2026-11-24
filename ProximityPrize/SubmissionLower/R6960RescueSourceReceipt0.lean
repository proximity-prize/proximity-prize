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
  width_first : WidthGuard t 179808 2379 r
  first : 0<surplus t 179808 2379 r 1 c v
  next : surplus t 179808 2379 r 1 c v ≤ surplus t 179808 2380 r 1 c v

theorem checked_from_values (t : Bank) (r c v : ℕ) (hb : P3_7_1.BankOK t)
    (seed : t.shape.U<K1.p) (reserve : 2*r≤t.shape.B) (width : WidthGuard t 179808 2379 r)
    (slope : t.shape.J<131071-2380) (shift : 2*2380*(r+t.shape.J)<t.shape.m*179808)
    {a b x y : ℕ} (a0 : fastPhase t.shape 179808 2379 r 1 c v 0 = a)
    (a1 : fastPhase t.shape 179808 2379 r 1 c v 1 = b)
    (b0 : fastPhase t.shape 179808 2380 r 1 c v 0 = x)
    (b1 : fastPhase t.shape 179808 2380 r 1 c v 1 = y)
    (pos : 0<((a-b : ℕ) : ℤ)-(debit 2379 t : ℤ))
    (inc : ((a-b : ℕ) : ℤ)-(debit 2379 t : ℤ) ≤ ((x-y : ℕ) : ℤ)-(debit 2380 t : ℤ)) :
    Checked t r c v := by
  have h1 := fastSurplus_eq t 2379 r c v (by omega)
    ((Nat.mul_le_mul_right (r+t.shape.J) (by decide : 2*2379≤2*2380)).trans_lt shift)
  have h2 := fastSurplus_eq t 2380 r c v slope shift
  unfold fastSurplus at h1 h2
  rw [a0,a1] at h1
  rw [b0,b1] at h2
  refine ⟨hb,seed,reserve,width,?_,?_⟩
  · rwa [← h1]
  · rwa [← h1, ← h2]

def buffered (t : Bank) (h r : ℕ) : ℕ := cutoffCount t.shape 179808 h r-1

theorem Checked.width {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2379≤h) (hi : h≤33599) : WidthGuard t 179808 h r :=
  HelperSource.width_at_height t 179808 2379 h r lo (by omega) cert.reserve_ok cert.width_first

theorem Checked.cutoff_fit {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2379≤h) (hi : h≤33599) : buffered t h r+2*h*r<t.shape.m*179808 :=
  FreeSource.buffered_fit t 179808 h r (cert.width lo hi)

/-- Only the actual moving prime's lower degree bounds enter avoidance. -/
theorem Checked.avoids {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2379≤h) (hi : h≤33599) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 1≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (buffered t h r), ¬ G∣Q :=
  HelperSource.crt_avoiding_row Crt word t 179808 r 1 c v (by omega) (by omega) (by decide)
    cert.bank_ok.nodes cert.bank_ok.moment.1 cert.bank_ok.moment.2 cert.seed_ok
    (cert.width lo hi)
    (HelperSource.surplus_positive t 179808 2379 h r 1 c v lo (by omega) cert.first cert.next)
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
    ⟨⟨900,1257,266,68705⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,77721⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,91124⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,114738⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,130980⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,111664⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1817,380,136443⟩,64827042824192,292013331876⟩,
    ⟨⟨1644,2285,480,146187⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,220223⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,164887⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,249371⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,339594⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4255,890,340332⟩,830225100570624,8759063388784⟩,
    ⟨⟨4281,5949,1250,407544⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,619710⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,674809⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,836683⟩,21862342000640000,675999454048899⟩
  ]

private def bank0 (i : Fin 17) : Bank := banks0.get ⟨i.val,i.isLt⟩

private def banks1 : List Bank :=
  [
    ⟨⟨900,1257,266,65145⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,73690⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,86443⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,108767⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,124353⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,105958⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1817,380,129548⟩,64827042824192,292013331876⟩,
    ⟨⟨1644,2285,480,138713⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,208942⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,156564⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,235563⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,320822⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4255,890,323171⟩,830225100570624,8759063388784⟩,
    ⟨⟨4281,5949,1250,386729⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,588064⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,640349⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,793956⟩,21862342000640000,675999454048899⟩
  ]

private def bank1 (i : Fin 17) : Bank := banks1.get ⟨i.val,i.isLt⟩

private def banks2 : List Bank :=
  [
    ⟨⟨900,1257,266,47523⟩,21654240231424,67643823442⟩,
    ⟨⟨950,1327,281,53719⟩,25475688955904,84031339757⟩,
    ⟨⟨965,1341,282,63221⟩,26453882961920,87154749585⟩,
    ⟨⟨950,1326,281,79096⟩,25475688955904,83828003187⟩,
    ⟨⟨998,1392,291,91396⟩,29207484170240,100699468110⟩,
    ⟨⟨1220,1696,356,77655⟩,53339440021504,222371564601⟩,
    ⟨⟨1302,1809,380,95753⟩,64827042824192,287901786632⟩,
    ⟨⟨1644,2285,480,101647⟩,130442673520640,732176567216⟩,
    ⟨⟨1927,2678,563,152899⟩,210083041509376,1381475727537⟩,
    ⟨⟨1505,2100,439,115224⟩,100029337436160,520524444033⟩,
    ⟨⟨2474,3438,750,167068⟩,457024195788800,3859704881140⟩,
    ⟨⟨3502,4866,1061,227726⟩,1294924103024640,15471861206598⟩,
    ⟨⟨3048,4235,890,239111⟩,830225100570624,8627387690344⟩,
    ⟨⟨4281,5949,1250,283449⟩,2299214724071424,33568648660145⟩,
    ⟨⟨6623,9203,1934,431058⟩,8510639324528640,192177638347017⟩,
    ⟨⟨6624,9204,1934,469278⟩,8513508830085120,192244798810122⟩,
    ⟨⟨9071,12604,2649,582002⟩,21862342000640000,675999454048899⟩
  ]

private def bank2 (i : Fin 17) : Bank := banks2.get ⟨i.val,i.isLt⟩

private def banks3 : List Bank :=
  [
    ⟨⟨650,907,192,24615⟩,8170644439040,18389221088⟩,
    ⟨⟨700,977,207,27163⟩,10208212418560,24758176234⟩,
    ⟨⟨750,1047,222,29746⟩,12559140782080,32653699308⟩,
    ⟨⟨800,1117,237,32359⟩,15245842841600,42302192650⟩,
    ⟨⟨998,1387,302,33671⟩,30044628975616,102461756220⟩,
    ⟨⟨1220,1696,370,37074⟩,54930349752320,229159736517⟩,
    ⟨⟨1302,1809,395,41359⟩,66768112975872,296724029248⟩,
    ⟨⟨1644,2285,498,49288⟩,134156626165760,753510622290⟩,
    ⟨⟨1927,2678,584,62466⟩,216034207334400,1421525065183⟩,
    ⟨⟨1505,2091,456,48280⟩,102969492373504,528831085877⟩,
    ⟨⟨1953,2726,570,75007⟩,218519657775104,1476869586813⟩,
    ⟨⟨2772,3870,809,105032⟩,624354479308800,5992280745484⟩,
    ⟨⟨3048,4235,924,98244⟩,854327964467200,8883701072242⟩,
    ⟨⟨4281,5949,1297,130869⟩,2364944629104640,34550690014738⟩,
    ⟨⟨6623,9203,2007,201270⟩,8754949968101376,197823002949183⟩,
    ⟨⟨6624,9204,2007,206664⟩,8757908515848192,197892215121891⟩,
    ⟨⟨9071,12604,2749,274292⟩,22490098892800000,695862530200649⟩
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

private theorem receipt_0_0_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 0) 0 128 = 4747754990300091403086773 := by decide +kernel
private theorem receipt_0_0_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 0) 128 128 = 1556531058151062933748469 := by decide +kernel
private theorem receipt_0_0_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 0) 256 11 = 9666306244156103072751 := by decide +kernel
private theorem receipt_0_0_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 0) 128 139 = 1566197364395219036821220 :=
  phaseBlock_append receipt_0_0_2359_0_part1 receipt_0_0_2359_0_part2 rfl rfl rfl
private theorem receipt_0_0_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 0) 0 267 = 6313952354695310439907993 :=
  phaseBlock_append receipt_0_0_2359_0_part0 receipt_0_0_2359_0_join0 rfl rfl rfl

private theorem receipt_0_0_2359_0 : fastPhase (bank 0 0).shape 179808 2379 0 1 0 1 0 = 6313952354695310439907993 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2359_0_join1

private theorem receipt_0_0_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 1) 0 128 = 4720010465392505130916675 := by decide +kernel
private theorem receipt_0_0_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 1) 128 128 = 1534759613443597264144093 := by decide +kernel
private theorem receipt_0_0_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 1) 256 11 = 8049841905700328137982 := by decide +kernel
private theorem receipt_0_0_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 1) 128 139 = 1542809455349297592282075 :=
  phaseBlock_append receipt_0_0_2359_1_part1 receipt_0_0_2359_1_part2 rfl rfl rfl
private theorem receipt_0_0_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2379 0 1 0 1 1) 0 267 = 6262819920741802723198750 :=
  phaseBlock_append receipt_0_0_2359_1_part0 receipt_0_0_2359_1_join0 rfl rfl rfl

private theorem receipt_0_0_2359_1 : fastPhase (bank 0 0).shape 179808 2379 0 1 0 1 1 = 6262819920741802723198750 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2359_1_join1

private theorem receipt_0_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 0) 0 128 = 4747794899369907245311877 := by decide +kernel
private theorem receipt_0_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 0) 128 128 = 1556540166144393662941807 := by decide +kernel
private theorem receipt_0_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 0) 256 11 = 9666342240883731518797 := by decide +kernel
private theorem receipt_0_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 0) 128 139 = 1566206508385277394460604 :=
  phaseBlock_append receipt_0_0_2360_0_part1 receipt_0_0_2360_0_part2 rfl rfl rfl
private theorem receipt_0_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 0) 0 267 = 6314001407755184639772481 :=
  phaseBlock_append receipt_0_0_2360_0_part0 receipt_0_0_2360_0_join0 rfl rfl rfl

private theorem receipt_0_0_2360_0 : fastPhase (bank 0 0).shape 179808 2380 0 1 0 1 0 = 6314001407755184639772481 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2360_0_join1

private theorem receipt_0_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 1) 0 128 = 4720050181344793704210004 := by decide +kernel
private theorem receipt_0_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 1) 128 128 = 1534768613016117795983730 := by decide +kernel
private theorem receipt_0_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 1) 256 11 = 8049871999348665379917 := by decide +kernel
private theorem receipt_0_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 1) 128 139 = 1542818485015466461363647 :=
  phaseBlock_append receipt_0_0_2360_1_part1 receipt_0_0_2360_1_part2 rfl rfl rfl
private theorem receipt_0_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2380 0 1 0 1 1) 0 267 = 6262868666360260165573651 :=
  phaseBlock_append receipt_0_0_2360_1_part0 receipt_0_0_2360_1_join0 rfl rfl rfl

private theorem receipt_0_0_2360_1 : fastPhase (bank 0 0).shape 179808 2380 0 1 0 1 1 = 6262868666360260165573651 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2360_1_join1

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2359_0 receipt_0_0_2359_1 receipt_0_0_2360_0 receipt_0_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 0) 0 128 = 4260851912111352355460308 := by decide +kernel
private theorem receipt_1_0_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 0) 128 128 = 1391613058964104157840609 := by decide +kernel
private theorem receipt_1_0_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 0) 256 11 = 8617651079654532602148 := by decide +kernel
private theorem receipt_1_0_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 0) 128 139 = 1400230710043758690442757 :=
  phaseBlock_append receipt_1_0_2359_0_part1 receipt_1_0_2359_0_part2 rfl rfl rfl
private theorem receipt_1_0_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 0) 0 267 = 5661082622155111045903065 :=
  phaseBlock_append receipt_1_0_2359_0_part0 receipt_1_0_2359_0_join0 rfl rfl rfl

private theorem receipt_1_0_2359_0 : fastPhase (bank 1 0).shape 179808 2379 0 1 0 2 0 = 5661082622155111045903065 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2359_0_join1

private theorem receipt_1_0_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 1) 0 128 = 4235820123745783735000485 := by decide +kernel
private theorem receipt_1_0_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 1) 128 128 = 1372114120615714568670302 := by decide +kernel
private theorem receipt_1_0_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 1) 256 11 = 7176393227063492257722 := by decide +kernel
private theorem receipt_1_0_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 1) 128 139 = 1379290513842778060928024 :=
  phaseBlock_append receipt_1_0_2359_1_part1 receipt_1_0_2359_1_part2 rfl rfl rfl
private theorem receipt_1_0_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2379 0 1 0 2 1) 0 267 = 5615110637588561795928509 :=
  phaseBlock_append receipt_1_0_2359_1_part0 receipt_1_0_2359_1_join0 rfl rfl rfl

private theorem receipt_1_0_2359_1 : fastPhase (bank 1 0).shape 179808 2379 0 1 0 2 1 = 5615110637588561795928509 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2359_1_join1

private theorem receipt_1_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 0) 0 128 = 4260887732044876852255319 := by decide +kernel
private theorem receipt_1_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 0) 128 128 = 1391621203033987252834204 := by decide +kernel
private theorem receipt_1_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 0) 256 11 = 8617683171308521378332 := by decide +kernel
private theorem receipt_1_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 0) 128 139 = 1400238886205295774212536 :=
  phaseBlock_append receipt_1_0_2360_0_part1 receipt_1_0_2360_0_part2 rfl rfl rfl
private theorem receipt_1_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 0) 0 267 = 5661126618250172626467855 :=
  phaseBlock_append receipt_1_0_2360_0_part0 receipt_1_0_2360_0_join0 rfl rfl rfl

private theorem receipt_1_0_2360_0 : fastPhase (bank 1 0).shape 179808 2380 0 1 0 2 0 = 5661126618250172626467855 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2360_0_join1

private theorem receipt_1_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 1) 0 128 = 4235855769229478263915605 := by decide +kernel
private theorem receipt_1_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 1) 128 128 = 1372122167527282273244251 := by decide +kernel
private theorem receipt_1_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 1) 256 11 = 7176420055435551020277 := by decide +kernel
private theorem receipt_1_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 1) 128 139 = 1379298587582717824264528 :=
  phaseBlock_append receipt_1_0_2360_1_part1 receipt_1_0_2360_1_part2 rfl rfl rfl
private theorem receipt_1_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2380 0 1 0 2 1) 0 267 = 5615154356812196088180133 :=
  phaseBlock_append receipt_1_0_2360_1_part0 receipt_1_0_2360_1_join0 rfl rfl rfl

private theorem receipt_1_0_2360_1 : fastPhase (bank 1 0).shape 179808 2380 0 1 0 2 1 = 5615154356812196088180133 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2360_1_join1

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2359_0 receipt_1_0_2359_1 receipt_1_0_2360_0 receipt_1_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 0) 0 128 = 2238290780252431708218127 := by decide +kernel
private theorem receipt_2_0_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 0) 128 128 = 710979033531719529835022 := by decide +kernel
private theorem receipt_2_0_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 0) 256 11 = 4310793573048753703341 := by decide +kernel
private theorem receipt_2_0_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 0) 128 139 = 715289827104768283538363 :=
  phaseBlock_append receipt_2_0_2359_0_part1 receipt_2_0_2359_0_part2 rfl rfl rfl
private theorem receipt_2_0_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 0) 0 267 = 2953580607357199991756490 :=
  phaseBlock_append receipt_2_0_2359_0_part0 receipt_2_0_2359_0_join0 rfl rfl rfl

private theorem receipt_2_0_2359_0 : fastPhase (bank 2 0).shape 179808 2379 0 1 0 7 0 = 2953580607357199991756490 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2359_0_join1

private theorem receipt_2_0_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 1) 0 128 = 2224634529833573990788392 := by decide +kernel
private theorem receipt_2_0_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 1) 128 128 = 700887636044475531185513 := by decide +kernel
private theorem receipt_2_0_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 1) 256 11 = 3589249366747221868824 := by decide +kernel
private theorem receipt_2_0_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 1) 128 139 = 704476885411222753054337 :=
  phaseBlock_append receipt_2_0_2359_1_part1 receipt_2_0_2359_1_part2 rfl rfl rfl
private theorem receipt_2_0_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2379 0 1 0 7 1) 0 267 = 2929111415244796743842729 :=
  phaseBlock_append receipt_2_0_2359_1_part0 receipt_2_0_2359_1_join0 rfl rfl rfl

private theorem receipt_2_0_2359_1 : fastPhase (bank 2 0).shape 179808 2379 0 1 0 7 1 = 2929111415244796743842729 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2359_1_join1

private theorem receipt_2_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 0) 0 128 = 2238309611194764514114952 := by decide +kernel
private theorem receipt_2_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 0) 128 128 = 710983198467140581291291 := by decide +kernel
private theorem receipt_2_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 0) 256 11 = 4310809626404550111645 := by decide +kernel
private theorem receipt_2_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 0) 128 139 = 715294008093545131402936 :=
  phaseBlock_append receipt_2_0_2360_0_part1 receipt_2_0_2360_0_part2 rfl rfl rfl
private theorem receipt_2_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 0) 0 267 = 2953603619288309645517888 :=
  phaseBlock_append receipt_2_0_2360_0_part0 receipt_2_0_2360_0_join0 rfl rfl rfl

private theorem receipt_2_0_2360_0 : fastPhase (bank 2 0).shape 179808 2380 0 1 0 7 0 = 2953603619288309645517888 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2360_0_join1

private theorem receipt_2_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 1) 0 128 = 2224653264786619268549259 := by decide +kernel
private theorem receipt_2_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 1) 128 128 = 700891750491229510514539 := by decide +kernel
private theorem receipt_2_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 1) 256 11 = 3589262785008098431224 := by decide +kernel
private theorem receipt_2_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 1) 128 139 = 704481013276237608945763 :=
  phaseBlock_append receipt_2_0_2360_1_part1 receipt_2_0_2360_1_part2 rfl rfl rfl
private theorem receipt_2_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2380 0 1 0 7 1) 0 267 = 2929134278062856877495022 :=
  phaseBlock_append receipt_2_0_2360_1_part0 receipt_2_0_2360_1_join0 rfl rfl rfl

private theorem receipt_2_0_2360_1 : fastPhase (bank 2 0).shape 179808 2380 0 1 0 7 1 = 2929134278062856877495022 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2360_1_join1

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2359_0 receipt_2_0_2359_1 receipt_2_0_2360_0 receipt_2_0_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 0) 0 128 = 197378020888942507519648 := by decide +kernel
private theorem receipt_3_0_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 0) 128 65 = 21305634537439529152304 := by decide +kernel
private theorem receipt_3_0_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 0) 0 193 = 218683655426382036671952 :=
  phaseBlock_append receipt_3_0_2359_0_part0 receipt_3_0_2359_0_part1 rfl rfl rfl

private theorem receipt_3_0_2359_0 : fastPhase (bank 3 0).shape 179808 2379 0 1 1 1 0 = 218683655426382036671952 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2359_0_join0

private theorem receipt_3_0_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 1) 0 128 = 195573797258849204159520 := by decide +kernel
private theorem receipt_3_0_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 1) 128 65 = 20632113183047092986896 := by decide +kernel
private theorem receipt_3_0_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2379 0 1 1 1 1) 0 193 = 216205910441896297146416 :=
  phaseBlock_append receipt_3_0_2359_1_part0 receipt_3_0_2359_1_part1 rfl rfl rfl

private theorem receipt_3_0_2359_1 : fastPhase (bank 3 0).shape 179808 2379 0 1 1 1 1 = 216205910441896297146416 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2359_1_join0

private theorem receipt_3_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 0) 0 128 = 197379439480001198463136 := by decide +kernel
private theorem receipt_3_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 0) 128 65 = 21305697495394655150808 := by decide +kernel
private theorem receipt_3_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 0) 0 193 = 218685136975395853613944 :=
  phaseBlock_append receipt_3_0_2360_0_part0 receipt_3_0_2360_0_part1 rfl rfl rfl

private theorem receipt_3_0_2360_0 : fastPhase (bank 3 0).shape 179808 2380 0 1 1 1 0 = 218685136975395853613944 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2360_0_join0

private theorem receipt_3_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 1) 0 128 = 195575201961922952923680 := by decide +kernel
private theorem receipt_3_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 1) 128 65 = 20632174295479490403088 := by decide +kernel
private theorem receipt_3_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2380 0 1 1 1 1) 0 193 = 216207376257402443326768 :=
  phaseBlock_append receipt_3_0_2360_1_part0 receipt_3_0_2360_1_part1 rfl rfl rfl

private theorem receipt_3_0_2360_1 : fastPhase (bank 3 0).shape 179808 2380 0 1 1 1 1 = 216207376257402443326768 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2360_1_join0

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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group0_stage i)).shape
      (cutoff h rect (group0_stage i)), ¬ G∣Q :=
  (group0_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group0_avoids

end Lower6960.RescueSource

end Merged_R6960RescueSourceReceipt0
