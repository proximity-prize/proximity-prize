import ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBaseline
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part652
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part716
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part780
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part844
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part908
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part972
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1036
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1100
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1164
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1228
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1292
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1356
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1420
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1484
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1548
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1612
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1306
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1370
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1434
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1498
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1562
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1626
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRaw
import ProximityPrize.SubmissionLower.PrimaryTaperFamily
import ProximityPrize.SubmissionLower.PrimaryTaperColumns
import ProximityPrize.SubmissionLower.Final50Price

-- merged module KoalaTaperTransfer
section Merged_KoalaTaperTransfer
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open private charged inWindow charged_add_gain gain window_gain
  from ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank
open private fees saved_by_fees fees_le_baseline
  from ProximityPrize.SubmissionLower.PrimaryTaperBudget
open private combine baseline_budget_on sum_add_pointwise_eq
  from ProximityPrize.SubmissionLower.Fast022
open private sum_checked from ProximityPrize.SubmissionLower.PrimaryTaperRankData

abbrev localRank : ℕ := 343744005134722

private abbrev noPowers : BlockIndex → Powers := fun _ => ⟨0, 0, 0⟩

private def paid (p₁ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if w2.Contains i ∨ w3.Contains i then ∑ q : Column, charge i q
  else charged p₁ noPowers noPowers i

private theorem middle_baseline (p₁ : BlockIndex → Powers) (i : BlockIndex)
    (hlo : 2008 ≤ i.1.val) (hhi : i.1.val < 3514) :
    charged p₁ noPowers noPowers i = baseline i := by
  have hw : ¬ inWindow i := by
    unfold inWindow
    omega
  have h₁ : ¬ i.1.val < 2008 := by omega
  have hz : (noPowers i).expand = fun _ => 0 := by
    funext k
    fin_cases k <;> rfl
  unfold charged fees combine
  simp only [hw, hhi, h₁, ite_false, ite_true]
  split <;> rw [hz] <;> rfl

private theorem sum_window_exchange {ι : Type} (S : Finset ι)
    (first second : ι → Prop) [DecidablePred first] [DecidablePred second]
    (old new baseline : ι → ℕ) (disjoint : ∀ i, first i → ¬ second i)
    (same : ∀ i, first i ∨ second i → old i = baseline i) :
    (∑ i ∈ S, if first i ∨ second i then new i else old i) +
      (∑ i ∈ S, if first i then baseline i else 0) +
      (∑ i ∈ S, if second i then baseline i else 0) =
    (∑ i ∈ S, old i) + (∑ i ∈ S, if first i then new i else 0) +
      (∑ i ∈ S, if second i then new i else 0) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h₁ : first i
  · have h₂ := disjoint i h₁
    rw [same i (Or.inl h₁)]
    simp only [h₁, h₂, true_or, ite_true, ite_false, Nat.add_zero]
    exact Nat.add_comm _ _
  · by_cases h₂ : second i
    · rw [same i (Or.inr h₂)]
      simp only [h₁, h₂, or_true, ite_true, ite_false, Nat.add_zero]
      exact Nat.add_comm _ _
    · simp [h₁, h₂]

attribute [local irreducible] Finset.univ

private theorem raw_def (w : Window) :
    rawWindow w = ∑ i : BlockIndex, if w.Contains i then baseline i else 0 := rfl

private theorem debit_def (w : Window) :
    debit w = ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0 := rfl

private theorem paid_invoice (p₁ : BlockIndex → Powers) :
    (∑ i : BlockIndex, paid p₁ i) + rawWindow w2 + rawWindow w3 =
      (∑ i : BlockIndex, charged p₁ noPowers noPowers i) + debit w2 + debit w3 := by
  rw [raw_def, raw_def, debit_def, debit_def]
  apply sum_window_exchange Finset.univ w2.Contains w3.Contains
    (charged p₁ noPowers noPowers) (fun i => ∑ q : Column, charge i q) baseline
  · intro i h₂
    simp only [w2, w3, Window.Contains] at *
    omega
  · intro i h
    rcases h with h | h
    · simp only [w2, Window.Contains] at h
      exact middle_baseline p₁ i h.1 (by omega)
    · simp only [w3, Window.Contains] at h
      exact middle_baseline p₁ i (by omega) h.2.1

private theorem published_tail (p₁ : BlockIndex → Powers)
    (hp₁ : 9573892230 ≤ savingsSum w1 p₁) :
    (∑ i : BlockIndex, charged p₁ noPowers noPowers i) ≤ 344162560924059 := by
  classical
  have hbase := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hgain := window_gain
  have hsumGain : (∑ i, charged p₁ noPowers noPowers i) + (∑ i, gain i) =
      ∑ i, fees p₁ noPowers noPowers i := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => charged_add_gain p₁ noPowers noPowers i
  have htail : 396610034658 ≤ ∑ i : BlockIndex, tailSaving i := by
    have h := fastSavings_le (J := 600) (by decide)
    rw [← sumChunk_eq_fastSavings, sum_checked] at h
    exact h
  have hsave := saved_by_fees p₁ noPowers noPowers
  have hsum := sum_add_pointwise_eq Finset.univ (fees p₁ noPowers noPowers)
    (fun i => baseline i - fees p₁ noPowers noPowers i) baseline
    (fun i _ => Nat.add_sub_of_le (fees_le_baseline p₁ noPowers noPowers i))
  omega

theorem node_rank_of_receipts (x y : Geom)
    (hraw : 28571050105634 ≤ rawWindow w2 + rawWindow w3)
    (hfee : debit w2 + debit w3 ≤ 28152494316297) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  classical
  obtain ⟨p₁, hp₁⟩ := K1_13_2_3_4.proof
  have h₂ := K1_13_2_2_2.proof
  have h₃ := K1_13_2_2_3.proof
  have h₄ := K1_13_2_2_4.proof
  have h₅ := K1_13_2_2_5.proof
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  have hbound (i : BlockIndex) :
      Module.finrank Geom (LinearMap.range (TaperNormalize.originBlock (cap i.1.val) i)) ≤
        fees p₁ noPowers noPowers i := by
    have ho := Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
    unfold fees
    split
    · exact ho.trans (hBlock i _)
    · exact le_min (ho.trans (hBlock i _))
        (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
  have hr := TaperNormalize.rank_le_of_blocks cap_antitone x y (paid p₁) (fun i => by
    unfold paid
    split
    · rename_i h
      have hs : 1650 ≤ i.1.val := by
        rcases h with h | h
        · simp only [w2, Window.Contains] at h
          omega
        · simp only [w3, Window.Contains] at h
          omega
      exact (Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)).trans
        (block_le_charge i hs)
    · unfold charged
      split
      · exact le_min (hbound i) (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
      · exact hbound i)
  have hbalance := paid_invoice p₁
  have hother := published_tail p₁ hp₁
  unfold localRank
  omega

#print axioms node_rank_of_receipts
end KoalaTaperTransfer
end Merged_KoalaTaperTransfer

-- merged module Low48PrimaryPivotBins2
section Merged_Low48PrimaryPivotBins2
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window2_588_716 : binChunk w2 588 128 = 15940021400 :=
  binChunk_join (w := w2) (start := 588) (left := 64) (right := 64) (x := 2275738089) (y := 13664283311) batch2_588_652 batch2_652_716
private theorem window2_716_844 : binChunk w2 716 128 = 98897485719 :=
  binChunk_join (w := w2) (start := 716) (left := 64) (right := 64) (x := 34238929886) (y := 64658555833) batch2_716_780 batch2_780_844
private theorem window2_588_844 : binChunk w2 588 256 = 114837507119 :=
  binChunk_join (w := w2) (start := 588) (left := 128) (right := 128) (x := 15940021400) (y := 98897485719) window2_588_716 window2_716_844
private theorem window2_844_972 : binChunk w2 844 128 = 280723506983 :=
  binChunk_join (w := w2) (start := 844) (left := 64) (right := 64) (x := 107991005254) (y := 172732501729) batch2_844_908 batch2_908_972
private theorem window2_972_1100 : binChunk w2 972 128 = 710333537487 :=
  binChunk_join (w := w2) (start := 972) (left := 64) (right := 64) (x := 274721008389) (y := 435612529098) batch2_972_1036 batch2_1036_1100
private theorem window2_844_1100 : binChunk w2 844 256 = 991057044470 :=
  binChunk_join (w := w2) (start := 844) (left := 128) (right := 128) (x := 280723506983) (y := 710333537487) window2_844_972 window2_972_1100
private theorem window2_588_1100 : binChunk w2 588 512 = 1105894551589 :=
  binChunk_join (w := w2) (start := 588) (left := 256) (right := 256) (x := 114837507119) (y := 991057044470) window2_588_844 window2_844_1100
private theorem window2_1100_1228 : binChunk w2 1100 128 = 1749172160308 :=
  binChunk_join (w := w2) (start := 1100) (left := 64) (right := 64) (x := 683887644365) (y := 1065284515943) batch2_1100_1164 batch2_1164_1228
private theorem window2_1228_1356 : binChunk w2 1228 128 = 4035471666511 :=
  binChunk_join (w := w2) (start := 1228) (left := 64) (right := 64) (x := 1643777913509) (y := 2391693753002) batch2_1228_1292 batch2_1292_1356
private theorem window2_1100_1356 : binChunk w2 1100 256 = 5784643826819 :=
  binChunk_join (w := w2) (start := 1100) (left := 128) (right := 128) (x := 1749172160308) (y := 4035471666511) window2_1100_1228 window2_1228_1356
private theorem window2_1356_1484 : binChunk w2 1356 128 = 6407429970534 :=
  binChunk_join (w := w2) (start := 1356) (left := 64) (right := 64) (x := 2990708504408) (y := 3416721466126) batch2_1356_1420 batch2_1420_1484
private theorem window2_1548_1651 : binChunk w2 1548 103 = 6720810879726 :=
  binChunk_join (w := w2) (start := 1548) (left := 64) (right := 39) (x := 4074144621316) (y := 2646666258410) batch2_1548_1612 batch2_1612_1651
private theorem window2_1484_1651 : binChunk w2 1484 167 = 10471694717053 :=
  binChunk_join (w := w2) (start := 1484) (left := 64) (right := 103) (x := 3750883837327) (y := 6720810879726) batch2_1484_1548 window2_1548_1651
private theorem window2_1356_1651 : binChunk w2 1356 295 = 16879124687587 :=
  binChunk_join (w := w2) (start := 1356) (left := 128) (right := 167) (x := 6407429970534) (y := 10471694717053) window2_1356_1484 window2_1484_1651
private theorem window2_1100_1651 : binChunk w2 1100 551 = 22663768514406 :=
  binChunk_join (w := w2) (start := 1100) (left := 256) (right := 295) (x := 5784643826819) (y := 16879124687587) window2_1100_1356 window2_1356_1651
private theorem window2_588_1651 : binChunk w2 588 1063 = 23769663065995 :=
  binChunk_join (w := w2) (start := 588) (left := 512) (right := 551) (x := 1105894551589) (y := 22663768514406) window2_588_1100 window2_1100_1651
theorem binCompute2 : binCompute w2 = 23769663065995 := by
  exact (binCompute_eq_chunk w2 588 (by decide) (by decide)).trans window2_588_1651

end Low48PrimaryPivot
end Merged_Low48PrimaryPivotBins2

-- merged module Low48PrimaryPivotBins3
section Merged_Low48PrimaryPivotBins3
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window3_1306_1434 : binChunk w3 1306 128 = 259342027810 :=
  binChunk_join (w := w3) (start := 1306) (left := 64) (right := 64) (x := 40502154112) (y := 218839873698) batch3_1306_1370 batch3_1370_1434
private theorem window3_1242_1434 : binChunk w3 1242 192 = 260726461076 :=
  binChunk_join (w := w3) (start := 1242) (left := 64) (right := 128) (x := 1384433266) (y := 259342027810) batch3_1242_1306 window3_1306_1434
private theorem window3_1434_1562 : binChunk w3 1434 128 = 1698101321440 :=
  binChunk_join (w := w3) (start := 1434) (left := 64) (right := 64) (x := 589827520782) (y := 1108273800658) batch3_1434_1498 batch3_1498_1562
private theorem window3_1562_1651 : binChunk w3 1562 89 = 2424003467786 :=
  binChunk_join (w := w3) (start := 1562) (left := 64) (right := 25) (x := 1656289264367) (y := 767714203419) batch3_1562_1626 batch3_1626_1651
private theorem window3_1434_1651 : binChunk w3 1434 217 = 4122104789226 :=
  binChunk_join (w := w3) (start := 1434) (left := 128) (right := 89) (x := 1698101321440) (y := 2424003467786) window3_1434_1562 window3_1562_1651
private theorem window3_1242_1651 : binChunk w3 1242 409 = 4382831250302 :=
  binChunk_join (w := w3) (start := 1242) (left := 192) (right := 217) (x := 260726461076) (y := 4122104789226) window3_1242_1434 window3_1434_1651
theorem binCompute3 : binCompute w3 = 4382831250302 := by
  exact (binCompute_eq_chunk w3 1242 (by decide) (by decide)).trans window3_1242_1651

end Low48PrimaryPivot
end Merged_Low48PrimaryPivotBins3

-- merged module KoalaTaperTransferReceipt
section Merged_KoalaTaperTransferReceipt
set_option Elab.async false
namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative

theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  apply node_rank_of_receipts x y
  · rw [rawWindow_w2, rawWindow_w3]
  · have h2 := debit_le_binCompute w2 (by decide)
    have h3 := debit_le_binCompute w3 (by decide)
    rw [binCompute2] at h2
    rw [binCompute3] at h3
    omega

#print axioms node_rank
end KoalaTaperTransfer
end Merged_KoalaTaperTransferReceipt

-- merged module Wide50EulerPrimaryFamily
section Merged_Wide50EulerPrimaryFamily
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace Wide50EulerPrimary

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open PrimaryTaper (nodeMap wordMap row_bounds primaryBox TrueWeightLE JetsBounded contact_of_word_kernel)
open TaperColumns
open KoalaTaperTransfer
open scoped BigOperators
open private local_range_finite from ProximityPrize.SubmissionLower.PrimaryTaperFamily
open private map_independent_family from ProximityPrize.SubmissionLower.PortLowBase

private theorem rank_at_position {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ KoalaTaperTransfer.localRank := by
  letI := local_range_finite x y
  apply (Submodule.finrank_mono ?_).trans (KoalaTaperTransfer.node_rank x y)
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

theorem word_rank (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * KoalaTaperTransfer.localRank := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, KoalaTaperTransfer.localRank := Finset.sum_le_sum fun i _ => rank_at_position _ _
    _ = _ := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

def sourceRank (A D : ℕ) : ℕ := compactCount A D - 262144 * KoalaTaperTransfer.localRank


theorem primary_family (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := (finrank_source A D hD).trans (exact_columns A D hA hD hBudget)
  have hr := word_rank A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩




#print axioms primary_family
end
end Wide50EulerPrimary
end Merged_Wide50EulerPrimaryFamily

-- merged module PrimaryTaperActive
section Merged_PrimaryTaperActive
set_option Elab.async false

namespace PrimaryTaperActive

open K1_13 (Row)
open K1_13_2_2 (gradeWeight)
open MvPolynomial
open TaperColumns (jetExponents)
open TaperBudget (cap)

def Fits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n

theorem of_jets {P : Row 4} (h : ∀ m ∈ P.support, m ∈ jetExponents) :
    Fits P 5163 := by
  intro m hm
  have hz := h m hm
  let q := m.weight gradeWeight
  change q ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧ m 1 + m 2 + m 3 ≤ cap q at hz
  have hq : q = m 0 + m 1 + m 2 + m 3 := by
    simp [q, Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, smul_eq_mul]
  obtain ⟨hqmax, _, hd⟩ := hz
  unfold cap at hd
  split at hd <;> omega

private def weight : Fin 4 → ℕ := ![1,2,2,2]

private theorem weight_at (m : Fin 4 →₀ ℕ) :
    m.weight weight = m 0 + 2*m 1 + 2*m 2 + 2*m 3 := by
  simp [weight, Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]

theorem fits_iff (P : Row 4) (n : ℕ) : Fits P n ↔ weightedTotalDegree weight P ≤ n := by
  unfold Fits weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [weight_at]

theorem of_dvd {P Q : Row 4} {n : ℕ} (hQ : Q ≠ 0) (hdiv : P ∣ Q) (h : Fits Q n) :
    Fits P n :=
  (fits_iff P n).mpr ((weightedTotalDegree_le_of_dvd weight hdiv hQ).trans ((fits_iff Q n).mp h))

#print axioms of_jets
#print axioms of_dvd
end PrimaryTaperActive
end Merged_PrimaryTaperActive

set_option Elab.async false
namespace Final50Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)

abbrev TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) := Final50Price.TrueWeightLE P D
abbrev physicalDegree := Final50Price.physicalDegree
abbrev agreement := Final50Price.agreement
abbrev primaryBox := Final50Price.primaryBox
abbrev primaryCutoff := Final50Price.primaryCutoff
abbrev sourceRank := Wide50EulerPrimary.sourceRank agreement physicalDegree
abbrev layerWidth := Final50Price.layerWidth
abbrev layerNeed := Final50Price.layerNeed
abbrev Messages := Final50Price.Messages
abbrev ProperCut := Final50Price.ProperCut
abbrev LayerBudget := @Final50Price.LayerBudget

/-- Exact dimension supplied by the compact source and the uniform node rank cap. -/
theorem sourceRank_eq : sourceRank = 993533597967758343 := by decide

/-- The number of layers guaranteed by the stronger compact certificate. -/
theorem certified_layers : sourceRank / layerWidth + 1 = 21410054907182 := by decide

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧
      PrimaryTaper.JetsBounded (e i) ∧ Contact w (e i)

end
end Final50Order

section
namespace Final50OrderProof
noncomputable section
open P3 (I K)
open Final50Order (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧
    PrimaryTaper.JetsBounded P ∧ Contact w P
end
end Final50OrderProof
end
section
namespace Final50OrderProof
noncomputable section
open Polynomial
open P3 (I K node)
open Final50Order (agreement)
open Final50Order (Messages ProperCut TrueWeightLE physicalDegree primaryBox
  PrimaryRank primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open private exists_fresh specialization_bounds sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : Geom[X], S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ),
    Irreducible f → 0 < (shape f).t → (shape f).t < K1.p →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    Final50Price.ActiveFits P 5164 →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)
def c3 : Prop :=
  ∀ (w : I → K) (x : Geom), PrimaryRank w →
    (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i))
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s)
    {f : Row 4} (hirr : Irreducible f) (hpos : 0 < (shape f).t) (htop : (shape f).t < K1.p) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hlpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hactive : Final50Price.ActiveFits P 5164 :=
    fun m hm => (PrimaryTaperActive.of_jets hP.2.2.1 m hm).trans (by decide)
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hirr hpos htop hP.1
    hweight hactive horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3)
    {w Γ s n} {f : Fin n → Row 4} (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, Final50Order.LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) := by
  classical
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hirr i) (hpos i) (htop i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := h3 w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) :=
    Final50Price.remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := hirr j
        have hk := hirr k
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    have hs : r T ≤ Final50Price.symbolCount :=
      PrimaryTaper.symbol_rank x e (fun i => (he i).2.2.1) hei
    dsimp only [cost, Final50Price.remaining]
    apply le_min hs
    simpa only [a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))
end
end Final50OrderProof
end
section
set_option maxRecDepth 12000
namespace Final50OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)
open Final50Order (agreement)
open Final50Order (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open Final50OrderProof (BankRow requiredOrder)
open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open private eval_line line_contacts_zero from ProximityPrize.SubmissionLower.Fast074
open private order_of_locator_lines from ProximityPrize.SubmissionLower.Fast074
private def Bounded (Q : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j
private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (P : Row 4) (S U : Geom[X]) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial Geom[X] :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : Geom[X])
    (hw : TrueWeightLE P T) (hc : Contact w P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hc
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hw hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
theorem order_of_contact (w : I → K) (P : Row 4) {T : ℕ} (hT : T ≤ primaryCutoff)
    (hw : TrueWeightLE P T) (hc : Contact w P) {S : Geom[X]} (hS : S.natDegree ≤ physicalDegree)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    K1_13.OrderAt P S (requiredOrder T) := by
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hw hc hS A hA (fun i hi => hits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT

theorem proof : Final50OrderProof.c1 := by
  intro w T P hT hP S hS hits
  obtain ⟨H, hH, hhits⟩ := hits
  exact order_of_contact w P hT hP.2.1 hP.2.2.2 hS hH hhits
end
end Final50OrderProof_1
end
section
namespace Final50OrderProof_2
noncomputable section
open Polynomial
open Final50Order (TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open private translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top
  apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd from ProximityPrize.SubmissionLower.PortLowBase
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem proof : Final50OrderProof.c2 := by
  intro f P Γ s d a hirr hpos htop hb hw ha hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds primaryBox primaryCutoff a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp
      (topHasse_one_not_dvd f hirr hpos htop) hdiv hexact
  have hactive : Final50Price.ActiveFits (topHasse a P) 5164 := by
    intro m hm
    have hh := ha _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  exact ⟨topHasse a P, hproper, hbox, hweight, hactive, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩
end
end Final50OrderProof_2
end
section
namespace Final50OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)
open Final50Order (TrueWeightLE physicalDegree primaryCutoff)
open Final50OrderProof (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open private jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor
  linearFactor_ne linearFactor_degree divide_specialization support_linear_mul from ProximityPrize.SubmissionLower.PortLowBase
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE, PrimaryTaper.JetsBounded]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hs, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm, hs m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2.1, fun m hm => (h m hm).2.2.2.2, hc⟩
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
      obtain ⟨hb, hj, ht, hw, hjets⟩ := bounds
      refine ⟨hb, hj, ht, ?_, hjets⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2.1)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2.1)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_, hjets⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    constructor <;> rintro ⟨hb, hj, ht, hw, hJets⟩ <;>
      exact ⟨hb, hj, ht, by omega, hJets⟩
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        simp [symbolAt, linearFactor])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem proof : Final50OrderProof.c3 := by
  classical
  intro w x hr hx
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Final50OrderProof_3
end
namespace Final50Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial

export Final50OrderProof (BankRow requiredOrder)
export Final50OrderProof_1 (order_of_contact)

theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2413) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hz | hd := (F.mark γ hγ).scalar_degree
    · simp [hz]
    · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at hd
      change (F.scalar γ).natDegree ≤ 133484
      omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩

/-- Compatible proper cuts for a family of distinct irreducible factors. -/
theorem proper_layers_of_rank {w Γ s n} {f : Fin n → Row 4}
    (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) :=
  Final50OrderProof.of_children Final50OrderProof_1.proof
    Final50OrderProof_2.proof Final50OrderProof_3.proof
    hm hr hirr hpos htop hdiff

/-- Supply the compact primary bank at height 2413. -/
theorem primary_rank (w : P3.I → K) : PrimaryRank w :=
  Wide50EulerPrimary.primary_family agreement physicalDegree (by decide) (by decide)
    (by decide) w (n := sourceRank) le_rfl

/-- A common evaluation point gives an independent symbol family at each cutoff. -/
theorem symbol_families : Final50OrderProof.c3 := Final50OrderProof_3.proof


end
end Final50Order