import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.R6960Anchor6966
import ProximityPrize.SubmissionLower.R6960Front6960Rank4

section Merged6967_Low48BentSupport
set_option Elab.async false

set_option Elab.async false

-- merged module Low48BentLattice
section Merged_Low48BentLattice

set_option autoImplicit false
namespace Low48BentLattice
open K1_13 (Shape)
open K1_13_6_2_4 (Exponent)
open scoped Pointwise

abbrev Cap := Shape × ℕ

def Add (a b : Cap) : Cap := (a.1.plus b.1, a.2 + b.2)

def Scale (n : ℕ) (a : Cap) : Cap := (a.1.scale n, n * a.2)

def Chamber (a : Cap) : Prop := a.1.j ≤ a.1.b ∧ 3 * a.1.t ≤ a.1.j ∧ 2 * a.2 ≤ a.1.t

def Allowed (a : Cap) (m : Exponent) : Prop :=
  m 0 + m 1 + m 2 + m 3 + m 4 ≤ a.1.b ∧
  m 1 + 2 * m 2 + 3 * m 3 + 4 * m 4 ≤ a.1.j ∧
  m 3 + 2 * m 4 ≤ a.1.t ∧ m 4 ≤ a.2

def latticePoints (a : Cap) : Set Exponent := {m | Allowed (Scale 2 a) m}

theorem coords (a : Cap) (m : Exponent) : m ∈ latticePoints a ↔
    m 0 + m 1 + m 2 + m 3 + m 4 ≤ 2 * a.1.b ∧
    m 1 + 2 * m 2 + 3 * m 3 + 4 * m 4 ≤ 2 * a.1.j ∧
    m 3 + 2 * m 4 ≤ 2 * a.1.t ∧ m 4 ≤ 2 * a.2 := Iff.rfl

theorem finite (a : Cap) : (latticePoints a).Finite := by
  refine (Finsupp.finite_of_degree_le (2 * a.1.b)).subset ?_
  intro m hm
  rw [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Fin.sum_univ_five]
  exact ((coords a m).mp hm).1

instance (a : Cap) : Finite (latticePoints a) := (finite a).to_subtype


theorem zero_mem (a : Cap) : 0 ∈ latticePoints a := by simp [coords]

theorem lattice_add {a b : Cap} (ha : Chamber a) (hb : Chamber b) :
    latticePoints a + latticePoints b = latticePoints (Add a b) := by
  ext m
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [coords, Add, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro hm
    obtain ⟨haB, haJ, haT⟩ := ha
    obtain ⟨hbB, hbJ, hbT⟩ := hb
    simp only [coords, Add, Shape.plus] at hm
    obtain ⟨hmB, hmJ, hmT, hmH⟩ := hm
    let h := min (m 4) (2 * a.2)
    let h' := m 4 - h
    have hh : h + h' = m 4 ∧ h ≤ 2 * a.2 ∧ h' ≤ 2 * b.2 := by dsimp [h, h']; omega
    let t := min (m 3) (2 * a.1.t - 2 * h)
    let t' := m 3 - t
    have ht : t + t' = m 3 ∧ t + 2 * h ≤ 2 * a.1.t ∧ t' + 2 * h' ≤ 2 * b.1.t := by
      dsimp [t, t']
      omega
    let j := 2 * a.1.j - 4 * h - 3 * t
    let j' := 2 * b.1.j - 4 * h' - 3 * t'
    have hj : j + 4 * h + 3 * t = 2 * a.1.j ∧ j' + 4 * h' + 3 * t' = 2 * b.1.j := by
      dsimp [j, j']
      omega
    have hhalf : (j + j') / 2 = j / 2 + j' / 2 := by
      by_cases ht₀ : m 3 ≤ 2 * a.1.t - 2 * h
      · have ht'₀ : t' = 0 := by dsimp [t, t']; omega
        omega
      · have ht₁ : t = 2 * a.1.t - 2 * h := min_eq_right (by omega)
        omega
    let y := min (m 2) (j / 2)
    let y' := m 2 - y
    have hy : y + y' = m 2 ∧ 2 * y ≤ j ∧ 2 * y' ≤ j' := by dsimp [y, y']; omega
    let x := min (m 1) (j - 2 * y)
    let x' := m 1 - x
    have hx : x + x' = m 1 ∧ x + 2 * y ≤ j ∧ x' + 2 * y' ≤ j' := by
      dsimp [x, x']
      omega
    let u := min (m 0) (2 * a.1.b - (x + y + t + h))
    let u' := m 0 - u
    have hu : u + u' = m 0 ∧ u + x + y + t + h ≤ 2 * a.1.b ∧
        u' + x' + y' + t' + h' ≤ 2 * b.1.b := by
      dsimp [u, u']
      omega
    let v : Exponent := Finsupp.equivFunOnFinite.symm ![u, x, y, t, h]
    let v' : Exponent := Finsupp.equivFunOnFinite.symm ![u', x', y', t', h']
    refine ⟨v, (coords a v).mpr ?_, v', (coords b v').mpr ?_, ?_⟩
    · change u + x + y + t + h ≤ 2 * a.1.b ∧ x + 2 * y + 3 * t + 4 * h ≤ 2 * a.1.j ∧
        t + 2 * h ≤ 2 * a.1.t ∧ h ≤ 2 * a.2
      omega
    · change u' + x' + y' + t' + h' ≤ 2 * b.1.b ∧
        x' + 2 * y' + 3 * t' + 4 * h' ≤ 2 * b.1.j ∧ t' + 2 * h' ≤ 2 * b.1.t ∧ h' ≤ 2 * b.2
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact ht.1
      · exact hh.1

theorem chamber_scale {a : Cap} (ha : Chamber a) (n : ℕ) : Chamber (Scale n a) := by
  refine ⟨Nat.mul_le_mul_left n ha.1, ?_, ?_⟩
  · simpa only [Scale, Shape.scale, ← Nat.mul_left_comm n 3] using
      Nat.mul_le_mul_left n ha.2.1
  · simpa only [Scale, Shape.scale, ← Nat.mul_left_comm n 2] using
      Nat.mul_le_mul_left n ha.2.2

theorem lattice_zero : latticePoints (⟨0, 0, 0⟩, 0) = 0 := by
  ext m
  simp only [coords, Nat.mul_zero, Set.mem_zero]
  constructor
  · rintro ⟨hm, _, _, _⟩
    ext i
    fin_cases i
    · change m 0 = 0
      omega
    · change m 1 = 0
      omega
    · change m 2 = 0
      omega
    · change m 3 = 0
      omega
    · change m 4 = 0
      omega

  · rintro rfl
    simp

theorem lattice_scale (a : Cap) (ha : Chamber a) (n : ℕ) :
    n • latticePoints a = latticePoints (Scale n a) := by
  induction n with
  | zero => simpa [Scale, Shape.scale] using lattice_zero.symm
  | succ n ih =>
    rw [succ_nsmul, ih, lattice_add (chamber_scale ha n) ha]
    cases a
    simp [Add, Scale, Shape.scale, Shape.plus, Nat.succ_mul]

def Sum {ι : Type*} (s : Finset ι) (a : ι → Cap) : Cap :=
  (⟨∑ i ∈ s, (a i).1.b, ∑ i ∈ s, (a i).1.j, ∑ i ∈ s, (a i).1.t⟩, ∑ i ∈ s, (a i).2)

theorem chamber_sum {ι : Type*} (s : Finset ι) (a : ι → Cap)
    (ha : ∀ i ∈ s, Chamber (a i)) : Chamber (Sum s a) := by
  refine ⟨Finset.sum_le_sum (fun i hi => (ha i hi).1), ?_, ?_⟩
  · exact (Finset.mul_sum _ _ _).trans_le (Finset.sum_le_sum (fun i hi => (ha i hi).2.1))
  · exact (Finset.mul_sum _ _ _).trans_le (Finset.sum_le_sum (fun i hi => (ha i hi).2.2))

theorem lattice_sum {ι : Type*} (s : Finset ι) (a : ι → Cap)
    (ha : ∀ i ∈ s, Chamber (a i)) :
    (∑ i ∈ s, latticePoints (a i)) = latticePoints (Sum s a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Sum] using lattice_zero.symm
  | insert i s hi ih =>
    have hs (j : ι) (hj : j ∈ s) : Chamber (a j) := ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, ih hs, lattice_add (ha i (Finset.mem_insert_self i s)) (chamber_sum s a hs)]
    simp [Add, Sum, Shape.plus, Finset.sum_insert hi]

end Low48BentLattice

end Merged_Low48BentLattice

-- merged module Low48BentSupport
section Merged_Low48BentSupport

set_option autoImplicit false

namespace Low48BentSupport
open Polynomial MvPolynomial
open Low48BentLattice
open K1_13 (Row Shape InBox shape indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (genericCoeffs)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_2 (generic5 rawGraph denominator padded)
open K1_13_6_2_4 (Exponent)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight)
noncomputable section

def graph (p : Shape) : Cap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def lifted (p : Shape) (k : ℕ) : Cap :=
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), 2 + k * p.t⟩, min (1 + k) ((2 + k * p.t) / 2))

def Box (a : Cap) (D : GeoJets5) : Prop := ∀ m ∈ D.support, Allowed a m

theorem graph_chamber {p : Shape} (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) :
    Chamber (graph p) := by
  simp only [Chamber, graph]
  exact ⟨le_max_right _ _, by omega, by omega⟩

theorem lifted_chamber {p : Shape} (hb : p.j ≤ p.b) (hj : 3 * p.t + 3 ≤ p.j)
    {k : ℕ} (hk : 3 ≤ k) : Chamber (lifted p k) := by
  have hkB := Nat.mul_le_mul_left k (show p.j ≤ p.b from hb)
  have hkJ := Nat.mul_le_mul_left k (show 3 * p.t + 3 ≤ p.j from hj)
  rw [Nat.mul_add, ← Nat.mul_left_comm 3] at hkJ
  simp only [Chamber, lifted, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm k 2]
  have hmin : min (1 + k) ((2 + k * p.t) / 2) ≤ (2 + k * p.t) / 2 := min_le_right _ _
  omega


theorem raw_add {a : Cap} {x y : Exponent} (hx : Allowed a x) (hy : Allowed a y) :
    x + y ∈ latticePoints a := by
  simp only [coords, Finsupp.add_apply]
  unfold Allowed at hx hy
  omega

local notation "W" => MvPolynomial.weightedTotalDegree

private theorem box_of_weights (P : Row 5) {b j t d : ℕ}
    (hb : W 1 P ≤ b) (hj : W Fin.val P ≤ j) (ht : W topWeight P ≤ t)
    (hd : W fifthWeight P ≤ d) :
    Box (⟨b, j, t⟩, d) (generic5 P) := by
  intro m hm
  have hm' := MvPolynomial.support_map_subset genericCoeffs P hm
  have hb' := (le_weightedTotalDegree (1 : Fin 5 → ℕ) hm').trans hb
  have hj' := (le_weightedTotalDegree Fin.val hm').trans hj
  have ht' := (le_weightedTotalDegree topWeight hm').trans ht
  have hd' := (le_weightedTotalDegree fifthWeight hm').trans hd
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc] at hb' hj' ht' hd'
  simp only [Fin.sum_univ_four, Pi.one_apply, smul_eq_mul, mul_one] at hb'
  simp only [Fin.sum_univ_four, Fin.val_castSucc, smul_eq_mul, Fin.val_last] at hj'
  simp only [topWeight, Fin.lastCases_last, Fin.lastCases_castSucc] at ht'
  simp [Pi.single_apply] at ht'
  have hzero (i : Fin 4) : fifthWeight i.castSucc = 0 := by
    simp only [fifthWeight, Pi.single_apply, Fin.castSucc_ne_last, ite_false]
  simp only [hzero, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add,
    show fifthWeight (Fin.last 4) = 1 by decide, mul_one] at hd'
  change m 0 + m 1 + m 2 + m 3 + m 4 ≤ b ∧ m 1 + 2 * m 2 + 3 * m 3 + 4 * m 4 ≤ j ∧
    m 3 + 2 * m 4 ≤ t ∧ m 4 ≤ d
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hb'
  · simpa [Nat.mul_comm] using hj'
  · simpa [Nat.mul_comm] using ht'
  · exact hd'

local notation "wtDegree" => MvPolynomial.weightedTotalDegree

theorem chart_support {p : Shape} {g : Row 4}
    (hp : p.j ≤ p.b ∧ 3 * p.t ≤ p.j) (htpos : 1 ≤ p.t)
    (hG : InBox (shape g) p) :
    Box (graph p) (generic5 (rawGraph g)) ∧
      ∀ k : ℕ, Box (lifted p k) (generic5 (denominator g k)) ∧
        ∀ i ≤ k + 4, Box (lifted p k) (generic5 (padded g k i)) := by
  have ht : 1 ≤ p.t := htpos
  have hj : 3 ≤ p.j := by have := hp.2; change 3 * p.t ≤ p.j at this; omega
  have hb : 1 ≤ p.b := by have := hp.1; change p.j ≤ p.b at this; omega
  change g.totalDegree ≤ p.b ∧ indexDegree g ≤ p.j ∧
    g.degreeOf 3 ≤ p.t at hG
  have hTotal : wtDegree ((1 : Fin 5 → ℕ) ∘ Fin.castSucc) g ≤ p.b := by
    change wtDegree (1 : Fin 4 → ℕ) g ≤ p.b
    rw [weightedTotalDegree_one]
    exact hG.1
  have hIndex : wtDegree ((Fin.val : Fin 5 → ℕ) ∘ Fin.castSucc) g ≤ p.j := by
    change wtDegree (Fin.val : Fin 4 → ℕ) g ≤ p.j
    rw [← indexDegree_eq]
    exact hG.2.1
  have hTop : wtDegree (topWeight ∘ Fin.castSucc) g ≤ p.t := by
    have hw : topWeight ∘ Fin.castSucc = (Pi.single (3 : Fin 4) 1 : Fin 4 → ℕ) := by
      funext i
      simp [topWeight]
    rw [hw, weightedTotalDegree_piSingle]
    exact hG.2.2
  have hFifth : wtDegree (fifthWeight ∘ Fin.castSucc) g ≤ 0 := by
    have hw : fifthWeight ∘ Fin.castSucc = (0 : Fin 4 → ℕ) := by
      funext i
      change (Pi.single (Fin.last 4) 1 : Fin 5 → ℕ) i.castSucc = 0
      rw [Pi.single_apply, ite_eq_right (Fin.castSucc_ne_last i)]
    rw [hw]
    apply Finset.sup_le
    intro m _
    simp [Finsupp.weight_eq_sum]
  have wt := support_bounds (1 : Fin 5 → ℕ) 0 (fun _ => le_rfl) (by decide)
    (fun _ => le_rfl) hTotal hb
  have wi := support_bounds (Fin.val : Fin 5 → ℕ) 1 (fun i => by rfl) (by decide)
    (fun i => i.isLt.le) hIndex hj
  have ws := support_bounds topWeight 1 (fun i => by fin_cases i <;> decide) (by decide)
    (fun i => by fin_cases i <;> decide) hTop ht
  have wf := support_bounds fifthWeight 1 (fun i => by fin_cases i <;> decide) (by decide)
    (fun i => by fin_cases i <;> decide) hFifth (by decide)
  constructor
  · apply box_of_weights
    · exact (wt.1.trans (by simp only [add_zero]; exact le_max_left _ _))
    · exact wi.1
    · exact ws.1
    · exact wf.1
  · intro k
    have hJ : p.j - 3 + 1 = p.j - 2 := by omega
    have hT : p.t - 1 + 1 = p.t := by omega
    have wTotal := wt.2 k
    have wIndex := wi.2 k
    have wTop := ws.2 k
    have wFifth : wtDegree fifthWeight (denominator g k) ≤ 1 + k ∧
        (∀ i ≤ k + 4, wtDegree fifthWeight (padded g k i) ≤ 1 + k) := by
      simpa only [show fifthWeight (Fin.last 4) = 1 by decide,
        show fifthWeight ((3 : Fin 4).castSucc) = 0 by decide, Nat.sub_zero, zero_add, Nat.mul_one]
        using wf.2 k
    simp only [Pi.one_apply, add_zero] at wTotal
    change wtDegree Fin.val (denominator g k) ≤ 4 + k * (p.j - 3 + 1) ∧ _ at wIndex
    change wtDegree topWeight (denominator g k) ≤ 2 + k * (p.t - 1 + 1) ∧ _ at wTop
    simp only [show (Fin.last 4).val = 4 by rfl, show ((3 : Fin 4).castSucc).val = 3 by rfl,
      show topWeight (Fin.last 4) = 2 by decide, show topWeight ((3 : Fin 4).castSucc) = 1 by decide,
      hJ, hT] at wIndex wTop
    have box (P : Row 5) (h1 : wtDegree 1 P ≤ 1 + k * (p.b - 1))
        (h2 : wtDegree Fin.val P ≤ 4 + k * (p.j - 2)) (h3 : wtDegree topWeight P ≤ 2 + k * p.t)
        (h4 : wtDegree fifthWeight P ≤ 1 + k) :
        Box (lifted p k) (generic5 P) := by
      intro m hm
      have hs := box_of_weights P h1 h2 h3 h4 m hm
      have h4' : m 4 ≤ (2 + k * p.t) / 2 := by
        have htop := hs.2.2.1
        change m 3 + 2 * m 4 ≤ 2 + k * p.t at htop
        omega
      exact ⟨hs.1, hs.2.1, hs.2.2.1, le_min hs.2.2.2 h4'⟩
    exact ⟨box _ wTotal.1 wIndex.1 wTop.1 wFifth.1,
      fun i hi => box _ (wTotal.2 i hi) (wIndex.2 i hi) (wTop.2 i hi) (wFifth.2 i hi)⟩

end
end Low48BentSupport

end Merged_Low48BentSupport

end Merged6967_Low48BentSupport

section Merged6967_R6960FreeSource6960
set_option Elab.async false


set_option Elab.async false

-- merged module R6960FreeSource
section Merged_R6960FreeSource
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.FreeSource
open Finset
open K1_14 (Shape FX L shapeSum triangle slots)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (Bank debit)
open P1_7_5 (kept)
open HelperSource (cutoffCount WidthGuard)
def rawGain (s : Shape) (A h r : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => cutoffCount s A h r+j-q*(131071-h))
theorem gain_eq_raw (s : Shape) (A h r : ℕ) (hk : 1≤131071-h) :
    HelperSource.gain s A h r (s.J+1) 0 0 = rawGain s A h r := by
  unfold HelperSource.gain rawGain shapeSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
  have hjs : j<s.J+1 := Nat.lt_succ_of_le (hj'.trans (min_le_right _ _))
  have hjq : j≤q := hj'.trans (min_le_left _ _)
  have hweight : j≤q*(131071-h) := hjq.trans (by
    simpa using Nat.mul_le_mul_left q hk)
  have hwidth : s.m*A+j-q*(131071-h)-2*h*r = cutoffCount s A h r+j-q*(131071-h) := by
    unfold cutoffCount
    omega
  simp [HelperSource.coordinateGain, HelperSource.orderCap, Nat.div_eq_of_lt hjs,
    kept, slots, hwidth]
theorem buffered_fit (t : Bank) (A h r : ℕ) (width : WidthGuard t A h r) :
    (cutoffCount t.shape A h r-1)+2*h*r < t.shape.m*A := by
  change t.shape.B * (131071-h) < t.shape.m*A-2*h*r at width
  unfold cutoffCount
  omega
theorem nonzero_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r : ℕ) (hh : 0<h) (hk : h≤131070) (checked : P3_7_1.BankOK t)
    (width : WidthGuard t A h r) (positive : debit h t < rawGain t.shape A h r) :
    ∃ P ∈ evaluated Crt word t.shape (cutoffCount t.shape A h r-1), P≠0 := by
  let N := cutoffCount t.shape A h r
  have hw : t.shape.B*(131071-h)<N := width
  have hs : N-1+1=N := by omega
  have floor := HelperSource.crt_rank_floor Crt word t hh hk checked.nodes checked.moment.1
    checked.moment.2 (N-1) (by
      intro q hq j _
      rw [hs]
      exact (Nat.mul_le_mul_right _ hq).trans (hw.le.trans (Nat.le_add_right N j)))
  unfold K1_14_1.rawVolumeAt at floor
  rw [hs] at floor
  have hf : rawGain t.shape A h r ≤ debit h t +
      ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W) := floor
  exact HelperSource.nonzero_of_supply Crt word t.shape N (by omega)
def compressedSurplus (t : Bank) (A h r : ℕ) : ℤ :=
  (HelperSource.compressedPhase t.shape A h r (t.shape.J+1) 0 0 0 -
    HelperSource.compressedPhase t.shape A h r (t.shape.J+1) 0 0 1 : ℕ) - (debit h t : ℤ)
theorem compressedSurplus_eq (t : Bank) (A h r : ℕ) :
    compressedSurplus t A h r = HelperSource.surplus t A h r (t.shape.J+1) 0 0 := by
  unfold compressedSurplus HelperSource.surplus
  rw [HelperSource.gain_eq_compressed _ _ _ _ _ _ _ (Nat.succ_pos _)]
theorem rawGain_positive (t : Bank) (A lo h r : ℕ) (hl : lo≤h) (hk : h≤131070)
    (positive : 0<compressedSurplus t A lo r)
    (increasing : compressedSurplus t A lo r ≤ compressedSurplus t A (lo+1) r) :
    debit h t < rawGain t.shape A h r := by
  rw [compressedSurplus_eq t A lo r] at positive
  rw [compressedSurplus_eq t A lo r, compressedSurplus_eq t A (lo+1) r] at increasing
  rw [← gain_eq_raw _ _ _ _ (by omega)]
  exact HelperSource.surplus_positive _ _ _ _ _ _ _ _ hl hk positive increasing
#print axioms nonzero_row
#print axioms rawGain_positive
end Lower6960.FreeSource

end Merged_R6960FreeSource

-- merged module R6960FreeSource6960
section Merged_R6960FreeSource6960
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.FreeSource
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (Bank debit)
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open HelperSource (WidthGuard cutoffCount)
private def freeStages : List (ℕ × Bank) :=
  [
   (0,⟨⟨95,132,29,984⟩,27270840320,8956669⟩),
   (1,⟨⟨104,144,32,1074⟩,35837181952,12729182⟩),
   (2,⟨⟨101,140,31,1384⟩,32807845888,11360420⟩),
   (3,⟨⟨124,172,38,1243⟩,60131901440,25559185⟩),
   (4,⟨⟨118,164,36,1593⟩,51745914880,21071762⟩),
   (5,⟨⟨128,177,39,1665⟩,65782415360,28566713⟩),
   (7,⟨⟨158,219,48,1653⟩,122606059520,66089082⟩),
   (10,⟨⟨178,247,54,2036⟩,174543339520,106278128⟩),
   (16,⟨⟨214,297,67,2918⟩,309161623552,226287616⟩),
   (10,⟨⟨178,247,55,2006⟩,176946151424,107778015⟩),
   (20,⟨⟨250,347,78,3255⟩,490108092416,418829988⟩),
   (32,⟨⟨378,524,119,3993⟩,1694923489280,2177690453⟩),
   (31,⟨⟨345,478,108,4305⟩,1284701945856,1504282153⟩),
   (44,⟨⟨470,651,148,5322⟩,3250957582336,5176394869⟩),
   (73,⟨⟨749,1038,236,7729⟩,13115102855168,33302514887⟩),
   (76,⟨⟨722,1000,227,8859⟩,11730838618112,28660654832⟩),
   (103,⟨⟨1011,1401,318,10575⟩,32159926059008,110150758881⟩)
  ]
private def stage (i : Fin 17) : ℕ × Bank := freeStages.get ⟨i.val,i.isLt⟩
def reserve (i : Fin 17) : ℕ := (stage i).1
def bank (i : Fin 17) : Bank := (stage i).2
def cutoff (h : ℕ) (i : Fin 17) : ℕ :=
  cutoffCount (bank i).shape 179818 h (reserve i)-1
structure Checked (i : Fin 17) : Prop where
  debit_ok : P3_7_1.BankOK (bank i)
  reserve_ok : 2*(reserve i)≤(bank i).shape.B
  width_first : WidthGuard (bank i) 179818 2359 (reserve i)
  first : 0<compressedSurplus (bank i) 179818 2359 (reserve i)
  next : compressedSurplus (bank i) 179818 2359 (reserve i) ≤
    compressedSurplus (bank i) 179818 2360 (reserve i)
private theorem checked_from_values (i : Fin 17) (db : P3_7_1.BankOK (bank i))
    (res : 2*(reserve i)≤(bank i).shape.B)
    (width : WidthGuard (bank i) 179818 2359 (reserve i))
    {x y : ℤ} (first : compressedSurplus (bank i) 179818 2359 (reserve i) = x)
    (next : compressedSurplus (bank i) 179818 2360 (reserve i) = y)
    (pos : 0<x) (inc : x≤y) : Checked i := by
  refine ⟨db,res,width,?_,?_⟩
  · rwa [first]
  · rwa [first,next]
private theorem moment_0 : momentEstimate 132 29 = 8956669 := by
  refine moment_from_blocks
    [(128,8556490),(33,400179)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_0 : Checked 0 := by
  refine checked_from_values 0
    (P3_7_1.checked (bank 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_0)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 39105453480) (y := 147368479950) rfl rfl (by decide) (by decide)
private theorem moment_1 : momentEstimate 144 32 = 12729182 := by
  refine moment_from_blocks
    [(128,11505698),(48,1223484)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_1 : Checked 1 := by
  refine checked_from_values 1
    (P3_7_1.checked (bank 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 16080159600) (y := 179886010800) rfl rfl (by decide) (by decide)
private theorem moment_2 : momentEstimate 140 31 = 11360420 := by
  refine moment_from_blocks
    [(128,10480802),(43,879618)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_2 : Checked 2 := by
  refine checked_from_values 2
    (P3_7_1.checked (bank 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 45424332520) (y := 296921840000) rfl rfl (by decide) (by decide)
private theorem moment_3 : momentEstimate 172 38 = 25559185 := by
  refine moment_from_blocks
    [(128,19318585),(82,6240600)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_3 : Checked 3 := by
  refine checked_from_values 3
    (P3_7_1.checked (bank 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 38739721220) (y := 389499003070) rfl rfl (by decide) (by decide)
private theorem moment_4 : momentEstimate 164 36 = 21071762 := by
  refine moment_from_blocks
    [(128,16874923),(72,4196839)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_4 : Checked 4 := by
  refine checked_from_values 4
    (P3_7_1.checked (bank 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 4668194776) (y := 508683911040) rfl rfl (by decide) (by decide)
private theorem moment_5 : momentEstimate 177 39 = 28566713 := by
  refine moment_from_blocks
    [(128,20817690),(88,7749023)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_5 : Checked 5 := by
  refine checked_from_values 5
    (P3_7_1.checked (bank 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 19243192976) (y := 697293054500) rfl rfl (by decide) (by decide)
private theorem moment_6 : momentEstimate 219 48 = 66089082 := by
  refine moment_from_blocks
    [(128,34759620),(128,31294933),(11,34529)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_6 : Checked 6 := by
  refine checked_from_values 6
    (P3_7_1.checked (bank 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_6)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 297300486056) (y := 1485042700850) rfl rfl (by decide) (by decide)
private theorem moment_7 : momentEstimate 247 54 = 106278128 := by
  refine moment_from_blocks
    [(128,44971630),(128,59409708),(45,1896790)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_7 : Checked 7 := by
  refine checked_from_values 7
    (P3_7_1.checked (bank 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_7)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 216918156147) (y := 2721486326790) rfl rfl (by decide) (by decide)
private theorem moment_8 : momentEstimate 297 67 = 226287616 := by
  refine moment_from_blocks
    [(128,65190835),(128,134418307),(108,26678474)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_8 : Checked 8 := by
  refine checked_from_values 8
    (P3_7_1.checked (bank 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 180054171528) (y := 9016997781960) rfl rfl (by decide) (by decide)
private theorem moment_9 : momentEstimate 247 55 = 107778015 := by
  refine moment_from_blocks
    [(128,45360574),(128,60399763),(46,2017678)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_9 : Checked 9 := by
  refine checked_from_values 9
    (P3_7_1.checked (bank 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 425776215186) (y := 2895778916640) rfl rfl (by decide) (by decide)
private theorem moment_10 : momentEstimate 347 78 = 418829988 := by
  refine moment_from_blocks
    [(128,85234680),(128,227560448),(128,103935818),(41,2099042)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_10 : Checked 10 := by
  refine checked_from_values 10
    (P3_7_1.checked (bank 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 1185266248188) (y := 18152762832160) rfl rfl (by decide) (by decide)
private theorem moment_11 : momentEstimate 524 119 = 2177690453 := by
  refine moment_from_blocks
    [(128,153341750),(128,658287360),(128,798862080),(128,477441955),(128,89753646),(3,3662)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_11 : Checked 11 := by
  refine checked_from_values 11
    (P3_7_1.checked (bank 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_11)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 9823168495924) (y := 93350624269160) rfl rfl (by decide) (by decide)
private theorem moment_12 : momentEstimate 478 108 = 1504282153 := by
  refine moment_from_blocks
    [(128,136459825),(128,534570880),(128,570357888),(128,246975702),(74,15917858)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_12 : Checked 12 := by
  refine checked_from_values 12
    (P3_7_1.checked (bank 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 5666047301100) (y := 79843204090459) rfl rfl (by decide) (by decide)
private theorem moment_13 : momentEstimate 651 148 = 5176394869 := by
  refine moment_from_blocks
    [(128,198825120),(128,1013136261),(128,1532425664),(128,1427478906),(128,805738851),(128,196970451),(31,1819616)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_13 : Checked 13 := by
  refine checked_from_values 13
    (P3_7_1.checked (bank 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_13)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 14911338072722) (y := 292832097713812) rfl rfl (by decide) (by decide)
private theorem moment_14 : momentEstimate 1038 236 = 33302514887 := by
  refine moment_from_blocks
    [(128,337278240),(128,2057177553),(128,4372358016),(128,5878965120),(128,6391522176),(128,5910029184),(128,4481522406),(128,2652304705),(128,1067311419),(122,154046068)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_14 : Checked 14 := by
  refine checked_from_values 14
    (P3_7_1.checked (bank 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 118833819505000) (y := 2404987697168555) rfl rfl (by decide) (by decide)
private theorem moment_15 : momentEstimate 1000 227 = 28660654832 := by
  refine moment_from_blocks
    [(128,323683360),(128,1961263575),(128,4071116928),(128,5361750144),(128,5696082048),(128,5074112640),(128,3602477140),(128,1924849303),(128,609309184),(75,36010510)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_15 : Checked 15 := by
  refine checked_from_values 15
    (P3_7_1.checked (bank 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_15)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 111384553979680) (y := 2799099570337160) rfl rfl (by decide) (by decide)
private theorem moment_16 : momentEstimate 1401 318 = 110150758881 := by
  refine moment_from_blocks
    [(128,467145120),(128,2955305376),(128,7120936534),(128,11215447936),(128,14016849792),(128,15480268672),(128,15605704576),(128,14393157504),(128,11866159893),(128,8558093849),(128,5277857273),(128,2505173440),(128,667990464),(55,20668452)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_16 : Checked 16 := by
  refine checked_from_values 16
    (P3_7_1.checked (bank 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_16)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 254959084826040) (y := 10579378014995976) rfl rfl (by decide) (by decide)
theorem checked (i : Fin 17) : Checked i := by
  fin_cases i
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact checked_9
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
theorem shape_guards (i : Fin 17) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*179818<K1.p := by
  fin_cases i <;> decide +kernel
theorem free_width {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    WidthGuard (bank i) 179818 h (reserve i) :=
  HelperSource.width_at_height _ _ 2359 _ _ lo (by omega)
    (checked i).reserve_ok (checked i).width_first
theorem cutoff_fit {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*179818 :=
  buffered_fit _ _ _ _ (free_width lo hi i)
theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have c := checked i
  exact nonzero_row Crt word (bank i) 179818 (reserve i) (by omega) (by omega) c.debit_ok
    (free_width lo hi i) (rawGain_positive _ _ 2359 _ _ lo (by omega) c.first c.next)
#print axioms checked
#print axioms cutoff_fit
#print axioms free_rows
end Lower6960.FreeSource

end Merged_R6960FreeSource6960

end Merged6967_R6960FreeSource6960

section Merged6967_Low6966Inventory
set_option Elab.async false








set_option Elab.async false











-- merged module R6960Low6966Inventory
section Merged_R6960Low6966Inventory
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace LowProfile6966
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical
abbrev anchorCutoff : ℕ := 106*agreement-1+58
def fullCap (top : ℕ) : Shape := ⟨142, 58, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 142 ∧ (∑ i, (a i).j) ≤ 58 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤142-top ∧ indexDegree g≤58-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 15) ∧ TrueWeightLE f anchorCutoff
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 142 at hb
    change (anchorLead P).totalDegree ≤ 142 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 58 at hj
    change indexDegree (anchorLead P) ≤ 58 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
end FactorCover
structure Inventory (Γ : Finset K) (s : K→(Polynomial K)) where
  top : ℕ
  top_le : top≤15
  g : Row 3
  lower : LowerRow top g
  low : Finset K
  low_sub : low⊆Γ
  low_vanish : ∀ γ∈low,atJet g (extend (s γ))=0
  n : ℕ
  factor : Fin n→Row 4
  small : ∀ i,SmallFactor (factor i)
  different : ∀ i j,i≠j → ¬Associated (factor i) (factor j)
  fits : Fits top (fun i=>shape (factor i))
  active : (∑ i,activeDegree (factor i))≤178
  order : Fin n→ℕ
  layers : LayerBudget (fun i=>shape (factor i)) order
  proper : ∀ i,0<order i → ProperCut (factor i) Γ s (order i)
  zeros : Finset (Fin n)
  zero_iff : ∀ i,i∈zeros ↔ order i=0
  retained : zeros=∅ ∨ (Low6966Retained.Box (Low6966Retained.combined (fun i=>shape (factor i)) zeros) ∧
    1≤(Low6966Retained.combined (fun i=>shape (factor i)) zeros).t ∧
    (Low6966Retained.combined (fun i=>shape (factor i)) zeros).t≤2)
  pieces : Fin n→Finset K
  piece_sub : ∀ i,pieces i⊆Γ
  on_factor : ∀ i γ,γ∈pieces i → OnFactor (factor i) (extend (s γ))
  off_retained : ∀ i∉zeros,∀ γ∈pieces i,atJet (∏ j∈zeros,factor j) (extend (s γ))≠0
  book : Finset K
  book_cap : book.card≤56000
  fat : Low6966Fat.FatEquations
  fat_at : ∀ i γ,γ∈pieces i → Low6966Fat.Holds fat (extend (s γ))
  cover_count : Γ.card ≤ book.card+low.card+∑ i,(pieces i).card
theorem inventory_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179759 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2316) :
    Nonempty (Inventory Γ F.scalar) := by
  obtain ⟨P,hP,hbox,hact,weight,vanish⟩ := Anchor6966.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [← differentialWeight_eq,←differentialWeightedDegree]
    exact weight
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := KoalaRetainedCut.anchor_factors hP
  let top := (shape P).t
  have htop : top≤15 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [MvPolynomial.weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [MvPolynomial.weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ 178 :=
    (MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ)
      Finset.univ f hP prodDvd).trans ((activeFits_iff P 178).mp hact)
  have hchar (i : Fin n) : (shape (f i)).t<K1.p := (small i).2.2.1.2.2.trans_lt (by decide)
  have hm := Low6966Order.messages_of_family M F hi
  obtain ⟨ord,layers,proper⟩ := Low6966Order.proper_layers hm (fun i=>(small i).1)
    (fun i=>(small i).2.1) hchar different
  let zeros := (univ : Finset (Fin n)).filter fun i=>ord i=0
  have zero_iff (i : Fin n) : i∈zeros ↔ ord i=0 := by simp [zeros]
  have retained := Low6966Retained.no_cut_shape _ _ fits.1 layers zeros
    (fun i hi=>(zero_iff i).mp hi)
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  obtain ⟨low,piece,lowSub,lowOn,sub,on,off,total⟩ := KoalaRetainedCut.priority_pieces
    (fun i => (factors i).2.2) F.scalar book zeros (fun γ hγ => covers _ (vanish γ hγ))
  exact ⟨⟨top,htop,K1_13_1.anchorLead P,lower_of_anchor P hP hbox hw,low,lowSub,lowOn,
    n,f,small,different,fits,active,ord,layers,proper,zeros,zero_iff,retained,piece,sub,
    (fun i γ hγ=>(on i γ hγ).2),off,book,booked,E,(fun i γ hγ=>fat γ (sub i hγ) (on i γ hγ).1),total⟩⟩
#print axioms inventory_of_family
end
end LowProfile6966

end Merged_R6960Low6966Inventory

end Merged6967_Low6966Inventory
