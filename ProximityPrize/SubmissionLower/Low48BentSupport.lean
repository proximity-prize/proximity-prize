import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic

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
