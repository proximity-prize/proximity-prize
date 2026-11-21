import ProximityPrize.SubmissionLower.PortLow7

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

theorem chamber_add {a b : Cap} (ha : Chamber a) (hb : Chamber b) : Chamber (Add a b) := by
  obtain ⟨ha₁, ha₂, ha₃⟩ := ha
  obtain ⟨hb₁, hb₂, hb₃⟩ := hb
  simp only [Chamber, Add, Shape.plus]
  omega

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
