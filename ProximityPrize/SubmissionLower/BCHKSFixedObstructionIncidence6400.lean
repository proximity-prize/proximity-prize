import ProximityPrize.SubmissionLower.BCHKSShiftedExactRoot6400

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators

set_option maxRecDepth 100000

/-- Incidence uniformization for fixed polynomial obstructions.  If every
agreement either belongs to a zero obstruction or is a root of a nonzero
obstruction, the aggregate root budget forces one challenge to have more than
`k` zero-obstruction agreements. -/
theorem exists_many_zero_obstruction_agreements
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (n a k D : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, a ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z,
      G i = 0 ∨ (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ D)
    (hcount : n * D < (a - k) * T.card) :
    ∃ z ∈ T, k + 1 ≤ ((A z).filter fun i => G i = 0).card := by
  classical
  let Bad : F → Finset I := fun z =>
    (A z).filter fun i => G i ≠ 0
  by_contra hnone
  have hsmall : ∀ z ∈ T,
      ((A z).filter fun i => G i = 0).card ≤ k := by
    intro z hz
    by_contra hlarge
    apply hnone
    exact ⟨z, hz, by omega⟩
  have hbadrow : ∀ z ∈ T, a - k ≤ (Bad z).card := by
    intro z hz
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := A z) (fun i => G i = 0)
    have hsplit' :
        ((A z).filter fun i => G i = 0).card + (Bad z).card =
          (A z).card := by
      simpa only [Bad, ne_eq] using hsplit
    have hA := hrow z hz
    have hZ := hsmall z hz
    change a - k ≤ ((A z).filter fun i => G i ≠ 0).card
    change a - k ≤ (Bad z).card
    omega
  have hfiber : ∀ i : I,
      (T.filter fun z => i ∈ Bad z).card ≤ D := by
    intro i
    by_cases hGi : G i = 0
    · have hempty : (T.filter fun z => i ∈ Bad z) = ∅ := by
        ext z
        simp [Bad, hGi]
      rw [hempty]
      simp
    · have hsub : (T.filter fun z => i ∈ Bad z) ⊆
          (G i).roots.toFinset := by
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        have hiBad := Finset.mem_filter.mp hz'.2
        have hvanish := hroot z hz'.1 i hiBad.1
        have heval : (G i).eval z = 0 := hvanish.resolve_left hGi
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hGi]
        exact heval
      calc
        (T.filter fun z => i ∈ Bad z).card
            ≤ (G i).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ (G i).roots.card := Multiset.toFinset_card_le _
        _ ≤ (G i).natDegree := Polynomial.card_roots' _
        _ ≤ D := hdegree i
  have hlower : (a - k) * T.card ≤
      ∑ z ∈ T, (Bad z).card := by
    calc
      (a - k) * T.card = ∑ z ∈ T, (a - k) := by simp [mul_comm]
      _ ≤ ∑ z ∈ T, (Bad z).card := Finset.sum_le_sum hbadrow
  have hupper : (∑ z ∈ T, (Bad z).card) ≤ n * D := by
    rw [sum_card_eq_sum_fiber_card T Bad]
    calc
      (∑ i : I, (T.filter fun z => i ∈ Bad z).card)
          ≤ ∑ _i : I, D := Finset.sum_le_sum fun i _ => hfiber i
      _ = n * D := by simp [hn]
  exact (not_lt_of_ge (hlower.trans hupper)) hcount

/-- Exact score-64 incidence arithmetic. -/
theorem score6400_fixed_obstruction_incidence_numeric
    (tcard : ℕ) (ht : 8063658 ≤ tcard) :
    262144 * 1670075 < 54293 * tcard := by
  norm_num at ht ⊢
  nlinarith

theorem score6400_regular_plus_incidence_numeric :
    497808089957772 + 8063658 = 497808098021430 := by
  norm_num

/-- The sharper transposed incidence argument.  A coordinate agreement fiber
larger than the degree of its fixed obstruction forces that obstruction to be
the zero polynomial. -/
theorem many_zero_obstructions_of_many_large_fibers
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (n e k D : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, n - e ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ D)
    (hcount : (n - e - k) * T.card > (n - k) * D) :
    k + 1 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  classical
  let Large : Finset I := Finset.univ.filter fun i : I =>
    D < (T.filter fun z => i ∈ A z).card
  have hlarge : k + 1 ≤ Large.card := by
    exact many_large_fibers T A n e k D hn hrow hcount
  have hsub : Large ⊆ Finset.univ.filter fun i : I => G i = 0 := by
    intro i hi
    have hiLarge : D < (T.filter fun z => i ∈ A z).card :=
      (Finset.mem_filter.mp hi).2
    have hGi : G i = 0 := by
      by_contra hne
      have hfiber : (T.filter fun z => i ∈ A z) ⊆
          (G i).roots.toFinset := by
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hroot z hz'.1 i hz'.2
      have hcard : (T.filter fun z => i ∈ A z).card ≤ D := by
        calc
          (T.filter fun z => i ∈ A z).card
              ≤ (G i).roots.toFinset.card := Finset.card_le_card hfiber
          _ ≤ (G i).roots.card := Multiset.toFinset_card_le _
          _ ≤ (G i).natDegree := Polynomial.card_roots' _
          _ ≤ D := hdegree i
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hGi⟩
  exact hlarge.trans (Finset.card_le_card hsub)

/-- Exact score-64 arithmetic for the transposed fixed-obstruction count. -/
theorem score6400_fixed_obstruction_large_fibers_numeric
    (tcard : ℕ) (ht : 4031860 ≤ tcard) :
    (262144 - 76780 - 131071) * tcard >
      (262144 - 131071) * 1670075 := by
  norm_num at ht ⊢
  nlinarith

theorem score6400_regular_plus_large_fibers_numeric :
    497808089957772 + 4031860 = 497808093989632 := by
  norm_num

/-- The degree-weighted fixed-factor fibre is strong enough to make at least
`185331` coordinate obstructions identically zero.  Keeping the selected
outer degree `d` in both the fibre lower bound and the obstruction degree is
what makes the cancellation exact. -/
theorem score6400_weighted_fixed_factor_incidence_numeric
    (tcard d D : ℕ) (hT : 2266 * D * d < tcard) :
    (262144 - 76780 - 185330) * tcard >
      (262144 - 185330) * (d * D) := by
  have hscaled : 34 * (2266 * D * d) < 34 * tcard :=
    Nat.mul_lt_mul_of_pos_left hT (by norm_num)
  by_cases hzero : d * D = 0
  · norm_num [hzero] at ⊢
    omega
  · have hpos : 0 < d * D := Nat.pos_of_ne_zero hzero
    have hcoeff : 76814 * (d * D) < 77044 * (d * D) :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
    norm_num at ⊢
    calc
      76814 * (d * D) < 77044 * (d * D) := hcoeff
      _ = 34 * (2266 * D * d) := by ring
      _ < 34 * tcard := hscaled

/-- Coordinate form of the weighted fixed-factor incidence estimate. -/
theorem many_zero_obstructions_of_weighted_fixed_factor_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (d D : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ d * D)
    (hT : 2266 * D * d < T.card) :
    185331 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  apply many_zero_obstructions_of_many_large_fibers
    T A G 262144 76780 185330 (d * D) hn
  · intro z hz
    simpa using hrow z hz
  · exact hroot
  · exact hdegree
  · exact score6400_weighted_fixed_factor_incidence_numeric
      T.card d D hT

/-- The score-64 fixed-factor count with the large fibres retained.

The factor-selection threshold is strong enough to ask for nine times the
ordinary obstruction degree and still obtain `185058` coordinates.  This is
the form needed at a simple affine identity coordinate: the same fibre then
pays the linear-factor Hensel bound, rather than merely proving that the
coordinate obstruction is identically zero. -/
theorem many_large_zero_obstruction_fibers_of_weighted_fixed_factor_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (d D : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ d * D)
    (hT : 2266 * D * d < T.card) :
    ∃ Large : Finset I,
      185058 ≤ Large.card ∧
      (∀ i ∈ Large, 9 * (d * D) <
        (T.filter fun z ↦ i ∈ A z).card) ∧
      ∀ i ∈ Large, G i = 0 := by
  classical
  let Large : Finset I := Finset.univ.filter fun i : I ↦
    9 * (d * D) < (T.filter fun z ↦ i ∈ A z).card
  have hcount :
      (262144 - 76780 - 185057) * T.card >
        (262144 - 185057) * (9 * (d * D)) := by
    have hscaled : 307 * (2266 * D * d) < 307 * T.card :=
      Nat.mul_lt_mul_of_pos_left hT (by norm_num)
    by_cases hzero : d * D = 0
    · rcases Nat.mul_eq_zero.mp hzero with hd | hD
      · simp [hd] at hT ⊢
        omega
      · simp [hD] at hT ⊢
        omega
    · have hpos : 0 < d * D := Nat.pos_of_ne_zero hzero
      have hcoeff : 693783 * (d * D) < 695662 * (d * D) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
      calc
        (262144 - 185057) * (9 * (d * D)) =
            693783 * (d * D) := by norm_num; ring
        _ < 695662 * (d * D) := hcoeff
        _ = 307 * (2266 * D * d) := by ring
        _ < 307 * T.card := hscaled
  have hlarge : 185058 ≤ Large.card := by
    simpa [Large] using many_large_fibers T A 262144 76780 185057
      (9 * (d * D)) hn (fun z hz ↦ by simpa using hrow z hz) hcount
  refine ⟨Large, hlarge, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    have hfiber : d * D < (T.filter fun z ↦ i ∈ A z).card := by
      have hlargeFiber := (Finset.mem_filter.mp hi).2
      by_cases hzero : d * D = 0
      · simpa [hzero] using hlargeFiber
      · have hpos : 0 < d * D := Nat.pos_of_ne_zero hzero
        have : d * D ≤ 9 * (d * D) := by omega
        exact this.trans_lt hlargeFiber
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (G i) (T.filter fun z ↦ i ∈ A z)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact hroot z hz'.1 i hz'.2
    · exact (hdegree i).trans_lt hfiber

/-- If the selected outer factor has degree at least two, direct affine
substitution into the coordinate parent has degree `D`, rather than the
coarser `d * D` owner bound.  The same weighted factor fibre then forces at
least `185348` coordinate identities. -/
theorem many_direct_zero_obstructions_of_weighted_fixed_factor_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (d D : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ D)
    (hd : 2 ≤ d)
    (hT : 2266 * D * d < T.card) :
    185348 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  have hbase : 4532 * D ≤ 2266 * D * d := by
    calc
      4532 * D = 2266 * D * 2 := by ring
      _ ≤ 2266 * D * d := Nat.mul_le_mul_left (2266 * D) hd
  have hTD : 4532 * D < T.card := hbase.trans_lt hT
  apply many_zero_obstructions_of_many_large_fibers
    T A G 262144 76780 185347 D hn
  · intro z hz
    simpa using hrow z hz
  · exact hroot
  · exact hdegree
  · have hscaled : 17 * (4532 * D) < 17 * T.card :=
      Nat.mul_lt_mul_of_pos_left hTD (by norm_num)
    by_cases hD : D = 0
    · simp [hD] at hT ⊢
      omega
    · have hpos : 0 < D := Nat.pos_of_ne_zero hD
      have hcoeff : 76797 * D < 77044 * D :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
      norm_num at ⊢
      calc
        76797 * D < 77044 * D := hcoeff
        _ = 17 * (4532 * D) := by ring
        _ < 17 * T.card := hscaled

end ProximityPrize.SubmissionLower
