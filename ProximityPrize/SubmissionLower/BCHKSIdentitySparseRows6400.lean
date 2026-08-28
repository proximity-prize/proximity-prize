import ProximityPrize.SubmissionLower.BCHKSCoordinateOwners6400
import ProximityPrize.SubmissionLower.BCHKSSparseDirtyQuadratic6400

/-!
# Sparse rows from a large fixed-identity locus

This is the incidence complement to the fixed-obstruction count.  Once many
coordinate obstruction polynomials vanish identically, it bounds the total
number of missing identity coordinates over all challenge rows.  The point is
that every agreement outside the identity locus is still charged to the root
budget of a nonzero obstruction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 100000

/-- If `Zero` is the locus of identically-zero coordinate obstructions, then
the aggregate number of coordinates of `Zero` missed by the agreement rows is
controlled by the root budget on its complement.

The deliberately subtraction-free conclusion is convenient for exact natural
number arithmetic at the score-64 endpoint. -/
theorem zero_obstruction_missing_incidence
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (n w D : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, w ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ D) :
    let Zero : Finset I := Finset.univ.filter fun i => G i = 0
    let Missing : F → Finset I := fun z => Zero \ A z
    (∑ z ∈ T, (Missing z).card) + w * T.card ≤
      Zero.card * T.card + (n - Zero.card) * D := by
  classical
  let Zero : Finset I := Finset.univ.filter fun i => G i = 0
  let NonzeroAgreement : F → Finset I := fun z =>
    (A z).filter fun i => G i ≠ 0
  let Missing : F → Finset I := fun z => Zero \ A z
  have hrowBound : ∀ z ∈ T,
      (Missing z).card + w ≤ Zero.card + (NonzeroAgreement z).card := by
    intro z hz
    have hzeroInter : (A z).filter (fun i => G i = 0) = A z ∩ Zero := by
      ext i
      simp [Zero]
    have hAsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := A z) (fun i => G i = 0)
    have hZsplit := Finset.card_sdiff_add_card_inter Zero (A z)
    have hAcard :
        (A z ∩ Zero).card + (NonzeroAgreement z).card = (A z).card := by
      simpa only [NonzeroAgreement, ne_eq, hzeroInter] using hAsplit
    have hZcard :
        (Missing z).card + (Zero ∩ A z).card = Zero.card := by
      simpa only [Missing] using hZsplit
    have hinter : (A z ∩ Zero).card = (Zero ∩ A z).card := by
      rw [Finset.inter_comm]
    have hw := hrow z hz
    omega
  have hmissingRows :
      (∑ z ∈ T, (Missing z).card) + w * T.card ≤
        Zero.card * T.card + ∑ z ∈ T, (NonzeroAgreement z).card := by
    calc
      (∑ z ∈ T, (Missing z).card) + w * T.card =
          ∑ z ∈ T, ((Missing z).card + w) := by
            simp [Finset.sum_add_distrib, mul_comm]
      _ ≤ ∑ z ∈ T, (Zero.card + (NonzeroAgreement z).card) :=
        Finset.sum_le_sum hrowBound
      _ = Zero.card * T.card +
          ∑ z ∈ T, (NonzeroAgreement z).card := by
            simp [Finset.sum_add_distrib, mul_comm]
  have hfiber : ∀ i : I,
      (T.filter fun z => i ∈ NonzeroAgreement z).card ≤
        if G i = 0 then 0 else D := by
    intro i
    by_cases hGi : G i = 0
    · have hempty : (T.filter fun z => i ∈ NonzeroAgreement z) = ∅ := by
        ext z
        simp [NonzeroAgreement, hGi]
      simp [hempty, hGi]
    · have hsub : (T.filter fun z => i ∈ NonzeroAgreement z) ⊆
          (G i).roots.toFinset := by
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        have hi := Finset.mem_filter.mp hz'.2
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hGi]
        exact hroot z hz'.1 i hi.1
      simp only [hGi, if_false]
      calc
        (T.filter fun z => i ∈ NonzeroAgreement z).card
            ≤ (G i).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ (G i).roots.card := Multiset.toFinset_card_le _
        _ ≤ (G i).natDegree := Polynomial.card_roots' _
        _ ≤ D := hdegree i
  have hnonzero :
      (∑ z ∈ T, (NonzeroAgreement z).card) ≤
        (n - Zero.card) * D := by
    rw [sum_card_eq_sum_fiber_card T NonzeroAgreement]
    let NZ : Finset I := Finset.univ.filter fun i => G i ≠ 0
    have hNZcard : NZ.card = Fintype.card I - Zero.card := by
      have hparts := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset I)) (p := fun i => G i = 0)
      have hnot : (Finset.univ.filter fun i : I => ¬G i = 0) = NZ := by
        ext i
        simp [NZ]
      change Zero.card + (Finset.univ.filter fun i : I => ¬G i = 0).card =
        Fintype.card I at hparts
      rw [hnot] at hparts
      omega
    calc
      (∑ i : I, (T.filter fun z => i ∈ NonzeroAgreement z).card)
          ≤ ∑ i : I, (if G i = 0 then 0 else D) :=
        Finset.sum_le_sum fun i _ => hfiber i
      _ = (Finset.univ.filter fun i : I => ¬G i = 0).card * D := by
        rw [Finset.sum_ite]
        simp [mul_comm]
      _ = NZ.card * D := by simp [NZ]
      _ = (Fintype.card I - Zero.card) * D := by rw [hNZcard]
      _ = (n - Zero.card) * D := by rw [hn]
  exact hmissingRows.trans (Nat.add_le_add_left hnonzero _)

/-- Markov extraction from `zero_obstruction_missing_incidence`.  The numeric
budget is kept in the same subtraction-free form as the preceding theorem. -/
theorem exists_many_sparse_identity_rows
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (n w D b keep : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, w ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ D)
    (hkeep : keep ≤ T.card)
    (hbudget :
      let Zero : Finset I := Finset.univ.filter fun i => G i = 0
      Zero.card * T.card + (n - Zero.card) * D <
        w * T.card + (b + 1) * (T.card - keep)) :
    let Zero : Finset I := Finset.univ.filter fun i => G i = 0
    ∃ Good : Finset F,
      Good ⊆ T ∧ keep < Good.card ∧
        ∀ z ∈ Good, (Zero \ A z).card ≤ b := by
  classical
  let Zero : Finset I := Finset.univ.filter fun i => G i = 0
  let Missing : F → Finset I := fun z => Zero \ A z
  let Good : Finset F := T.filter fun z => (Missing z).card ≤ b
  let Bad : Finset F := T.filter fun z => b < (Missing z).card
  have hsum := zero_obstruction_missing_incidence
    T A G n w D hn hrow hroot hdegree
  change (∑ z ∈ T, (Missing z).card) + w * T.card ≤
    Zero.card * T.card + (n - Zero.card) * D at hsum
  have hbadLower : (b + 1) * Bad.card ≤
      ∑ z ∈ T, (Missing z).card := by
    calc
      (b + 1) * Bad.card = ∑ z ∈ Bad, (b + 1) := by simp [mul_comm]
      _ ≤ ∑ z ∈ Bad, (Missing z).card := by
        apply Finset.sum_le_sum
        intro z hz
        exact (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ T, (Missing z).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
  have hpartition : Good.card + Bad.card = T.card := by
    simpa only [Good, Bad, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (p := fun z => (Missing z).card ≤ b))
  have hGood : keep < Good.card := by
    by_contra hsmall
    have hbadCard : T.card - keep ≤ Bad.card := by omega
    have hlower :
        w * T.card + (b + 1) * (T.card - keep) ≤
          (∑ z ∈ T, (Missing z).card) + w * T.card := by
      simpa [Nat.add_comm] using Nat.add_le_add_right
        ((Nat.mul_le_mul_left (b + 1) hbadCard).trans hbadLower)
        (w * T.card)
    exact (not_lt_of_ge (hlower.trans hsum)) (by simpa [Zero] using hbudget)
  refine ⟨Good, Finset.filter_subset _ _, hGood, ?_⟩
  intro z hz
  exact (Finset.mem_filter.mp hz).2

/-- Sparse identity rows directly force a polynomial pencil.  The embedding
`omega` only transports coordinate indices to their distinct RS evaluation
points; no algebraic branch choice is used. -/
theorem sparse_identity_rows_force_pencil
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F)
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (sect : F → F[X]) (U₀ U₁ : I → F)
    (n w D k b keep : ℕ)
    (hn : Fintype.card I = n)
    (hrow : ∀ z ∈ T, w ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hGdegree : ∀ i, (G i).natDegree ≤ D)
    (hsectDegree : ∀ z ∈ T, (sect z).natDegree ≤ k)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (sect z).eval (omega i) = U₀ i + z * U₁ i)
    (hkeep : keep ≤ T.card) (hkeepPos : 1 ≤ keep)
    (hwide :
      let Zero : Finset I := Finset.univ.filter fun i => G i = 0
      k + 3 * b < Zero.card)
    (hbudget :
      let Zero : Finset I := Finset.univ.filter fun i => G i = 0
      Zero.card * T.card + (n - Zero.card) * D <
        w * T.card + (b + 1) * (T.card - keep)) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ keep < Good.card ∧
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  classical
  let Zero : Finset I := Finset.univ.filter fun i => G i = 0
  have hZeroPos : 0 < Zero.card := by
    change k + 3 * b < Zero.card at hwide
    omega
  letI : Nonempty I := ⟨(Finset.card_pos.mp hZeroPos).choose⟩
  obtain ⟨Good, hGoodT, hGoodCard, hGoodSparse⟩ :=
    exists_many_sparse_identity_rows T A G n w D b keep hn hrow hroot
      hGdegree hkeep (by simpa [Zero] using hbudget)
  let W : Finset F := Zero.map omega
  let Bad : F → Finset F := fun z => (Zero \ A z).map omega
  have hWcard : W.card = Zero.card := Finset.card_map _
  have hBad : ∀ z ∈ Good, (Bad z).card ≤ b := by
    intro z hz
    rw [show (Bad z).card = (Zero \ A z).card by
      exact Finset.card_map _]
    exact hGoodSparse z hz
  have hdegreeGood : ∀ z ∈ Good, (sect z).natDegree ≤ k := by
    intro z hz
    exact hsectDegree z (hGoodT hz)
  let line₀ : F → F := fun x => U₀ (Function.invFun omega x)
  let line₁ : F → F := fun x => U₁ (Function.invFun omega x)
  have hagreeGood : ∀ z ∈ Good, ∀ x ∈ W \ Bad z,
      (sect z).eval x = line₀ x + z * line₁ x := by
    intro z hz x hx
    have hx' := Finset.mem_sdiff.mp hx
    obtain ⟨i, hiZero, hix⟩ := Finset.mem_map.mp hx'.1
    have hiA : i ∈ A z := by
      by_contra hiA
      apply hx'.2
      exact Finset.mem_map.mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨hiZero, hiA⟩, hix⟩
    subst x
    simpa [line₀, line₁, Function.leftInverse_invFun omega.injective i] using
      hagreement z (hGoodT hz) i hiA
  have htwo : 1 < Good.card := hkeepPos.trans_lt hGoodCard
  obtain ⟨z₀, hz₀, z₁, hz₁, hne⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨p₀, p₁, hp₀, hp₁, hpencil⟩ :=
    sparseBad_pencil_alignment Good W k b sect line₀ line₁ Bad
      hdegreeGood hBad (by simpa [W, Zero] using hwide) hagreeGood
      hz₀ hz₁ hne
  exact ⟨Good, p₀, p₁, hGoodT, hGoodCard, hp₀, hp₁, hpencil⟩

/-- The sparse-row interpolation inequality has a very wide margin at the
minimum score-64 identity count. -/
theorem score6400_minimal_identity_sparse_numeric :
    131071 + 3 * 18000 < 185348 := by norm_num

/-- With the minimum fixed-factor seed fibre, the direct sparse-row argument
closes every identity locus up to `203330`. -/
theorem score6400_low_identity_sparse_budget
    (tcard d zcard : ℕ)
    (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 185331 ≤ zcard) (hzhi : zcard ≤ 203330) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (18000 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 203330 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 76813 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      76813 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper :
      zcard * tcard + (262144 - zcard) * 1898945373 ≤
        203330 * tcard + 76813 * 1898945373 :=
    Nat.add_le_add hzmul hcompmul
  have hstrict :
      203330 * tcard + 76813 * 1898945373 <
        185364 * tcard + (18000 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_low_identity_sparse_width
    (zcard : ℕ) (hzlo : 185331 ≤ zcard) :
    131071 + 3 * 18000 < zcard := by omega

/-! ## Adaptive sparse-row ranges

The first sparse-row pass uses the largest dirty-row allowance compatible
with the minimum identity count.  Once that pass has excluded the bottom
range, the allowance can be increased.  Repeating this elementary step closes
the entire interval through `212478`; the endpoint `212479` is exactly where
the fixed-factor seed ratio no longer pays for the three-row union bound. -/

theorem score6400_identity_sparse_budget_2
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 203331 ≤ zcard) (hzhi : zcard ≤ 209425) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (24086 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 209425 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 58813 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      58813 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      209425 * tcard + 58813 * 1898945373 <
        185364 * tcard + (24086 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_3
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 209426 ≤ zcard) (hzhi : zcard ≤ 211459) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (26118 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 211459 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 52718 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      52718 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      211459 * tcard + 52718 * 1898945373 <
        185364 * tcard + (26118 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_4
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 211460 ≤ zcard) (hzhi : zcard ≤ 212138) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (26796 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212138 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 50684 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      50684 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212138 * tcard + 50684 * 1898945373 <
        185364 * tcard + (26796 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_5
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212139 ≤ zcard) (hzhi : zcard ≤ 212364) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27022 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212364 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 50005 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      50005 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212364 * tcard + 50005 * 1898945373 <
        185364 * tcard + (27022 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_6
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212365 ≤ zcard) (hzhi : zcard ≤ 212440) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27097 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212440 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 49779 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      49779 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212440 * tcard + 49779 * 1898945373 <
        185364 * tcard + (27097 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_7
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212441 ≤ zcard) (hzhi : zcard ≤ 212466) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27123 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212466 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 49703 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      49703 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212466 * tcard + 49703 * 1898945373 <
        185364 * tcard + (27123 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_8
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212467 ≤ zcard) (hzhi : zcard ≤ 212474) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27131 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212474 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 49677 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      49677 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212474 * tcard + 49677 * 1898945373 <
        185364 * tcard + (27131 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_9
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212475 ≤ zcard) (hzhi : zcard ≤ 212477) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27134 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212477 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 49669 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      49669 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212477 * tcard + 49669 * 1898945373 <
        185364 * tcard + (27134 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

theorem score6400_identity_sparse_budget_10
    (tcard d zcard : ℕ) (hd : 1 ≤ d)
    (hT : 2266 * 1898945373 * d < tcard)
    (hzlo : 212478 ≤ zcard) (hzhi : zcard ≤ 212478) :
    zcard * tcard + (262144 - zcard) * 1898945373 <
      185364 * tcard + (27135 + 1) * (tcard - 76781) := by
  have hbase : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
    simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
  have hTD : 2266 * 1898945373 < tcard := hbase.trans_lt hT
  have hzmul : zcard * tcard ≤ 212478 * tcard :=
    Nat.mul_le_mul_right tcard hzhi
  have hcomp : 262144 - zcard ≤ 49666 := by omega
  have hcompmul : (262144 - zcard) * 1898945373 ≤
      49666 * 1898945373 := Nat.mul_le_mul_right 1898945373 hcomp
  have hupper := Nat.add_le_add hzmul hcompmul
  have hstrict :
      212478 * tcard + 49666 * 1898945373 <
        185364 * tcard + (27135 + 1) * (tcard - 76781) := by
    norm_num at hTD ⊢
    omega
  exact hupper.trans_lt hstrict

/-- Ready-to-use score-64 specialization of the low-identity branch. -/
theorem score6400_low_identity_force_pencil
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F)
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (sect : F → F[X]) (U₀ U₁ : I → F) (d : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hGdegree : ∀ i, (G i).natDegree ≤ 1898945373)
    (hsectDegree : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (sect z).eval (omega i) = U₀ i + z * U₁ i)
    (hd : 1 ≤ d) (hT : 2266 * 1898945373 * d < T.card)
    (hzlo : 185331 ≤ (Finset.univ.filter fun i : I => G i = 0).card)
    (hzhi : (Finset.univ.filter fun i : I => G i = 0).card ≤ 203330) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76781 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  apply sparse_identity_rows_force_pencil omega T A G sect U₀ U₁
    262144 185364 1898945373 131071 18000 76781 hn hrow hroot
    hGdegree hsectDegree hagreement
  · have hbase : 76781 < T.card := by
      have hpos : 0 < 1898945373 := by norm_num
      have hmul : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
        simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
      have : 2266 * 1898945373 < T.card := hmul.trans_lt hT
      omega
    omega
  · norm_num
  · exact score6400_low_identity_sparse_width _ hzlo
  · exact score6400_low_identity_sparse_budget T.card d _ hd hT hzlo hzhi

/-- Common specialization used by each adaptive identity interval. -/
theorem score6400_identity_range_force_pencil
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F)
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (sect : F → F[X]) (U₀ U₁ : I → F) (d b : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hGdegree : ∀ i, (G i).natDegree ≤ 1898945373)
    (hsectDegree : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (sect z).eval (omega i) = U₀ i + z * U₁ i)
    (hd : 1 ≤ d) (hT : 2266 * 1898945373 * d < T.card)
    (hwide :
      131071 + 3 * b <
        (Finset.univ.filter fun i : I ↦ G i = 0).card)
    (hbudget :
      (Finset.univ.filter fun i : I ↦ G i = 0).card * T.card +
          (262144 - (Finset.univ.filter fun i : I ↦ G i = 0).card) *
            1898945373 <
        185364 * T.card + (b + 1) * (T.card - 76781)) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76781 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  apply sparse_identity_rows_force_pencil omega T A G sect U₀ U₁
    262144 185364 1898945373 131071 b 76781 hn hrow hroot
    hGdegree hsectDegree hagreement
  · have hmul : 2266 * 1898945373 ≤ 2266 * 1898945373 * d := by
      simpa using Nat.mul_le_mul_left (2266 * 1898945373) hd
    have hlarge : 2266 * 1898945373 < T.card := hmul.trans_lt hT
    norm_num at hlarge ⊢
    omega
  · norm_num
  · exact hwide
  · exact hbudget

/-- Adaptive sparse-row closure through the exact last viable identity count.
This improves the former `203330` endpoint to `212478` without introducing
any new algebraic assumption. -/
theorem score6400_extended_identity_force_pencil
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F)
    (T : Finset F) (A : F → Finset I) (G : I → F[X])
    (sect : F → F[X]) (U₀ U₁ : I → F) (d : ℕ)
    (hn : Fintype.card I = 262144)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0)
    (hGdegree : ∀ i, (G i).natDegree ≤ 1898945373)
    (hsectDegree : ∀ z ∈ T, (sect z).natDegree ≤ 131071)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (sect z).eval (omega i) = U₀ i + z * U₁ i)
    (hd : 1 ≤ d) (hT : 2266 * 1898945373 * d < T.card)
    (hzlo : 185331 ≤ (Finset.univ.filter fun i : I ↦ G i = 0).card)
    (hzhi : (Finset.univ.filter fun i : I ↦ G i = 0).card ≤ 212478) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76781 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, sect z = p₀ + Polynomial.C z * p₁ := by
  let Zero : Finset I := Finset.univ.filter fun i ↦ G i = 0
  by_cases h1 : Zero.card ≤ 203330
  · apply score6400_low_identity_force_pencil omega T A G sect U₀ U₁ d
      hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using hzlo
    · simpa [Zero] using h1
  have hlo2 : 203331 ≤ Zero.card := by omega
  by_cases h2 : Zero.card ≤ 209425
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 24086 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 24086 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_2 T.card d Zero.card hd hT hlo2 h2
  have hlo3 : 209426 ≤ Zero.card := by omega
  by_cases h3 : Zero.card ≤ 211459
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 26118 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 26118 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_3 T.card d Zero.card hd hT hlo3 h3
  have hlo4 : 211460 ≤ Zero.card := by omega
  by_cases h4 : Zero.card ≤ 212138
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 26796 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 26796 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_4 T.card d Zero.card hd hT hlo4 h4
  have hlo5 : 212139 ≤ Zero.card := by omega
  by_cases h5 : Zero.card ≤ 212364
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 27022 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 27022 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_5 T.card d Zero.card hd hT hlo5 h5
  have hlo6 : 212365 ≤ Zero.card := by omega
  by_cases h6 : Zero.card ≤ 212440
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 27097 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 27097 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_6 T.card d Zero.card hd hT hlo6 h6
  have hlo7 : 212441 ≤ Zero.card := by omega
  by_cases h7 : Zero.card ≤ 212466
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 27123 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 27123 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_7 T.card d Zero.card hd hT hlo7 h7
  have hlo8 : 212467 ≤ Zero.card := by omega
  by_cases h8 : Zero.card ≤ 212474
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 27131 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 27131 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_8 T.card d Zero.card hd hT hlo8 h8
  have hlo9 : 212475 ≤ Zero.card := by omega
  by_cases h9 : Zero.card ≤ 212477
  · apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
      d 27134 hn hrow hroot hGdegree hsectDegree hagreement hd hT
    · simpa [Zero] using (show 131071 + 3 * 27134 < Zero.card by omega)
    · simpa [Zero] using
        score6400_identity_sparse_budget_9 T.card d Zero.card hd hT hlo9 h9
  have hlo10 : 212478 ≤ Zero.card := by omega
  have hhi10 : Zero.card ≤ 212478 := by simpa [Zero] using hzhi
  apply score6400_identity_range_force_pencil omega T A G sect U₀ U₁
    d 27135 hn hrow hroot hGdegree hsectDegree hagreement hd hT
  · simpa [Zero] using (show 131071 + 3 * 27135 < Zero.card by omega)
  · simpa [Zero] using
      score6400_identity_sparse_budget_10 T.card d Zero.card hd hT hlo10 hhi10

/-! ## The direct coordinate obstruction

Unlike the function-field owner obstruction, this polynomial is obtained by
inserting the received affine coordinate directly into the selected
trivariate factor.  Its degree is bounded by the selected factor's `(Y,Z)`
total-degree cap, with no outer-degree multiplier.
-/

/-- Direct affine substitution into the coordinate parent of a trivariate
relation. -/
noncomputable def directAffineObstruction
    {F : Type} [Field F] (R : F[X][X][Y]) (x a b : F) : F[X] :=
  fixedAffineOwnerObstruction (triSpecializeX R x) a b

/-- Direct affine substitution commutes with specialization in the challenge
variable. -/
theorem directAffineObstruction_eval
    {F : Type} [Field F] (R : F[X][X][Y]) (x a b z : F) :
    (directAffineObstruction R x a b).eval z =
      biEval (triSpecializeX R x) (a + z * b) z := by
  let J := triSpecializeX R x
  change (Polynomial.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) J).eval z =
        (J.map (Polynomial.evalRingHom z)).eval (a + z * b)
  induction J using Polynomial.induction_on' with
  | add J K hJ hK =>
      simpa [biEval] using congrArg₂ (fun u v : F => u + v) hJ hK
  | monomial n c =>
      simp [biEval, Polynomial.map_monomial, Polynomial.eval_monomial,
        mul_comm b z]

/-- Every agreement coordinate of an exact section is a root of its direct
affine obstruction. -/
theorem directAffineObstruction_root_of_agreement
    {F : Type} [Field F] (R : F[X][X][Y]) (P : F[X])
    (x a b z : F) (hroot : triEval R z P = 0)
    (hagree : P.eval x = a + z * b) :
    (directAffineObstruction R x a b).eval z = 0 := by
  rw [directAffineObstruction_eval, ← hagree,
    ← eval_triEval_eq_biEval_triSpecializeX, hroot]
  simp

/-- The direct obstruction has degree at most the `(Y,Z)` total-degree cap. -/
theorem directAffineObstruction_natDegree_le
    {F : Type} [Field F] (R : F[X][X][Y]) (x a b : F) (D : ℕ)
    (hYZ : YZCap R D) :
    (directAffineObstruction R x a b).natDegree ≤ D := by
  unfold directAffineObstruction
  exact (natDegree_fixedAffineOwnerObstruction_le_totalDegree
      (triSpecializeX R x) a b).trans (by
        rw [show triSpecializeX R x =
          Polynomial.Bivariate.evalX (Polynomial.C x) R by
            simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]]
        exact evalX_totalDegree_le_of_yzCap x R hYZ)

/-- A selected positive-`Y` factor with at most `212478` direct affine
identities already yields the score-64 polynomial pencil.  Thus any remaining
counterexample to alignment must lie in the genuinely high-identity branch. -/
theorem fixed_factor_low_identity_alignment_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][Y]) (hRpos : 0 < R.natDegree)
    (hYZ : YZCap R 1898945373)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 2266 * 1898945373 * R.natDegree < T.card)
    (hzhi :
      (Finset.univ.filter fun i : I =>
        directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card ≤
          212478) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76781 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  have hd : 1 ≤ R.natDegree := hRpos
  have hGdegree : ∀ i, (G i).natDegree ≤ 1898945373 := by
    intro i
    exact directAffineObstruction_natDegree_le R (omega i) (U₀ i) (U₁ i)
      1898945373 hYZ
  have hGroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0 := by
    intro z hz i hi
    exact directAffineObstruction_root_of_agreement R (P z)
      (omega i) (U₀ i) (U₁ i) z (hvan z hz) (hagreement z hz i hi)
  have hGdegreeWeighted : ∀ i,
      (G i).natDegree ≤ R.natDegree * 1898945373 := by
    intro i
    exact (hGdegree i).trans (by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left 1898945373 hd)
  have hzlo : 185331 ≤
      (Finset.univ.filter fun i : I => G i = 0).card := by
    apply many_zero_obstructions_of_many_large_fibers
      T A G 262144 76780 185330
        (R.natDegree * 1898945373) hn hrow hGroot hGdegreeWeighted
    have hscaled :
        34 * (2266 * 1898945373 * R.natDegree) < 34 * T.card :=
      Nat.mul_lt_mul_of_pos_left hT (by norm_num)
    have hpositive : 0 < R.natDegree * 1898945373 := by positivity
    have hcoeff :
        76814 * (R.natDegree * 1898945373) <
          77044 * (R.natDegree * 1898945373) :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) hpositive
    norm_num at ⊢
    calc
      76814 * (R.natDegree * 1898945373) <
          77044 * (R.natDegree * 1898945373) := hcoeff
      _ = 34 * (2266 * 1898945373 * R.natDegree) := by ring
      _ < 34 * T.card := hscaled
  apply score6400_extended_identity_force_pencil omega T A G P U₀ U₁
    R.natDegree hn hrow hGroot hGdegree hPdegree hagreement hd hT hzlo
  simpa [G] using hzhi

/-! ## Closing the degree-one selected-factor branch

For a selected factor of outer degree one, every direct identity coordinate
supplies a nonzero linear coordinate parent.  Its coefficient of `Y` is a
degree-`D` cleanup polynomial, so 131,413 identity coordinates feed directly
into `linear_sparse_dirty_pencil_6400`. -/

/-- A degree-one irreducible selected factor forces the score-64 pencil on a
very large challenge subset, with no upper bound on its direct identity
locus. -/
theorem fixed_factor_degree_one_alignment_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][Y]) (hRirr : Irreducible R)
    (hRdegree : R.natDegree = 1)
    (hYZ : YZCap R 1898945373)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 2266 * 1898945373 < T.card) :
    ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  have hGdegree : ∀ i, (G i).natDegree ≤ 1898945373 := by
    intro i
    exact directAffineObstruction_natDegree_le R (omega i) (U₀ i) (U₁ i)
      1898945373 hYZ
  have hGroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0 := by
    intro z hz i hi
    exact directAffineObstruction_root_of_agreement R (P z)
      (omega i) (U₀ i) (U₁ i) z (hvan z hz) (hagreement z hz i hi)
  let Identity : Finset I := Finset.univ.filter fun i => G i = 0
  have hIdentity : 185331 ≤ Identity.card := by
    apply many_zero_obstructions_of_many_large_fibers
      T A G 262144 76780 185330 1898945373 hn hrow hGroot hGdegree
    have hscaled :
        34 * (2266 * 1898945373) < 34 * T.card :=
      Nat.mul_lt_mul_of_pos_left hT (by norm_num)
    norm_num at ⊢
    calc
      76814 * 1898945373 < 77044 * 1898945373 := by norm_num
      _ = 34 * (2266 * 1898945373) := by ring
      _ < 34 * T.card := hscaled
  obtain ⟨S, hSIdentity, hScard⟩ :=
    Finset.exists_subset_card_eq (show 131413 ≤ Identity.card by omega)
  letI : Nonempty I := ⟨(Finset.card_pos.mp (by omega : 0 < S.card)).choose⟩
  let W : Finset F := S.map omega
  let B : F → F[X][X] := fun x => triSpecializeX R x
  let line₀ : F → F := fun x => U₀ (Function.invFun omega x)
  let line₁ : F → F := fun x => U₁ (Function.invFun omega x)
  let L : F → F[X] := fun x =>
    Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x)
  have hWcard : W.card = 131413 := by
    simpa [W] using hScard
  have hBne : ∀ x ∈ W, B x ≠ 0 := by
    intro x hx
    exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
      R hRirr (by omega) x
  have hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 1 := by
    intro x hx
    exact (triSpecializeX_natDegree_le R x).trans hRdegree.le
  have hBXdeg : ∀ x ∈ W,
      Polynomial.Bivariate.degreeX (B x) ≤ 1898945373 := by
    intro x hx
    have htotal : Polynomial.Bivariate.totalDegree (B x) ≤ 1898945373 := by
      simpa [B, triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
        evalX_totalDegree_le_of_yzCap x R hYZ
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro i hi
    have hterm : ((B x).coeff i).natDegree + i ≤ 1898945373 := by
      apply (Finset.le_sup
        (f := fun j => ((B x).coeff j).natDegree + j) hi).trans
      simpa [Polynomial.Bivariate.totalDegree] using htotal
    omega
  have hBroot : ∀ x ∈ W, (B x).eval (L x) = 0 := by
    intro x hx
    obtain ⟨i, hiS, hix⟩ := Finset.mem_map.mp hx
    subst x
    have hiIdentity := hSIdentity hiS
    have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
    change (triSpecializeX R (omega i)).eval
      (Polynomial.C (line₀ (omega i)) +
        Polynomial.X * Polynomial.C (line₁ (omega i))) = 0
    have hline₀ : line₀ (omega i) = U₀ i := by
      simp [line₀, Function.leftInverse_invFun omega.injective i]
    have hline₁ : line₁ (omega i) = U₁ i := by
      simp [line₁, Function.leftInverse_invFun omega.injective i]
    rw [hline₀, hline₁]
    simpa only [G, directAffineObstruction, fixedAffineOwnerObstruction] using hGi
  have hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
      ((B x).map (Polynomial.evalRingHom z)).eval ((P z).eval x) = 0 := by
    intro z hz x hx
    change biEval (triSpecializeX R x) ((P z).eval x) z = 0
    rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hz]
    simp
  apply linear_sparse_dirty_pencil_6400 W T B L P line₀ line₁ 1898945373
  · exact hWcard
  · exact le_rfl
  · norm_num at hT ⊢
    exact hT
  · exact hPdegree
  · intro x hx
    rfl
  · exact hBne
  · exact hBdeg
  · exact hBXdeg
  · exact hBroot
  · exact hsectionRoot

/-! ## Degree two: isolate the simple-root residual

For an outer quadratic, 131,413 repeated direct identities are enough for the
quadratic sparse-dirty producer.  Consequently the only unresolved quadratic
case has at least 81,067 generically simple affine identities. -/

/-- Every irreducible degree-two selected factor either has a large simple
direct-identity locus, or already forces the score-64 polynomial pencil. -/
theorem fixed_factor_degree_two_simple_or_alignment_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][Y]) (hRirr : Irreducible R)
    (hRdegree : R.natDegree = 2)
    (hYZ : YZCap R 1898945373)
    (T : Finset F) (P : F → F[X]) (A : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdegree : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (A z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 2266 * 1898945373 * 2 < T.card)
    (hhigh : 212478 < (Finset.univ.filter fun i : I ↦
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card) :
    let Identity : Finset I := Finset.univ.filter fun i =>
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0
    let Simple : Finset I := Identity.filter fun i =>
      (triSpecializeX R (omega i)).derivative.eval
        (Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i)) ≠ 0
    81067 ≤ Simple.card ∨
      ∃ Good : Finset F, ∃ p₀ p₁ : F[X],
        Good ⊆ T ∧ 2114009265202 ≤ Good.card ∧
        p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
        ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let G : I → F[X] := fun i =>
    directAffineObstruction R (omega i) (U₀ i) (U₁ i)
  let Identity : Finset I := Finset.univ.filter fun i => G i = 0
  let BI : I → F[X][X] := fun i => triSpecializeX R (omega i)
  let LI : I → F[X] := fun i =>
    Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i)
  let Simple : Finset I := Identity.filter fun i =>
    (BI i).derivative.eval (LI i) ≠ 0
  have hGdegree : ∀ i, (G i).natDegree ≤ 1898945373 := by
    intro i
    exact directAffineObstruction_natDegree_le R (omega i) (U₀ i) (U₁ i)
      1898945373 hYZ
  have hGroot : ∀ z ∈ T, ∀ i ∈ A z, (G i).eval z = 0 := by
    intro z hz i hi
    exact directAffineObstruction_root_of_agreement R (P z)
      (omega i) (U₀ i) (U₁ i) z (hvan z hz) (hagreement z hz i hi)
  have hIdentity : 212479 ≤ Identity.card := by
    have hh : 212479 ≤ (Finset.univ.filter fun i : I ↦
        directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0).card := by
      omega
    simpa [Identity, G] using hh
  rcases large_simple_or_exists_sparse_nonsimple_coordinates_extended_6400
      Identity Simple (Finset.filter_subset _ _) hIdentity with hsimple | hrepeat
  · exact Or.inl hsimple
  · right
    obtain ⟨S, hSrepeat, hScard⟩ := hrepeat
    letI : Nonempty I := ⟨(Finset.card_pos.mp (by omega : 0 < S.card)).choose⟩
    let W : Finset F := S.map omega
    let B : F → F[X][X] := fun x => triSpecializeX R x
    let line₀ : F → F := fun x => U₀ (Function.invFun omega x)
    let line₁ : F → F := fun x => U₁ (Function.invFun omega x)
    let L : F → F[X] := fun x =>
      Polynomial.C (line₀ x) + Polynomial.X * Polynomial.C (line₁ x)
    have hWcard : W.card = 131413 := by simpa [W] using hScard
    have hBne : ∀ x ∈ W, B x ≠ 0 := by
      intro x hx
      exact triSpecializeX_ne_zero_of_irreducible_natDegree_pos
        R hRirr (by omega) x
    have hBdeg : ∀ x ∈ W, (B x).natDegree ≤ 2 := by
      intro x hx
      exact (triSpecializeX_natDegree_le R x).trans hRdegree.le
    have hBXdeg : ∀ x ∈ W,
        Polynomial.Bivariate.degreeX (B x) ≤ 1898945373 := by
      intro x hx
      have htotal : Polynomial.Bivariate.totalDegree (B x) ≤ 1898945373 := by
        simpa [B, triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
          evalX_totalDegree_le_of_yzCap x R hYZ
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro i hi
      have hterm : ((B x).coeff i).natDegree + i ≤ 1898945373 := by
        apply (Finset.le_sup
          (f := fun j => ((B x).coeff j).natDegree + j) hi).trans
        simpa [Polynomial.Bivariate.totalDegree] using htotal
      omega
    have hBroot : ∀ x ∈ W, (B x).eval (L x) = 0 := by
      intro x hx
      obtain ⟨i, hiS, hix⟩ := Finset.mem_map.mp hx
      subst x
      have hiIdentity : i ∈ Identity :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).1
      have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
      change (triSpecializeX R (omega i)).eval
        (Polynomial.C (line₀ (omega i)) +
          Polynomial.X * Polynomial.C (line₁ (omega i))) = 0
      have hline₀ : line₀ (omega i) = U₀ i := by
        simp [line₀, Function.leftInverse_invFun omega.injective i]
      have hline₁ : line₁ (omega i) = U₁ i := by
        simp [line₁, Function.leftInverse_invFun omega.injective i]
      rw [hline₀, hline₁]
      simpa only [G, directAffineObstruction, fixedAffineOwnerObstruction] using hGi
    have hBrepeated : ∀ x ∈ W, (B x).derivative.eval (L x) = 0 := by
      intro x hx
      obtain ⟨i, hiS, hix⟩ := Finset.mem_map.mp hx
      subst x
      have hiNotSimple : i ∉ Simple :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).2
      have hiIdentity : i ∈ Identity :=
        (Finset.mem_sdiff.mp (hSrepeat hiS)).1
      have hzero : (BI i).derivative.eval (LI i) = 0 := by
        by_contra hne
        exact hiNotSimple (Finset.mem_filter.mpr ⟨hiIdentity, hne⟩)
      simpa [B, L, BI, LI, line₀, line₁,
        Function.leftInverse_invFun omega.injective i] using hzero
    have hsectionRoot : ∀ z ∈ T, ∀ x ∈ W,
        ((B x).map (Polynomial.evalRingHom z)).eval ((P z).eval x) = 0 := by
      intro z hz x hx
      change biEval (triSpecializeX R x) ((P z).eval x) z = 0
      rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hz]
      simp
    apply repeated_quadratic_sparse_dirty_pencil_6400
      W T B L P line₀ line₁ 1898945373
    · exact hWcard
    · exact le_rfl
    · have hbase : 2266 * 1898945373 < T.card := by
        have hle : 2266 * 1898945373 ≤ 2266 * 1898945373 * 2 := by norm_num
        exact hle.trans_lt hT
      norm_num at hbase ⊢
      exact hbase
    · exact hPdegree
    · intro x hx
      rfl
    · exact hBne
    · exact hBdeg
    · exact hBXdeg
    · exact hBroot
    · exact hBrepeated
    · exact hsectionRoot

end ProximityPrize.SubmissionLower
