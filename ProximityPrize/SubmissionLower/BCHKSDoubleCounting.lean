import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open scoped BigOperators
open Finset

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-- Counting incidences by rows or by columns. -/
theorem sum_card_eq_sum_fiber_card
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (T : Finset ζ) (A : ζ → Finset ι) :
    (∑ z ∈ T, (A z).card) =
      ∑ x : ι, (T.filter fun z => x ∈ A z).card := by
  classical
  calc
    (∑ z ∈ T, (A z).card) =
        ∑ z ∈ T, ∑ x : ι, if x ∈ A z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp
    _ = ∑ x : ι, ∑ z ∈ T, if x ∈ A z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : ι, (T.filter fun z => x ∈ A z).card := by
      apply Finset.sum_congr rfl
      intro x hx
      simp

/-- If every row misses at most `e` of `n` coordinates and the displayed
strict incidence inequality holds, more than `k` coordinates have fiber
larger than `B`. -/
theorem many_large_fibers
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (T : Finset ζ) (A : ζ → Finset ι) (n e k B : ℕ)
    (hn : Fintype.card ι = n)
    (hrow : ∀ z ∈ T, n - e ≤ (A z).card)
    (hcount : (n - e - k) * T.card > (n - k) * B) :
    k + 1 ≤ (Finset.univ.filter fun x : ι =>
      B < (T.filter fun z => x ∈ A z).card).card := by
  classical
  let fib : ι → ℕ := fun x => (T.filter fun z => x ∈ A z).card
  let G : Finset ι := Finset.univ.filter fun x => B < fib x
  have hnk : k < n := by
    by_contra h
    have : n - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    have : n - e - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp_all
  have hBT : B < T.card := by
    by_contra h
    have hTB : T.card ≤ B := by omega
    have hcoef : n - e - k ≤ n - k := Nat.sub_le_sub_right (Nat.sub_le n e) k
    have hle : (n - e - k) * T.card ≤ (n - k) * B :=
      (Nat.mul_le_mul hcoef hTB)
    omega
  have hlower : (n - e) * T.card ≤ ∑ x : ι, fib x := by
    rw [← sum_card_eq_sum_fiber_card T A]
    calc
      (n - e) * T.card = ∑ z ∈ T, (n - e) := by simp [mul_comm]
      _ ≤ ∑ z ∈ T, (A z).card := Finset.sum_le_sum hrow
  change k + 1 ≤ G.card
  by_contra hsmall
  have hG : G.card ≤ k := by omega
  let H : Finset ι := Finset.univ.filter fun x => ¬ B < fib x
  have hpartition : (∑ x : ι, fib x) =
      (∑ x ∈ G, fib x) + ∑ x ∈ H, fib x := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ι => B < fib x) fib
    simpa [G, H, add_comm] using hs.symm
  have hgood : (∑ x ∈ G, fib x) ≤ G.card * T.card := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    dsimp [fib]
    simpa only [nsmul_eq_mul, one_mul] using
      Finset.card_filter_le T (fun z => x ∈ A z)
  have hbad_each : ∀ x ∈ H, fib x ≤ B := by
    intro x hx
    have hx' : ¬ B < fib x := by
      have := (Finset.mem_filter.mp (show x ∈ Finset.univ.filter
        (fun x : ι => ¬ B < fib x) by simpa [H] using hx)).2
      exact this
    omega
  have hHcard : H.card = n - G.card := by
    have hp := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (fun x => B < fib x)
    change (Finset.univ.filter (fun x : ι => ¬ B < fib x)).card =
      n - (Finset.univ.filter (fun x : ι => B < fib x)).card
    rw [← hn, ← Finset.card_univ]
    omega
  have hbad : (∑ x ∈ H, fib x) ≤ (n - G.card) * B := by
    calc
      (∑ x ∈ H, fib x) ≤ H.card * B :=
        Finset.sum_le_card_nsmul H fib B hbad_each
      _ = (n - G.card) * B := by rw [hHcard]
  have hupper : (∑ x : ι, fib x) ≤
      G.card * T.card + (n - G.card) * B := by
    rw [hpartition]
    exact Nat.add_le_add hgood hbad
  have hGn : G.card ≤ n := by rw [← hn]; exact Finset.card_le_univ G
  have hkN : k ≤ n := hnk.le
  have hmono : G.card * T.card + (n - G.card) * B ≤
      k * T.card + (n - k) * B := by
    have h1 := Nat.sub_add_cancel hGn
    have h2 := Nat.sub_add_cancel hkN
    have h3 := Nat.sub_add_cancel hBT.le
    have hm := Nat.mul_le_mul_right (T.card - B) hG
    nlinarith
  have htotal : (n - e) * T.card ≤ k * T.card + (n - k) * B :=
    hlower.trans (hupper.trans hmono)
  have hcoef : k ≤ n - e := by
    by_contra hk
    have hz : n - e - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, zero_mul] at hcount
    omega
  have hsub := Nat.sub_add_cancel hcoef
  nlinarith

/-- The numerical BCHKS parameters turn the stated pair-fiber lower bound
into the strict inequality required by `many_large_fibers`. -/
theorem concrete_incidence_inequality (dH d D tcard : ℕ)
    (ht : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ tcard) :
    (262144 - 76721 - 131071) * tcard >
      (262144 - 131071) * ((2 * 131071 + 1) * dH * d * D) := by
  norm_num at ht ⊢
  nlinarith

/-- Direct specialization: at least `131072` coordinates have fibers larger
than the BCHKS collision budget. -/
theorem concrete_many_large_fibers
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (T : Finset ζ) (A : ζ → Finset ι) (dH d D : ℕ)
    (hn : Fintype.card ι = 262144)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ T.card) :
    131072 ≤ (Finset.univ.filter fun x : ι =>
      (2 * 131071 + 1) * dH * d * D <
        (T.filter fun z => x ∈ A z).card).card := by
  apply many_large_fibers T A 262144 76721 131071
    ((2 * 131071 + 1) * dH * d * D) hn hrow
  exact concrete_incidence_inequality dH d D T.card hT


/-- Elementary incidence finish: among sufficiently many affine challenges, one large
agreement set consists entirely of coordinates where both affine rows agree. -/
theorem doubleCounting_exists_common_affine_set
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F]
    (U p : Fin 2 → ι → F) (T : Finset F) (A : F → Finset ι) (e : ℕ)
    (hT : e + 1 < T.card)
    (hAcard : ∀ z ∈ T, Fintype.card ι - e ≤ (A z).card)
    (hEq : ∀ z ∈ T, ∀ x ∈ A z,
      U 0 x + z * U 1 x = p 0 x + z * p 1 x) :
    ∃ z ∈ T, ∀ x ∈ A z, U 0 x = p 0 x ∧ U 1 x = p 1 x := by
  classical
  let B : Finset ι := Finset.univ.filter fun x =>
    U 0 x ≠ p 0 x ∨ U 1 x ≠ p 1 x
  let R : F → Finset ι := fun z => A z ∩ B
  have hRsub (z : F) : R z ⊆ B := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hRpair : (↑T : Set F).PairwiseDisjoint R := by
    rintro z hz w hw hzw
    change Disjoint (R z) (R w)
    rw [Finset.disjoint_left]
    intro x hxz hxw
    have hxAz : x ∈ A z := (Finset.mem_inter.mp hxz).1
    have hxAw : x ∈ A w := (Finset.mem_inter.mp hxw).1
    have hzEq := hEq z hz x hxAz
    have hwEq := hEq w hw x hxAw
    have hmul : (z - w) * (U 1 x - p 1 x) = 0 := by
      linear_combination hzEq - hwEq
    have hzw0 : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have hrow1 : U 1 x = p 1 x := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzw0)
    have hrow0 : U 0 x = p 0 x := by
      rw [hrow1] at hzEq
      exact add_right_cancel hzEq
    have hxB : x ∈ B := (Finset.mem_inter.mp hxz).2
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
    exact hxB.elim (fun h => h hrow0) (fun h => h hrow1)
  have hRlower (z : F) (hz : z ∈ T) : B.card ≤ (R z).card + e := by
    have hsplit := Finset.card_inter_add_card_sdiff (A z) B
    have hsdiff : (A z \ B).card ≤ Bᶜ.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp hx).2
    rw [Finset.card_compl] at hsdiff
    have ha := hAcard z hz
    have hbcard : B.card ≤ Fintype.card ι := Finset.card_le_univ B
    dsimp only [R]
    omega
  have hB : B.card ≤ e := by
    by_contra hnot
    have heB : e < B.card := Nat.lt_of_not_ge hnot
    have hsumLower : T.card * (B.card - e) ≤ ∑ z ∈ T, (R z).card := by
      calc
        T.card * (B.card - e) = ∑ z ∈ T, (B.card - e) := by
          exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
        _ ≤ ∑ z ∈ T, (R z).card := by
          exact Finset.sum_le_sum fun z hz => by
            have := hRlower z hz
            omega
    have hunionSub : (T.biUnion R).card ≤ B.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨z, hzT, hxR⟩ := Finset.mem_biUnion.mp hx
      exact hRsub z hxR
    have hunionCard : (T.biUnion R).card = ∑ z ∈ T, (R z).card :=
      Finset.card_biUnion hRpair
    rw [hunionCard] at hunionSub
    have hprod : T.card * (B.card - e) ≤ B.card := hsumLower.trans hunionSub
    have hdpos : 0 < B.card - e := Nat.sub_pos_of_lt heB
    have htlo : e + 2 ≤ T.card := by omega
    have he_mul : e ≤ e * (B.card - e) :=
      Nat.le_mul_of_pos_right e hdpos
    have hstrict : B.card < (e + 2) * (B.card - e) := by
      calc
        B.card = e + (B.card - e) := (Nat.add_sub_of_le heB.le).symm
        _ ≤ e * (B.card - e) + (B.card - e) := Nat.add_le_add_right he_mul _
        _ < e * (B.card - e) + 2 * (B.card - e) := by omega
        _ = (e + 2) * (B.card - e) := by ring
    have hprodLower : (e + 2) * (B.card - e) ≤
        T.card * (B.card - e) := Nat.mul_le_mul_right _ htlo
    omega
  by_contra hno
  push Not at hno
  have hRpos : ∀ z ∈ T, 1 ≤ (R z).card := by
    intro z hz
    obtain ⟨x, hxA, hxnot⟩ := hno z hz
    apply Finset.card_pos.mpr
    refine ⟨x, Finset.mem_inter.mpr ⟨hxA, ?_⟩⟩
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h0 : U 0 x = p 0 x
    · exact Or.inr (hxnot h0)
    · exact Or.inl h0
  have hTsum : T.card ≤ ∑ z ∈ T, (R z).card := by
    calc
      T.card = ∑ z ∈ T, 1 := by simp
      _ ≤ ∑ z ∈ T, (R z).card := Finset.sum_le_sum hRpos
  have hunionSub : (T.biUnion R).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨z, hzT, hxR⟩ := Finset.mem_biUnion.mp hx
    exact hRsub z hxR
  rw [Finset.card_biUnion hRpair] at hunionSub
  have hTB : T.card ≤ B.card := hTsum.trans hunionSub
  omega



/-- The incidence arithmetic also absorbs the one-unit base-`Z` numerator overhead. -/
theorem concrete_incidence_inequality_plus (dH d D tcard : ℕ)
    (ht : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ tcard) :
    (262144 - 76721 - 131071) * tcard >
      (262144 - 131071) * ((2 * 131071 + 2) * dH * d * D) := by
  norm_num at ht ⊢
  nlinarith

theorem concrete_many_large_fibers_plus
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (T : Finset ζ) (A : ζ → Finset ι) (dH d D : ℕ)
    (hn : Fintype.card ι = 262144)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ T.card) :
    131072 ≤ (Finset.univ.filter fun x : ι =>
      (2 * 131071 + 2) * dH * d * D <
        (T.filter fun z => x ∈ A z).card).card := by
  apply many_large_fibers T A 262144 76721 131071
    ((2 * 131071 + 2) * dH * d * D) hn hrow
  exact concrete_incidence_inequality_plus dH d D T.card hT

/-- At the 63.94 error cell, `632176` is a sufficient row-to-fibre
conversion coefficient.  This is the exact incidence calculation and has no
dependence on the Hensel lifting horizon. -/
theorem incidence_6394_arithmetic (r tcard : Nat)
    (ht : 632176 * r + 76721 + 1 ≤ tcard) :
    (262144 - 76721 - 131071) * tcard >
      (262144 - 131071) * ((2 * 131071 + 2) * r) := by
  norm_num at ht ⊢
  nlinarith

theorem incidence_6394_arithmetic_mul (dH d D tcard : Nat)
    (ht : 632176 * dH * d * D + 76721 + 1 ≤ tcard) :
    (262144 - 76721 - 131071) * tcard >
      (262144 - 131071) * ((2 * 131071 + 2) * dH * d * D) := by
  simpa [Nat.mul_assoc] using
    incidence_6394_arithmetic (dH * d * D) tcard (by
      simpa [Nat.mul_assoc] using ht)

/-- Exact-incidence extraction used by the short-horizon nonlinear branch. -/
theorem many_large_fibers_6394
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (T : Finset ζ) (A : ζ → Finset ι) (dH d D : Nat)
    (hn : Fintype.card ι = 262144)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 632176 * dH * d * D + 76721 + 1 ≤ T.card) :
    131072 ≤ (Finset.univ.filter fun x : ι =>
      (2 * 131071 + 2) * dH * d * D <
        (T.filter fun z => x ∈ A z).card).card := by
  simpa only [Nat.reduceAdd] using
    (many_large_fibers T A 262144 76721 131071
      ((2 * 131071 + 2) * dH * d * D) hn hrow
      (incidence_6394_arithmetic_mul dH d D T.card hT))

end ProximityPrize.SubmissionLower
