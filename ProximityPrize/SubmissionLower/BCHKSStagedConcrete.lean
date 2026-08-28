import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

namespace ProximityPrize.SubmissionLower

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

/-- Two-stage sharp BCHKS selection.  The first stage reserves the selected
factor's own bad-specialization budget.  After deleting that set, the second
stage spends `A*dR*dH+e` per positive second-stage factor. -/
theorem exists_staged_weighted_selection
    {σ ρ η : Type*} [DecidableEq σ] [DecidableEq ρ] [DecidableEq η]
    (S : Finset σ) (Rs : Finset ρ) (Hs : ρ → Finset η)
    (degR : ρ → Nat) (degH : η → Nat) (bad : ρ → Nat)
    (A e : Nat)
    (RelR : σ → ρ → Prop) [DecidableRel RelR]
    (RelH : σ → ρ → η → Prop) [∀ r, DecidableRel (fun z h => RelH z r h)]
    (Bad : ρ → Finset σ)
    (hRcover : ∀ z ∈ S, ∃ r ∈ Rs, RelR z r)
    (hglobal :
      (∑ r ∈ Rs, (A * degR r ^ 2 + e * degR r + bad r)) < S.card)
    (hBad : ∀ r ∈ Rs, ((S.filter fun z => RelR z r) ∩ Bad r).card ≤ bad r)
    (hHpos : ∀ r ∈ Rs, ∀ h ∈ Hs r, 0 < degH h)
    (hHsum : ∀ r ∈ Rs, (∑ h ∈ Hs r, degH h) ≤ degR r)
    (hHcover : ∀ r ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z r) \ Bad r,
      ∃ h ∈ Hs r, RelH z r h) :
    ∃ r ∈ Rs, ∃ h ∈ Hs r, ∃ T : Finset σ,
      T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad r) ∧
      (∀ z ∈ T, RelR z r ∧ RelH z r h) ∧
      A * degR r * degH h + e < T.card := by
  classical
  let capR : ρ → Nat := fun r => A * degR r ^ 2 + e * degR r + bad r
  obtain ⟨r, hr, hrfiber⟩ :=
    exists_rel_fiber_gt_capacity S Rs RelR capR hRcover (by simpa [capR] using hglobal)
  let U := S.filter fun z => RelR z r
  have hbadU : (U ∩ Bad r).card ≤ bad r := by simpa [U] using hBad r hr
  have hUgood : A * degR r ^ 2 + e * degR r < (U \ Bad r).card := by
    rw [Finset.card_sdiff]
    apply Nat.lt_sub_of_add_lt
    have hbadd : A * degR r ^ 2 + e * degR r + (Bad r ∩ U).card ≤
        A * degR r ^ 2 + e * degR r + bad r := by
      apply Nat.add_le_add_left
      simpa [Finset.inter_comm] using hbadU
    exact hbadd.trans_lt (by simpa [capR, U] using hrfiber)
  have hHcard : (Hs r).card ≤ degR r := by
    calc
      (Hs r).card = ∑ h ∈ Hs r, 1 := by simp
      _ ≤ ∑ h ∈ Hs r, degH h := by
        exact Finset.sum_le_sum fun h hh => hHpos r hr h hh
      _ ≤ degR r := hHsum r hr
  let capH : η → Nat := fun h => A * degR r * degH h + e
  have hcapHsum : (∑ h ∈ Hs r, capH h) ≤ A * degR r ^ 2 + e * degR r := by
    dsimp [capH]
    change (∑ h ∈ Hs r, ((A * degR r) * degH h + e)) ≤ _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      A * degR r * (∑ h ∈ Hs r, degH h) + (Hs r).card * e ≤
          A * degR r * degR r + degR r * e := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left (A * degR r) (hHsum r hr))
          (Nat.mul_le_mul_right e hHcard)
      _ = A * degR r ^ 2 + e * degR r := by ring
  have hsecondLarge : (∑ h ∈ Hs r, capH h) < (U \ Bad r).card :=
    hcapHsum.trans_lt hUgood
  obtain ⟨h, hh, hhfiber⟩ :=
    exists_rel_fiber_gt_capacity (U \ Bad r) (Hs r) (fun z h => RelH z r h)
      capH (hHcover r hr) hsecondLarge
  let T := (U \ Bad r).filter fun z => RelH z r h
  refine ⟨r, hr, h, hh, T, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzU : z ∈ U := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
    exact (Finset.mem_filter.mp hzU).1
  · intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzU : z ∈ U := (Finset.mem_sdiff.mp hz'.1).1
    exact ⟨(Finset.mem_filter.mp hzU).2, hz'.2⟩
  · simpa [T, capH] using hhfiber



/-- Concrete two-stage selection for the normalized factors of an interpolation
polynomial and the positive factors of the selected specialization. -/
theorem exists_concrete_staged_factor_selection
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x₀ : Polynomial (Polynomial (Polynomial F)) → F)
    (Bad : Polynomial (Polynomial (Polynomial F)) → Finset F)
    (badCap : Polynomial (Polynomial (Polynomial F)) → Nat)
    (A e : Nat)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hx : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → triSpecializeX R (x₀ R) ≠ 0)
    (hBadCap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → (Bad R).card ≤ badCap R)
    (hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → ∀ z ∈ S \ Bad R,
        biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0)
    (hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (A * R.natDegree ^ 2 + e * R.natDegree + badCap R)) < S.card) :
    ∃ R H T,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R (x₀ R)) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad R) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval (x₀ R) (P z)) z = 0) ∧
      A * R.natDegree * H.natDegree + e < T.card := by
  classical
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  let Hs : Polynomial (Polynomial (Polynomial F)) → Finset (Polynomial (Polynomial F)) :=
    fun R => (UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R (x₀ R))).toFinset.filter fun H => 0 < H.natDegree
  let RelR : F → Polynomial (Polynomial (Polynomial F)) → Prop :=
    fun z R => triEval R z (P z) = 0
  let RelH : F → Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) → Prop :=
    fun z R H => biEval H (Polynomial.eval (x₀ R) (P z)) z = 0
  have hRcover : ∀ z ∈ S, ∃ R ∈ Rs, RelR z R := by
    intro z hz
    obtain ⟨R, hRQ, hRpos, hzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (P z) (hQz z hz) (hQeval z hz)
    exact ⟨R, by simp [Rs, hRQ, hRpos], hzero⟩
  have hHpos : ∀ R ∈ Rs, ∀ H ∈ Hs R, 0 < H.natDegree := by
    intro R hR H hH
    exact (Finset.mem_filter.mp hH).2
  have hHsum : ∀ R ∈ Rs, (∑ H ∈ Hs R, H.natDegree) ≤ R.natDegree := by
    intro R hR
    have hRm := Finset.mem_filter.mp hR
    have hRX := hx R (by simpa [Rs] using hRm.1) hRm.2
    calc
      (∑ H ∈ Hs R, H.natDegree) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R (x₀ R))).toFinset, H.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ (triSpecializeX R (x₀ R)).natDegree :=
        normalizedFactors_toFinset_sum_natDegree_le _ hRX
      _ ≤ R.natDegree := triSpecializeX_natDegree_le R (x₀ R)
  have hHcover : ∀ R ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z R) \ Bad R,
      ∃ H ∈ Hs R, RelH z R H := by
    intro R hR z hz
    have hRm := Finset.mem_filter.mp hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by simpa [Rs] using hRm.1
    have hzS : z ∈ S := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
    have hzgood : z ∈ S \ Bad R := Finset.mem_sdiff.mpr ⟨hzS, (Finset.mem_sdiff.mp hz).2⟩
    have hRzero : RelR z R := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
    have hpoint : biEval (triSpecializeX R (x₀ R))
        (Polynomial.eval (x₀ R) (P z)) z = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX, hRzero]
      simp
    obtain ⟨H, hHR, hHpos, hHzero⟩ :=
      exists_positive_normalizedFactor_biEval_eq_zero
        (triSpecializeX R (x₀ R)) z (Polynomial.eval (x₀ R) (P z))
        (hsecond R hRQ hRm.2 z hzgood) hpoint
    exact ⟨H, by simp [Hs, hHR, hHpos], hHzero⟩
  have hBad : ∀ R ∈ Rs,
      ((S.filter fun z => RelR z R) ∩ Bad R).card ≤ badCap R := by
    intro R hR
    apply (Finset.card_le_card Finset.inter_subset_right).trans
    have hm := Finset.mem_filter.mp hR
    exact hBadCap R (by simpa [Rs] using hm.1) hm.2
  obtain ⟨R, hRs, H, hHs, T, hTS, hTbad, hrel, hmargin⟩ :=
    exists_staged_weighted_selection S Rs Hs Polynomial.natDegree Polynomial.natDegree
      badCap A e RelR RelH Bad hRcover (by simpa [Rs] using hglobal)
      hBad hHpos hHsum hHcover
  have hRm := Finset.mem_filter.mp hRs
  have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by simpa [Rs] using hRm.1
  have hHm := Finset.mem_filter.mp hHs
  have hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R (x₀ R)) := by simpa [Hs] using hHm.1
  exact ⟨R, H, T, hRQ, hRm.2, hHR, hHm.2, hTS, hTbad, hrel, hmargin⟩

end ProximityPrize.SubmissionLower
