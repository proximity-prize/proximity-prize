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
      T ⊆ S ∧
      (∀ z ∈ T, z ∉ Bad r) ∧
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

/-- Two-stage selection with a first-stage-dependent pair coefficient.  This
lets the linear outer-factor branch retain its resultant budget while the
nonlinear branch pays only for the incidence argument it actually consumes. -/
theorem exists_staged_weighted_selection_by_factor
    {σ ρ η : Type*} [DecidableEq σ] [DecidableEq ρ] [DecidableEq η]
    (S : Finset σ) (Rs : Finset ρ) (Hs : ρ → Finset η)
    (degR : ρ → Nat) (degH : η → Nat) (bad pairCost : ρ → Nat)
    (e : Nat)
    (RelR : σ → ρ → Prop) [DecidableRel RelR]
    (RelH : σ → ρ → η → Prop) [∀ r, DecidableRel (fun z h => RelH z r h)]
    (Bad : ρ → Finset σ)
    (hRcover : ∀ z ∈ S, ∃ r ∈ Rs, RelR z r)
    (hglobal :
      (∑ r ∈ Rs, (pairCost r * degR r + e * degR r + bad r)) < S.card)
    (hBad : ∀ r ∈ Rs, ((S.filter fun z => RelR z r) ∩ Bad r).card ≤ bad r)
    (hHpos : ∀ r ∈ Rs, ∀ h ∈ Hs r, 0 < degH h)
    (hHsum : ∀ r ∈ Rs, (∑ h ∈ Hs r, degH h) ≤ degR r)
    (hHcover : ∀ r ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z r) \ Bad r,
      ∃ h ∈ Hs r, RelH z r h) :
    ∃ r ∈ Rs, ∃ h ∈ Hs r, ∃ T : Finset σ,
      T ⊆ S ∧
      (∀ z ∈ T, z ∉ Bad r) ∧
      (∀ z ∈ T, RelR z r ∧ RelH z r h) ∧
      pairCost r * degH h + e < T.card := by
  classical
  let capR : ρ → Nat := fun r => pairCost r * degR r + e * degR r + bad r
  obtain ⟨r, hr, hrfiber⟩ :=
    exists_rel_fiber_gt_capacity S Rs RelR capR hRcover
      (by simpa [capR] using hglobal)
  let U := S.filter fun z => RelR z r
  have hbadU : (U ∩ Bad r).card ≤ bad r := by simpa [U] using hBad r hr
  have hUgood : pairCost r * degR r + e * degR r < (U \ Bad r).card := by
    rw [Finset.card_sdiff]
    apply Nat.lt_sub_of_add_lt
    have hbadd : pairCost r * degR r + e * degR r + (Bad r ∩ U).card ≤
        pairCost r * degR r + e * degR r + bad r := by
      apply Nat.add_le_add_left
      simpa [Finset.inter_comm] using hbadU
    exact hbadd.trans_lt (by simpa [capR, U] using hrfiber)
  have hHcard : (Hs r).card ≤ degR r := by
    calc
      (Hs r).card = ∑ h ∈ Hs r, 1 := by simp
      _ ≤ ∑ h ∈ Hs r, degH h := by
        exact Finset.sum_le_sum fun h hh => hHpos r hr h hh
      _ ≤ degR r := hHsum r hr
  let capH : η → Nat := fun h => pairCost r * degH h + e
  have hcapHsum :
      (∑ h ∈ Hs r, capH h) ≤ pairCost r * degR r + e * degR r := by
    dsimp [capH]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left (pairCost r) (hHsum r hr))
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right e hHcard)
  have hsecondLarge : (∑ h ∈ Hs r, capH h) < (U \ Bad r).card :=
    hcapHsum.trans_lt hUgood
  obtain ⟨h, hh, hhfiber⟩ :=
    exists_rel_fiber_gt_capacity (U \ Bad r) (Hs r) (fun z h => RelH z r h)
      capH (hHcover r hr) hsecondLarge
  let T := (U \ Bad r).filter fun z => RelH z r h
  refine ⟨r, hr, h, hh, T, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).1
  · intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hz'.1).1).2, hz'.2⟩
  · simpa [T, capH] using hhfiber

end ProximityPrize.SubmissionLower
