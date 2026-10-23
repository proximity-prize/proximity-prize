/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetUpper

namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def dot {k : ℕ} (x v : Fin k → F) : F := ∑ i, x i * v i

omit [Fintype F] [DecidableEq F] in
lemma dot_surjective {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    Function.Surjective (dot d) := by
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    simpa only [ne_eq, Pi.zero_apply, Function.ne_iff] using hd
  intro y
  let v : Fin k → F := fun i => if i = j then (d j)⁻¹ * y else 0
  refine ⟨v, ?_⟩
  simp only [dot, v]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro b _ hbj
    simp [hbj]
  · simp

lemma dot_zero_fiber_card_mul {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    ((Finset.univ.filter fun v : Fin k → F => dot d v = 0).card) * Fintype.card F =
      Fintype.card (Fin k → F) := by
  classical
  let φ : (Fin k → F) →+ F :=
    { toFun := dot d
      map_zero' := by simp [dot]
      map_add' := by
        intro x y
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hsurj : Function.Surjective φ := dot_surjective hd
  let K := (Finset.univ.filter fun v : Fin k → F => φ v = 0).card
  have hfiber (y : F) :
      (Finset.univ.filter fun v : Fin k → F => φ v = y).card = K := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj y) (hsurj 0)
  have hsum : Fintype.card (Fin k → F) =
      ∑ y : F, (Finset.univ.filter fun v : Fin k → F => φ v = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin k → F)))
      (t := (Finset.univ : Finset F)) (f := φ)
      (fun _ _ => Finset.mem_univ _))
  rw [hsum]
  simp_rw [hfiber]
  simp [K, φ, Nat.mul_comm]

lemma exists_dot_offdiag_le {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      Fintype.card F *
          ((A.product A).filter fun xy =>
            xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card ≤
        A.card * (A.card - 1) := by
  classical
  let P := A.offDiag
  let off : (Fin k → F) → ℕ := fun v =>
    ∑ xy ∈ P, if dot xy.1 v = dot xy.2 v then 1 else 0
  have hPcard : P.card = A.card * (A.card - 1) := by
    simp only [P, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  have hinner (xy : (Fin k → F) × (Fin k → F)) (hxy : xy ∈ P) :
      Fintype.card F *
          (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) =
        Fintype.card (Fin k → F) := by
    have hne : xy.1 ≠ xy.2 := by
      exact (Finset.mem_offDiag.mp (by simpa only [P] using hxy)).2.2
    have hd : xy.1 - xy.2 ≠ 0 := sub_ne_zero.mpr hne
    have hfilter :
        (Finset.univ.filter fun v : Fin k → F => dot xy.1 v = dot xy.2 v).card =
          (Finset.univ.filter fun v : Fin k → F => dot (xy.1 - xy.2) v = 0).card := by
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    rw [← Finset.card_filter, hfilter, Nat.mul_comm]
    exact dot_zero_fiber_card_mul hd
  have htotal :
      (∑ v : Fin k → F, Fintype.card F * off v) =
        ∑ _v : Fin k → F, P.card := by
    calc
      (∑ v : Fin k → F, Fintype.card F * off v) =
          ∑ v : Fin k → F, ∑ xy ∈ P,
            Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
              simp only [off, Finset.mul_sum]
      _ = ∑ xy ∈ P, ∑ v : Fin k → F,
          Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ xy ∈ P, Fintype.card F *
            (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro xy _
              rw [Finset.mul_sum]
      _ = ∑ _xy ∈ P, Fintype.card (Fin k → F) := by
            apply Finset.sum_congr rfl
            intro xy hxy
            exact hinner xy hxy
      _ = ∑ _v : Fin k → F, P.card := by simp [Nat.mul_comm]
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin k → F))) Finset.univ_nonempty
    (show (∑ v : Fin k → F, Fintype.card F * off v) ≤
      ∑ _v : Fin k → F, P.card by rw [htotal])
  refine ⟨v, ?_⟩
  rw [← hPcard]
  have hoff :
      ((A.product A).filter fun xy =>
        xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card = off v := by
    rw [Finset.card_filter]
    simp only [off, P]
    rw [show A.offDiag = (A ×ˢ A).filter (fun xy => xy.1 ≠ xy.2) by
      ext xy
      rcases xy with ⟨x, y⟩
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hx, hy, hne⟩
        exact ⟨⟨hx, hy⟩, hne⟩
      · rintro ⟨⟨hx, hy⟩, hne⟩
        exact ⟨hx, hy, hne⟩]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hne : xy.1 ≠ xy.2 <;>
      by_cases heq : dot xy.1 v = dot xy.2 v <;> simp [hne, heq]
  simpa only [hoff] using hv

/-- Some linear functional has an image whose density is at least
`|A| / (|F| + |A| - 1)`.  This is the quantitative form of the collision
argument: unlike `exists_dot_surjective_of_card_sq_lt`, it does not require the
image to be all of `F`. -/
theorem exists_dot_image_card_bound {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      A.card * Fintype.card F ≤
        (A.image (fun x => dot x v)).card * (Fintype.card F + A.card - 1) := by
  classical
  by_cases hA : A.card = 0
  · refine ⟨0, ?_⟩
    simp [hA]
  obtain ⟨v, hoff⟩ := exists_dot_offdiag_le A
  let q := Fintype.card F
  let N := A.card
  let O := ((A.product A).filter fun xy =>
    xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card
  let E := ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v).card
  let c : F → ℕ := fun y => (A.filter fun x => dot x v = y).card
  let support : Finset F := Finset.univ.filter fun y => c y ≠ 0
  have hYeq : support = A.image (fun x => dot x v) := by
    ext y
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, c]
    exact Finset.fiber_card_ne_zero_iff_mem_image A (fun x => dot x v) y
  have hsumc : ∑ y ∈ support, c y = N := by
    have hall : ∑ y : F, c y = A.card := by
      symm
      simpa only [c] using (Finset.card_eq_sum_card_fiberwise
        (s := A) (t := (Finset.univ : Finset F)) (f := fun x => dot x v)
        (fun _ _ => Finset.mem_univ _))
    change ∑ y ∈ support, c y = A.card
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    exact hyY
  have hsumsq : ∑ y ∈ support, c y ^ 2 = E := by
    have hall : ∑ y : F, c y ^ 2 = E := by
      simp only [c, E, Finset.card_filter]
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp
      rw [Finset.card_filter, Finset.sum_product_right]
      simp_rw [Finset.card_filter]
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    simp [hyY]
  have hE : E = N + O := by
    simp only [E, N, O]
    rw [show ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v) =
        A.diag ∪ ((A.product A).filter fun xy =>
          xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v) by
      ext xy
      rcases xy with ⟨x, y⟩
      by_cases hxy : x = y <;> simp [hxy]]
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hdiag hoffdiag
      simp only [Finset.mem_diag] at hdiag
      simp only [Finset.mem_filter] at hoffdiag
      exact hoffdiag.2.1 hdiag.2
  have hlower : N ^ 2 ≤ support.card * E := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := support) (f := c)
    rw [hsumc, hsumsq] at hcauchy
    exact hcauchy
  have hupper : q * O ≤ N * (N - 1) := by
    simpa only [q, N, O] using hoff
  have hNpos : 0 < N := by simpa only [N] using Nat.pos_of_ne_zero hA
  have hcombined : q * N ^ 2 ≤
      support.card * (q * N + N * (N - 1)) := by
    calc
      q * N ^ 2 ≤ q * (support.card * E) := Nat.mul_le_mul_left q hlower
      _ = support.card * (q * N + q * O) := by rw [hE]; ring
      _ ≤ support.card * (q * N + N * (N - 1)) := by
        exact Nat.mul_le_mul_left support.card (Nat.add_le_add_left hupper (q * N))
  have hleft : q * N ^ 2 = N * (N * q) := by ring
  have hright : support.card * (q * N + N * (N - 1)) =
      N * (support.card * (q + N - 1)) := by
    have hN : 1 ≤ N := hNpos
    rw [show q + N - 1 = q + (N - 1) by omega]
    ring
  rw [hleft, hright] at hcombined
  refine ⟨v, ?_⟩
  rw [← hYeq]
  simpa only [q, N] using Nat.le_of_mul_le_mul_left hcombined hNpos

theorem exists_dot_surjective_of_card_sq_lt {k : ℕ} (A : Finset (Fin k → F))
    (hlarge : (Fintype.card F - 1) ^ 2 < A.card) :
    ∃ v : Fin k → F, A.image (fun x => dot x v) = Finset.univ := by
  classical
  obtain ⟨v, hoff⟩ := exists_dot_offdiag_le A
  refine ⟨v, ?_⟩
  by_contra hsurj
  let q := Fintype.card F
  let N := A.card
  let O := ((A.product A).filter fun xy =>
    xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card
  let E := ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v).card
  let c : F → ℕ := fun y => (A.filter fun x => dot x v = y).card
  let support : Finset F := Finset.univ.filter fun y => c y ≠ 0
  have hYeq : support = A.image (fun x => dot x v) := by
    ext y
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, c]
    exact Finset.fiber_card_ne_zero_iff_mem_image A (fun x => dot x v) y
  have hYcard : support.card ≤ q - 1 := by
    have hproper : support ⊂ (Finset.univ : Finset F) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro hYu
      apply hsurj
      rw [← hYeq, hYu]
    have hlt := Finset.card_lt_card hproper
    have : support.card ≤ Fintype.card F - 1 := by
      have hlt' : support.card < Fintype.card F := by
        simpa only [Finset.card_univ] using hlt
      omega
    simpa only [q] using this
  have hsumc : ∑ y ∈ support, c y = N := by
    have hall : ∑ y : F, c y = A.card := by
      symm
      simpa only [c] using (Finset.card_eq_sum_card_fiberwise
        (s := A) (t := (Finset.univ : Finset F)) (f := fun x => dot x v)
        (fun _ _ => Finset.mem_univ _))
    change ∑ y ∈ support, c y = A.card
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    exact hyY
  have hsumsq : ∑ y ∈ support, c y ^ 2 = E := by
    have hall : ∑ y : F, c y ^ 2 = E := by
      simp only [c, E, Finset.card_filter]
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp
      rw [Finset.card_filter, Finset.sum_product_right]
      simp_rw [Finset.card_filter]
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    simp [hyY]
  have hE : E = N + O := by
    simp only [E, N, O]
    rw [show ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v) =
        A.diag ∪ ((A.product A).filter fun xy =>
          xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v) by
      ext xy
      rcases xy with ⟨x, y⟩
      by_cases hxy : x = y <;> simp [hxy]]
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hdiag hoffdiag
      simp only [Finset.mem_diag] at hdiag
      simp only [Finset.mem_filter] at hoffdiag
      exact hoffdiag.2.1 hdiag.2
  have hlower : N ^ 2 ≤ (q - 1) * E := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := support) (f := c)
    rw [hsumc, hsumsq] at hcauchy
    exact hcauchy.trans (Nat.mul_le_mul_right E hYcard)
  have hupper : q * O ≤ N * (N - 1) := by
    simpa only [q, N, O] using hoff
  rw [hE] at hlower
  have hq : 1 ≤ q := by
    have : 0 < Fintype.card F := Fintype.card_pos
    simp only [q]
    omega
  have hNpos : 0 < N := by
    have : 0 < (q - 1) ^ 2 + 1 := by omega
    have := hlarge
    simp only [N] at this ⊢
    omega
  have hN : 1 ≤ N := hNpos
  have hlowerZ0 : (N : ℤ) ^ 2 ≤ ((q - 1 : ℕ) : ℤ) * ((N : ℤ) + (O : ℤ)) := by
    exact_mod_cast hlower
  have hlowerZ : (N : ℤ) ^ 2 ≤ ((q : ℤ) - 1) * ((N : ℤ) + (O : ℤ)) := by
    simpa only [Nat.cast_sub hq, Nat.cast_one] using hlowerZ0
  have hupperZ0 : (q : ℤ) * (O : ℤ) ≤ (N : ℤ) * ((N - 1 : ℕ) : ℤ) := by
    exact_mod_cast hupper
  have hupperZ : (q : ℤ) * (O : ℤ) ≤ (N : ℤ) * ((N : ℤ) - 1) := by
    simpa only [Nat.cast_sub hN, Nat.cast_one] using hupperZ0
  have hlargeZ0 : (((q - 1 : ℕ) : ℤ) ^ 2) < (N : ℤ) := by
    exact_mod_cast (show (q - 1) ^ 2 < N by simpa only [q, N] using hlarge)
  have hlargeZ : ((q : ℤ) - 1) ^ 2 < (N : ℤ) := by
    simpa only [Nat.cast_sub hq, Nat.cast_one] using hlargeZ0
  have hqZ : 0 ≤ (q : ℤ) := by omega
  have hqZone : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hqm1Z : 0 ≤ (q : ℤ) - 1 := by omega
  have hlowerScaled := mul_le_mul_of_nonneg_left hlowerZ hqZ
  have hupperScaled := mul_le_mul_of_nonneg_left hupperZ hqm1Z
  have hNZ : 0 < (N : ℤ) := by exact_mod_cast hNpos
  nlinarith

open ToyProblem
open scoped NNReal

/-- Quantitative fixed-word collision bound.  A family of `N` distinct close
messages yields winning-set density at least `N / (|F| + N - 1)`; no
surjectivity assumption on the selected linear functional is needed. -/
theorem winningSetDensity_ge_of_fixed_word_list
    {ι B : Type} [Fintype ι]
    [Fintype B] [DecidableEq B] [AddCommGroup B] [Module F B]
    {k m : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → B)) (δ : ℝ≥0)
    (hlower : ((m - 1 : ℕ) : ℝ) <
      (1 - (δ : ℝ)) * Fintype.card ι)
    (hupper : (1 - (δ : ℝ)) * Fintype.card ι ≤ (m : ℝ))
    {J : Type} [Fintype J] [DecidableEq J]
    (p : J → Fin k → F) (T : J → Finset ι) (f : ι → B)
    (hp : Function.Injective p)
    (hJpos : 0 < Fintype.card J)
    (hTcard : ∀ a, (T a).card = m)
    (hag : ∀ a i, i ∈ T a → f i = enc (p a) i)
    (hzero : ∀ (u : Fin k → F) (S : Finset ι), m ≤ S.card →
      (∀ i ∈ S, enc u i = 0) → u = 0) :
    (Fintype.card J : ℝ≥0) /
        ((Fintype.card F + Fintype.card J - 1 : ℕ) : ℝ≥0) ≤
      winningSetDensity enc δ := by
  classical
  let P : Finset (Fin k → F) := Finset.univ.image p
  have hPcard : P.card = Fintype.card J := by
    simp only [P, Finset.card_image_of_injective Finset.univ hp, Finset.card_univ]
  obtain ⟨v, hv⟩ := exists_dot_image_card_bound P
  let img : Finset F := P.image (fun u => dot u v)
  have hv' : Fintype.card J * Fintype.card F ≤
      img.card * (Fintype.card F + Fintype.card J - 1) := by
    simpa only [img, hPcard] using hv
  let x : ViolatingInstance enc δ :=
    { v := v
      μ₁ := 0
      μ₂ := 1
      f₁ := f
      f₂ := 0
      violates := by
        intro hrel
        rcases hrel with ⟨W, ⟨M, hW, hc⟩, S, hS, hA⟩
        have hmS : m ≤ S.card := by
          have hltR : ((m - 1 : ℕ) : ℝ) < (S.card : ℝ) :=
            lt_of_lt_of_le hlower hS
          have hlt : m - 1 < S.card := by exact_mod_cast hltR
          omega
        have henczero : ∀ i ∈ S, enc (M 1) i = 0 := by
          intro i hi
          have h := hA 1 i hi
          rw [hW 1] at h
          simpa using h.symm
        have hmzero : M 1 = 0 := hzero (M 1) S hmS henczero
        have hc1 := hc 1
        rw [hmzero] at hc1
        simp at hc1 }
  have hYsub : (img : Set F) ⊆
      winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ := by
    intro γ hγ
    have hγ' : γ ∈ img := hγ
    simp only [img, Finset.mem_image] at hγ'
    rcases hγ' with ⟨u, huP, huγ⟩
    simp only [P, Finset.mem_image, Finset.mem_univ, true_and] at huP
    rcases huP with ⟨a, rfl⟩
    simp only [winningSetFor, Set.mem_setOf_eq]
    refine ⟨![enc (p a)], ?_, T a, ?_, ?_⟩
    · refine ⟨![p a], ?_, ?_⟩
      · intro i
        fin_cases i
        rfl
      · intro i
        fin_cases i
        simpa [x, dot] using huγ
    · rw [hTcard]
      simpa using hupper
    · intro i j hj
      fin_cases i
      simpa [x] using hag a j hj
  have hYcard : img.card ≤
      (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard := by
    rw [← Set.ncard_coe_finset img]
    exact Set.ncard_le_ncard hYsub (Set.toFinite _)
  have hnat : Fintype.card J * Fintype.card F ≤
      (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard *
        (Fintype.card F + Fintype.card J - 1) :=
    hv'.trans (Nat.mul_le_mul_right _ hYcard)
  refine le_trans ?_ (winningSetRatio_le_winningSetDensity x)
  rw [winningSetRatio]
  have hqpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hdenNat : 0 < Fintype.card F + Fintype.card J - 1 := by
    have hq : 0 < Fintype.card F := Fintype.card_pos
    omega
  have hden : (0 : ℝ≥0) <
      ((Fintype.card F + Fintype.card J - 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast hdenNat
  rw [div_le_div_iff₀ hden hqpos]
  exact_mod_cast hnat

theorem winningSetSoundness_eq_one_of_large_fixed_word_list
    {ι B : Type} [Fintype ι]
    [Fintype B] [DecidableEq B] [AddCommGroup B] [Module F B]
    {k m : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → B)) (δ : ℝ≥0)
    (hlower : ((m - 1 : ℕ) : ℝ) <
      (1 - (δ : ℝ)) * Fintype.card ι)
    (hupper : (1 - (δ : ℝ)) * Fintype.card ι ≤ (m : ℝ))
    {J : Type} [Fintype J] [DecidableEq J]
    (p : J → Fin k → F) (T : J → Finset ι) (f : ι → B)
    (hp : Function.Injective p)
    (hlarge : (Fintype.card F - 1) ^ 2 < Fintype.card J)
    (hTcard : ∀ a, (T a).card = m)
    (hag : ∀ a i, i ∈ T a → f i = enc (p a) i)
    (hzero : ∀ (u : Fin k → F) (S : Finset ι), m ≤ S.card →
      (∀ i ∈ S, enc u i = 0) → u = 0) :
    winningSetDensity enc δ = 1 := by
  classical
  let P : Finset (Fin k → F) := Finset.univ.image p
  have hPcard : P.card = Fintype.card J := by
    simp only [P, Finset.card_image_of_injective Finset.univ hp, Finset.card_univ]
  obtain ⟨v, hv⟩ := exists_dot_surjective_of_card_sq_lt P (by simpa [hPcard] using hlarge)
  have hex (γ : F) : ∃ a : J, dot (p a) v = γ := by
    have hγ : γ ∈ P.image (fun u => dot u v) := by rw [hv]; exact Finset.mem_univ γ
    simp only [Finset.mem_image] at hγ
    rcases hγ with ⟨u, huP, huγ⟩
    simp only [P, Finset.mem_image, Finset.mem_univ, true_and] at huP
    rcases huP with ⟨a, rfl⟩
    exact ⟨a, huγ⟩
  let pick : F → J := fun γ => Classical.choose (hex γ)
  have hpick (γ : F) : dot (p (pick γ)) v = γ := Classical.choose_spec (hex γ)
  let x : ViolatingInstance enc δ :=
    { v := v
      μ₁ := 0
      μ₂ := 1
      f₁ := f
      f₂ := 0
      violates := by
        intro hrel
        rcases hrel with ⟨W, ⟨M, hW, hc⟩, S, hS, hA⟩
        have hmS : m ≤ S.card := by
          have hltR : ((m - 1 : ℕ) : ℝ) < (S.card : ℝ) :=
            lt_of_lt_of_le hlower hS
          have hlt : m - 1 < S.card := by exact_mod_cast hltR
          omega
        have henczero : ∀ i ∈ S, enc (M 1) i = 0 := by
          intro i hi
          have h := hA 1 i hi
          rw [hW 1] at h
          simpa using h.symm
        have hmzero : M 1 = 0 := hzero (M 1) S hmS henczero
        have hc1 := hc 1
        rw [hmzero] at hc1
        simp at hc1 }
  have hwin : winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ = Set.univ := by
    ext γ
    simp only [Set.mem_univ, iff_true, winningSetFor, Set.mem_setOf_eq]
    refine ⟨![enc (p (pick γ))], ?_, T (pick γ), ?_, ?_⟩
    · refine ⟨![p (pick γ)], ?_, ?_⟩
      · intro i
        fin_cases i
        rfl
      · intro i
        fin_cases i
        simpa [x, dot] using hpick γ
    · rw [hTcard]
      simpa using hupper
    · intro i j hj
      fin_cases i
      simpa [x] using hag (pick γ) j hj
  apply le_antisymm (winningSetDensity_le_one enc δ)
  calc
    1 = winningSetRatio x := by
      rw [winningSetRatio, hwin, Set.ncard_univ, Nat.card_eq_fintype_card]
      simp
    _ ≤ winningSetDensity enc δ := winningSetRatio_le_winningSetDensity x

theorem winningSetSoundness_eq_one_of_many_interpolation_sets
    {ι B : Type} [Fintype ι]
    [Fintype B] [DecidableEq B] [AddCommGroup B] [Module F B]
    {k m : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → B)) (δ : ℝ≥0)
    (hlower : ((m - 1 : ℕ) : ℝ) <
      (1 - (δ : ℝ)) * Fintype.card ι)
    (hupper : (1 - (δ : ℝ)) * Fintype.card ι ≤ (m : ℝ))
    (f : ι → B)
    (hchoose : (Fintype.card F - 1) ^ 2 < Nat.choose (Fintype.card ι) m)
    (hinterpolate : ∀ T : Set.powersetCard ι m,
      ∃ u : Fin k → F, ∀ i ∈ (T : Finset ι), f i = enc u i)
    (hfar : ∀ (u : Fin k → F) (S : Finset ι), m < S.card →
      (∀ i ∈ S, f i = enc u i) → False)
    (hzero : ∀ (u : Fin k → F) (S : Finset ι), m ≤ S.card →
      (∀ i ∈ S, enc u i = 0) → u = 0) :
    winningSetDensity enc δ = 1 := by
  classical
  let p : Set.powersetCard ι m → Fin k → F :=
    fun T => Classical.choose (hinterpolate T)
  have hp_spec (T : Set.powersetCard ι m) :
      ∀ i ∈ (T : Finset ι), f i = enc (p T) i :=
    Classical.choose_spec (hinterpolate T)
  have hp : Function.Injective p := by
    intro S T hpST
    by_contra hST
    have hcardUnion : m < ((S : Finset ι) ∪ (T : Finset ι)).card := by
      obtain ⟨i, hiS, hiT⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne S T).mp hST
      have hTsub : (T : Finset ι) ⊆ (S : Finset ι) ∪ (T : Finset ι) :=
        Finset.subset_union_right
      have hTstrict : (T : Finset ι) ⊂ (S : Finset ι) ∪ (T : Finset ι) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, ?_⟩
        intro heq
        have hiUnion : i ∈ (S : Finset ι) ∪ (T : Finset ι) :=
          Finset.mem_union_left _ hiS
        have : i ∈ (T : Finset ι) := by rwa [← heq] at hiUnion
        exact hiT this
      have hlt := Finset.card_lt_card hTstrict
      simpa only [Set.powersetCard.card_eq T] using hlt
    apply hfar (p S) ((S : Finset ι) ∪ (T : Finset ι)) hcardUnion
    intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · exact hp_spec S i hiS
    · rw [hpST]
      exact hp_spec T i hiT
  apply winningSetSoundness_eq_one_of_large_fixed_word_list enc δ hlower hupper
    (J := Set.powersetCard ι m) p (fun T => (T : Finset ι)) f hp
  · simpa only [← Nat.card_eq_fintype_card, Set.powersetCard.card] using hchoose
  · exact Set.powersetCard.card_eq
  · exact hp_spec
  · exact hzero

end ProximityPrize.SubmissionUpper.HalfRadiusCollision
