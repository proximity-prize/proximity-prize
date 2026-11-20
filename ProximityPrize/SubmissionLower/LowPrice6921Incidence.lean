import ProximityPrize.SubmissionLower.LowFat6921
import ProximityPrize.SubmissionLower.Fast048
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowFat6921.Messages

open K1

theorem mono {w Γ Δ s} (h : LowFat6921.Messages w Γ s) (hsub : Δ ⊆ Γ) : LowFat6921.Messages w Δ s :=
  ⟨h.distinct.mono hsub, fun γ hg => h.degree γ (hsub hg), fun γ hg => h.hits γ (hsub hg)⟩

theorem old_degree {w Γ s} (h : LowFat6921.Messages w Γ s) (γ : K) (hg : γ ∈ Γ) :
    (s γ).natDegree ≤ 133671 :=
  (h.degree γ hg).trans (by decide)

end LowFat6921.Messages

namespace LowPrice6921

open Polynomial Finset K1 K1_13 K1_13_6 K1_13_5 ProximityPrize.Benchmark
open scoped BigOperators

noncomputable section

private theorem occupancy {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (marks : Finset α) (nodes : Finset ι) (T : α → Finset ι) (x t d : ℕ)
    (hT : ∀ a ∈ marks, T a ⊆ nodes ∧ (T a).card = x)
    (hpair : ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b → (T a ∩ T b).card ≤ t)
    (hocc : ∀ i ∈ nodes, (marks.filter fun a => i ∈ T a).card ≤ d) :
    (marks.card * x)^2 ≤ nodes.card * (marks.card * (x + (marks.card - 1)*t)) ∧
      marks.card * x ≤ nodes.card * d := by
  classical
  let occ (i : ι) := (marks.filter fun a => i ∈ T a).card
  have section_eq (V : Finset ι) (hV : V ⊆ nodes) :
      (nodes.filter fun i => i ∈ V) = V := by
    ext i
    exact mem_filter.trans ⟨And.right, fun hi => ⟨hV hi, hi⟩⟩
  have first : ∑ i ∈ nodes, occ i = marks.card * x := by
    calc
      _ = ∑ a ∈ marks, (T a).card := by
        simp only [occ, card_filter]
        rw [sum_comm]
        refine sum_congr rfl fun a ha => ?_
        rw [sum_boole, Nat.cast_id, section_eq _ (hT a ha).1]
      _ = _ := by rw [sum_congr rfl (fun a ha => (hT a ha).2), sum_const, smul_eq_mul]
  have second : ∑ i ∈ nodes, occ i ^ 2 =
      ∑ a ∈ marks, ∑ b ∈ marks, (T a ∩ T b).card := by
    simp only [occ, sq, card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have identity (i : ι) :
        (if i ∈ T a then 1 else 0 : ℕ) * (if i ∈ T b then 1 else 0) =
          if i ∈ T a ∩ T b then 1 else 0 := by
      by_cases h₁ : i ∈ T a <;> by_cases h₂ : i ∈ T b <;> simp [h₁, h₂]
    simp_rw [identity]
    rw [sum_boole, Nat.cast_id, section_eq _ (inter_subset_left.trans (hT a ha).1)]
  have row (a : α) (ha : a ∈ marks) :
      ∑ b ∈ marks, (T a ∩ T b).card ≤ x + (marks.card - 1) * t := by
    rw [← add_sum_erase marks _ ha, inter_self, (hT a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b ∈ marks.erase a, t := sum_le_sum fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _ := by rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
  have second_le :
      ∑ i ∈ nodes, occ i ^ 2 ≤ marks.card * (x + (marks.card - 1) * t) := by
    rw [second]
    exact (sum_le_sum row).trans_eq (by rw [sum_const, smul_eq_mul])
  have cs := sq_sum_le_card_mul_sum_sq (s := nodes) (f := occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le), ?_⟩
  rw [← first, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hocc

/-- The final step of the incidence inequality, with the benchmark's
two deficiencies 81975 and 46651. -/
private theorem incidence_arithmetic (m x : ℕ) (d : ℕ)
    (hm : 0 < m) (hx : 46651 ≤ x)
    (hsec : (m*x)^2 ≤ (x+81975) * (m * (x + (m-1)*(x-46651))))
    (hfirst : m*x ≤ (x+81975)*d) :
    46651*m ≤ 81975*d + 46651 := by
  have hcancel :
      m*x^2 ≤ (x+81975) * (x + (m-1)*(x-46651)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsec
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := by
    exact Int.ofNat_sub (by omega)
  have hX : ((x - 46651 : ℕ) : ℤ) = (x : ℤ)-46651 := Int.ofNat_sub hx
  have hcancelZ := (Int.ofNat_le.mpr hcancel)
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := (Int.ofNat_le.mpr hfirst)
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*81975 - ((m : ℤ)-1)*46651)*x ≥
      ((m : ℤ)-1)*81975*46651 := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(d : ℤ))*x ≤ (d : ℤ)*81975 := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbad : (d : ℤ)*81975 < ((m : ℤ)-1)*46651 := by omega
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*81975 - ((m : ℤ)-1)*46651 < ((m : ℤ)-(d : ℤ))*81975 := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (by norm_num : (0 : ℤ) ≤ 81975)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(d : ℤ))*81975*x ≤ (d : ℤ)*81975*81975 from by
        convert right using 1; ring))
  have bigger := mul_lt_mul_of_pos_right hbad (by norm_num : (0 : ℤ) < 81975)
  nlinarith only [impossible, bigger]

/-- A proper section occupancy bound d implies fixed-word capacity
(81975/46651)d + 1. Common agreement nodes are removed before counting. -/
private theorem section_capacity_new {w Γ s} (h : LowFat6921.Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46651 * Γ.card ≤ 81975*d + 46651 := by
  classical
  by_cases hm : Γ.card ≤ 1
  · omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ Γ) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ Γ) : 180169 ≤ (hits γ).card := by
    obtain ⟨T, hT, ht⟩ := h.hits γ hγ
    exact hT.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, ht i hi⟩)
  have pair_count (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ 133518 := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < Γ.card)
  have hcommon : common.card ≤ 133518 :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 180169 - common.card
  let t := 133518 - common.card
  have ht : t = x - 46651 := by dsimp [t, x]; omega
  have hx : 46651 ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 81975 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) :
      ∃ T : Finset I, γ ∈ Γ → T ⊆ hits γ \ common ∧ T.card = x := by
    by_cases hγ : γ ∈ Γ
    · have hc := hit_count γ hγ
      have hd : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨T, hT, hcT⟩ := exists_subset_card_eq hd
      exact ⟨T, fun _ => ⟨hT, hcT⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose T hT using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ Γ) : T γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hT γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (T a ∩ T b).card ≤ t := by
    have cover : (T a ∩ T b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with ht' | hc
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hT a ha).1 (mem_inter.mp ht').1)).1,
          (mem_sdiff.mp ((hT b hb).1 (mem_inter.mp ht').2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hc, common_le b hb hc⟩
    have disj : Disjoint (T a ∩ T b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) :
      (Γ.filter fun γ => i ∈ T γ).card ≤ d := by
    have proper : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hT γ hγ).1 hi)).1).2⟩
  obtain ⟨sec, first⟩ := occupancy Γ nodes T x t d
    (fun γ hγ => ⟨into_nodes γ hγ, (hT γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at sec
  rw [hnodes] at first
  exact incidence_arithmetic _ _ _ (by omega) hx sec first


theorem hit_ratio_comparison : (46594 : ℕ) * 81975 ≤ 46651 * 81879 := by decide

/-- Transport the exact incidence inequality to the published tariff constants. -/
theorem section_capacity {w Γ s} (h : LowFat6921.Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46594 * Γ.card ≤ 81879 * d + 46594 := by
  have hcount := Nat.mul_le_mul_left 46594 (section_capacity_new h d hsection)
  have hratio := Nat.mul_le_mul_right d hit_ratio_comparison
  have hcancel (m d : ℕ) (hc : 46594 * (46651 * m) ≤ 46594 * (81975 * d + 46651))
      (hr : (46594 * 81975) * d ≤ (46651 * 81879) * d) :
      46594 * m ≤ 81879 * d + 46594 := by omega
  exact hcancel Γ.card d hcount hratio

theorem nodeCapacity_count {w Γ s d} (h : LowFat6921.Messages w Γ s) (hc : NodeCapacity w Γ s d) :
    46594 * Γ.card ≤ 81879 * d + 46594 := by
  obtain ⟨persistent, hall, hcap⟩ := hc
  apply section_capacity h d
  intro i hi
  apply hcap
  intro hp
  obtain ⟨γ, hg, hn⟩ := hi
  exact hn (hall i hp γ hg)

theorem curveCount_le_twice_degree {w Γ s d} (h : LowFat6921.Messages w Γ s) (hd : 0 < d)
    (hc : NodeCapacity w Γ s d) : Γ.card ≤ 2*d := by
  have hcount := nodeCapacity_count h hc
  omega

theorem curve_capacity {w Γ s d} (h : LowFat6921.Messages w Γ s) (hc : CurveSections Γ s d) :
    46594 * Γ.card ≤ 81879*d + 46594 :=
  section_capacity h d (fun i => hc (node i) (w i))

theorem curve_capacity_integral {w Γ s d} (h : LowFat6921.Messages w Γ s)
    (hc : CurveSections Γ s d) (hd : 0 < d) : Γ.card ≤ 2*d := by
  have := curve_capacity h hc
  omega

theorem piece_curve_capacity {w Γ s} (C : Pieces Γ) (h : LowFat6921.Messages w Γ s)
    (hc : C.curves s) : 46594 * C.union.card ≤ 81879 * C.total + 46594 * C.n := by
  classical
  have hc' (i : Fin C.n) := curve_capacity (h.mono (C.subset i)) (hc i)
  calc
    _ ≤ 46594 * ∑ i, (C.piece i).card :=
      Nat.mul_le_mul_left _ (by exact card_biUnion_le)
    _ = ∑ i, 46594 * (C.piece i).card := by rw [mul_sum]
    _ ≤ ∑ i : Fin C.n, (81879 * C.degree i + 46594) := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, sum_add_distrib, mul_sum, Nat.mul_comm]

theorem piece_curve_capacity_integral {w Γ s} (C : Pieces Γ) (h : LowFat6921.Messages w Γ s)
    (hc : C.curves s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 2*C.total := by
  classical
  have hc' (i : Fin C.n) := curve_capacity_integral (h.mono (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 2 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]

theorem surface_capacity {w Γ s d} (h : LowFat6921.Messages w Γ s)
    (hs : SurfaceSections Γ s d) (hd : 0 < d) : Γ.card ≤ 4*d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ 2*d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := h.mono (filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (card_le_card hC).trans ((piece_curve_capacity_integral C hH hc hpos).trans
      (Nat.mul_le_mul_left 2 hdeg))
  have := section_capacity h (2*d) hsection
  omega

theorem piece_surface_capacity {w Γ s} (C : Pieces Γ) (h : LowFat6921.Messages w Γ s)
    (hc : C.surfaces s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 4*C.total := by
  classical
  have hc' (i : Fin C.n) := surface_capacity (h.mono (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 4 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]

theorem family_count {w Γ s} (C : NodeFamily w Γ s) (h : LowFat6921.Messages w Γ s) :
    46594 * C.labels.card ≤ 81879 * C.totalCap + 46594 * C.n := by
  classical
  calc
    46594 * C.labels.card ≤ 46594 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46594 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (81879 * C.cap i + 46594) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 81879 * C.totalCap + 46594 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

end
end LowPrice6921
