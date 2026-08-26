import ProximityPrize.SubmissionLower.BCHKSFullCoreGoodOwnerCover6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSResidualNearFullProfile6400
theorem nearFull_profile_rigid
    {I : Type*} [DecidableEq I]
    (D A : Finset I) (order : I -> Nat) (d a c : Nat)
    (hAsub : A ⊆ D)
    (hAcard : A.card = a)
    (horder : ∀ i ∈ D, order i <= d)
    (hFullCard : (D.filter fun i => order i = d).card = c)
    (hca : c <= a)
    (hdefect : A.sum (fun i => d - order i) <= a - c) :
    let Full := D.filter fun i => order i = d
    Full ⊆ A /\
      A.sum (fun i => d - order i) = a - c /\
      ∀ i ∈ A \ Full, order i = d - 1 := by
  classical
  dsimp only
  let Full := D.filter fun i => order i = d
  let Bad := A.filter fun i => order i ≠ d
  have hBadSub : Bad ⊆ A := Finset.filter_subset _ _
  have hBadTerm : ∀ i ∈ Bad, 1 <= d - order i := by
    intro i hi
    have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
    have hine : order i ≠ d := (Finset.mem_filter.mp hi).2
    have hle := horder i (hAsub hiA)
    omega
  have hBadLeSum : Bad.card <= Bad.sum (fun i => d - order i) := by
    calc
      Bad.card = ∑ _i ∈ Bad, 1 := by simp
      _ <= Bad.sum (fun i => d - order i) := by
        exact Finset.sum_le_sum (fun i hi => hBadTerm i hi)
  have hBadSumLe : Bad.sum (fun i => d - order i) <=
      A.sum (fun i => d - order i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBadSub (by simp)
  have hBadCardLe : Bad.card <= a - c :=
    hBadLeSum.trans (hBadSumLe.trans hdefect)
  have hGoodEq : A.filter (fun i => order i = d) = A ∩ Full := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_inter, Full]
    constructor
    · rintro ⟨hiA, hiorder⟩
      exact ⟨hiA, hAsub hiA, hiorder⟩
    · rintro ⟨hiA, hiFull⟩
      exact ⟨hiA, hiFull.2⟩
  have hpartition :
      (A.filter fun i => order i = d).card + Bad.card = A.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Bad]
      tauto
    · exact Finset.disjoint_left.mpr (by
        intro i hiEq hiNe
        exact (Finset.mem_filter.mp hiNe).2
          (Finset.mem_filter.mp hiEq).2)
  have hGoodSub : A.filter (fun i => order i = d) ⊆ Full := by
    rw [hGoodEq]
    exact Finset.inter_subset_right
  have hGoodCardLe : (A.filter fun i => order i = d).card <= c := by
    rw [← hFullCard]
    exact Finset.card_le_card hGoodSub
  have hGoodCard : (A.filter fun i => order i = d).card = c := by
    rw [hAcard] at hpartition
    omega
  have hGoodEqFull : A.filter (fun i => order i = d) = Full := by
    apply Finset.eq_of_subset_of_card_le hGoodSub
    rw [hGoodCard, hFullCard]
  have hFullSub : Full ⊆ A := by
    rw [← hGoodEqFull]
    exact Finset.filter_subset _ _
  have hBadCard : Bad.card = a - c := by
    rw [hAcard, hGoodCard] at hpartition
    omega
  have hBadSumEq : Bad.sum (fun i => d - order i) = Bad.card := by
    have : Bad.sum (fun i => d - order i) <= a - c :=
      hBadSumLe.trans hdefect
    omega
  have hDefectEq : A.sum (fun i => d - order i) = a - c := by
    have hsumLe := hdefect
    have hsumGe : a - c <= A.sum (fun i => d - order i) := by
      rw [← hBadCard]
      exact hBadLeSum.trans hBadSumLe
    omega
  refine ⟨hFullSub, hDefectEq, ?_⟩
  intro i hi
  have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
  have hiNotFull : i ∉ Full := (Finset.mem_sdiff.mp hi).2
  have hiNe : order i ≠ d := by
    intro hieq
    exact hiNotFull (Finset.mem_filter.mpr ⟨hAsub hiA, hieq⟩)
  have hiBad : i ∈ Bad := Finset.mem_filter.mpr ⟨hiA, hiNe⟩
  have htermLe : d - order i <= 1 := by
    have hother : (Bad.erase i).card <=
        (Bad.erase i).sum (fun j => d - order j) := by
      calc
        (Bad.erase i).card = ∑ _j ∈ Bad.erase i, 1 := by simp
        _ <= (Bad.erase i).sum (fun j => d - order j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hBadTerm j (Finset.mem_of_mem_erase hj)
    have hsumErase := Bad.sum_erase_add (fun j => d - order j) hiBad
    have hcardErase := Finset.card_erase_of_mem hiBad
    omega
  have hle := horder i (hAsub hiA)
  omega
end BCHKSResidualNearFullProfile6400
end ProximityPrize.SubmissionLower
