import ProximityPrize.SubmissionLower.BCHKSParameters6401
import ProximityPrize.SubmissionLower.BCHKSSubfieldListBudgetAudit6401
import ProximityPrize.SubmissionLower.JohnsonFamily
namespace ProximityPrize.SubmissionLower
namespace BCHKSList6401
open ProximityPrize.Benchmark
open scoped NNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def listBound6401 : ℕ := 17045844
noncomputable abbrev SquaredCode6401 :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
      IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))
set_option maxRecDepth 20000 in
theorem squaredCode_minDistance6401 :
    Code.minDist SquaredCode6401 = 131073 := by
  calc
    Code.minDist SquaredCode6401 =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance
abbrev SquaredWord6401 :=
  IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field
def agreementCoordinates6401
    (y c : SquaredWord6401) : Finset IRSProfile.Index :=
  {i | c i = y i}
theorem agreementCoordinates_card6401 (y c : SquaredWord6401) :
    (agreementCoordinates6401 y c).card = Code.agree c y := by
  rfl
theorem close_agreement_card_ge6401
    (y c : SquaredWord6401)
    (hc : c ∈ Code.closeCodewordsRel SquaredCode6401 y
      (bchksRadius6401 : ℝ)) :
    bchksAgreements6401 ≤ (agreementCoordinates6401 y c).card := by
  have hnNat : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hm := (Code.mem_closeCodewordsRel_iff.mp hc).2
  rw [Code.relHammingDist_coe] at hm
  have hdist : hammingDist y c ≤ bchksErrors6401 := by
    rw [div_le_iff₀ (by positivity)] at hm
    have hfloor := Nat.le_floor hm
    simpa only [bchksRadius6401_floor] using hfloor
  have hsum : Code.agree c y + hammingDist c y = 262144 := by
    simpa only [hnNat] using
      (Code.agree_add_hammingDist (u := c) (v := y))
  rw [hammingDist_comm] at hdist
  rw [agreementCoordinates_card6401]
  norm_num [bchksAgreements6401, bchksErrors6401] at hdist ⊢
  omega
theorem pair_agreement_card_le6401
    (y c d : SquaredWord6401)
    (hc : c ∈ Code.closeCodewordsRel SquaredCode6401 y
      (bchksRadius6401 : ℝ))
    (hd : d ∈ Code.closeCodewordsRel SquaredCode6401 y
      (bchksRadius6401 : ℝ))
    (hne : c ≠ d) :
    (agreementCoordinates6401 c d).card ≤ 131071 := by
  have hdist : 131073 ≤ hammingDist c d := by
    rw [← squaredCode_minDistance6401]
    exact Code.minDist_le_dist
      (Code.mem_closeCodewordsRel_iff.mp hc).1
      (Code.mem_closeCodewordsRel_iff.mp hd).1 hne
  have hnNat : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  rw [hammingDist_comm] at hdist
  have hsum : Code.agree d c + hammingDist d c = 262144 := by
    simpa only [hnNat] using
      (Code.agree_add_hammingDist (u := d) (v := c))
  rw [agreementCoordinates_card6401]
  omega
structure ExactAgreementFamily6401
    (y : SquaredWord6401) (T : Finset SquaredWord6401) where
  coords : {c // c ∈ T} → Finset IRSProfile.Index
  subset_agreement : ∀ c, coords c ⊆ agreementCoordinates6401 y c.1
  card_eq : ∀ c, (coords c).card = bchksAgreements6401
  pair_intersection_le : ∀ c d, c ≠ d →
    ((coords c) ∩ (coords d)).card ≤ 131071
theorem exists_exactAgreementFamily6401
    (y : SquaredWord6401) (T : Finset SquaredWord6401)
    (hT : ∀ c ∈ T,
      c ∈ Code.closeCodewordsRel SquaredCode6401 y
        (bchksRadius6401 : ℝ)) :
    Nonempty (ExactAgreementFamily6401 y T) := by
  classical
  have hexists : ∀ c : {c // c ∈ T},
      ∃ A : Finset IRSProfile.Index,
        A ⊆ agreementCoordinates6401 y c.1 ∧
          A.card = bchksAgreements6401 := by
    intro c
    obtain ⟨A, hsub, hcard⟩ := Finset.exists_subset_card_eq
      (close_agreement_card_ge6401 y c.1 (hT c.1 c.2))
    exact ⟨A, hsub, hcard⟩
  let coords : {c // c ∈ T} → Finset IRSProfile.Index :=
    fun c => Classical.choose (hexists c)
  have hsubset : ∀ c, coords c ⊆ agreementCoordinates6401 y c.1 :=
    fun c => (Classical.choose_spec (hexists c)).1
  have hcard : ∀ c, (coords c).card = bchksAgreements6401 :=
    fun c => (Classical.choose_spec (hexists c)).2
  refine ⟨{
    coords := coords
    subset_agreement := hsubset
    card_eq := hcard
    pair_intersection_le := ?_
  }⟩
  intro c d hcd
  have hval : c.1 ≠ d.1 := by
    intro h
    exact hcd (Subtype.ext h)
  have hpair := pair_agreement_card_le6401 y c.1 d.1
    (hT c.1 c.2) (hT d.1 d.2) hval
  calc
    ((coords c) ∩ (coords d)).card ≤
        (agreementCoordinates6401 c.1 d.1).card := by
      apply Finset.card_le_card
      intro i hi
      have hic := hsubset c (Finset.mem_inter.mp hi).1
      have hid := hsubset d (Finset.mem_inter.mp hi).2
      simp only [agreementCoordinates6401, Finset.mem_filter,
        Finset.mem_univ, true_and] at hic hid ⊢
      exact hid.trans hic.symm
    _ ≤ 131071 := hpair
open BCHKSSubfieldListBudgetAudit6401
def maxMCANumeratorAfterList6401 : ℕ :=
  exactFieldNumerator6401 - listBound6401
theorem exact_list_and_mca_ledger6401 :
    maxMCANumeratorAfterList6401 = 274980728094349243 ∧
      currentConservativeMCANumerator6401 + listBound6401 =
        274980700017045844 ∧
      maxMCANumeratorAfterList6401 -
          currentConservativeMCANumerator6401 = 28094349243 ∧
      2 ^ (128 : ℕ) *
          (currentConservativeMCANumerator6401 + listBound6401) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [maxMCANumeratorAfterList6401, exactFieldNumerator6401,
    listBound6401, currentConservativeMCANumerator6401]
end BCHKSList6401
end ProximityPrize.SubmissionLower
