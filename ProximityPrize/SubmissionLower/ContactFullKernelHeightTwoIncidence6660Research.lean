import ProximityPrize.Benchmark.TargetLower
import Mathlib.Combinatorics.Enumerative.DoubleCounting

 


















namespace ProximityPrize.SubmissionLower
namespace ContactFullKernelHeightTwoIncidence6660Research

set_option autoImplicit false

section Generic

variable {Seed Node Component : Type*}
variable [DecidableEq Node]

 

theorem card_mul_gap_le_of_component_identities
    (seeds : Finset Seed) (nodes : Finset Node)
    (assigned : Seed → Component)
    (identities : Component → Finset Node)
    (agreement : Seed → Node → Prop)
    [∀ seed node, Decidable (agreement seed node)]
    (a w cutCap : ℕ)
    (hidentitySmall : ∀ seed ∈ seeds,
      (identities (assigned seed)).card < w)
    (hagreement : ∀ seed ∈ seeds,
      a ≤ (nodes.filter (agreement seed)).card)
    (hfiber : ∀ node ∈ nodes,
      (seeds.filter (fun seed ↦
        agreement seed node ∧ node ∉ identities (assigned seed))).card ≤ cutCap) :
    seeds.card * (a - (w - 1)) ≤ nodes.card * cutCap := by
  classical
  let proper : Seed → Node → Prop := fun seed node ↦
    agreement seed node ∧ node ∉ identities (assigned seed)
  have hlower : ∀ seed ∈ seeds,
      a - (w - 1) ≤ (nodes.filter (proper seed)).card := by
    intro seed hseed
    let I := identities (assigned seed)
    have hIcard : I.card ≤ w - 1 := by
      have hlt : I.card < w := by
        simpa only [I] using hidentitySmall seed hseed
      omega
    have hsub : (nodes.filter (agreement seed)) \ I ⊆
        nodes.filter (proper seed) := by
      intro node hnode
      obtain ⟨hfiltered, hnot⟩ := Finset.mem_sdiff.mp hnode
      obtain ⟨hnodes, hagree⟩ := Finset.mem_filter.mp hfiltered
      exact Finset.mem_filter.mpr ⟨hnodes, hagree, hnot⟩
    calc
      a - (w - 1) ≤ a - I.card :=
        Nat.sub_le_sub_left hIcard a
      _ ≤ (nodes.filter (agreement seed)).card - I.card :=
        Nat.sub_le_sub_right (hagreement seed hseed) I.card
      _ ≤ ((nodes.filter (agreement seed)) \ I).card :=
        Finset.le_card_sdiff I (nodes.filter (agreement seed))
      _ ≤ (nodes.filter (proper seed)).card := Finset.card_le_card hsub
  have hcount := Finset.card_mul_le_card_mul proper hlower hfiber
  simpa [proper] using hcount

end Generic

def n : ℕ := 262144
def agreements : ℕ := 182772
def w : ℕ := 131071
def properGap : ℕ := agreements - (w - 1)
def heightTwoAgreementMixed : ℕ := 379381876621
def nonidentitySeedCeiling : ℕ := 1923575155022

def pairComponentCap : ℕ := 514089
def exactIdentitySeedCap : ℕ := 201227
def allIdentityComponentCeiling : ℕ :=
  pairComponentCap * exactIdentitySeedCap
def combinedHeightTwoCeiling : ℕ :=
  nonidentitySeedCeiling + allIdentityComponentCeiling
def fieldBudget : ℕ := 137490364055697543

theorem frozen_height_two_arithmetic :
    properGap = 51702 ∧
      n * heightTwoAgreementMixed = 99452682664935424 ∧
      allIdentityComponentCeiling = 103448587203 ∧
      combinedHeightTwoCeiling = 2027023742225 ∧
      combinedHeightTwoCeiling < fieldBudget := by
  norm_num [properGap, agreements, w, n, heightTwoAgreementMixed,
    allIdentityComponentCeiling, pairComponentCap, exactIdentitySeedCap,
    combinedHeightTwoCeiling, nonidentitySeedCeiling, fieldBudget]

 

theorem nonidentity_card_le_frozen_ceiling
    (seedCard : ℕ)
    (hcount : seedCard * properGap ≤ n * heightTwoAgreementMixed) :
    seedCard ≤ nonidentitySeedCeiling := by
  norm_num [properGap, agreements, w, n, heightTwoAgreementMixed,
    nonidentitySeedCeiling] at hcount ⊢
  omega

end ContactFullKernelHeightTwoIncidence6660Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoIncidence6660Research.card_mul_gap_le_of_component_identities
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoIncidence6660Research.nonidentity_card_le_frozen_ceiling
