import ProximityPrize.Benchmark.TargetLower

/-!
# Exact medium-edge counterprofile at score 64.01

Two MCA-bad high-family challenges whose chosen agreement sets meet in the
Reed--Solomon dimension need not reconstruct a pair close to the two received
rows.  This file gives the exact `n = 262144`, `A = 185354`, `k = 131072`
counterprofile.  It also records why uniqueness of each chosen challenge
neighbour does not repair the implication.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSMediumEdgeExactCounterprofile6401

open Finset Polynomial

def profileN : ℕ := 262144
def profileA : ℕ := 185354
def profileK : ℕ := 131072
def profileUnion : ℕ := 239636

def domain : Finset ℕ := range profileN
def commonCore : Finset ℕ := range profileK
def leftAgreement : Finset ℕ := range profileA
def rightOnly : Finset ℕ := Ico profileA profileUnion
def rightAgreement : Finset ℕ := commonCore ∪ rightOnly

/-- Received rows.  On the four consecutive blocks `I,X,Y,R` they are
`(0,0), (-1,1), (0,1), (1,0)`. -/
def received : Fin 2 → ℕ → ℚ
  | 0, i =>
      if i < profileK then 0
      else if i < profileA then -1
      else if i < profileUnion then 0
      else 1
  | 1, i =>
      if i < profileK then 0
      else if i < profileUnion then 1
      else 0

def leftParameter : ℚ := 1
def rightParameter : ℚ := 0
def zeroNeighbour : ℕ → ℚ := fun _ ↦ 0

/-- Degree-`< k` Reed--Solomon trace on a chosen coordinate set. -/
def HasLowDegreeTrace (f : ℕ → ℚ) (S : Finset ℕ) : Prop :=
  ∃ P : ℚ[X], P.natDegree < profileK ∧
    ∀ i ∈ S, P.eval (i : ℚ) = f i

/-- A degree-`< k` polynomial vanishing on the `k`-point common core is zero. -/
theorem polynomial_eq_zero_of_vanishes_on_commonCore
    (P : ℚ[X]) (hdeg : P.natDegree < profileK)
    (hzero : ∀ i ∈ commonCore, P.eval (i : ℚ) = 0) :
    P = 0 := by
  let nodes : Finset ℚ := commonCore.image fun i : ℕ ↦ (i : ℚ)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P 0 nodes
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    simpa using hzero i hi
  · have hinj : Function.Injective (fun i : ℕ ↦ (i : ℚ)) := by
      exact_mod_cast Nat.cast_injective
    rw [card_image_of_injective _ hinj]
    simpa [nodes, commonCore, profileK] using hdeg

theorem exact_set_arithmetic :
    domain.card = 262144 ∧
      commonCore.card = 131072 ∧
      leftAgreement.card = 185354 ∧
      rightAgreement.card = 185354 ∧
      (leftAgreement ∩ rightAgreement).card = 131072 ∧
      (leftAgreement ∪ rightAgreement).card = 239636 ∧
      domain.card - (leftAgreement ∪ rightAgreement).card = 22508 := by
  native_decide

theorem received_sum_zero_iff_left (i : ℕ) :
    received 0 i + received 1 i = 0 ↔ i ∈ leftAgreement := by
  simp only [leftAgreement, mem_range, profileA]
  by_cases hk : i < 131072 <;>
    by_cases hA : i < 185354 <;>
      by_cases hu : i < 239636 <;>
        simp [received, profileK, profileA, profileUnion, hk, hA, hu] <;> omega

theorem received_zero_zero_iff_common (i : ℕ) :
    received 0 i = 0 ∧ received 1 i = 0 ↔ i ∈ commonCore := by
  simp only [commonCore, mem_range, profileK]
  by_cases hk : i < 131072 <;>
    by_cases hA : i < 185354 <;>
      by_cases hu : i < 239636 <;>
        simp [received, profileK, profileA, profileUnion, hk, hA, hu] <;> omega

theorem received_zero_iff_right (i : ℕ) :
    received 0 i = 0 ↔ i ∈ rightAgreement := by
  simp only [rightAgreement, mem_union, commonCore, mem_range, rightOnly,
    mem_Ico, profileK, profileA, profileUnion]
  by_cases hk : i < 131072 <;>
    by_cases hA : i < 185354 <;>
      by_cases hu : i < 239636 <;>
        simp [received, profileK, profileA, profileUnion, hk, hA, hu] <;> omega

theorem left_combination_is_zero {i : ℕ} (hi : i ∈ leftAgreement) :
    received 0 i + leftParameter * received 1 i = zeroNeighbour i := by
  have hzero := (received_sum_zero_iff_left i).2 hi
  simpa [leftParameter, zeroNeighbour] using hzero

theorem right_combination_is_zero {i : ℕ} (hi : i ∈ rightAgreement) :
    received 0 i + rightParameter * received 1 i = zeroNeighbour i := by
  have hzero := (received_zero_iff_right i).2 hi
  simpa [rightParameter, zeroNeighbour] using hzero

theorem received_one_not_lowDegree_on_left :
    ¬ HasLowDegreeTrace (received 1) leftAgreement := by
  rintro ⟨P, hdeg, heval⟩
  have hzero : ∀ i ∈ commonCore, P.eval (i : ℚ) = 0 := by
    intro i hi
    have hiK : i < 131072 := by simpa [commonCore, profileK] using hi
    have hiA : i ∈ leftAgreement := by
      simp only [leftAgreement, mem_range, profileA]
      omega
    simpa [received, profileK, profileUnion, hiK] using heval i hiA
  have hP : P = 0 := polynomial_eq_zero_of_vanishes_on_commonCore P hdeg hzero
  have hKA : profileK ∈ leftAgreement := by
    simp [leftAgreement, profileK, profileA]
  have hone := heval profileK hKA
  simp [hP, received, profileK, profileUnion] at hone

theorem received_one_not_lowDegree_on_right :
    ¬ HasLowDegreeTrace (received 1) rightAgreement := by
  rintro ⟨P, hdeg, heval⟩
  have hzero : ∀ i ∈ commonCore, P.eval (i : ℚ) = 0 := by
    intro i hi
    have hiR : i ∈ rightAgreement := subset_union_left hi
    have hiK : i < 131072 := by simpa [commonCore, profileK] using hi
    simpa [received, profileK, profileUnion, hiK] using heval i hiR
  have hP : P = 0 := polynomial_eq_zero_of_vanishes_on_commonCore P hdeg hzero
  have hA : profileA ∈ rightAgreement := by
    simp [rightAgreement, rightOnly, profileA, profileUnion]
  have hone := heval profileA hA
  simp [hP, received, profileK, profileA, profileUnion] at hone

/-- Both challenges are MCA-bad on their chosen sets: their affine
combination is the zero codeword, while received row one has no degree-`< k`
trace on the same set. -/
theorem both_challenges_are_MCA_bad_on_chosen_sets :
    (∀ i ∈ leftAgreement,
        received 0 i + leftParameter * received 1 i = zeroNeighbour i) ∧
      ¬ HasLowDegreeTrace (received 1) leftAgreement ∧
      (∀ i ∈ rightAgreement,
        received 0 i + rightParameter * received 1 i = zeroNeighbour i) ∧
      ¬ HasLowDegreeTrace (received 1) rightAgreement :=
  ⟨fun _ hi ↦ left_combination_is_zero hi,
    received_one_not_lowDegree_on_left,
    fun _ hi ↦ right_combination_is_zero hi,
    received_one_not_lowDegree_on_right⟩

/-- The zero neighbour is the unique degree-`< k` polynomial on either
chosen set. -/
theorem chosen_zero_neighbour_unique
    (S : Finset ℕ) (hcore : commonCore ⊆ S)
    (P : ℚ[X]) (hdeg : P.natDegree < profileK)
    (heval : ∀ i ∈ S, P.eval (i : ℚ) = zeroNeighbour i) :
    P = 0 := by
  apply polynomial_eq_zero_of_vanishes_on_commonCore P hdeg
  intro i hi
  simpa [zeroNeighbour] using heval i (hcore hi)

def reconstructedRow1 (c_z c_w : ℕ → ℚ) (z w : ℚ) : ℕ → ℚ :=
  fun i ↦ (c_z i - c_w i) / (z - w)

def reconstructedRow0 (c_z c_w : ℕ → ℚ) (z w : ℚ) : ℕ → ℚ :=
  fun i ↦ c_z i - z * reconstructedRow1 c_z c_w z w i

theorem reconstructed_pair_is_zero :
    reconstructedRow0 zeroNeighbour zeroNeighbour leftParameter rightParameter = 0 ∧
      reconstructedRow1 zeroNeighbour zeroNeighbour leftParameter rightParameter = 0 := by
  constructor <;> funext i <;>
    simp [reconstructedRow0, reconstructedRow1, zeroNeighbour, leftParameter,
      rightParameter]

def pairAgreementWithZero : Finset ℕ :=
  domain.filter fun i ↦ received 0 i = 0 ∧ received 1 i = 0

theorem pairAgreementWithZero_eq_commonCore :
    pairAgreementWithZero = commonCore := by
  ext i
  simp only [pairAgreementWithZero, mem_filter]
  rw [received_zero_zero_iff_common]
  constructor
  · exact fun h ↦ h.2
  · intro hi
    refine ⟨?_, hi⟩
    have hiK : i < 131072 := by simpa [commonCore, profileK] using hi
    simpa [domain, profileN] using hiK.trans (by omega : 131072 < 262144)

/-- The reconstructed pair agrees with the received pair on exactly `k`, not
on `A`, coordinates. -/
theorem reconstructed_pair_is_not_close :
    pairAgreementWithZero.card = 131072 ∧
      pairAgreementWithZero.card < 185354 := by
  rw [pairAgreementWithZero_eq_commonCore]
  native_decide

/-- Code-pair polynomial evaluations on the finite benchmark domain. -/
def polynomialPairAgreement (P0 P1 : ℚ[X]) : Finset ℕ :=
  domain.filter fun i ↦
    P0.eval (i : ℚ) = received 0 i ∧
      P1.eval (i : ℚ) = received 1 i

/-- A pair aligned with the left zero neighbour can pair-agree only inside
the left chosen set. -/
theorem left_aligned_agreement_subset
    (P0 P1 : ℚ[X]) (halign : P0 + P1 = 0) :
    polynomialPairAgreement P0 P1 ⊆ leftAgreement := by
  intro i hi
  have hi' := mem_filter.mp hi
  have hsumEval : received 0 i + received 1 i = 0 := by
    have h := congrArg (fun Q : ℚ[X] ↦ Q.eval (i : ℚ)) halign
    simpa [hi'.2.1, hi'.2.2] using h
  exact (received_sum_zero_iff_left i).1 hsumEval

/-- A pair aligned with the right zero neighbour can pair-agree only inside
the right chosen set. -/
theorem right_aligned_agreement_subset
    (P0 P1 : ℚ[X]) (halign : P0 = 0) :
    polynomialPairAgreement P0 P1 ⊆ rightAgreement := by
  intro i hi
  have hi' := mem_filter.mp hi
  have hzero0 : received 0 i = 0 := by simpa [halign] using hi'.2.1.symm
  exact (received_zero_iff_right i).1 hzero0

theorem trace_of_full_polynomialPairAgreement
    (P0 P1 : ℚ[X]) (S : Finset ℕ)
    (hsub : polynomialPairAgreement P0 P1 ⊆ S)
    (hcard : S.card ≤ (polynomialPairAgreement P0 P1).card)
    (hdeg1 : P1.natDegree < profileK) :
    HasLowDegreeTrace (received 1) S := by
  have heq : polynomialPairAgreement P0 P1 = S :=
    Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨P1, hdeg1, ?_⟩
  intro i hi
  have hiA : i ∈ polynomialPairAgreement P0 P1 := by simpa [heq] using hi
  exact (mem_filter.mp hiA).2.2

/-- Exact high-family statement for the left challenge: no degree-`< k`
code pair aligned with its selected zero neighbour is close to the received
pair on `A` coordinates. -/
theorem left_challenge_not_explained_by_close_pair
    (P0 P1 : ℚ[X])
    (hdeg0 : P0.natDegree < profileK) (hdeg1 : P1.natDegree < profileK)
    (halign : P0 + P1 = 0) :
    (polynomialPairAgreement P0 P1).card < profileA := by
  by_contra h
  have hclose : profileA ≤ (polynomialPairAgreement P0 P1).card :=
    Nat.le_of_not_gt h
  have htrace := trace_of_full_polynomialPairAgreement P0 P1 leftAgreement
    (left_aligned_agreement_subset P0 P1 halign) (by
      simpa [leftAgreement, profileA] using hclose) hdeg1
  exact received_one_not_lowDegree_on_left htrace

/-- Exact high-family statement for the right challenge. -/
theorem right_challenge_not_explained_by_close_pair
    (P0 P1 : ℚ[X])
    (hdeg0 : P0.natDegree < profileK) (hdeg1 : P1.natDegree < profileK)
    (halign : P0 = 0) :
    (polynomialPairAgreement P0 P1).card < profileA := by
  by_contra h
  have hclose : profileA ≤ (polynomialPairAgreement P0 P1).card :=
    Nat.le_of_not_gt h
  have htrace := trace_of_full_polynomialPairAgreement P0 P1 rightAgreement
    (right_aligned_agreement_subset P0 P1 halign) (by
      have hc := exact_set_arithmetic.2.2.2.1
      rw [hc]
      exact hclose) hdeg1
  exact received_one_not_lowDegree_on_right htrace

/-- Final exact refutation of the missing medium-edge implication. -/
theorem medium_edge_does_not_force_close_pair :
    leftAgreement.card = 185354 ∧
      rightAgreement.card = 185354 ∧
      (leftAgreement ∩ rightAgreement).card = 131072 ∧
      (∀ i ∈ leftAgreement,
        received 0 i + leftParameter * received 1 i = zeroNeighbour i) ∧
      (∀ i ∈ rightAgreement,
        received 0 i + rightParameter * received 1 i = zeroNeighbour i) ∧
      ¬ HasLowDegreeTrace (received 1) leftAgreement ∧
      ¬ HasLowDegreeTrace (received 1) rightAgreement ∧
      pairAgreementWithZero.card = 131072 ∧
      pairAgreementWithZero.card < 185354 := by
  refine ⟨exact_set_arithmetic.2.2.1, exact_set_arithmetic.2.2.2.1,
    exact_set_arithmetic.2.2.2.2.1, fun _ hi ↦ left_combination_is_zero hi,
    fun _ hi ↦ right_combination_is_zero hi,
    received_one_not_lowDegree_on_left, received_one_not_lowDegree_on_right,
    reconstructed_pair_is_not_close.1, reconstructed_pair_is_not_close.2⟩

end BCHKSMediumEdgeExactCounterprofile6401
end ProximityPrize.SubmissionLower
