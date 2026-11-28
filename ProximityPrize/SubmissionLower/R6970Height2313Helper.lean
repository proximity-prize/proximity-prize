import ProximityPrize.SubmissionLower.R6970Height2313Free

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0597
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.Prefix6969Helper
open Research6969.TransitionArithmetic (value value_eq)
open Research6966.FarSourceArithmetic (Request)
open _root_.Research6969.TransitionBanks (bank154 rank154)
open HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
abbrev bankAt (u : ℕ) : Bank := bank154 u
abbrev helperBank := bankAt 10281

theorem checked (u : ℕ) : P3_7_1.BankOK (bankAt u) := rank154 u

theorem helper_bank_checked : P3_7_1.BankOK helperBank := checked 10281

inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary
def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1
def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0
def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 57
  | .mixedBoundary => 57
  | _ => 1
abbrev HelperTest.cap : HelperTest → ℕ
  | .twoSlopes | .jetBoundary => 10281
  | .seedBoundary => 6300
  | .mixedBoundary => 8000

private def helperRequest (test : HelperTest) : Request :=
  ⟨bankAt test.cap, 10, test.slope, test.excess, test.seed⟩

private abbrev compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  value (helperRequest test) h

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) (hi : h ≤ 2313) :
    compressedSurplus h test = surplus (bankAt test.cap) 179730 h 10 test.slope test.excess test.seed :=
  value_eq (helperRequest test) h (by cases test <;> decide)
    (by change 170 < 131071 - h; omega)

private theorem twoSlopes_first : compressedSurplus 2305 .twoSlopes = 20382885092284 := by decide +kernel
private theorem twoSlopes_next : compressedSurplus 2306 .twoSlopes = 1844255147446283 := by decide +kernel
private theorem seedBoundary_first : compressedSurplus 2305 .seedBoundary = 15708932619573 := by decide +kernel
private theorem seedBoundary_next : compressedSurplus 2306 .seedBoundary = 700700872716082 := by decide +kernel
private theorem mixedBoundary_first : compressedSurplus 2305 .mixedBoundary = 22147520915115708 := by decide +kernel
private theorem mixedBoundary_next : compressedSurplus 2306 .mixedBoundary = 23261558112651117 := by decide +kernel
private theorem jetBoundary_first : compressedSurplus 2305 .jetBoundary = 93734560775287234 := by decide +kernel
private theorem jetBoundary_next : compressedSurplus 2306 .jetBoundary = 95599089947788823 := by decide +kernel

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2305≤h) (hi : h≤33755) :
    debit h (bankAt test.cap) < gain (bankAt test.cap).shape 179730 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2305 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq _ _ (by decide)]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus (bankAt test.cap) 179730 2305 10 test.slope test.excess test.seed ≤
      surplus (bankAt test.cap) 179730 2306 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq 2305 test (by decide), ← compressedSurplus_eq 2306 test (by decide)]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2305≤h) (hi : h≤33755) :
    WidthGuard helperBank 179730 h 10 :=
  width_at_height _ _ 2305 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179730 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2305≤h) (hi : h≤33755) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q := by
  obtain ⟨Q,inside,avoids⟩ := crt_avoiding_row Crt word (bankAt test.cap) 179730 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    (checked test.cap).nodes (checked test.cap).moment.1 (checked test.cap).moment.2
    (by cases test <;> decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
  exact ⟨Q, K1_14_1.evaluated_mono Crt word (s:=(bankAt test.cap).shape) (s':=helperBank.shape)
    rfl rfl rfl (by cases test <;> decide) le_rfl inside, avoids⟩
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2305≤h) (hi : h≤33755) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179730 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2305≤h) (hi : h≤33755) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤56 ∧ (2≤jetDegree G → seedDegree G≤56) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 57≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 57≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2305≤h) (hi : h≤33755) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179730 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179730 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.Prefix6969Helper
end Z6969Source0597


end Research6970.Height2313
