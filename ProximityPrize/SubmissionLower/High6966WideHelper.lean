import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960HelperPrefix
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.Wide6966Helper
open HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
def bankAt (u:ℕ) : Bank := ⟨⟨294,408,89,u⟩,777085255680,779461982⟩
abbrev helperBank := bankAt 20142
theorem checked (u:ℕ) : P3_7_1.BankOK (bankAt u) := by
  have moment : P1_7_1_3.momentEstimate 408 89 = 779461982 := by
    refine P1_7_1_3_2.moment_from_blocks
      [(128,109021770),(128,353396160),(128,272672821),(113,44371231)] ?_ rfl rfl
    exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
  exact P3_7_1.checked (bankAt u) (m:=294) (B:=408) (J:=89) (N:=777085255680) (M:=779461982) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment
theorem helper_bank_checked : P3_7_1.BankOK helperBank := checked 20142
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
  | .seedBoundary => 97
  | .mixedBoundary => 93
  | _ => 1
def HelperTest.cap : HelperTest → ℕ
  | .twoSlopes => 20142
  | .seedBoundary => 4009
  | .mixedBoundary => 4426
  | .jetBoundary => 11884
private def compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  (compressedPhase (bankAt test.cap).shape 179769 h 10 test.slope test.excess test.seed 0 -
    compressedPhase (bankAt test.cap).shape 179769 h 10 test.slope test.excess test.seed 1 : ℕ) - (debit h (bankAt test.cap) : ℤ)
private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) :
    compressedSurplus h test = surplus (bankAt test.cap) 179769 h 10 test.slope test.excess test.seed := by
  unfold compressedSurplus surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ (by cases test <;> decide)]
private theorem twoSlopes_first :
    compressedSurplus 2330 .twoSlopes = 3075459454900 := by rfl
private theorem twoSlopes_next :
    compressedSurplus 2331 .twoSlopes = 1058102237527326 := by rfl
private theorem seedBoundary_first :
    compressedSurplus 2330 .seedBoundary = 12409045631770 := by rfl
private theorem seedBoundary_next :
    compressedSurplus 2331 .seedBoundary = 54234956880594 := by rfl
private theorem mixedBoundary_first :
    compressedSurplus 2330 .mixedBoundary = 11697082435820 := by rfl
private theorem mixedBoundary_next :
    compressedSurplus 2331 .mixedBoundary = 62671583261052 := by rfl
private theorem jetBoundary_first :
    compressedSurplus 2330 .jetBoundary = 129085484029010 := by rfl
private theorem jetBoundary_next :
    compressedSurplus 2331 .jetBoundary = 496446854448762 := by rfl
theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2330≤h) (hi : h≤33677) :
    debit h (bankAt test.cap) < gain (bankAt test.cap).shape 179769 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2330 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus (bankAt test.cap) 179769 2330 10 test.slope test.excess test.seed ≤
      surplus (bankAt test.cap) 179769 2331 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq, ← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2330≤h) (hi : h≤33677) :
    WidthGuard helperBank 179769 h 10 :=
  width_at_height _ _ 2330 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179769 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2330≤h) (hi : h≤33677) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q := by
  obtain ⟨Q,inside,avoids⟩ := crt_avoiding_row Crt word (bankAt test.cap) 179769 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    (checked test.cap).nodes (checked test.cap).moment.1 (checked test.cap).moment.2
    (by cases test <;> decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
  exact ⟨Q, K1_14_1.evaluated_mono Crt word (s:=(bankAt test.cap).shape) (s':=helperBank.shape)
    rfl rfl rfl (by cases test <;> decide) le_rfl inside, avoids⟩
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2330≤h) (hi : h≤33677) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179769 10 2 0 1 (by omega) (by omega) (by decide)
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
    (lo : 2330≤h) (hi : h≤33677) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤96 ∧ (2≤jetDegree G → seedDegree G≤92) := by
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
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 97≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 93≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2330≤h) (hi : h≤33677) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179769 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179769 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.Wide6966Helper
