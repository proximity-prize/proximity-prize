import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.HelperSource
open Finset Polynomial
open Lower6960.HelperSource (surplus gain WidthGuard cutoffCount compressedPhase gain_eq_compressed surplus_positive width_at_height crt_avoiding_row crt_supply nonzero_of_supply)
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)

def helperBank : Bank := ⟨⟨415,579,126,7914⟩,2180245356544,3136491116⟩

theorem helper_bank_checked : P3_7_1.BankOK helperBank := by
  have moment : P1_7_1_3.momentEstimate 579 126 = 3136491116 := by
    refine P1_7_1_3_2.moment_from_blocks
      [(128,173065948),(128,793552896),(128,1064052736),(128,808741656),(128,283624301),(65,13453579)] ?_ rfl rfl
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
  exact P3_7_1.checked helperBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment

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
  | .seedBoundary => 86
  | .mixedBoundary => 81
  | _ => 1

private def compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  (compressedPhase helperBank.shape 179798 h 14 test.slope test.excess test.seed 0 -
    compressedPhase helperBank.shape 179798 h 14 test.slope test.excess test.seed 1 : ℕ) - (debit h helperBank : ℤ)

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) :
    compressedSurplus h test = surplus helperBank 179798 h 14 test.slope test.excess test.seed := by
  unfold compressedSurplus surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ (by cases test <;> decide)]

private theorem twoSlopes_first :
    compressedSurplus 2368 .twoSlopes = 988306437104 := by rfl
private theorem twoSlopes_next :
    compressedSurplus 2369 .twoSlopes = 426182241706905 := by rfl
private theorem seedBoundary_first :
    compressedSurplus 2368 .seedBoundary = 54934766503849726 := by rfl
private theorem seedBoundary_next :
    compressedSurplus 2369 .seedBoundary = 55383623557319224 := by rfl
private theorem mixedBoundary_first :
    compressedSurplus 2368 .mixedBoundary = 53770951937294588 := by rfl
private theorem mixedBoundary_next :
    compressedSurplus 2369 .mixedBoundary = 54221704000941204 := by rfl
private theorem jetBoundary_first :
    compressedSurplus 2368 .jetBoundary = 20735462186639996 := by rfl
private theorem jetBoundary_next :
    compressedSurplus 2369 .jetBoundary = 21172263452250018 := by rfl

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2368≤h) (hi : h≤2401) :
    debit h helperBank < gain helperBank.shape 179798 h 14 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2368 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus helperBank 179798 2368 14 test.slope test.excess test.seed ≤
      surplus helperBank 179798 2369 14 test.slope test.excess test.seed
    rw [← compressedSurplus_eq, ← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide

theorem helper_width {h : ℕ} (lo : 2368≤h) (hi : h≤2401) :
    WidthGuard helperBank 179798 h 14 :=
  width_at_height _ _ 2368 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)

def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179798 h 14-1

theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q :=
  crt_avoiding_row Crt word helperBank 179798 14 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (by decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess

theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179798 14 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)

private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega

/-- Every unavoidable prime in the concrete helper has slope degree one and
lies in the degree rectangles used by the four rescue branches. -/
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤85 ∧ (2≤jetDegree G → seedDegree G≤80) := by
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
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 86≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 81≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)

/-- A pair of distinct unavoidable moving primes would violate the same
concrete two-slope receipt. -/
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179798 14 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact Lower6960.HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179798 h 14)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH

#print axioms helper_bank_checked
#print axioms helper_surplus
#print axioms helper_avoids
#print axioms helper_nonzero
#print axioms helper_common_caps
#print axioms helper_not_two

end Lower6961.Lo.HelperSource
