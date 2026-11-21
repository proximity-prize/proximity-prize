import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.HighJoint6921
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace HighMassBridge6921
noncomputable section
open K21 H21 Polynomial
open scoped BigOperators
open HighJoint6921 (HeightBand)

def choose (w : ℤ) : HeightBand :=
  if w ≤ 3554 then .first else if w ≤ 8249 then .second else if w ≤ 23999 then .third else .fourth

theorem bounds {w : ℤ} (lo : 2472 ≤ w) (hi : w ≤ 32950) :
    (choose w).lower ≤ w.toNat ∧ w.toNat ≤ (choose w).upper := by
  unfold choose
  split_ifs <;> simp only [HeightBand.lower, HeightBand.upper] <;> omega

theorem seed_eq (w : ℤ) : (choose w).seedBank = terminalShape w := by
  unfold choose terminalShape band
  split_ifs <;> rfl

theorem cap_eq (w : ℤ) : (choose w).ordinateCap = (band w).yBound := by
  unfold choose band
  split_ifs <;> rfl

theorem full_mem (w : ℤ) : (choose w).fullBank ∈ scheduled w := by
  unfold choose scheduled
  split_ifs <;> simp [HeightBand.fullBank, HighJoint6921.bridgeShape, HighJoint6921.laterShape]

theorem seed_mem (w : ℤ) : (choose w).seedBank ∈ scheduled w := by
  rw [seed_eq]
  unfold scheduled
  split_ifs <;> simp

private theorem width_full {w : ℤ} (lo : 2472 ≤ w) :
    (choose w).fullBank.B * (131071 - w.toNat) ≤ (choose w).fullBank.m * 180130 := by
  unfold choose
  split_ifs <;> simp [HeightBand.fullBank, HighJoint6921.bridgeShape, HighJoint6921.laterShape] <;> omega

private theorem width_seed {w : ℤ} (lo : 2472 ≤ w) :
    (choose w).seedBank.B * (131071 - w.toNat) ≤ (choose w).seedBank.m * 180130 := by
  unfold choose
  split_ifs <;> simp [HeightBand.seedBank, HighJoint6921.bridgeShape, HighJoint6921.laterShape] <;> omega

theorem mass {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ} {rows : Banks}
    (hr : JetSource M F rows) (s : K1_14.Shape) (hs : s ∈ scheduled M.overhead)
    (hm : 0 < s.m) (hwidth : s.B * (131071 - M.overhead.toNat) ≤ s.m * 180130)
    (f : Equation) (hd : ∀ W < HighJoint6921.top s, ∀ P ∈ rows s W, P ≠ 0 →
      f ^ HighJoint6921.forcedPower s M.overhead.toNat W P.natDegree ∣ P.leadingCoeff) :
    HighJoint6921.TerminalMass s M.overhead.toNat f := by
  have ht : 0 < s.m * 180130 := by omega
  have last : s.m*180130-1+1 = s.m*180130 := by omega
  refine ⟨rows s, ?_, ?_⟩
  · have hh := hr.floor_bound s hs (s.m*180130-1) (by omega) (by
      intro q hq j _
      rw [last]
      exact ((Nat.mul_le_mul_right _ hq).trans hwidth).trans (Nat.le_add_right _ _))
    rw [last] at hh
    exact hh
  · intro W hW P hP hn
    have hc : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hb,hj,_⟩ := hr.shape s hs W P hP _ _ hc
    refine ⟨hj,hb,hr.leading s hs W P hP hn,?_,hd W hW P hP hn⟩
    intro i
    rw [← coeff_natDegree (p := P)]
    by_cases h : (P.coeff P.natDegree).coeff i = 0
    · rw [h]
      simp
    · exact (hr.shape s hs W P hP _ _ h).2.2

theorem ordinate {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ} {rows : Banks}
    (hr : JetSource M F rows) (lo : 2472 ≤ M.overhead) (hi : M.overhead ≤ 32950)
    (f : Equation) (hf : f ≠ 0)
    (hd : ∀ W < HighJoint6921.top (choose M.overhead).fullBank,
      ∀ P ∈ rows (choose M.overhead).fullBank W, P ≠ 0 →
      f ^ HighJoint6921.forcedPower (choose M.overhead).fullBank M.overhead.toNat W P.natDegree ∣ P.leadingCoeff) :
    f.natDegree ≤ (band M.overhead).yBound := by
  rw [← cap_eq]
  obtain ⟨hl,hu⟩ := bounds lo hi
  apply HighJoint6921.ordinate_bound (choose M.overhead) hl hu hf
  apply mass hr _ (full_mem _) _ (width_full lo) _ hd
  cases choose M.overhead <;> decide

theorem seed {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ} {rows : Banks}
    (hr : JetSource M F rows) (lo : 2472 ≤ M.overhead) (hi : M.overhead ≤ 32950)
    (f : Equation) (hf : ReducedEquation M.overhead f)
    (hd : TerminalDivisibility M.overhead rows f) :
    SeedBound f ((choose M.overhead).seedCap f.natDegree) := by
  obtain ⟨hl,hu⟩ := bounds lo hi
  have hn : f ≠ 0 := fun h => by simpa [h] using hf.1
  apply HighJoint6921.seed_bound (choose M.overhead) hl hu hn hf.1 ((cap_eq _).symm ▸ hf.2.1)
  have hm : 0 < (choose M.overhead).seedBank.m := by cases choose M.overhead <;> decide
  refine mass hr _ (seed_mem _) hm (width_seed lo) f ?_
  rw [seed_eq]
  exact hd
end
end HighMassBridge6921
