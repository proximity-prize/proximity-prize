import ProximityPrize.SubmissionLower.JointTerminal6921

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighJoint6921

open K1_14 K1_14_4 Polynomial
open scoped BigOperators

def top (s : Shape) : ℕ := s.m * 180169

def base (h : ℕ) : ℕ := 131071 - h

def rawWidth (s : Shape) (h q j : ℕ) : ℕ := top s + j - q * base h

def rawVolume (s : Shape) (h : ℕ) : ℕ :=
  triangle s.U * shapeSum s (rawWidth s h)

def forcedPower (s : Shape) (h W j : ℕ) : ℕ :=
  1 + (top s - 1 - W) / (2 * h) - j

def width (s : Shape) (h W j : ℕ) : ℕ :=
  min (s.B + 1) ((W + j) / base h + 1) - j

/-- Source rank after physical and pole constraints, together with divisibility
of each leading derivative coefficient in the same terminal bank. -/
def TerminalMass (s : Shape) (h : ℕ) (f : Equation) : Prop :=
  ∃ V : ℕ → Submodule FX Jet,
    rawVolume s h ≤ sourceDebit h s +
      ∑ W ∈ Finset.range (top s), Module.finrank FX (V W) ∧
    ∀ W < top s, ∀ P ∈ V W, P ≠ 0 →
      let j := P.natDegree
      let i := P.leadingCoeff.natDegree
      j ≤ s.J ∧ i + j ≤ s.B ∧ (i + j) * base h ≤ W + j ∧
        SeedBound P.leadingCoeff s.U ∧ f ^ forcedPower s h W j ∣ P.leadingCoeff

def quotientVolume (s : Shape) (h e step : ℕ) : ℕ :=
  ∑ W ∈ Finset.range (top s), ∑ j ∈ Finset.range (s.J + 1),
    (width s h W j - forcedPower s h W j * e) *
      slots s.U (forcedPower s h W j * step)

private theorem row_cutoff {s : Shape} {h W : ℕ} {P : Jet} {f : Equation}
    (hk : 0 < base h)
    (hp : P.natDegree ≤ s.J ∧ P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧
      (P.leadingCoeff.natDegree + P.natDegree) * base h ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff s.U ∧ f ^ forcedPower s h W P.natDegree ∣ P.leadingCoeff) :
    P.natDegree < s.J + 1 ∧ P.leadingCoeff.natDegree < width s h W P.natDegree ∧
      SeedBound P.leadingCoeff s.U ∧ f ^ forcedPower s h W P.natDegree ∣ P.leadingCoeff := by
  obtain ⟨hj, hb, hw, hu, hd⟩ := hp
  have hquot := (Nat.le_div_iff_mul_le hk).mpr hw
  refine ⟨by omega, ?_, hu, hd⟩
  unfold width
  omega

/-- A joint degree exclusion from a numerical quotient-volume inequality. -/
theorem seed_of_strict {s : Shape} {h e v : ℕ} {f : Equation}
    (hf : f ≠ 0) (hk : 0 < base h) (he : e ≤ f.natDegree) (hm : TerminalMass s h f)
    (hstrict : sourceDebit h s + quotientVolume s h e (v+1) < rawVolume s h) :
    SeedBound f v := by
  obtain ⟨V, hmass, hrows⟩ := hm
  exact JointTerminal.seed_bound_of_bank V hf (top s) (s.J + 1) s.U e v
    (sourceDebit h s) (rawVolume s h) (width s h) (forcedPower s h) he hmass
    (fun W hW P hP hn => row_cutoff hk (hrows W hW P hP hn)) hstrict

/-- A zero seed charge tests ordinate degree alone in the full bank. -/
theorem ordinate_of_strict {s : Shape} {h e : ℕ} {f : Equation}
    (hf : f ≠ 0) (hk : 0 < base h) (hm : TerminalMass s h f)
    (hstrict : sourceDebit h s + quotientVolume s h e 0 < rawVolume s h) :
    f.natDegree < e := by
  by_contra! he
  obtain ⟨V, hmass, hrows⟩ := hm
  have htotal := Finset.sum_le_sum (s := Finset.range (top s)) fun W hW =>
    Module.finrank_le_of_rank_le
      (JointTerminal.cutoff_capacity (V W) hf s.U (s.J+1) e 0 (width s h W) (forcedPower s h W)
        he (Nat.zero_le _) (fun P hP hn => row_cutoff hk (hrows W (Finset.mem_range.mp hW) P hP hn)))
  change _ ≤ quotientVolume s h e 0 at htotal
  omega

end HighJoint6921
