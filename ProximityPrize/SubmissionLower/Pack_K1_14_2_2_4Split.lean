import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Fast032
set_option Elab.async false

section PackSource_K1_14_2_2_4Split
set_option autoImplicit true
set_option maxHeartbeats 1000000

namespace K1_14_2_2_4

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped Classical BigOperators

/-- Strip the fixed parts and divide by the full common ordinary gcd.
The degrees spent by the gcd are subtracted from both residual rows. -/
def c1 : Prop :=
  ∀ w rows (i : Fin 10) (B : RowPair w rows i) (A : FixedPair B),
    Nonempty (SharedGcd A)

/-- Pay for the parents on high-multiplicity ordinary factors by their
compatibility graphs, counted with the degrees of the distinct factors. -/
def c2 : Prop :=
  ∀ (H : Equation) (P Q : Jet) (S : Finset (Ideal Ambient)) (r : ℕ),
    H ≠ 0 → seedDegree H < p → H.natDegree < p → 0 < r →
    C H ∣ P → C H ∣ Q →
    (∀ I ∈ S, Active I ∧ compatible P Q I ∧ HighOn H r I) →
    ∀ k, highScale r k * mass S k ≤ highCap (seedDegree H) H.natDegree k

/-- Off the high factors, complete gcd division loses at most r - 1 in
the ambient local ring or in its rank-one jet-image quotient. -/
def c3 : Prop :=
  ∀ (H : Equation) (P : Jet) (I : Ideal Ambient) (m r : ℕ),
    H ≠ 0 → seedDegree H < p → H.natDegree < p →
    Active I → 0 < r → r ≤ m → ¬ HighOn H r I →
    orderOn I (C H * P) m → orderOn I P (m + 1 - r)

/-- The residual intersection has local length at least n squared at
rank two and at least n at rank one. -/
def c4 : Prop :=
  ∀ (P Q : Jet) (I : Ideal Ambient) (hI : Active I) (n : ℕ),
    0 < n → orderOn I P n → orderOn I Q n →
    ((if dual I then n ^ 2 else n : ℕ) : ℕ∞) ≤ localLength P Q I hI.prime

/-- Generic section degrees of the residual pair, with the specified
local length counted at each parent that meets the chosen section. -/
def c5 : Prop :=
  ∀ (P Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient)) (k : Fin 4) (d : ℕ),
    P ≠ 0 → Q ≠ 0 → IsRelPrime (toJet P) (toJet Q) →
    s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t → 0 < d →
    (∀ I ∈ S, ∃ hI : Active I,
      sectionDegree I k ≠ 0 → (d : ℕ∞) ≤ localLength P Q I hI.prime) →
    d * mass S k ≤ pairCap s t k

private theorem cancel_fixed {I : Ideal Ambient} (hp : I.IsPrime) (G : ODE) (P : Jet)
    (m : ℕ) (hG : ¬ fixedOn G I) (ho : orderOn I (fixedIncl G * P) m) :
    orderOn I P m := by
  obtain ⟨a, ha, h⟩ := ho
  refine ⟨a * toJet (fixedIncl G), fun hn => (hp.mem_or_mem hn).elim ha hG, ?_⟩
  simpa only [map_mul, mul_assoc] using h

private theorem cheap_small :
    ∀ i : Fin 10, (stageAt i).cheap.U < p ∧ (stageAt i).cheap.B < p := by
  decide +kernel

private theorem from_paired_bounds {S : Finset (Ideal Ambient)} {k : Fin 4}
    (H : Equation) (r g d high low cap : ℕ)
    (hh : g * mass (S.filter (HighOn H r)) k ≤ high)
    (hl : d * mass (S.filter fun I => ¬ HighOn H r I) k ≤ low)
    (hnum : d * high + g * low < g * d * (cap + 1)) :
    mass S k ≤ cap := by
  have hadd : mass (S.filter (HighOn H r)) k +
      mass (S.filter fun I => ¬ HighOn H r I) k = mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hscaled : g * d * mass S k ≤ d * high + g * low := by
    calc
      g * d * mass S k =
          d * (g * mass (S.filter (HighOn H r)) k) +
            g * (d * mass (S.filter fun I => ¬ HighOn H r I) k) := by
              rw [← hadd]
              ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hh) (Nat.mul_le_mul_left _ hl)
  by_contra! hbad
  have hge := Nat.mul_le_mul_left (g * d) (show cap + 1 ≤ mass S k by omega)
  exact (not_lt_of_ge hge) (hscaled.trans_lt hnum)

private theorem paired_stage (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    {w rows} (i : Fin 10) {B : RowPair w rows i} {A : FixedPair B} (G : SharedGcd A)
    (S : Finset (Ideal Ambient)) (square : Bool)
    (hstage : if square then 4 ≤ i.val else 0 < i.val ∧ i.val ≤ 4)
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hin : Fits S (budget (i.val - 1)))
    (hpass : ∀ I ∈ S, Active I ∧ pairGood A I ∧
      orderOn I B.cheap ((stageAt i).reserve + 1) ∧
      orderOn I B.layered ((stageAt i).reserve + 1)) :
    Fits S (if square then budget i.val else exitBudget i) := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let m := (stageAt i).reserve + 1
  let s := residualShape (stageAt i).cheap x z
  let t := residualShape (stageAt i).layered x z
  let cap := if square then budget i.val else exitBudget i
  have hx : x ≤ (stageAt i).cheap.U := G.seed_le.trans (min_le_left _ _)
  have hz : z ≤ (stageAt i).cheap.B := G.ordinate_le.trans (min_le_left _ _)
  have hxp : x < p := hx.trans_lt (cheap_small i).1
  have hzp : z < p := hz.trans_lt (cheap_small i).2
  intro k
  rcases schedule_bound i square k hstage x z hx hz with hclip | ⟨r, hr, hrm, hnum⟩
  · exact (hin k).trans hclip
  let n := m + 1 - r
  let d := residualScale square k n
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d residualScale
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply h2 G.ordinary B.cheap B.layered _ r G.ordinary_ne hxp hzp hr
    · refine ⟨fixedIncl A.cheap.equation * G.cheapTail, G.cheap_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl A.layered.equation * G.layeredTail, G.layered_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    have hp := hpass I hm
    exact ⟨hp.1, hp.2.1.1.2.2, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤ pairCap s t k := by
    apply h5 G.cheapTail G.layeredTail s t _ k d G.cheap_ne G.layered_ne
      G.relativelyPrime (min_le_right _ _) (min_le_right _ _) G.cheap_caps G.layered_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, hg, hP, hQ⟩ := hpass I hm
    rw [G.cheap_factor] at hP
    rw [G.layered_factor] at hQ
    have hlP := h3 G.ordinary G.cheapTail I m r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hg.2.1 hP)
    have hlQ := h3 G.ordinary G.layeredTail I m r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hg.2.2 hQ)
    have hlen := h4 G.cheapTail G.layeredTail I ha n hn hlP hlQ
    refine ⟨ha, fun hdegree => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d residualScale
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square ≠ true := fun he => hIdual (hdual he I hm)
      have hk : k ≠ 3 := fun he => hIdual (show 0 < sectionDegree I 3 by
        rw [← he]
        exact Nat.pos_of_ne_zero hdegree)
      simpa [d, residualScale, hs, hk, hIdual] using hlen
  exact from_paired_bounds G.ordinary r (highScale r k) d _ _ (cap k) hh hl hnum

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_14_2_2.c4 := by
  intro w rows i B A S hi hin hpass
  obtain ⟨G⟩ := h1 w rows i B A
  have hlin (hi4 : i.val ≤ 4) : Fits S (exitBudget i) :=
    paired_stage h2 h3 h4 h5 i G S false ⟨hi, hi4⟩ (by simp) hin hpass
  refine ⟨hlin, ?_⟩
  by_cases hi4 : 4 ≤ i.val
  · exact paired_stage h2 h3 h4 h5 i G (S.filter dual) true hi4
      (fun _ I hI => (Finset.mem_filter.mp hI).2)
      (fits_mono (Finset.filter_subset _ _) hin)
      (fun I hI => hpass I (Finset.mem_filter.mp hI).1)
  · have he : exitBudget i = budget i.val := by
      simp [exitBudget, show i.val ≠ 4 by omega]
    rw [← he]
    exact fits_mono (Finset.filter_subset _ _) (hlin (by omega))

end
end K1_14_2_2_4
end PackSource_K1_14_2_2_4Split
