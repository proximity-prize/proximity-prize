/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
/- Derived from Lucieno (PR 618), and BitWonka (PR 581) for additional interpolation profiles.
   New 68.32 source parameters, adaptive schedule, cell assignments and integer receipts. Apache-2.0. -/
import ProximityPrize.SubmissionLower.K6833TerminalInactive
import ProximityPrize.SubmissionLower.K6833TerminalLocalTop
import ProximityPrize.SubmissionLower.K6833TerminalLowerBlock
import ProximityPrize.SubmissionLower.K6833TerminalModeCounts

set_option Elab.async false

namespace ProximityPrize.SubmissionLower.K6833Residual

open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetSpecialize SecondJetRelaxedDifferentiation

noncomputable section

set_option autoImplicit false

variable {K N : Type*} [Field K] [Fintype N]

def ProfileInterpolant (p : JetProfile) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ p.secondCap ∧ e 1 ≤ p.slopeCap ∧
    e 1+e 2+e 3 ≤ p.middleCap ∧ e 1+e 2+e 3+e 4 ≤ p.totalCap ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < profileCutoff p (e 1)) ∧
  (∀ i, MvPolynomial.X 0^p.order ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ p.derivativeOrder, ∀ f : Polynomial K, f.natDegree ≤ 131071 →
    ∀ z : K, ∀ S : Finset N, 181068 ≤ S.card →
      (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
        specialize f z ((pderiv 1)^[d] P) = 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in

theorem exists_profile_interpolant (j : Fin 6) (hN : Fintype.card N ≤ 262144)
    (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P, ProfileInterpolant (jetProfile j) nodes u0 u1 P := by
  classical
  let p := jetProfile j
  let exponent : ProfileIndex j → Fin 5 →₀ ℕ := SecondJetRelaxedGlobalIndex.exponent
  let caps (h : ℕ) := (profileCutoff p h+p.secondCap-1)/131071
  let W := lowerNodeSpace (K := K) (N := N) p.order p.totalCap p.secondCap
    p.slopeCap p.middleCap caps
  have hexponent : Function.Injective exponent :=
    SecondJetRelaxedGlobalIndex.exponent_injective _ _ _ _ _ _
  have hsB : 2*p.slopeCap ≤ p.secondCap := by
    fin_cases j <;> decide
  have hkm : p.derivativeOrder < p.order := by
    fin_cases j <;> decide
  have hexponentBounds (i : ProfileIndex j) :
      2*exponent i 1+exponent i 3 ≤ p.secondCap ∧ exponent i 1 ≤ p.slopeCap ∧
      exponent i 1+exponent i 2+exponent i 3 ≤ p.middleCap ∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4 ≤ p.totalCap ∧
      exponent i 0+131071*exponent i 2+131070*exponent i 3+131069*exponent i 1 <
        profileCutoff p (exponent i 1) :=
    SecondJetRelaxedGlobalIndex.exponent_bounds _ _ _ _ _ _ hsB i
  have hinactive (i : ProfileIndex j) (hi : ¬topColumnActive p.order i) :
      globalContactMap exponent p.order nodes u0 u1 (Pi.single i (1 : K)) ∈ W := by
    apply lowerNodeSpace_mem
    intro n
    obtain ⟨hB, hs, hU, hL, hD⟩ := hexponentBounds i
    have htop : ¬(sourceMiddle (exponent i) = p.middleCap ∧ exponent i 2 < p.order) :=
      fun h => hi ((topColumnActive_iff p.order i).mpr h)
    have hcolumn := inactive_column_mem_lower p.order p.totalCap p.secondCap
      p.slopeCap p.middleCap 131071 (profileCutoff p) (by decide)
      (nodes n) (u0 n) (u1 n) (exponent i) hB hs hU hL hD htop
    exact ⟨⟨_, hcolumn⟩, (globalContactMap_single exponent p.order nodes u0 u1 i n).symm⟩
  have hlower : Module.finrank K W ≤ 262144 * profileLowerRank p := by
    have hbound := lowerNodeSpace_rank (K := K) (N := N) p.order p.totalCap
      p.secondCap p.slopeCap p.middleCap caps
    have hrank := profileLowerRank_eq_rankBound j
    dsimp only at hrank
    change Module.finrank K W ≤ Fintype.card N *
      SecondJetRelaxedGlobalMap.rankBound p.order p.totalCap p.secondCap
        p.slopeCap (p.middleCap-1) caps at hbound
    change SecondJetRelaxedGlobalMap.rankBound p.order p.totalCap p.secondCap
      p.slopeCap (p.middleCap-1) caps = profileLowerRank p at hrank
    rw [hrank] at hbound
    exact hbound.trans (Nat.mul_le_mul_right _ hN)
  obtain ⟨P, hP, hsupp, hcontact⟩ := exists_global_contact_of_inactive_mem
    exponent hexponent p.order nodes u0 u1 W (topColumnActive p.order)
    hinactive (262144 * profileLowerRank p) hlower (profile_rank_lt_columns j)
  have hbounds (e : Fin 5 →₀ ℕ) (he : e ∈ P.support) :
      2*e 1+e 3 ≤ p.secondCap ∧ e 1 ≤ p.slopeCap ∧
      e 1+e 2+e 3 ≤ p.middleCap ∧ e 1+e 2+e 3+e 4 ≤ p.totalCap ∧
      e 0+131071*e 2+131070*e 3+131069*e 1 < profileCutoff p (e 1) := by
    obtain ⟨i, rfl⟩ := hsupp e he
    exact hexponentBounds i
  have hflat : ∀ i, MvPolynomial.X 0^p.order ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P) := fun i =>
    SecondJetGlobalDifferentiation.nested_to_flat_contact _ p.order (hcontact i)
  refine ⟨P, hP, hbounds, hflat, ?_⟩
  intro d hd f hf z S hS hvalues
  apply derivative_vanish P p.order 181068 131071 p.derivativeOrder p.minimumOrder
    d (by decide) (by decide) (lt_of_le_of_lt hd hkm) hd ?_ nodes u0 u1 hflat f hf z S hS hvalues
  intro e he
  have hcut := (hbounds e he).2.2.2.2
  dsimp [profileCutoff] at hcut
  norm_num
  omega

theorem exists_cell_interpolants (ids : Fin 6 × Fin 6 × Fin 6)
    (hN : Fintype.card N ≤ 262144) (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P : Fin 3 → Poly (K := K), ∀ j, ProfileInterpolant (cellConfig ids j) nodes u0 u1 (P j) := by
  have h (j : Fin 3) : ∃ P, ProfileInterpolant (cellConfig ids j) nodes u0 u1 P := by
    fin_cases j
    · exact exists_profile_interpolant ids.1 hN nodes u0 u1
    · exact exists_profile_interpolant ids.2.1 hN nodes u0 u1
    · exact exists_profile_interpolant ids.2.2 hN nodes u0 u1
  choose P hP using h
  exact ⟨P, hP⟩

end

end ProximityPrize.SubmissionLower.K6833Residual

#print axioms ProximityPrize.SubmissionLower.K6833Residual.exists_cell_interpolants

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
