import ProximityPrize.SubmissionLower.BCHKSConcreteStagedPair
import ProximityPrize.SubmissionLower.BCHKSSelectedHenselData
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionLower.BCHKSSelectedNonpole
import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The coordinate-incidence part of the outer assembly.  It is stated
separately because it is independent of all Hensel choices. -/
theorem exists_large_domain_fibers
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : T → Polynomial IRSProfile.Field)
    (dH d D : ℕ)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + (z : IRSProfile.Field) * U 1 i) :
    ∃ A' : Finset IRSProfile.Field, 131072 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 131071 + 2) * dH * d * D < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : IRSProfile.Index,
          IRSProfile.domain i = (x : IRSProfile.Field) ∧
          Polynomial.eval (x : IRSProfile.Field) (P z) =
            U 0 i + (z : IRSProfile.Field) * U 1 i := by
  classical
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 131071 + 2) * dH * d * D <
      (T.filter fun z => i ∈ A z).card
  have hG : 131072 ≤ G.card := by
    simpa [G] using concrete_many_large_fibers_plus T A dH d D
      (by norm_num [IRSProfile.Index]) hrow hT
  let A' : Finset IRSProfile.Field := G.image IRSProfile.domain
  have hA' : A'.card = G.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
  let idx : A' → IRSProfile.Index := fun x => Classical.choose
    (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧ IRSProfile.domain (idx x) = (x : IRSProfile.Field) := by
    have hs := Classical.choose_spec (Finset.mem_image.mp x.property)
    exact hs
  let Fib : A' → Finset T := fun x => T.attach.filter fun z =>
    idx x ∈ A (z : IRSProfile.Field)
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 131071 + 2) * dH * d * D <
      (T.attach.filter (fun z : T => idx x ∈ A (z : IRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : IRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : IRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA


/-- Conditional degree-at-least-two outer assembly.  Once a selected factor
has supplied the Hensel/non-pole package, the incidence estimate produces the
base-`Z` interpolation set and the canonical alignment theorem finishes the
branch. -/
theorem degree_ge_two_outer_assembly
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    {H : IRSProfile.Field[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : IRSProfile.Field) (R : IRSProfile.Field[X][X][Y])
    (hHyp : RationalFunctions.HenselNumerators.Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX e : ℕ) (hkDX : k < DX)
    (hHD : Polynomial.Bivariate.totalDegree H ≤ D)
    (hRD : ∀ i ∈ R.support, Polynomial.Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Polynomial.Bivariate.natDegreeY R)
    (T : Finset IRSProfile.Field) (P : T → Polynomial IRSProfile.Field)
    (S : SelectedHenselData x₀ R H hHyp hzeta D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : IRSProfile.Field)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hcard : 2*DX*H.natDegree*d*D + e + 1 < T.card)
    (hkF : k < Fintype.card IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (Arow z).card)
    (hT : 2 * 111624646 * H.natDegree * d * D + 76721 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ Arow z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + (z : IRSProfile.Field) * U 1 i)
    (hk : k = 131071) :
    (∀ t, k < t → t < DX →
      RationalFunctions.HenselNumerators.finiteAlpha (R:=R) (H:=H) x₀ DX t = 0) ∧
    ∃ p₀ p₁ : IRSProfile.Field[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : IRSProfile.Field) * p₁ := by
  classical
  obtain ⟨A, hA, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers U T Arow P H.natDegree d D hrow hT hagree
  have hne : ∀ x : A, (Fib x).Nonempty := by
    intro x
    exact Finset.card_pos.mp (Nat.zero_lt_of_lt (hFib x))
  let zpick : ∀ x : A, T := fun x => Classical.choose (hne x)
  have hzpick (x : A) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : A → IRSProfile.Index := fun x => Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : A) : IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 0 (idx ⟨x, hx⟩) else 0
  let U₁ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : A, ∀ z ∈ Fib x,
      (P z).eval (x : IRSProfile.Field) = U₀ x + (z : IRSProfile.Field) * U₁ x := by
    intro x z hz
    obtain ⟨i, hi, he⟩ := hinc x z hz
    have hii : i = idx x := IRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [U₀, U₁, x.property] using he
  apply hensel_baseZ_alignment_final x₀ R hHyp hzeta D d k DX e hkDX hHD hRD hRdeg
    T S.root P hPdeg S.hx S.hy S.hsL S.hsimple S.hExact S.hslope S.hW S.hxi
  · intro t _ z
    exact (hNP z).hden t
  · exact S.hweight
  · exact hcard
  · exact hkF
  · exact A
  · simpa [hk] using hA
  · exact U₀
  · exact U₁
  · intro x
    simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hFib x
  · exact halign

end ProximityPrize.SubmissionLower
