import ProximityPrize.SubmissionLower.KoalaRectSections
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open scoped BigOperators Pointwise

def diagonal (a b c n : ℕ) : Box := ⟨a*n, n, b*n, c*n⟩

abbrev project (F : Type*) [Field F] (a b c : ℕ) :=
  monomialMap F (diagonal a b c 1).support

private theorem add_support (a b c n : ℕ) :
    (diagonal a b c n).support + (diagonal a b c 1).support ⊆
      (diagonal a b c (n+1)).support := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨h₁, h₀, h₂, h₃⟩
  rcases hv with ⟨j₁, j₀, j₂, j₃⟩
  simp only [diagonal, Nat.mul_one] at h₁ h₀ h₂ h₃ j₁ j₀ j₂ j₃
  change _ ≤ n+1 ∧ _ ≤ a*(n+1)+2*(n+1) ∧ _ ≤ b*(n+1) ∧ _ ≤ c*(n+1)
  simp only [Finsupp.add_apply, Nat.mul_succ]
  omega

theorem dilate (a b c n : ℕ) :
    n • (diagonal a b c 1).support ⊆ (diagonal a b c n).support := by
  induction n with
  | zero =>
    rw [zero_smul, Set.zero_subset]
    exact ⟨by simp [diagonal], by simp [diagonal], by simp [diagonal], by simp [diagonal]⟩
  | succ n ih =>
    rw [succ_nsmul]
    exact (Set.add_subset_add ih subset_rfl).trans (add_support a b c n)

private def take (m : Exp) (a b c : ℕ) : Exp :=
  let j := min (m 1) 1
  Finsupp.equivFunOnFinite.symm
    ![min (m 0) (a+2*(1-j)), j, min (m 2) b, min (m 3) c]

private theorem take_mem (m : Exp) (a b c : ℕ) :
    take m a b c ∈ (diagonal a b c 1).support := by
  change min (m 1) 1 ≤ 1 ∧
    min (m 0) (a+2*(1-min (m 1) 1)) + 2*min (m 1) 1 ≤ a*1+2*1 ∧
    min (m 2) b ≤ b*1 ∧ min (m 3) c ≤ c*1
  omega

private theorem take_le (m : Exp) (a b c : ℕ) : take m a b c ≤ m := by
  intro i
  fin_cases i <;> exact min_le_left _ _

private theorem rest_mem {m : Exp} {a b c n : ℕ} (hm : m ∈ (diagonal a b c (n+1)).support) :
    m - take m a b c ∈ (diagonal a b c n).support := by
  rcases hm with ⟨hv, hy, hu, hw⟩
  simp only [diagonal, Nat.mul_succ] at hv hy hu hw
  change m 1 - min (m 1) 1 ≤ n ∧
    (m 0 - min (m 0) (a+2*(1-min (m 1) 1))) + 2*(m 1-min (m 1) 1) ≤ a*n+2*n ∧
    m 2 - min (m 2) b ≤ b*n ∧ m 3 - min (m 3) c ≤ c*n
  omega

variable {F : Type*} [Field F]

private theorem lift_monomial (a b c n : ℕ) (m : Exp)
    (hm : m ∈ (diagonal a b c n).support) (u : F) :
    ∃ p : MvPolynomial (diagonal a b c 1).support F,
      project F a b c p = monomial m u ∧ p.totalDegree ≤ n := by
  induction n generalizing m with
  | zero =>
    have hz : m = 0 := by
      rcases hm with ⟨h₁, h₀, h₂, h₃⟩
      simp only [diagonal, Nat.mul_zero, Nat.add_zero] at h₁ h₀ h₂ h₃
      ext i
      fin_cases i
      · change m 0 = 0
        omega
      · exact Nat.eq_zero_of_le_zero h₁
      · exact Nat.eq_zero_of_le_zero h₂
      · exact Nat.eq_zero_of_le_zero h₃
    exact ⟨C u, by simp [hz, project, monomialMap], by simp⟩
  | succ n ih =>
    obtain ⟨p, hp, hd⟩ := ih _ (rest_mem hm)
    let i : (diagonal a b c 1).support := ⟨take m a b c, take_mem m a b c⟩
    refine ⟨p * X i, ?_, (totalDegree_mul _ _).trans (Nat.add_le_add hd (by simp))⟩
    rw [map_mul, hp, show project F a b c (X i) = monomial (take m a b c) 1 from aeval_X _ _,
      monomial_mul_monomial, tsub_add_cancel_of_le (take_le m a b c), mul_one]

theorem lift_diagonal {a b c n : ℕ} {g : Ring F} (hg : g ∈ space F (diagonal a b c n)) :
    ∃ p : MvPolynomial (diagonal a b c 1).support F,
      project F a b c p = g ∧ p.totalDegree ≤ n := by
  classical
  choose p hp hd using fun m : g.support => lift_monomial a b c n m.val (hg m.property) (g.coeff m)
  refine ⟨∑ m : g.support, p m, ?_, totalDegree_finsetSum_le (fun m _ => hd m)⟩
  rw [map_sum]
  simp only [hp]
  rw [Finset.sum_coe_sort g.support fun m => monomial m (g.coeff m)]
  exact g.support_sum_monomial_coeff

theorem project_surjective {a b c : ℕ} (hb : 0<b) (hc : 0<c) :
    Function.Surjective (project F a b c) := by
  apply monomialMap_surjective
  intro i
  fin_cases i <;>
    simp [Box.support, diagonal, Finsupp.single_apply] <;> omega

theorem diagonal_piece (I : Ideal (Ring F)) (a b c n : ℕ) :
    affineHilbertFunction (I.comap (project F a b c)) n =
      Module.finrank F (piece I (diagonal a b c n)) := by
  let φ := project F a b c
  let g := Ideal.quotientMapₐ I φ le_rfl
  have hbound (p : MvPolynomial (diagonal a b c 1).support F) (hp : p.totalDegree ≤ n) :
      φ p ∈ space F (diagonal a b c n) :=
    restrictSupport_mono F (dilate a b c n)
      (monomialMap_mem_restrictSupport_nsmul (show 0 ∈ (diagonal a b c 1).support from
        ⟨by simp [diagonal], by simp, by simp, by simp⟩) hp)
  let L : quotientDegreeLE (I.comap φ) n →ₗ[F] piece I (diagonal a b c n) :=
    (g.toLinearMap.domRestrict _).codRestrict _ fun x => by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.2
      rw [LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply, ← hpx]
      exact ⟨_, hbound p hp, rfl⟩
  have hL : Function.Bijective L := by
    refine ⟨fun x y hxy => Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val hxy)), ?_⟩
    intro x
    obtain ⟨f, hf, hx⟩ := Submodule.mem_map.mp x.2
    obtain ⟨p, hp, hd⟩ := lift_diagonal hf
    refine ⟨⟨Ideal.Quotient.mk (I.comap φ) p, mem_quotientDegreeLE.mpr ⟨p, hd, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I (φ p) = x.val
    rw [hp]
    exact hx
  exact (LinearEquiv.ofBijective L hL).finrank_eq

#print axioms lift_diagonal
#print axioms diagonal_piece
end
end SplitCut.Rect
