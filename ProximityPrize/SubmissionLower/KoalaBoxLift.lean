import ProximityPrize.SubmissionLower.KoalaBoxDegree
import ProximityPrize.SubmissionLower.KoalaRawBounds -- serialize candidate build

set_option autoImplicit false
namespace SplitCut.BoxDegree
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

def takeBox (m : Exp) (a b c : ℕ) : Exp :=
  Finsupp.equivFunOnFinite.symm fun i : Idx => i.elim (min (m none) a)
    ![min (m (some 0)) b,min (m (some 1)) c]

private theorem lift_monomial (a b c n : ℕ) (m : Exp) (hm : m ∈ exps (a*n) (b*n) (c*n))
    (u : F) : ∃ p : MvPolynomial (exps a b c) F,
      proj F a b c p = monomial m u ∧ p.totalDegree ≤ n := by
  induction n generalizing m with
  | zero =>
    have hz : m = 0 := by
      rcases hm with ⟨hx,hy,hz⟩
      ext i
      cases i with
      | none => simpa using (Nat.eq_zero_of_le_zero (by simpa using hx) : m none = 0)
      | some i =>
        fin_cases i
        · simpa using (Nat.eq_zero_of_le_zero (by simpa using hy) : m (some 0) = 0)
        · simpa using (Nat.eq_zero_of_le_zero (by simpa using hz) : m (some 1) = 0)
    exact ⟨C u, by simp [hz,proj,monomialMap], by simp⟩
  | succ n ih =>
    let q := takeBox m a b c
    have hq : q ∈ exps a b c := ⟨min_le_right _ _, min_le_right _ _, min_le_right _ _⟩
    have hle : q ≤ m := by
      intro i
      cases i with
      | none => exact min_le_left _ _
      | some i => fin_cases i <;> exact min_le_left _ _
    have hc : m-q ∈ exps (a*n) (b*n) (c*n) := by
      rcases hm with ⟨hx,hy,hz⟩
      simp only [Nat.mul_succ] at hx hy hz
      change m none - min (m none) a ≤ _ ∧ m (some 0) - min (m (some 0)) b ≤ _ ∧
        m (some 1) - min (m (some 1)) c ≤ _
      omega
    obtain ⟨p,hp,hd⟩ := ih _ hc
    let i : exps a b c := ⟨q,hq⟩
    refine ⟨p * MvPolynomial.X i, ?_, (totalDegree_mul _ _).trans ?_⟩
    · rw [map_mul, hp, show proj F a b c (MvPolynomial.X i) = monomial q 1 from aeval_X _ _,
        monomial_mul_monomial, tsub_add_cancel_of_le hle, mul_one]
    · exact Nat.add_le_add hd (by simp)

/-- Every polynomial in the dilated box lifts to ordinary total degree at most the dilation. -/
theorem lift_box {a b c n : ℕ} {g : MvPolynomial Idx F}
    (hg : g ∈ space F (a*n) (b*n) (c*n)) :
    ∃ p : MvPolynomial (exps a b c) F, proj F a b c p = g ∧ p.totalDegree ≤ n := by
  classical
  choose p hp hd using fun m : g.support => lift_monomial a b c n m.val (hg m.property) (g.coeff m)
  refine ⟨∑ m : g.support, p m, ?_, totalDegree_finsetSum_le (fun m _ => hd m)⟩
  rw [map_sum]
  simp only [hp]
  rw [Finset.sum_coe_sort g.support fun m => monomial m (g.coeff m)]
  exact g.support_sum_monomial_coeff

theorem mono {a b c x y z : ℕ} (ha : a≤x) (hb : b≤y) (hc : c≤z) :
    space F a b c ≤ space F x y z :=
  restrictSupport_mono F (fun _ h => ⟨h.1.trans ha,h.2.1.trans hb,h.2.2.trans hc⟩)

end
end SplitCut.BoxDegree
