import ProximityPrize.SubmissionLower.KoalaRuledQuotient

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

namespace SplitCut.Rect
noncomputable section
open MvPolynomial Filter
open scoped Polynomial

variable {F : Type*} [Field F]

def Box.debit (d k : Box) : Box :=
  ⟨d.base-k.base, d.velocity-k.velocity, d.seed₀-k.seed₀, d.seed₁-k.seed₁⟩

private theorem debit_add (d k : Box) (h₀ : k.base ≤ d.base) (h₁ : k.velocity ≤ d.velocity)
    (h₂ : k.seed₀ ≤ d.seed₀) (h₃ : k.seed₁ ≤ d.seed₁) :
    (d.debit k).add k = d := by
  cases d
  simp only [Box.debit, Box.add, Nat.sub_add_cancel h₀, Nat.sub_add_cancel h₁,
    Nat.sub_add_cancel h₂, Nat.sub_add_cancel h₃]

def volume (d : Box) : ℕ := (d.velocity+1)*(d.base+d.velocity+1)*(d.seed₀+1)*(d.seed₁+1)

private theorem graph_rank {g : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {J : Ideal (Ring F)} (hJ : Ideal.span {g} ≤ J)
    {k d : Box} (S : Section (Ideal.span {g}) k) (hS : S.finite ∈ J)
    (hreg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {g}) S.finite))
    (hpad : 2*S.order ≤ d.base) (h₀ : ordinateWeight g ≤ d.base)
    (h₂ : g.degreeOf 2 ≤ d.seed₀) (h₃ : g.degreeOf 3 ≤ d.seed₁) :
    (Module.finrank F (piece J (d.add k)) : ℚ) ≤
      (volume (d.add k) : ℚ) - volume (rootShift (d.add k) g) - volume d + volume (rootShift d g) := by
  have hd := root_piece_rank hg hv h₀ h₂ h₃
  have hdk := root_piece_rank hg hv (d := d.add k)
    (h₀.trans (Nat.le_add_right _ _)) (h₂.trans (Nat.le_add_right _ _))
    (h₃.trans (Nat.le_add_right _ _))
  have hdrop := hilbert_drop hJ S hpad hS hreg
  have hvolume (box : Box) : Module.finrank F (space F box) = volume box := ambient_rank F box
  simp only [hvolume] at hd hdk
  have hdq := congrArg (Nat.cast (R:=ℚ)) hd
  have hdkq := congrArg (Nat.cast (R:=ℚ)) hdk
  have hdropq := Nat.cast_le (α:=ℚ).mpr hdrop
  push_cast at hdq hdkq hdropq
  linarith only [hdq, hdkq, hdropq]

private def volumePoly (a b c h t u v : ℚ) : ℚ[X] :=
  (Polynomial.X+Polynomial.C (1-t)) *
    (Polynomial.C (a+1)*Polynomial.X+Polynomial.C (1-h-t)) *
    (Polynomial.C b*Polynomial.X+Polynomial.C (1-u)) *
    (Polynomial.C c*Polynomial.X+Polynomial.C (1-v))

private def difference (a b c y z w h t u v : ℚ) : ℚ[X] :=
  volumePoly a b c 0 0 0 0 - volumePoly a b c y 0 z w -
    volumePoly a b c h t u v + volumePoly a b c (h+y) t (u+z) (v+w)

def mixedLead (a b c y z w h t u v : ℚ) : ℚ :=
  y*t*b*c + (z*c+w*b)*(t*(a+1)+h+t) + y*(u*c+v*b) + (a+1)*(z*v+w*u)

private theorem difference_expansion (a b c y z w h t u v : ℚ) :
    let R := difference a b c y z w h t u v
    let M := mixedLead a b c y z w h t u v
    R = Polynomial.C M*Polynomial.X^2 + Polynomial.C (R.eval 1-R.eval 0-M)*Polynomial.X +
      Polynomial.C (R.eval 0) := by
  dsimp only [difference, volumePoly, mixedLead]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_1, Polynomial.C_0]
  ring

private theorem volumePoly_eval (a b c h t u v q : ℚ) :
    (volumePoly a b c h t u v).eval q =
      (q-t+1)*((a+1)*q-h-t+1)*(b*q-u+1)*(c*q-v+1) := by
  unfold volumePoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The affine graph degree is bounded by the mixed degree of the root and relative tangent cuts. -/
theorem graph_degree {g : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {J : Ideal (Ring F)} (hJ : Ideal.span {g} ≤ J)
    {k : Box} (S : Section (Ideal.span {g}) k) (hS : S.finite ∈ J)
    (hreg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {g}) S.finite))
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hdim : (affineHilbertPolynomial (J.comap (project F a b c))).natDegree = 2) :
    affineDegree (J.comap (project F a b c)) ≤
      2*mixedLead a b c (ordinateWeight g) (g.degreeOf 2) (g.degreeOf 3)
        k.base k.velocity k.seed₀ k.seed₁ := by
  let y := ordinateWeight g
  let z := g.degreeOf 2
  let w := g.degreeOf 3
  let R := difference a b c y z w k.base k.velocity k.seed₀ k.seed₁
  let M := mixedLead a b c y z w k.base k.velocity k.seed₀ k.seed₁
  have hR : R = Polynomial.C M*Polynomial.X^2 +
      Polynomial.C (R.eval 1-R.eval 0-M)*Polynomial.X + Polynomial.C (R.eval 0) :=
    difference_expansion ..
  have hRdeg : R.natDegree ≤ 2 := by rw [hR]; exact Polynomial.natDegree_quadratic_le
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim (R:=R) hRdeg ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop
      (y+z+w+2*S.order+k.base+k.velocity+k.seed₀+k.seed₁)] with n hn
    have hl₀ := Nat.le_mul_of_pos_left n ha
    have hl₂ := Nat.le_mul_of_pos_left n hb
    have hl₃ := Nat.le_mul_of_pos_left n hc
    have h₀ : k.base ≤ a*n := by omega
    have h₁ : k.velocity ≤ n := by omega
    have h₂ : k.seed₀ ≤ b*n := by omega
    have h₃ : k.seed₁ ≤ c*n := by omega
    let d := (diagonal a b c n).debit k
    have hpad : 2*S.order ≤ d.base := by dsimp only [d, Box.debit, diagonal]; omega
    have hy₀ : y ≤ a*n-k.base := by omega
    have hz₀ : z ≤ b*n-k.seed₀ := by omega
    have hw₀ : w ≤ c*n-k.seed₁ := by omega
    have hda : d.add k = diagonal a b c n := debit_add _ _ h₀ h₁ h₂ h₃
    have h := graph_rank hg hv hJ S hS hreg hpad hy₀ hz₀ hw₀
    rw [hda, ← diagonal_piece J a b c n] at h
    change _ ≤ R.eval _
    unfold R difference
    simp only [Polynomial.eval_sub, Polynomial.eval_add, volumePoly_eval]
    simp only [volume, rootShift, diagonal, d, Box.debit, ← show y = ordinateWeight g from rfl,
      ← show z = g.degreeOf 2 from rfl, ← show w = g.degreeOf 3 from rfl] at h
    push_cast [Nat.cast_sub h₀, Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃,
      Nat.cast_sub hy₀, Nat.cast_sub hz₀, Nat.cast_sub hw₀,
      Nat.cast_sub (hy₀.trans (Nat.sub_le _ _)), Nat.cast_sub (hz₀.trans (Nat.sub_le _ _)),
      Nat.cast_sub (hw₀.trans (Nat.sub_le _ _))] at h
    refine h.trans_eq ?_
    ring
  · have hcoeff : R.coeff 2 = M := by
      rw [hR]
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [hcoeff]
    change (Nat.factorial 2 : ℚ)*M = 2*M
    norm_num [Nat.factorial]

#print axioms graph_degree
end
end SplitCut.Rect
