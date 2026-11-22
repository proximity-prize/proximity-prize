import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import ProximityPrize.SubmissionLower.KoalaRuledEmbedding

-- merged module KoalaWeightedDegree
section Merged_KoalaWeightedDegree
set_option autoImplicit false

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open scoped BigOperators

variable {σ F : Type*} [Field F]

private def recordWeight (w : σ → ℕ) :
    MvPolynomial σ F →+* Polynomial (MvPolynomial σ F) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => Polynomial.C (X i) * Polynomial.X^(w i))

private theorem record_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (c : F) :
    recordWeight w (monomial m c) = Polynomial.monomial (Finsupp.weight w m) (monomial m c) := by
  change (monomial m c).eval₂ _ _ = _
  rw [eval₂_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
  have hmono : C c * (∏ i ∈ m.support, (X i : MvPolynomial σ F)^m i) = monomial m c := by
    simpa only [Finsupp.prod] using (MvPolynomial.monomial_eq (s := m) (a := c)).symm
  rw [hmono, Polynomial.C_mul_X_pow_eq_monomial]
  simp [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.mul_comm]

private theorem record_coeff (w : σ → ℕ) (f : MvPolynomial σ F) (n : ℕ) (m : σ →₀ ℕ) :
    ((recordWeight w f).coeff n).coeff m = if Finsupp.weight w m = n then f.coeff m else 0 := by
  classical
  have hf := f.support_sum_monomial_coeff
  conv_lhs => rw [← hf]
  simp only [map_sum, record_monomial, Polynomial.finsetSum_coeff, coeff_sum]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single_of_mem m hm]
    · split_ifs <;> simp [Polynomial.coeff_monomial, *]
    · intro i hi hne
      by_cases h : Finsupp.weight w i = n
      · simp [h, MvPolynomial.coeff_monomial, hne]
      · simp [Polynomial.coeff_monomial, h]
  · have hz : f.coeff m = 0 := notMem_support_iff.mp hm
    simp only [hz, ite_self]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hne : i ≠ m := fun h => hm (h ▸ hi)
    by_cases h : Finsupp.weight w i = n
    · simp [h, MvPolynomial.coeff_monomial, hne]
    · simp [Polynomial.coeff_monomial, h]

private theorem record_degree (w : σ → ℕ) (f : MvPolynomial σ F) :
    (recordWeight w f).natDegree = f.weightedTotalDegree w := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    ext m
    rw [record_coeff]
    by_cases hm : m ∈ f.support
    · simp [ne_of_lt ((le_weightedTotalDegree w hm).trans_lt hn)]
    · simp [notMem_support_iff.mp hm]
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    by_contra! hbig
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hbig
    have hh := congrArg (fun p : MvPolynomial σ F => p.coeff m) hz
    simp [record_coeff] at hh
    exact (mem_support_iff.mp hm) hh

private theorem record_ne_zero (w : σ → ℕ) {f : MvPolynomial σ F} (hf : f ≠ 0) :
    recordWeight w f ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  have hz := record_coeff w f (Finsupp.weight w m) m
  rw [h] at hz
  exact hm (by simpa using hz.symm)

theorem weighted_degree_mul (w : σ → ℕ) {f g : MvPolynomial σ F} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f*g).weightedTotalDegree w = f.weightedTotalDegree w + g.weightedTotalDegree w := by
  rw [← record_degree w (f*g), map_mul,
    Polynomial.natDegree_mul (record_ne_zero w hf) (record_ne_zero w hg), record_degree, record_degree]

#print axioms weighted_degree_mul
end
end SplitCut.Rect
end Merged_KoalaWeightedDegree

-- merged module KoalaRuledQuotient
section Merged_KoalaRuledQuotient
set_option autoImplicit false

namespace SplitCut.Rect
noncomputable section
open MvPolynomial

variable {F : Type*} [Field F]

def axisWeights : Fin 4 → ℕ := ![1,2,0,0]

abbrev ordinateWeight (p : Ring F) : ℕ := p.weightedTotalDegree axisWeights

theorem weight_exponent (m : Exp) : Finsupp.weight axisWeights m = m 0 + 2*m 1 := by
  rw [Finsupp.weight_eq_sum]
  simp [axisWeights, Fin.sum_univ_succ, nsmul_eq_mul, Nat.mul_comm]

theorem mem_space {p : Ring F} {d : Box} :
    p ∈ space F d ↔ p.degreeOf 1 ≤ d.velocity ∧ ordinateWeight p ≤ d.base+2*d.velocity ∧
      p.degreeOf 2 ≤ d.seed₀ ∧ p.degreeOf 3 ≤ d.seed₁ := by
  simp only [degreeOf_le_iff, ordinateWeight, weightedTotalDegree, Finset.sup_le_iff, weight_exponent]
  exact ⟨fun h => ⟨fun _ hm => (h hm).1, fun _ hm => (h hm).2.1, fun _ hm => (h hm).2.2.1,
      fun _ hm => (h hm).2.2.2⟩,
    fun ⟨h₁,h₀,h₂,h₃⟩ _ hm => ⟨h₁ _ hm, h₀ _ hm, h₂ _ hm, h₃ _ hm⟩⟩

def rootShift (d : Box) (g : Ring F) : Box :=
  ⟨d.base-ordinateWeight g, d.velocity, d.seed₀-g.degreeOf 2, d.seed₁-g.degreeOf 3⟩

theorem root_mul_mem_iff {g p : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {d : Box} (h₀ : ordinateWeight g ≤ d.base) (h₂ : g.degreeOf 2 ≤ d.seed₀)
    (h₃ : g.degreeOf 3 ≤ d.seed₁) :
    g*p ∈ space F d ↔ p ∈ space F (rootShift d g) := by
  by_cases hp : p = 0
  · simp only [hp, mul_zero, Submodule.zero_mem]
  rw [mem_space, mem_space, degreeOf_mul_eq (n:=1) hg hp, degreeOf_mul_eq (n:=2) hg hp,
    degreeOf_mul_eq (n:=3) hg hp]
  change _ ≤ d.velocity ∧ (g*p).weightedTotalDegree axisWeights ≤ _ ∧ _ ↔ _
  rw [weighted_degree_mul axisWeights hg hp]
  simp only [rootShift, ordinateWeight, hv, Nat.zero_add]
  change g.weightedTotalDegree axisWeights ≤ d.base at h₀
  omega

/-- The kernel of the root quotient on a large box consists of the exact shifted box of multiples. -/
theorem root_piece_rank {g : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {d : Box} (h₀ : ordinateWeight g ≤ d.base) (h₂ : g.degreeOf 2 ≤ d.seed₀)
    (h₃ : g.degreeOf 3 ≤ d.seed₁) :
    Module.finrank F (piece (Ideal.span {g}) d) +
      Module.finrank F (space F (rootShift d g)) = Module.finrank F (space F d) := by
  let I : Ideal (Ring F) := Ideal.span {g}
  let M := space F d
  let M' := space F (rootShift d g)
  let π := (Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict M
  have hmul : ∀ p ∈ M', g*p ∈ M := fun _ hp => (root_mul_mem_iff hg hv h₀ h₂ h₃).mpr hp
  let μ : M' →ₗ[F] M := ((LinearMap.mulLeft F g).domRestrict M').codRestrict M fun p => hmul _ p.2
  have hinj : Function.Injective μ := fun p q h => Subtype.ext
    (mul_left_cancel₀ hg (congrArg Subtype.val h))
  have hker : LinearMap.range μ = LinearMap.ker π := by
    apply le_antisymm
    · rintro _ ⟨p,rfl⟩
      rw [LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · intro x hx
      have hI : x.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
      obtain ⟨p,hp⟩ := Ideal.mem_span_singleton.mp hI
      have hm : g*p ∈ M := hp ▸ x.2
      exact ⟨⟨p,(root_mul_mem_iff hg hv h₀ h₂ h₃).mp hm⟩, Subtype.ext hp.symm⟩
  have hdim := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, ← hker, LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

#print axioms root_piece_rank
end
end SplitCut.Rect
end Merged_KoalaRuledQuotient

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