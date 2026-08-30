import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CP
import ProximityPrize.SubmissionLower.F3
section ProximityFlatProofPort
namespace MonomialOrder
open MvPolynomial
open scoped MonomialOrder
variable {sigma:Type*} {m:MonomialOrder sigma}
variable {R:Type*} [CommSemiring R]
variable (m) in
noncomputable def degree (f:MvPolynomial sigma R):sigma →₀ ℕ:=
 m.toSyn.symm (f.support.sup m.toSyn)
variable (m) in
noncomputable def leadingCoeff (f:MvPolynomial sigma R):R:=
 f.coeff (m.degree f)
@[simp]
theorem degree_zero:m.degree (0:MvPolynomial sigma R)=0:=by
 simp [degree]
theorem degree_le_iff {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}:
   m.degree f ≼[m] d ↔ ∀ c∈f.support,c ≼[m] d:=by
 unfold degree
 simp only [AddEquiv.apply_symm_apply,Finset.sup_le_iff,
   MvPolynomial.mem_support_iff,ne_eq]
theorem le_degree {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}
   (hd:d∈f.support):d ≼[m] m.degree f:=by
 unfold degree
 simp only [AddEquiv.apply_symm_apply,Finset.le_sup hd]
theorem coeff_eq_zero_of_lt {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}
   (hd:m.degree f ≺[m] d):f.coeff d=0:=by
 rw [←not_le] at hd
 by_contra hf
 apply hd (m.le_degree (MvPolynomial.mem_support_iff.mpr hf))
@[simp]
theorem leadingCoeff_zero:m.leadingCoeff (0:MvPolynomial sigma R)=0:=by
 simp [degree,leadingCoeff]
theorem leadingCoeff_ne_zero_iff {f:MvPolynomial sigma R}:
   m.leadingCoeff f≠0 ↔ f≠0:=by
 constructor
 · rw [not_imp_not]
   intro hf
   rw [hf,leadingCoeff_zero]
 · intro hf
   rw [←support_nonempty] at hf
   rw [leadingCoeff, ←MvPolynomial.mem_support_iff,degree]
   suffices f.support.sup m.toSyn∈m.toSyn '' f.support by
     obtain ⟨d,hd,hd'⟩:=this
     rw [←hd',AddEquiv.symm_apply_apply]
     exact hd
   exact Finset.sup_mem_of_nonempty hf
@[simp]
theorem leadingCoeff_eq_zero_iff {f:MvPolynomial sigma R}:
   leadingCoeff m f=0 ↔ f=0:=by
 simp only [←not_iff_not,leadingCoeff_ne_zero_iff]
lemma degree_mem_support {p:MvPolynomial sigma R} (hp:p≠0):
   m.degree p∈p.support:=by
 unfold degree
 suffices p.support.sup m.toSyn∈m.toSyn '' p.support by
   obtain ⟨d,hd,hd'⟩:=this
   rw [←hd',AddEquiv.symm_apply_apply]
   exact hd
 exact Finset.sup_mem_of_nonempty (support_nonempty.mpr hp)
theorem degree_mul_le {f g:MvPolynomial sigma R}:
   m.degree (f*g) ≼[m] m.degree f+m.degree g:=by
 classical
 letI:DecidableEq sigma:=Classical.decEq sigma
 rw [degree_le_iff]
 intro c
 rw [←not_lt,MvPolynomial.mem_support_iff,not_imp_not]
 intro hc
 rw [coeff_mul]
 apply Finset.sum_eq_zero
 rintro ⟨d,e⟩ hde
 simp only [Finset.mem_antidiagonal] at hde
 dsimp only
 by_cases hd:m.degree f ≺[m] d
 · rw [m.coeff_eq_zero_of_lt hd,zero_mul]
 · suffices m.degree g ≺[m] e by
     rw [m.coeff_eq_zero_of_lt this,mul_zero]
   simp only [not_lt] at hd
   apply lt_of_add_lt_add_left (a:=m.toSyn d)
   grw [←map_add _ _ e,hd, ←map_add,hde]
   exact hc
theorem coeff_mul_of_add_of_degree_le {f g:MvPolynomial sigma R}
   {a b:sigma →₀ ℕ} (ha:m.degree f ≼[m] a) (hb:m.degree g ≼[m] b):
   (f*g).coeff (a+b)=f.coeff a*g.coeff b:=by
 classical
 letI:DecidableEq sigma:=Classical.decEq sigma
 rw [coeff_mul,Finset.sum_eq_single (a,b)]
 · rintro ⟨c,d⟩ hcd h
   simp only [Finset.mem_antidiagonal] at hcd
   by_cases hf:m.degree f ≺[m] c
   · rw [m.coeff_eq_zero_of_lt hf,zero_mul]
   · suffices m.degree g ≺[m] d by
       rw [coeff_eq_zero_of_lt this,mul_zero]
     rw [not_lt] at hf
     rw [←not_le]
     intro hf'
     apply h
     suffices c=a by
       simpa [Prod.mk.injEq,this] using hcd
     apply m.toSyn.injective
     apply le_antisymm (le_trans hf ha)
     apply le_of_add_le_add_right (a:=m.toSyn b)
     rw [←map_add, ←hcd,map_add]
     simp only [add_le_add_iff_left]
     exact le_trans hf' hb
 · simp
theorem coeff_mul_of_degree_add {f g:MvPolynomial sigma R}:
   (f*g).coeff (m.degree f+m.degree g)=
     m.leadingCoeff f*m.leadingCoeff g:=
 coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)
theorem degree_mul_of_mul_leadingCoeff_ne_zero {f g:MvPolynomial sigma R}
   (hfg:m.leadingCoeff f*m.leadingCoeff g≠0):
   m.degree (f*g)=m.degree f+m.degree g:=by
 apply m.toSyn.injective
 apply le_antisymm degree_mul_le
 apply le_degree
 rw [MvPolynomial.mem_support_iff,coeff_mul_of_degree_add]
 exact hfg
theorem degree_mul [NoZeroDivisors R] {f g:MvPolynomial sigma R}
   (hf:f≠0) (hg:g≠0):
   m.degree (f*g)=m.degree f+m.degree g:=by
 apply degree_mul_of_mul_leadingCoeff_ne_zero
 simp only [ne_eq,mul_eq_zero,leadingCoeff_eq_zero_iff,not_or]
 tauto
end MonomialOrder
end ProximityFlatProofPort
