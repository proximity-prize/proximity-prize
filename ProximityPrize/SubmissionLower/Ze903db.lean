import ProximityPrize.SubmissionLower.ZsE91Ed
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qU3xjYb
noncomputable section
open Polynomial q7kdBxd qrzQ9fc
open scoped WithZero
variable {J:Input} {r :Bool} (D:GraphPrime J r) (h:Horizontal D)
private theorem normalize {K:Type} [Field K] (v :Valuation K ℤᵐ⁰)
    {f :K[X]} (hf :f≠0) :
    ∃ (c:K) (g:v.valuationSubring[X]) (i:ℕ),
      g.map v.valuationSubring.subtype=C c*f∧g.coeff i=1 := by
  classical
  obtain ⟨i,hi,hmax⟩:=Finset.exists_max_image f.support (fun j=>v (f.coeff j))
    (support_nonempty.mpr hf)
  have hin:f.coeff i≠0:=mem_support_iff.mp hi
  have hc (j:ℕ) :v ((f.coeff i)⁻¹*f.coeff j)≤1 := by
    rw [mul_comm,← div_eq_mul_inv,v.map_div]
    apply (div_le_one₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hin))).mpr
    by_cases hj:j∈f.support
    · exact hmax j hj
    · have hz :f.coeff j=0:=notMem_support_iff.mp hj
      simp [hz]
  let G:=C (f.coeff i)⁻¹*f
  let O:=v.valuationSubring.toSubring
  have hG: (↑G.coeffs :Set K)⊆O:= by
    intro a ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp ha
    change v (G.coeff j)≤1
    rw [coeff_C_mul]
    exact hc j
  refine ⟨(f.coeff i)⁻¹,G.toSubring O hG,i,G.map_toSubring O hG,Subtype.ext ?_⟩
  change ((G.toSubring O hG).coeff i).val=(1 :K)
  rw [coeff_toSubring',coeff_C_mul]
  exact inv_mul_cancel₀ hin
end
end qU3xjYb
