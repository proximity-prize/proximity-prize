import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z7
namespace ProximityPrize.SubmissionLower.RCN059
open scoped BigOperators
noncomputable section
variable {k F L Γ:Type*} [Field k] [Field F] [Field L]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq F:=Classical.decEq F
def ResidueApprox (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F):Prop:=
 ∀ f:F,v (φ f) ≤ 1 → ∃ c:k,v (φ (f-κ c)) < 1
def ConstantPolynomialUnit (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (w:ℕ):Prop:=
 ∀ c:Fin (w+1) → k,(∃ i,c i≠0) →
   v (∑ i,φ (κ (c i))*x^(i:ℕ))=1
private theorem sum_eq_one_of_close {w:ℕ}
   (v:Valuation L Γ) (x:L) (hx:v x=1)
   (b c:Fin (w+1) → L)
   (hclose:∀ i,v (b i-c i) < 1)
   (hc:v (∑ i,c i*x^(i:ℕ))=1):
   v (∑ i,b i*x^(i:ℕ))=1:=by
 have herr:v (∑ i,(b i-c i)*x^(i:ℕ)) < 1:=by
   apply v.map_sum_lt (by simp)
   intro i _
   simpa only [map_mul,map_pow,hx,one_pow,mul_one] using hclose i
 have hsplit:(∑ i,b i*x^(i:ℕ))=
     (∑ i,c i*x^(i:ℕ))+
     (∑ i,(b i-c i)*x^(i:ℕ)):=by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro i _
   ring
 rw [hsplit,v.map_add_eq_of_lt_left (by simpa only [hc] using herr),hc]
theorem valuation_sum_eq_dominant_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (j:Fin (w+1)) (haj:a j≠0)
   (hmax:∀ i,v (φ (a i)) ≤ v (φ (a j))):
   v (∑ i,φ (a i)*x^(i:ℕ))=v (φ (a j)):=by
 have hφj:φ (a j)≠0:=by
   intro h
   apply haj
   apply φ.injective
   simpa using h
 have hvj:v (φ (a j))≠0:=(Valuation.ne_zero_iff v).mpr hφj
 have hnorm:∀ i,v (φ (a i/a j)) ≤ 1:=by
   intro i
   rw [map_div₀,map_div₀]
   exact (div_le_one₀ (zero_lt_iff.mpr hvj)).mpr (hmax i)
 choose c hc using fun i => hres (a i/a j) (hnorm i)
 have hcj:c j≠0:=by
   intro h
   have hbad:=hc j
   simpa [h,haj] using hbad
 have hsum:v (∑ i,φ (a i/a j)*x^(i:ℕ))=1:=by
   apply sum_eq_one_of_close v x hx
     (fun i => φ (a i/a j)) (fun i => φ (κ (c i)))
   · intro i
     simpa only [map_sub] using hc i
   · exact hunit c ⟨j,hcj⟩
 have hscale:(∑ i,φ (a i)*x^(i:ℕ))=
     φ (a j)*(∑ i,φ (a i/a j)*x^(i:ℕ)):=by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [map_div₀]
   field_simp
 rw [hscale,map_mul,hsum,mul_one]
theorem valuation_coefficient_le_sum_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   v (φ (a i)) ≤ v (∑ j,φ (a j)*x^(j:ℕ)):=by
 classical
 by_cases hai:a i=0
 · simp [hai]
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 obtain ⟨j,_,hmax⟩:=
   Finset.exists_max_image Finset.univ (fun j:Fin (w+1) => v (φ (a j)))
     Finset.univ_nonempty
 have haj:a j≠0:=by
   intro h
   have hz:v (φ (a j))=0:=by simp [h]
   apply hvi
   apply le_antisymm
   · simpa only [hz] using hmax i (Finset.mem_univ i)
   · exact zero_le
 rw [valuation_sum_eq_dominant_of_residueApprox v φ κ x hx hres hunit a j haj
   (fun z => hmax z (Finset.mem_univ z))]
 exact hmax i (Finset.mem_univ i)
theorem coefficient_pole_le_generic_value_of_residueApprox {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 have hval:=valuation_coefficient_le_sum_of_residueApprox
   v φ κ x hx hres hunit a i
 by_cases hai:a i=0
 · simp only [hai,map_zero,RCN187.poleOrder,
     WithZero.log_zero,max_self]
   exact le_max_left _ _
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 have hsum:v (∑ j,φ (a j)*x^(j:ℕ))≠0:=
   ne_of_gt ((zero_lt_iff.mpr hvi).trans_le hval)
 exact max_le_max_left 0 ((WithZero.log_le_log hvi hsum).mpr hval)
end
end ProximityPrize.SubmissionLower.RCN059
