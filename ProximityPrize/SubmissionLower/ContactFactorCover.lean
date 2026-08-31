import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactGenericSurface
namespace ProximityPrize.SubmissionLower.ContactFactorCover
open UniqueFactorizationMonoid ContactGenericSurface ContactInterpolation
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
def activeFactors (Q:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
  classical
  exact (normalizedFactors Q).toFinset.filter
    (fun F => 0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
theorem activeFactors_spec (Q F:MvPolynomial (Fin 4) K)
    (hF:F∈activeFactors Q):
    Irreducible F∧F∣Q∧0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
  classical
  obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hF
  have hmem:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hm
  exact ⟨irreducible_of_normalized_factor F hmem,
    dvd_of_mem_normalizedFactors hmem,hp⟩
theorem exists_normalized_factor_of_map_zero
    {A:Type*} [CommRing A] [IsDomain A]
    (ψ:MvPolynomial (Fin 4) K →+*A)
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hzero:ψ Q=0):
    ∃ F∈normalizedFactors Q,ψ F=0:=by
  have hassoc:=Associated.map ψ (prod_normalizedFactors hQ)
  rw [hzero] at hassoc
  have hp:ψ (normalizedFactors Q).prod=0:=
    (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
theorem eq_C_of_all_degreeOf_zero (P:MvPolynomial (Fin 3) L)
    (h:∀ i,P.degreeOf i=0):P=MvPolynomial.C (P.coeff 0):=by
  classical
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
  intro d hd
  have hd0:d=0:=by
    ext i
    have hi:=MvPolynomial.monomial_le_degreeOf i hd
    rw [h i] at hi
    exact Nat.eq_zero_of_le_zero hi
  simp [hd0]
theorem pureX_nonvanishing (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (v:Fin 3 → L) (P:Polynomial K)
    (hpure:collectX K F=MvPolynomial.C P):
    MvPolynomial.eval v (surfaceMap φ F)≠0:=by
  have hP:P≠0:=by
    intro h
    apply hF
    apply (collectX K).injective
    simpa only [h,map_zero] using hpure
  have hφP:φ P≠0:=by
    intro h
    apply hP
    apply hφ
    simpa only [map_zero] using h
  change MvPolynomial.eval v (MvPolynomial.map φ (collectX K F))≠0
  rw [hpure,MvPolynomial.map_C,MvPolynomial.eval_C]
  exact hφP
theorem positive_seed_degree_of_surface_zero
    (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
    (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
    0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
  by_contra hn
  have hy:F.degreeOf 1 ≤ 0:=by omega
  have hr:F.degreeOf 2 ≤ 0:=by omega
  have hz:F.degreeOf 3 ≤ 0:=by omega
  have hc:=surfaceMap_separated_caps φ F 0 0 0 hy hr hz
  have hconst:surfaceMap φ F=MvPolynomial.C ((surfaceMap φ F).coeff 0):=by
    apply eq_C_of_all_degreeOf_zero
    intro i
    fin_cases i
    · exact Nat.eq_zero_of_le_zero hc.1
    · exact Nat.eq_zero_of_le_zero hc.2.1
    · exact Nat.eq_zero_of_le_zero hc.2.2
  have hvalue:=hzero
  rw [hconst,MvPolynomial.eval_C] at hvalue
  apply surfaceMap_ne_zero φ hφ F hF
  rw [hconst,hvalue,map_zero]
theorem exists_active_factor_of_surface_zero
    (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (v:Fin 3 → L)
    (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
    ∃ F∈activeFactors Q,MvPolynomial.eval v (surfaceMap φ F)=0:=by
  classical
  obtain ⟨F,hmem,hz⟩:=exists_normalized_factor_of_map_zero
    ((MvPolynomial.eval v).comp (surfaceMap φ)) Q hQ hzero
  have hF:=ne_zero_of_mem_normalizedFactors hmem
  have hpos:=positive_seed_degree_of_surface_zero φ hφ F hF v hz
  exact ⟨F,Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem,hpos⟩,hz⟩
theorem activeFactors_product_dvd (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
    (∏ F∈activeFactors Q,F)∣Q:=by
  classical
  apply (Finset.prod_dvd_prod_of_subset (activeFactors Q)
    (normalizedFactors Q).toFinset id (Finset.filter_subset _ _)).trans
  exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
theorem activeFactors_mem_box (Q F:MvPolynomial (Fin 4) K)
    (D w zcap s:ℕ) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K D w zcap s) (hF:F∈activeFactors Q):
    F∈globalCoefficientBox K D w zcap s:=
  ContactFactorCaps.mem_globalCoefficientBox_of_dvd F Q D w zcap s hQ
    (activeFactors_spec Q F hF).2.1 hbox
theorem activeFactors_degree_budgets (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
    (∑ F∈activeFactors Q,F.degreeOf (1:Fin 4)) ≤ Q.degreeOf 1∧
    (∑ F∈activeFactors Q,F.degreeOf (2:Fin 4)) ≤ Q.degreeOf 2∧
    (∑ F∈activeFactors Q,F.degreeOf (3:Fin 4)) ≤ Q.degreeOf 3:=
  ContactFactorCaps.separated_degree_budgets_of_prod_dvd (activeFactors Q) id Q hQ
    (activeFactors_product_dvd Q hQ)
theorem activeFactors_input_budgets (Q:MvPolynomial (Fin 4) K)
    (D w zcap s:ℕ) (hw:0 < w) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K D w zcap s):
    (∑ F∈activeFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
    (∑ F∈activeFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
    (∑ F∈activeFactors Q,F.degreeOf (3:Fin 4)) ≤ zcap:=
  ContactFactorCaps.separated_factor_caps_of_prod_dvd (activeFactors Q) id Q
    D w zcap s hw hQ hbox (activeFactors_product_dvd Q hQ)
theorem activeFactors_card_le (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
    (activeFactors Q).card ≤ Q.degreeOf 1+Q.degreeOf 2+Q.degreeOf 3:=by
  classical
  have hsum:(activeFactors Q).card ≤
      ∑ F∈activeFactors Q,(F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):=by
    calc
      (activeFactors Q).card=∑ _F∈activeFactors Q,(1:ℕ):=by simp
      _ ≤ _:=Finset.sum_le_sum fun F hF => (activeFactors_spec Q F hF).2.2
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  have hb:=activeFactors_degree_budgets Q hQ
  omega
theorem exists_active_irreducible_box_factor
    (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
    (Q:MvPolynomial (Fin 4) K) (D w zcap s:ℕ) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K D w zcap s)
    (v:Fin 3 → L) (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
    ∃ F∈activeFactors Q,Irreducible F∧F∣Q∧
      F∈globalCoefficientBox K D w zcap s∧
      MvPolynomial.eval v (surfaceMap φ F)=0:=by
  obtain ⟨F,hF,hz⟩:=exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
  have hs:=activeFactors_spec Q F hF
  exact ⟨F,hF,hs.1,hs.2.1,activeFactors_mem_box Q F D w zcap s hQ hbox hF,hz⟩
end
end ProximityPrize.SubmissionLower.ContactFactorCover
