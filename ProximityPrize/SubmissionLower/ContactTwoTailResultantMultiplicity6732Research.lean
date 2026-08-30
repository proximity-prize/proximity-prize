import ProximityPrize.SubmissionLower.PlaneResultantPointCount
namespace ProximityPrize.SubmissionLower.ContactTwoTailResultantMultiplicity6732Research
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
variable {K:Type} [Field K] [DecidableEq K]
theorem sum_pairwise_power_factor_degrees_le
    {I:Type*} [Fintype I]
    (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
    (hR:R≠0)
    (hqMonic:∀ i,(q i).Monic)
    (hqCoprime:Pairwise fun i j↦IsCoprime (q i) (q j))
    (hpow:∀ i,q i^multiplicity i∣R):
    (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
  classical
  have hpowersCoprime:Pairwise fun i j↦
      IsCoprime ((q i)^multiplicity i) ((q j)^multiplicity j):=by
    intro i j hij
    exact (hqCoprime hij).pow
  have hprodDvd:(∏ i,(q i)^multiplicity i)∣R:=
    Fintype.prod_dvd_of_coprime hpowersCoprime hpow
  have hdegree:(∏ i,(q i)^multiplicity i).natDegree=
      ∑ i,multiplicity i*(q i).natDegree:=by
    rw [Polynomial.natDegree_prod_of_monic
      (s:=Finset.univ) (f:=fun i↦(q i)^multiplicity i)
      (fun i _↦(hqMonic i).pow _)]
    apply Finset.sum_congr rfl
    intro i _
    exact Polynomial.natDegree_pow (q i) (multiplicity i)
  rw [←hdegree]
  exact Polynomial.natDegree_le_of_dvd hprodDvd hR
theorem sum_power_factor_degrees_le
    {I:Type*} [Fintype I]
    (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
    (hR:R≠0)
    (hqIrreducible:∀ i,Irreducible (q i))
    (hqMonic:∀ i,(q i).Monic)
    (hqInjective:Function.Injective q)
    (hpow:∀ i,q i^multiplicity i∣R):
    (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
  apply sum_pairwise_power_factor_degrees_le R q multiplicity hR hqMonic
  · intro i j hij
    apply (hqIrreducible i).coprime_iff_not_dvd.mpr
    intro hdvd
    have hassociated:=
      (hqIrreducible i).associated_of_dvd (hqIrreducible j) hdvd
    have heq:q i=q j:=Polynomial.eq_of_monic_of_associated
      (hqMonic i) (hqMonic j) hassociated
    exact hij (hqInjective heq)
  · exact hpow
theorem sum_power_factor_degrees_le_resultant_bidegree
    {I:Type*} [Fintype I]
    (P Q:Polynomial (Polynomial K)) (m n:ℕ)
    (q:I → Polynomial K) (multiplicity:I → ℕ)
    (hresultant:Polynomial.resultant P Q m n≠0)
    (hqIrreducible:∀ i,Irreducible (q i))
    (hqMonic:∀ i,(q i).Monic)
    (hqInjective:Function.Injective q)
    (hpow:∀ i,
      q i^multiplicity i∣Polynomial.resultant P Q m n):
    (∑ i,multiplicity i*(q i).natDegree) ≤
      n*Polynomial.Bivariate.degreeX P+
        m*Polynomial.Bivariate.degreeX Q:=by
  exact (sum_power_factor_degrees_le
    (Polynomial.resultant P Q m n) q multiplicity hresultant
      hqIrreducible hqMonic hqInjective hpow).trans
    (bivariate_resultant_natDegree_le (F:=K) P Q m n)
theorem sum_grouped_power_factor_degrees_le
    {I:Type*} [Fintype I]
    (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
    (hR:R≠0)
    (hqIrreducible:∀ i,Irreducible (q i))
    (hqMonic:∀ i,(q i).Monic)
    (hpow:∀ f∈Finset.univ.image q,
      f^(∑ i with q i=f,multiplicity i)∣R):
    (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
  classical
  let roots:Finset (Polynomial K):=Finset.univ.image q
  let grouped:roots → ℕ:=fun f↦∑ i with q i=f.1,multiplicity i
  have hrootsMonic:∀ f:roots,f.1.Monic:=by
    intro f
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
    simpa only [hi] using hqMonic i
  have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
    intro f
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
    simpa only [hi] using hqIrreducible i
  have hrootsPow:∀ f:roots,f.1^grouped f∣R:=by
    intro f
    exact hpow f.1 f.2
  have hbound:=sum_power_factor_degrees_le R
    (fun f:roots↦f.1) grouped hR hrootsIrreducible hrootsMonic
      Subtype.val_injective hrootsPow
  have hregroup:
      (∑ f:roots,grouped f*f.1.natDegree)=
        ∑ i,multiplicity i*(q i).natDegree:=by
    change (∑ f:roots,
      (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=_
    have hattach:
        (∑ f:roots,
          (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=
        ∑ f∈roots,
          (∑ i with q i=f,multiplicity i)*f.natDegree:=by
      rw [show (Finset.univ:Finset roots)=roots.attach from
        Finset.univ_eq_attach roots]
      exact Finset.sum_attach roots (fun f:Polynomial K↦
        (∑ i with q i=f,multiplicity i)*f.natDegree)
    rw [hattach]
    simp_rw [Finset.sum_mul]
    calc
      (∑ f∈roots,∑ i with q i=f,
          multiplicity i*f.natDegree)=
          ∑ f∈roots,∑ i with q i=f,
            multiplicity i*(q i).natDegree:=by
        apply Finset.sum_congr rfl
        intro f _
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _=∑ i∈(Finset.univ:Finset I),
          multiplicity i*(q i).natDegree:=
        Finset.sum_fiberwise_of_maps_to
          (s:=Finset.univ) (t:=roots) (g:=q)
          (fun i _↦Finset.mem_image_of_mem q (Finset.mem_univ i)) _
      _=_:=by rfl
  rw [←hregroup]
  exact hbound
end
end ProximityPrize.SubmissionLower.ContactTwoTailResultantMultiplicity6732Research
