import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
namespace ProximityPrize.SubmissionLower.ContactImplicitContactLift
open ContactFactorCaps ContactFactorCover ContactSingularDegreeBounds
open ContactRegularFactorGate ContactTaylorNumerators ContactGenericSurface
open ContactTranslation ContactPolynomialSolutions
noncomputable section
variable {K:Type*} [Field K]
def implicitLift (A:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
  MvPolynomial.pderiv (0:Fin 4) A+
    MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A
theorem implicitLift_R_derivative (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0):
    MvPolynomial.pderiv (2:Fin 4) (implicitLift A)=MvPolynomial.pderiv (1:Fin 4) A:=by
  have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
    pderiv_degree_bound 0 2 A 0 (by omega)
  have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
    pderiv_degree_bound 1 2 A 0 (by omega)
  have hx0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hX
  have hy0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hY
  simp only [implicitLift,map_add,MvPolynomial.pderiv_mul,hx0,hy0,
    MvPolynomial.pderiv_X_self,one_mul,mul_zero,add_zero,zero_add]
theorem implicitLift_nonzero (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
    implicitLift A≠0:=by
  intro h
  apply hY
  rw [←implicitLift_R_derivative A hR,h,map_zero]
theorem implicitLift_R_degree_le (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0):(implicitLift A).degreeOf 2 ≤ 1:=by
  have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
    pderiv_degree_bound 0 2 A 0 (by omega)
  have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
    pderiv_degree_bound 1 2 A 0 (by omega)
  have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf 2 ≤ 1:=by simp
  have hm:=degree_mul_bound (2:Fin 4) hvar hY
  exact degree_add_bound (2:Fin 4) (hX.trans (by omega)) (by simpa using hm)
theorem implicitLift_other_degree_le (A:MvPolynomial (Fin 4) K)
    (i:Fin 4) (hi:i≠2):(implicitLift A).degreeOf i ≤ A.degreeOf i:=by
  have hX:=pderiv_degree_bound 0 i A (A.degreeOf i) le_rfl
  have hY:=pderiv_degree_bound 1 i A (A.degreeOf i) le_rfl
  have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf i ≤ 0:=by
    simp [MvPolynomial.degreeOf_X,hi]
  have hm:=degree_mul_bound i hvar hY
  exact degree_add_bound i hX (by simpa using hm)
theorem implicitLift_solution (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0) (P:Polynomial K) (γ:K)
    (hA:specialization K P γ A=0):specialization K P γ (implicitLift A)=0:=by
  have hchain:=derivative_specialization K P γ A
  rw [hA,Polynomial.derivative_zero,pderiv_zero_of_degree_zero (2:Fin 4) A hR,
    map_zero,mul_zero,add_zero] at hchain
  have hspec:specialization K P γ (implicitLift A)=
      specialization K P γ (MvPolynomial.pderiv (0:Fin 4) A)+
        P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A):=by
    simp [implicitLift,specialization]
  exact hspec.trans hchain.symm
theorem weighted_mul_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
    MvPolynomial.weightedTotalDegree weights (P*Q) ≤
      MvPolynomial.weightedTotalDegree weights P+MvPolynomial.weightedTotalDegree weights Q:=by
  rw [←degree_weightedLift,map_mul]
  simpa only [degree_weightedLift] using
    (MvPolynomial.degreeOf_mul_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_add_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
    MvPolynomial.weightedTotalDegree weights (P+Q) ≤
      max (MvPolynomial.weightedTotalDegree weights P) (MvPolynomial.weightedTotalDegree weights Q):=by
  rw [←degree_weightedLift,map_add]
  simpa only [degree_weightedLift] using
    (MvPolynomial.degreeOf_add_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_X (weights:Fin 4 → ℕ) (i:Fin 4):
    MvPolynomial.weightedTotalDegree weights (MvPolynomial.X i:MvPolynomial (Fin 4) K)=weights i:=by
  simp [MvPolynomial.weightedTotalDegree,MvPolynomial.support_X,Finsupp.weight_single]
theorem pderiv_weight_sub_bound (weights:Fin 4 → ℕ)
    (A:MvPolynomial (Fin 4) K) (i:Fin 4) (B:ℕ)
    (hA:MvPolynomial.weightedTotalDegree weights A ≤ B):
    MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i A) ≤ B-weights i:=by
  apply (weightedTotalDegree_le_iff weights _ _).mpr
  intro d hd
  have hh:=(MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i A d hd)).trans hA
  simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
  omega
theorem implicitLift_seed_weight_le (A:MvPolynomial (Fin 4) K):
    MvPolynomial.weightedTotalDegree seedWeights (implicitLift A) ≤
      MvPolynomial.weightedTotalDegree seedWeights A:=by
  have hX:=pderiv_weight_le seedWeights A 0
  have hY:=pderiv_weight_le seedWeights A 1
  have hvar:MvPolynomial.weightedTotalDegree seedWeights
      (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=0:=by
    rw [weighted_X]
    simp [seedWeights]
  have hm:=weighted_mul_le seedWeights (MvPolynomial.X (2:Fin 4))
    (MvPolynomial.pderiv (1:Fin 4) A)
  rw [hvar,zero_add] at hm
  exact (weighted_add_le seedWeights _ _).trans (max_le hX (hm.trans hY))
theorem implicitLift_contact_weight_le
    (A:MvPolynomial (Fin 4) K) (D w:ℕ) (hw:1 ≤ w) (hDw:w < D)
    (hA:MvPolynomial.weightedTotalDegree (contactWeights w) A ≤ D-1):
    MvPolynomial.weightedTotalDegree (contactWeights w) (implicitLift A) ≤ D-2:=by
  have hX:=pderiv_weight_sub_bound (contactWeights w) A 0 (D-1) hA
  have hY:=pderiv_weight_sub_bound (contactWeights w) A 1 (D-1) hA
  change MvPolynomial.weightedTotalDegree (contactWeights w)
    (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-1-1 at hX
  change MvPolynomial.weightedTotalDegree (contactWeights w)
    (MvPolynomial.pderiv (1:Fin 4) A) ≤ D-1-w at hY
  have hx:MvPolynomial.weightedTotalDegree (contactWeights w)
      (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-2:=by omega
  have hvar:MvPolynomial.weightedTotalDegree (contactWeights w)
      (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=w-1:=by
    rw [weighted_X]
    simp [contactWeights]
  have hm:=weighted_mul_le (contactWeights w) (MvPolynomial.X (2:Fin 4))
    (MvPolynomial.pderiv (1:Fin 4) A)
  rw [hvar] at hm
  have hm':MvPolynomial.weightedTotalDegree (contactWeights w)
      (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A) ≤ D-2:=by omega
  exact (weighted_add_le (contactWeights w) _ _).trans (max_le hx hm')
theorem implicitLift_mem_box
    (A:MvPolynomial (Fin 4) K) (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
    (hbox:A∈ContactInterpolation.globalCoefficientBox K D w L 0):
    implicitLift A∈ContactInterpolation.globalCoefficientBox K D w L 1:=by
  have hD:0 < D:=by omega
  have hcaps:=(mem_globalCoefficientBox_iff A D w L 0 hD).mp hbox
  have hR:A.degreeOf 2=0:=by
    apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hs:=(implicitLift_seed_weight_le A).trans hcaps.1
  have hc:=implicitLift_contact_weight_le A D w hw hDw hcaps.2.2
  have hr:=implicitLift_R_degree_le A hR
  intro d hd
  have hseed:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hs
  have hcontact:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
  have hslope:=(MvPolynomial.monomial_le_degreeOf (f:=implicitLift A) (2:Fin 4) hd).trans hr
  rw [seed_weight] at hseed
  rw [contact_weight] at hcontact
  exact ⟨hseed,hslope,by omega⟩
def positiveRFactors (F:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
  classical
  exact (activeFactors F).filter (fun G => 0 < G.degreeOf 2)
theorem positiveRFactors_spec (F G:MvPolynomial (Fin 4) K)
    (hG:G∈positiveRFactors F):Irreducible G∧G∣F∧0 < G.degreeOf 2:=by
  classical
  obtain ⟨hmem,hpos⟩:=Finset.mem_filter.mp hG
  have hh:=activeFactors_spec F G hmem
  exact ⟨hh.1,hh.2.1,hpos⟩
theorem positiveRFactors_product_dvd (F:MvPolynomial (Fin 4) K) (hF:F≠0):
    (∏ G∈positiveRFactors F,G)∣F:=by
  classical
  exact (Finset.prod_dvd_prod_of_subset (positiveRFactors F) (activeFactors F) id
    (Finset.filter_subset _ _)).trans (activeFactors_product_dvd F hF)
theorem factor_derivative_regular_at_zero {B:Type*} [CommRing B]
    (ψ:MvPolynomial (Fin 4) K →+*B) (F G:MvPolynomial (Fin 4) K)
    (hdiv:G∣F) (hG:ψ G=0)
    (hregular:ψ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    ψ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
  intro hz
  obtain ⟨T,hT⟩:=hdiv
  apply hregular
  rw [hT,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,hG,
    zero_mul,zero_mul,zero_add]
theorem lift_positive_factor_budgets (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
    (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
      (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
      (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
  have hF:=implicitLift_nonzero A hR hY
  have hprod:=positiveRFactors_product_dvd (implicitLift A) hF
  have hb:=ContactFactorCaps.sum_degreeOf_le_of_prod_dvd
    (positiveRFactors (implicitLift A)) id (implicitLift A) hF hprod
  exact ⟨(hb 2).trans (implicitLift_R_degree_le A hR),
    (hb 1).trans (implicitLift_other_degree_le A 1 (by decide)),
    (hb 3).trans (implicitLift_other_degree_le A 3 (by decide))⟩
theorem lift_positive_factor_card_le_one (A:MvPolynomial (Fin 4) K)
    (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
    (positiveRFactors (implicitLift A)).card ≤ 1:=by
  classical
  have hc:(positiveRFactors (implicitLift A)).card ≤
      ∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4):=by
    calc
      _=∑ _G∈positiveRFactors (implicitLift A),(1:ℕ):=by simp
      _ ≤ _:=Finset.sum_le_sum fun G hG => (positiveRFactors_spec _ G hG).2.2
  exact hc.trans (lift_positive_factor_budgets A hR hY).1
section SurfacePoints
variable {T:Type*} [Field T]
theorem exists_regular_lift_factor_at_surface
    (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
    (A:MvPolynomial (Fin 4) K) (hA:A≠0) (hR:A.degreeOf 2=0)
    (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0)
    (hregular:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0):
    ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G∣implicitLift A∧
      G.degreeOf 2=1∧MvPolynomial.eval v (surfaceMap φ G)=0∧
      MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) G))≠0∧¬ G∣A:=by
  classical
  let ψ:MvPolynomial (Fin 4) K →+*T:=(MvPolynomial.eval v).comp (surfaceMap φ)
  have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
    intro hz
    apply hregular
    rw [hz,map_zero,map_zero]
  have hF:=implicitLift_nonzero A hR hY
  obtain ⟨G,hG,hz⟩:=exists_active_factor_of_surface_zero φ hφ (implicitLift A) hF v hzero
  have hspec:=activeFactors_spec (implicitLift A) G hG
  have hFregular:ψ (MvPolynomial.pderiv (2:Fin 4) (implicitLift A))≠0:=by
    rw [implicitLift_R_derivative A hR]
    exact hregular
  have hGreg:=factor_derivative_regular_at_zero ψ (implicitLift A) G hspec.2.1 hz hFregular
  have hpos:0 < G.degreeOf 2:=by
    apply Nat.pos_of_ne_zero
    intro hn
    apply hGreg
    rw [pderiv_zero_of_degree_zero (2:Fin 4) G hn,map_zero]
  have hdeg:G.degreeOf 2=1:=by
    have hh:=(ContactFactorCaps.degreeOf_le_of_dvd (2:Fin 4) G (implicitLift A)
      hspec.2.1 hF).trans (implicitLift_R_degree_le A hR)
    omega
  have hproper:¬ G∣A:=by
    intro hd
    have hh:=ContactFactorCaps.degreeOf_le_of_dvd (2:Fin 4) G A hd hA
    omega
  exact ⟨G,Finset.mem_filter.mpr ⟨hG,hpos⟩,hspec.1,hspec.2.1,hdeg,hz,hGreg,hproper⟩
end SurfacePoints
theorem exists_regular_lift_factor_of_solution
    (A:MvPolynomial (Fin 4) K) (hA:A≠0) (P:Polynomial K) (γ:K)
    (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
    (hbox:A∈ContactInterpolation.globalCoefficientBox K D w L 0)
    (hsolution:specialization K P γ A=0)
    (hregular:specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0):
    ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G.degreeOf 2=1∧
      G∈ContactInterpolation.globalCoefficientBox K D w L 1∧
      specialization K P γ G=0∧
      specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0∧¬ G∣A:=by
  have hR:A.degreeOf 2=0:=by
    apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hFsolution:=implicitLift_solution A hR P γ hsolution
  let φ:=ContactGenericInitialPoint.polynomialEmbedding K
  let v:Fin 3 → ContactGenericInitialPoint.GenericField K:=
    fun i => ContactGenericInitialPoint.initialPoint K P γ i.succ
  have hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0:=by
    have hh:=(ContactGeometricFirstTail.actual_generic_initial_zero_iff K P γ (implicitLift A)).mpr hFsolution
    simpa only [ContactGeometricFirstTail.canonical_geometricSurfaceMap] using hh
  have hreg:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
    intro hz
    apply hregular
    apply (ContactGeometricFirstTail.actual_generic_initial_zero_iff K P γ _).mp
    simpa only [ContactGeometricFirstTail.canonical_geometricSurfaceMap] using hz
  obtain ⟨G,hG,hi,hd,hdeg,hpoint,hGreg,hproper⟩:=
    exists_regular_lift_factor_at_surface φ (ContactGenericInitialPoint.polynomialEmbedding_injective K)
      A hA hR v hzero hreg
  have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
    intro hz
    exact hregular (by rw [hz,map_zero])
  have hGbox:=ContactFactorCaps.mem_globalCoefficientBox_of_dvd G (implicitLift A)
    D w L 1 (implicitLift_nonzero A hR hY) hd (implicitLift_mem_box A D w L hw hDw hbox)
  have hGsol:specialization K P γ G=0:=by
    apply (ContactGeometricFirstTail.actual_generic_initial_zero_iff K P γ G).mp
    simpa only [ContactGeometricFirstTail.canonical_geometricSurfaceMap] using hpoint
  have hGregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
    intro hz
    apply hGreg
    have hh:=(ContactGeometricFirstTail.actual_generic_initial_zero_iff K P γ _).mpr hz
    simpa only [ContactGeometricFirstTail.canonical_geometricSurfaceMap] using hh
  exact ⟨G,hG,hi,hdeg,hGbox,hGsol,hGregular,hproper⟩
end
end ProximityPrize.SubmissionLower.ContactImplicitContactLift
