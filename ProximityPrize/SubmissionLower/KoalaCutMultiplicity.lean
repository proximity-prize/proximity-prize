import ProximityPrize.SubmissionLower.PortLow6

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SplitCut.CutMultiplicity

noncomputable section
open MvPolynomial Filter
open K1_13_6_3_6 (quotientMul quotientMul_mk quotientMul_injective quotientMul_exact)
open K1_13_6_3_5 (boundaryWeight)
open private K1_13_6_3_6.colon_map_localization from ProximityPrize.SubmissionLower.Fast053

variable {F σ:Type} [Field F] [Finite σ]

def localLength (I P : Ideal (MvPolynomial σ F)) (hp : P.IsPrime) : ℕ∞ :=
  letI:=hp
  let L:=Localization.AtPrime P
  Module.length L (L ⧸ I.map (algebraMap _ L))

omit [Finite σ] in
theorem weight_eq_length (J P : Ideal (MvPolynomial σ F)) (hp : P.IsPrime) :
    boundaryWeight J P=(localLength J P hp).toNat:=by
  simp only [boundaryWeight,dite_eq_left hp,localLength]

omit [Finite σ] in
private theorem length_cyclic (I P : Ideal (MvPolynomial σ F)) (hp : P.IsPrime)
    (g : MvPolynomial σ F) : localLength I P hp =
      localLength (I.colon {g}) P hp+localLength (I ⊔ Ideal.span {g}) P hp:=by
  let _:P.IsPrime:=hp
  let L:=Localization.AtPrime P
  let r:=algebraMap (MvPolynomial σ F) L
  let J:=I.map r
  let a:=r g
  have h := Module.length_eq_add_of_exact (quotientMul J a)
    (Submodule.factor (le_sup_left:J≤J ⊔ Ideal.span {a}))
    (quotientMul_injective J a) (Submodule.factor_surjective le_sup_left)
    (quotientMul_exact J a)
  change Module.length L (L ⧸ I.map r) =
    Module.length L (L ⧸ (I.colon {g}).map r) +
      Module.length L (L ⧸ (I ⊔ Ideal.span {g}).map r)
  rw [K1_13_6_3_6.colon_map_localization P.primeCompl, Ideal.map_sup, Ideal.map_span,
    Set.image_singleton]
  exact h

omit [Finite σ] in
private theorem length_eq_zero_of_not_le {I P : Ideal (MvPolynomial σ F)} (hp : P.IsPrime)
    (h : ¬ I≤P):localLength I P hp=0:=by
  let _:P.IsPrime:=hp
  let L:=Localization.AtPrime P
  have htop : I.map (algebraMap (MvPolynomial σ F) L) = ⊤ := by
    by_contra ht
    exact h (Set.disjoint_compl_left_iff_subset.mp
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mp ht))
  change Module.length L (L ⧸ I.map (algebraMap (MvPolynomial σ F) L))=0
  simp [htop,Module.length_eq_zero]

omit [Finite σ] in
private theorem length_self (P : Ideal (MvPolynomial σ F)) (hp : P.IsPrime) :
    localLength P P hp=1:=by
  let _:P.IsPrime:=hp
  let L:=Localization.AtPrime P
  change Module.length L (L ⧸ P.map (algebraMap (MvPolynomial σ F) L))=1
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  have h : IsSimpleModule L (L ⧸ IsLocalRing.maximalIdeal L) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
  exact Module.length_eq_one _ _

private theorem exists_prime_colon (I : Ideal (MvPolynomial σ F)) (hI : I ≠ ⊤) :
    ∃ g:MvPolynomial σ F,g ∉ I ∧ (I.colon {g}).IsPrime:=by
  let _:=Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨A, hA, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
    (MvPolynomial σ F) (1:MvPolynomial σ F ⧸ I) one_ne_zero
  obtain ⟨hp,x,hx⟩:=isAssociatedPrime_iff.mp hA
  obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective x
  have heq : A = I.colon {g} := by
    ext a
    rw [hx,Submodule.mem_colon_singleton,Submodule.mem_colon_singleton,Submodule.mem_bot]
    change Ideal.Quotient.mk I a*Ideal.Quotient.mk I g=0↔a*g ∈ I
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [heq] at hp
  refine ⟨g,fun hg => hp.ne_top ?_,hp⟩
  simpa only [Submodule.colon_eq_top_iff_subset,Set.singleton_subset_iff,SetLike.mem_coe] using hg

private theorem hilbert_step (I : Ideal (MvPolynomial σ F)) (g : MvPolynomial σ F)
    (N:ℕ) (hN:g.totalDegree≤N) :
    affineHilbertFunction (I ⊔ Ideal.span {g}) N +
      affineHilbertFunction (I.colon {g}) (N - g.totalDegree)≤affineHilbertFunction I N:=by
  let J:=I ⊔ Ideal.span {g}
  let A:=I.colon {g}
  let q:=Ideal.Quotient.factorₐ F (show I≤J from le_sup_left)
  let cut : quotientDegreeLE I N →ₗ[F] quotientDegreeLE J N :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change q y.val ∈ _
      rw [← hpy]
      exact mk_mem_quotientDegreeLE hp
  have hcut : Function.Surjective cut := by
    intro y
    obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p,mk_mem_quotientDegreeLE hp⟩,Subtype.ext hpy⟩
  let mul:=(quotientMul I g).restrictScalars F
  let emb : quotientDegreeLE A (N - g.totalDegree) →ₗ[F] quotientDegreeLE I N :=
    (mul.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p,hp,hpy⟩:=mem_quotientDegreeLE.mp y.property
      change quotientMul I g y.val ∈ _
      rw [← hpy,quotientMul_mk]
      exact mk_mem_quotientDegreeLE ((totalDegree_mul p g).trans (by omega))
  have hemb (y : quotientDegreeLE A (N - g.totalDegree)) : emb y ∈ LinearMap.ker cut := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change q (quotientMul I g y.val)=0
    have hex:=LinearMap.exact_iff.mp (quotientMul_exact I g)
    have hm:=LinearMap.mem_range_self (quotientMul I g) y.val
    rw [← hex] at hm
    exact hm
  have hinj : Function.Injective (emb.codRestrict (LinearMap.ker cut) hemb) := by
    intro x y he
    exact Subtype.ext (quotientMul_injective I g (congrArg (fun z => z.val.val) he))
  have hker:=LinearMap.finrank_le_finrank_of_injective hinj
  have hrank:=cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut,finrank_top] at hrank
  change affineHilbertFunction J N+affineHilbertFunction A (N - g.totalDegree)≤_
  unfold affineHilbertFunction
  omega

private theorem hilbert_coeff_step (I : Ideal (MvPolynomial σ F)) (g : MvPolynomial σ F)
    (d:ℕ) (hI:(affineHilbertPolynomial I).natDegree≤d) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {g})).coeff d +
      (affineHilbertPolynomial (I.colon {g})).coeff d≤(affineHilbertPolynomial I).coeff d:=by
  let J:=I ⊔ Ideal.span {g}
  let A:=I.colon {g}
  let b:=g.totalDegree
  let S:=affineHilbertPolynomial J+Polynomial.taylor (-(b:ℚ)) (affineHilbertPolynomial A)
  have hA:=(natDegree_affineHilbertPolynomial_le_of_le (Ideal.le_colon:I≤A)).trans hI
  have hJ:=(natDegree_affineHilbertPolynomial_le_of_le (le_sup_left:I≤J)).trans hI
  have hS : S.natDegree ≤ d :=
    Polynomial.natDegree_add_le_of_degree_le hJ (by rwa [Polynomial.natDegree_taylor])
  have hc : S.coeff d ≤ (affineHilbertPolynomial I).coeff d := by
    refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hS hI ?_
    obtain ⟨N₀,h₀⟩:=exists_eval_affineHilbertPolynomial A
    filter_upwards [eventually_eval_affineHilbertPolynomial J, eventually_eval_affineHilbertPolynomial I,
      eventually_ge_atTop (N₀+b)] with N h₁ h₂ hN
    have hb:b≤N:=by omega
    simp only [S, Polynomial.eval_add, Polynomial.taylor_eval, h₁, h₂, ← sub_eq_add_neg,
      ← Nat.cast_sub hb,h₀ (N - b) (by omega:N₀≤N - b)]
    exact_mod_cast hilbert_step I g N hb
  change (affineHilbertPolynomial A).natDegree≤d at hA
  dsimp only [S] at hc
  rw [Polynomial.coeff_add,Polynomial.coeff_taylor_of_natDegree_le _ hA] at hc
  exact hc

/-- The leading Hilbert coefficient pays the generic local length of each minimal
    component, including repeated components of a principal section. -/
theorem coefficient_budget (J : Ideal (MvPolynomial σ F)) (d : ℕ)
    (hd:(affineHilbertPolynomial J).natDegree≤d) :
    (∀ P (hp : J.IsMinimalPrime P), localLength J P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ J.minimalPrimesFinset,
        (boundaryWeight J P:ℚ)*(affineHilbertPolynomial P).coeff d ≤
        (affineHilbertPolynomial J).coeff d:=by
  classical
  let T:=J.minimalPrimesFinset
  suffices aux : ∀ I : Ideal (MvPolynomial σ F), J ≤ I →
      (∀ P (hp:J.IsMinimalPrime P),localLength I P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ T, (boundaryWeight I P : ℚ) * (affineHilbertPolynomial P).coeff d ≤
        (affineHilbertPolynomial I).coeff d from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α:=Ideal (MvPolynomial σ F))) with
  | h I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      have hz (P : Ideal (MvPolynomial σ F)) (hp : P.IsPrime) : localLength ⊤ P hp = 0 :=
        length_eq_zero_of_not_le hp (by simpa using hp.ne_top)
      exact ⟨fun P hp => by simp [hz P hp.isPrime], by
        refine le_of_eq ?_
        simp only [affineHilbertPolynomial_top,Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro P hP
        have hp:=(Ideal.mem_minimalPrimesFinset.mp hP).isPrime
        simp [weight_eq_length _ _ hp,hz P hp]⟩
    obtain ⟨g,hg,hprime⟩:=exists_prime_colon I hI
    let A:=I.colon {g}
    let B:=I ⊔ Ideal.span {g}
    have hIA:I≤A:=Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨hfin,hbudget⟩:=ih B hIB (hJI.trans hIB.le)
    have hstep (P : Ideal (MvPolynomial σ F)) (hp : J.IsMinimalPrime P) :
        localLength I P hp.isPrime=localLength A P hp.isPrime+localLength B P hp.isPrime :=
      length_cyclic I P hp.isPrime g
    have hterm (P : Ideal (MvPolynomial σ F)) (hp : J.IsMinimalPrime P) :
        localLength A P hp.isPrime=if P=A then 1 else 0:=by
      split_ifs with h
      · subst P
        exact length_self A hp.isPrime
      · exact length_eq_zero_of_not_le hp.isPrime
          (fun hAP => h (le_antisymm (hp.2 ⟨hprime,hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P : Ideal (MvPolynomial σ F)) (hp : J.IsMinimalPrime P) :
        localLength A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P : Ideal (MvPolynomial σ F)) (hP : P ∈ T) :
        (boundaryWeight I P:ℚ)=(boundaryWeight B P:ℚ)+(if P=A then 1 else 0):=by
      have hp:=Ideal.mem_minimalPrimesFinset.mp hP
      have hw (L : Ideal (MvPolynomial σ F)) : boundaryWeight L P = (localLength L P hp.isPrime).toNat :=
        weight_eq_length _ _ hp.isPrime
      rw [hw,hw,hstep P hp,ENat.toNat_add (hfinite P hp) (hfin P hp),hterm P hp,Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim:=(natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp => by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp,hfin P hp⟩, ?_⟩
    calc
      _ = (∑ P ∈ T, (boundaryWeight B P : ℚ) * (affineHilbertPolynomial P).coeff d) +
          (if A ∈ T then (affineHilbertPolynomial A).coeff d else 0):=by
        rw [← Finset.sum_ite_eq' T A (fun P => (affineHilbertPolynomial P).coeff d),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP,add_mul,ite_mul,one_mul,zero_mul]
      _ ≤ (affineHilbertPolynomial B).coeff d + (affineHilbertPolynomial A).coeff d := by
        apply add_le_add hbudget
        split_ifs
        · exact le_rfl
        · exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
            ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdim)
            (eventually_eval_affineHilbertPolynomial_nonneg A)
      _≤_:=hilbert_coeff_step I g d hdim

omit [Finite σ] in
theorem weight_pos {J P : Ideal (MvPolynomial σ F)} [P.IsPrime] (hJP : J ≤ P)
    (hfin:localLength J P ‹P.IsPrime› ≠ ⊤):0 < boundaryWeight J P:=by
  let L:=Localization.AtPrime P
  have htop : J.map (algebraMap (MvPolynomial σ F) L) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L J).mpr
      (Set.disjoint_compl_left_iff_subset.mpr hJP)
  have:=Ideal.Quotient.nontrivial_iff.mpr htop
  rw [weight_eq_length J P ‹P.IsPrime›]
  exact ENat.toNat_pos (Module.length_pos (R:=L)).ne' hfin

omit [Finite σ] in
/-- Length one gives the localization hypothesis in `stable_of_simple_cut`. -/
theorem simple_saturation {J P : Ideal (MvPolynomial σ F)} [P.IsPrime]
    (hfin:localLength J P ‹P.IsPrime› ≠ ⊤) (h:boundaryWeight J P=1) :
    ∀ x ∈ P, ∃ t ∉ P,t*x ∈ J:=by
  let L:=Localization.AtPrime P
  let r:=algebraMap (MvPolynomial σ F) L
  have hlen : localLength J P ‹P.IsPrime› = 1 := by
    have he:=ENat.natCast_toNat hfin
    rw [← weight_eq_length J P ‹P.IsPrime›, h,Nat.cast_one] at he
    exact he.symm
  unfold localLength at hlen
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, ← Localization.AtPrime.map_eq_maximalIdeal] at hlen
  intro x hx
  have hx' : r x ∈ J.map r := by
    rw [show J.map r=P.map r from hlen]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨t,htp,ht⟩:=(IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L J x).mp hx'
  exact ⟨t,htp,ht⟩

end
end SplitCut.CutMultiplicity

#print axioms SplitCut.CutMultiplicity.coefficient_budget
#print axioms SplitCut.CutMultiplicity.simple_saturation
