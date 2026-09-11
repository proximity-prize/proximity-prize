import ProximityPrize.SubmissionLower.Part.F005_00
section Compact_PackedLegacyCore2
section PackedLegacy_ContactOrderBridge
namespace ProximityPrize.SubmissionLower.ContactOrderBridge
open scoped BigOperators Pointwise
open RCN081 RCN119 RCN100 RCN122
noncomputable section
section KernelBridge
variable (K:Type*) [Field K]

theorem diagonalAtLeast_iff_coeff (m:ℕ) (Q:Poly4 K) :
    AtLeast diagonalWeights m Q ↔
      ∀ (r:ℕ) (d:Fin 3 →₀ ℕ), r + d 0 < m →
        MvPolynomial.coeff d ((MvPolynomial.finSuccEquiv K 3 Q).coeff r) = 0:=by
  classical
  constructor
  · intro h r d hsmall
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw:=h (Finsupp.cons r d) (MvPolynomial.mem_support_iff.mpr hc)
    have hcons:(Finsupp.cons r d) (1:Fin 4) = d 0:=rfl
    rw [weight_fin4] at hw
    simp [diagonalWeights, hcons] at hw
    omega
  · intro h d hd
    have hweight:Finsupp.weight diagonalWeights d = d 0 + d 1:=by
      rw [weight_fin4]
      simp [diagonalWeights]
    by_contra hsmall
    have hlt:d 0 + d.tail 0 < m:=by
      simp only [Finsupp.tail_apply]
      change d 0 + d 1 < m
      omega
    have hz:=h (d 0) d.tail hlt
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hz
    have he:Finsupp.cons (d 0) d.tail = d:=by
      ext i
      fin_cases i <;> simp [Finsupp.tail_apply]
    rw [he] at hz
    exact MvPolynomial.mem_support_iff.mp hd hz
theorem contactAtLeast_iff_block_divisibility (x u₀ u₁:K) (m:ℕ) (Q:Poly4 K) :
    ContactAtLeast K x u₀ u₁ m Q ↔
      ∀ r:ℕ, slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u₀ u₁ Q).coeff r:=by
  change AtLeast localWeights m (localize K x u₀ u₁ Q) ↔ _
  rw [← atLeast_contactBlowup_iff K m (localize K x u₀ u₁ Q), diagonalAtLeast_iff_coeff]
  simp only [collected_contactBlowup_localize, Polynomial.coeff_map]
  constructor
  · intro h r
    apply (contactJet_eq_zero_iff K (m - r) _).mp
    apply (contactJet_eq_zero_iff_coeff K (m - r) _).mpr
    intro d hd
    exact h r d (by omega)
  · intro h r d hd
    have hjet:=(contactJet_eq_zero_iff K (m - r) _).mpr (h r)
    exact (contactJet_eq_zero_iff_coeff K (m - r) _).mp hjet d (by omega)
theorem contactAtLeast_of_mem_kernel {I:Type*} [Fintype I]
    (D w L s m:ℕ) (nodes u₀ u₁:I → K)
    (a:CoefficientIndex D w L s → K)
    (ha:a ∈ LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)) (i:I) :
    ContactAtLeast K (nodes i) (u₀ i) (u₁ i) m (reconstruct K D w L s a):=by
  apply (contactAtLeast_iff_block_divisibility K (nodes i) (u₀ i) (u₁ i) m _).mpr
  exact RCN101.translated_contact_of_mem_ker
    K D w L s m nodes u₀ u₁ a ha i
def slopeDiagonal:Poly K →ₐ[K] Poly K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 0, MvPolynomial.X 2]
theorem monomial_fin3 (d:Fin 3 →₀ ℕ) (a:K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 *
        MvPolynomial.X 2 ^ d 2:=by
  have hd:d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2):=by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]
theorem slopeDiagonal_fixed (P:Poly K) (hP:∀ d ∈ P.support, d 1 = 0) :
    slopeDiagonal K P = P:=by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_fin3]
  simp [slopeDiagonal, hP d hd]
@[simp] theorem slopeDiagonal_slopeDifference :
    slopeDiagonal K (slopeDifference K) = 0:=by
  simp [slopeDiagonal, slopeDifference]
end KernelBridge
end
end ProximityPrize.SubmissionLower.ContactOrderBridge
end PackedLegacy_ContactOrderBridge

/-! Packed from ProximityPrize.SubmissionLower.CH. -/
section PackedLegacy_CH
namespace ProximityPrize.SubmissionLower.RCN324
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
private theorem prime_dvd_factorial:∀ {n p:ℕ},p.Prime → (p∣n.factorial ↔ p ≤ n)
 | 0,_,hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp => by
     rw [Nat.factorial_succ,hp.dvd_mul,prime_dvd_factorial hp]
     exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h => (_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
theorem derivation_pow_mul (D:Derivation K R R) (pi u:R) (mu:ℕ)
   (hmu:1 ≤ mu):
   D (pi^mu*u)=
     pi^(mu-1)*((mu:R)*u*D pi+pi*D u):=by
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_pow_mul (D:Derivation K R R) (pi u a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a):
   D (pi^mu*u)=pi^mu*((mu:R)*a*u+D u):=by
 rw [derivation_pow_mul D pi u mu hmu,htangent]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_preserves_divisibility (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   pi^mu∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [tangent_pow_mul D pi u a mu hmu htangent]
 exact dvd_mul_right _ _
theorem iterate_pow_mul_expansion (D:Derivation K R R) (pi u:R)
   (mu r:ℕ) (hr:r ≤ mu):
   ∃ error:R,
     (D:R → R)^[r] (pi^mu*u)=
       (mu.descFactorial r:R)*pi^(mu-r)*u*(D pi)^r+
         pi^(mu-r+1)*error:=by
 induction r with
 | zero =>
     refine ⟨0,?_⟩
     simp
 | succ r ih =>
     have hr0:r ≤ mu:=le_trans (Nat.le_succ r) hr
     obtain ⟨error,herror⟩:=ih hr0
     obtain ⟨k,hk⟩:∃ k,mu-r=k+1:=by
       have hpos:0 < mu-r:=Nat.sub_pos_of_lt (Nat.lt_of_succ_le hr)
       exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
     have hnext:mu-(r+1)=k:=by omega
     let q:=D pi
     let nextError:R:=
       (mu.descFactorial r:R)*D u*q^r+
       (mu.descFactorial r:R)*u*(r:R)*q^(r-1)*D q+
       (k+2:R)*q*error+pi*D error
     refine ⟨nextError,?_⟩
     rw [Function.iterate_succ_apply',herror,map_add]
     simp only [D.leibniz,Derivation.leibniz_pow,D.map_natCast,
       nsmul_eq_mul,smul_eq_mul]
     rw [hk,hnext,Nat.descFactorial_succ]
     have hmur:mu-r=k+1:=hk
     push_cast [hmur]
     dsimp only [q,nextError]
     ring
theorem isUnit_add_of_isUnit_of_not_isUnit [IsLocalRing R]
   {a b:R} (ha:IsUnit a) (hb:¬ IsUnit b):IsUnit (a+b):=by
 by_contra hab
 have hnb:¬ IsUnit (-b):=by simpa using hb
 have hs:=IsLocalRing.nonunits_add hab hnb
 apply hs
 simpa [add_assoc] using ha
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem addVal_iterate_eq_sub_of_transverse
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu < p) (hr:r ≤ mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R → R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [prime_dvd_factorial hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R → R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one
   [IsDomain R] [IsRegularLocalRing R] (hdim:ringKrullDim R=1):
   IsDiscreteValuationRing R:=by
 have hfin':=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
   (inferInstance:IsRegularLocalRing R)
 rw [hdim] at hfin'
 have hfin:Module.finrank (ResidueField R) (CotangentSpace R)=1:=by
   exact_mod_cast hfin'
 exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
end ProximityPrize.SubmissionLower.RCN324
end PackedLegacy_CH

/-! Packed from ProximityPrize.SubmissionLower.BI. -/
section PackedLegacy_BI
namespace ProximityPrize.SubmissionLower.RCN133
open Function Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {ι K M:Type*} [Field K] [AddCommGroup M] [Module K M]
theorem finite_iUnion_ssubset
   (s:Finset ι) (p:ι → Submodule K M)
   (h₁:∀ i,p i≠⊤) (h₂:s.card < ENat.card K):
   ⋃ i∈s,(p i:Set M) ⊂ univ:=by
 letI:DecidableEq ι:=Classical.decEq ι
 letI:DecidableEq K:=Classical.decEq K
 induction s using Finset.induction_on with
 | empty => simp
 | insert j s hj hj' =>
   simp only [ssubset_univ_iff] at hj' ⊢
   rcases s.eq_empty_or_nonempty with rfl | hs
   · simpa using! h₁ j
   replace h₂:s.card+1 < ENat.card K:=by simpa [Finset.card_insert_of_notMem hj] using! h₂
   specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
   contrapose hj'
   replace hj':(p j:Set M) ∪ (⋃ i∈s,p i)=univ:=by
     simpa [Finset.mem_insert] using! hj'
   suffices (p j:Set M) ⊆ ⋃ i∈s,p i by rwa [union_eq_right.mpr this] at hj'
   intro x (hx:x∈p j)
   rcases eq_or_ne x 0 with rfl | hx₀
   · simpa using! hs
   obtain ⟨y,hy⟩:∃ y,y∉p j:=by specialize h₁ j;contrapose! h₁;ext;simp [h₁]
   have hy₀:y≠0:=by aesop
   let sxy:={x+t • y | (t:K) (ht:t≠0)}
   have hsxy:sxy ⊆ ⋃ i∈s,p i:=by
     suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
     rw [Set.disjoint_iff]
     rintro-⟨⟨t,ht₀,rfl⟩,ht:x+t • y∈p j⟩
     rw [(p j).add_mem_iff_right hx,(p j).smul_mem_iff ht₀] at ht
     contradiction
   obtain ⟨k,hk,t₁,t₂,ht,ht₁,ht₂⟩:∃ᵉ (k∈s) (t₁:K) (t₂:K),
       t₁≠t₂∧x+t₁ • y∈p k∧x+t₂ • y∈p k:=by
     suffices ∃ᵉ (k∈s) (z₁∈sxy) (z₂∈sxy),z₁≠z₂∧z₁∈p k∧z₂∈p k by
       obtain ⟨k,hk, -,⟨t₁, -,rfl⟩, -,⟨t₂, -,rfl⟩,htne,ht₁,ht₂⟩:=this
       exact ⟨k,hk,t₁,t₂,by aesop,ht₁,ht₂⟩
     choose f hf using fun z:sxy↦mem_iUnion.mp (hsxy z.property)
     have hf':MapsTo f univ s:=fun z _↦by specialize hf z;aesop
     suffices ∃ z₁ z₂,z₁≠z₂∧f z₁=f z₂ by
       obtain ⟨z₁,z₂,hne,heq⟩:=this
       exact ⟨f z₁,hf' (mem_univ _),z₁,z₁.property,z₂,z₂.property,
         Subtype.coe_ne_coe.mpr hne,by specialize hf z₁;simp_all,by specialize hf z₂;aesop⟩
     have key:s.card < sxy.encard:=by
       refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
       have:Injective (fun t:K↦x+t • y):=
         fun t₁ t₂ ht↦smul_left_injective K hy₀ <| by simpa using! ht
       have aux:sxy=((fun t:K↦x+t • y) '' {t | t≠0}):=by ext;simp [sxy]
       rw [aux,this.encard_image,encard_ne_add_one]
     obtain ⟨z₁, -,z₂, -,h⟩:=exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
     exact ⟨z₁,z₂,h⟩
   replace ht:y∈p k:=by
     have:(t₁-t₂) • y∈p k:=by convert sub_mem ht₁ ht₂;module
     refine ((p k).smul_mem_iff ?_).mp this
     rwa [sub_ne_zero]
   replace ht:x∈p k:=by convert sub_mem ht₁ ((p k).smul_mem t₁ ht);simp
   simpa using! ⟨k,hk,ht⟩
theorem exists_avoiding_finite_proper_submodules
   [Finite ι] [Infinite K]
   (p:ι → Submodule K M) (hproper:∀ i,p i≠⊤):
   ∃ x,∀ i,x∉p i:=by
 let _i:Fintype ι:=Fintype.ofFinite ι
 suffices ⋃ i,(p i:Set M) ⊂ univ by
   simpa [ssubset_univ_iff,iUnion_eq_univ_iff] using this
 simpa using finite_iUnion_ssubset Finset.univ p hproper (by simp)
variable {N:Type*} [AddCommGroup N] [Module K N]
variable {σ:Type*} [DecidableEq σ]
def polynomialOfSupport (E:Finset (σ →₀ ℕ)) (c:E → K):
   MvPolynomial σ K:=
 ∑ d:E,MvPolynomial.monomial d.1 (c d)
@[simp] theorem coeff_polynomialOfSupport
   (E:Finset (σ →₀ ℕ)) (c:E → K) (d:σ →₀ ℕ):
   MvPolynomial.coeff d (polynomialOfSupport E c)=
     if hd:d∈E then c ⟨d,hd⟩ else 0:=by
 classical
 rw [show polynomialOfSupport E c=
     ∑ e∈(Finset.univ:Finset E),
       MvPolynomial.monomial e.1 (c e) by simp [polynomialOfSupport]]
 rw [MvPolynomial.coeff_sum]
 simp only [MvPolynomial.coeff_monomial]
 by_cases hd:d∈E
 · simp only [hd,dite_true]
   rw [Finset.sum_eq_single ⟨d,hd⟩]
   · simp
   · intro e _ hne
     have hval:e.1≠d:=by
       intro heq
       apply hne
       exact Subtype.ext heq
     rw [if_neg hval]
   · simp
 · simp only [hd,dite_false]
   apply Finset.sum_eq_zero
   intro e _
   have hval:e.1≠d:=by
     intro heq
     apply hd
     rw [←heq]
     exact e.2
   rw [if_neg hval]
theorem support_polynomialOfSupport_subset
   (E:Finset (σ →₀ ℕ)) (c:E → K):
   (polynomialOfSupport E c).support ⊆ E:=by
 intro d hd
 by_contra hnot
 have hcoeff:=MvPolynomial.mem_support_iff.mp hd
 rw [coeff_polynomialOfSupport,dif_neg hnot] at hcoeff
 exact hcoeff rfl
end
end ProximityPrize.SubmissionLower.RCN133
end PackedLegacy_BI

/-! Packed from ProximityPrize.SubmissionLower.AZ. -/
section PackedLegacy_AZ
namespace ProximityPrize.SubmissionLower
open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap
def AffineLineGivenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (T:F → Finset ι),
   a < S.card →
   (∀ z∈S,(T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
       LinearCode.projectedCodeSubmod C (T z)) →
   ∃ z∈S,∀ j:Fin 2,
     LinearCode.projectedWord (U j) (T z)∈LinearCode.projectedCodeSubmod C (T z)
theorem mcaError_affineLine_le_of_givenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ)
   (hgiven:AffineLineGivenSetsBound C δ a):
   mcaError (AffineLineGenerator F) C δ ≤
     ENNReal.ofReal ((a:ℝ)/Fintype.card F):=by
 classical
 unfold mcaError
 refine iSup_le fun U => ?_
 rw [Probability.prob_uniform_eq_ofReal]
 apply ENNReal.ofReal_le_ofReal
 apply div_le_div_of_nonneg_right
 · exact_mod_cast (show
     (Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)).card ≤ a by
     by_contra hnot
     have hlarge:a < (Finset.univ.filter (fun z:F =>
         IsMCA (AffineLineGenerator F) C z U δ)).card:=by omega
     let S:Finset F:=Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)
     have hmem (z:F) (hz:z∈S):
         IsMCA (AffineLineGenerator F) C z U δ:=by
       simpa [S] using hz
     let T:F → Finset ι:=fun z =>
       if hz:z∈S then Classical.choose (hmem z hz) else ∅
     have hTspec (z:F) (hz:z∈S):
         (T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)∧
         LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
           LinearCode.projectedCodeSubmod C (T z)∧
         ∃ j:Fin 2,LinearCode.projectedWord (U j) (T z)∉
           LinearCode.projectedCodeSubmod C (T z):=by
       rcases Classical.choose_spec (hmem z hz) with ⟨hcard,hcomb,hbad⟩
       have hTz:T z=Classical.choose (hmem z hz):=by
         simp only [T,dif_pos hz]
       rw [hTz]
       refine ⟨hcard,?_,hbad⟩
       simpa [AffineLineGenerator,Fin.sum_univ_two] using hcomb
     obtain ⟨z,hzS,hall⟩:=hgiven U S T (by simpa [S] using hlarge)
       (fun z hz => (hTspec z hz).1) (fun z hz => (hTspec z hz).2.1)
     obtain ⟨j,hj⟩:=(hTspec z hzS).2.2
     exact hj (hall j))
 · positivity
open Finset
variable {ι F:Type} [Fintype ι] [DecidableEq ι]
 [Field F] [DecidableEq F]
theorem exists_common_affine_set
   (U p:Fin 2 → ι → F) (T:Finset F) (A:F → Finset ι) (e:ℕ)
   (hT:e+1 < T.card)
   (hAcard:∀ z∈T,Fintype.card ι-e ≤ (A z).card)
   (hEq:∀ z∈T,∀ x∈A z,
     U 0 x+z*U 1 x=p 0 x+z*p 1 x):
   ∃ z∈T,∀ x∈A z,U 0 x=p 0 x∧U 1 x=p 1 x:=by
 classical
 let B:Finset ι:=Finset.univ.filter fun x =>
   U 0 x≠p 0 x∨U 1 x≠p 1 x
 let R:F → Finset ι:=fun z => A z ∩ B
 have hRsub (z:F):R z ⊆ B:=by
   intro x hx
   exact (Finset.mem_inter.mp hx).2
 have hRpair:(↑T:Set F).PairwiseDisjoint R:=by
   rintro z hz w hw hzw
   change Disjoint (R z) (R w)
   rw [Finset.disjoint_left]
   intro x hxz hxw
   have hxAz:x∈A z:=(Finset.mem_inter.mp hxz).1
   have hxAw:x∈A w:=(Finset.mem_inter.mp hxw).1
   have hzEq:=hEq z hz x hxAz
   have hwEq:=hEq w hw x hxAw
   have hmul:(z-w)*(U 1 x-p 1 x)=0:=by
     linear_combination hzEq-hwEq
   have hzw0:z-w≠0:=sub_ne_zero.mpr hzw
   have hrow1:U 1 x=p 1 x:=by
     exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzw0)
   have hrow0:U 0 x=p 0 x:=by
     rw [hrow1] at hzEq
     exact add_right_cancel hzEq
   have hxB:x∈B:=(Finset.mem_inter.mp hxz).2
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at hxB
   exact hxB.elim (fun h => h hrow0) (fun h => h hrow1)
 have hRlower (z:F) (hz:z∈T):B.card ≤ (R z).card+e:=by
   have hsplit:=Finset.card_inter_add_card_sdiff (A z) B
   have hsdiff:(A z \ B).card ≤ Bᶜ.card:=by
     apply Finset.card_le_card
     intro x hx
     rw [Finset.mem_compl]
     exact (Finset.mem_sdiff.mp hx).2
   rw [Finset.card_compl] at hsdiff
   have ha:=hAcard z hz
   have hbcard:B.card ≤ Fintype.card ι:=Finset.card_le_univ B
   dsimp only [R]
   omega
 have hB:B.card ≤ e:=by
   by_contra hnot
   have heB:e < B.card:=Nat.lt_of_not_ge hnot
   have hsumLower:T.card*(B.card-e) ≤ ∑ z∈T,(R z).card:=by
     calc
       T.card*(B.card-e)=∑ z∈T,(B.card-e):=by
         exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
       _ ≤ ∑ z∈T,(R z).card:=by
         exact Finset.sum_le_sum fun z hz => by
           have:=hRlower z hz
           omega
   have hunionSub:(T.biUnion R).card ≤ B.card:=by
     apply Finset.card_le_card
     intro x hx
     obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
     exact hRsub z hxR
   have hunionCard:(T.biUnion R).card=∑ z∈T,(R z).card:=
     Finset.card_biUnion hRpair
   rw [hunionCard] at hunionSub
   have hprod:T.card*(B.card-e) ≤ B.card:=hsumLower.trans hunionSub
   have hdpos:0 < B.card-e:=Nat.sub_pos_of_lt heB
   have htlo:e+2 ≤ T.card:=by omega
   have he_mul:e ≤ e*(B.card-e):=
     Nat.le_mul_of_pos_right e hdpos
   have hstrict:B.card < (e+2)*(B.card-e):=by
     calc
       B.card=e+(B.card-e):=(Nat.add_sub_of_le heB.le).symm
       _ ≤ e*(B.card-e)+(B.card-e):=Nat.add_le_add_right he_mul _
       _ < e*(B.card-e)+2*(B.card-e):=by omega
       _=(e+2)*(B.card-e):=by ring
   have hprodLower:(e+2)*(B.card-e) ≤
       T.card*(B.card-e):=Nat.mul_le_mul_right _ htlo
   omega
 by_contra hno
 push Not at hno
 have hRpos:∀ z∈T,1 ≤ (R z).card:=by
   intro z hz
   obtain ⟨x,hxA,hxnot⟩:=hno z hz
   apply Finset.card_pos.mpr
   refine ⟨x,Finset.mem_inter.mpr ⟨hxA,?_⟩⟩
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases h0:U 0 x=p 0 x
   · exact Or.inr (hxnot h0)
   · exact Or.inl h0
 have hTsum:T.card ≤ ∑ z∈T,(R z).card:=by
   calc
     T.card=∑ z∈T,1:=by simp
     _ ≤ ∑ z∈T,(R z).card:=Finset.sum_le_sum hRpos
 have hunionSub:(T.biUnion R).card ≤ B.card:=by
   apply Finset.card_le_card
   intro x hx
   obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
   exact hRsub z hxR
 rw [Finset.card_biUnion hRpair] at hunionSub
 have hTB:T.card ≤ B.card:=hTsum.trans hunionSub
 omega
def AffineLineAlignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (A:F → Finset ι),
   a < S.card →
   (∀ z∈S,Fintype.card ι-e ≤ (A z).card) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (A z)∈
       LinearCode.projectedCodeSubmod C (A z)) →
   ∃ p:Fin 2 → ι → F,
     (∀ j,p j∈C)∧
     ∃ T:Finset F,T ⊆ S∧e+1 < T.card∧
       ∀ z∈T,∀ x∈A z,
         U 0 x+z*U 1 x=p 0 x+z*p 1 x
theorem givenSetsBound_of_alignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (e a:ℕ)
   (hsize:∀ A:Finset ι,
     (A.card:ℝ) ≥ (Fintype.card ι:ℝ)*(1-δ) →
     Fintype.card ι-e ≤ A.card)
   (halign:AffineLineAlignmentBound C e a):
   AffineLineGivenSetsBound C δ a:=by
 classical
 intro U S A hS hAcard hcomb
 obtain ⟨p,hpC,T,hTS,hTcard,hEq⟩:=
   halign U S A hS (fun z hz => hsize (A z) (hAcard z hz)) hcomb
 obtain ⟨z,hzT,hz⟩:=
   exists_common_affine_set U p T A e hTcard
     (fun z hz => hsize (A z) (hAcard z (hTS hz))) hEq
 refine ⟨z,hTS hzT,fun j => ?_⟩
 rw [LinearCode.mem_projectedCodeSubmod_iff]
 refine ⟨p j,hpC j,?_⟩
 funext x
 simp only [LinearCode.projectedWord]
 rcases hz x.1 x.2 with ⟨h0,h1⟩
 fin_cases j
 · exact h0
 · exact h1
end ProximityPrize.SubmissionLower
end PackedLegacy_AZ

/-! Packed from ProximityPrize.SubmissionLower.DV. -/
section PackedLegacy_DV
namespace ProximityPrize.SubmissionLower.RCN050
open ProximityPrize.Benchmark
noncomputable section
variable {ι K:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field K] [Fintype K] [DecidableEq K]
def pencilSeeds (seeds:Finset K) (selected:K → Polynomial K)
   (P₀ P₁:Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => selected γ=P₀+Polynomial.C γ*P₁)
def SelectedNoLargePencilBound (domain:ι ↪ K) (w e B:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K),
   (∀ γ∈seeds,(selected γ).natDegree ≤ w) →
   (∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card) →
   (∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i) →
   (∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1) →
   seeds.card ≤ B
theorem degree_lt_succ_of_natDegree_le (P:Polynomial K) (w:ℕ)
   (hdegree:P.natDegree ≤ w):P.degree < ((w+1:ℕ):WithBot ℕ):=by
 rcases eq_or_ne P 0 with hzero | hnonzero
 · simp [hzero]
 · rw [←Polynomial.natDegree_lt_iff_degree_lt hnonzero]
   omega
theorem exists_selected_polynomials
   (domain:ι ↪ K) (w:ℕ) (U:Fin 2 → ι → K)
   (seeds:Finset K) (A:K → Finset ι)
   (hprojected:∀ γ∈seeds,
     LinearCode.projectedWord (fun i => U 0 i+γ*U 1 i) (A γ)∈
       LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w+1)) (A γ)):
   ∃ selected:K → Polynomial K,
     (∀ γ∈seeds,(selected γ).natDegree ≤ w)∧
     (∀ γ∈seeds,∀ i∈A γ,
       (selected γ).eval (domain i)=U 0 i+γ*U 1 i):=by
 classical
 have hexists (γ:K) (hγ:γ∈seeds):∃ P:Polynomial K,
     P.natDegree ≤ w∧∀ i∈A γ,P.eval (domain i)=U 0 i+γ*U 1 i:=by
   have hc:=hprojected γ hγ
   rw [LinearCode.mem_projectedCodeSubmod_iff] at hc
   obtain ⟨c,hcode,hvalue⟩:=hc
   change c∈ReedSolomon.code domain (w+1) at hcode
   rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcode
   obtain ⟨P,hdegree,rfl⟩:=hcode
   refine ⟨P,?_,?_⟩
   · rcases eq_or_ne P 0 with hzero | hnonzero
     · simp [hzero]
     · have hd:P.natDegree < w+1:=
         (Polynomial.natDegree_lt_iff_degree_lt hnonzero).mpr hdegree
       omega
   · intro i hi
     have hh:=congrFun hvalue ⟨i,hi⟩
     simpa [LinearCode.projectedWord,ReedSolomon.evalOnPoints] using hh.symm
 let selected:K → Polynomial K:=fun γ =>
   if hγ:γ∈seeds then Classical.choose (hexists γ hγ) else 0
 have hspec (γ:K) (hγ:γ∈seeds):
     (selected γ).natDegree ≤ w∧
       ∀ i∈A γ,(selected γ).eval (domain i)=U 0 i+γ*U 1 i:=by
   simpa only [selected,dif_pos hγ] using Classical.choose_spec (hexists γ hγ)
 exact ⟨selected,fun γ hγ => (hspec γ hγ).1,fun γ hγ => (hspec γ hγ).2⟩
theorem exists_large_pencil_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B)
   (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K) (hlarge:B < seeds.card)
   (hdegree:∀ γ∈seeds,(selected γ).natDegree ≤ w)
   (hcard:∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card)
   (hagreement:∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     e+1 < (pencilSeeds seeds selected P₀ P₁).card:=by
 by_contra hno
 have hsmall:∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1:=by
   intro P₀ P₁ h₀ h₁
   apply Nat.le_of_not_gt
   intro hh
   exact hno ⟨P₀,P₁,h₀,h₁,hh⟩
 have hh:=hcount U seeds A selected hdegree hcard hagreement hsmall
 omega
theorem alignmentBound_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B):
   AffineLineAlignmentBound (ReedSolomon.code domain (w+1)) e B:=by
 classical
 intro U seeds A hlarge hcard hprojected
 obtain ⟨selected,hdegree,hagreement⟩:=exists_selected_polynomials domain w U seeds A hprojected
 obtain ⟨P₀,P₁,h₀,h₁,hTcard⟩:=exists_large_pencil_of_selected_count
   domain w e B hcount U seeds A selected hlarge hdegree hcard hagreement
 let T:=pencilSeeds seeds selected P₀ P₁
 have hTsub:T ⊆ seeds:=Finset.filter_subset _ _
 let rows:Fin 2 → ι → K:=
   ![ReedSolomon.evalOnPoints domain P₀,ReedSolomon.evalOnPoints domain P₁]
 refine ⟨rows,?_,T,hTsub,hTcard,?_⟩
 · intro j
   fin_cases j
   · change ReedSolomon.evalOnPoints domain P₀∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₀ w h₀)
   · change ReedSolomon.evalOnPoints domain P₁∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₁ w h₁)
 · intro γ hγ i hi
   have hpoly:selected γ=P₀+Polynomial.C γ*P₁:=(Finset.mem_filter.mp hγ).2
   have heval:=congrArg (Polynomial.eval (domain i)) hpoly
   have hword:=hagreement γ (hTsub hγ) i hi
   simpa [rows,ReedSolomon.evalOnPoints] using hword.symm.trans heval
def SelectedNoLargePencilBound6400:Prop:=
 SelectedNoLargePencilBound IRSProfile.domain 131071 76780 274980728111352763
end
end ProximityPrize.SubmissionLower.RCN050
end PackedLegacy_DV

/-! Packed from ProximityPrize.SubmissionLower.K7. -/
section PackedLegacy_K7
namespace ProximityPrize.SubmissionLower.RCN175
open RCN174 RCN256 RCN223 ProximityPrize.Benchmark
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev FrozenCoefficientIndex6600:=
 CoefficientIndex weightedCap w seedTotalCap slopeCap
end
end ProximityPrize.SubmissionLower.RCN175
end PackedLegacy_K7

/-! Packed from ProximityPrize.SubmissionLower.GR. -/
section PackedLegacy_GR
namespace ProximityPrize.SubmissionLower.RCN320
open ProximityPrize.Benchmark RCN174 RCN175 RCN256 RCN223 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
end
end ProximityPrize.SubmissionLower.RCN320
end PackedLegacy_GR

/-! Packed from ProximityPrize.SubmissionLower.BF. -/
section PackedLegacy_BF
namespace ProximityPrize.SubmissionLower.RCN128
open ProximityPrize.Benchmark RCN050 RCN174 RCN319 RCN320 RCN238 RCN223
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
def SelectedNoLargePencilBound6600:Prop:=
 SelectedNoLargePencilBound IRSProfile.domain w errors alignmentBudget
def GlobalCountLtAlignment6600:Prop:=
 ∀ (Q:MvPolynomial (Fin 4) IRSProfile.Field),
   Q≠0 →
   Q∈globalCoefficientBox IRSProfile.Field
     weightedCap w seedTotalCap slopeCap →
   ∀ (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
     (seeds:Finset IRSProfile.Field)
     (u0 u1:IRSProfile.Index → IRSProfile.Field),
     (∀ gamma∈seeds,(selected gamma).natDegree ≤ w) →
     (∀ gamma∈seeds,
       specialization IRSProfile.Field (selected gamma) gamma Q=0) →
     (∀ gamma∈seeds,agreements ≤
       (Finset.univ.filter (fun i:IRSProfile.Index↦
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card) →
     NoLargeSelectedPencil selected seeds w errors →
     seeds.card < alignmentBudget
abbrev InterpolantSelectedCount6600:=GlobalCountLtAlignment6600
theorem challenge_field_characteristic6600:
   CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
end
end ProximityPrize.SubmissionLower.RCN128
end PackedLegacy_BF

/-! Packed from ProximityPrize.SubmissionLower.BY. -/
section PackedLegacy_BY
namespace ProximityPrize.SubmissionLower.RCN179
open scoped BigOperators
open RCN081 RCN167 RCN313 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem wt_polyG_le_of_R_le_Y
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem numeratorStep_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F M:Poly4 K) (b A C:ℕ)
   (hRY:weights 2 ≤ weights 1) (hYC:weights 1 ≤ C)
   (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
   (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
   wt weights (numeratorStep K F b M) ≤
     A+2*(C-weights 2):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 let Hcap:=C-weights 2
 have hRC:weights 2 ≤ C:=by omega
 have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
 have hG:wt weights G ≤ C:=
   wt_polyG_le_of_R_le_Y weights hX F C hRY hYC hF
 have hRwt:wt weights R=weights 2:=weighted_X weights 2
 have hRH:weights 2+Hcap=C:=by
   dsimp [Hcap]
   omega
 have hRH2:weights 2 ≤ Hcap:=by
   dsimp [Hcap]
   omega
 have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
   have h:=wt_pderiv_le weights M 0 A hM
   rw [hX,Nat.sub_zero] at h
   exact h
 have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A-weights 1:=
   wt_pderiv_le weights M 1 A hM
 have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
   wt_pderiv_le weights M 2 A hM
 have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
   have h:=wt_pderiv_le weights H 0 Hcap hH
   rw [hX,Nat.sub_zero] at h
   exact h
 have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap-weights 1:=
   wt_pderiv_le weights H 1 Hcap hH
 have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
   wt_pderiv_le weights H 2 Hcap hH
 have hH2:wt weights (H^2) ≤ 2*Hcap:=
   (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
 have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
     A+2*Hcap:=by
   have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights R (H^2)
   have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights G H
   have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
   omega
 have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤
     2*Hcap:=by
   have h1:=wt_mul_le weights R H
   have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
   omega
 have hinner:wt weights
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   exact (wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
 have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
 have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
   omega
 have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change wt weights
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap
 exact (wt_sub_le weights _ _).trans
   (max_le ((wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C) (b:ℕ):
   wt weights (numerator K F b) ≤
     weights 1+b*(2*(C-weights 2)):=by
 induction b with
 | zero =>
     rw [numerator_zero]
     unfold wt
     rw [weighted_X]
     simp
 | succ b ih =>
     rw [numerator_succ]
     have h:=numeratorStep_wt_le_equal_weight weights hX F
       (numerator K F b) b
       (weights 1+b*(2*(C-weights 2))) C hRY hYC hRR
       (hbase.trans (Nat.le_add_right _ _)) hF ih
     convert h using 1 <;> ring
theorem clearedTaylorNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x:K):
   wt weights (clearedTaylorNumerator F w coeffs x) ≤
     weights 1+w*(2*(C-weights 2)):=by
 unfold clearedTaylorNumerator
 apply wt_sum_le
 intro j hj
 have hjw:j ≤ w:=by
   have:=Finset.mem_range.mp hj
   omega
 have hM:=numerator_wt_le_equal_weight weights hX F C hRY hYC hRR
   hbase hF j
 have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
     weights 1+j*(2*(C-weights 2)):=by
   have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
   rw [wt_C,Nat.zero_add] at hm
   exact hm.trans hM
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*(w-j))) ≤
     2*(w-j)*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*(w-j))).trans
     (Nat.mul_le_mul_left _ hH)
 have hSX:=shiftedX_wt_eq_zero weights hX x
 have hSXP:wt weights
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   have hp:=wt_pow_le weights
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
   rw [hSX,Nat.mul_zero] at hp
   exact hp
 have h1:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j*
     polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 simp only [commonNumeratorTerm]
 apply h2.trans
 calc
   wt weights (MvPolynomial.C (coeffs j)*numerator K F j*
       polyH K F^(2*(w-j)))+
       wt weights ((MvPolynomial.C x-MvPolynomial.X 0:Poly4 K)^j) ≤
       (weights 1+j*(2*(C-weights 2))+
         2*(w-j)*(C-weights 2))+0:=
     Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP
   _=weights 1+w*(2*(C-weights 2)):=by
     have hjw':j+(w-j)=w:=by omega
     calc
       (weights 1+j*(2*(C-weights 2))+
           2*(w-j)*(C-weights 2))+0=
           weights 1+(j+(w-j))*(2*(C-weights 2)):=by ring
       _=weights 1+w*(2*(C-weights 2)):=by rw [hjw']
theorem agreementNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
     max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
 have hTaylor:=clearedTaylorNumerator_wt_le_equal_weight weights hX F C hRY
   hYC hRR hbase hF w coeffs x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*w)) ≤
     2*w*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*w)).trans
     (Nat.mul_le_mul_left _ hH)
 have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
   (polyH K F^(2*w))
 unfold agreementNumerator
 apply (wt_sub_le weights _ _).trans
 apply max_le
 · exact hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
 · apply hprod.trans
   calc
     wt weights (affineSeedPolynomial u₀ u₁)+
         wt weights (polyH K F^(2*w)) ≤
         weights 3+2*w*(C-weights 2):=Nat.add_le_add hA hHP
     _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
       have hz:=Nat.le_max_right (weights 1) (weights 3)
       calc
         weights 3+2*w*(C-weights 2)=
             weights 3+w*(2*(C-weights 2)):=by ring
         _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=
           Nat.add_le_add_right hz _
end
end ProximityPrize.SubmissionLower.RCN179
end PackedLegacy_BY

/-! Packed from ProximityPrize.SubmissionLower.Z6. -/
section PackedLegacy_Z6
namespace ProximityPrize.SubmissionLower.RCN164
open scoped Classical
open RCN159 RCN159.ResidualStage RCN213 RCN173 RCN238 RCN095 RCN275
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree}
 {support:ResidualSupportParameters}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem recursive_scaled_stratified_incidence_bound
   (hphi:Function.Injective phi) {w a:ℕ}
   (S:ResidualStage phi Gamma x p e flag w support)
   (degreeCost unitCost U V:ℕ)
   (hwa:w < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*(a-w) ≤
       D.degree*degreeCost+unitCost)
   (hdegree:∀ k ≤ w,
     (S.nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (S.nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w)^2 ≤ U*degreeCost+V*unitCost:=by
 classical
 obtain ⟨D⟩:=S.exists_terminal_descendant hphi
 let k:=w-D.degree
 have hk:k ≤ w:=Nat.sub_le w D.degree
 have hDle:D.degree ≤ w:=D.degree_le
 have hdegreeEq:D.degree=w-k:=by
   dsimp only [k]
   omega
 have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
   simpa only [k] using D.nodes_card
 have hterminalAgreement:∀ gamma∈Gamma,
     a-k ≤ (D.stage.agreementFiber gamma).card:=by
   intro gamma hgamma
   exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
     (by simpa only [k] using D.agreement_card gamma hgamma)
 let geometricCost:=D.degree*degreeCost+unitCost
 have hgap:0 < a-w:=Nat.sub_pos_of_lt hwa
 have hterminalFiberDiv:∀ i∈D.stage.nodes,
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
       geometricCost/(a-w):=by
   intro i hi
   apply (Nat.le_div_iff_mul_le hgap).mpr
   exact hfiber D i hi
     (D.stage.proper_agreement_of_terminal D.terminal hi)
 have hrawTerminal:=incidence_after_exempt_nodes
   (fun gamma i↦D.stage.Agrees gamma i)
   Gamma D.stage.nodes ∅ (a-k) (geometricCost/(a-w))
   (by simp) hterminalAgreement (by
     intro i hi
     exact hterminalFiberDiv i (by simpa using hi))
 have hrawScaled:(Gamma.card*(a-w))*(a-k) ≤
     (S.nodes.card-k)*((w-k)*degreeCost+unitCost):=by
   calc
     (Gamma.card*(a-w))*(a-k)=
         (Gamma.card*(a-k))*(a-w):=by ring
     _ ≤ ((D.stage.nodes.card*(geometricCost/(a-w)))*
         (a-w)):=Nat.mul_le_mul_right (a-w) (by
           simpa only [Finset.card_empty,Nat.sub_zero] using hrawTerminal)
     _=D.stage.nodes.card*
         ((geometricCost/(a-w))*(a-w)):=by ring
     _ ≤ D.stage.nodes.card*geometricCost:=
       Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
     _=(S.nodes.card-k)*
         ((w-k)*degreeCost+unitCost):=by
       simp only [hnodeEq,geometricCost,hdegreeEq]
 have hlinear:=stratified_incidence_linear
   (Gamma.card*(a-w)) S.nodes.card a w k
   degreeCost unitCost U V hk hwa hrawScaled
   (hdegree k hk) (hunit k hk)
 calc
   Gamma.card*(a-w)^2=(Gamma.card*(a-w))*(a-w):=by ring
   _ ≤ U*degreeCost+V*unitCost:=hlinear
end
end ProximityPrize.SubmissionLower.RCN164
end PackedLegacy_Z6

/-! Packed from ProximityPrize.SubmissionLower.U. -/
section PackedLegacy_U
namespace ProximityPrize.SubmissionLower.RCN276
open scoped BigOperators
open RCN174 RCN286 RCN095 RCN266
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
structure Profile where
 n:ℕ
 w:ℕ
 agreements:ℕ
 weightedCap:ℕ
 seedTotalCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq,Repr
namespace Profile
def errors (p:Profile):ℕ:=p.n-p.agreements
def gap (p:Profile):ℕ:=p.agreements-p.w
def yCap (p:Profile):ℕ:=(p.weightedCap-1)/p.w
def degreeIncidence (p:Profile):ℕ:=
 (p.n*p.gap*p.w+p.agreements-1)/p.agreements
def unitIncidence (p:Profile):ℕ:=p.n-p.w
def surfaceFlag (p:Profile):FlagDegree:=
 ⟨p.seedTotalCap+p.slopeCap-p.yCap,
   p.yCap-p.slopeCap,p.slopeCap⟩
def derivativeFlag (p:Profile):FlagDegree:=
 ⟨p.surfaceFlag.zOnly,p.surfaceFlag.yz,p.surfaceFlag.all-1⟩
def agreementDirection (p:Profile):FlagDegree:=
 p.surfaceFlag+p.derivativeFlag
def rectangularSurfaceFlag (p:Profile):FlagDegree:=
 ⟨p.seedTotalCap,p.yCap,p.slopeCap⟩
def factorPrimary (p:Profile) (flag:FlagDegree):ℕ:=
 flagMixed flag p.agreementDirection p.agreementDirection*p.degreeIncidence^2+
   2*flagMixed flag p.agreementDirection unitYZFlag*
     p.degreeIncidence*p.unitIncidence+
   flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2
def factorZTail (p:Profile) (flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag p.agreementDirection unitZFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)
def factorAllTail (p:Profile) (flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag p.agreementDirection unitAllFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitAllFlag*p.unitIncidence)
def factorRegularLedger (p:Profile) (flag:FlagDegree):ℕ:=
 p.factorPrimary flag+p.factorZTail flag+p.factorAllTail flag
def regularNumerator (p:Profile):ℕ:=
 p.factorRegularLedger p.rectangularSurfaceFlag
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq,Repr
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
   a.r*b.y*c.z+a.r*b.z*c.y+
   a.z*b.y*c.r+a.z*b.r*c.y
def algebraicCap (p:Profile):ℕ:=
 (2*p.slopeCap-1)*p.seedTotalCap
def implicitWeightedCap (p:Profile):ℕ:=
 (2*p.slopeCap-1)*p.weightedCap
def implicitYCap (p:Profile):ℕ:=
 (p.implicitWeightedCap-1)/p.w
def liftedSurface (p:Profile):DegreeVector:=
 ⟨p.implicitYCap,1,p.algebraicCap⟩
def implicitCut (p:Profile):DegreeVector:=
 ⟨p.implicitYCap,0,p.algebraicCap⟩
def liftedLast (p:Profile):DegreeVector:=
 ⟨1+2*p.implicitWeightedCap*p.implicitYCap,
   p.implicitWeightedCap,
   2*p.implicitWeightedCap*p.algebraicCap⟩
def liftedAgreement (p:Profile):DegreeVector:=
 ⟨1+2*p.w*p.implicitYCap,
   p.w,2*p.w*p.algebraicCap+1⟩
def unitZ:DegreeVector:=⟨0,0,1⟩
def retainedSingularContribution (p:Profile):ℕ:=
 p.gap*
   (p.gap*
     (p.algebraicCap+2*p.algebraicCap^2+
       mixed p.liftedSurface p.implicitCut p.liftedLast+
       (p.errors+1)*mixed p.liftedSurface p.implicitCut unitZ)+
     (p.n-p.w)*
       mixed p.liftedSurface p.implicitCut p.liftedAgreement)
def totalNumerator (p:Profile):ℕ:=
 p.regularNumerator+p.retainedSingularContribution
def fixedCost (p:Profile):ℕ:=
 (p.totalNumerator+p.gap^2-1)/p.gap^2
end Profile
theorem factorRegularLedger_projection_decomposition
   (p:Profile) (flag:FlagDegree):
   p.factorRegularLedger flag=
     flag.zOnly*p.factorRegularLedger unitZFlag+
     flag.yz*p.factorRegularLedger unitYZFlag+
     flag.all*p.factorRegularLedger unitAllFlag:=by
 cases flag
 simp [Profile.factorRegularLedger,Profile.factorPrimary,
   Profile.factorZTail,Profile.factorAllTail,flagMixed,
   unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem sum_factorRegularLedger_le_flag
   {I:Type} [Fintype I] (p:Profile)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
   (hall:(∑ i,(flag i).all) ≤ cap.all):
   (∑ i,p.factorRegularLedger (flag i)) ≤
     p.factorRegularLedger cap:=by
 classical
 calc
   (∑ i,p.factorRegularLedger (flag i))=
       ∑ i,((flag i).zOnly*p.factorRegularLedger unitZFlag+
         (flag i).yz*p.factorRegularLedger unitYZFlag+
         (flag i).all*p.factorRegularLedger unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedger_projection_decomposition p (flag i)
   _=(∑ i,(flag i).zOnly)*p.factorRegularLedger unitZFlag+
       (∑ i,(flag i).yz)*p.factorRegularLedger unitYZFlag+
       (∑ i,(flag i).all)*p.factorRegularLedger unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*p.factorRegularLedger unitZFlag+
       cap.yz*p.factorRegularLedger unitYZFlag+
       cap.all*p.factorRegularLedger unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=p.factorRegularLedger cap:=
     (factorRegularLedger_projection_decomposition p cap).symm
noncomputable section
variable {K:Type} [Field K]
theorem regularFlag_budgets
   (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap):
   (∑ F:RegularIndex Q,(regularFlag Q F).zOnly) ≤ p.seedTotalCap∧
     (∑ F:RegularIndex Q,(regularFlag Q F).yz) ≤ p.yCap∧
     (∑ F:RegularIndex Q,(regularFlag Q F).all) ≤ p.slopeCap:=by
 classical
 have hb:=directFactor_input_budgets Q hQ p.weightedCap p.w
   p.seedTotalCap p.slopeCap hw hbox
 simp only [regularFlag,Finset.sum_coe_sort]
 exact ⟨hb.2.2,hb.1,hb.2.1⟩
theorem sum_factor_counts_rectangular_le
   (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (count:RegularIndex Q → ℕ)
   (hcount:∀ F,count F*p.gap^2 ≤
     p.factorRegularLedger (regularFlag Q F)):
   (∑ F,count F)*p.gap^2 ≤ p.regularNumerator:=by
 have hcaps:=regularFlag_budgets p Q hQ hw hbox
 calc
   (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F,p.factorRegularLedger (regularFlag Q F):=
     Finset.sum_le_sum (fun F _↦hcount F)
   _ ≤ p.factorRegularLedger p.rectangularSurfaceFlag:=
     sum_factorRegularLedger_le_flag p (regularFlag Q)
       p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
   _=p.regularNumerator:=rfl
end
def meetProfile:Profile where
 n:=262144
 w:=131071
 agreements:=182807
 weightedCap:=4570175
 seedTotalCap:=598
 slopeCap:=6
end ProximityPrize.SubmissionLower.RCN276
end PackedLegacy_U

/-! Packed from ProximityPrize.SubmissionLower.B8. -/
section PackedLegacy_B8
namespace ProximityPrize.SubmissionLower.RCN091
open scoped Classical
open RCN159 RCN164 RCN213 RCN275 RCN276 RCN238 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def meetFactorDegreeCost (p:FlagDegree):ℕ:=
 (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       ResidualSupportParameters.fixedMeetSupport.agreementDirection*
     meetProfile.degreeIncidence+
   flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitZFlag+
     flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitAllFlag)
def meetFactorUnitCost (p:FlagDegree):ℕ:=
 (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitYZFlag*meetProfile.degreeIncidence+
   flagMixed p unitYZFlag unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed p unitYZFlag unitZFlag+
     flagMixed p unitYZFlag unitAllFlag)
end
end ProximityPrize.SubmissionLower.RCN091
end PackedLegacy_B8

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EN. -/
section PackedLegacy_EN
namespace ProximityPrize.SubmissionLower.RCN141
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN167 RCN169 RCN290 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
def prime6656:ℕ:=2130706433
def meetTightProfile:TightParameters where
 n:=meetProfile.n
 w:=meetProfile.w
 a:=meetProfile.agreements
 D:=meetProfile.weightedCap
 L:=meetProfile.seedTotalCap
 s:=meetProfile.slopeCap
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def meetImplicitCost (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):RCN223.DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
end
end ProximityPrize.SubmissionLower.RCN141
end PackedLegacy_EN

/-! Packed from ProximityPrize.SubmissionLower.AG. -/
section PackedLegacy_AG
namespace ProximityPrize.SubmissionLower.RCN292
open scoped Classical BigOperators
open RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN081 RCN238 RCN243 RCN291 RCN318 RCN172 RCN294
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev TightParameters:=RCN318.TightParameters
namespace TightParameters
theorem implicitVector_budgets_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p) (hw:1 ≤ P.w):
   (∑ q:ImplicitIndex Q,(implicitVector Q q).y) ≤ P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).r) ≤
       2*P.implicitYCap*P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).z) ≤ P.implicitYCap:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hb:=implicitPair_input_budgets (singularAuxiliary Q) hJ
   (P.kappa*P.D) P.w P.algebraicCap (by omega) hJbox
 simpa only [implicitVector,Finset.sum_coe_sort,
   RCN318.TightParameters.implicitYCap] using hb
theorem exceptionalSeeds_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hj:1 ≤ P.algebraicCap)
   (hjSmall:P.algebraicCap < p)
   (selected:K → Polynomial K) (Gamma:Finset K):
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
     2*P.algebraicCap^2:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=
   Nat.eq_zero_of_le_zero
     (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ P.algebraicCap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:(singularAuxiliary Q).degreeOf 3 ≤ P.algebraicCap:=
   degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 exact exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
   P.algebraicCap p hj hjSmall hJY hJZ Gamma selected
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem implicitSeeds_pair_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors)
   (q:ImplicitIndex Q):
   (implicitSeeds Q selected Gamma q).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (implicitVector Q q)+
       (P.errors+1)*P.gap*(implicitVector Q q).z:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 obtain ⟨_hA,hG,hGR,hAbox,hGbox,hproper⟩:=
   implicitPair_data (singularAuxiliary Q) hJ
     (P.kappa*P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
 have hsub:=implicitSeeds_subset Q selected Gamma q
 have hpair:=implicit_pair_seed_bound q.1.1 q.1.2 hG hGR hproper
   (P.kappa*P.D) P.w P.implicitYCap P.algebraicCap
   p P.n P.a P.errors hAbox hGbox rfl selected
   (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
   hw hchar hwa han hjYSmall hjZSmall hmixedSmall
   (fun gamma hgamma => hdegree gamma (hsub hgamma))
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
   (fun gamma hgamma => hagreement gamma (hsub hgamma))
   (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
 simpa [implicitVector,
   RCN318.TightParameters.agreement,
   RCN318.TightParameters.errors,
   RCN318.TightParameters.gap,dot] using hpair
theorem singularSeeds_tight_gap_bound
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card*P.gap ≤ P.tightNumerator:=by
 have hcaps:=P.implicitVector_budgets_of_profile Q hQ hbox hs hsSmall hw
 have hexc:=P.exceptionalSeeds_bound_of_profile Q hQ hbox hs hsSmall
   hj hjZSmall selected Gamma
 have hsum:=P.with_exceptions_bound
   (fun q:ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
   (implicitVector Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hcaps.1 hcaps.2.1 hcaps.2.2
   (P.implicitSeeds_pair_bound_of_profile Q hQ hbox hs hsSmall hw hchar
     hDw hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
     hinj hnodes hdegree hagreement hnoPencil)
   hexc
 exact (Nat.mul_le_mul_right P.gap
   (singularSeeds_card_le_sum Q selected Gamma)).trans hsum
theorem singularSeeds_count_le_countCap
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card ≤ P.countCap:=by
 apply P.count_le_countCap _ (by
   simpa [RCN318.TightParameters.gap] using
     Nat.sub_pos_of_lt hwa)
 exact P.singularSeeds_tight_gap_bound Q hQ hbox hs hsSmall hw hchar hDw
   hj hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
   hinj hnodes hdegree hagreement hnoPencil
end TightParameters
def firstResidualQ2:TightParameters:=
 ⟨262144,131071,182807,8591929,598,14⟩
def secondResidualGcd12:TightParameters:=
 ⟨262144,131071,182807,4570175,598,7⟩
end
end ProximityPrize.SubmissionLower.RCN292
end PackedLegacy_AG

/-! Packed from ProximityPrize.SubmissionLower.J6. -/
section PackedLegacy_J6
namespace ProximityPrize.SubmissionLower.RCN092
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN292
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN092
end PackedLegacy_J6

/-! Packed from ProximityPrize.SubmissionLower.GQ. -/
section PackedLegacy_GQ
namespace ProximityPrize.SubmissionLower.RCN317
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN092
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN317
end PackedLegacy_GQ
end Compact_PackedLegacyCore2
