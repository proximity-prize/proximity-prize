import ProximityPrize.SubmissionLower.LowerFoundation
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open MvPolynomial ContactOrderBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def xWeights : Fin 4 → ℕ := ![1,0,0,0]

theorem x_weight_blowup (d : Fin 4 →₀ ℕ) :
    Finsupp.weight xWeights (blowupExponent d) =
      Finsupp.weight diagonalWeights d := by
  rw [RCN081.weight_fin4, RCN081.weight_fin4]
  simp [xWeights, diagonalWeights, blowupExponent]

theorem atLeast_x_blowup (m : ℕ) (P : Poly4 K) :
    AtLeast xWeights m (contactBlowup K P) ↔ AtLeast diagonalWeights m P := by
  classical
  constructor
  · intro h d hd
    have hm : blowupExponent d ∈ (contactBlowup K P).support := by
      rw [support_contactBlowup]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    simpa only [x_weight_blowup] using h _ hm
  · intro h d hd
    rw [support_contactBlowup] at hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    simpa only [x_weight_blowup] using h e he

theorem atLeast_x_iff_dvd (m : ℕ) (P : Poly4 K) :
    AtLeast xWeights m P ↔
      Polynomial.X ^ m ∣ MvPolynomial.finSuccEquiv K 3 P := by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h n hn
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw := h (Finsupp.cons n d) (MvPolynomial.mem_support_iff.mpr hc)
    rw [RCN081.weight_fin4] at hw
    simp [xWeights] at hw
    omega
  · intro h d hd
    by_contra hm
    have hm' : d 0 < m := by
      rw [RCN081.weight_fin4] at hm
      simpa [xWeights] using hm
    have hc := congrArg (MvPolynomial.coeff d.tail) (h (d 0) hm')
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hc
    have he : Finsupp.cons (d 0) d.tail = d := by
      ext i
      fin_cases i <;> simp
    rw [he, MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc

def contactPolynomial (x u0 u1 : K) :
    Poly4 K →+* Polynomial (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.finSuccEquiv K 3).toRingHom.comp
    ((contactBlowup K).comp ((contactBlowup K).comp
      (localize K x u0 u1).toRingHom))

theorem contactAtLeast_iff_dvd (x u0 u1 : K) (m : ℕ) (P : Poly4 K) :
    ContactAtLeast K x u0 u1 m P ↔
      Polynomial.X ^ m ∣ contactPolynomial K x u0 u1 P := by
  change AtLeast localWeights m (localize K x u0 u1 P) ↔ _
  rw [← atLeast_contactBlowup_iff K m, ← atLeast_x_blowup K m,
    atLeast_x_iff_dvd K m]
  rfl

theorem blowup_ne_zero {P : Poly4 K} (hP : P ≠ 0) : contactBlowup K P ≠ 0 := by
  intro h
  have hs := congrArg MvPolynomial.support h
  rw [support_contactBlowup] at hs
  simp only [MvPolynomial.support_zero, Finset.image_eq_empty] at hs
  exact hP (MvPolynomial.support_eq_empty.mp hs)

def delocalize (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C x,
    MvPolynomial.X 1 - MvPolynomial.C u0 - MvPolynomial.X 3 * MvPolynomial.C u1 -
      MvPolynomial.X 2 * (MvPolynomial.X 0 - MvPolynomial.C x),
    MvPolynomial.X 2, MvPolynomial.X 3]

theorem delocalize_localize (x u0 u1 : K) (P : Poly4 K) :
    delocalize K x u0 u1 (localize K x u0 u1 P) = P := by
  have he : (delocalize K x u0 u1).comp (localize K x u0 u1) =
      AlgHom.id K (Poly4 K) := by
    ext i
    fin_cases i <;> simp [delocalize, localize, localVariables]
  exact DFunLike.congr_fun he P

theorem contactPolynomial_ne_zero (x u0 u1 : K) {P : Poly4 K} (hP : P ≠ 0) :
    contactPolynomial K x u0 u1 P ≠ 0 := by
  have hl : localize K x u0 u1 P ≠ 0 := by
    intro h
    have := congrArg (delocalize K x u0 u1) h
    rw [delocalize_localize, map_zero] at this
    exact hP this
  exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv K 3).injective).mpr
    (blowup_ne_zero K (blowup_ne_zero K hl))

def contactOrder (x u0 u1 : K) (P : Poly4 K) : ℕ :=
  (contactPolynomial K x u0 u1 P).natTrailingDegree

theorem contactAtLeast_iff_le (x u0 u1 : K) (m : ℕ) (P : Poly4 K) (hP : P ≠ 0) :
    ContactAtLeast K x u0 u1 m P ↔ m ≤ contactOrder K x u0 u1 P := by
  rw [contactAtLeast_iff_dvd, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hm
    have hz := h (contactOrder K x u0 u1 P) (by omega)
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr
      (contactPolynomial_ne_zero K x u0 u1 hP)) hz
  · intro h n hn
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    exact lt_of_lt_of_le hn h

theorem contactOrder_mul (x u0 u1 : K) (P Q : Poly4 K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    contactOrder K x u0 u1 (P * Q) =
      contactOrder K x u0 u1 P + contactOrder K x u0 u1 Q := by
  unfold contactOrder
  rw [map_mul, Polynomial.natTrailingDegree_mul
    (contactPolynomial_ne_zero K x u0 u1 hP)
    (contactPolynomial_ne_zero K x u0 u1 hQ)]

theorem contact_mul_iff (x u0 u1 : K) (m : ℕ) (P Q : Poly4 K) (hP : P ≠ 0) :
    ContactAtLeast K x u0 u1 m (P * Q) ↔
      ContactAtLeast K x u0 u1 (m - contactOrder K x u0 u1 P) Q := by
  by_cases hQ : Q = 0
  · subst Q
    simp [ContactAtLeast, AtLeast]
  rw [contactAtLeast_iff_le K x u0 u1 m _ (mul_ne_zero hP hQ),
    contactAtLeast_iff_le K x u0 u1 _ Q hQ, contactOrder_mul K x u0 u1 P Q hP hQ]
  omega

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open MvPolynomial ContactOrderBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def contactSubmodule (x u0 u1 : K) (m : ℕ) : Submodule K (Poly4 K) :=
  (MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight localWeights d}).comap
    (localize K x u0 u1).toLinearMap

theorem mem_contactSubmodule (x u0 u1 : K) (m : ℕ) (Q : Poly4 K) :
    Q ∈ contactSubmodule K x u0 u1 m ↔ ContactAtLeast K x u0 u1 m Q := by
  rfl

def factorMultiplication (F : Poly4 K) : Poly4 K →ₗ[K] Poly4 K where
  toFun Q := F * Q
  map_add' Q R := mul_add F Q R
  map_smul' a Q := by simp [MvPolynomial.smul_eq_C_mul, mul_left_comm]

theorem factorMultiplication_ker (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    LinearMap.ker ((contactSubmodule K x u0 u1 m).mkQ.comp
      (factorMultiplication K F)) =
        contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F) := by
  ext Q
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ContactAtLeast K x u0 u1 m (F * Q) ↔
    ContactAtLeast K x u0 u1 (m - contactOrder K x u0 u1 F) Q
  exact contact_mul_iff K x u0 u1 m F Q hF

def factorJetMap (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    (Poly4 K ⧸ contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)) →ₗ[K]
      (Poly4 K ⧸ contactSubmodule K x u0 u1 m) :=
  (contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)).liftQ
    ((contactSubmodule K x u0 u1 m).mkQ.comp (factorMultiplication K F))
    (by rw [factorMultiplication_ker K x u0 u1 m F hF])

theorem factorJetMap_injective (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    Function.Injective (factorJetMap K x u0 u1 m F hF) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [factorMultiplication_ker K x u0 u1 m F hF]

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open scoped BigOperators
open MvPolynomial ContactOrderBridge RCN122
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def RelativeContactAtLeast (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) : Prop :=
  ∃ B : Poly4 K, ContactAtLeast K x u0 u1 m (Q - F * B)

theorem relative_contact_iff_jet_range
    (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) (hF : F ≠ 0) :
    RelativeContactAtLeast K x u0 u1 m F Q ↔
      (contactSubmodule K x u0 u1 m).mkQ Q ∈
        LinearMap.range (factorJetMap K x u0 u1 m F hF) := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨Submodule.Quotient.mk B,?_⟩
    change (Submodule.Quotient.mk (F*B) : Poly4 K ⧸ contactSubmodule K x u0 u1 m) =
      Submodule.Quotient.mk Q
    symm
    exact (Submodule.Quotient.eq _).mpr hB
  · rintro ⟨q,hq⟩
    obtain ⟨B,rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨B,?_⟩
    apply (Submodule.Quotient.eq (contactSubmodule K x u0 u1 m)).mp
    exact hq.symm

theorem relative_contact_specialization_dvd
    (F Q : Poly4 K) (f : Polynomial K) (x u0 u1 gamma : K) (m : ℕ)
    (hF : specialization K f gamma F = 0)
    (hagrees : f.eval x = u0 + gamma * u1)
    (hcontact : RelativeContactAtLeast K x u0 u1 m F Q) :
    (Polynomial.X - Polynomial.C x)^m ∣ specialization K f gamma Q := by
  obtain ⟨B,hB⟩ := hcontact
  have ht := X_pow_dvd_taylor_specialization K (Q-F*B) f x u0 u1 gamma m hagrees
    ((contactAtLeast_iff_block_divisibility K x u0 u1 m (Q-F*B)).mp hB)
  simp only [map_sub, map_mul, hF, zero_mul, sub_zero] at ht
  exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
    (specialization K f gamma Q) x m).mpr (Polynomial.X_pow_dvd_iff.mp ht)

theorem relative_contact_specialization_eq_zero
    {I : Type*} (F Q : Poly4 K) (f : Polynomial K) (gamma : K)
    (nodes : I ↪ K) (u0 u1 : I → K) (support : Finset I) (m : I → ℕ)
    (hF : specialization K f gamma F = 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i + gamma * u1 i)
    (hcontact : ∀ i ∈ support,
      RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q)
    (hdegree : (specialization K f gamma Q).natDegree < ∑ i ∈ support, m i) :
    specialization K f gamma Q = 0 := by
  classical
  by_contra hne
  have hmult : ∀ i ∈ support, m i ≤
      (specialization K f gamma Q).rootMultiplicity (nodes i) := by
    intro i hi
    apply (Polynomial.le_rootMultiplicity_iff hne).mpr
    exact relative_contact_specialization_dvd K F Q f
      (nodes i) (u0 i) (u1 i) gamma (m i) hF (hagrees i hi) (hcontact i hi)
  have hsum : (∑ i ∈ support, m i) ≤ (specialization K f gamma Q).natDegree := by
    calc
      _ ≤ ∑ i ∈ support, (specialization K f gamma Q).rootMultiplicity (nodes i) :=
        Finset.sum_le_sum hmult
      _ = ∑ a ∈ support.map nodes, (specialization K f gamma Q).rootMultiplicity a :=
        (Finset.sum_map support nodes
          (fun a : K => (specialization K f gamma Q).rootMultiplicity a)).symm
      _ ≤ _ := @RCN355.sum_rootMultiplicity_le_natDegree K inferInstance (Classical.decEq K)
        (specialization K f gamma Q) (support.map nodes)
  omega

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.RelativeContactRank6814
open scoped BigOperators
open MvPolynomial RCN119
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

variable (K : Type*) [Field K]

def totalWeights : Fin 3 → ℕ := fun _ => 1

theorem coefficientBox_bounds (M L s : ℕ) (p : RCN119.Poly K) :
    p ∈ coefficientBox K M L s ↔
      p.degreeOf 0 ≤ M ∧ weightedTotalDegree totalWeights p ≤ L ∧ p.degreeOf 1 ≤ s := by
  classical
  rw [coefficientBox, MvPolynomial.mem_restrictSupport_iff K]
  constructor
  · intro hp
    refine ⟨MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hp hd).1), ?_,
      MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hp hd).2.2)⟩
    change p.support.sup (Finsupp.weight totalWeights) ≤ L
    apply Finset.sup_le
    intro d hd
    simpa [totalWeights, RCN372.weight_fin3] using (hp hd).2.1
  · rintro ⟨h0,ht,h1⟩ d hd
    have htot : Finsupp.weight totalWeights d ≤ L :=
      (Finset.le_sup (f := Finsupp.weight totalWeights) hd).trans ht
    exact ⟨MvPolynomial.degreeOf_le_iff.mp h0 d hd,
      by simpa [totalWeights, RCN372.weight_fin3] using htot,
      MvPolynomial.degreeOf_le_iff.mp h1 d hd⟩

theorem slope_degrees :
    (slopeDifference K).degreeOf 0 = 1 ∧
      weightedTotalDegree totalWeights (slopeDifference K) = 1 ∧
      (slopeDifference K).degreeOf 1 = 1 := by
  classical
  have hb := (coefficientBox_bounds K 1 1 1 _).mp (slopeDifference_mem_coefficientBox K)
  have h0 : Finsupp.single (0 : Fin 3) 1 ∈ (slopeDifference K).support := by
    simp [MvPolynomial.mem_support_iff, slopeDifference]
  have h1 : Finsupp.single (1 : Fin 3) 1 ∈ (slopeDifference K).support := by
    simp [MvPolynomial.mem_support_iff, slopeDifference]
  have hlo0 := MvPolynomial.degreeOf_le_iff.mp (le_refl ((slopeDifference K).degreeOf 0)) _ h0
  have hlo1 := MvPolynomial.degreeOf_le_iff.mp (le_refl ((slopeDifference K).degreeOf 1)) _ h1
  have hlot := Finset.le_sup (f := Finsupp.weight totalWeights) h0
  change Finsupp.weight totalWeights (Finsupp.single 0 1) ≤
    weightedTotalDegree totalWeights (slopeDifference K) at hlot
  simp only [Finsupp.single_eq_same] at hlo0 hlo1
  have hlot' : 1 ≤ weightedTotalDegree totalWeights (slopeDifference K) := by
    simpa [totalWeights, RCN372.weight_fin3] using hlot
  exact ⟨Nat.le_antisymm hb.1 hlo0, Nat.le_antisymm hb.2.1 hlot',
    Nat.le_antisymm hb.2.2 hlo1⟩

theorem slope_power_degrees (h : ℕ) :
    (slopeDifference K ^ h).degreeOf 0 = h ∧
      weightedTotalDegree totalWeights (slopeDifference K ^ h) = h ∧
      (slopeDifference K ^ h).degreeOf 1 = h := by
  have hd := slope_degrees K
  have ht : weightedTotalDegree totalWeights (slopeDifference K ^ h) = h := by
    induction h with
    | zero => simp [MvPolynomial.weightedTotalDegree]
    | succ h ih =>
        rw [pow_succ, RCN071.weightedTotalDegree_mul_fin3 _ _ _
          (pow_ne_zero h (slopeDifference_ne_zero K)) (slopeDifference_ne_zero K), ih, hd.2.1]
  refine ⟨?_,ht,?_⟩
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (slopeDifference_ne_zero K), hd.1, mul_one]
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (slopeDifference_ne_zero K), hd.2.2, mul_one]

theorem quotient_mem_coefficientBox {M L s h : ℕ} (q : RCN119.Poly K)
    (hq : slopeDifference K ^ h * q ∈ coefficientBox K M L s) :
    q ∈ coefficientBox K (M-h) (L-h) (s-h) := by
  by_cases hz : q = 0
  · rw [hz]; exact Submodule.zero_mem _
  have hn := pow_ne_zero h (slopeDifference_ne_zero K)
  have hb := (coefficientBox_bounds K M L s _).mp hq
  have hd := slope_power_degrees K h
  have h0 := hb.1
  have ht := hb.2.1
  have h1 := hb.2.2
  rw [MvPolynomial.degreeOf_mul_eq hn hz, hd.1] at h0
  rw [RCN071.weightedTotalDegree_mul_fin3 _ _ _ hn hz, hd.2.1] at ht
  rw [MvPolynomial.degreeOf_mul_eq hn hz, hd.2.2] at h1
  exact (coefficientBox_bounds K _ _ _ q).mpr ⟨by omega,by omega,by omega⟩

theorem kernelEmbedding_surjective {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Function.Surjective (kernelEmbedding K hM hL hs) := by
  intro p
  have hp : contactJet K h p.val.val = 0 := p.property
  obtain ⟨q,hq⟩ := (contactJet_eq_zero_iff K h p.val.val).mp hp
  have hmem : q ∈ coefficientBox K (M-h) (L-h) (s-h) := by
    apply quotient_mem_coefficientBox K q
    rw [← hq]
    exact p.val.property
  refine ⟨⟨q,hmem⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hq.symm

theorem blockJet_rank_add_quotient_finrank_eq {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) +
      Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) =
      Module.finrank K (coefficientBox K M L s) := by
  have he := (LinearEquiv.ofBijective (kernelEmbedding K hM hL hs)
    ⟨kernelEmbedding_injective K hM hL hs,kernelEmbedding_surjective K hM hL hs⟩).finrank_eq
  have hr := (blockJet K M L s h).finrank_range_add_finrank_ker
  omega

theorem blockJet_kernel_eq_bot_of_large (M L s h : ℕ) (hh : M < h ∨ s < h) :
    LinearMap.ker (blockJet K M L s h) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change p.val = 0
  by_contra hne
  have hz : contactJet K h p.val = 0 := hp
  obtain ⟨q,hq⟩ := (contactJet_eq_zero_iff K h p.val).mp hz
  have hqne : q ≠ 0 := by
    intro h
    apply hne
    rw [hq,h,mul_zero]
  have hn := pow_ne_zero h (slopeDifference_ne_zero K)
  have hb := (coefficientBox_bounds K M L s p.val).mp p.property
  have h0 := hb.1
  have h1 := hb.2.2
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(slope_power_degrees K h).1] at h0
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(slope_power_degrees K h).2.2] at h1
  omega

theorem blockJet_rank_eq_contactRankBound (M L s h : ℕ) (hML : M ≤ L) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) =
      contactRankBound M L s h := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL := hM.trans hML
      have he := blockJet_rank_add_quotient_finrank_eq K hM hL hs
      rw [coefficientBox_finrank_range K M L s hML,
        coefficientBox_finrank_range K (M-h) (L-h) (s-h) (Nat.sub_le_sub_right hML h)] at he
      have hm : M-h+1 = M+1-h := by omega
      have hl : L-h+1 = L+1-h := by omega
      have hs' : s-h+1 = s+1-h := by omega
      simp only [hm,hl,hs'] at he
      unfold contactRankBound blockInputCount blockKernelLowerBound
      omega
    · have hk := blockJet_kernel_eq_bot_of_large K M L s h (Or.inr (by omega))
      have he := (blockJet K M L s h).finrank_range_add_finrank_ker
      rw [hk,finrank_bot,Nat.add_zero] at he
      rw [coefficientBox_finrank_range K M L s hML] at he
      have hz : s+1-h=0 := by omega
      simpa [contactRankBound,blockInputCount,blockKernelLowerBound,hz] using he
  · have hk := blockJet_kernel_eq_bot_of_large K M L s h (Or.inl (by omega))
    have he := (blockJet K M L s h).finrank_range_add_finrank_ker
    rw [hk,finrank_bot,Nat.add_zero] at he
    rw [coefficientBox_finrank_range K M L s hML] at he
    have hz : M+1-h=0 := by omega
    simpa [contactRankBound,blockInputCount,blockKernelLowerBound,hz] using he

theorem localTarget_finrank_eq (m L s : ℕ) :
    Module.finrank K (RCN100.LocalTarget K m L s) = localRankBound m L s := by
  change Module.finrank K ((r : Fin m) → LinearMap.range
    (blockJet K (min r.val L) L s (m-r.val))) = _
  rw [Module.finrank_pi_fintype]
  unfold localRankBound
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [blockJet_rank_eq_contactRankBound K _ _ _ _ (min_le_right _ _),
    RCN100.full_contactRankBound_eq]

end
end ProximityPrize.SubmissionLower.RelativeContactRank6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def unpackExponent (r : ℕ) (d : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.cons (r-d 0) d

theorem monomial3_eq (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 *
        MvPolynomial.X 1 ^ d 1 * MvPolynomial.X 2 ^ d 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem translated_unpack_monomial (r : ℕ) (d : Fin 3 →₀ ℕ) (a : K)
    (hd : d 0 ≤ r) :
    homogenizedTranslation K 0 0 0 (MvPolynomial.monomial (unpackExponent r d) a) =
      Polynomial.monomial r (MvPolynomial.monomial d a) := by
  rw [RCN122.monomial_eq K, monomial3_eq K,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow]
  simp [unpackExponent, homogenizedTranslation, translationVariables, seedAffine,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, mul_pow]
  simp only [show (Finsupp.cons (r-d 0) d) (1 : Fin 4) = d 0 from rfl,
    show (Finsupp.cons (r-d 0) d) (2 : Fin 4) = d 1 from rfl,
    show (Finsupp.cons (r-d 0) d) (3 : Fin 4) = d 2 from rfl]
  conv_rhs => rw [show r = (r-d 0)+d 0 by omega, pow_add]
  ring

def unpackBlock (r : ℕ) : RCN119.Poly K →ₗ[K] Poly4 K :=
  (MvPolynomial.basisMonomials (Fin 3) K).constr K
    (fun d => MvPolynomial.monomial (unpackExponent r d) 1)

theorem unpackBlock_apply (r : ℕ) (p : RCN119.Poly K) :
    unpackBlock K r p = ∑ d ∈ p.support,
      p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1 : K) := by
  rw [unpackBlock, Module.Basis.constr_apply]
  rfl

theorem translated_unpackBlock (r : ℕ) (p : RCN119.Poly K)
    (hp : p.degreeOf 0 ≤ r) :
    homogenizedTranslation K 0 0 0 (unpackBlock K r p) = Polynomial.monomial r p := by
  classical
  rw [unpackBlock_apply, map_sum]
  have he : ∀ d ∈ p.support,
      homogenizedTranslation K 0 0 0
          (p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1 : K)) =
        Polynomial.monomial r (MvPolynomial.monomial d (p.coeff d)) := by
    intro d hd
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact translated_unpack_monomial K r d (p.coeff d)
      (MvPolynomial.degreeOf_le_iff.mp hp d hd)
  rw [Finset.sum_congr rfl he]
  conv_rhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum]

theorem unpackBlock_mem (m L s : ℕ) (r : Fin m)
    (p : coefficientBox K (min r.val L) L s) :
    unpackBlock K r.val p.val ∈ globalCoefficientBox K m 1 L s := by
  classical
  rw [unpackBlock_apply]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
  left
  have hb := p.property hd
  change d 0 ≤ min r.val L ∧ d 0+d 1+d 2 ≤ L ∧ d 1 ≤ s at hb
  change d 0+d 1+d 2 ≤ L ∧ d 1 ≤ s ∧ (r.val-d 0)+1*d 0+(1-1)*d 1 < m
  have hr := r.isLt
  omega

abbrev LocalSource (m L s : ℕ) :=
  (r : Fin m) → coefficientBox K (min r.val L) L s

def unpack (m L s : ℕ) : LocalSource K m L s →ₗ[K] Poly4 K where
  toFun p := ∑ r : Fin m, unpackBlock K r.val (p r).val
  map_add' p q := by simp [map_add, Finset.sum_add_distrib]
  map_smul' a p := by simp [map_smul, Finset.smul_sum]

theorem unpack_mem (m L s : ℕ) (p : LocalSource K m L s) :
    unpack K m L s p ∈ globalCoefficientBox K m 1 L s := by
  change (∑ r : Fin m, unpackBlock K r.val (p r).val) ∈ _
  apply Submodule.sum_mem
  intro r _
  exact unpackBlock_mem K m L s r (p r)

theorem translated_unpack (m L s : ℕ) (p : LocalSource K m L s) :
    homogenizedTranslation K 0 0 0 (unpack K m L s p) =
      ∑ r : Fin m, Polynomial.monomial r.val (p r).val := by
  change homogenizedTranslation K 0 0 0 (∑ r : Fin m, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply translated_unpackBlock
  exact ((coefficientBox_bounds K _ _ _ _).mp (p r).property).1.trans (min_le_left _ _)

theorem translated_unpack_coeff (m L s : ℕ) (p : LocalSource K m L s) (r : Fin m) :
    (homogenizedTranslation K 0 0 0 (unpack K m L s p)).coeff r.val = (p r).val := by
  classical
  rw [translated_unpack, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Fin.val_inj]
  simp

def sourceJet (m L s : ℕ) : LocalSource K m L s →ₗ[K] LocalTarget K m L s :=
  LinearMap.pi fun r =>
    (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp (LinearMap.proj r)

theorem sourceJet_surjective (m L s : ℕ) :
    Function.Surjective (sourceJet K m L s) := by
  classical
  intro v
  choose p hp using fun r => (v r).property
  refine ⟨p,?_⟩
  funext r
  apply Subtype.ext
  exact hp r

theorem sourceJet_eq_zero_iff (m L s : ℕ) (p : LocalSource K m L s) :
    sourceJet K m L s p = 0 ↔ ContactAtLeast K 0 0 0 m (unpack K m L s p) := by
  rw [contactAtLeast_iff_block_divisibility]
  constructor
  · intro h n
    by_cases hn : n < m
    · have hr := congrArg (fun v : LocalTarget K m L s => (v ⟨n,hn⟩).val) h
      have hz : contactJet K (m-n) (p ⟨n,hn⟩).val = 0 := hr
      rw [translated_unpack_coeff K m L s p ⟨n,hn⟩]
      exact (contactJet_eq_zero_iff K (m-n) _).mp hz
    · simp [show m-n=0 by omega]
  · intro h
    funext r
    apply Subtype.ext
    change contactJet K (m-r.val) (p r).val = 0
    apply (contactJet_eq_zero_iff K (m-r.val) _).mpr
    have hr := h r.val
    rw [translated_unpack_coeff] at hr
    exact hr

def boundedJetMap (m L s : ℕ) : LocalSource K m L s →ₗ[K]
    (Poly4 K ⧸ contactSubmodule K 0 0 0 m) :=
  (contactSubmodule K 0 0 0 m).mkQ.comp (unpack K m L s)

theorem boundedJetMap_ker (m L s : ℕ) :
    LinearMap.ker (boundedJetMap K m L s) = LinearMap.ker (sourceJet K m L s) := by
  ext p
  simp only [LinearMap.mem_ker]
  change ((contactSubmodule K 0 0 0 m).mkQ (unpack K m L s p) = 0) ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_contactSubmodule,
    ← sourceJet_eq_zero_iff]

theorem boundedJetMap_finrank (m L s : ℕ) :
    Module.finrank K (LinearMap.range (boundedJetMap K m L s)) = localRankBound m L s := by
  have hfull := LinearMap.range_eq_top.mpr (sourceJet_surjective K m L s)
  have hs := (sourceJet K m L s).finrank_range_add_finrank_ker
  rw [hfull, finrank_top, localTarget_finrank_eq] at hs
  have hb := (boundedJetMap K m L s).finrank_range_add_finrank_ker
  rw [boundedJetMap_ker] at hb
  omega

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators Pointwise
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RCN180 (encodeBox reconstruct_encodeBox)
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def blocksOf {D w L s : ℕ} (m : ℕ) (Q : globalCoefficientBox K D w L s) :
    LocalSource K m L s :=
  fun r => extractBlock K D w L s 0 0 0 r.val (encodeBox Q)

theorem blocksOf_coeff {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) (r : Fin m) :
    (blocksOf K m Q r).val = (homogenizedTranslation K 0 0 0 Q.val).coeff r.val := by
  rw [← reconstruct_encodeBox Q, translation_reconstruct_coeff]
  rfl

theorem contact_unpack_blocksOf {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) :
    ContactAtLeast K 0 0 0 m (Q.val-unpack K m L s (blocksOf K m Q)) := by
  rw [contactAtLeast_iff_block_divisibility]
  intro r
  by_cases hr : r < m
  · rw [map_sub, Polynomial.coeff_sub, translated_unpack_coeff K m L s _ ⟨r,hr⟩,
      blocksOf_coeff, sub_self]
    exact dvd_zero _
  · simp [show m-r=0 by omega]

theorem jet_mem_range_of_globalBox {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) :
    (contactSubmodule K 0 0 0 m).mkQ Q.val ∈ LinearMap.range (boundedJetMap K m L s) := by
  refine ⟨blocksOf K m Q,?_⟩
  change (Submodule.Quotient.mk (unpack K m L s (blocksOf K m Q)) :
      Poly4 K ⧸ contactSubmodule K 0 0 0 m) = Submodule.Quotient.mk Q.val
  symm
  exact (Submodule.Quotient.eq _).mpr (contact_unpack_blocksOf K m Q)

theorem globalBox_mul {D L s D' L' s' : ℕ} {F Q : Poly4 K}
    (hF : F ∈ globalCoefficientBox K D 1 L s)
    (hQ : Q ∈ globalCoefficientBox K D' 1 L' s') :
    F*Q ∈ globalCoefficientBox K (D+D') 1 (L+L') (s+s') := by
  have hset : globalExponents D 1 L s + globalExponents D' 1 L' s' ⊆
      globalExponents (D+D') 1 (L+L') (s+s') := by
    rintro _ ⟨a,ha,b,hb,rfl⟩
    simp only [globalExponents, Set.mem_setOf_eq, Finsupp.add_apply,
      Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at ha hb ⊢
    omega
  change F*Q ∈ MvPolynomial.restrictSupport K _
  apply MvPolynomial.restrictSupport_mono (R:=K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hF hQ

theorem globalBox_mono_total_slope {D L s L' s' : ℕ}
    (hL : L ≤ L') (hs : s ≤ s') :
    globalCoefficientBox K D 1 L s ≤ globalCoefficientBox K D 1 L' s' := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1.trans hL,hd.2.1.trans hs,hd.2.2⟩

theorem factorJetMap_mem_bounded
    {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF)
    (hT : TF ≤ L) (hR : RF ≤ s)
    (v : LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))) :
    factorJetMap K 0 0 0 m F hF v.val ∈ LinearMap.range (boundedJetMap K m L s) := by
  obtain ⟨q,hq⟩ := v.property
  rw [← hq]
  change (contactSubmodule K 0 0 0 m).mkQ
    (F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q) ∈ _
  apply jet_mem_range_of_globalBox K (D:=DF+(m-contactOrder K 0 0 0 F))
    (w:=1) (L:=L) (s:=s) m
    ⟨F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q,?_⟩
  exact globalBox_mono_total_slope K (L':=L) (s':=s) (by omega) (by omega)
    (globalBox_mul K hbox (unpack_mem K _ _ _ q))

def boundedFactorMap {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF)) →ₗ[K]
      LinearMap.range (boundedJetMap K m L s) :=
  LinearMap.codRestrict _
    ((factorJetMap K 0 0 0 m F hF).comp
      (LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))).subtype)
    (factorJetMap_mem_bounded K F hF hbox hT hR)

theorem boundedFactorMap_injective {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    Function.Injective (boundedFactorMap K (m:=m) F hF hbox hT hR) := by
  intro a b hab
  apply Subtype.ext
  apply factorJetMap_injective K 0 0 0 m F hF
  exact congrArg Subtype.val hab

abbrev RelativeJetTarget {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :=
  LinearMap.range (boundedJetMap K m L s) ⧸
    LinearMap.range (boundedFactorMap K (m:=m) F hF hbox hT hR)

theorem relativeJetTarget_finrank {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    Module.finrank K (RelativeJetTarget K (m:=m) F hF hbox hT hR) =
      localRankBound m L s -
        localRankBound (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) := by
  have hi := LinearMap.finrank_range_of_inj
    (boundedFactorMap_injective K (m:=m) F hF hbox hT hR)
  rw [boundedJetMap_finrank] at hi
  have hq := (LinearMap.range
    (boundedFactorMap K (m:=m) F hF hbox hT hR)).finrank_quotient_add_finrank
  rw [hi, boundedJetMap_finrank] at hq
  change Module.finrank K (RelativeJetTarget K (m:=m) F hF hbox hT hR) + _ = _ at hq
  omega

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt wt_C wt_X wt_add_le wt_mul_le wt_pow_le)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def center (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0+MvPolynomial.C x,
    MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1,
    MvPolynomial.X 2, MvPolynomial.X 3]

theorem center_inverse (x u0 u1 : K) (Q : Poly4 K) :
    center K (-x) (-u0) (-u1) (center K x u0 u1 Q) = Q := by
  have he : (center K (-x) (-u0) (-u1)).comp (center K x u0 u1) =
      AlgHom.id K (Poly4 K) := by
    ext i
    fin_cases i <;> simp [center] <;> ring
  exact DFunLike.congr_fun he Q

theorem center_ne_zero (x u0 u1 : K) {Q : Poly4 K} (hQ : Q ≠ 0) :
    center K x u0 u1 Q ≠ 0 := by
  intro h
  have hc := congrArg (center K (-x) (-u0) (-u1)) h
  rw [center_inverse, map_zero] at hc
  exact hQ hc

theorem center_contact (x u0 u1 : K) (m : ℕ) (Q : Poly4 K) :
    ContactAtLeast K 0 0 0 m (center K x u0 u1 Q) ↔
      ContactAtLeast K x u0 u1 m Q := by
  have he : (localize K 0 0 0).comp (center K x u0 u1) = localize K x u0 u1 := by
    ext i
    fin_cases i <;> simp [center,localize,localVariables] <;> ring
  unfold ContactAtLeast
  rw [show localize K 0 0 0 (center K x u0 u1 Q) = localize K x u0 u1 Q from
    DFunLike.congr_fun he Q]

theorem center_contactOrder (x u0 u1 : K) (Q : Poly4 K) (hQ : Q ≠ 0) :
    contactOrder K 0 0 0 (center K x u0 u1 Q) = contactOrder K x u0 u1 Q := by
  apply Nat.le_antisymm
  · apply (contactAtLeast_iff_le K x u0 u1 _ Q hQ).mp
    apply (center_contact K x u0 u1 _ Q).mp
    exact (contactAtLeast_iff_le K 0 0 0 _ _ (center_ne_zero K x u0 u1 hQ)).mpr le_rfl
  · apply (contactAtLeast_iff_le K 0 0 0 _ _ (center_ne_zero K x u0 u1 hQ)).mp
    apply (center_contact K x u0 u1 _ Q).mpr
    exact (contactAtLeast_iff_le K x u0 u1 _ Q hQ).mpr le_rfl

theorem algHom_weight_le (phi : Poly4 K →ₐ[K] Poly4 K) (w : Fin 4 → ℕ)
    (hvar : ∀ i, wt w (phi (MvPolynomial.X i)) ≤ w i) (Q : Poly4 K) :
    wt w (phi Q) ≤ wt w Q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q, map_sum]
  apply RCN235.wt_finset_sum_le
  intro d hd
  have hp (i : Fin 4) : wt w (phi (MvPolynomial.X i)^d i) ≤ d i*w i :=
    (wt_pow_le w _ _).trans (Nat.mul_le_mul_left _ (hvar i))
  have hm := wt_mul_le w (MvPolynomial.C (Q.coeff d)) (phi (MvPolynomial.X 0)^d 0)
  have hm1 := wt_mul_le w (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0)
    (phi (MvPolynomial.X 1)^d 1)
  have hm2 := wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1)
    (phi (MvPolynomial.X 2)^d 2)
  have hm3 := wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1*
      phi (MvPolynomial.X 2)^d 2) (phi (MvPolynomial.X 3)^d 3)
  have hc : phi (MvPolynomial.C (Q.coeff d)) = MvPolynomial.C (Q.coeff d) := phi.commutes _
  rw [RCN122.monomial_eq K, map_mul, map_mul, map_mul, map_mul, hc]
  simp only [map_pow]
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  rw [wt_C] at hm
  have hbound := MvPolynomial.le_weightedTotalDegree w hd
  rw [RCN081.weight_fin4] at hbound
  change _ ≤ wt w Q at hbound
  omega

theorem center_weight_le (x u0 u1 : K) (w : Fin 4 → ℕ) (hw : w 3 ≤ w 1) (Q : Poly4 K) :
    wt w (center K x u0 u1 Q) ≤ wt w Q := by
  apply algHom_weight_le
  intro i
  simp only [center, MvPolynomial.aeval_X]
  fin_cases i
  · change wt w (MvPolynomial.X 0+MvPolynomial.C x) ≤ w 0
    exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
  · change wt w (MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1) ≤ w 1
    apply (wt_add_le w _ _).trans
    apply max_le
    · exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
    · exact (wt_mul_le w _ _).trans (by simpa [wt_X,wt_C] using hw)
  · change wt w (MvPolynomial.X 2 : Poly4 K) ≤ w 2
    rw [wt_X]
  · change wt w (MvPolynomial.X 3 : Poly4 K) ≤ w 3
    rw [wt_X]

theorem center_globalBox {D w L s : ℕ} (x u0 u1 : K)
    (Q : globalCoefficientBox K D w L s) :
    center K x u0 u1 Q.val ∈ globalCoefficientBox K D w L s := by
  by_cases hz : Q.val = 0
  · rw [hz,map_zero]; exact Submodule.zero_mem _
  obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hz
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) (Q.property hd).2.2
  have hb := (RCN180.mem_flagGlobalCoefficientBox_iff Q.val D w L s hD).mp Q.property
  apply (RCN180.mem_flagGlobalCoefficientBox_iff _ D w L s hD).mpr
  refine ⟨(center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.1,
    (center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.2.1,
    (center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.2.2⟩
  all_goals simp [RCN156.residualTotalWeights,RCN156.residualSWeights,RCN081.contactWeights]

theorem center_relativeContact (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) :
    RelativeContactAtLeast K 0 0 0 m (center K x u0 u1 F) (center K x u0 u1 Q) ↔
      RelativeContactAtLeast K x u0 u1 m F Q := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨center K (-x) (-u0) (-u1) B,?_⟩
    apply (center_contact K x u0 u1 m _).mp
    rw [map_sub,map_mul]
    have he : center K x u0 u1 (center K (-x) (-u0) (-u1) B) = B := by
      simpa using center_inverse K (-x) (-u0) (-u1) B
    rw [he]
    exact hB
  · rintro ⟨B,hB⟩
    refine ⟨center K x u0 u1 B,?_⟩
    rw [← map_mul,← map_sub]
    exact (center_contact K x u0 u1 m _).mpr hB

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def NodeTarget {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :=
  RelativeJetTarget K (m:=m) (center K x u0 u1 F) (center_ne_zero K x u0 u1 hF)
    (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR

local instance nodeTargetAddCommGroup {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : AddCommGroup (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (AddCommGroup (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetModule {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : Module K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (Module K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetFinite {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : Module.Finite K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (Module.Finite K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

theorem nodeTarget_finrank {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :
    Module.finrank K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) =
      localRankBound m L s-localRankBound (m-contactOrder K x u0 u1 F) (L-TF) (s-RF) := by
  change Module.finrank K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR) = _
  rw [relativeJetTarget_finrank, center_contactOrder K x u0 u1 F hF]

def nodeJet (D w L s m : ℕ) (x u0 u1 : K) :
    globalCoefficientBox K D w L s →ₗ[K] LinearMap.range (boundedJetMap K m L s) :=
  LinearMap.codRestrict _
    ((contactSubmodule K 0 0 0 m).mkQ.comp
      ((center K x u0 u1).toLinearMap.comp (globalCoefficientBox K D w L s).subtype))
    (fun Q => jet_mem_range_of_globalBox K m ⟨center K x u0 u1 Q.val,
      center_globalBox K x u0 u1 Q⟩)

def nodeConstraint {DF TF RF m L s : ℕ} (D w : ℕ) (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :
    globalCoefficientBox K D w L s →ₗ[K] NodeTarget K (m:=m) F hF hbox hT hR x u0 u1 :=
  (LinearMap.range (boundedFactorMap K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ.comp
      (nodeJet K D w L s m x u0 u1)

theorem nodeConstraint_zero_contact {DF TF RF m L s D w : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) (Q : globalCoefficientBox K D w L s)
    (hQ : nodeConstraint K (m:=m) D w F hF hbox hT hR x u0 u1 Q = 0) :
    RelativeContactAtLeast K x u0 u1 m F Q.val := by
  apply (center_relativeContact K x u0 u1 m F Q.val).mp
  apply (relative_contact_iff_jet_range K 0 0 0 m _ _
    (center_ne_zero K x u0 u1 hF)).mpr
  change (LinearMap.range (boundedFactorMap K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ
      (nodeJet K D w L s m x u0 u1 Q) = 0 at hQ
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hQ
  obtain ⟨v,hv⟩ := hQ
  exact ⟨v.val,congrArg Subtype.val hv⟩

def relativeConstraints {I : Type*} [Fintype I] {DF TF RF L s : ℕ}
    (D w : ℕ) (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (nodes u0 u1 : I → K) (m : I → ℕ) :
    globalCoefficientBox K D w L s →ₗ[K]
      ((i : I) → NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)) :=
  LinearMap.pi fun i => nodeConstraint K (m:=m i) D w F hF hbox hT hR (nodes i) (u0 i) (u1 i)

theorem relativeConstraints_zero_contact {I : Type*} [Fintype I] {DF TF RF L s D w : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (nodes u0 u1 : I → K) (m : I → ℕ) (Q : globalCoefficientBox K D w L s)
    (hQ : relativeConstraints K D w F hF hbox hT hR nodes u0 u1 m Q = 0) :
    ∀ i, RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q.val := by
  intro i
  exact nodeConstraint_zero_contact K F hF hbox hT hR (nodes i) (u0 i) (u1 i) Q
    (congrFun hQ i)

set_option maxHeartbeats 300000 in
private theorem exists_not_dvd_kernel
    {W : Type*} [AddCommGroup W] [Module K W] [Module.Finite K W]
    {TF RF D w L s nu : ℕ}
    (A : globalCoefficientBox K D w L s →ₗ[K] W)
    (F : Poly4 K) (hF : F ≠ 0)
    (hcode : nu ≤ wt (RCN081.contactWeights w) F)
    (htotal : TF ≤ wt RCN156.residualTotalWeights F)
    (hslope : RF ≤ wt RCN156.residualSWeights F)
    (hdim : coefficientCount (D-nu) w (L-TF) (s-RF) +
      Module.finrank K W < coefficientCount D w L s) :
    ∃ Q : globalCoefficientBox K D w L s, ¬ F ∣ Q.val ∧ A Q = 0 := by
  classical
  let V := LinearMap.ker A
  let recon : V →ₗ[K] Poly4 K := (globalCoefficientBox K D w L s).subtype.comp V.subtype
  have hrecon : Function.Injective recon := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  by_contra hnone
  have hdiv : ∀ v : V, F ∣ recon v := by
    intro v
    by_contra hv
    apply hnone
    exact ⟨v.val,hv,v.property⟩
  have hquot (v : V) : RCN180.quotientPolynomial recon F hdiv v ∈
      globalCoefficientBox K (D-nu) w (L-TF) (s-RF) := by
    let R := RCN180.quotientPolynomial recon F hdiv v
    have he : recon v = F*R := RCN180.recon_eq_mul_quotientPolynomial recon F hdiv v
    by_cases hz : R = 0
    · change R ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    have hn : recon v ≠ 0 := by rw [he]; exact mul_ne_zero hF hz
    exact RCN180.quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) F R D w L s nu TF RF hn hF hz v.val.property he hcode htotal hslope
  letI : Module.Finite K (globalCoefficientBox K (D-nu) w (L-TF) (s-RF)) :=
    RCN180.globalCoefficientBoxFinite (K:=K) (D-nu) w (L-TF) (s-RF)
  let divMap : V →ₗ[K] globalCoefficientBox K (D-nu) w (L-TF) (s-RF) :=
    LinearMap.codRestrict _ (RCN180.quotientLinear (K:=K) (V:=V) recon F hF hdiv)
      (fun v => by
        change RCN180.quotientPolynomial recon F hdiv v ∈ _
        exact hquot v)
  have hdivMap : Function.Injective divMap := by
    intro a b hab
    apply RCN180.quotientLinear_injective recon hrecon F hF hdiv
    exact congrArg Subtype.val hab
  have hupper : Module.finrank K V ≤
      Module.finrank K (globalCoefficientBox K (D-nu) w (L-TF) (s-RF)) :=
    LinearMap.finrank_le_finrank_of_injective (f:=divMap) hdivMap
  have hupperCount : Module.finrank K V ≤ coefficientCount (D-nu) w (L-TF) (s-RF) :=
    hupper.trans_eq (RCN180.globalCoefficientBox_finrank (K:=K) (D-nu) w (L-TF) (s-RF))
  have hnull : Module.finrank K A.range + Module.finrank K A.ker = coefficientCount D w L s :=
    A.finrank_range_add_finrank_ker.trans (RCN180.globalCoefficientBox_finrank (K:=K) D w L s)
  have hrange := A.range.finrank_le
  change Module.finrank K A.ker ≤ _ at hupperCount
  have hcount : coefficientCount D w L s ≤
      coefficientCount (D-nu) w (L-TF) (s-RF) + Module.finrank K W := by
    rw [← hnull]
    exact (Nat.add_le_add hrange hupperCount).trans_eq (Nat.add_comm _ _)
  exact (Nat.not_le_of_gt hdim) hcount

theorem exists_proper_relative_helper
    {I : Type*} [Fintype I] {DF TF RF D w L s nu : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (hcode : nu ≤ wt (RCN081.contactWeights w) F)
    (htotal : TF ≤ wt RCN156.residualTotalWeights F)
    (hslope : RF ≤ wt RCN156.residualSWeights F)
    (nodes u0 u1 : I → K) (m : I → ℕ)
    (hdim : coefficientCount (D-nu) w (L-TF) (s-RF) +
      (∑ i : I, (localRankBound (m i) L s-
        localRankBound (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF))) <
      coefficientCount D w L s) :
    ∃ Q : Poly4 K, Q ∈ globalCoefficientBox K D w L s ∧ ¬ F ∣ Q ∧
      ∀ i, RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q := by
  classical
  let W := (i : I) → NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have htarget : Module.finrank K W =
      ∑ i : I, (localRankBound (m i) L s-
        localRankBound (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF)) := by
    change Module.finrank K ((i : I) → NodeTarget K (m:=m i) F hF hbox hT hR
      (nodes i) (u0 i) (u1 i)) = _
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact nodeTarget_finrank K F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have hd : coefficientCount (D-nu) w (L-TF) (s-RF) + Module.finrank K W <
      coefficientCount D w L s := by rw [htarget]; exact hdim
  obtain ⟨Q,hproper,hQ⟩ := exists_not_dvd_kernel K
    (relativeConstraints K D w F hF hbox hT hR nodes u0 u1 m) F hF hcode htotal hslope hd
  exact ⟨Q.val,Q.property,hproper,
    relativeConstraints_zero_contact K F hF hbox hT hR nodes u0 u1 m Q hQ⟩

end
end ProximityPrize.SubmissionLower.RelativeBounded6814
end MergedPart7
