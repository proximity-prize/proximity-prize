import ProximityPrize.SubmissionLower.Primary82170

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

namespace TaperNormalize

noncomputable section

open K1_13 K1_13_2 K1_13_2_2
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

def blockExponents (k : ℕ) (i : BlockIndex) : Set SourceExponent :=
  {e | e ∈ K1_13_2.blockExponents i ∧ e (some 1) + e (some 2) + e (some 3) ≤ k}

def BlockSpace (k : ℕ) (i : BlockIndex) : Submodule Geom SourcePolynomial :=
  restrictSupport Geom (blockExponents k i)

instance (k : ℕ) (i : BlockIndex) : Module.Finite Geom (BlockSpace k i) :=
  restrictSupport_finite (sourceExponents_finite.subset (fun _ h => h.1.1))

def originBlock (k : ℕ) (i : BlockIndex) : BlockSpace k i →ₗ[Geom] Local :=
  (localConstraintAt 3000 0 0).domRestrict (BlockSpace k i)

variable (k : ℕ)
private def residualDegree (k : ℕ) (i : BlockIndex) : ℕ := min i.1.val k

def activeFlag (i : BlockIndex) : Flag :=
  {K1_13_2_2.activeFlag i with degree := (residualDegree k i : ℤ)}

private theorem active_degree (i : BlockIndex) :
    (activeFlag k i).degree = (residualDegree k i : ℤ) := by
  rfl
private def removed (i : BlockIndex) : ℕ := i.1.val - residualDegree k i
private def stripped (i : BlockIndex) (e : SourceExponent) : JetExp :=
  Finsupp.equivFunOnFinite.symm
    ![e (some 0) - removed k i, e (some 1), e (some 2), e (some 3)]
private theorem source_grade (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]
private theorem source_index (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]
private theorem removed_le (i : BlockIndex) (e : blockExponents k i) :
    removed k i ≤ e.val (some 0) := by
  have hd := e.property.1.2.2.1
  have hcap := e.property.2
  rw [source_grade] at hd
  simp only [removed, residualDegree]
  omega
private theorem stripped_mem (i : BlockIndex) (e : blockExponents k i) :
    stripped k i e ∈ oldExponents (activeFlag k i) := by
  have hd := e.property.1.2.2.1
  have hj := e.property.1.1.2.1
  have hc := e.property.1.1.2.2.1
  have hx := e.property.1.2.1
  have hg := e.property.1.2.2.2
  have ha := removed_le k i e
  rw [source_grade] at hd
  rw [source_index] at hj hg
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight, Pi.single_apply,
    smul_eq_mul] at hc
  change ((stripped k i e).weight gradeWeight : ℤ) = (activeFlag k i).degree ∧
    -offset i ≤ ((stripped k i e).weight oldWeight : ℤ) ∧
    ((stripped k i e).weight oldWeight : ℤ) ≤ min 1650 (2999 - offset i) ∧
    ((stripped k i e) 3 : ℤ) ≤ 550
  rw [active_degree]
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, oldWeight, stripped,
    smul_eq_mul, Nat.mul_comm]
  simp only [removed, residualDegree] at *
  omega
private def encodeColumn (i : BlockIndex) (e : blockExponents k i) : oldSpace (activeFlag k i) := by
  refine ⟨monomial (stripped k i e) 1, ?_⟩
  change monomial (stripped k i e) 1 ∈ restrictSupport Geom (oldExponents (activeFlag k i))
  exact (monomial_mem_restrictSupport Geom).mpr (Or.inl (stripped_mem k i e))
private def encode (i : BlockIndex) : BlockSpace k i →ₗ[Geom] oldSpace (activeFlag k i) :=
  (basisRestrictSupport Geom (blockExponents k i)).constr Geom (encodeColumn k i)
private theorem encode_basis (i : BlockIndex) (e : blockExponents k i) :
    ((encode k i (basisRestrictSupport Geom (blockExponents k i) e)) : JetPoly) =
      monomial (stripped k i e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport Geom (blockExponents k i)).constr_basis Geom (encodeColumn k i) e)
local notation "T" => (MvPolynomial.X (localT 3) : Local)
local notation "E" => (MvPolynomial.X (localE 3) : Local)
private def jetVar (j : Fin 3) : Local := MvPolynomial.X (localY j)
private def valueImage : Local := unscaledLocalImage 3 0 0 (some 0)
private def scaledImage : Fin 4 → Local :=
  ![T * E, T * jetVar 0, T ^ 2 * jetVar 1, T ^ 3 * jetVar 2]
private def originSubst : SourcePolynomial →ₐ[Geom] Local := unscaledLocalSubstitution 3 0 0
private theorem scaled_shear_zero : bind₁ scaledImage (shearImage 0) = valueImage := by
  simp [shearImage, scaledImage, valueImage, unscaledLocalImage, localCorrection, Fin.sum_univ_three, jetVar]
  ring
private theorem scaled_shear_succ (j : Fin 3) :
    bind₁ scaledImage (shearImage j.succ) = T ^ j.succ.val * jetVar j := by
  fin_cases j <;> simp [shearImage, scaledImage]
private theorem bind_monomial_one {σ τ : Type*} [Fintype σ]
    (f : σ → MvPolynomial τ Geom) (e : σ →₀ ℕ) :
    bind₁ f (monomial e 1) = ∏ j, f j ^ e j := by
  rw [bind₁_monomial, C_1, one_mul]
  exact Finsupp.prod_fintype e (fun j n => f j ^ n) (fun _ => pow_zero _)
private theorem origin_monomial (e : SourceExponent) :
    originSubst (monomial e 1) = T ^ e none *
      (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) := by
  rw [originSubst, unscaledLocalSubstitution, bind_monomial_one, Fintype.prod_option, Fin.prod_univ_four]
  change (C (0 : Geom) + T) ^ e none *
    (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) = _
  simp
private theorem stripped_monomial (i : BlockIndex) (e : SourceExponent) :
    bind₁ scaledImage (coordinateChange (monomial (stripped k i e) 1)) =
    valueImage ^ (e (some 0) - removed k i) *
      (T * jetVar 0) ^ e (some 1) * (T ^ 2 * jetVar 1) ^ e (some 2) * (T ^ 3 * jetVar 2) ^ e (some 3) := by
  rw [coordinateChange, bind₁_bind₁, bind_monomial_one, Fin.prod_univ_four]
  have h1 := scaled_shear_succ (0 : Fin 3)
  have h2 := scaled_shear_succ (1 : Fin 3)
  have h3 := scaled_shear_succ (2 : Fin 3)
  change bind₁ scaledImage (shearImage 1) = T ^ 1 * jetVar 0 at h1
  change bind₁ scaledImage (shearImage 2) = T ^ 2 * jetVar 1 at h2
  change bind₁ scaledImage (shearImage 3) = T ^ 3 * jetVar 2 at h3
  simp [scaled_shear_zero, h1, h2, h3, stripped]
private theorem shifted_origin_monomial (i : BlockIndex) (e : blockExponents k i) :
    T ^ (-offset i).toNat * originSubst (monomial e.val 1) =
    T ^ (offset i).toNat * valueImage ^ removed k i *
      bind₁ scaledImage (coordinateChange (monomial (stripped k i e) 1)) := by
  have hx := e.property.1.2.2.2
  rw [source_index] at hx
  have ht : (-offset i).toNat + e.val none =
      (offset i).toNat + e.val (some 1) + 2 * e.val (some 2) + 3 * e.val (some 3) := by omega
  have ha : removed k i + (e.val (some 0) - removed k i) = e.val (some 0) := by
    have := removed_le k i e
    omega
  have hT : T ^ (-offset i).toNat * T ^ e.val none =
      T ^ (offset i).toNat * T ^ e.val (some 1) * T ^ (2 * e.val (some 2)) *
        T ^ (3 * e.val (some 3)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA : valueImage ^ e.val (some 0) =
      valueImage ^ removed k i * valueImage ^ (e.val (some 0) - removed k i) := by
    rw [← pow_add, ha]
  rw [origin_monomial, stripped_monomial]
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (T ^ (-offset i).toNat * T ^ e.val none) *
        (valueImage ^ e.val (some 0) * (jetVar 0) ^ e.val (some 1) *
          (jetVar 1) ^ e.val (some 2) * (jetVar 2) ^ e.val (some 3)) := by ring
    _ = _ := by rw [hT, hA]; ring
private theorem shifted_origin (i : BlockIndex) (p : BlockSpace k i) :
    T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) =
    T ^ (offset i).toNat * valueImage ^ removed k i *
      bind₁ scaledImage (coordinateChange ((encode k i p : oldSpace (activeFlag k i)) : JetPoly)) := by
  let l := (LinearMap.mulLeft Geom (T ^ (-offset i).toNat)).comp
    (originSubst.toLinearMap.comp (BlockSpace k i).subtype)
  let r := (LinearMap.mulLeft Geom (T ^ (offset i).toNat * valueImage ^ removed k i)).comp
    ((bind₁ scaledImage).toLinearMap.comp
      (coordinateChange.toLinearMap.comp ((oldSpace (activeFlag k i)).subtype.comp (encode k i))))
  have h : l = r := by
    apply (basisRestrictSupport Geom (blockExponents k i)).ext
    intro e
    change T ^ (-offset i).toNat *
      originSubst (↑(basisRestrictSupport Geom (blockExponents k i) e) : SourcePolynomial) =
      T ^ (offset i).toNat * valueImage ^ removed k i *
        bind₁ scaledImage (coordinateChange
          (↑(encode k i (basisRestrictSupport Geom (blockExponents k i) e)) : JetPoly))
    rw [encode_basis, coe_basisRestrictSupport_apply]
    exact shifted_origin_monomial k i e
  exact LinearMap.congr_fun h p
private def scaledWeight (j : Fin 4) : ℕ := contactWeight j + gradeWeight j
private theorem weight_scaled (e : JetExp) :
    e.weight scaledWeight = e.weight contactWeight + e.weight gradeWeight := by
  simp [Finsupp.weight_eq_sum, scaledWeight, smul_eq_mul, Nat.mul_add, Finset.sum_add_distrib]
private theorem t_power_order (n : ℕ) :
    T ^ n ∈ restrictWeightedOrder (localContactWeight 3) n := by
  simpa using pow_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := Geom) (localContactWeight 3) (localT 3) (m := 1) le_rfl) n
private theorem scaled_image_order (j : Fin 4) :
    scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) (scaledWeight j) := by
  have hY (k : Fin 3) : jetVar k ∈ restrictWeightedOrder (localContactWeight 3) 0 := by simp
  have hE : E ∈ restrictWeightedOrder (localContactWeight 3) 3 :=
    X_mem_restrictWeightedOrder _ _ le_rfl
  fin_cases j
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) hE
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) (hY 0)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 2) (hY 1)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 3) (hY 2)
private theorem value_order :
    valueImage ∈ restrictWeightedOrder (localContactWeight 3) 1 := by
  have h (j : Fin 4) : scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) 1 :=
    restrictWeightedOrder_anti _ (Nat.succ_le_succ (Nat.zero_le _)) (scaled_image_order j)
  rw [← scaled_shear_zero]
  simp only [shearImage, ite_true, map_add, map_sub, bind₁_X_right]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (h 0) (h 1)) (h 2)) (h 3)
private theorem order_of_t_power_mul {n m : ℕ} {p : Local}
    (h : T ^ n * p ∈ restrictWeightedOrder (localContactWeight 3) (m + n)) :
    p ∈ restrictWeightedOrder (localContactWeight 3) m := by
  rw [MvPolynomial.X_pow_eq_monomial] at h
  intro e he
  have hh := mem_restrictWeightedOrder.mp h (Finsupp.single (localT 3) n + e) (by
    rw [MvPolynomial.mem_support_iff, coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he)
  change m ≤ e.weight (localContactWeight 3)
  simp only [map_add, Finsupp.weight_single, localContactWeight_T, smul_eq_mul, mul_one] at hh
  omega
private theorem kernel_le (i : BlockIndex) :
    LinearMap.ker ((flagContact (activeFlag k i)).comp (encode k i)) ≤ LinearMap.ker (originBlock k i) := by
  intro p hp
  let q : oldSpace (activeFlag k i) := encode k i p
  let shear : JetPoly := coordinateChange (q : JetPoly)
  let cut := (activeFlag k i).order.toNat
  have hz : weightedTruncation contactWeight cut shear = 0 := LinearMap.mem_ker.mp hp
  have hcontact := (weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (q : JetPoly).IsWeightedHomogeneous gradeWeight (residualDegree k i) := by
    intro e he
    have hd := (q.property (mem_support_iff.mpr he)).1
    change (e.weight gradeWeight : ℤ) = (activeFlag k i).degree at hd
    rw [active_degree] at hd
    omega
  have hshear : shear.IsWeightedHomogeneous gradeWeight (residualDegree k i) :=
    hgrade.bind₁ shearImage_grade
  have hscaled : shear ∈ restrictWeightedOrder scaledWeight (cut + residualDegree k i) := by
    intro e he
    have hg := hshear (mem_support_iff.mp he)
    have hc := mem_restrictWeightedOrder.mp hcontact e he
    change cut + residualDegree k i ≤ e.weight scaledWeight
    rw [weight_scaled, hg]
    exact Nat.add_le_add_right hc _
  have hprod := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (t_power_order (offset i).toNat)
      (by simpa using pow_mem_restrictWeightedOrder value_order (removed k i)))
    (bind₁_mem_restrictWeightedOrder scaled_image_order hscaled)
  have hbound : 3000 + (-offset i).toNat ≤
      (offset i).toNat + removed k i + (cut + residualDegree k i) := by
    change 3000 + (-offset i).toNat ≤ (offset i).toNat + removed k i +
      ((3000 - (i.1.val : ℤ) - offset i).toNat + residualDegree k i)
    simp only [removed, residualDegree]
    omega
  have hshift : T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) ∈
      restrictWeightedOrder (localContactWeight 3) (3000 + (-offset i).toNat) := by
    rw [shifted_origin]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  change weightedTruncation (localContactWeight 3) 3000 (originSubst (p : SourcePolynomial)) = 0
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (order_of_t_power_mul hshift)
theorem origin_block_rank (i : BlockIndex) :
    Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
      Module.finrank Geom (LinearMap.range (flagContact (activeFlag k i))) := by
  let f := (flagContact (activeFlag k i)).comp (encode k i)
  have hker := Submodule.finrank_mono (kernel_le k i)
  change Module.finrank Geom (LinearMap.ker f) ≤
    Module.finrank Geom (LinearMap.ker (originBlock k i)) at hker
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (originBlock k i).finrank_range_add_finrank_ker
  exact (show Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
      Module.finrank Geom (LinearMap.range f) by omega).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

open private rank_zero_of_order_nonpos lower_le_kernel from ProximityPrize.SubmissionLower.Fast068

def initialFlag (i : BlockIndex) : Flag :=
  {K1_13_2.initialFlag i with degree := (residualDegree k i : ℤ)}

theorem taper_active_range_le (i : BlockIndex) :
    LinearMap.range (flagContact (activeFlag k i)) ≤
      LinearMap.range (flagContact (initialFlag k i)) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨⟨p.1, ?_⟩, rfl⟩
  intro e he
  obtain ⟨hgrade, hlow, hupp, hcap⟩ := p.2 he
  exact ⟨hgrade, hlow, hupp.trans (min_le_left _ _), hcap⟩

def bound (i : BlockIndex) (power : Fin 11 → ℕ) : ℕ :=
  let F := initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCount (activeFlag k i)
    let lower := max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))
    (min active (oldCount F - lower)).toNat

theorem origin_block_rank_bound (h2 : K1_13_2_2.c2) (h3 : K1_13_2_2.c3) (h4 : K1_13_2_2.c4) (h5 : K1_13_2_2.c5)
    (i : BlockIndex) (power : Fin 11 → ℕ) :
    Module.finrank Geom (LinearMap.range (originBlock k i)) ≤ bound k i power := by
  let F := initialFlag k i
  let A := activeFlag k i
  have hOrigin := origin_block_rank k i
  change Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
    Module.finrank Geom (LinearMap.range (flagContact A)) at hOrigin
  by_cases ho : F.order ≤ 0
  · have hz := rank_zero_of_order_nonpos A (show A.order ≤ 0 from ho)
    have h := hOrigin.trans (le_of_eq hz)
    have horder : (initialFlag k i).order ≤ 0 := ho
    simpa [bound, horder] using h
  have hActive := (flagContact A).finrank_range_le
  rw [finrank_oldSpace] at hActive
  have hCols := h3 h2
  have hRows := h4 h2
  have hKernel0 := lower_le_kernel F (hCols F) (hRows F)
  have hKernel1 := lower_le_kernel (residualFlag F power)
    (hCols (residualFlag F power)) (hRows (residualFlag F power))
  obtain ⟨f, hf⟩ := h5 F power
  have hInj := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hRank := Submodule.finrank_mono (taper_active_range_le k i)
  change Module.finrank Geom (LinearMap.range (flagContact A)) ≤
    Module.finrank Geom (LinearMap.range (flagContact F)) at hRank
  have hNullity := (flagContact F).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hNullity
  have hFullCols := hCols F
  have hActiveCols := hCols A
  have hbound :
      (Module.finrank Geom (LinearMap.range (originBlock k i)) : ℤ) ≤
      min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))) := by
    apply le_min
    · omega
    · have hMax :
          max 0 (max (kernelLower F) (kernelLower (residualFlag F power))) ≤
            (Module.finrank Geom (LinearMap.ker (flagContact F)) : ℤ) := by
        exact max_le (Int.natCast_nonneg _) (max_le hKernel0 (by omega))
      omega
  unfold bound
  change Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
    (if F.order ≤ 0 then 0 else
      (min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power))))).toNat)
  rw [ite_eq_right ho]
  omega

open private high_monomial_vanishes from ProximityPrize.SubmissionLower.PortLowBase
open private finrank_finset_sup_le from ProximityPrize.SubmissionLower.Fast017

def differentiated : JetVariable 3 → ℕ := fun v => v.elim 0 (fun j => if j = 0 then 0 else 1)

def Eligible (cap : ℕ → ℕ) (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧ e.weight jetDerivativeWeight ≤ 1650 ∧
    e.weight topWeight ≤ 550 ∧ e.weight differentiated ≤ cap (e.weight jetDegreeWeight)

def space (cap : ℕ → ℕ) : Submodule Geom SourcePolynomial := restrictSupport Geom {e | Eligible cap e}

theorem differentiated_eq (e : SourceExponent) :
    e.weight differentiated = e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, differentiated]

theorem translate_monomial {cap : ℕ → ℕ} (hc : Antitone cap)
    (x y : Geom) (e : SourceExponent) (c : Geom) (he : Eligible cap e) :
    globalPointTranslation x y (monomial e c) ∈ space cap := by
  have preserve {w : JetVariable 3 → ℕ} {n : ℕ} (h : e.weight w ≤ n) :
      ∀ a ∈ (globalPointTranslation x y (monomial e c)).support, a.weight w ≤ n :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y ((monomial_mem_restrictWeightAtMost _ _ _ _).mpr (Or.inl h)))
  intro a ha
  have hgrade := preserve (w := jetDegreeWeight) (le_refl _) a ha
  exact ⟨hgrade.trans he.1, preserve he.2.1 a ha, preserve he.2.2.1 a ha,
    (preserve he.2.2.2 a ha).trans (hc hgrade)⟩

theorem translate {cap : ℕ → ℕ} (hc : Antitone cap) (x y : Geom) (Q : space cap) :
    globalPointTranslation x y Q.1 ∈ space cap := by
  rw [congrArg (globalPointTranslation x y) Q.1.as_sum, map_sum]
  exact Submodule.sum_mem _ fun e he => translate_monomial hc x y e (Q.1.coeff e) (Q.2 he)

private theorem finrank_of_column_cover {ι : Type*} [Fintype ι]
    (source : Set SourceExponent) (f f' : SourcePolynomial →ₗ[Geom] Local)
    (shift : SourcePolynomial → SourcePolynomial)
    (hshift : ∀ Q ∈ restrictSupport Geom source, shift Q ∈ restrictSupport Geom source)
    (heval : ∀ Q, f' Q = f (shift Q)) (p : ι → Submodule Geom Local)
    [∀ i, Module.Finite Geom (p i)] (bound : ι → ℕ)
    (hcol : ∀ e ∈ source, ∀ c, f (MvPolynomial.monomial e c) = 0 ∨
      ∃ i, f (MvPolynomial.monomial e c) ∈ p i)
    (hbound : ∀ i, Module.finrank Geom (p i) ≤ bound i) :
    Module.finrank Geom (LinearMap.range (f'.domRestrict (restrictSupport Geom source))) ≤ ∑ i, bound i := by
  classical
  have cover : LinearMap.range (f'.domRestrict (restrictSupport Geom source)) ≤ Finset.univ.sup p := by
    intro L hL
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp hL
    rw [← hQ]
    change f' Q.1 ∈ Finset.univ.sup p
    rw [heval]
    let R := shift Q.1
    have hR : R ∈ restrictSupport Geom source := hshift _ Q.2
    have expand := congrArg f R.as_sum
    rw [map_sum] at expand
    rw [expand]
    refine Submodule.sum_mem _ fun e he => ?_
    rcases hcol e (hR he) (R.coeff e) with hzero | ⟨i, hi⟩
    · rw [hzero]
      exact Submodule.zero_mem _
    · exact (Finset.le_sup (f := p) (Finset.mem_univ i)) hi
  exact (Submodule.finrank_mono cover).trans
    ((finrank_finset_sup_le p _).trans (Finset.sum_le_sum fun i _ => hbound i))
theorem rank_le_of_blocks {cap : ℕ → ℕ} (hc : Antitone cap) (x y : Geom)
    (budget : BlockIndex → ℕ)
    (hbudget : ∀ i, Module.finrank Geom (LinearMap.range (originBlock (cap i.1.val) i)) ≤ budget i) :
    Module.finrank Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict (space cap))) ≤
      ∑ i : BlockIndex, budget i := by
  let ranges : BlockIndex → Submodule Geom Local :=
    fun i => LinearMap.range (originBlock (cap i.1.val) i)
  have (i : BlockIndex) : Module.Finite Geom (ranges i) := by dsimp only [ranges]; infer_instance
  refine finrank_of_column_cover {e | Eligible cap e}
    (localConstraintAt 3000 0 0) (localConstraintAt 3000 x y) (globalPointTranslation x y)
    (fun Q hQ => translate hc x y ⟨Q, hQ⟩)
    (fun Q => localConstraintAt_eq_zero_globalPointTranslation x y Q)
    ranges budget ?_ hbudget
  intro e he c
  by_cases hx : e none < 3000
  · have he' : Eligible cap e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none + (1650 - idx), by omega⟩)
    have hw := weight_le_add_mul_totalJetDegree 133671 e
    change e.weight (differentialWeight 133671) ≤ e none + 133671 * grade at hw
    have hold : SourceEligible e := ⟨hb, hj, he'.2.2.1, by omega⟩
    have hi : e ∈ blockExponents (cap i.1.val) i := by
      refine ⟨⟨hold, hx, rfl, ?_⟩, ?_⟩
      · change (e none : ℤ) - idx = ((e none + (1650 - idx) : ℕ) : ℤ) - 1650
        omega
      · simpa only [← differentiated_eq] using he'.2.2.2
    have hm : monomial e c ∈ BlockSpace (cap i.1.val) i :=
      (monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact Or.inr ⟨i, ⟨⟨_, hm⟩, rfl⟩⟩
  · exact Or.inl (high_monomial_vanishes _ _ (Nat.le_of_not_gt hx))

theorem rank_le {cap : ℕ → ℕ} (hc : Antitone cap) (x y : Geom)
    (power : BlockIndex → Fin 11 → ℕ) (h2 : K1_13_2_2.c2) (h3 : K1_13_2_2.c3)
    (h4 : K1_13_2_2.c4) (h5 : K1_13_2_2.c5) :
    Module.finrank Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict (space cap))) ≤
      ∑ i : BlockIndex, bound (cap i.1.val) i (power i) :=
  rank_le_of_blocks hc x y _ (fun i => origin_block_rank_bound _ h2 h3 h4 h5 i (power i))

theorem range_le_old (i : BlockIndex) :
    LinearMap.range (originBlock k i) ≤ LinearMap.range (K1_13_2.originBlock i) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p.1, fun e he => (p.2 he).1⟩, rfl⟩

#print axioms rank_le
#print axioms range_le_old
end
end TaperNormalize
