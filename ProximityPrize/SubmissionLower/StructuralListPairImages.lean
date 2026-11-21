import ProximityPrize.SubmissionLower.StructuralListPairComponents

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial

noncomputable section

abbrev ComponentOpen (T : Chart 2) (P : Ideal (InitialRing 2)) :=
  Localization.Away (Ideal.Quotient.mk P T.denominator)

def componentLocalize (T : Chart 2) (P : Ideal (InitialRing 2)) : InitialRing 2 →ₐ[Geo] ComponentOpen T P :=
  (IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ P) (ComponentOpen T P)).comp (Ideal.Quotient.mkₐ Geo P)

def componentInvDenom (T : Chart 2) (P : Ideal (InitialRing 2)) : ComponentOpen T P :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk P T.denominator)

theorem componentDenom_mul_inv (T : Chart 2) (P : Ideal (InitialRing 2)) :
    componentLocalize T P T.denominator * componentInvDenom T P = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk P T.denominator)

def componentMap (T : Chart 2) (P : Ideal (InitialRing 2)) : CoeffRing →ₐ[Geo] ComponentOpen T P :=
  aeval fun i => componentLocalize T P (T.numerator i) * componentInvDenom T P

def componentIdeal (T : Chart 2) (P : Ideal (InitialRing 2)) : Ideal CoeffRing :=
  RingHom.ker (componentMap T P).toRingHom

/-- Region cut out by the coefficient map from a source component. -/
theorem componentGeometry (T : Chart 2) (P : Ideal (InitialRing 2)) (hp : P.IsPrime)
    (hD : T.denominator ∉ P) : (componentIdeal T P).IsPrime ∧
      (affineHilbertPolynomial (componentIdeal T P)).natDegree ≤ (affineHilbertPolynomial P).natDegree := by
  let := hp
  have hne : Ideal.Quotient.mk P T.denominator ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let : IsDomain (ComponentOpen T P) := Localization.Away.isDomain hne
  refine ⟨RingHom.ker_isPrime _, ?_⟩
  let E := awayPresentationEquiv P T.denominator
  exact (natDegree_affineHilbertPolynomial_le_of_injective
      (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (componentMap T P)))
      (E.symm.injective.comp (Ideal.kerLiftAlg_injective (componentMap T P)))).trans
    (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P T.denominator)

/-- Evaluation on a source component gives a point of its coefficient image. -/
theorem componentOutput_mem (T : Chart 2) (P : Ideal (InitialRing 2)) (y : Fin 3 → Geo)
    (hy : y ∈ zeroLocus Geo P) (hD : eval y T.denominator ≠ 0) :
    T.output y ∈ zeroLocus Geo (componentIdeal T P) := by
  let ev := Ideal.Quotient.liftₐ P (aeval y) (fun q hq => hy q hq)
  let ext : ComponentOpen T P →ₐ[Geo] Geo := IsLocalization.Away.liftAlgHom (f := ev) (Ideal.Quotient.mk P T.denominator)
    (isUnit_iff_ne_zero.mpr hD)
  have he (q : InitialRing 2) : ext (componentLocalize T P q) = eval y q :=
    IsLocalization.Away.lift_eq (g := ev.toRingHom)
      (Ideal.Quotient.mk P T.denominator) (isUnit_iff_ne_zero.mpr hD) (Ideal.Quotient.mk P q)
  have hu := congrArg ext (componentDenom_mul_inv T P)
  rw [map_mul, he, map_one] at hu
  have hinv : ext (componentInvDenom T P) = (eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hD).mpr ((mul_comm _ _).trans hu)
  have h : ext.comp (componentMap T P) = aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ext (componentMap T P (MvPolynomial.X i)) = aeval (T.output y) (MvPolynomial.X i)
    rw [componentMap, aeval_X, map_mul, he, hinv, aeval_X, Chart.output, div_eq_mul_inv]
  intro q hq
  change componentMap T P q = 0 at hq
  rw [← h]
  change ext (componentMap T P q) = 0
  rw [hq, map_zero]

/-- Coefficient polynomials of bounded degree clear into the source component band. -/
theorem componentHilbert_le_band (T : Chart 2) (P : Ideal (InitialRing 2)) (a d e : ℕ)
    (hD : T.denominator ∈ bandSpace a d e) (hN : ∀ i, T.numerator i ∈ bandSpace a d e) (m : ℕ) :
    affineHilbertFunction (componentIdeal T P) m ≤
      Module.finrank Geo (componentBand P (m*a) (m*d) (m*e)) := by
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ P) (ComponentOpen T P)
  let δ := componentLocalize T P T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ComponentOpen T P)
      (Ideal.Quotient.mk P T.denominator)
  let y (i : Fin k) := componentLocalize T P (T.numerator i) * componentInvDenom T P
  have hy (i : Fin k) : δ * y i = componentLocalize T P (T.numerator i) := by
    change componentLocalize T P T.denominator * (componentLocalize T P (T.numerator i) * componentInvDenom T P) = _
    rw [mul_left_comm _ (componentLocalize T P (T.numerator i)), componentDenom_mul_inv, mul_one]
  let V (n : ℕ) : Submodule Geo (ComponentOpen T P) :=
    (componentBand P (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ComponentOpen T P) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ComponentOpen T P) :
      z ∈ W n ↔ ∃ q ∈ bandSpace (n * a) (n * d) (n * e), componentLocalize T P q = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, componentBand, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, componentLocalize, j]
  have hOne : (1 : InitialRing 2) ∈ bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← C_1, weightedTotalDegree_C]
    exact mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) :
      T.denominator ^ n ∈ bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin k) (n : ℕ) (z : ComponentOpen T P) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ComponentOpen T P) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (q : CoeffRing) (hP : q.totalDegree ≤ m) : componentMap T P q ∈ W m := by
    change aeval y q ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := componentIdeal T P
  let ι : (CoeffRing ⧸ Q) →ₐ[Geo] ComponentOpen T P := Ideal.kerLiftAlg (componentMap T P)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨q, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change componentMap T P q ∈ W m
    exact hclear q hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (componentMap T P) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)

end

end StructuralList
