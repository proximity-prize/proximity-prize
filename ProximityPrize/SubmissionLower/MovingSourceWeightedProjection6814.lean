import ProximityPrize.SubmissionLower.MovingSourceIndexedPair6814
namespace ProximityPrize.SubmissionLower.MovingSourceWeightedProjection6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 700000
open scoped BigOperators Classical
open RCN002 RCN011 RCN021 RCN022 RCN093 RCN095 RCN102 RCN106 RCN113 RCN120 RCN125 RCN264 RCN333 RCN371
open MovingSourceFlatBaseChange6814 MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceLocalCarrier6814 MovingSourceIndexedPair6814

variable {Ω : Type} [Field Ω]
local instance : DecidableEq Ω := Classical.decEq Ω

theorem planeMap_relPrime (order : Fin 3 ≃ Fin 3)
    (B C : MvPolynomial (Fin 3) Ω) (hB : B≠0) (hcop : IsRelPrime B C) :
    IsRelPrime (planeMap Ω order B) (planeMap Ω order C) := by
  letI : Module.Flat (Polynomial Ω) (RatFunc Ω) :=
    IsLocalization.flat (RatFunc Ω) (nonZeroDivisors (Polynomial Ω))
  letI : Algebra (Collected Ω) (RationalPolynomials Ω) := MvPolynomial.algebraMvPolynomial
  letI : Module.Flat (Collected Ω) (RationalPolynomials Ω) := coefficient_map_flat
  have hcol : collect Ω order B≠0 := fun hz => hB ((collect Ω order).injective (hz.trans (map_zero _).symm))
  have hh : IsRelPrime (rationalMap Ω order B) (rationalMap Ω order C) :=
    map_isRelPrime_of_flat (A:=Collected Ω) (B:=RationalPolynomials Ω)
      (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)))
      (collect Ω order B) (collect Ω order C) hcol
      (isRelPrime_equiv (collect Ω order).toRingEquiv B C hcop)
  exact isRelPrime_equiv (bivariateEquiv (RatFunc Ω)).toRingEquiv _ _ hh

def HasThickness (G H A M B C : MvPolynomial (Fin 3) Ω) (d : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] (ev : MvPolynomial (Fin 3) Ω →+* R)
    (J : Ideal R) [J.IsMaximal] (surface : R),
    ev G∈Ideal.span {surface} → ev H∉J → ev A∉J → ev M∈J →
    ev B∈Ideal.span {surface} ⊔ J^d ∧ ev C∈Ideal.span {surface} ⊔ J^d

theorem HasThickness.mem_regular
    {G H A M B C : MvPolynomial (Fin 3) Ω} {d : ℕ}
    (thick : HasThickness G H A M B C d) (hd : 0<d)
    (V : RegularComponent Ω G M (H*A)) : B∈V.1 ∧ C∈V.1 := by
  let E := CoordinateField Ω V.1
  let ev := (coordinateEvaluation Ω V.1).toRingHom
  letI : (⊥ : Ideal E).IsMaximal := Ideal.bot_isMaximal
  have he (P : MvPolynomial (Fin 3) Ω) : ev P=0 ↔ P∈V.1 := by
    change P∈RingHom.ker (coordinateEvaluation Ω V.1).toRingHom ↔ P∈V.1
    rw [coordinateEvaluation_ker]
  have hH : H∉V.1 := fun hm => regularComponent_H_not_mem Ω G M (H*A) V (V.1.mul_mem_right A hm)
  have hA : A∉V.1 := fun hm => regularComponent_H_not_mem Ω G M (H*A) V (V.1.mul_mem_left H hm)
  have hz := thick E ev ⊥ 0
    (by rw [(he G).mpr (regularComponent_G_mem Ω G M (H*A) V)]; exact Ideal.zero_mem _)
    (by simpa only [Ideal.mem_bot] using (he H).not.mpr hH)
    (by simpa only [Ideal.mem_bot] using (he A).not.mpr hA)
    (by exact (he M).mpr (regularComponent_T_mem Ω G M (H*A) V))
  have hI : (Ideal.span ({(0 : E)} : Set E) ⊔ (⊥ : Ideal E)^d)=(⊥ : Ideal E) := by
    rw [Ideal.span_singleton_eq_bot.mpr rfl,Ideal.bot_pow (Nat.ne_of_gt hd),sup_bot_eq]
  have hB0 : ev B=0 := Ideal.mem_bot.mp (hI ▸ hz.1)
  have hC0 : ev C=0 := Ideal.mem_bot.mp (hI ▸ hz.2)
  exact ⟨(he B).mp hB0,(he C).mp hC0⟩

theorem weighted_directional_degree
    [IsAlgClosed Ω]
    (G H A M B C : MvPolynomial (Fin 3) Ω) (hG : G≠0) (hB : B≠0) (hC : C≠0)
    (hcop : IsRelPrime B C) (d : ℕ) (hd : 0<d) (thick : HasThickness G H A M B C d)
    {ι : Type} [Fintype ι] (component : ι → RegularComponent Ω G M (H*A))
    (hinj : Function.Injective component) (axis : Axis) (lam mu nu : Ω)
    (ht : ∀ i, Transcendental Ω
      (flagEvaluation Ω (component i).1 lam mu nu (MvPolynomial.X (axis.order 0))))
    (hgate : ∀ i, ∀ hx : Transcendental Ω
      (flagEvaluation Ω (component i).1 lam mu nu (MvPolynomial.X (axis.order 0))),
      (letI := flagBaseAlgebra Ω (component i).1 lam mu nu axis.order hx;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (component i).1)) ∧
      (letI := flagBaseAlgebra Ω (component i).1 lam mu nu axis.order hx;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (component i).1)))
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p B) (hq : RCN095.PolynomialInFlag q C) :
    d*(∑ i, RCN344.coordinateDegree Ω (CoordinateField Ω (component i).1)
      (RCN042.coordinateOfGate (flagEvaluation Ω (component i).1 lam mu nu
        (MvPolynomial.X (axis.order 0))) (hgate i)))≤flagMixed p q axis.flag := by
  let plane := flagPlaneMap Ω lam mu nu axis.order
  let P := plane B
  let Q := plane C
  let W := plane G
  have hFlagInj : Function.Injective (flagAlgHom lam mu nu : MvPolynomial (Fin 3) Ω →ₐ[Ω] _) := by
    intro P₁ P₂ h
    apply (flagEquiv lam mu nu).injective
    exact h
  have hinjPlane : Function.Injective plane := by
    intro P₁ P₂ hh
    change planeMap Ω axis.order (flagAlgHom lam mu nu P₁)=
      planeMap Ω axis.order (flagAlgHom lam mu nu P₂) at hh
    exact hFlagInj (planeMap_injective Ω axis.order hh)
  have hPne : P≠0 := by
    intro hz
    apply hB
    apply hinjPlane
    exact hz.trans (map_zero plane).symm
  have hWne : W≠0 := by
    intro hz
    apply hG
    apply hinjPlane
    exact hz.trans (map_zero plane).symm
  have hflagB : flagAlgHom lam mu nu B≠0 := fun hz =>
    hB (hFlagInj (hz.trans (map_zero (flagAlgHom lam mu nu)).symm))
  have hflagRel : IsRelPrime (flagAlgHom lam mu nu B) (flagAlgHom lam mu nu C) := by
    simpa only [AlgEquiv.coe_ringEquiv,flagEquiv_apply] using
      isRelPrime_equiv (flagEquiv lam mu nu).toRingEquiv B C hcop
  have hrel : IsRelPrime P Q := planeMap_relPrime (Ω:=Ω) axis.order
    (flagAlgHom lam mu nu B) (flagAlgHom lam mu nu C) hflagB hflagRel
  let hfinite i := (hgate i (ht i)).1
  have hgen i := flag_generators_axis Ω (component i).1 axis lam mu nu (ht i)
  let rel i := relationKernel Ω (CoordinateField Ω (component i).1) axis.order
    (flagEvaluation Ω (component i).1 lam mu nu) (ht i)
  letI : ∀ i, (rel i).IsPrime := fun i => RingHom.ker_isPrime _
  have hroot i : P∈rel i ∧ Q∈rel i := by
    have hm := thick.mem_regular hd (component i)
    exact ⟨flagPlaneMap_mem_relation (component i).1 lam mu nu axis.order (ht i) hm.1,
      flagPlaneMap_mem_relation (component i).1 lam mu nu axis.order (ht i) hm.2⟩
  have hWmem i : W∈rel i := flagPlaneMap_mem_relation (component i).1 lam mu nu axis.order (ht i)
    (regularComponent_G_mem Ω G M (H*A) (component i))
  have hex i : ∃ V, Irreducible V ∧ V∣W ∧ V∈rel i :=
    exists_irreducible_divisor_mem_prime (rel i) W hWne (hWmem i)
  choose carrier hcarrier hdiv hcarrierMem using hex
  have hthick (r : Polynomial (RatFunc Ω)) (hr : Irreducible r)
      (a : IndexedFactorFiber component lam mu nu axis.order ht r) :
      (fiberLocalizePlane r hr P∈Ideal.span {fiberLocalizePlane r hr (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu axis.order ht r hr a^d) ∧
      (fiberLocalizePlane r hr Q∈Ideal.span {fiberLocalizePlane r hr (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu axis.order ht r hr a^d) := by
    let J := indexedFiberRelation component lam mu nu axis.order ht r hr a
    let ev := (fiberLocalizePlane r hr).comp plane
    letI : J.IsMaximal := indexedFiberRelation_isMaximal component lam mu nu axis.order ht
      hfinite hgen r hr a
    have hc : J.comap ev=(component a.1).1 := by
      change J.comap ((fiberLocalizePlane r hr).comp
        ((planeMap Ω axis.order).comp (flagAlgHom lam mu nu).toRingHom))=_
      rw [←Ideal.comap_comap,indexedFiberRelation_under,←Ideal.comap_comap,
        relationKernel_contract,flagEvaluation_kernel_contract]
    have hF : ev G∈Ideal.span {fiberLocalizePlane r hr (carrier a.1)} :=
      Ideal.mem_span_singleton.mpr (map_dvd (fiberLocalizePlane r hr) (hdiv a.1))
    have hH : ev H∉J := by
      intro hm
      have hh : H∈(component a.1).1 := by rw [←hc]; exact hm
      exact regularComponent_H_not_mem Ω G M (H*A) (component a.1)
        ((component a.1).1.mul_mem_right A hh)
    have hA : ev A∉J := by
      intro hm
      have hh : A∈(component a.1).1 := by rw [←hc]; exact hm
      exact regularComponent_H_not_mem Ω G M (H*A) (component a.1)
        ((component a.1).1.mul_mem_left H hh)
    have hM : ev M∈J := by
      change M∈J.comap ev
      rw [hc]
      exact regularComponent_T_mem Ω G M (H*A) (component a.1)
    have hh := thick (Polynomial (FiberCoefficient r hr)) ev J
      (fiberLocalizePlane r hr (carrier a.1)) hF hH hA hM
    have hBvalue : ev B=fiberLocalizePlane r hr P := rfl
    have hCvalue : ev C=fiberLocalizePlane r hr Q := rfl
    rw [hBvalue,hCvalue] at hh
    exact hh
  have hb := indexed_pair_degree_sum_le component hinj lam mu nu axis.order ht hfinite hgen hgate
    P Q hPne hrel (fun i => (hroot i).1) (fun i => (hroot i).2)
    carrier hcarrier hcarrierMem (fun _ => d) hthick
  rw [←Finset.mul_sum] at hb
  exact hb.trans (flag_resultant_degree_le axis lam mu nu B C p q hp hq hC)

end
end ProximityPrize.SubmissionLower.MovingSourceWeightedProjection6814
