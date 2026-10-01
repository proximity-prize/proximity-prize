import ProximityPrize.SubmissionLower.MergedInfra6815_33
import ProximityPrize.SubmissionLower.MergedInfra6815_29
import ProximityPrize.SubmissionLower.MergedInfra6815_31
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceLocalCarrier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped Classical
open RCN143

theorem exists_irreducible_divisor_mem_prime
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (I : Ideal R) [I.IsPrime] (F : R) (hF : F≠0) (hmem : F∈I) :
    ∃ G, Irreducible G ∧ G∣F ∧ G∈I := by
  obtain ⟨factors,hfactor,hprod⟩ := WfDvdMonoid.exists_factors F hF
  let ev := Ideal.Quotient.mk I
  have hz : ev F=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have ha := Associated.map ev hprod
  rw [hz] at ha
  have hp : ev factors.prod=0 := (associated_zero_iff_eq_zero _).mp ha
  rw [map_multiset_prod] at hp
  obtain ⟨g,hg,hzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  exact ⟨g,hfactor g hg,(Multiset.dvd_prod hg).trans hprod.dvd,
    Ideal.Quotient.eq_zero_iff_mem.mp hzero⟩

variable {Base : Type} [Field Base]
local instance : DecidableEq Base := Classical.decEq Base
@[reducible] local instance localPlaneSemiring (I : Ideal (Polynomial Base)) [I.IsPrime] :
    Semiring (Polynomial (LocalBase I)) := Polynomial.commSemiring.toSemiring

theorem local_carrier_prime_and_contract
    (I : Ideal (Polynomial Base)) [I.IsPrime]
    (J : Ideal (Polynomial (Polynomial Base)))
    (hcontract : J.comap Polynomial.C=I)
    (G : Polynomial (Polynomial Base)) (hG : Irreducible G) (hGmem : G∈J) :
    (Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))}).IsPrime ∧
    (Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))}).comap
        (Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I)))=Ideal.span {G} := by
  let C : Polynomial Base →+* Polynomial (Polynomial Base) := Polynomial.C
  let M := I.primeCompl.map C.toMonoidHom
  let R := Polynomial (LocalBase I)
  letI : Algebra (Polynomial (Polynomial Base)) R := Polynomial.algebra (Polynomial Base) (LocalBase I)
  letI : IsLocalization M R := Polynomial.isLocalization I.primeCompl (LocalBase I)
  have hd : Disjoint (M : Set (Polynomial (Polynomial Base)))
      (Ideal.span {G} : Set (Polynomial (Polynomial Base))) := by
    rw [Set.disjoint_left]
    intro x hx hxG
    obtain ⟨r,hr,rfl⟩ := Submonoid.mem_map.mp hx
    have hm : C r∈J := J.mem_of_dvd (Ideal.mem_span_singleton.mp hxG) hGmem
    have hh : r∈J.comap Polynomial.C := hm
    rw [hcontract] at hh
    exact hr hh
  have hprime := Ideal.isPrime_span_singleton_of_prime hG.prime
  have hp := IsLocalization.isPrime_of_isPrime_disjoint M R (Ideal.span {G}) hprime hd
  have hc := IsLocalization.under_map_of_isPrime_disjoint M R hprime hd
  have hval : algebraMap (Polynomial (Polynomial Base)) R G=
      G.map (algebraMap (Polynomial Base) (LocalBase I)) := rfl
  have hspan : (Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))} : Ideal R)=
      Ideal.map (algebraMap (Polynomial (Polynomial Base)) R) (Ideal.span {G}) := by
    rw [Ideal.map_span,Set.image_singleton,hval]
  constructor
  · rw [hspan]
    exact hp
  · rw [hspan]
    exact hc

theorem local_carrier_relation_bar_ne_bot
    (I : Ideal (Polynomial Base)) [I.IsPrime]
    (J : Ideal (Polynomial (Polynomial Base)))
    (hcontract : J.comap Polynomial.C=I)
    (G : Polynomial (Polynomial Base)) (hG : Irreducible G) (hGmem : G∈J)
    (P Q : Polynomial (Polynomial Base)) (hcop : IsRelPrime P Q) (hP : P∈J) (hQ : Q∈J) :
    let f := Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I))
    Ideal.map (Ideal.Quotient.mk (Ideal.span {f G})) (Ideal.map f J)≠⊥ := by
  let f := Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I))
  let q := Ideal.Quotient.mk (Ideal.span {f G})
  change Ideal.map q (Ideal.map f J)≠⊥
  intro hbot
  have hc := (local_carrier_prime_and_contract I J hcontract G hG hGmem).2
  have hd (N : Polynomial (Polynomial Base)) (hN : N∈J) : G∣N := by
    have hm : q (f N)∈Ideal.map q (Ideal.map f J) :=
      Ideal.mem_map_of_mem q (Ideal.mem_map_of_mem f hN)
    have hz : q (f N)=0 := Ideal.mem_bot.mp (hbot ▸ hm)
    have hh : f N∈Ideal.span {f G} := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hn : N∈(Ideal.span {f G}).comap f := hh
    have hc' : (Ideal.span {f G}).comap f=Ideal.span {G} := by
      simpa only [f,Polynomial.coe_mapRingHom] using hc
    rw [hc',Ideal.mem_span_singleton] at hn
    exact hn
  exact hG.not_isUnit (hcop (hd P hP) (hd Q hQ))

end
end ProximityPrize.SubmissionLower.MovingSourceLocalCarrier6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceIndexedPair6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open RCN002 RCN011 RCN021 RCN022 RCN093 RCN102 RCN106 RCN107 RCN110 RCN111 RCN120 RCN226 RCN264
open MovingSourcePairPrimary6814 MovingSourcePairResultant6814 MovingSourceLocalCarrier6814

variable {Ω : Type} [Field Ω]
variable {G T H : MvPolynomial (Fin 3) Ω} {A : Type} [Fintype A]
variable (component : A → RegularComponent Ω G T H) (hinj : Function.Injective component)
variable (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
variable (ht : ∀ a, Transcendental Ω
  (flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite : ∀ a,
  letI := flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
  FiniteDimensional (RatFunc Ω) (CoordinateField Ω (component a).1))
variable (hgen : ∀ a,
  letI := flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
  IntermediateField.adjoin (RatFunc Ω)
    ({flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 2)),
      flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 1))} :
      Set (CoordinateField Ω (component a).1))=⊤)

include hinj hgen in
theorem indexed_pair_grouped_power_dvd
    (P Q : PlaneRing Ω) (hPne : P≠0) (hcop : IsRelPrime P Q)
    (hPmem : ∀ a, P∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (hQmem : ∀ a, Q∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (carrier : A → PlaneRing Ω) (hcarrier : ∀ a,Irreducible (carrier a))
    (hcarrierMem : ∀ a, carrier a∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (d : A → ℕ) (q : Polynomial (RatFunc Ω)) (hq : Irreducible q) (hqMonic : q.Monic)
    (hleft : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
      fiberLocalizePlane q hq P∈Ideal.span {fiberLocalizePlane q hq (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^d a.1)
    (hright : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
      fiberLocalizePlane q hq Q∈Ideal.span {fiberLocalizePlane q hq (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^d a.1) :
    q^(∑ a : IndexedFactorFiber component lam mu nu order ht q,
      d a.1*indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1)∣
      Polynomial.resultant P Q P.natDegree Q.natDegree := by
  let Fib := IndexedFactorFiber component lam mu nu order ht q
  let I : Ideal (Polynomial (RatFunc Ω)) := Ideal.span {q}
  letI : I.IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
  let R := FiberCoefficient q hq
  let surf (a : Fib) := fiberLocalizePlane q hq (carrier a.1)
  let rel := indexedFiberRelation component lam mu nu order ht q hq
  let bar (a : Fib) := indexedFiberRelationBar component lam mu nu order ht q hq (carrier a.1) a
  have hcontract (a : Fib) :
      (relationKernel Ω (CoordinateField Ω (component a.1).1) order
        (flagEvaluation Ω (component a.1).1 lam mu nu) (ht a.1)).comap Polynomial.C=I := by
    rw [relationKernel_comap_C]
    exact congrArg (fun f => Ideal.span {f}) a.2.symm
  letI : ∀ a : Fib,(Ideal.span {surf a}).IsPrime := fun a =>
    (local_carrier_prime_and_contract I _ (hcontract a) (carrier a.1) (hcarrier a.1) (hcarrierMem a.1)).1
  letI : ∀ a : Fib,(rel a).IsMaximal :=
    indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen q hq
  letI : ∀ a : Fib,(bar a).IsMaximal := fun a => by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f:=Ideal.Quotient.mk (Ideal.span {surf a})) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker,Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.mem_map_of_mem (fiberLocalizePlane q hq) (hcarrierMem a.1)
  have hbar (a : Fib) : bar a=Ideal.map (Ideal.Quotient.mk (Ideal.span {surf a})) (rel a) := rfl
  have hbarNe (a : Fib) : bar a≠⊥ :=
    local_carrier_relation_bar_ne_bot I _ (hcontract a) (carrier a.1) (hcarrier a.1)
      (hcarrierMem a.1) P Q hcop (hPmem a.1) (hQmem a.1)
  letI : ∀ a : Fib, IsLocalHom (algebraMap R (Localization.AtPrime (bar a))) := fun a =>
    indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite q hq (carrier a.1) a
  letI : ∀ a : Fib, FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (bar a))) := fun a =>
    indexedNaturalSurfaceResidue_finite component lam mu nu order ht hfinite hgen q hq
      (carrier a.1) a (hcarrierMem a.1)
  let C := sourcePairCertificate (fiberLocalizePlane q hq P) (fiberLocalizePlane q hq Q)
    surf rel bar hbar hbarNe (fun a : Fib => d a.1) hleft hright
    (indexedFiberRelation_pairwise_coprime component hinj lam mu nu order ht hfinite hgen q hq)
  letI : ∀ a : Fib, Module.Finite R (Polynomial R ⧸ C.pieces a) :=
    thickPiece_finite surf rel (fun a : Fib => d a.1)
      (exists_monic_mem_indexedFiberRelation component lam mu nu order ht hfinite hgen q hq)
  letI : Module.Finite R (∀ a : Fib, Polynomial R ⧸ C.pieces a) := inferInstance
  have hp := grouped_pair_power_dvd I q rfl hq hqMonic P Q P.natDegree Q.natDegree
    le_rfl le_rfl hcop (coprime_resultant_ne_zero P Q hPne hcop) _ C
  have he (a : Fib) : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (bar a)))=
        indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1 :=
    indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu order ht hfinite hgen q hq
      (carrier a.1) a (hcarrierMem a.1)
  change q^(∑ a : Fib, d a.1*Module.finrank (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (Localization.AtPrime (bar a))))∣_ at hp
  simpa only [he] using hp

include hinj hgen hfinite in
theorem indexed_pair_degree_sum_le
    [IsAlgClosed Ω]
    (hgate : ∀ a, ∀ hx : Transcendental Ω
        (flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))),
      (letI := flagBaseAlgebra Ω (component a).1 lam mu nu order hx;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (component a).1)) ∧
      (letI := flagBaseAlgebra Ω (component a).1 lam mu nu order hx;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (component a).1)))
    (P Q : PlaneRing Ω) (hPne : P≠0) (hcop : IsRelPrime P Q)
    (hPmem : ∀ a, P∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (hQmem : ∀ a, Q∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (carrier : A → PlaneRing Ω) (hcarrier : ∀ a,Irreducible (carrier a))
    (hcarrierMem : ∀ a, carrier a∈relationKernel Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (d : A → ℕ)
    (hthick : ∀ (q : Polynomial (RatFunc Ω)) (hq : Irreducible q)
      (a : IndexedFactorFiber component lam mu nu order ht q),
      (fiberLocalizePlane q hq P∈Ideal.span {fiberLocalizePlane q hq (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^d a.1) ∧
      (fiberLocalizePlane q hq Q∈Ideal.span {fiberLocalizePlane q hq (carrier a.1)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^d a.1)) :
    (∑ a, d a*RCN344.coordinateDegree Ω (CoordinateField Ω (component a).1)
      (RCN042.coordinateOfGate
        (flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))) (hgate a))) ≤
      (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree := by
  let C := RCN104.indexedWeightedFlagPlaneChannel_of_fixedFactors component lam mu nu order
    ht hfinite hgen hgate d (Polynomial.resultant P Q P.natDegree Q.natDegree)
    (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree
    (coprime_resultant_ne_zero P Q hPne hcop) le_rfl
    (fun q hq hm _ => indexed_pair_grouped_power_dvd component hinj lam mu nu order ht hfinite hgen
      P Q hPne hcop hPmem hQmem carrier hcarrier hcarrierMem d q hq hm
      (fun a => (hthick q hq a).1) (fun a => (hthick q hq a).2))
  exact C.sum_mul_cost_le

end
end ProximityPrize.SubmissionLower.MovingSourceIndexedPair6814
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceWeightedPairFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 700000
open scoped BigOperators Classical
open RCN002 RCN022 RCN032 RCN037 RCN042 RCN046 RCN093 RCN095 RCN116 RCN264 RCN338 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourcePoleBudget6814 MovingSourceAutomaticProjection6814
open MovingSourceWeightedProjection6814
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
local instance : DecidableEq Ω := Classical.decEq Ω
variable {G H A M B C : MvPolynomial (Fin 3) Ω}

def weighted_pair_certificate
    (base : ∀ V : RegularComponent Ω G M (H*A), SeparableLiteralCoordinate V.1)
    (hY : ∀ V : RegularComponent Ω G M (H*A), LiteralProjectionGate V 0)
    (hZ : ∀ V : RegularComponent Ω G M (H*A), LiteralProjectionGate V 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (D : AdaptiveNestedProjectionData base hY hZ hderiv)
    (hG : G≠0) (hB : B≠0) (hC : C≠0) (hcop : IsRelPrime B C)
    (d : ℕ) (hd : 0<d) (thick : HasThickness G H A M B C d)
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p B) (hq : RCN095.PolynomialInFlag q C) :
    let unit := projectionFamily_of_coprime_pair base hY hZ hderiv D B C hB hC hcop
      (fun V => (thick.mem_regular hd V).1) (fun V => (thick.mem_regular hd V).2) p q hp hq
    RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d) := by
  let x (axis : Axis) (V : RegularComponent Ω G M (H*A)) :=
    flagEvaluation Ω V.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis : Axis) (V : RegularComponent Ω G M (H*A)) (ht : Transcendental Ω (x axis V)) :
      (letI := (elementEmbedding Ω (CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω V.1)) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω V.1)) := by
    cases axis with
    | z =>
      have hz : Transcendental Ω (coordinate Ω V.1 2) := by simpa [x,Axis.order,RCN125.zOrder] using ht
      have he := elementEmbedding_congr ht hz (by simp [x,Axis.order,RCN125.zOrder])
      rw [he]
      exact hZ V hz
    | u =>
      have hu : Transcendental Ω (affineU Ω V.1 D.lam) := by simpa [x,Axis.order,RCN125.uOrder] using ht
      have he := elementEmbedding_congr ht hu (by simp [x,Axis.order,RCN125.uOrder])
      rw [he]
      exact D.uGate V hu
    | v =>
      have he := elementEmbedding_congr ht (D.allAffineTranscendental V) (by simp [x,Axis.order,RCN125.vOrder])
      rw [he]
      exact ⟨D.allFinite V,D.allSeparable V⟩
  have hsum (axis : Axis) :
      (∑ V : RegularComponent Ω G M (H*A), d*coordinateDegree Ω (CoordinateField Ω V.1)
        (coordinateOfGate (x axis V) (gate axis V)))≤flagMixed p q axis.flag := by
    rw [sum_mul_coordinateOfGate_eq_active
      (fun V : RegularComponent Ω G M (H*A) => CoordinateField Ω V.1)
      (x axis) (gate axis) (fun _ => d)]
    have hh := weighted_directional_degree G H A M B C hG hB hC hcop d hd thick
      (fun V : {V : RegularComponent Ω G M (H*A) // Transcendental Ω (x axis V)} => V.1)
      Subtype.val_injective axis D.lam D.mu (D.mu*D.lam) (fun V => V.2)
      (fun V => gate axis V.1) p q hp hq
    simpa only [Finset.mul_sum] using hh
  exact { z := hsum .z, yz := hsum .u, all := hsum .v }

theorem exists_weighted_pair_family
    (G H A M B C : MvPolynomial (Fin 3) Ω)
    (hG : G≠0) (hB : B≠0) (hC : C≠0) (hcop : IsRelPrime B C)
    (d : ℕ) (hd : 0<d) (thick : HasThickness G H A M B C d)
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p B) (hq : RCN095.PolynomialInFlag q C)
    (c : ℕ) [CharP Ω c]
    (hZsmall : flagMixed p q unitZFlag<c) (hYsmall : flagMixed p q unitYZFlag<c)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0) :
    ∃ base : ∀ V : RegularComponent Ω G M (H*A), SeparableLiteralCoordinate V.1,
      ∃ unit : AdaptiveUnitProjectionFamily base p q,
        Nonempty (RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d)) := by
  have mems (V : RegularComponent Ω G M (H*A)) := thick.mem_regular hd V
  have hY (V : RegularComponent Ω G M (H*A)) : LiteralProjectionGate V 0 := by
    intro ht
    have ht' : Transcendental Ω (flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.u.order 0))) := by
      simpa [Axis.order,RCN125.uOrder,affineU] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.uOrder,affineU])
    have hh := prime_projection_gate V.1 .u 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hYsmall
    rw [he] at hh
    exact hh
  have hZ (V : RegularComponent Ω G M (H*A)) : LiteralProjectionGate V 2 := by
    intro ht
    have ht' : Transcendental Ω (flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
      simpa [Axis.order,RCN125.zOrder] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
    have hh := prime_projection_gate V.1 .z 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hZsmall
    rw [he] at hh
    exact hh
  let base (V : RegularComponent Ω G M (H*A)) : SeparableLiteralCoordinate V.1 :=
    Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates V.1
      (regularComponent_ne_point Ω G M (H*A) V) (hY V) (hZ V))
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  let unit := projectionFamily_of_coprime_pair base hY hZ hderiv D B C hB hC hcop
    (fun V => (mems V).1) (fun V => (mems V).2) p q hp hq
  exact ⟨base,unit,⟨weighted_pair_certificate base hY hZ hderiv D hG hB hC hcop d hd thick p q hp hq⟩⟩

end
end ProximityPrize.SubmissionLower.MovingSourceWeightedPairFamily6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN046 RCN072 RCN084 RCN095 RCN237 RCN264 RCN338 RCN341 RCN344
open MovingSourceRegularRestriction6814 MovingSourceHybridCount6814 MovingFiberThreeSources6811

private theorem sum_pullback_le {I J : Type} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (v : J → ℕ) :
    (∑ i, v (f i))≤∑ j, v j := by
  classical
  letI : DecidableEq J := Classical.decEq J
  calc
    _=∑ j∈Finset.univ.image f, v j := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _≤_ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem hybrid_arithmetic {I : Type} [Fintype I]
    (z u v : I → ℕ) (a b c n d count zCap uCap vCap : ℕ)
    (hcount : count≤∑ i, (a*z i+b*u i+c*v i))
    (hz : n*(∑ i, z i)≤zCap) (hu : (∑ i, d*u i)≤uCap) (hv : (∑ i, d*v i)≤vCap) :
    n*d*count≤d*a*zCap+n*(b*uCap+c*vCap) := by
  have he : n*d*(∑ i, (a*z i+b*u i+c*v i))=
      d*a*(n*∑ i, z i)+n*(b*(∑ i, d*u i)+c*(∑ i, d*v i)) := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  exact (Nat.mul_le_mul_left (n*d) hcount).trans (he.le.trans
    (Nat.add_le_add (Nat.mul_le_mul_left (d*a) hz)
      (Nat.mul_le_mul_left n (Nat.add_le_add (Nat.mul_le_mul_left b hu) (Nat.mul_le_mul_left c hv)))))

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {G M R : MvPolynomial (Fin 3) Ω} {p q : FlagDegree}

def restrict_weighted_certificate
    (base : ∀ V : RegularComponent Ω G M R, SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (L : MvPolynomial (Fin 3) Ω) :
    RegularComponentWeightedInertiaResultantCertificate
      (restrict_projection_family base p q unit L).toPrimeFlagBudgetFamily (fun _ => d) where
  z := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.zCost V)).trans cert.z
  yz := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.yzCost V)).trans cert.yz
  all := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.allCost V)).trans cert.all

theorem weighted_hybrid_isolated_points
    (base : ∀ V : RegularComponent Ω G M R, SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (n zCap : ℕ)
    (hZ : n*(∑ V : RegularComponent Ω G M R, unit.toPrimeFlagBudgetFamily.zCost V)≤zCap)
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) Ω) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hG : ∀ x∈points, MvPolynomial.eval x G=0)
    (hM : ∀ x∈points, MvPolynomial.eval x M=0)
    (hR : ∀ x∈points, MvPolynomial.eval x R≠0)
    (hzero : ∀ x∈points, MvPolynomial.aeval x cut=0)
    (hisolated : ∀ x∈points, IsolatedPoint G M cut x) :
    n*d*points.card≤d*W.zOnly*zCap+n*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag) := by
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card≤∑ V : RegularComponent Ω G M R, budget.weightedCost W V := by
    apply (card_le_sum_componentSeeds Ω G M R points id hG hM hR).trans
    apply Finset.sum_le_sum
    intro V _
    by_cases he : (componentSeeds Ω G M R points id V).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω G M R points id V hx
      have hxV := componentSeeds_on_prime Ω G M R points id V x hx
      apply (budget.primeBudget V).zero_le W cut hcut
        (hisolated x hxS V.1 inferInstance (regularComponent_ne_point Ω G M R V)
          hxV (regularComponent_G_mem Ω G M R V) (regularComponent_T_mem Ω G M R V))
      · intro y hy
        exact componentSeeds_on_prime Ω G M R points id V y hy
      · intro y hy
        exact hzero y (componentSeeds_subset Ω G M R points id V hy)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  exact hybrid_arithmetic budget.zCost budget.yzCost budget.allCost W.zOnly W.yz W.all n d
    points.card zCap (flagMixed p q unitYZFlag) (flagMixed p q unitAllFlag) hcard hZ cert.yz cert.all

open RCN136 RCN207
theorem restricted_weighted_source_point_count
    {K : Type} [Field K]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (S : Source F)
    (carrier : MvPolynomial (Fin 3) Ω) (pOld : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F) (hp : PolynomialInFlag pOld carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(pOld.zOnly+pOld.yz+pOld.all)<c)
    (h2 : (2 : Ω)≠0) (hfact : (S.k.factorial : Ω)≠0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (R : MvPolynomial (Fin 3) Ω) (hHdiv : surfaceMap phi (RCN313.polyH K F)∣R)
    (base : ∀ V : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) Ω) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hG : ∀ v∈points, MvPolynomial.eval v carrier=0)
    (hM : ∀ v∈points, MvPolynomial.eval v
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target)=0)
    (hR : ∀ v∈points, MvPolynomial.eval v (R*S.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) cut v) :
    S.d*d*points.card≤d*W.zOnly*flagMixed pOld unitZFlag S.flag+
      S.d*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag) := by
  let M := movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target
  let base' := fun V : RegularComponent Ω carrier M (R*S.leading phi) => base (forgetExtra (S.leading phi) V)
  let unit' := restrict_projection_family base p q unit (S.leading phi)
  let cert' := restrict_weighted_certificate base unit d cert (S.leading phi)
  have hH (V : RegularComponent Ω carrier M (R*S.leading phi)) : surfaceMap phi (RCN313.polyH K F)∉V.1 := by
    intro hh
    exact regularComponent_H_not_mem Ω carrier M (R*S.leading phi) V
      (V.1.mem_of_dvd (dvd_mul_of_dvd_left hHdiv _) hh)
  have hZ := old_z_bound_on_new_projections phi F S carrier pOld hcarrier hcarrierF hp
    c hunit h2 hfact Q A target hQ hA (R*S.leading phi)
    hH (extra_not_mem (S.leading phi)) base' p q unit'
  exact weighted_hybrid_isolated_points base' unit' d cert' S.d (flagMixed pOld unitZFlag S.flag)
    hZ W cut hcut points hG hM hR hzero hisolated

end
end ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
open MvPolynomial RCN084 RCN207

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

theorem quotient_nonzero_at_regular_point (F G : Poly) (hdiv : G∣F)
    (x : Fin 3 → K) (hG : MvPolynomial.eval x G=0)
    (hreg : MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) F)≠0) :
    ∃ Q : Poly, F=G*Q ∧ MvPolynomial.eval x Q≠0 := by
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨Q,hQ,?_⟩
  rw [hQ,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hG,zero_mul,add_zero] at hreg
  exact (mul_ne_zero_iff.mp hreg).2

theorem isolated_whole_of_factor (F G N A : Poly) (hdiv : G∣F)
    (x : Fin 3 → K) (hG : MvPolynomial.eval x G=0)
    (hreg : MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) F)≠0)
    (hisolated : IsolatedPoint G N A x) : IsolatedPoint F N A x := by
  obtain ⟨Q,hQ,hQne⟩ := quotient_nonzero_at_regular_point F G hdiv x hG hreg
  intro P hprime hnotpoint hpoint hFmem hNmem
  have hQnot : Q∉P := by
    intro hmem
    apply hQne
    exact hpoint hmem
  have hGmem : G∈P := by
    rw [hQ] at hFmem
    exact (hprime.mem_or_mem hFmem).resolve_right hQnot
  exact hisolated P hprime hnotpoint hpoint hGmem hNmem

end
end ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceMovingDegrees6814 MovingSourceCoupledClearing6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

end
end ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedPointCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 700000
open RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN264 RCN313 RCN338 RCN341
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814
open MovingSourceWeightedProjection6814 MovingSourceWeightedPairFamily6814 MovingSourceWeightedPairPoints6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [CharP E 2130706433]
variable (f : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "Poly3" => MvPolynomial (Fin 3) E
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap f)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)

abbrev ExtendedMovingFamily (F : MvPolynomial (Fin 4) K) (Q A : Poly3) :=
  RegularComponent OmegaT (extendedCarrier f F) (extendedEquation f F Q A) (extendedDenominator f F A)

theorem extended_source_pair_family
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ∃ base : ∀ V : ExtendedMovingFamily f F Q A, SeparableLiteralCoordinate V.1,
      ∃ unit : AdaptiveUnitProjectionFamily base (ordinaryFlag S.P) (ordinaryFlag T.P),
        Nonempty (RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d)) := by
  obtain ⟨B,C,hB,hC,hBC,hBflag,hCflag,hthick⟩ := exists_extended_thick_pair f F S T hcop d hS hT hchar Q A hden hQ hA
  have ht : HasThickness (extendedCarrier f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
      (extendedEquation f F Q A) B C d := hthick
  have hG : extendedCarrier f F≠0 := by
    intro hh
    exact hF (extendedCarrier_injective f (by simpa only [extendedCarrier,map_zero] using hh))
  exact exists_weighted_pair_family (extendedCarrier f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
    (extendedEquation f F Q A) B C hG hB hC hBC d hd ht
    (ordinaryFlag S.P) (ordinaryFlag T.P) hBflag hCflag 2130706433 hz hu
    (extendedCarrier_derivative_nonzero f F hpos hsmall)

theorem extended_source_pair_point_count
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (extendedCarrier f F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433)
    (W : FlagDegree) (cut : Poly3T) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → OmegaT))
    (hG : ∀ v∈points, MvPolynomial.eval v (extendedCarrier f F)=0)
    (hM : ∀ v∈points, MvPolynomial.eval v (extendedEquation f F Q A)=0)
    (hregular : ∀ v∈points, MvPolynomial.eval v (extendedDenominator f F A*SZ.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint (extendedCarrier f F) (extendedEquation f F Q A) cut v) :
    SZ.d*d*points.card≤d*W.zOnly*flagMixed p unitZFlag SZ.flag+
      SZ.d*(W.yz*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag+
        W.all*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  obtain ⟨base,unit,⟨cert⟩⟩ := extended_source_pair_family f F hF hpos hsmall S T hcop d hd hS hT hchar
    Q A hden hQ hA hz hu
  have hGne : extendedCarrier f F≠0 := by
    intro hh
    exact hF (extendedCarrier_injective f (by simpa only [extendedCarrier,map_zero] using hh))
  have hHdiv : surfaceMap phi (polyH K F)∣extendedDenominator f F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (SZ.k.factorial : OmegaT)≠0 := SecondJetOwnShape.factorial_ne SZ.k hZchar
  exact restricted_weighted_source_point_count phi F SZ (extendedCarrier f F) p hGne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift Q) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA) (extendedDenominator f F A) hHdiv base unit d cert
    W cut hcut points hG hM hregular hzero hisolated

def ExtendedPointBudget (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (Q A : Poly3) (scale z u v : ℕ) : Prop :=
  ∀ (W : FlagDegree) (cut : Poly3T), PolynomialInFlag W cut →
    ∀ points : Finset (Fin 3 → OmegaT),
      (∀ x∈points, MvPolynomial.eval x (extendedCarrier f F)=0) →
      (∀ x∈points, MvPolynomial.eval x (extendedEquation f F Q A)=0) →
      (∀ x∈points, MvPolynomial.eval x (extendedDenominator f F A*SZ.leading phi)≠0) →
      (∀ x∈points, MvPolynomial.aeval x cut=0) →
      (∀ x∈points, IsolatedPoint (extendedCarrier f F) (extendedEquation f F Q A) cut x) →
      scale*points.card≤W.zOnly*z+W.yz*u+W.all*v

theorem extended_sources_point_budget
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (extendedCarrier f F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ExtendedPointBudget f F SZ Q A (SZ.d*d) (d*flagMixed p unitZFlag SZ.flag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hh := extended_source_pair_point_count f F hF hpos hsmall S T hcop d hd hS hT hchar
    SZ hZchar p hp hunit Q A hden hQ hA hz hu W cut hcut points hG hM hregular hzero hisolated
  convert hh using 1 <;> ring

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedPointCount6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814 MovingSourceExtendedPointCount6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap eta)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)
local instance : Algebra (RatFunc E) OmegaT := targetAlgebra E
local instance : IsScalarTower E (RatFunc E) OmegaT := target_tower E

def frozenCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) F
def frozenH (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) (polyH K F)
def frozenG (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) (polyG K F)
abbrev ExtendedFactorFamily (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) E)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) E) :=
  RegularComponent E G (filteredCut n coeff (frozenH eta F) (frozenG eta F)) (frozenH eta F)

def extendedTargetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) E)
    (Q A : MvPolynomial (Fin 3) E) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate E)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) E) : scalarPolynomialMap E OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap E]

theorem lift_frozen (P : MvPolynomial (Fin 4) K) :
    lift (surfaceMap (codeMap eta) P)=surfaceMap phi P := by
  simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem eval_lift_embedding (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (f : CoordinateField E C →ₐ[E] OmegaT) (P : MvPolynomial (Fin 3) E) :
    MvPolynomial.eval (embeddingPoint C f) (lift P)=f (coordinateEvaluation E C P) := by
  rw [MvPolynomial.eval_map,coefficientEmbedding_eq_algebraMap E]
  exact AlgHom.congr_fun (embeddingPoint_aeval C f) P

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedMovingDegrees6814
end MergedPart8
