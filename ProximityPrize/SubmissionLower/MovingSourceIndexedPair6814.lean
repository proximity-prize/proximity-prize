import ProximityPrize.SubmissionLower.MovingSourceLocalCarrier6814

/-! Weighted pair resultants on the original indexed curve family.
Each curve may have its own irreducible carrier factor. All such pieces
over a coefficient prime feed ONE resultant exponent. -/
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

#print axioms indexed_pair_grouped_power_dvd
#print axioms indexed_pair_degree_sum_le
end
end ProximityPrize.SubmissionLower.MovingSourceIndexedPair6814
