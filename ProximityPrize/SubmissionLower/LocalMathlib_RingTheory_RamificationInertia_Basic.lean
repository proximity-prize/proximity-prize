/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Thomas Browning
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_Galois_IsGaloisGroup
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Flat_TorsionFree
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_RamificationInertia_Inertia
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_RamificationInertia_Ramification
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Spectrum_Prime_FreeLocus
section ProximityFlatProofPort
section
namespace Ideal
variable {R:Type*} [CommRing R] (p:Ideal R) [p.IsPrime] (S:Type*) [CommRing S] [Algebra R S]
open IsLocalRing Module OrderIso PrimeSpectrum in
theorem sum_ramification_inertia_eq_finrank_fiber
    [Algebra.QuasiFinite R S] [Fintype (p.primesOver S)]:
    ∑ q:p.primesOver S,q.1.ramificationIdx R*q.1.inertiaDeg R=
      finrank p.ResidueField (p.Fiber S):=by
  let:=Fintype.ofFinite (PrimeSpectrum (p.Fiber S))
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum, ←(primesOverOrderIsoFiber R S p).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [toEquiv_symm,coe_symm_toEquiv,coe_primesOverOrderIsoFiber_symm_apply]
  set r:=q.1.comap Algebra.TensorProduct.includeRight
  let:=Localization.AtPrime.algebraOfLiesOver p r
  rw [ramificationIdx_eq p r,inertiaDeg_eq p r]
  let Rp:=Localization.AtPrime p
  let Sq:=Localization.AtPrime q.1
  let Sr:=Localization.AtPrime r
  let κp:=p.ResidueField
  let κr:=r.ResidueField
  let A:=Sr ⧸ p.map (algebraMap R Sr)
  suffices length Sr A*finrank κp κr=finrank κp Sq by simpa using congr_arg ENat.toNat this
  calc length Sr A*finrank κp κr=length Sr A*length κp κr:=by rw [length_eq_finrank]
    _=length Rp A:=(length_restrictScalars Rp Sr A).symm
    _=length Rp Sq:=(Fiber.localizationAlgEquivQuotient p q.1).toLinearEquiv.length_eq.symm
    _=length κp Sq:=length_eq_of_surjective residue_surjective
    _=finrank κp Sq:=length_eq_finrank κp Sq
theorem sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]:
    ∑ q:p.primesOver S,q.1.ramificationIdx R*q.1.inertiaDeg R=Module.finrank R S:=by
  rw [sum_ramification_inertia_eq_finrank_fiber,finrank_fiber_eq_finrank]
theorem sum_ramification_inertia_eq_card
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    {G:Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S]:
    ∑ q:p.primesOver S,q.1.ramificationIdx R*q.1.inertiaDeg R=Nat.card G:=by
  let:=IsGaloisGroup.finite G R S
  rw [sum_ramification_inertia_eq_finrank,IsGaloisGroup.card_eq_finrank' G R S]
end Ideal
