import ProximityPrize.SubmissionLower.MovingSourceThickGenericPair6814

/-! Canonical carrier factors for the weighted pair count. Localization
does not erase the chosen factor, and a relation containing a coprime
pair cannot collapse to that single carrier equation. -/
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

#print axioms exists_irreducible_divisor_mem_prime
#print axioms local_carrier_prime_and_contract
#print axioms local_carrier_relation_bar_ne_bot
end
end ProximityPrize.SubmissionLower.MovingSourceLocalCarrier6814
