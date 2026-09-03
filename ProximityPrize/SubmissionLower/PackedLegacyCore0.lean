import ProximityPrize.Benchmark.TargetLower
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.GradedMulAction
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Derivation.ToSquareZero
import ProximityPrize.SubmissionLower.KernelEval

/-! Packed from ProximityPrize.SubmissionLower.I5. -/
section PackedLegacy_I5
namespace ProximityPrize.SubmissionLower.RCN072
noncomputable section
variable (K:Type) [Field K]
abbrev Poly3:=MvPolynomial (Fin 3) K
def freezeCoordinates (v:Fin 3 → K) (n:ℕ):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (fun i => if i.val < n then MvPolynomial.C (v i) else MvPolynomial.X i)
def freezeKernel (v:Fin 3 → K) (n:ℕ):Ideal (Poly3 K):=
 RingHom.ker (freezeCoordinates K v n).toRingHom
instance freezeKernel_isPrime (v:Fin 3 → K) (n:ℕ):
   (freezeKernel K v n).IsPrime:=
 RingHom.ker_isPrime (freezeCoordinates K v n).toRingHom
theorem freeze_comp (v:Fin 3 → K) (n m:ℕ) (hnm:n ≤ m):
   (freezeCoordinates K v m).comp (freezeCoordinates K v n)=
     freezeCoordinates K v m:=by
 ext i
 by_cases hi:i.val < n
 · simp [freezeCoordinates,hi,lt_of_lt_of_le hi hnm]
 · simp [freezeCoordinates,hi]
theorem freezeKernel_mono (v:Fin 3 → K) (n m:ℕ) (hnm:n ≤ m):
   freezeKernel K v n ≤ freezeKernel K v m:=by
 intro F hF
 change freezeCoordinates K v n F=0 at hF
 change freezeCoordinates K v m F=0
 have h:=AlgHom.congr_fun (freeze_comp K v n m hnm) F
 change freezeCoordinates K v m (freezeCoordinates K v n F)=
   freezeCoordinates K v m F at h
 rw [hF,map_zero] at h
 exact h.symm
theorem coordinate_difference_ne_zero (i:Fin 3) (a:K):
   (MvPolynomial.X i-MvPolynomial.C a:Poly3 K)≠0:=by
 intro h
 have h':=congrArg (MvPolynomial.pderiv i) h
 simp at h'
theorem freezeKernel_lt_succ (v:Fin 3 → K) (n:ℕ) (hn:n < 3):
   freezeKernel K v n < freezeKernel K v (n+1):=by
 classical
 let i:Fin 3:=⟨n,hn⟩
 let F:Poly3 K:=MvPolynomial.X i-MvPolynomial.C (v i)
 have hmem:F∈freezeKernel K v (n+1):=by
   change freezeCoordinates K v (n+1) F=0
   simp [freezeCoordinates,F,i]
 have hnot:F∉freezeKernel K v n:=by
   change freezeCoordinates K v n F≠0
   simpa [freezeCoordinates,F,i] using coordinate_difference_ne_zero K i (v i)
 apply lt_of_le_of_ne (freezeKernel_mono K v n (n+1) (Nat.le_succ n))
 intro heq
 exact hnot (heq.symm ▸ hmem)
def pointKernel (v:Fin 3 → K):Ideal (Poly3 K):=
 RingHom.ker (MvPolynomial.aeval v).toRingHom
instance pointKernel_isPrime (v:Fin 3 → K):(pointKernel K v).IsPrime:=
 RingHom.ker_isPrime (MvPolynomial.aeval v).toRingHom
theorem freezeKernel_three (v:Fin 3 → K):
   freezeKernel K v 3=pointKernel K v:=by
 have h:freezeCoordinates K v 3=
     (Algebra.ofId K (Poly3 K)).comp (MvPolynomial.aeval v):=by
   ext i
   simp [freezeCoordinates]
 apply Ideal.ext
 intro F
 change freezeCoordinates K v 3 F=0 ↔ MvPolynomial.aeval v F=0
 rw [h]
 change MvPolynomial.C (MvPolynomial.aeval v F)=0 ↔ _
 simp
theorem pointKernel_height_ge_three (v:Fin 3 → K):
   (3:ℕ∞) ≤ (pointKernel K v).height:=by
 have h01:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 0 (by decide))
 have h12:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 1 (by decide))
 have h23:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 2 (by decide))
 have h1:(1:ℕ∞) ≤ (freezeKernel K v 1).height:=by
   calc
     1=(0:ℕ∞)+1:=by simp
     _ ≤ (freezeKernel K v 0).height+1:=by gcongr;exact zero_le
     _ ≤ (freezeKernel K v 1).height:=h01
 have h2:(2:ℕ∞) ≤ (freezeKernel K v 2).height:=by
   calc
     2=(1:ℕ∞)+1:=by norm_num
     _ ≤ (freezeKernel K v 1).height+1:=by gcongr
     _ ≤ (freezeKernel K v 2).height:=h12
 rw [←freezeKernel_three K v]
 calc
   3=(2:ℕ∞)+1:=by norm_num
   _ ≤ (freezeKernel K v 2).height+1:=by gcongr
   _ ≤ (freezeKernel K v 3).height:=h23
def cutIdeal (F T:Poly3 K):Ideal (Poly3 K):=Ideal.span {F,T}
def componentSet (F T:Poly3 K):Set (Ideal (Poly3 K)):=
 (cutIdeal K F T).minimalPrimes
theorem componentSet_finite (F T:Poly3 K):(componentSet K F T).Finite:=
 Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
def componentFamily (F T:Poly3 K):Finset (Ideal (Poly3 K)):=
 (componentSet_finite K F T).toFinset
@[simp] theorem mem_componentFamily (F T:Poly3 K) (P:Ideal (Poly3 K)):
   P∈componentFamily K F T ↔ P∈(cutIdeal K F T).minimalPrimes:=
 Set.Finite.mem_toFinset _
theorem component_isPrime (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):P.IsPrime:=
 ((mem_componentFamily K F T P).mp hP).isPrime
theorem cutIdeal_le_component (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):cutIdeal K F T ≤ P:=
 ((mem_componentFamily K F T P).mp hP).le
theorem component_height_le_two (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):P.height ≤ 2:=by
 classical
 have hm:P∈(Ideal.span ({F,T}:Finset (Poly3 K))).minimalPrimes:=by
   simpa only [Finset.coe_insert,Finset.coe_singleton,cutIdeal] using
     (mem_componentFamily K F T P).mp hP
 have hh:=Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
 have hc:({F,T}:Finset (Poly3 K)).card ≤ 2:=
   (Finset.card_insert_le F {T}).trans (by simp)
 exact hh.trans (by exact_mod_cast hc)
theorem exists_component_of_common_point
   (F T:Poly3 K) (v:Fin 3 → K)
   (hF:MvPolynomial.eval v F=0) (hT:MvPolynomial.eval v T=0):
   ∃ P∈componentFamily K F T,P ≤ pointKernel K v:=by
 have hcut:cutIdeal K F T ≤ pointKernel K v:=by
   apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hF
   · exact hT
 obtain ⟨P,hP,hle⟩:=Ideal.exists_minimalPrimes_le hcut
 exact ⟨P,(mem_componentFamily K F T P).mpr hP,hle⟩
theorem component_ne_pointKernel
   (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T) (v:Fin 3 → K):
   P≠pointKernel K v:=by
 intro heq
 have hle:=component_height_le_two K F T P hP
 rw [heq] at hle
 have hbad:(3:ℕ∞) ≤ 2:=(pointKernel_height_ge_three K v).trans hle
 norm_num at hbad
end
end ProximityPrize.SubmissionLower.RCN072
end PackedLegacy_I5

/-! Packed from ProximityPrize.SubmissionLower.E6. -/
section PackedLegacy_E6
namespace ProximityPrize.SubmissionLower.RCN264
open RCN072
noncomputable section
variable (K:Type) [Field K]
def regularComponents (G T H:MvPolynomial (Fin 3) K):
   Finset (Ideal (MvPolynomial (Fin 3) K)):=by
 classical
 exact (componentFamily K G T).filter (fun P => H∉P)
abbrev RegularComponent (G T H:MvPolynomial (Fin 3) K):=
 {P:Ideal (MvPolynomial (Fin 3) K)//P∈regularComponents K G T H}
variable (G T H:MvPolynomial (Fin 3) K)
theorem regularComponent_mem (C:RegularComponent K G T H):
   C.1∈componentFamily K G T:=by
 classical
 exact (Finset.mem_filter.mp C.2).1
instance regularComponent_isPrime (C:RegularComponent K G T H):C.1.IsPrime:=
 component_isPrime K G T C.1 (regularComponent_mem K G T H C)
theorem regularComponent_H_not_mem (C:RegularComponent K G T H):H∉C.1:=by
 classical
 exact (Finset.mem_filter.mp C.2).2
theorem regularComponent_G_mem (C:RegularComponent K G T H):G∈C.1:=
 cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
   (Ideal.subset_span (Set.mem_insert G {T}))
theorem regularComponent_T_mem (C:RegularComponent K G T H):T∈C.1:=
 cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
   (Ideal.subset_span (Set.mem_insert_of_mem G (Set.mem_singleton T)))
theorem regularComponent_ne_point (C:RegularComponent K G T H) (v:Fin 3 → K):
   C.1≠RingHom.ker (MvPolynomial.aeval v).toRingHom:=
 component_ne_pointKernel K G T C.1 (regularComponent_mem K G T H C) v
theorem exists_regular_component (v:Fin 3 → K)
   (hG:MvPolynomial.eval v G=0) (hT:MvPolynomial.eval v T=0)
   (hH:MvPolynomial.eval v H≠0):
   ∃ C:RegularComponent K G T H,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 obtain ⟨P,hP,hv⟩:=exists_component_of_common_point K G T v hG hT
 have hnot:H∉P:=by
   intro h
   exact hH (hv h)
 exact ⟨⟨P,Finset.mem_filter.mpr ⟨hP,hnot⟩⟩,hv⟩
def componentSeeds {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → K)
   (C:RegularComponent K G T H):Finset Seed:=by
 classical
 exact S.filter (fun γ => C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom)
theorem componentSeeds_subset {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K) (C:RegularComponent K G T H):
   componentSeeds K G T H S v C ⊆ S:=by
 classical
 exact Finset.filter_subset _ _
theorem componentSeeds_on_prime {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K) (C:RegularComponent K G T H)
   (γ:Seed) (hγ:γ∈componentSeeds K G T H S v C):
   C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom:=by
 classical
 exact (Finset.mem_filter.mp hγ).2
theorem card_le_sum_componentSeeds {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0):
   S.card ≤ ∑ C:RegularComponent K G T H,(componentSeeds K G T H S v C).card:=by
 classical
 letI:DecidableEq Seed:=Classical.decEq Seed
 have hcover:S ⊆ Finset.univ.biUnion (componentSeeds K G T H S v):=by
   intro γ hγ
   obtain ⟨C,hC⟩:=exists_regular_component K G T H (v γ) (hG γ hγ) (hT γ hγ) (hH γ hγ)
   apply Finset.mem_biUnion.mpr
   exact ⟨C,Finset.mem_univ C,Finset.mem_filter.mpr ⟨hγ,hC⟩⟩
 exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
theorem aggregate_component_incidence {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0)
   (gap nodes pencil:ℕ) (cap budget:Fin 3 → ℕ)
   (degree:RegularComponent K G T H → Fin 3 → ℕ)
   (hcomponent:∀ C,
     (componentSeeds K G T H S v C).card*gap ≤
       nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2)
   (hbudget:∀ i,(∑ C,degree C i) ≤ budget i):
   S.card*gap ≤ nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=by
 classical
 have hfubini:(∑ C:RegularComponent K G T H,∑ i:Fin 3,cap i*degree C i)=
     ∑ i:Fin 3,cap i*(∑ C:RegularComponent K G T H,degree C i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   S.card*gap ≤ (∑ C:RegularComponent K G T H,
       (componentSeeds K G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap (card_le_sum_componentSeeds K G T H S v hG hT hH)
   _=∑ C:RegularComponent K G T H,
       (componentSeeds K G T H S v C).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent K G T H,
       (nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2):=
     Finset.sum_le_sum (fun C _ => hcomponent C)
   _=nodes*(∑ i:Fin 3,cap i*(∑ C:RegularComponent K G T H,degree C i))+
       pencil*gap*(∑ C:RegularComponent K G T H,degree C 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left nodes (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left (cap i) (hbudget i))))
       (Nat.mul_le_mul_left (pencil*gap) (hbudget 2))
end
end ProximityPrize.SubmissionLower.RCN264
end PackedLegacy_E6

/-! Packed from ProximityPrize.SubmissionLower.CM. -/
section PackedLegacy_CM
namespace ProximityPrize.SubmissionLower.RCN354
noncomputable section
variable {K A S:Type*} [Field K] [CommRing A] [CommRing S]
 [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
theorem pointKernel_isMaximal (phi:A →ₐ[K] K):
   (RingHom.ker phi.toRingHom).IsMaximal:=by
 apply RingHom.ker_isMaximal_of_surjective phi.toRingHom
 intro c
 exact ⟨algebraMap K A c,by simp⟩
theorem quotient_scalar_compatibility (phi:A →ₐ[K] K) (N:Ideal S)
   (hN:N.comap (algebraMap A S)=RingHom.ker phi.toRingHom) (a:A):
   Ideal.Quotient.mkₐ K N (algebraMap A S a)=
     algebraMap K (S ⧸ N) (phi a):=by
 have ha:a-algebraMap K A (phi a)∈RingHom.ker phi.toRingHom:=by
   change phi (a-algebraMap K A (phi a))=0
   simp
 have hamem:algebraMap A S (a-algebraMap K A (phi a))∈N:=by
   change a-algebraMap K A (phi a)∈N.comap (algebraMap A S)
   rw [hN]
   exact ha
 have hz:Ideal.Quotient.mkₐ K N
     (algebraMap A S (a-algebraMap K A (phi a)))=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr hamem
 have hconstant (c:K):
     algebraMap A S (algebraMap K A c)=algebraMap K S c:=
   (IsScalarTower.algebraMap_apply K A S c).symm
 apply sub_eq_zero.mp
 simpa [map_sub,hconstant] using hz
section IntegralLift
variable [IsAlgClosed K] [Algebra.IsIntegral A S]
theorem exists_point_lift
   (hinj:Function.Injective (algebraMap A S)) (phi:A →ₐ[K] K):
   ∃ psi:S →ₐ[K] K,psi.comp (IsScalarTower.toAlgHom K A S)=phi:=by
 classical
 letI:(RingHom.ker phi.toRingHom).IsMaximal:=pointKernel_isMaximal phi
 have hker:RingHom.ker (algebraMap A S) ≤ RingHom.ker phi.toRingHom:=by
   rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
   exact bot_le
 obtain ⟨N,hNmax,hN⟩:=Ideal.exists_ideal_over_maximal_of_isIntegral
   (S:=S) (RingHom.ker phi.toRingHom) hker
 letI:N.IsMaximal:=hNmax
 let q:S →ₐ[K] S ⧸ N:=Ideal.Quotient.mkₐ K N
 have hcomp:(algebraMap K (S ⧸ N)).comp phi.toRingHom=
     (Ideal.Quotient.mk N).comp (algebraMap A S):=by
   ext a
   exact (quotient_scalar_compatibility phi N hN a).symm
 letI:Algebra.IsIntegral K (S ⧸ N):=by
   constructor
   intro z
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective z
   exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk N) hcomp
     (Algebra.IsIntegral.isIntegral (R:=A) s)
 let e:K ≃ₐ[K] S ⧸ N:=AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ N))
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S ⧸ N))
 let psi:S →ₐ[K] K:=e.symm.toAlgHom.comp q
 refine ⟨psi,?_⟩
 ext a
 change psi (algebraMap A S a)=phi a
 apply e.injective
 change e (e.symm (q (algebraMap A S a)))=e (phi a)
 rw [e.apply_symm_apply]
 have he (c:K):e c=algebraMap K (S ⧸ N) c:=by
   simpa using e.commutes c
 rw [he]
 exact quotient_scalar_compatibility phi N hN a
def chosenPointLift (hinj:Function.Injective (algebraMap A S))
   (phi:A →ₐ[K] K):S →ₐ[K] K:=
 Classical.choose (exists_point_lift hinj phi)
theorem chosenPointLift_spec (hinj:Function.Injective (algebraMap A S))
   (phi:A →ₐ[K] K):
   (chosenPointLift hinj phi).comp (IsScalarTower.toAlgHom K A S)=phi:=
 Classical.choose_spec (exists_point_lift hinj phi)
theorem chosenPointLift_injective (hinj:Function.Injective (algebraMap A S)):
   Function.Injective (chosenPointLift hinj:(A →ₐ[K] K) → (S →ₐ[K] K)):=by
 intro phi theta h
 have hrestrict:=congrArg
   (fun psi:S →ₐ[K] K => psi.comp (IsScalarTower.toAlgHom K A S)) h
 simpa only [chosenPointLift_spec] using hrestrict
end IntegralLift
section IntegralBase
variable [IsAlgClosed K] (R:Type*) [CommRing R]
 [Algebra R A] [Algebra R S] [IsScalarTower R A S] [Algebra.IsIntegral R S]
include R in
theorem exists_point_lift_of_integral_base
   (hinj:Function.Injective (algebraMap A S)) (phi:A →ₐ[K] K):
   ∃ psi:S →ₐ[K] K,psi.comp (IsScalarTower.toAlgHom K A S)=phi:=by
 letI:Algebra.IsIntegral A S:=Algebra.IsIntegral.tower_top R
 exact exists_point_lift hinj phi
end IntegralBase
end
end ProximityPrize.SubmissionLower.RCN354
end PackedLegacy_CM

/-! Packed from ProximityPrize.SubmissionLower.A. -/
section PackedLegacy_A

end PackedLegacy_A

/-! Packed from ProximityPrize.SubmissionLower.CW. -/
section PackedLegacy_CW
section ProximityFlatProofPort
variable {A B:Type*} [CommRing A] [CommRing B] [Algebra A B]
 (P:Ideal B) (p:Ideal A) [P.LiesOver p]
instance module_finite_of_liesOver [Module.Finite A B]:Module.Finite (A ⧸ p) (B ⧸ P):=
 Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)
example [Module.Finite A B]:Module.Finite (A ⧸ P.under A) (B ⧸ P):=inferInstance
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B]:
   Algebra.FiniteType (A ⧸ p) (B ⧸ P):=
 Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)
instance isNoetherian_of_liesOver [IsNoetherian A B]:IsNoetherian (A ⧸ p) (B ⧸ P):=
 isNoetherian_of_tower A inferInstance
instance QuotientMapQuotient.isNoetherian [IsNoetherian A B]:
   IsNoetherian (A ⧸ p) (B ⧸ p.map (algebraMap A B)):=
 isNoetherian_of_tower A <|
   isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap <|
     LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
end ProximityFlatProofPort
end PackedLegacy_CW

/-! Packed from ProximityPrize.SubmissionLower.S0. -/
section PackedLegacy_S0
section ProximityFlatProofPort
theorem CharP.ker_intAlgebraMap_eq_span
   {R:Type*} [Ring R] (p:ℕ) [CharP R p]:
   RingHom.ker (algebraMap ℤ R)=Ideal.span {(p:ℤ)}:=by
 ext a
 simp [CharP.intCast_eq_zero_iff R p,Ideal.mem_span_singleton]
variable {R:Type*} [CommRing R]
namespace CharP
variable (R) in
theorem quotient (p:ℕ) [hp1:Fact p.Prime] (hp2:↑p∈nonunits R):
   CharP (R ⧸ (Ideal.span ({(p:R)}:Set R):Ideal R)) p:=
 have hp0:(p:R ⧸ (Ideal.span {(p:R)}:Ideal R))=0:=
   map_natCast (Ideal.Quotient.mk (Ideal.span {(p:R)}:Ideal R)) p ▸
     Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
 ringChar.of_eq <|
   Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun h1 =>
     hp2 <|
       isUnit_iff_dvd_one.2 <|
         Ideal.mem_span_singleton.1 <|
           Ideal.Quotient.eq_zero_iff_mem.1 <|
             @Subsingleton.elim _ (@CharOne.subsingleton _ _ (ringChar.of_eq h1)) _ _
theorem quotient' (p:ℕ) [CharP R p] (I:Ideal R) (h:∀ x:ℕ,(x:R)∈I → (x:R)=0):
   CharP (R ⧸ I) p where
 cast_eq_zero_iff x:=by
   rw [←cast_eq_zero_iff R p x, ←map_natCast (Ideal.Quotient.mk I)]
   refine Ideal.Quotient.eq.trans (?_:↑x-0∈I ↔ _)
   rw [sub_zero]
   exact ⟨h x,fun h' => h'.symm ▸ I.zero_mem⟩
theorem quotient_iff (n:ℕ) [CharP R n] (I:Ideal R):
   CharP (R ⧸ I) n ↔ ∀ x:ℕ,↑x∈I → (x:R)=0:=by
 refine ⟨fun _ x hx => ?_,CharP.quotient' n I⟩
 rw [CharP.cast_eq_zero_iff R n, ←CharP.cast_eq_zero_iff (R ⧸ I) n _]
 exact (Submodule.Quotient.mk_eq_zero I).mpr hx
theorem quotient_iff_le_ker_natCast (n:ℕ) [CharP R n] (I:Ideal R):
   CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R):=by
 rw [CharP.quotient_iff,RingHom.ker_eq_comap_bot];rfl
end CharP
lemma Ideal.natCast_mem_of_charP_quotient (p:ℕ) (I:Ideal R) [CharP (R ⧸ I) p]:
   (p:R)∈I:=
 Ideal.Quotient.eq_zero_iff_mem.mp <| by simp
theorem Ideal.Quotient.index_eq_zero (I:Ideal R):(↑I.toAddSubgroup.index:R ⧸ I)=0:=by
 rw [AddSubgroup.index,Nat.card_eq]
 split_ifs with hq;swap
 · simp
 letI:Fintype (R ⧸ I):=@Fintype.ofFinite _ hq
 exact Nat.cast_card_eq_zero (R ⧸ I)
end ProximityFlatProofPort
end PackedLegacy_S0

/-! Packed from ProximityPrize.SubmissionLower.HY. -/
section PackedLegacy_HY
section ProximityFlatProofPort
@[simp high]
theorem LinearMap.det_zero'' {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
   [Module.Free R M] [Module.Finite R M] [Nontrivial M]:LinearMap.det (0:M →ₗ[R] M)=0:=by
 letI:Nonempty (Module.Free.ChooseBasisIndex R M):=(Module.Free.chooseBasis R M).index_nonempty
 nontriviality R
 exact LinearMap.det_zero' (Module.Free.chooseBasis R M)
end ProximityFlatProofPort
end PackedLegacy_HY

/-! Packed from ProximityPrize.SubmissionLower.HN. -/
section PackedLegacy_HN
section ProximityFlatProofPort
theorem Int.natAbs_eq_iff_associated {a b:ℤ}:a.natAbs=b.natAbs ↔ Associated a b:=by
 refine Int.natAbs_eq_natAbs_iff.trans ?_
 constructor
 · rintro (rfl | rfl)
   · rfl
   · exact ⟨-1,by simp⟩
 · rintro ⟨u,rfl⟩
   obtain rfl | rfl:=Int.units_eq_one_or u
   · exact Or.inl (by simp)
   · exact Or.inr (by simp)
end ProximityFlatProofPort
end PackedLegacy_HN

/-! Packed from ProximityPrize.SubmissionLower.HO. -/
section PackedLegacy_HO
section ProximityFlatProofPort
namespace Int
@[simps]
def natAbsHom:ℤ →*₀ ℕ where
 toFun:=Int.natAbs
 map_mul':=Int.natAbs_mul
 map_one':=Int.natAbs_one
 map_zero':=Int.natAbs_zero
lemma natAbs_natCast_sub_natCast_of_ge {a b:ℕ} (h:b ≤ a):Int.natAbs (↑a-↑b)=a-b:=by
 lia
lemma natAbs_natCast_sub_natCast_of_le {a b:ℕ} (h:a ≤ b):Int.natAbs (↑a-↑b)=b-a:=by
 lia
end Int
end ProximityFlatProofPort
end PackedLegacy_HO

/-! Packed from ProximityPrize.SubmissionLower.IA. -/
section PackedLegacy_IA
section ProximityFlatProofPort
namespace Int
theorem isCoprime_iff_nat_coprime {a b:ℤ}:IsCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs:=by
 rw [isCoprime_iff_gcd_eq_one,Nat.coprime_iff_gcd_eq_one,gcd_eq_natAbs]
theorem gcd_ne_one_iff_gcd_mul_right_ne_one {a:ℤ} {m n:ℕ}:
   a.gcd (m*n)≠1 ↔ a.gcd m≠1∨a.gcd n≠1:=by
 simp only [←isCoprime_iff_gcd_eq_one, ←not_and_or,not_iff_not,IsCoprime.mul_right_iff]
theorem sq_of_gcd_eq_one {a b c:ℤ} (h:Int.gcd a b=1) (heq:a*b=c^2):
   ∃ a0:ℤ,a=a0^2∨a= -a0^2:=by
 have h':IsUnit (GCDMonoid.gcd a b):=by
   rw [←coe_gcd,h,Int.ofNat_one]
   exact isUnit_one
 obtain ⟨d,⟨u,hu⟩⟩:=exists_associated_pow_of_mul_eq_pow h' heq
 use d
 rw [←hu]
 rcases Int.units_eq_one_or u with hu' | hu' <;>
   · rw [hu']
     simp
theorem sq_of_isCoprime {a b c:ℤ} (h:IsCoprime a b) (heq:a*b=c^2):
   ∃ a0:ℤ,a=a0^2∨a= -a0^2:=
 sq_of_gcd_eq_one (isCoprime_iff_gcd_eq_one.mp h) heq
theorem natAbs_euclideanDomain_gcd (a b:ℤ):
   Int.natAbs (EuclideanDomain.gcd a b)=Int.gcd a b:=by
 apply Nat.dvd_antisymm <;> rw [←Int.natCast_dvd_natCast]
 · rw [Int.natAbs_dvd]
   exact Int.dvd_coe_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
 · rw [Int.dvd_natAbs]
   exact EuclideanDomain.dvd_gcd (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
end Int
theorem Int.Prime.dvd_mul {m n:ℤ} {p:ℕ} (hp:Nat.Prime p) (h:(p:ℤ)∣m*n):
   p∣m.natAbs∨p∣n.natAbs:=by
 rwa [←hp.dvd_mul, ←Int.natAbs_mul, ←Int.natCast_dvd]
theorem Int.Prime.dvd_mul' {m n:ℤ} {p:ℕ} (hp:Nat.Prime p) (h:(p:ℤ)∣m*n):
   (p:ℤ)∣m∨(p:ℤ)∣n:=by
 rw [Int.natCast_dvd,Int.natCast_dvd]
 exact Int.Prime.dvd_mul hp h
theorem Int.Prime.dvd_pow {n:ℤ} {k p:ℕ} (hp:Nat.Prime p) (h:(p:ℤ)∣n^k):
   p∣n.natAbs:=by
 rw [Int.natCast_dvd,Int.natAbs_pow] at h
 exact hp.dvd_of_dvd_pow h
theorem Int.Prime.dvd_pow' {n:ℤ} {k p:ℕ} (hp:Nat.Prime p) (h:(p:ℤ)∣n^k):
   (p:ℤ)∣n:=by
 rw [Int.natCast_dvd]
 exact Int.Prime.dvd_pow hp h
theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m:ℤ} {p:ℕ} (hp:Nat.Prime p)
   (h:(p:ℤ)∣2*m^2):p=2∨p∣Int.natAbs m:=by
 rcases Int.Prime.dvd_mul hp h with hp2 | hpp
 · apply Or.intro_left
   exact le_antisymm (Nat.le_of_dvd zero_lt_two hp2) (Nat.Prime.two_le hp)
 · apply Or.intro_right
   rw [sq,Int.natAbs_mul] at hpp
   exact or_self_iff.mp ((Nat.Prime.dvd_mul hp).mp hpp)
namespace Int
theorem exists_prime_and_dvd {n:ℤ} (hn:n.natAbs≠1):∃ p,Prime p∧p∣n:=by
 obtain ⟨p,pp,pd⟩:=Nat.exists_prime_and_dvd hn
 exact ⟨p,Nat.prime_iff_prime_int.mp pp,Int.natCast_dvd.mpr pd⟩
theorem prime_iff_natAbs_prime {k:ℤ}:Prime k ↔ Nat.Prime k.natAbs:=
 (Int.associated_natAbs k).prime_iff.trans Nat.prime_iff_prime_int.symm
instance instDecidablePredPrime:DecidablePred (Prime:ℤ → Prop):=fun m↦
 decidable_of_iff (Nat.Prime m.natAbs) prime_iff_natAbs_prime.symm
instance (priority:=100):DecidablePred (Irreducible:ℤ → Prop):=fun m↦
 decidable_of_iff (Prime m) irreducible_iff_prime.symm
theorem span_natAbs (a:ℤ):Ideal.span ({(a.natAbs:ℤ)}:Set ℤ)=Ideal.span {a}:=by
 rw [Ideal.span_singleton_eq_span_singleton]
 exact (associated_natAbs _).symm
@[simp]
theorem isCoprime_two_left {m:ℤ}:IsCoprime 2 m ↔ Odd m:=by
 simp [isCoprime_iff_nat_coprime]
@[simp]
theorem isCoprime_two_right {m:ℤ}:IsCoprime m 2 ↔ Odd m:=by
 simp [isCoprime_iff_nat_coprime]
theorem eq_pow_of_mul_eq_pow_odd_left {a b c:ℤ} (hab:IsCoprime a b) {k:ℕ} (hk:Odd k)
   (h:a*b=c^k):∃ d,a=d^k:=by
 obtain ⟨d,hd⟩:=exists_associated_pow_of_mul_eq_pow' hab h
 replace hd:=hd.symm
 rw [associated_iff_natAbs,natAbs_eq_natAbs_iff, ←hk.neg_pow] at hd
 obtain rfl | rfl:=hd <;> exact ⟨_,rfl⟩
theorem eq_pow_of_mul_eq_pow_odd_right {a b c:ℤ} (hab:IsCoprime a b) {k:ℕ} (hk:Odd k)
   (h:a*b=c^k):∃ d,b=d^k:=
 eq_pow_of_mul_eq_pow_odd_left (c:=c) hab.symm hk (by rwa [mul_comm] at h)
theorem eq_pow_of_mul_eq_pow_odd {a b c:ℤ} (hab:IsCoprime a b) {k:ℕ} (hk:Odd k)
   (h:a*b=c^k):(∃ d,a=d^k)∧∃ e,b=e^k:=
 ⟨eq_pow_of_mul_eq_pow_odd_left hab hk h,eq_pow_of_mul_eq_pow_odd_right hab hk h⟩
end Int
end ProximityFlatProofPort
end PackedLegacy_IA

/-! Packed from ProximityPrize.SubmissionLower.V8. -/
section PackedLegacy_V8
section ProximityFlatProofPort
theorem ZMod.ker_intCastRingHom (n:ℕ):
   RingHom.ker (Int.castRingHom (ZMod n))=Ideal.span ({(n:ℤ)}:Set ℤ):=by
 ext
 rw [Ideal.mem_span_singleton,RingHom.mem_ker,Int.coe_castRingHom,
   ZMod.intCast_zmod_eq_zero_iff_dvd]
theorem ZMod.ringHom_eq_of_ker_eq {n:ℕ} {R:Type*} [Ring R] (f g:R →+*ZMod n)
   (h:RingHom.ker f=RingHom.ker g):f=g:=by
 have:=f.liftOfRightInverse_comp _ (ZMod.ringHom_rightInverse f) ⟨g,le_of_eq h⟩
 rw [Subtype.coe_mk] at this
 rw [←this,RingHom.ext_zmod (f.liftOfRightInverse _ _ ⟨g,_⟩) _,RingHom.id_comp]
@[simp]
theorem isReduced_zmod {n:ℕ}:IsReduced (ZMod n) ↔ Squarefree n∨n=0:=by
 rw [←RingHom.ker_isRadical_iff_reduced_of_surjective
     (ZMod.ringHom_surjective <| Int.castRingHom <| ZMod n),
     ZMod.ker_intCastRingHom, ←isRadical_iff_span_singleton,isRadical_iff_squarefree_or_zero,
     Int.squarefree_natCast,Nat.cast_eq_zero]
instance {n:ℕ} [Fact <| Squarefree n]:IsReduced (ZMod n):=
 isReduced_zmod.2 <| Or.inl <| Fact.out
end ProximityFlatProofPort
end PackedLegacy_V8

/-! Packed from ProximityPrize.SubmissionLower.HQ. -/
section PackedLegacy_HQ
section ProximityFlatProofPort
open QuotientAddGroup Set ZMod
variable (n:ℕ) {A R:Type*} [AddGroup A] [Ring R]
namespace Int
def quotientSpanNatEquivZMod:ℤ ⧸ Ideal.span {(n:ℤ)} ≃+*ZMod n:=
 (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans <|
   RingHom.quotientKerEquivOfRightInverse <|
     show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast
def quotientSpanEquivZMod (a:ℤ):ℤ ⧸ Ideal.span ({a}:Set ℤ) ≃+*ZMod a.natAbs:=
 (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
@[simp]
theorem quotientSpanNatEquivZMod_comp_Quotient_mk (n:ℕ):
   (Int.quotientSpanNatEquivZMod n:_ →+*_).comp (Ideal.Quotient.mk (Ideal.span {(n:ℤ)}))=
     Int.castRingHom (ZMod n):=rfl
@[simp]
theorem quotientSpanNatEquivZMod_comp_castRingHom (n:ℕ):
   ((Int.quotientSpanNatEquivZMod n).symm:_ →+*_).comp (Int.castRingHom (ZMod n))=
     Ideal.Quotient.mk (Ideal.span {(n:ℤ)}):=by ext;simp
@[simp]
theorem quotientSpanEquivZMod_comp_Quotient_mk (n:ℤ):
   (Int.quotientSpanEquivZMod n:_ →+*_).comp (Ideal.Quotient.mk (Ideal.span {(n:ℤ)}))=
     Int.castRingHom (ZMod n.natAbs):=rfl
@[simp]
theorem quotientSpanEquivZMod_comp_castRingHom (n:ℤ):
   ((Int.quotientSpanEquivZMod n).symm:_ →+*_).comp (Int.castRingHom (ZMod n.natAbs))=
     Ideal.Quotient.mk (Ideal.span {(n:ℤ)}):=by ext;simp
instance {n:ℤ} [NeZero n]:Finite (ℤ ⧸ Ideal.span {n}):=
 Finite.of_equiv _ n.quotientSpanEquivZMod.symm.toEquiv
end Int
noncomputable section ChineseRemainder
open Ideal
open scoped Function in
def ZMod.prodEquivPi {ι:Type*} [Fintype ι] (a:ι → ℕ)
   (coprime:Pairwise (Nat.Coprime on a)):ZMod (∏ i,a i) ≃+*Π i,ZMod (a i):=
 have:Pairwise fun i j => IsCoprime (span {(a i:ℤ)}) (span {(a j:ℤ)}):=
   fun _i _j h↦(isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R:=ℤ))
 Int.quotientSpanNatEquivZMod _ |>.symm.trans <|
 quotEquivOfEq (iInf_span_singleton_natCast (R:=ℤ) coprime) |>.symm.trans <|
 quotientInfRingEquivPiQuotient _ this |>.trans <|
 RingEquiv.piCongrRight fun i↦Int.quotientSpanNatEquivZMod (a i)
open Finset Function in
@[simp]
theorem ZMod.prodEquivPi_apply {ι:Type*} [Fintype ι] (a:ι → ℕ)
   (coprime:Pairwise (Nat.Coprime on a)) (b:ZMod (∏ i,a i)) (i:ι):
   prodEquivPi a coprime b i=castHom (dvd_prod_of_mem a (mem_univ i)) _ b:=
 RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom (fun _↦ZMod _) i).comp
   (prodEquivPi a coprime).toRingHom) _) b
def ZMod.equivPi (hn:n≠0):
   ZMod n ≃+*Π (p:n.primeFactors),ZMod (p^(n.factorization p)):=
 (ringEquivCongr <| Nat.prod_primeFactors_coe_pow_factorization hn).trans
   <| prodEquivPi (fun (p:n.primeFactors)↦(p:ℕ)^(n.factorization p))
     n.pairwise_coprime_pow_primeFactors_factorization
end ChineseRemainder
end ProximityFlatProofPort
end PackedLegacy_HQ

/-! Packed from ProximityPrize.SubmissionLower.S2. -/
section PackedLegacy_S2
section ProximityFlatProofPort
namespace Submodule
open LinearMap
variable {ι R:Type*} [CommRing R]
 {Ms:ι → Type*} [∀ i,AddCommGroup (Ms i)] [∀ i,Module R (Ms i)]
 {N:Type*} [AddCommGroup N] [Module R N]
 {Ns:ι → Type*} [∀ i,AddCommGroup (Ns i)] [∀ i,Module R (Ns i)]
def piQuotientLift [Fintype ι] [DecidableEq ι] (p:∀ i,Submodule R (Ms i)) (q:Submodule R N)
   (f:∀ i,Ms i →ₗ[R] N) (hf:∀ i,p i ≤ q.comap (f i)):(∀ i,Ms i ⧸ p i) →ₗ[R] N ⧸ q:=
 lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)
@[simp]
theorem piQuotientLift_mk [Fintype ι] [DecidableEq ι] (p:∀ i,Submodule R (Ms i))
   (q:Submodule R N) (f:∀ i,Ms i →ₗ[R] N) (hf:∀ i,p i ≤ q.comap (f i)) (x:∀ i,Ms i):
   (piQuotientLift p q f hf fun i => Quotient.mk (x i))=Quotient.mk (lsum _ _ R f x):=by
 rw [piQuotientLift,lsum_apply,LinearMap.sum_apply, ←mkQ_apply,lsum_apply,LinearMap.sum_apply,_root_.map_sum]
 simp only [coe_proj,mapQ_apply,mkQ_apply,comp_apply]
@[simp]
theorem piQuotientLift_single [Fintype ι] [DecidableEq ι] (p:∀ i,Submodule R (Ms i))
   (q:Submodule R N) (f:∀ i,Ms i →ₗ[R] N) (hf:∀ i,p i ≤ q.comap (f i)) (i)
   (x:Ms i ⧸ p i):piQuotientLift p q f hf (Pi.single i x)=mapQ _ _ (f i) (hf i) x:=by
 simp_rw [piQuotientLift,lsum_apply,LinearMap.sum_apply,comp_apply,proj_apply]
 rw [Finset.sum_eq_single i]
 · rw [Pi.single_eq_same]
 · rintro j-hj
   rw [Pi.single_eq_of_ne hj,map_zero]
 · intros
   have:=Finset.mem_univ i
   contradiction
def quotientPiLift (p:∀ i,Submodule R (Ms i)) (f:∀ i,Ms i →ₗ[R] Ns i)
   (hf:∀ i,p i ≤ ker (f i)):(∀ i,Ms i) ⧸ pi Set.univ p →ₗ[R] ∀ i,Ns i:=
 (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
   mem_ker.mpr <| by
     ext i
     simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))
@[simp]
theorem quotientPiLift_mk (p:∀ i,Submodule R (Ms i)) (f:∀ i,Ms i →ₗ[R] Ns i)
   (hf:∀ i,p i ≤ ker (f i)) (x:∀ i,Ms i):
   quotientPiLift p f hf (Quotient.mk x)=fun i => f i (x i):=
 rfl
namespace quotientPi_aux
variable (p:∀ i,Submodule R (Ms i))
@[simp]
def toFun:((∀ i,Ms i) ⧸ pi Set.univ p) → ∀ i,Ms i ⧸ p i:=
 quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge
theorem map_add (x y:((i:ι) → Ms i) ⧸ pi Set.univ p):
   toFun p (x+y)=toFun p x+toFun p y:=
 LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y
theorem map_smul (r:R) (x:((i:ι) → Ms i) ⧸ pi Set.univ p):
   toFun p (r • x)=(RingHom.id R r) • toFun p x:=
 LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x
variable [Fintype ι] [DecidableEq ι]
@[simp]
def invFun:(∀ i,Ms i ⧸ p i) → (∀ i,Ms i) ⧸ pi Set.univ p:=
 piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p
theorem left_inv:Function.LeftInverse (invFun p) (toFun p):=fun x =>
 Submodule.Quotient.induction_on _ x fun x' => by
   dsimp only [toFun,invFun]
   rw [quotientPiLift_mk p,funext fun i => (mkQ_apply (p i) (x' i)),piQuotientLift_mk p,
     lsum_single,id_apply]
theorem right_inv:Function.RightInverse (invFun p) (toFun p):=by
 dsimp only [toFun,invFun]
 rw [Function.rightInverse_iff_comp, ←coe_comp, ←@id_coe R]
 congr
 refine pi_ext fun i x↦?_
 induction x using Submodule.Quotient.induction_on with | _ x'
 refine funext fun j↦?_
 rw [comp_apply,piQuotientLift_single,mapQ_apply,
   quotientPiLift_mk,id_apply]
 by_cases hij:i=j <;> simp only [mkQ_apply,coe_single]
 · subst hij
   rw [Pi.single_eq_same,Pi.single_eq_same]
 · rw [Pi.single_eq_of_ne (Ne.symm hij),Pi.single_eq_of_ne (Ne.symm hij),Quotient.mk_zero]
end quotientPi_aux
open quotientPi_aux in
@[simps!]
def quotientPi [Fintype ι] [DecidableEq ι] (p:∀ i,Submodule R (Ms i)):
   ((∀ i,Ms i) ⧸ pi Set.univ p) ≃ₗ[R] ∀ i,Ms i ⧸ p i where
 toFun:=toFun p
 invFun:=invFun p
 map_add':=map_add p
 map_smul':=quotientPi_aux.map_smul p
 left_inv:=left_inv p
 right_inv:=right_inv p
end Submodule
end ProximityFlatProofPort
end PackedLegacy_S2

/-! Packed from ProximityPrize.SubmissionLower.CQ. -/
section PackedLegacy_CQ
section ProximityFlatProofPort
open Module
open scoped DirectSum
namespace Submodule
variable {ι R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
 [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]
noncomputable def quotientEquivPiSpan (N:Submodule R M) (b:Basis ι R M)
   (h:Module.finrank R N=Module.finrank R M):
   (M ⧸ N) ≃ₗ[R] Π i,R ⧸ Ideal.span ({smithNormalFormCoeffs b h i}:Set R):=by
 letI:DecidableEq ι:=Classical.decEq ι
 haveI:=Fintype.ofFinite ι
 let a:=smithNormalFormCoeffs b h
 let b':=smithNormalFormTopBasis b h
 let ab:=smithNormalFormBotBasis b h
 have ab_eq:=smithNormalFormBotBasis_def b h
 have mem_I_iff:∀ x,x∈N ↔ ∀ i,a i∣b'.repr x i:=by
   intro x
   simp_rw [ab.mem_submodule_iff',ab,ab_eq]
   have:∀ (c:ι → R) (i),b'.repr (∑ j:ι,c j • a j • b' j) i=a i*c i:=by
     intro c i
     simp only [←mul_smul,b'.repr_sum_self,mul_comm]
   constructor
   · rintro ⟨c,rfl⟩ i
     exact ⟨c i,this c i⟩
   · rintro ha
     choose c hc using ha
     exact ⟨c,b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
 let N':Submodule R (ι → R):=Submodule.pi Set.univ fun i => span R ({a i}:Set R)
 have:Submodule.map (b'.equivFun:M →ₗ[R] ι → R) N=N':=by
   ext x
   simp only [N',Submodule.mem_map,Submodule.mem_pi,mem_span_singleton,Set.mem_univ,
     mem_I_iff,smul_eq_mul,forall_true_left,LinearEquiv.coe_coe,
     Basis.equivFun_apply,mul_comm _ (a _),eq_comm (b:=(x _))]
   constructor
   · rintro ⟨y,hy,rfl⟩ i
     exact hy i
   · rintro hdvd
     refine ⟨∑ i,x i • b' i,fun i => ?_,?_⟩ <;> rw [b'.repr_sum_self]
     · exact hdvd i
 refine (Submodule.Quotient.equiv N N' b'.equivFun this).trans (re₂₃:=inferInstance)
   (re₃₂:=inferInstance) ?_
 classical
 exact Submodule.quotientPi (show _ → Submodule R R from fun i => span R ({a i}:Set R))
noncomputable def quotientEquivPiZMod (N:Submodule ℤ M) (b:Basis ι ℤ M)
   (h:Module.finrank ℤ N=Module.finrank ℤ M):
   M ⧸ N ≃+Π i,ZMod (smithNormalFormCoeffs b h i).natAbs:=
 let a:=smithNormalFormCoeffs b h
 let e:=N.quotientEquivPiSpan b h
 let e':(∀ i:ι,ℤ ⧸ Ideal.span ({a i}:Set ℤ)) ≃+∀ i:ι,ZMod (a i).natAbs:=
   AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
 (↑(e:(M ⧸ N) ≃ₗ[ℤ] _):M ⧸ N ≃+_).trans e'
theorem finiteQuotientOfFreeOfRankEq [Module.Free ℤ M] [Module.Finite ℤ M]
   (N:Submodule ℤ M) (h:Module.finrank ℤ N=Module.finrank ℤ M):Finite (M ⧸ N):=by
 let b:=Module.Free.chooseBasis ℤ M
 let a:=smithNormalFormCoeffs b h
 let e:=N.quotientEquivPiZMod b h
 have:∀ i,NeZero (a i).natAbs:=fun i↦
   ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
 exact Finite.of_equiv (Π i,ZMod (a i).natAbs) e.symm
theorem finiteQuotient_iff [Module.Free ℤ M] [Module.Finite ℤ M] (N:Submodule ℤ M):
   Finite (M ⧸ N) ↔ Module.finrank ℤ N=Module.finrank ℤ M:=by
 refine ⟨fun h↦le_antisymm (finrank_le N) <|
   ((LinearMap.lsmul ℤ M (Nat.card (M ⧸ N))).codRestrict N
     fun x↦?_).finrank_le_finrank_of_injective ?_,fun h↦finiteQuotientOfFreeOfRankEq N h⟩
 · simpa using! AddSubgroup.nsmul_index_mem N.toAddSubgroup x
 · refine (LinearMap.lsmul_injective ?_).codRestrict _
   exact Int.ofNat_ne_zero.mpr <| Nat.card_ne_zero.mpr
     ⟨Set.nonempty_iff_univ_nonempty.mpr Set.univ_nonempty,h⟩
variable (F:Type*) [CommRing F] [Algebra F R] [Module F M] [IsScalarTower F R M]
 (b:Basis ι R M) {N:Submodule R M}
noncomputable def quotientEquivDirectSum (h:Module.finrank R N=Module.finrank R M):
   (M ⧸ N) ≃ₗ[F] ⨁ i,R ⧸ Ideal.span ({smithNormalFormCoeffs b h i}:Set R):=by
 haveI:=Fintype.ofFinite ι
 exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
   (DirectSum.linearEquivFunOnFintype _ _ _).symm
theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b:Basis ι R M) [Nontrivial F]
   (h:Module.finrank R N=Module.finrank R M)
   [∀ i,Module.Free F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i}:Set R))]
   [∀ i,Module.Finite F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i}:Set R))]:
   Module.finrank F (M ⧸ N)=
     ∑ i,Module.finrank F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i}:Set R)):=by
 rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h,Module.finrank_directSum]
end Submodule
end ProximityFlatProofPort
end PackedLegacy_CQ

/-! Packed from ProximityPrize.SubmissionLower.HZ. -/
section PackedLegacy_HZ
section ProximityFlatProofPort
open Module Submodule
section Submodule
variable {M:Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
theorem Submodule.natAbs_det_equiv (N:Submodule ℤ M) {E:Type*} [EquivLike E M N]
   [AddEquivClass E M N] (e:E):
   Int.natAbs
     (LinearMap.det
       (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e:M →+N)))=
     Nat.card (M ⧸ N):=by
 let b:=Module.Free.chooseBasis ℤ M
 have h:Module.finrank ℤ N=Module.finrank ℤ M:=
   (AddEquiv.toIntLinearEquiv e:M ≃ₗ[ℤ] N).symm.finrank_eq
 let a:=smithNormalFormCoeffs b h
 let b':=smithNormalFormTopBasis b h
 let ab:=smithNormalFormBotBasis b h
 have ab_eq:=smithNormalFormBotBasis_def b h
 let e':M ≃ₗ[ℤ] N:=b'.equiv ab (Equiv.refl _)
 let f:M →ₗ[ℤ] M:=N.subtype.comp (e':M →ₗ[ℤ] N)
 let f_apply:∀ x,f x=b'.equiv ab (Equiv.refl _) x:=fun x↦rfl
 suffices (LinearMap.det f).natAbs=Nat.card (M ⧸ N) by
   calc
     _=(LinearMap.det (N.subtype ∘ₗ
           (AddEquiv.toIntLinearEquiv e:M ≃ₗ[ℤ] N))).natAbs:=rfl
     _=(LinearMap.det (N.subtype ∘ₗ _)).natAbs:=
           Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
     _=Nat.card (M ⧸ N):=this
 have ha:∀ i,f (b' i)=a i • b' i:=by
   intro i
   rw [f_apply,b'.equiv_apply,Equiv.refl_apply]
   exact ab_eq i
 calc
   Int.natAbs (LinearMap.det f)=Int.natAbs (LinearMap.toMatrix b' b' f).det:=by
     rw [LinearMap.det_toMatrix]
   _=Int.natAbs (Matrix.diagonal a).det:=?_
   _=Int.natAbs (∏ i,a i):=by rw [Matrix.det_diagonal]
   _=∏ i,Int.natAbs (a i):=map_prod Int.natAbsHom a Finset.univ
   _=Nat.card (M ⧸ N):=?_
 · congr 2;ext i j
   rw [LinearMap.toMatrix_apply,ha,map_smul,Basis.repr_self,Finsupp.smul_single,
     smul_eq_mul,mul_one]
   by_cases h:i=j
   · rw [h,Matrix.diagonal_apply_eq,Finsupp.single_eq_same]
   · rw [Matrix.diagonal_apply_ne _ h,Finsupp.single_eq_of_ne h]
 simp_rw [Nat.card_congr (quotientEquivPiZMod N b h).toEquiv,Nat.card_pi,Nat.card_zmod,a]
theorem Submodule.natAbs_det_basis_change {ι:Type*} [Fintype ι] [DecidableEq ι] (b:Basis ι ℤ M)
   (N:Submodule ℤ M) (bN:Basis ι ℤ N):
   (b.det ((↑) ∘ bN)).natAbs=Nat.card (M ⧸ N):=by
 let e:=b.equiv bN (Equiv.refl _)
 calc
   (b.det (N.subtype ∘ bN)).natAbs=(LinearMap.det (N.subtype ∘ₗ (e:M →ₗ[ℤ] N))).natAbs:=by
     rw [Basis.det_comp_basis]
   _=_:=natAbs_det_equiv N e
end Submodule
section AddSubgroup
theorem AddSubgroup.index_eq_natAbs_det {E:Type*} [AddCommGroup E] {ι:Type*}
   [DecidableEq ι] [Fintype ι] (bE:Basis ι ℤ E) (N:AddSubgroup E) (bN:Basis ι ℤ N):
   N.index=(bE.det (bN ·)).natAbs:=
 have:Module.Free ℤ E:=Module.Free.of_basis bE
 have:Module.Finite ℤ E:=Module.Finite.of_basis bE
 (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm
set_option backward.isDefEq.respectTransparency false in
theorem AddSubgroup.relIndex_eq_natAbs_det {E:Type*} [AddCommGroup E]
   (L₁ L₂:AddSubgroup E) (H:L₁ ≤ L₂) {ι:Type*} [DecidableEq ι] [Fintype ι]
   (b₁:Basis ι ℤ L₁.toIntSubmodule) (b₂:Basis ι ℤ L₂.toIntSubmodule):
   L₁.relIndex L₂=(b₂.det (fun i↦⟨b₁ i,(H (SetLike.coe_mem _))⟩)).natAbs:=by
 rw [relIndex,index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
 rfl
theorem AddSubgroup.relIndex_eq_abs_det {E:Type*} [AddCommGroup E] [Module ℚ E]
   (L₁ L₂:AddSubgroup E) (H:L₁ ≤ L₂) {ι:Type*} [DecidableEq ι] [Fintype ι]
   (b₁ b₂:Basis ι ℚ E) (h₁:L₁=.closure (Set.range b₁)) (h₂:L₂=.closure (Set.range b₂)):
   L₁.relIndex L₂=|b₂.det b₁|:=by
 rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
   (b₂.addSubgroupOfClosure L₂ h₂),Nat.cast_natAbs,Int.cast_abs]
 change |algebraMap ℤ ℚ _|=_
 rw [Basis.det_apply,Basis.det_apply,RingHom.map_det]
 congr;ext
 simp [Basis.toMatrix_apply]
end AddSubgroup
end ProximityFlatProofPort
end PackedLegacy_HZ

/-! Packed from ProximityPrize.SubmissionLower.U2. -/
section PackedLegacy_U2
section ProximityFlatProofPort
open Module
namespace Ideal
variable {ι R S:Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]
noncomputable def basisSpanSingleton (b:Basis ι R S) {x:S} (hx:x≠0):
   Basis ι R (span ({x}:Set S)):=
 b.map <|
   LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
       LinearEquiv.ofEq _ _
         (by
           ext
           simp [mem_span_singleton',mul_comm]) ≪≫ₗ
     (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x}:Set S))).restrictScalars R
@[simp]
theorem basisSpanSingleton_apply (b:Basis ι R S) {x:S} (hx:x≠0) (i:ι):
   (basisSpanSingleton b hx i:S)=x*b i:=by
 simp only [basisSpanSingleton,Basis.map_apply,LinearEquiv.trans_apply,
   Submodule.restrictScalarsEquiv_apply,LinearEquiv.ofInjective_apply,LinearEquiv.coe_ofEq_apply,
   LinearEquiv.restrictScalars_apply,LinearMap.mulLeft_apply]
@[simp]
theorem constr_basisSpanSingleton {N:Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
   (b:Basis ι R S) {x:S} (hx:x≠0):
   (b.constr N).toFun (((↑):_ → S) ∘ (basisSpanSingleton b hx))=Algebra.lmul R S x:=
 b.ext fun i => by simp
end Ideal
theorem Basis.mem_ideal_iff {ι R S:Type*} [CommSemiring R] [Semiring S] [Algebra R S]
   {I:Ideal S} (b:Basis ι R I) {x:S}:
   x∈I ↔ ∃ c:ι →₀ R,x=Finsupp.sum c fun i x => x • (b i:S):=
 (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff
theorem Basis.mem_ideal_iff' {ι R S:Type*} [Fintype ι] [CommSemiring R] [Semiring S] [Algebra R S]
   {I:Ideal S} (b:Basis ι R I) {x:S}:x∈I ↔ ∃ c:ι → R,x=∑ i,c i • (b i:S):=
 (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
end ProximityFlatProofPort
end PackedLegacy_U2

/-! Packed from ProximityPrize.SubmissionLower.F4. -/
section PackedLegacy_F4
section ProximityFlatProofPort
universe u v w
variable {R S T:Type*} [CommRing R] [Ring S]
 [Algebra R S]
 {K L F:Type*} [Field K] [Field L] [Field F]
 [Algebra K L] [Algebra K F]
 {ι:Type w}
open Module LinearMap Matrix Polynomial
open scoped Matrix
namespace Algebra
section EqProdRoots
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb:PowerBasis R S):
   norm R pb.gen=(-1)^pb.dim*coeff (minpoly R pb.gen) 0:=by
 rw [norm_eq_matrix_det pb.basis,Matrix.det_eq_sign_charpoly_coeff,charpoly_leftMulMatrix,
   Fintype.card_fin]
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb:PowerBasis R S)
   (hf:((minpoly R pb.gen).map (algebraMap R F)).Splits):
   algebraMap R F (norm R pb.gen)=((minpoly R pb.gen).aroots F).prod:=by
 haveI:=Module.nontrivial R F
 have:=minpoly.monic pb.isIntegral_gen
 rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, ←pb.natDegree_minpoly,map_mul,
   ←coeff_map,
   hf.coeff_zero_eq_prod_roots_of_monic (this.map _),
   this.natDegree_map,map_pow, ←mul_assoc, ←mul_pow]
 simp only [map_neg,map_one,neg_mul,neg_neg,one_pow,one_mul]
end EqProdRoots
section EqZeroIff
variable [Finite ι]
@[simp]
theorem norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S]:norm R (0:S)=0:=by
 nontriviality
 rw [norm_apply,coe_lmul_eq_mul,map_zero,LinearMap.det_zero' (Module.Free.chooseBasis R S)]
@[simp]
theorem norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x:S}:
   norm R x=0 ↔ x=0:=by
 constructor
 swap
 · rintro rfl;exact norm_zero
 · let b:=Module.Free.chooseBasis R S
   let decEq:=Classical.decEq (Module.Free.ChooseBasisIndex R S)
   rw [norm_eq_matrix_det b, ←Matrix.exists_mulVec_eq_zero_iff]
   rintro ⟨v,v_ne,hv⟩
   rw [←b.equivFun.apply_symm_apply v,b.equivFun_symm_apply,b.equivFun_apply,
     leftMulMatrix_mulVec_repr] at hv
   refine (mul_eq_zero.mp (b.ext_elem fun i => ?_)).resolve_right (show ∑ i,v i • b i≠0 from ?_)
   · simpa only [map_zero,Pi.zero_apply] using! congr_fun hv i
   · contrapose v_ne with sum_eq
     apply b.equivFun.symm.injective
     rw [b.equivFun_symm_apply,sum_eq,map_zero]
theorem norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x:S}:
   norm R x≠0 ↔ x≠0:=not_iff_not.mpr norm_eq_zero_iff
@[simp]
theorem norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x:S}:
   LinearMap.det (LinearMap.mul R S x)=0 ↔ x=0:=norm_eq_zero_iff
theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b:Basis ι R S) {x:S}:
   Algebra.norm R x=0 ↔ x=0:=by
 haveI:Module.Free R S:=Module.Free.of_basis b
 haveI:Module.Finite R S:=Module.Finite.of_basis b
 exact norm_eq_zero_iff
theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b:Basis ι R S) {x:S}:
   Algebra.norm R x≠0 ↔ x≠0:=
 not_iff_not.mpr (norm_eq_zero_iff_of_basis b)
end EqZeroIff
section DivisionRing
variable {L:Type*} [DivisionRing L] [Algebra K L] [Module.Finite K L]
theorem norm_inv (x:L):Algebra.norm K x⁻¹=(Algebra.norm K x)⁻¹:=by
 letI:DecidableEq L:=Classical.decEq L
 by_cases hx:x=0
 · simp [hx]
 exact mul_left_injective₀ (norm_ne_zero_iff.mpr hx) (by simp [hx, ←map_mul])
theorem norm_zpow (x:L) (n:ℤ):Algebra.norm K (x^n)=Algebra.norm K x^n:=
 map_zpow' _ norm_inv _ _
end DivisionRing
open IntermediateField
section IntermediateField
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one {x:L} (hx:¬IsIntegral K x):
   norm K (AdjoinSimple.gen K x)=1:=by
 rw [norm_eq_one_of_not_exists_basis]
 contrapose hx
 obtain ⟨s,⟨b⟩⟩:=hx
 refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
 · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
 · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x:L)
   (hf:((minpoly K x).map (algebraMap K F)).Splits):
   (algebraMap K F) (norm K (AdjoinSimple.gen K x))=
     ((minpoly K x).aroots F).prod:=by
 have injKxL:=(algebraMap K⟮x⟯ L).injective
 by_cases hx:IsIntegral K x;swap
 · simp [minpoly.eq_zero hx,IntermediateField.AdjoinSimple.norm_gen_eq_one hx,aroots_def]
 rw [←adjoin.powerBasis_gen hx,PowerBasis.norm_gen_eq_prod_roots] <;>
   rw [adjoin.powerBasis_gen hx, ←minpoly.algebraMap_eq injKxL] <;>
   simp only [AdjoinSimple.algebraMap_gen _ _,hf]
end IntermediateField
section EqProdEmbeddings
open IntermediateField IntermediateField.AdjoinSimple Polynomial
variable (F) (E:Type*) [Field E] [Algebra K E]
theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb:PowerBasis R S)
   (hE:((minpoly R pb.gen).map (algebraMap R F)).Splits) (hfx:IsSeparable R pb.gen):
   algebraMap R F (norm R pb.gen)=
     (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod fun σ => σ pb.gen:=by
 letI:=Classical.decEq F
 rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
 rw [@Fintype.prod_equiv (S →ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
   (fun σ => σ pb.gen) (fun x => x) ?_]
 · rw [Finset.prod_mem_multiset,Finset.prod_eq_multiset_prod,Multiset.toFinset_val,
     Multiset.dedup_eq_self.mpr,Multiset.map_id]
   · exact nodup_roots (.map hfx)
   · intro x;rfl
 · intro σ;simp only [PowerBasis.liftEquiv'_apply_coe]
theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
   [Algebra.IsSeparable K F] [FiniteDimensional K F] (pb:PowerBasis K L):
   ∏ σ:F →ₐ[K] E,σ (algebraMap L F pb.gen)=
     ((@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod
       fun σ:L →ₐ[K] E => σ pb.gen)^finrank L F:=by
 haveI:FiniteDimensional L F:=FiniteDimensional.right K L F
 haveI:Algebra.IsSeparable L F:=Algebra.isSeparable_tower_top_of_isSeparable K L F
 letI:Fintype (L →ₐ[K] E):=PowerBasis.AlgHom.fintype pb
 rw [Fintype.prod_equiv algHomEquivSigma (fun σ:F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
   ←Finset.univ_sigma_univ,Finset.prod_sigma, ←Finset.prod_pow]
 · refine Finset.prod_congr rfl fun σ _ => ?_
   letI:Algebra L E:=σ.toRingHom.toAlgebra
   simp_rw [Finset.prod_const]
   congr
   exact AlgHom.card L F E
 · intro σ
   simp only [algHomEquivSigma,Equiv.coe_fn_mk,AlgHom.restrictDomain,AlgHom.comp_apply,
     IsScalarTower.coe_toAlgHom']
lemma norm_eq_of_algEquiv [Ring T] [Algebra R T] (e:S ≃ₐ[R] T) (x):
   Algebra.norm R (e x)=Algebra.norm R x:=by
 simp_rw [Algebra.norm_apply, ←LinearMap.det_conj _ e.toLinearEquiv];congr;ext;simp
set_option backward.isDefEq.respectTransparency false in
lemma norm_eq_of_ringEquiv {A B C:Type*} [CommRing A] [CommRing B] [Ring C]
   [Algebra A C] [Algebra B C] (e:A ≃+*B) (he:(algebraMap B C).comp e=algebraMap A C)
   (x:C):
   e (Algebra.norm A x)=Algebra.norm B x:=by
 classical
 by_cases h:∃ s:Finset C,Nonempty (Basis s B C)
 · obtain ⟨s,⟨b⟩⟩:=h
   letI:Algebra A B:=RingHom.toAlgebra e
   letI:IsScalarTower A B C:=IsScalarTower.of_algebraMap_eq' he.symm
   rw [Algebra.norm_eq_matrix_det b,
     Algebra.norm_eq_matrix_det (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ←he])),
     e.map_det]
   congr
   ext i j
   simp [leftMulMatrix_apply,LinearMap.toMatrix_apply]
 rw [norm_eq_one_of_not_exists_basis _ h,norm_eq_one_of_not_exists_basis,map_one]
 intro ⟨s,⟨b⟩⟩
 exact h ⟨s,⟨b.mapCoeffs e (by simp [Algebra.smul_def, ←he])⟩⟩
lemma norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂:Type*} [CommRing A₁] [Ring B₁]
   [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁:A₁ ≃+*A₂) (e₂:B₁ ≃+*B₂)
   (he:RingHom.comp (algebraMap A₂ B₂) ↑e₁=RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x):
   Algebra.norm A₁ x=e₁.symm (Algebra.norm A₂ (e₂ x)):=by
 letI:=(RingHom.comp (e₂:B₁ →+*B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
 · let e':B₁ ≃ₐ[A₁] B₂:={ e₂ with commutes':=fun _↦rfl}
   rw [←Algebra.norm_eq_of_ringEquiv e₁ he, ←Algebra.norm_eq_of_algEquiv e']
   simp [e']
 intro c x
 apply e₂.symm.injective
 simp only [RingHom.coe_comp,RingHom.coe_coe,Function.comp_apply,map_mul,
   RingEquiv.symm_apply_apply,commutes]
end EqProdEmbeddings
end Algebra
end ProximityFlatProofPort
end PackedLegacy_F4

/-! Packed from ProximityPrize.SubmissionLower.V1. -/
section PackedLegacy_V1
section ProximityFlatProofPort
variable {α:Type*}
namespace UniqueFactorizationMonoid
variable {R:Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
section Multiplicative
variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
 {β:Type*} [CommMonoidWithZero β]
theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s:Finset α} (i:α → ℕ) (p:α)
   (hps:p∉s) (is_prime:∀ q∈insert p s,Prime q)
   (is_coprime:∀ᵉ (q∈insert p s) (q'∈insert p s),q∣q' → q=q'):
   IsRelPrime (p^i p) (∏ p'∈s,p'^i p'):=by
 have hp:=is_prime _ (Finset.mem_insert_self _ _)
 refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
 intro d hdp hdprod hd
 apply hps
 replace hdp:=hd.dvd_of_dvd_pow hdp
 obtain ⟨q,q_mem',hdq⟩:=hd.exists_mem_multiset_dvd hdprod
 obtain ⟨q,q_mem,rfl⟩:=Multiset.mem_map.mp q_mem'
 replace hdq:=hd.dvd_of_dvd_pow hdq
 have:p∣q:=dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
 convert! q_mem using 0
 rw [Finset.mem_val,
   is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]
@[elab_as_elim]
theorem induction_on_prime_power {P:α → Prop} (s:Finset α) (i:α → ℕ)
   (is_prime:∀ p∈s,Prime p) (is_coprime:∀ᵉ (p∈s) (q∈s),p∣q → p=q)
   (h1:∀ {x},IsUnit x → P x) (hpr:∀ {p} (i:ℕ),Prime p → P (p^i))
   (hcp:∀ {x y},IsRelPrime x y → P x → P y → P (x*y)):
   P (∏ p∈s,p^i p):=by
 letI:=Classical.decEq α
 induction s using Finset.induction_on with
 | empty => simpa using h1 isUnit_one
 | insert p f' hpf' ih =>
   rw [Finset.prod_insert hpf']
   exact
     hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
       (hpr (i p) (is_prime _ (Finset.mem_insert_self _ _)))
       (ih (fun q hq => is_prime _ (Finset.mem_insert_of_mem hq)) fun q hq q' hq' =>
         is_coprime _ (Finset.mem_insert_of_mem hq) _ (Finset.mem_insert_of_mem hq'))
@[elab_as_elim]
theorem induction_on_coprime {P:α → Prop} (a:α) (h0:P 0) (h1:∀ {x},IsUnit x → P x)
   (hpr:∀ {p} (i:ℕ),Prime p → P (p^i))
   (hcp:∀ {x y},IsRelPrime x y → P x → P y → P (x*y)):P a:=by
 letI:=Classical.decEq α
 have P_of_associated:∀ {x y},Associated x y → P x → P y:=by
   rintro x y ⟨u,rfl⟩ hx
   exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
 by_cases ha0:a=0
 · rwa [ha0]
 haveI:Nontrivial α:=⟨⟨_,_,ha0⟩⟩
 letI:StrongNormalizationMonoid α:=UniqueFactorizationMonoid.strongNormalizationMonoid
 refine P_of_associated (prod_normalizedFactors ha0) ?_
 rw [←(normalizedFactors a).map_id,Finset.prod_multiset_map_count]
 refine induction_on_prime_power _ _ ?_ ?_ @h1 @hpr @hcp <;> simp only [Multiset.mem_toFinset]
 · apply prime_of_normalized_factor
 · apply normalizedFactors_eq_of_dvd
theorem multiplicative_prime_power {f:α → β} (s:Finset α) (i j:α → ℕ)
   (is_prime:∀ p∈s,Prime p) (is_coprime:∀ᵉ (p∈s) (q∈s),p∣q → p=q)
   (h1:∀ {x y},IsUnit y → f (x*y)=f x*f y)
   (hpr:∀ {p} (i:ℕ),Prime p → f (p^i)=f p^i)
   (hcp:∀ {x y},IsRelPrime x y → f (x*y)=f x*f y):
   f (∏ p∈s,p^(i p+j p))=f (∏ p∈s,p^i p)*f (∏ p∈s,p^j p):=by
 letI:=Classical.decEq α
 induction s using Finset.induction_on with
 | empty => simpa using h1 isUnit_one
 | insert p s hps ih =>
   have hpr_p:=is_prime _ (Finset.mem_insert_self _ _)
   have hpr_s:∀ p∈s,Prime p:=fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
   have hcp_p:=fun i => prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime
   have hcp_s:∀ᵉ (p∈s) (q∈s),p∣q → p=q:=fun p hp q hq =>
     is_coprime p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
   rw [Finset.prod_insert hps,Finset.prod_insert hps,Finset.prod_insert hps,hcp (hcp_p _),
     hpr _ hpr_p,hcp (hcp_p _),hpr _ hpr_p,hcp (hcp_p (fun p => i p+j p)),hpr _ hpr_p,
     ih hpr_s hcp_s,pow_add,mul_assoc,mul_left_comm (f p^j p),mul_assoc]
theorem multiplicative_of_coprime (f:α → β) (a b:α) (h0:f 0=0)
   (h1:∀ {x y},IsUnit y → f (x*y)=f x*f y)
   (hpr:∀ {p} (i:ℕ),Prime p → f (p^i)=f p^i)
   (hcp:∀ {x y},IsRelPrime x y → f (x*y)=f x*f y):
   f (a*b)=f a*f b:=by
 letI:=Classical.decEq α
 by_cases ha0:a=0
 · rw [ha0,zero_mul,h0,zero_mul]
 by_cases hb0:b=0
 · rw [hb0,mul_zero,h0,mul_zero]
 by_cases hf1:f 1=0
 · calc
     f (a*b)=f (a*b*1):=by rw [mul_one]
     _=0:=by simp only [h1 isUnit_one,hf1,mul_zero]
     _=f a*f (b*1):=by simp only [h1 isUnit_one,hf1,mul_zero]
     _=f a*f b:=by rw [mul_one]
 haveI:Nontrivial α:=⟨⟨_,_,ha0⟩⟩
 letI:StrongNormalizationMonoid α:=UniqueFactorizationMonoid.strongNormalizationMonoid
 suffices
     f (∏ p∈(normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
       p^((normalizedFactors a).count p+(normalizedFactors b).count p))=
     f (∏ p∈(normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
       p^(normalizedFactors a).count p)*
     f (∏ p∈(normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
       p^(normalizedFactors b).count p) by
   obtain ⟨ua,a_eq⟩:=prod_normalizedFactors ha0
   obtain ⟨ub,b_eq⟩:=prod_normalizedFactors hb0
   rw [←a_eq, ←b_eq,mul_right_comm (Multiset.prod (normalizedFactors a)) ua
       (Multiset.prod (normalizedFactors b)*ub),h1 ua.isUnit,h1 ub.isUnit,h1 ua.isUnit, ←
     mul_assoc,h1 ub.isUnit,mul_right_comm _ (f ua), ←mul_assoc]
   congr
   rw [←(normalizedFactors a).map_id, ←(normalizedFactors b).map_id,
     Finset.prod_multiset_map_count,Finset.prod_multiset_map_count,
     Finset.prod_subset (Finset.subset_union_left (s₂:=(normalizedFactors b).toFinset)),
     Finset.prod_subset (Finset.subset_union_right (s₂:=(normalizedFactors b).toFinset)), ←
     Finset.prod_mul_distrib]
   · simp_rw [id, ←pow_add,this]
   all_goals simp only [Multiset.mem_toFinset]
   · intro p _ hpb
     simp [hpb]
   · intro p _ hpa
     simp [hpa]
 refine multiplicative_prime_power _ _ _ ?_ ?_ @h1 @hpr @hcp
 all_goals simp only [Multiset.mem_toFinset,Finset.mem_union]
 · rintro p (hpa | hpb) <;> apply prime_of_normalized_factor <;> assumption
 · rintro p (hp | hp) q (hq | hq) hdvd <;>
     rw [←normalize_normalized_factor _ hp, ←normalize_normalized_factor _ hq] <;>
     exact
       normalize_eq_normalize hdvd
         ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
           (prime_of_normalized_factor _ hq).irreducible hdvd)
end Multiplicative
end UniqueFactorizationMonoid
end ProximityFlatProofPort
end PackedLegacy_V1

/-! Packed from ProximityPrize.SubmissionLower.CX. -/
section PackedLegacy_CX
section ProximityFlatProofPort
open Module
open scoped nonZeroDivisors
section abs_norm
namespace Submodule
variable {R M:Type*} [Ring R] [AddCommGroup M] [Module R M]
section
noncomputable def cardQuot (S:Submodule R M):ℕ:=
 AddSubgroup.index S.toAddSubgroup
theorem cardQuot_apply (S:Submodule R M):cardQuot S=Nat.card (M ⧸ S):=by
 rfl
variable (R M)
@[simp]
theorem cardQuot_bot [Infinite M]:cardQuot (⊥:Submodule R M)=0:=
 AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite
@[simp]
theorem cardQuot_top:cardQuot (⊤:Submodule R M)=1:=
 AddSubgroup.index_top
variable {R M}
@[simp]
theorem cardQuot_eq_one_iff {P:Submodule R M}:cardQuot P=1 ↔ P=⊤:=
 AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])
end
end Submodule
section RingOfIntegers
variable {S:Type*} [CommRing S]
open Submodule
theorem cardQuot_mul_of_coprime
   {I J:Ideal S} (coprime:IsCoprime I J):cardQuot (I*J)=cardQuot I*cardQuot J:=by
 rw [cardQuot_apply,cardQuot_apply,cardQuot_apply,
   Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv,
   Nat.card_prod]
theorem Ideal.mul_add_mem_pow_succ_inj (P:Ideal S) {i:ℕ} (a d d' e e':S) (a_mem:a∈P^i)
   (e_mem:e∈P^(i+1)) (e'_mem:e'∈P^(i+1)) (h:d-d'∈P):
   a*d+e-(a*d'+e')∈P^(i+1):=by
 have:a*d-a*d'∈P^(i+1):=by
   simp only [←mul_sub]
   exact Ideal.mul_mem_mul a_mem h
 convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
 ring
section PPrime
variable {P:Ideal S} [P_prime:P.IsPrime]
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP:P≠⊥)
   {i:ℕ} (a c:S) (a_mem:a∈P^i)
   (a_notMem:a∉P^(i+1)) (c_mem:c∈P^i):
   ∃ d:S,∃ e∈P^(i+1),a*d+e=c:=by
 suffices eq_b:P^i=Ideal.span {a} ⊔ P^(i+1) by
   rw [eq_b] at c_mem
   simp only [mul_comm a]
   exact Ideal.mem_span_singleton_sup.mp c_mem
 refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
   (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
     (Ideal.pow_succ_lt_pow hP i).le)).symm
 contrapose a_notMem with this
 rw [this]
 exact mem_sup.mpr ⟨a,mem_span_singleton_self a,0,by simp,by simp⟩
theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P:Ideal S} [P_prime:P.IsPrime]
   (hP:P≠⊥) {i:ℕ} {a b:S} (a_notMem:a∉P^(i+1)) (ab_mem:a*b∈P^(i+1)):
   b∈P:=by
 simp only [←Ideal.span_singleton_le_iff_mem, ←Ideal.dvd_iff_le,pow_succ, ←
   Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
 exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP:P≠⊥)
   {i:ℕ} (a d d' e e':S)
   (a_notMem:a∉P^(i+1)) (e_mem:e∈P^(i+1)) (e'_mem:e'∈P^(i+1))
   (h:a*d+e-(a*d'+e')∈P^(i+1)):d-d'∈P:=by
 have h':a*(d-d')∈P^(i+1):=by
   convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
   ring
 exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'
theorem cardQuot_pow_of_prime [IsDedekindDomain S] (hP:P≠⊥) {i:ℕ}:
   cardQuot (P^i)=cardQuot P^i:=by
 induction i with
 | zero => simp
 | succ i ih => ?_
 have:P^(i+1) < P^i:=Ideal.pow_succ_lt_pow hP i
 suffices hquot:map (P^i.succ).mkQ (P^i) ≃ S ⧸ P by
   rw [pow_succ' (cardQuot P), ←ih,cardQuot_apply (P^i.succ), ←
     card_quotient_mul_card_quotient (P^i) (P^i.succ) this.le,cardQuot_apply (P^i),
     cardQuot_apply P,Nat.card_congr hquot]
 choose a a_mem a_notMem using SetLike.exists_of_lt this
 choose f g hg hf using fun c (hc:c∈P^i) =>
   Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_notMem hc
 choose k hk_mem hk_eq using fun c' (hc':c'∈map (mkQ (P^i.succ)) (P^i)) =>
   Submodule.mem_map.mp hc'
 refine Equiv.ofBijective (fun c' => Quotient.mk'' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨?_,?_⟩
 · rintro ⟨c₁',hc₁'⟩ ⟨c₂',hc₂'⟩ h
   rw [Subtype.mk_eq_mk, ←hk_eq _ hc₁', ←hk_eq _ hc₂',mkQ_apply,mkQ_apply,
     Submodule.Quotient.eq, ←hf _ (hk_mem _ hc₁'), ←hf _ (hk_mem _ hc₂')]
   refine Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) ?_
   simpa only [Submodule.Quotient.mk''_eq_mk,Submodule.Quotient.mk''_eq_mk,
     Submodule.Quotient.eq] using h
 · intro d'
   induction d' using Quotient.inductionOn with | _ d
   have hd':=(mem_map (f:=mkQ (P^i.succ))).mpr ⟨a*d,Ideal.mul_mem_right d _ a_mem,rfl⟩
   refine ⟨⟨_,hd'⟩,?_⟩
   simp only [Submodule.Quotient.mk''_eq_mk,Ideal.Quotient.mk_eq_mk,Ideal.Quotient.eq]
   refine
     Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_notMem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
   rw [hf,add_zero]
   exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')
end PPrime
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free ℤ S] (I J:Ideal S):
   cardQuot (I*J)=cardQuot I*cardQuot J:=by
 let b:=Module.Free.chooseBasis ℤ S
 haveI:Infinite S:=Infinite.of_surjective _ b.repr.toEquiv.surjective
 exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
     (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI,Ideal.mul_top])
     (fun {I} i hI =>
       have:Ideal.IsPrime I:=Ideal.isPrime_of_prime hI
       cardQuot_pow_of_prime hI.ne_zero)
     fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
       (Ideal.isUnit_iff.mp
         (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))
noncomputable def Ideal.absNorm [IsDedekindDomain S] [Module.Free ℤ S]:
   Ideal S →*₀ ℕ where
 toFun:=Submodule.cardQuot
 map_mul' I J:=by rw [cardQuot_mul]
 map_one':=by rw [Ideal.one_eq_top,cardQuot_top]
 map_zero':=by
   have:Infinite S:=Module.Free.infinite ℤ S
   rw [Ideal.zero_eq_bot,cardQuot_bot]
namespace Ideal
variable [IsDedekindDomain S] [Module.Free ℤ S]
theorem absNorm_apply (I:Ideal S):absNorm I=cardQuot I:=rfl
lemma absNorm_eq_index (I:Ideal S):absNorm I=I.toAddSubgroup.index:=rfl
@[simp]
theorem absNorm_bot:absNorm (⊥:Ideal S)=0:=by rw [←Ideal.zero_eq_bot,map_zero]
@[simp]
theorem absNorm_top:absNorm (⊤:Ideal S)=1:=by rw [←Ideal.one_eq_top,map_one]
@[simp]
theorem absNorm_eq_one_iff {I:Ideal S}:absNorm I=1 ↔ I=⊤:=by
 rw [absNorm_apply,cardQuot_eq_one_iff]
theorem absNorm_ne_zero_iff (I:Ideal S):Ideal.absNorm I≠0 ↔ Finite (S ⧸ I):=
 ⟨fun h => Nat.finite_of_card_ne_zero h,fun h =>
   (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩
theorem absNorm_dvd_absNorm_of_le {I J:Ideal S} (h:J ≤ I):Ideal.absNorm I∣Ideal.absNorm J:=
 map_dvd absNorm (dvd_iff_le.mpr h)
theorem irreducible_of_irreducible_absNorm {I:Ideal S} (hI:Irreducible (Ideal.absNorm I)):
   Irreducible I:=
 irreducible_iff.mpr
   ⟨fun h =>
     hI.not_isUnit (by simpa only [Ideal.isUnit_iff,Nat.isUnit_iff,absNorm_eq_one_iff] using h),
     by
     rintro a b rfl
     simpa only [Ideal.isUnit_iff,Nat.isUnit_iff,absNorm_eq_one_iff] using
       hI.isUnit_or_isUnit (map_mul absNorm a b)⟩
theorem isPrime_of_irreducible_absNorm {I:Ideal S} (hI:Irreducible (Ideal.absNorm I)):
   I.IsPrime:=
 isPrime_of_prime
   (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))
theorem prime_of_irreducible_absNorm_span {a:S} (ha:a≠0)
   (hI:Irreducible (Ideal.absNorm (Ideal.span ({a}:Set S)))):Prime a:=
 (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)
theorem absNorm_mem (I:Ideal S):↑(Ideal.absNorm I)∈I:=by
 rw [absNorm_apply,cardQuot, ←Ideal.Quotient.eq_zero_iff_mem,map_natCast,
   Quotient.index_eq_zero]
theorem span_singleton_absNorm_le (I:Ideal S):Ideal.span {(Ideal.absNorm I:S)} ≤ I:=by
 simp only [Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe,Ideal.absNorm_mem I]
theorem span_singleton_absNorm {I:Ideal S} (hI:(Ideal.absNorm I).Prime):
   Ideal.span (singleton (Ideal.absNorm I:ℤ))=I.comap (algebraMap ℤ S):=by
 have:Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I:ℤ))):=by
   rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ←Nat.prime_iff_prime_int]
 apply (this.isMaximal _).eq_of_le
 · exact ((isPrime_of_irreducible_absNorm
     ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap ℤ S)).ne_top
 · rw [span_singleton_le_iff_mem,mem_comap,algebraMap_int_eq,map_natCast]
   exact absNorm_mem I
 · rw [Ne,span_singleton_eq_bot]
   exact Int.ofNat_ne_zero.mpr hI.ne_zero
variable [Module.Finite ℤ S]
theorem natAbs_det_equiv (I:Ideal S) {E:Type*} [EquivLike E S I] [AddEquivClass E S I] (e:E):
   Int.natAbs
       (LinearMap.det
         ((Submodule.subtype I).restrictScalars ℤ ∘ₗ AddMonoidHom.toIntLinearMap (e:S →+I)))=
     Ideal.absNorm I:=by
 by_cases hI:I=⊥
 · subst hI
   have:(1:S)≠0:=one_ne_zero
   have:(1:S)=0:=EquivLike.injective e (Subsingleton.elim _ _)
   contradiction
 exact Submodule.natAbs_det_equiv (I.restrictScalars ℤ) e
theorem natAbs_det_basis_change {ι:Type*} [Fintype ι] [DecidableEq ι] (b:Basis ι ℤ S)
   (I:Ideal S) (bI:Basis ι ℤ I):(b.det ((↑) ∘ bI)).natAbs=Ideal.absNorm I:=
 Submodule.natAbs_det_basis_change b (I.restrictScalars ℤ) bI
@[simp]
theorem absNorm_span_singleton (r:S):
   absNorm (span ({r}:Set S))=(Algebra.norm ℤ r).natAbs:=by
 letI:DecidableEq S:=Classical.decEq S
 rw [Algebra.norm_apply]
 by_cases hr:r=0
 · simp only [hr,Ideal.span_zero,Ideal.absNorm_bot,
     LinearMap.det_zero'',Set.singleton_zero,map_zero,Int.natAbs_zero]
 let b:=Module.Free.chooseBasis ℤ S
 rw [←natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
 congr
 refine b.ext fun i => ?_
 simp
lemma absNorm_span_natCast (n:ℕ):(span {(n:S)}).absNorm=n^Module.finrank ℤ S:=by
 simp [absNorm_span_singleton,Algebra.norm_natCast]
theorem absNorm_dvd_norm_of_mem {I:Ideal S} {x:S} (h:x∈I):
   ↑(Ideal.absNorm I)∣Algebra.norm ℤ x:=by
 rw [←Int.dvd_natAbs, ←absNorm_span_singleton x,Int.natCast_dvd_natCast]
 exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)
@[simp]
theorem absNorm_span_insert (r:S) (s:Set S):
   absNorm (span (insert r s))∣gcd (absNorm (span s)) (Algebra.norm ℤ r).natAbs:=
 (dvd_gcd_iff _ _ _).mpr
   ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
     _root_.trans
       (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
       (by rw [absNorm_span_singleton])⟩
theorem absNorm_eq_zero_iff {I:Ideal S}:Ideal.absNorm I=0 ↔ I=⊥:=by
 constructor
 · intro hI
   rw [←le_bot_iff]
   intro x hx
   rw [mem_bot, ←Algebra.norm_eq_zero_iff (R:=ℤ), ←Int.natAbs_eq_zero,
     ←Ideal.absNorm_span_singleton, ←zero_dvd_iff, ←hI]
   apply Ideal.absNorm_dvd_absNorm_of_le
   rwa [Ideal.span_singleton_le_iff_mem]
 · rintro rfl
   exact absNorm_bot
theorem absNorm_ne_zero_iff_mem_nonZeroDivisors {I:Ideal S}:
   absNorm I≠0 ↔ I∈(Ideal S)⁰:=by
 simp_rw [ne_eq,Ideal.absNorm_eq_zero_iff,mem_nonZeroDivisors_iff_ne_zero,Submodule.zero_eq_bot]
theorem absNorm_pos_iff_mem_nonZeroDivisors {I:Ideal S}:
   0 < absNorm I ↔ I∈(Ideal S)⁰:=by
 rw [←absNorm_ne_zero_iff_mem_nonZeroDivisors,Nat.pos_iff_ne_zero]
theorem absNorm_ne_zero_of_nonZeroDivisors (I:(Ideal S)⁰):absNorm (I:Ideal S)≠0:=
 absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
theorem absNorm_pos_of_nonZeroDivisors (I:(Ideal S)⁰):0 < absNorm (I:Ideal S):=
 absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
lemma finiteIndex {I:Ideal S} (hI:I≠⊥):I.toAddSubgroup.FiniteIndex:=by
 rwa [AddSubgroup.finiteIndex_iff, ←absNorm_eq_index,Ne,absNorm_eq_zero_iff]
open AddSubgroup in
lemma isFiniteRelIndex {I:Ideal S} (hI:I≠⊥) (J:Ideal S):
   I.toAddSubgroup.IsFiniteRelIndex J.toAddSubgroup:=by
 have:=finiteIndex hI
 exact isFiniteRelIndex_of_finiteIndex
lemma exists_prime_and_absNorm_eq_pow (P:Ideal S) [P.IsMaximal]:
   ∃ p n,0 < n∧↑p∈P∧p.Prime∧P.absNorm=p^n:=by
 have:IsAddTorsionFree S:=.of_isTorsionFree ℤ _
 have:=CharZero.of_isAddTorsionFree S S
 have:Finite (S ⧸ P):=Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars ℤ)
   (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
     (Ideal.IsMaximal.ne_bot_of_isIntegral_int P))
 cases nonempty_fintype (S ⧸ P)
 letI:=Ideal.Quotient.field P
 obtain ⟨p,hpR⟩:=CharP.exists (S ⧸ P)
 obtain ⟨n,hp,e⟩:=FiniteField.card (S ⧸ P) p
 have hP:P.absNorm=p^(n:ℕ):=(Nat.card_eq_fintype_card.trans e:)
 refine ⟨p,n,n.2,?_,hp,hP⟩
 rw [←Ideal.IsPrime.pow_mem_iff_mem (I:=P) inferInstance _ n.pos, ←Nat.cast_pow, ←hP]
 exact P.absNorm_mem
lemma exists_isMaximal_dvd_of_dvd_absNorm
   {p:ℤ} (hp:Prime p) (I:Ideal S) (hI:p∣I.absNorm):
   ∃ P:Ideal S,P.IsMaximal∧P.under ℤ=.span {p}∧P∣I:=by
 have:IsAddTorsionFree S:=.of_isTorsionFree ℤ _
 have:=CharZero.of_isAddTorsionFree S S
 have hpMax:(Ideal.span {p}).IsMaximal:=
   ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
 induction I using UniqueFactorizationMonoid.induction_on_prime with
 | h₁ =>
   obtain ⟨Q,hQ,e⟩:=Ideal.exists_ideal_over_maximal_of_isIntegral (S:=S) (Ideal.span {p})
     (fun x↦by simp+contextual)
   exact ⟨Q,hQ,e,dvd_zero _⟩
 | h₂ I hI' =>
   obtain rfl:I=⊤:=by simpa using hI'
   cases hp.not_dvd_one (by simpa using hI)
 | h₃ I P hI' hP IH =>
   simp only [_root_.map_mul,Nat.cast_mul,hp.dvd_mul] at hI
   cases hI with
   | inr h =>
     obtain ⟨Q,h₁,h₂,h₃⟩:=IH h
     exact ⟨Q,h₁,h₂,dvd_mul_of_dvd_right h₃ _⟩
   | inl hI =>
     have:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
     refine ⟨P,this,(hpMax.eq_of_le (by simpa using this.ne_top) ?_).symm,dvd_mul_right _ _⟩
     obtain ⟨q,n,hn,hqP,hq,H⟩:=Ideal.exists_prime_and_absNorm_eq_pow P
     rw [H,Nat.cast_pow,dvd_prime_pow (Nat.prime_iff_prime_int.mp hq)] at hI
     obtain ⟨m,hmn,hp⟩:=hI
     rw [Ideal.span_singleton_le_iff_mem]
     have:m≠0:=fun h↦hpMax.ne_top (Ideal.span_singleton_eq_top.mpr (by simpa [h] using hp))
     exact Ideal.mem_of_dvd _ hp.symm.dvd (Ideal.pow_mem_of_mem _ (by simpa) _ this.bot_lt)
lemma exists_isMaximal_dvd_of_dvd_absNorm'
   {p:ℕ} (hp:p.Prime) (I:Ideal S) (hI:p∣I.absNorm):
   ∃ P:Ideal S,P.IsMaximal∧P.under ℤ=.span {(p:ℤ)}∧P∣I:=
 exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
   (by exact_mod_cast hI)
theorem finite_setOf_absNorm_eq [CharZero S] (n:ℕ):
   {I:Ideal S | Ideal.absNorm I=n}.Finite:=by
 obtain hn | hn:=Nat.eq_zero_or_pos n
 · simp only [hn,absNorm_eq_zero_iff,Set.setOf_eq_eq_singleton,Set.finite_singleton]
 · let f:=fun I:Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
   refine Set.Finite.of_finite_image (f:=f) ?_ ?_
   · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
       let g:=((↑):Ideal (S ⧸ @Ideal.span S _ {↑n}) → Set (S ⧸ @Ideal.span S _ {↑n}))
       refine Set.Finite.of_finite_image (f:=g) ?_ SetLike.coe_injective.injOn
       exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
     rw [←absNorm_ne_zero_iff,absNorm_span_singleton]
     simpa only [Ne,Int.natAbs_eq_zero,Algebra.norm_eq_zero_iff,Nat.cast_eq_zero] using
       ne_of_gt hn
   · intro I hI J hJ h
     rw [←comap_map_mk (span_singleton_absNorm_le I), ←hI.symm, ←
       comap_map_mk (span_singleton_absNorm_le J), ←hJ.symm]
     congr
theorem finite_setOf_absNorm_le [CharZero S] (n:ℕ):
   {I:Ideal S | Ideal.absNorm I ≤ n}.Finite:=by
 rw [show {I:Ideal S | Ideal.absNorm I ≤ n}=
   (⋃ i∈Set.Icc 0 n,{I:Ideal S | Ideal.absNorm I=i}) by ext;simp]
 refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOf_absNorm_eq i)
theorem finite_setOf_absNorm_le₀ [CharZero S] (n:ℕ):
   {I:(Ideal S)⁰ | Ideal.absNorm (I:Ideal S) ≤ n}.Finite:=by
 have:Finite {I:Ideal S//I∈(Ideal S)⁰∧absNorm I ≤ n}:=
   (finite_setOf_absNorm_le n).subset fun _ ⟨_,h⟩↦h
 exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I↦absNorm I ≤ n)).symm
theorem card_norm_le_eq_card_norm_le_add_one (n:ℕ) [CharZero S]:
   Nat.card {I:Ideal S//absNorm I ≤ n}=
     Nat.card {I:(Ideal S)⁰//absNorm (I:Ideal S) ≤ n}+1:=by
 classical
 have:Finite {I:Ideal S//I∈(Ideal S)⁰∧absNorm I ≤ n}:=
   (finite_setOf_absNorm_le n).subset fun _ ⟨_,h⟩↦h
 have:Finite {I:Ideal S//I∉(Ideal S)⁰∧absNorm I ≤ n}:=
   (finite_setOf_absNorm_le n).subset fun _ ⟨_,h⟩↦h
 rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I↦I∈(Ideal S)⁰)
   (fun I↦absNorm I ≤ n))]
 let e:{I:Ideal S//absNorm I ≤ n} ≃ {I:Ideal S//I∈(Ideal S)⁰∧absNorm I ≤ n} ⊕
     {I:Ideal S//I∉(Ideal S)⁰∧absNorm I ≤ n}:=by
   refine (Equiv.subtypeEquivRight ?_).trans (subtypeOrEquiv _ _ ?_)
   · intro _
     simp_rw [←or_and_right,em,true_and]
   · exact Pi.disjoint_iff.mpr fun I↦Prop.disjoint_iff.mpr (by tauto)
 simp_rw [Nat.card_congr e,Nat.card_sum,add_right_inj]
 conv_lhs =>
   enter [1,1,I]
   rw [←absNorm_ne_zero_iff_mem_nonZeroDivisors,ne_eq,not_not,and_iff_left_iff_imp.mpr
     (fun h↦by rw [h];exact Nat.zero_le n),absNorm_eq_zero_iff]
 rw [Nat.card_unique]
theorem norm_dvd_iff {x:S} (hx:Prime (Algebra.norm ℤ x)) {y:ℤ}:
   Algebra.norm ℤ x∣y ↔ x∣y:=by
 rw [←Ideal.mem_span_singleton (y:=x), ←eq_intCast (algebraMap ℤ S), ←Ideal.mem_comap,
   ←Ideal.span_singleton_absNorm,Ideal.mem_span_singleton,Ideal.absNorm_span_singleton,
   Int.natAbs_dvd]
 rwa [Ideal.absNorm_span_singleton, ←Int.prime_iff_natAbs_prime]
end Ideal
end RingOfIntegers
section Int
open Ideal
@[simp]
theorem Int.ideal_span_absNorm_eq_self (J:Ideal ℤ):
   span {(absNorm J:ℤ)}=J:=by
 obtain ⟨g,rfl⟩:=IsPrincipalIdealRing.principal J
 simp
@[simp]
theorem Int.prime_absNorm (J:Ideal ℤ):
   (absNorm J).Prime ↔ Prime J:=by
 obtain ⟨g,rfl⟩:=IsPrincipalIdealRing.principal J
 simp [prime_span_singleton_iff,prime_iff_natAbs_prime]
end Int
end abs_norm
end ProximityFlatProofPort
end PackedLegacy_CX

/-! Packed from ProximityPrize.SubmissionLower.CS. -/
section PackedLegacy_CS
section ProximityFlatProofPort
namespace Ideal
universe u v
variable {R:Type u} [CommRing R]
 {S:Type v} [CommRing S] [Algebra R S]
 (p:Ideal R) (P:Ideal S)
local notation "f" => algebraMap R S
open Module UniqueFactorizationMonoid
attribute [local instance] Ideal.Quotient.field
section DecEq
variable {S₁:Type*} [CommRing S₁] [Algebra R S₁]
noncomputable def inertiaDeg':ℕ:=
 if hPp:comap f P=p then
   letI:Algebra (R ⧸ p) (S ⧸ P):=Quotient.algebraQuotientOfLEComap hPp.ge
   finrank (R ⧸ p) (S ⧸ P)
 else 0
@[simp]
theorem inertiaDeg'_of_subsingleton [hp:p.IsMaximal] [hQ:Subsingleton (S ⧸ P)]:
   inertiaDeg' p P=0:=by
 have:=Ideal.Quotient.subsingleton_iff.mp hQ
 subst this
 exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top
@[deprecated (since:="2026-07-03")] alias inertiaDeg_of_subsingleton:=
 inertiaDeg'_of_subsingleton
@[simp]
theorem inertiaDeg'_algebraMap [P.LiesOver p]:
   inertiaDeg' p P=finrank (R ⧸ p) (S ⧸ P):=by
 rw [inertiaDeg',dif_pos (over_def P p).symm]
@[deprecated (since:="2026-07-03")] alias inertiaDeg_algebraMap:=inertiaDeg'_algebraMap
theorem inertiaDeg'_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p]:0 < inertiaDeg' p P:=
 have:Nontrivial (S ⧸ P):=Quotient.nontrivial_of_liesOver_of_isPrime P p
 finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm
theorem inertiaDeg'_pos' [P.IsPrime] [Module.Finite R S] [P.LiesOver p]:0 < inertiaDeg' p P:=
 have:p.IsPrime:=Ideal.over_def P p ▸ inferInstance
 Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm
@[deprecated (since:="2026-07-03")] alias inertiaDeg_pos':=inertiaDeg'_pos'
theorem inertiaDeg'_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p]:
   inertiaDeg' p P≠0:=
 (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm
@[deprecated (since:="2026-07-03")] alias inertiaDeg_ne_zero:=inertiaDeg'_ne_zero
lemma inertiaDeg'_comap_eq (e:S ≃ₐ[R] S₁) (P:Ideal S₁):
   inertiaDeg' p (P.comap e)=inertiaDeg' p P:=by
 have he:(P.comap e).comap (algebraMap R S)=p ↔ P.comap (algebraMap R S₁)=p:=by
   rw [←comap_coe e,comap_comap, ←e.toAlgHom_toRingHom,AlgHom.comp_algebraMap]
 by_cases h:P.LiesOver p
 · rw [inertiaDeg'_algebraMap,inertiaDeg'_algebraMap]
   exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
 · rw [inertiaDeg',dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
   rw [inertiaDeg',dif_neg (fun eq => h ⟨eq.symm⟩)]
@[deprecated (since:="2026-07-03")] alias inertiaDeg_comap_eq:=inertiaDeg'_comap_eq
lemma inertiaDeg'_map_eq (P:Ideal S)
   {E:Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e:E):
   inertiaDeg' p (P.map e)=inertiaDeg' p P:=by
 rw [show P.map e=_ from map_comap_of_equiv (RingEquivClass.toRingEquiv e:S ≃+*S₁)]
 exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P
@[deprecated (since:="2026-07-03")] alias inertiaDeg_map_eq:=inertiaDeg'_map_eq
theorem inertiaDeg'_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
   [hP:P.LiesOver (⊥:Ideal R)]:
   (⊥:Ideal R).inertiaDeg' P=finrank R S:=by
 rw [inertiaDeg',dif_pos (over_def P (⊥:Ideal R)).symm]
 replace hP:P=⊥:=eq_bot_of_liesOver_bot R P
 rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
   ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
 rfl
@[deprecated (since:="2026-07-03")] alias inertiaDeg_bot:=inertiaDeg'_bot
theorem inertiaDeg'_le_inertiaDeg' {T:Type*} [CommRing T] [Algebra R T] [Algebra S T]
   [IsScalarTower R S T] [Module.Finite R T] (Q:Ideal T) [P.LiesOver p] [Q.LiesOver P]
   [p.IsPrime]:inertiaDeg' P Q ≤ inertiaDeg' p Q:=by
 have:Q.LiesOver p:=LiesOver.trans Q P p
 rw [inertiaDeg'_algebraMap,inertiaDeg'_algebraMap]
 have:IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q):=IsScalarTower.of_algebraMap_eq <| by
   rintro ⟨x⟩
   simp [Submodule.Quotient.quot_mk_eq_mk,IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
 exact finrank_top_le_finrank_of_isScalarTower ..
@[deprecated (since:="2026-07-03")] alias inertiaDeg_le_inertiaDeg:=inertiaDeg'_le_inertiaDeg'
end DecEq
section absNorm
lemma absNorm_eq_pow_inertiaDeg'_of_liesOver {S:Type*} [CommRing S] [IsDedekindDomain S]
   [Module.Free ℤ S] [IsDedekindDomain R] [Module.Free ℤ R] [Algebra S R] [Module.Finite S R]
   (P:Ideal R) (p:Ideal S) [P.LiesOver p] (hp:p.IsPrime) (hp_ne_bot:p≠⊥):
   absNorm P=absNorm p^(p.inertiaDeg' P):=by
 have:p.IsMaximal:=hp.isMaximal hp_ne_bot
 let _:Field (S ⧸ p):=Quotient.field p
 simpa [absNorm_apply,Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K:=S ⧸ p)
@[deprecated (since:="2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver:=
 absNorm_eq_pow_inertiaDeg'_of_liesOver
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p:ℤ}
   (P:Ideal R) [P.LiesOver (span {p})] (hp:Prime p):
   absNorm P=p.natAbs^((span {p}).inertiaDeg' P):=by
 simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
   (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p:ℕ}
   (P:Ideal R) [P.LiesOver (span {(p:ℤ)})] (hp:p.Prime):
   absNorm P=p^((span {(p:ℤ)}).inertiaDeg' P):=
 absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
end absNorm
section tower
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
theorem inertiaDeg'_algebra_tower (p:Ideal R) (P:Ideal S) (I:Ideal T) [p.IsMaximal]
   [P.IsMaximal] [P.LiesOver p] [I.LiesOver P]:inertiaDeg' p I=
   inertiaDeg' p P*inertiaDeg' P I:=by
 have h₁:=P.over_def p
 have h₂:=I.over_def P
 have h₃:=(LiesOver.trans I P p).over
 simp only [inertiaDeg',dif_pos h₁.symm,dif_pos h₂.symm,dif_pos h₃.symm]
 letI:Algebra (R ⧸ p) (S ⧸ P):=Ideal.Quotient.algebraQuotientOfLEComap h₁.le
 letI:Algebra (S ⧸ P) (T ⧸ I):=Ideal.Quotient.algebraQuotientOfLEComap h₂.le
 letI:Algebra (R ⧸ p) (T ⧸ I):=Ideal.Quotient.algebraQuotientOfLEComap h₃.le
 letI:IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I):=IsScalarTower.of_algebraMap_eq <| by
   rintro ⟨x⟩;exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
 exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm
@[deprecated (since:="2026-07-03")] alias inertiaDeg_algebra_tower:=inertiaDeg'_algebra_tower
end tower
end Ideal
end ProximityFlatProofPort
end PackedLegacy_CS

/-! Packed from ProximityPrize.SubmissionLower.CV. -/
section PackedLegacy_CV
/- Definitions supplied by the imported Mathlib boundary. -/
end PackedLegacy_CV

/-! Packed from ProximityPrize.SubmissionLower.T7. -/
section PackedLegacy_T7
section ProximityFlatProofPort
open TensorProduct
lemma Module.finite_of_surjective_of_ker_le_nilradical
   {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
   [Algebra R S] [Algebra R T]
   [Module.Finite R T] (f:S →ₐ[R] T)
   (hf₁:Function.Surjective f) (hf₂:RingHom.ker f ≤ nilradical S)
   (hf₃:(RingHom.ker f).FG):
   Module.Finite R S:=by
 have:Module.Finite R (S ⧸ RingHom.ker f):=
   let e:=Ideal.quotientKerAlgEquivOfSurjective hf₁
   .of_surjective e.symm.toLinearMap e.symm.surjective
 generalize hI:RingHom.ker f=I at*
 suffices ∀ i,Module.Finite R (S ⧸ I^i) by
   obtain ⟨n,hn:_=⊥⟩:=hf₃.isNilpotent_iff_le_nilradical.mpr hf₂
   let e:(S ⧸ I^n) ≃ₐ[R] S:=hn ▸ (AlgEquiv.quotientBot R S)
   exact .of_surjective e.toLinearMap e.surjective
 intro n
 induction n with
 | zero => rw [pow_zero,Ideal.one_eq_top];infer_instance
 | succ n IH =>
   let φ:(S ⧸ I^(n+1)) →ₐ[S] S ⧸ I^n:=
     Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right n.le_succ)
   have hφ:Function.Surjective φ:=
     Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
   have hφ':φ.toLinearMap ∘ₗ (I^(n+1)).mkQ=(I^n).mkQ:=rfl
   refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (φ.toLinearMap.restrictScalars R) ?_ ?_⟩
   · simpa [LinearMap.range_eq_top_of_surjective (φ.toLinearMap.restrictScalars R) hφ] using
       Module.Finite.fg_top
   · have:Module.Finite R ((S ⧸ I) ⊗[S] ↑(I^n)):=by
       have:Module.Finite S ↑(I^n):=.of_fg (.pow hf₃ _)
       exact .trans (S ⧸ I) _
     let ψ:(S ⧸ I) ⊗[S] ↑(I^n) →ₗ[S] (S ⧸ I^(n+1)):=by
       refine ?_ ∘ₗ (TensorProduct.quotTensorEquivQuotSMul _ I).toLinearMap
       refine Submodule.liftQ _ ((Submodule.mkQ _).comp (I^n).subtype) ?_
       rw [LinearMap.ker_comp, ←Submodule.map_le_map_iff_of_injective (I^n).subtype_injective,
         Submodule.map_smul'',Submodule.map_comap_eq]
       simpa [pow_succ'] using Ideal.mul_le_left (I:=I) (J:=I^n)
     convert! Module.Finite.fg_top.map (ψ.restrictScalars R) using 1
     suffices LinearMap.ker φ.toLinearMap=Submodule.map (I^(n+1)).mkQ (I^n) by
       simpa [LinearMap.range_restrictScalars,ψ,LinearMap.range_comp,Submodule.range_liftQ]
     apply Submodule.comap_injective_of_surjective (I^(n+1)).mkQ_surjective
     simpa [←LinearMap.ker_comp,hφ'] using Ideal.pow_le_pow_right n.le_succ
end ProximityFlatProofPort
end PackedLegacy_T7

/-! Packed from ProximityPrize.SubmissionLower.IF. -/
section PackedLegacy_IF
section ProximityFlatProofPort
variable (R A:Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A]:
   Module.Finite R A:=
 have (I:MaximalSpectrum A):=finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
 .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A]:
   Module.Finite R A:=
 have:=finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
 IsSemiprimaryRing.finite_of_isArtinian R A A
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R]:
   Module.Finite R A ↔ IsArtinianRing A:=
 ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
   fun _↦finite_of_isArtinianRing R A⟩
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R]:
   Module.Finite R A ↔ Ring.KrullDimLE 0 A:=by
 have:IsNoetherianRing A:=Algebra.FiniteType.isNoetherianRing R A
 rw [finite_iff_isArtinianRing,isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
   and_iff_right this]
end ProximityFlatProofPort
end PackedLegacy_IF

/-! Packed from ProximityPrize.SubmissionLower.IZ. -/
section PackedLegacy_IZ
section ProximityFlatProofPort
variable (R S T:Type*) [CommRing R] [CommRing S] [Algebra R S]
 [CommRing T] [Algebra R T]
open TensorProduct Topology
noncomputable
def PrimeSpectrum.tensorProductTo (x:PrimeSpectrum (S ⊗[R] T)):
   PrimeSpectrum S × PrimeSpectrum T:=
 ⟨comap (algebraMap _ _) x,comap Algebra.TensorProduct.includeRight.toRingHom x⟩
@[fun_prop]
lemma PrimeSpectrum.continuous_tensorProductTo:Continuous (tensorProductTo R S T):=
 (continuous_comap _).prodMk (continuous_comap _)
variable (hRT:(algebraMap R T).SurjectiveOnStalks)
include hRT
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
   (p₁ p₂:PrimeSpectrum (S ⊗[R] T))
   (h:tensorProductTo R S T p₁=tensorProductTo R S T p₂):
   p₁ ≤ p₂:=by
 let g:T →+*S ⊗[R] T:=Algebra.TensorProduct.includeRight.toRingHom
 intro x hxp₁
 by_contra hxp₂
 obtain ⟨t,r,a,ht,e⟩:=hRT.exists_mul_eq_tmul x
   (p₂.asIdeal.comap g) inferInstance
 have h₁:a ⊗ₜ[R] t∈p₁.asIdeal:=e ▸ p₁.asIdeal.mul_mem_left (1 ⊗ₜ[R] (r • t)) hxp₁
 have h₂:a ⊗ₜ[R] t∉p₂.asIdeal:=e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
 rw [←mul_one a, ←one_mul t, ←Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
 have h₃:t∉p₂.asIdeal.comap g:=fun h↦h₂ (Ideal.mul_mem_left _ _ h)
 have h₄:a∉p₂.asIdeal.comap (algebraMap S (S ⊗[R] T)):=
   fun h↦h₂ (Ideal.mul_mem_right _ _ h)
 replace h₃:t∉p₁.asIdeal.comap g:=by
   rwa [show p₁.asIdeal.comap g=p₂.asIdeal.comap g from congr($h.2.1)]
 replace h₄:a∉p₁.asIdeal.comap (algebraMap S (S ⊗[R] T)):=by
   rwa [show p₁.asIdeal.comap (algebraMap S (S ⊗[R] T))=p₂.asIdeal.comap _ from congr($h.1.1)]
 exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks:
   IsEmbedding (tensorProductTo R S T):=by
 refine ⟨?_,fun p₁ p₂ e↦
   (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
     (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
 let g:T →+*S ⊗[R] T:=Algebra.TensorProduct.includeRight.toRingHom
 refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
 rintro _ ⟨f,rfl⟩
 rw [@isOpen_iff_forall_mem_open]
 rintro J (hJ:f∉J.asIdeal)
 obtain ⟨t,r,a,ht,e⟩:=hRT.exists_mul_eq_tmul f
   (J.asIdeal.comap g) inferInstance
 refine ⟨_,?_,⟨_,(basicOpen a).2.prod (basicOpen t).2,rfl⟩,?_⟩
 · rintro x ⟨hx₁:a ⊗ₜ[R] (1:T)∉x.asIdeal,hx₂:(1:S) ⊗ₜ[R] t∉x.asIdeal⟩
     (hx₃:f∈x.asIdeal)
   apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
   rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul, ←e]
   exact x.asIdeal.mul_mem_left _ hx₃
 · have:a ⊗ₜ[R] (1:T)*(1:S) ⊗ₜ[R] t∉J.asIdeal:=by
     rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul, ←e]
     exact J.asIdeal.primeCompl.mul_mem ht hJ
   rwa [J.isPrime.mul_mem_iff_mem_or_mem.not,not_or] at this
end ProximityFlatProofPort
end PackedLegacy_IZ

/-! Packed from ProximityPrize.SubmissionLower.AT. -/
section PackedLegacy_AT
section ProximityFlatProofPort
open Algebra TensorProduct nonZeroDivisors
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] (p:Ideal R) [p.IsPrime]
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
instance [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]:
   IsLocalRing (ResidueField R ⊗[R] S):=
 let eSp:ResidueField R ⊗[R] S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S):=
   (Algebra.TensorProduct.comm _ _ _).trans
     ((TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
 have:Nontrivial (IsLocalRing.ResidueField R ⊗[R] S):=by
   rw [eSp.nontrivial_congr,Ideal.Quotient.nontrivial_iff]
   exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
     (inferInstance:(maximalIdeal S).IsMaximal).lt_top).ne
 .of_surjective' TensorProduct.includeRight.toRingHom
   (TensorProduct.mk_surjective _ _ _ residue_surjective)
namespace Ideal
lemma ResidueField.exists_smul_eq_tmul_one
   (x:S ⊗[R] p.ResidueField):∃ r∉p,∃ s,r • x=s ⊗ₜ[R] 1:=by
 obtain ⟨t,r,a,hrt,e⟩:=RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
   p.surjectiveOnStalks_residueField x ⊥ isPrime_bot
 obtain ⟨t,rfl⟩:=IsLocalRing.residue_surjective t
 obtain ⟨⟨y,t⟩,rfl⟩:=IsLocalization.mk'_surjective p.primeCompl t
 simp only [smul_def,Submodule.mem_bot,mul_eq_zero,algebraMap_residueField_eq_zero,
   IsLocalRing.residue_eq_zero_iff,not_or,IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
 refine ⟨r*y,p.primeCompl.mul_mem hrt.1 hrt.2,y • a,?_⟩
 rw [Algebra.smul_def, ←Algebra.TensorProduct.includeRight.commutes,smul_tmul,
   ←Algebra.algebraMap_eq_smul_one,Algebra.TensorProduct.includeRight_apply]
 simpa [←tmul_smul,Submonoid.smul_def, ←smul_mul_assoc,smul_comm _ r,
   ←IsLocalRing.ResidueField.algebraMap_eq, ←algebraMap.coe_smul,
   ←IsScalarTower.algebraMap_apply] using congr(t • $e)
abbrev Fiber (p:Ideal R) [p.IsPrime] (S:Type*) [AddCommGroup S] [Module R S]:Type _:=
 p.ResidueField ⊗[R] S
instance (q:Ideal (p.Fiber S)) [q.IsPrime]:q.LiesOver p:=
 .trans _ (⊥:Ideal p.ResidueField) _
instance (q:Ideal (p.Fiber S)) [q.IsPrime]:Localization.AtPrime.IsLiesOverAlgebra p q where
 algebraMap_eq:=(Localization.localRingHom_unique p q _ (Ideal.over_def q p) fun _↦rfl).symm
lemma Fiber.exists_smul_eq_one_tmul (x:p.Fiber S):∃ r∉p,∃ s,r • x=1 ⊗ₜ[R] s:=by
 obtain ⟨r,hr,s,e⟩:=Ideal.ResidueField.exists_smul_eq_tmul_one _
   (Algebra.TensorProduct.comm _ _ _ x)
 refine ⟨r,hr,s,by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def Fiber.algEquivQuotient:
   letI Rp:=Localization p.primeCompl
   letI pRp:=IsLocalRing.maximalIdeal Rp
   letI Sp:=Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
   letI pSp:=pRp.map (algebraMap Rp Sp)
   p.Fiber S ≃ₐ[S] Sp ⧸ pSp:=
 (commRight R S p.ResidueField).symm.trans <| (tensorQuotientEquiv S _ S _).trans <|
   { __:=Ideal.quotientEquiv _ _ (Localization.tensorLeftAlgEquiv p.primeCompl S) (by
       rw [←Ideal.map_coe includeRight,Ideal.map_map]
       congr
       ext
       simp [Localization.tensorLeftAlgEquiv_apply_one_tmul p.primeCompl])
     commutes':=by simp}
noncomputable def Fiber.algEquivAux₁:
   letI Sp:=Localization (algebraMapSubmonoid S p.primeCompl)
   letI pS:=p.map (algebraMap R S)
   letI:Algebra S (p.Fiber S):=rightAlgebra
   p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp):=
 letI:Algebra S (p.Fiber S):=rightAlgebra
 (Fiber.algEquivQuotient p).trans <| quotientEquivAlgOfEq S <| by
   rw [←Localization.AtPrime.map_eq_maximalIdeal,map_map, ←IsScalarTower.algebraMap_eq,
     IsScalarTower.algebraMap_eq R S, ←map_map]
noncomputable def Fiber.algEquivAux₂ (q:Ideal (p.Fiber S)) [q.IsPrime]:
   letI r:=q.comap includeRight
   letI Sr:=Localization.AtPrime r
   letI pS:=p.map (algebraMap R S)
   Localization.AtPrime q ≃ₐ[R] Sr ⧸ pS.map (algebraMap S Sr):=
 letI:Algebra S (p.Fiber S):=rightAlgebra
 letI Sp:=Localization (algebraMapSubmonoid S p.primeCompl)
 letI pS:=p.map (algebraMap R S)
 letI SpS:=S ⧸ pS
 letI r:=q.comap includeRight
 letI Sr:=Localization.AtPrime r
 letI e₁:p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp):=algEquivAux₁ p
 letI q':Ideal (Sp ⧸ pS.map (algebraMap S Sp)):=q.comap e₁.symm
 haveI:(q'.under SpS).LiesOver r:=under_liesOver_of_liesOver SpS q' (q.under S)
 haveI:algebraMapSubmonoid SpS r.primeCompl=(q'.under SpS).primeCompl:=
   algebraMapSubmonoid_primeCompl_of_liesOver_surjective (q'.under SpS) r Quotient.mk_surjective
 haveI:IsLocalization (algebraMapSubmonoid SpS r.primeCompl) (Localization.AtPrime q'):=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     (algebraMapSubmonoid SpS (algebraMapSubmonoid S p.primeCompl)) (Localization.AtPrime q') q'
 haveI:=IsScalarTower.to₁₃₄ R S SpS (Localization.AtPrime q')
 haveI:=IsScalarTower.to₁₃₄ R S SpS (Sr ⧸ pS.map (algebraMap S Sr))
 ((Localization.localAlgEquiv q' q e₁.symm rfl).symm.restrictScalars R).trans
   ((IsLocalization.algEquiv (algebraMapSubmonoid SpS r.primeCompl) (Localization.AtPrime q')
     (Sr ⧸ pS.map (algebraMap S Sr))).restrictScalars R)
noncomputable def Fiber.localizationAlgEquivQuotient (q:Ideal (p.Fiber S)) [q.IsPrime]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime (q.comap includeRight))]
   [Localization.AtPrime.IsLiesOverAlgebra p (q.comap includeRight)]:
   letI r:=q.comap includeRight
   letI Sr:=Localization.AtPrime r
   Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr):=
 ((algEquivAux₂ p q).extendScalarsOfIsLocalization (Localization.AtPrime p) p.primeCompl).trans
   (quotientEquivAlgOfEq (Localization.AtPrime p) (map_map _ _))
end Ideal
@[deprecated (since:="2026-05-11")] alias Fiber.algEquivQuotient:=Ideal.Fiber.algEquivQuotient
set_option backward.isDefEq.respectTransparency false in
variable (R S) in
@[simps]
noncomputable def PrimeSpectrum.preimageEquivFiber (p:PrimeSpectrum R):
   comap (algebraMap R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where
 toFun q:=⟨RingHom.ker (Algebra.TensorProduct.lift
   (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId _ _) congr($(q.2.symm).asIdeal))
     (IsScalarTower.toAlgHom _ _ _) fun _ _↦.all _ _).toRingHom,RingHom.ker_isPrime _⟩
 invFun q:=⟨q.comap Algebra.TensorProduct.includeRight.toRingHom,by
   simp only [AlgHom.toRingHom_eq_coe,Set.mem_preimage, ←comap_comp_apply,
     AlgHom.comp_algebraMap_of_tower]
   exact (residueField_comap _).le ⟨q.comap (algebraMap _ _),rfl⟩⟩
 left_inv q:=by ext x;simp
 right_inv q:=by
   ext x
   obtain ⟨r,hr,s,e⟩:=Ideal.Fiber.exists_smul_eq_one_tmul _ x
   have:=@PrimeSpectrum.isPrime
   rw [←Ideal.IsPrime.mul_mem_left_iff (x:=algebraMap _ _ r),iff_comm,
     ←Ideal.IsPrime.mul_mem_left_iff (x:=algebraMap _ _ r), ←Algebra.smul_def,e]
   · simp
   · rw [←Ideal.mem_comap, ←PrimeSpectrum.comap_asIdeal]
     convert! hr
     exact (residueField_comap _).le ⟨q.comap (algebraMap _ _),rfl⟩
   · simpa [-Algebra.algebraMap_self, -AlgHom.commutes, -AlgHom.map_algebraMap,
       -Ideal.ResidueField.map_algebraMap]
variable (R S) in
@[simps!]
noncomputable def PrimeSpectrum.preimageOrderIsoFiber (p:PrimeSpectrum R):
   comap (algebraMap R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where
 toEquiv:=preimageEquivFiber R S p
 map_rel_iff' {q₁ q₂}:=by
   constructor
   · obtain ⟨q₁,rfl⟩:=(preimageEquivFiber R S p).symm.surjective q₁
     obtain ⟨q₂,rfl⟩:=(preimageEquivFiber R S p).symm.surjective q₂
     simpa using! Ideal.comap_mono
   · intro H x hx
     obtain ⟨r,hr,s,e⟩:=Ideal.Fiber.exists_smul_eq_one_tmul _ x
     rw [←Ideal.IsPrime.mul_mem_left_iff (x:=algebraMap _ _ r), ←Algebra.smul_def,e] at hx ⊢
     · replace hx:s∈q₁.1.asIdeal:=by simpa using! hx
       simpa using! H hx
     · rw [←q₂.2] at hr;simpa [IsScalarTower.algebraMap_apply R S q₂.1.asIdeal.ResidueField]
     · rw [←q₁.2] at hr;simpa [IsScalarTower.algebraMap_apply R S q₁.1.asIdeal.ResidueField]
@[deprecated (since:="2025-12-07")]
alias PrimeSpectrum.preimageOrderIsoTensorResidueField:=PrimeSpectrum.preimageOrderIsoFiber
variable (R S) in
@[simps!]
noncomputable def PrimeSpectrum.primesOverOrderIsoFiber (R S:Type*) [CommRing R]
   [CommRing S] [Algebra R S] (p:Ideal R) [p.IsPrime]:
   p.primesOver S ≃o PrimeSpectrum (p.Fiber S):=
 .trans ⟨⟨fun q↦⟨⟨q,q.2.1⟩,PrimeSpectrum.ext q.2.2.1.symm⟩,
   fun q↦⟨q.1.asIdeal,⟨q.1.2,⟨congr($(q.2).1).symm⟩⟩⟩,fun _↦rfl,fun _↦rfl⟩,.rfl⟩
   (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p,‹_›⟩)
@[simps!]
noncomputable def PrimeSpectrum.preimageHomeomorphFiber (R S:Type*) [CommRing R]
   [CommRing S] [Algebra R S] (p:PrimeSpectrum R):
   comap (algebraMap R S) ⁻¹' {p} ≃ₜ PrimeSpectrum (p.asIdeal.Fiber S):=by
 letI H:Topology.IsEmbedding (preimageOrderIsoFiber R S p).symm:=by
   refine (Topology.IsEmbedding.of_comp_iff .subtypeVal).mp ?_
   have:=PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks _ S _
     (Ideal.surjectiveOnStalks_residueField p.asIdeal)
   exact ((Homeomorph.prodUnique _ _).isEmbedding.comp this).comp
     (homeomorphOfRingEquiv (Algebra.TensorProduct.comm _ _ _).toRingEquiv).isEmbedding
 exact
 { __:=preimageOrderIsoFiber R S p
   continuous_toFun:=by
     convert!
       (H.toHomeomorphOfSurjective (preimageOrderIsoFiber R S p).symm.surjective).symm.continuous
     ext1 x
     obtain ⟨x,rfl⟩:=(H.toHomeomorphOfSurjective
       (preimageOrderIsoFiber R S p).symm.surjective).surjective x
     simp only [Equiv.toFun_as_coe,RelIso.coe_fn_toEquiv,Homeomorph.symm_apply_apply]
     simp
   continuous_invFun:=H.continuous}
@[simp]
theorem PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply (q:PrimeSpectrum (p.Fiber S)):
   (primesOverOrderIsoFiber R S p).symm q=q.1.comap Algebra.TensorProduct.includeRight:=
 rfl
end ProximityFlatProofPort
end PackedLegacy_AT

/-! Packed from ProximityPrize.SubmissionLower.HX. -/
section PackedLegacy_HX
section ProximityFlatProofPort
variable {M:Type*}
namespace Submonoid
@[to_additive]
noncomputable instance [Monoid M]:Group (IsUnit.submonoid M):=
  { (inferInstance:Monoid (IsUnit.submonoid M)) with
    inv:=fun x↦⟨x.prop.unit⁻¹.val,x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel:=fun x↦
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val)}
@[to_additive]
noncomputable instance [CommMonoid M]:CommGroup (IsUnit.submonoid M):=
  { (inferInstance:Group (IsUnit.submonoid M)) with
    mul_comm:=fun a b↦by convert! mul_comm a b}
@[to_additive]
theorem _root_.IsUnit.submonoid.coe_inv [Monoid M] (x:IsUnit.submonoid M):
    ↑x⁻¹=(↑x.prop.unit⁻¹:M):=
  rfl
@[deprecated (since:="2026-05-24")]
alias _root_.AddSubmonoid.IsUnit.Submonoid.coe_neg:=IsAddUnit.addSubmonoid.coe_neg
set_option linter.dupNamespace false in
@[to_additive existing,deprecated (since:="2026-05-24")]
alias IsUnit.Submonoid.coe_inv:=IsUnit.submonoid.coe_inv
section Monoid
variable [Monoid M] (S:Submonoid M)
@[to_additive
 ]
def leftInv:Submonoid M where
  carrier:={ x:M | ∃ y:S,x*y=1}
  one_mem':=⟨1,mul_one 1⟩
  mul_mem':=fun {a} _b ⟨a',ha⟩ ⟨b',hb⟩↦
    ⟨b'*a',by simp only [coe_mul, ←mul_assoc,mul_assoc a,hb,mul_one,ha]⟩
@[to_additive]
theorem leftInv_leftInv_le:S.leftInv.leftInv ≤ S:=by
  rintro x ⟨⟨y,z,h₁⟩,h₂:x*y=1⟩
  convert! z.prop
  rw [←mul_one x, ←h₁, ←mul_assoc,h₂,one_mul]
@[to_additive]
theorem unit_mem_leftInv (x:Mˣ) (hx:(x:M)∈S):((x⁻¹:):M)∈S.leftInv:=
  ⟨⟨x,hx⟩,x.inv_val⟩
@[to_additive]
theorem leftInv_leftInv_eq (hS:S ≤ IsUnit.submonoid M):S.leftInv.leftInv=S:=by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have:x=((hS hx).unit⁻¹⁻¹:Mˣ):=by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)
@[to_additive
 ]
noncomputable def fromLeftInv:S.leftInv → S:=fun x↦x.prop.choose
@[to_additive (attr:=simp)]
theorem mul_fromLeftInv (x:S.leftInv):(x:M)*S.fromLeftInv x=1:=
  x.prop.choose_spec
@[to_additive (attr:=simp)]
theorem fromLeftInv_one:S.fromLeftInv 1=1:=
  (one_mul _).symm.trans (Subtype.ext <| S.mul_fromLeftInv 1)
end Monoid
section CommMonoid
variable [CommMonoid M] (S:Submonoid M)
@[to_additive (attr:=simp)]
theorem fromLeftInv_mul (x:S.leftInv):(S.fromLeftInv x:M)*x=1:=by
  rw [mul_comm,mul_fromLeftInv]
@[to_additive]
theorem leftInv_le_isUnit:S.leftInv ≤ IsUnit.submonoid M:=fun x ⟨y,hx⟩↦
  ⟨⟨x,y,hx,mul_comm x y ▸ hx⟩,rfl⟩
@[to_additive]
theorem fromLeftInv_eq_iff (a:S.leftInv) (b:M):
    (S.fromLeftInv a:M)=b ↔ (a:M)*b=1:=by
  rw [←IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop),S.mul_fromLeftInv,eq_comm]
@[to_additive (attr:=simps)
 ]
noncomputable def fromCommLeftInv:S.leftInv →*S where
  toFun:=S.fromLeftInv
  map_one':=S.fromLeftInv_one
  map_mul' x y:=
    Subtype.ext <| by
      rw [fromLeftInv_eq_iff,mul_comm x,Submonoid.coe_mul,Submonoid.coe_mul,mul_assoc, ←
        mul_assoc (x:M),mul_fromLeftInv,one_mul,mul_fromLeftInv]
variable (hS:S ≤ IsUnit.submonoid M)
@[to_additive (attr:=simps apply)
 ]
noncomputable def leftInvEquiv:S.leftInv ≃*S:=
  { S.fromCommLeftInv with
    invFun:=fun x↦⟨↑(hS x.2).unit⁻¹,x,by simp⟩
    left_inv:=by
      intro x
      ext
      simp [←Units.mul_eq_one_iff_inv_eq]
    right_inv:=by
      rintro ⟨x,hx⟩
      ext
      simp [fromLeftInv_eq_iff]}
@[to_additive (attr:=simp)]
theorem fromLeftInv_leftInvEquiv_symm (x:S):S.fromLeftInv ((S.leftInvEquiv hS).symm x)=x:=
  (S.leftInvEquiv hS).right_inv x
@[to_additive (attr:=simp)]
theorem leftInvEquiv_symm_fromLeftInv (x:S.leftInv):
    (S.leftInvEquiv hS).symm (S.fromLeftInv x)=x:=
  (S.leftInvEquiv hS).left_inv x
@[to_additive]
theorem leftInvEquiv_mul (x:S.leftInv):(S.leftInvEquiv hS x:M)*x=1:=by
  simpa only [leftInvEquiv_apply,fromCommLeftInv] using fromLeftInv_mul S x
@[to_additive]
theorem mul_leftInvEquiv (x:S.leftInv):(x:M)*S.leftInvEquiv hS x=1:=by
  simp only [leftInvEquiv_apply,fromCommLeftInv,mul_fromLeftInv]
@[to_additive (attr:=simp)]
theorem leftInvEquiv_symm_mul (x:S):((S.leftInvEquiv hS).symm x:M)*x=1:=by
  convert! S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp
@[to_additive (attr:=simp)]
theorem mul_leftInvEquiv_symm (x:S):(x:M)*(S.leftInvEquiv hS).symm x=1:=by
  convert! S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp
end CommMonoid
section Group
variable [Group M] (S:Submonoid M)
open scoped Pointwise
@[to_additive]
theorem leftInv_eq_inv:S.leftInv=S⁻¹:=
  Submonoid.ext fun _↦
    ⟨fun h↦Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h↦⟨⟨_,h⟩,mul_inv_cancel _⟩⟩
@[to_additive (attr:=simp)]
theorem fromLeftInv_eq_inv (x:S.leftInv):(S.fromLeftInv x:M)=(x:M)⁻¹:=by
  rw [←mul_right_inj (x:M),mul_inv_cancel,mul_fromLeftInv]
end Group
section CommGroup
variable [CommGroup M] (S:Submonoid M) (hS:S ≤ IsUnit.submonoid M)
@[to_additive (attr:=simp)]
theorem leftInvEquiv_symm_eq_inv (x:S):((S.leftInvEquiv hS).symm x:M)=(x:M)⁻¹:=by
  rw [←mul_right_inj (x:M),mul_inv_cancel,mul_leftInvEquiv_symm]
end CommGroup
end Submonoid
end ProximityFlatProofPort
end PackedLegacy_HX

/-! Packed from ProximityPrize.SubmissionLower.F2. -/
section PackedLegacy_F2
section ProximityFlatProofPort
variable {R:Type*} [CommRing R] (M:Submonoid R) (S:Type*) [CommRing S]
 [Algebra R S]
open Function
namespace IsLocalization
section InvSubmonoid
def invSubmonoid:Submonoid S:=
 (M.map (algebraMap R S)).leftInv
variable [IsLocalization M S]
theorem submonoid_map_le_is_unit:M.map (algebraMap R S) ≤ IsUnit.submonoid S:=by
 rintro _ ⟨a,ha,rfl⟩
 exact IsLocalization.map_units S ⟨_,ha⟩
noncomputable abbrev equivInvSubmonoid:M.map (algebraMap R S) ≃*invSubmonoid M S:=
 ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm
noncomputable def toInvSubmonoid:M →*invSubmonoid M S:=
 (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S:R →*S).submonoidMap M)
theorem toInvSubmonoid_surjective:Function.Surjective (toInvSubmonoid M S):=
 Function.Surjective.comp (β:=M.map (algebraMap R S))
   (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)
@[simp]
theorem toInvSubmonoid_mul (m:M):(toInvSubmonoid M S m:S)*algebraMap R S m=1:=
 Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _
@[simp]
theorem mul_toInvSubmonoid (m:M):algebraMap R S m*(toInvSubmonoid M S m:S)=1:=
 Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_,_⟩
@[simp]
theorem smul_toInvSubmonoid (m:M):m • (toInvSubmonoid M S m:S)=1:=by
 convert! mul_toInvSubmonoid M S m
 ext
 rw [←Algebra.smul_def]
 rfl
variable {S}
theorem surj'' (z:S):∃ (r:R) (m:M),z=r • (toInvSubmonoid M S m:S):=by
 rcases IsLocalization.surj M z with ⟨⟨r,m⟩,e:z*_=algebraMap R S r⟩
 refine ⟨r,m,?_⟩
 rw [Algebra.smul_def, ←e,mul_assoc]
 simp
theorem toInvSubmonoid_eq_mk' (x:M):(toInvSubmonoid M S x:S)=mk' S 1 x:=by
 rw [←(IsLocalization.map_units S x).mul_left_inj]
 simp
theorem mem_invSubmonoid_iff_exists_mk' (x:S):
   x∈invSubmonoid M S ↔ ∃ m:M,mk' S 1 m=x:=by
 simp_rw [←toInvSubmonoid_eq_mk']
 exact ⟨fun h => ⟨_,congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x,h⟩).choose_spec⟩,
   fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩
variable (S)
theorem span_invSubmonoid:Submodule.span R (invSubmonoid M S:Set S)=⊤:=by
 rw [eq_top_iff]
 rintro x-
 rcases IsLocalization.surj'' M x with ⟨r,m,rfl⟩
 exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)
theorem finiteType_of_monoid_fg [Monoid.FG M]:Algebra.FiniteType R S:=by
 have:=Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
 rw [Monoid.fg_iff_submonoid_fg] at this
 rcases this with ⟨s,hs⟩
 refine ⟨⟨s,?_⟩⟩
 rw [eq_top_iff]
 rintro x-
 change x∈(Subalgebra.toSubmodule (Algebra.adjoin R _:Subalgebra R S):Set S)
 rw [Algebra.adjoin_eq_span,hs,span_invSubmonoid]
 trivial
instance {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
   (M:Submonoid S) [Monoid.FG M]:Algebra.FiniteType R (Localization M):=
 .trans ‹_› (IsLocalization.finiteType_of_monoid_fg M _)
end InvSubmonoid
end IsLocalization
end ProximityFlatProofPort
end PackedLegacy_F2

/-! Packed from ProximityPrize.SubmissionLower.W0. -/
section PackedLegacy_W0
section ProximityFlatProofPort
open Topology TopologicalSpace
variable («X») {«Y»} [TopologicalSpace «X»] [TopologicalSpace «Y»] {f:«X» → «Y»}
section closedPoints
def closedPoints:Set «X»:=setOf (IsClosed {·})
variable {«X»}
@[simp]
lemma mem_closedPoints_iff {x}:x∈closedPoints «X» ↔ IsClosed {x}:=Iff.rfl
lemma preimage_closedPoints_subset (hf:Function.Injective f) (hf':Continuous f):
   f ⁻¹' closedPoints «Y» ⊆ closedPoints «X»:=by
 intro x hx
 rw [mem_closedPoints_iff]
 convert! continuous_iff_isClosed.mp hf' _ hx
 rw [←Set.image_singleton,Set.preimage_image_eq _ hf]
lemma Topology.IsClosedEmbedding.preimage_closedPoints (hf:IsClosedEmbedding f):
   f ⁻¹' closedPoints «Y»=closedPoints «X»:=by
 ext x
 simp [mem_closedPoints_iff, ←Set.image_singleton,hf.isClosed_iff_image_isClosed]
lemma closedPoints_eq_univ [T1Space «X»]:
   closedPoints «X»=Set.univ:=
 Set.eq_univ_iff_forall.mpr fun _↦isClosed_singleton
lemma Set.Finite.isDiscrete_of_subset_closedPoints
   {s:Set «X»} (hs:s.Finite) (hs':s ⊆ closedPoints «X»):IsDiscrete s:=by
 have:T1Space s:=⟨fun x↦by convert! (hs' x.2).preimage continuous_subtype_val;aesop⟩
 have:Finite s:=hs
 exact ⟨inferInstance⟩
end closedPoints
@[mk_iff,stacks 005U]
class JacobsonSpace:Prop where
 closure_inter_closedPoints:∀ {«Z»},IsClosed «Z» → closure («Z» ∩ closedPoints «X»)=«Z»
export JacobsonSpace (closure_inter_closedPoints)
variable {«X»}
lemma closure_closedPoints [JacobsonSpace «X»]:closure (closedPoints «X»)=Set.univ:=by
 simpa using closure_inter_closedPoints isClosed_univ
lemma jacobsonSpace_iff_locallyClosed:
   JacobsonSpace «X» ↔ ∀ «Z»,«Z».Nonempty → IsLocallyClosed «Z» → («Z» ∩ closedPoints «X»).Nonempty:=by
 rw [jacobsonSpace_iff]
 constructor
 · simp_rw [isLocallyClosed_iff_isOpen_coborder,coborder,isOpen_compl_iff,
     Set.nonempty_iff_ne_empty]
   intro H «Z» hZ hZ' e
   have:«Z» ⊆ closure «Z» \ «Z»:=by
     refine subset_closure.trans ?_
     nth_rw 1 [←H isClosed_closure]
     rw [hZ'.closure_subset_iff,Set.subset_sdiff,Set.disjoint_iff,Set.inter_assoc,
       Set.inter_comm _ «Z»,e]
     exact ⟨Set.inter_subset_left,Set.inter_subset_right⟩
   rw [Set.subset_sdiff,disjoint_self,Set.bot_eq_empty] at this
   exact hZ this.2
 · intro H «Z» hZ
   refine subset_antisymm (hZ.closure_subset_iff.mpr Set.inter_subset_left) ?_
   rw [←Set.disjoint_compl_left_iff_subset,Set.disjoint_iff_inter_eq_empty,
     ←Set.not_nonempty_iff_eq_empty]
   intro H'
   have:=H _ H' (isClosed_closure.isOpen_compl.isLocallyClosed.inter hZ.isLocallyClosed)
   rw [Set.nonempty_iff_ne_empty,Set.inter_assoc,ne_eq,
     ←Set.disjoint_iff_inter_eq_empty,Set.disjoint_compl_left_iff_subset] at this
   exact this subset_closure
lemma nonempty_inter_closedPoints [JacobsonSpace «X»] {«Z»:Set «X»}
   (hZ:«Z».Nonempty) (hZ':IsLocallyClosed «Z»):(«Z» ∩ closedPoints «X»).Nonempty:=
 jacobsonSpace_iff_locallyClosed.mp inferInstance «Z» hZ hZ'
theorem JacobsonSpace.closure_inter_closedPoints_eq_closure [JacobsonSpace «X»]
   {S:Set «X»} (hS:IsLocallyClosed S):closure (S ∩ closedPoints «X»)=closure S:=by
 refine (closure_mono (Set.inter_subset_left)).antisymm ?_
 rw [IsClosed.closure_subset_iff isClosed_closure]
 intro x hx
 by_contra H
 obtain ⟨y,⟨hy₁,hy₂⟩,hy₃⟩:=nonempty_inter_closedPoints («Z»:=S \ closure (S ∩ closedPoints «X»))
   ⟨x,hx,H⟩ (.inter hS isClosed_closure.isOpen_compl.isLocallyClosed)
 exact hy₂ (subset_closure ⟨hy₁,hy₃⟩)
lemma isClosed_singleton_of_isLocallyClosed_singleton [JacobsonSpace «X»] {x:«X»}
   (hx:IsLocallyClosed {x}):IsClosed {x}:=by
 obtain ⟨_,⟨y,rfl:y=x,rfl⟩,hy'⟩:=
   nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
 exact hy'
lemma Topology.IsOpenEmbedding.preimage_closedPoints (hf:IsOpenEmbedding f) [JacobsonSpace «Y»]:
   f ⁻¹' closedPoints «Y»=closedPoints «X»:=by
 apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
 intro x hx
 apply isClosed_singleton_of_isLocallyClosed_singleton
 rw [←Set.image_singleton]
 exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)
lemma JacobsonSpace.of_isOpenEmbedding [JacobsonSpace «Y»] (hf:IsOpenEmbedding f):
   JacobsonSpace «X»:=by
 rw [jacobsonSpace_iff_locallyClosed, ←hf.preimage_closedPoints]
 intro «Z» hZ hZ'
 obtain ⟨_,⟨x,hx,rfl⟩,hx'⟩:=nonempty_inter_closedPoints
   (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
 exact ⟨_,hx,hx'⟩
lemma JacobsonSpace.of_isClosedEmbedding [JacobsonSpace «Y»] (hf:IsClosedEmbedding f):
   JacobsonSpace «X»:=by
 rw [jacobsonSpace_iff_locallyClosed, ←hf.preimage_closedPoints]
 intro «Z» hZ hZ'
 obtain ⟨_,⟨x,hx,rfl⟩,hx'⟩:=nonempty_inter_closedPoints
   (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
 exact ⟨_,hx,hx'⟩
lemma JacobsonSpace.discreteTopology [JacobsonSpace «X»]
   (h:(closedPoints «X»).Finite):DiscreteTopology «X»:=by
 have:closedPoints «X»=Set.univ:=by
   rw [←Set.univ_subset_iff, ←closure_closedPoints,
     closure_subset_iff_isClosed, ←(closedPoints «X»).biUnion_of_singleton]
   exact h.isClosed_biUnion fun _↦id
 have inst:Finite «X»:=Set.finite_univ_iff.mp (this ▸ h)
 rw [discreteTopology_iff_forall_isOpen]
 intro s
 rw [←isClosed_compl_iff, ←sᶜ.biUnion_of_singleton]
 refine sᶜ.toFinite.isClosed_biUnion fun x _↦?_
 rw [←mem_closedPoints_iff,this]
 trivial
instance (priority:=100) [Finite «X»] [JacobsonSpace «X»]:DiscreteTopology «X»:=
 JacobsonSpace.discreteTopology (Set.toFinite _)
instance (priority:=100) [T1Space «X»]:JacobsonSpace «X»:=
 ⟨by simp [closedPoints_eq_univ,closure_eq_iff_isClosed]⟩
lemma TopologicalSpace.IsOpenCover.jacobsonSpace_iff {ι:Type*} {U:ι → Opens «X»}
   (hU:IsOpenCover U):JacobsonSpace «X» ↔ ∀ i,JacobsonSpace (U i):=by
 refine ⟨fun H i↦.of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal,fun H↦?_⟩
 rw [jacobsonSpace_iff_locallyClosed]
 intro «Z» hZ hZ'
 rw [←hU.iUnion_inter «Z»,Set.nonempty_iUnion] at hZ
 obtain ⟨i,x,hx,hx'⟩:=hZ
 obtain ⟨y,hy,hy'⟩:=(jacobsonSpace_iff_locallyClosed.mp (H i)) _ ⟨⟨x,hx'⟩,hx⟩
   (hZ'.preimage continuous_subtype_val)
 refine ⟨y,hy,hU.isClosed_iff_coe_preimage.mpr fun j↦?_⟩
 by_cases h:(y:«X»)∈U j
 · convert_to IsClosed {(⟨y,h⟩:U j)}
   · ext;simp [←Subtype.coe_inj]
   apply isClosed_singleton_of_isLocallyClosed_singleton
   convert!
     (hy'.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
           (U i).2.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed).preimage
       continuous_subtype_val
   ext
   simp [←Subtype.coe_inj]
 · convert! isClosed_empty
   rw [Set.eq_empty_iff_forall_notMem]
   intro z (hz:z.1=y.1)
   exact h (hz ▸ z.2)
theorem subsingleton_image_closure_of_finite_of_isPreirreducible [JacobsonSpace «X»]
   {S:Set «X»} (hS:IsLocallyClosed S) (hS':IsPreirreducible S)
   (hf₁:Continuous f) (hf₂:IsClosedMap f) (hfS:(f '' S).Finite):
   (f '' closure S).Subsingleton:=by
 obtain rfl | hS'':=S.eq_empty_or_nonempty
 · simp
 replace hS':IsIrreducible S:=⟨hS'',hS'⟩
 have H₁:IsIrreducible (S ∩ closedPoints «X»):=by
   rwa [←isIrreducible_iff_closure, ←JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
     isIrreducible_iff_closure] at hS'
 have H₂:f '' (S ∩ closedPoints «X») ⊆ closedPoints «Y»:=by
   rintro _ ⟨x,hx,rfl⟩;simpa using hf₂ _ hx.2
 have H₃:=((hfS.subset (Set.image_mono Set.inter_subset_left)).isDiscrete_of_subset_closedPoints
   H₂).subsingleton_of_isPreirreducible (H₁.image _ hf₁.continuousOn).isPreirreducible
 have H₄:IsClosed (f '' (S ∩ closedPoints «X»)):=by
   obtain (h | ⟨x,hx⟩):=Set.eq_empty_or_nonempty (f '' (S ∩ closedPoints «X»))
   · simp [h]
   · rw [H₃.eq_singleton_of_mem hx];exact H₂ hx
 have:=image_closure_subset_closure_image (s:=S ∩ closedPoints «X») hf₁
 rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hS,H₄.closure_eq] at this
 exact H₃.anti this
end ProximityFlatProofPort
end PackedLegacy_W0

/-! Packed from ProximityPrize.SubmissionLower.IY. -/
section PackedLegacy_IY
section ProximityFlatProofPort
open Ideal
variable {R:Type*} [CommRing R]
namespace PrimeSpectrum
lemma exists_isClosed_singleton_of_isJacobsonRing [IsJacobsonRing R]
   (s:(Set (PrimeSpectrum R))) (hs:IsOpen s) (hs':s.Nonempty):
   ∃ x∈s,IsClosed {x}:=by
 simp_rw [isClosed_singleton_iff_isMaximal]
 obtain ⟨I,hI'⟩:=(isClosed_iff_zeroLocus_ideal _).mp hs.isClosed_compl
 simp_rw [←@Set.notMem_compl_iff _ s,hI',mem_zeroLocus]
 have:=hs'.ne_empty
 contrapose! this
 simp_rw [not_imp_not] at this
 rw [←Set.compl_univ,eq_compl_comm,hI',eq_comm, ←zeroLocus_bot,
   zeroLocus_eq_iff,Ideal.radical_eq_jacobson,Ideal.radical_eq_jacobson]
 refine le_antisymm (le_sInf ?_) (Ideal.jacobson_mono bot_le)
 rintro x ⟨-,hx⟩
 exact sInf_le ⟨this ⟨x,hx.isPrime⟩ hx,hx⟩
instance [IsJacobsonRing R]:JacobsonSpace (PrimeSpectrum R):=by
 rw [jacobsonSpace_iff_locallyClosed]
 rintro S hS ⟨U,«Z»,hU,hZ,rfl⟩
 simp only [←isClosed_compl_iff,isClosed_iff_zeroLocus_ideal,@compl_eq_comm _ U] at hU hZ
 obtain ⟨⟨I,rfl⟩,⟨J,rfl⟩⟩:=And.intro hU hZ
 simp only [Set.nonempty_iff_ne_empty,ne_eq,Set.inter_assoc,
   ←Set.disjoint_iff_inter_eq_empty,Set.disjoint_compl_left_iff_subset,
   zeroLocus_subset_zeroLocus_iff,Ideal.radical_eq_jacobson,Ideal.jacobson,le_sInf_iff] at hS ⊢
 contrapose hS
 rintro x ⟨hJx,hx⟩
 exact @hS ⟨x,hx.isPrime⟩ ⟨hJx,(isClosed_singleton_iff_isMaximal _).mpr hx⟩
lemma isJacobsonRing_iff_jacobsonSpace:
   IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R):=by
 refine ⟨fun _↦inferInstance,fun H↦⟨fun I hI↦le_antisymm ?_ Ideal.le_jacobson⟩⟩
 rw [←I.isRadical_jacobson.radical]
 conv_rhs => rw [←hI.radical]
 simp_rw [←vanishingIdeal_zeroLocus_eq_radical]
 apply vanishingIdeal_anti_mono
 rw [←H.1 (isClosed_zeroLocus I),(isClosed_zeroLocus _).closure_subset_iff]
 rintro x ⟨hx:I ≤ x.asIdeal,hx'⟩
 change jacobson I ≤ x.asIdeal
 exact sInf_le ⟨hx,(isClosed_singleton_iff_isMaximal _).mp hx'⟩
lemma isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
   [IsNoetherianRing R] [IsJacobsonRing R] (x:PrimeSpectrum R):
   List.TFAE [IsOpen {x},IsClopen {x},IsClosed {x}∧StableUnderGeneralization {x}]:=by
 tfae_have 1 → 2
 | h => by
   obtain ⟨y,rfl:y=x,h'⟩:=exists_isClosed_singleton_of_isJacobsonRing _ h
     ⟨x,Set.mem_singleton x⟩
   exact ⟨h',h⟩
 tfae_have 2 → 3
 | h => ⟨h.isClosed,h.isOpen.stableUnderGeneralization⟩
 tfae_have 3 → 1
 | ⟨h₁,h₂⟩ => by
   rw [isClosed_singleton_iff_isMaximal, ←isMax_iff] at h₁
   suffices {x}=(⋃ p∈{ p:PrimeSpectrum R | IsMin p∧p≠x},closure {p})ᶜ by
     rw [this,isOpen_compl_iff]
     refine Set.Finite.isClosed_biUnion ?_ (fun _ _↦isClosed_closure)
     exact (finite_setOf_isMin R).subset fun x h↦h.1
   ext p
   simp only [Set.mem_singleton_iff,ne_eq,Set.mem_setOf_eq,Set.compl_iUnion,Set.mem_iInter,
     Set.mem_compl_iff,and_imp, ←specializes_iff_mem_closure, ←le_iff_specializes,
     not_imp_not]
   constructor
   · rintro rfl _ _
     rw [stableUnderGeneralization_singleton, ←isMin_iff] at h₂
     exact h₂.eq_of_le
   · intro hp
     apply h₁.eq_of_ge
     obtain ⟨q,hq,hq'⟩:=Ideal.exists_minimalPrimes_le (J:=p.asIdeal) bot_le
     exact (hp ⟨q,hq.1.1⟩ (isMin_iff.mpr hq) hq').ge.trans hq'
 tfae_finish
end PrimeSpectrum
end ProximityFlatProofPort
end PackedLegacy_IY

/-! Packed from ProximityPrize.SubmissionLower.CR. -/
section PackedLegacy_CR
section ProximityFlatProofPort
variable (R S M₁ M₂ M₃:Type*)
namespace TensorProduct
variable [CommSemiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
 [Algebra R S]
 [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂] [Module R M₃]
attribute [ext] TensorProduct.ext
def prodRight:M₁ ⊗[R] (M₂ × M₃) ≃ₗ[S] (M₁ ⊗[R] M₂) × (M₁ ⊗[R] M₃):=
 LinearEquiv.ofLinear
   (TensorProduct.AlgebraTensorModule.lift <|
     LinearMap.prodMapLinear R M₂ M₃ (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₃) S ∘ₗ
       LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
   (LinearMap.coprod
     (AlgebraTensorModule.lTensor _ _ <| LinearMap.inl _ _ _)
     (AlgebraTensorModule.lTensor _ _ <| LinearMap.inr _ _ _))
   (by ext <;> simp)
   (by ext <;> simp)
@[simp] theorem prodRight_tmul (m₁:M₁) (m:M₂ × M₃):
   prodRight R S M₁ M₂ M₃ (m₁ ⊗ₜ m)=(m₁ ⊗ₜ m.1,m₁ ⊗ₜ m.2):=
 rfl
@[simp] theorem prodRight_symm_tmul (m₁:M₁) (m₂:M₂) (m₃:M₃):
   (prodRight R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂,m₁ ⊗ₜ m₃)=(m₁ ⊗ₜ (m₂,m₃)):=
 (LinearEquiv.symm_apply_eq _).mpr rfl
variable [Module S M₂] [IsScalarTower R S M₂]
def prodLeft:(M₁ × M₂) ⊗[R] M₃ ≃ₗ[S] (M₁ ⊗[R] M₃) × (M₂ ⊗[R] M₃):=
 AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
     TensorProduct.prodRight R R _ _ _ ≪≫ₗ
     (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
   fun c x↦x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)
@[simp] theorem prodLeft_tmul (m₁:M₁) (m₂:M₂) (m₃:M₃):
   prodLeft R S M₁ M₂ M₃ ((m₁,m₂) ⊗ₜ m₃)=(m₁ ⊗ₜ m₃,m₂ ⊗ₜ m₃):=
 rfl
@[simp] theorem prodLeft_symm_tmul (m₁:M₁) (m₂:M₂) (m₃:M₃):
   (prodLeft R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₃,m₂ ⊗ₜ m₃)=((m₁,m₂) ⊗ₜ m₃):=
 (LinearEquiv.symm_apply_eq _).mpr rfl
end TensorProduct
end ProximityFlatProofPort
end PackedLegacy_CR

/-! Packed from ProximityPrize.SubmissionLower.U9. -/
section PackedLegacy_U9
section ProximityFlatProofPort
open TensorProduct
namespace Algebra.TensorProduct
variable (R S A:Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
 [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {ι:Type*} (B:ι → Type*) [∀ i,Semiring (B i)] [∀ i,Algebra R (B i)]
@[simp]
lemma piRightHom_one:piRightHom R S A B 1=1:=rfl
variable {R S A B} in
@[simp]
lemma piRightHom_mul (x y:A ⊗[R] ∀ i,B i):
   piRightHom R S A B (x*y)=piRightHom R S A B x*piRightHom R S A B y:=by
 induction x
 · simp
 · induction y
   · simp
   · ext j
     simp
   · simp_all [mul_add]
 · simp_all [add_mul]
def piRightHom:A ⊗[R] (∀ i,B i) →ₐ[S] ∀ i,A ⊗[R] B i:=
 AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)
variable [Fintype ι] [DecidableEq ι]
def piRight:A ⊗[R] (∀ i,B i) ≃ₐ[S] ∀ i,A ⊗[R] B i:=
 AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)
@[simp]
lemma piRight_tmul (x:A) (f:∀ i,B i):
   piRight R S A B (x ⊗ₜ f)=(fun j↦x ⊗ₜ f j):=rfl
variable (ι) in
def piScalarRight:A ⊗[R] (ι → R) ≃ₐ[S] ι → A:=
 (piRight R S A (fun _:ι↦R)).trans <|
   AlgEquiv.piCongrRight (fun _↦Algebra.TensorProduct.rid R S A)
lemma piScalarRight_tmul (x:A) (y:ι → R):
   piScalarRight R S A ι (x ⊗ₜ y)=fun i↦y i • x:=
 rfl
@[simp]
lemma piScalarRight_tmul_apply (x:A) (y:ι → R) (i:ι):
   piScalarRight R S A ι (x ⊗ₜ y) i=y i • x:=
 rfl
section
variable (B C:Type*) [Semiring B] [Semiring C] [Algebra R B] [Algebra R C]
nonrec def prodRight:A ⊗[R] (B × C) ≃ₐ[S] A ⊗[R] B × A ⊗[R] C:=
 AlgEquiv.ofLinearEquiv (TensorProduct.prodRight R S A B C)
   (by simp [Algebra.TensorProduct.one_def])
   (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _↦by simp))
lemma prodRight_tmul (a:A) (x:B × C):prodRight R S A B C (a ⊗ₜ x)=(a ⊗ₜ x.1,a ⊗ₜ x.2):=
 rfl
@[simp]
lemma prodRight_tmul_fst (a:A) (x:B × C):(prodRight R S A B C (a ⊗ₜ x)).fst=a ⊗ₜ x.1:=
 rfl
@[simp]
lemma prodRight_tmul_snd (a:A) (x:B × C):(prodRight R S A B C (a ⊗ₜ x)).snd=a ⊗ₜ x.2:=
 rfl
@[simp]
lemma prodRight_symm_tmul (a:A) (b:B) (c:C):
   (prodRight R S A B C).symm (a ⊗ₜ b,a ⊗ₜ c)=a ⊗ₜ (b,c):=by
 apply (prodRight R S A B C).injective
 simp [prodRight_tmul]
end
end Algebra.TensorProduct
theorem TensorProduct.piScalarRight_symm_algebraMap
   (R:Type*) [CommSemiring R] (S:Type*) [CommSemiring S] [Algebra R S]
   (ι:Type*) [Fintype ι] [DecidableEq ι]
   {N:Type*} [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N]
   (x:ι → R):
   (TensorProduct.piScalarRight R S N ι).symm (algebraMap _ _ x)=1 ⊗ₜ[R] x:=by
 simp [Algebra.algebraMap_eq_smul_one,Pi.smul_def',LinearEquiv.symm_apply_eq,
   piScalarRight_apply,piScalarRightHom_tmul]
end ProximityFlatProofPort
end PackedLegacy_U9

/-! Packed from ProximityPrize.SubmissionLower.F5. -/
section PackedLegacy_F5
section ProximityFlatProofPort
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
open TensorProduct
attribute [-instance] Module.Free.instFaithfulSMulOfNontrivial Algebra.IsIntegral.isLocalHom
namespace Algebra
variable (R S) in
@[mk_iff,stacks 00PL]
class QuasiFinite:Prop where
 finite_fiber (P:Ideal R) [P.IsPrime]:
   Module.Finite P.ResidueField (P.Fiber S):=by infer_instance
attribute [stacks 00PM] quasiFinite_iff
namespace QuasiFinite
attribute [instance] finite_fiber
instance [QuasiFinite R S] (P:Ideal R) [P.IsPrime]:IsArtinianRing (P.Fiber S):=
 .of_finite P.ResidueField _
lemma finite_comap_preimage_singleton [QuasiFinite R S] (P:PrimeSpectrum R):
   (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite:=
 (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete
lemma finite_primesOver [QuasiFinite R S] (I:Ideal R):(I.primesOver S).Finite:=by
 by_cases h:I.IsPrime
 · refine ((finite_comap_preimage_singleton ⟨I,h⟩).image PrimeSpectrum.asIdeal).subset ?_
   exact fun J hJ↦⟨⟨_,hJ.1⟩,PrimeSpectrum.ext hJ.2.1.symm,rfl⟩
 · convert! Set.finite_empty
   by_contra!
   obtain ⟨J,h₁,⟨rfl⟩⟩:=this
   exact h inferInstance
lemma finite_comap_preimage [QuasiFinite R S] {s:Set (PrimeSpectrum R)} (hs:s.Finite):
   (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite:=
 hs.preimage' fun _ _↦finite_comap_preimage_singleton _
lemma isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P:PrimeSpectrum R):
   IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}):=
 ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩
lemma isDiscrete_comap_preimage [QuasiFinite R S] {s:Set (PrimeSpectrum R)}
   (hs:IsDiscrete s):
   IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s):=
 hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
   fun _↦isDiscrete_comap_preimage_singleton _
instance (priority:=low) [Module.Finite R S]:QuasiFinite R S where
@[stacks 00PP "(3)"]
instance baseChange [QuasiFinite R S] {A:Type*} [CommRing A] [Algebra R A]:
   QuasiFinite A (A ⊗[R] S):=by
 refine ⟨fun P hP↦?_⟩
 let p:=P.under R
 let:=Localization.AtPrime.algebraOfLiesOver p P
 let e:P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S):=
   (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
     (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
 exact .of_surjective e.symm.toLinearMap e.symm.surjective
open IsLocalRing in
private lemma finite_of_isArtinianRing_of_isLocalRing
   [QuasiFinite R S] [IsArtinianRing R] [IsLocalRing R]:Module.Finite R S:=by
 let e:(maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S):=
   (Algebra.TensorProduct.congr (.symm <| .ofBijective _
     (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
   (Algebra.TensorProduct.comm _ _ _).trans
   ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
 have:Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)):=
   have:Module.Finite R ((maximalIdeal R).Fiber S):=
     .trans (maximalIdeal R).ResidueField _
   .of_surjective e.toLinearMap e.surjective
 refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
   ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
 · refine Ideal.mk_ker.trans_le ?_
   rw [Ideal.map_le_iff_le_comap, ←Ring.KrullDimLE.nilradical_eq_maximalIdeal]
   exact fun x hx↦IsNilpotent.map hx _
 · rw [←RingHom.ker_coe_toRingHom,Ideal.Quotient.mkₐ_ker]
   exact Ideal.FG.map (IsNoetherian.noetherian _) _
lemma _root_.Module.Finite.of_quasiFinite [IsArtinianRing R] [QuasiFinite R S]:
   Module.Finite R S:=by
 classical
 let e:R ≃ₐ[R] PrimeSpectrum.PiLocalization R:=
   .ofBijective (IsScalarTower.toAlgHom _ _ _)
     (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
 have:Fintype (PrimeSpectrum R):=.ofFinite _
 let e':S ≃ₐ[R] Π p:PrimeSpectrum R,Localization p.asIdeal.primeCompl ⊗[R] S:=
   (Algebra.TensorProduct.rid R R S).symm.trans <| (Algebra.TensorProduct.congr .refl e).trans <|
     (Algebra.TensorProduct.piRight _ _ _ _).trans <| AlgEquiv.piCongrRight
     fun _↦Algebra.TensorProduct.comm _ _ _
 have (p:PrimeSpectrum R):Module.Finite R (Localization p.asIdeal.primeCompl ⊗[R] S):=
   have:Module.Finite R (Localization.AtPrime p.asIdeal):=
     .of_surjective (Algebra.linearMap _ _)
       (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
   have:Module.Finite (Localization.AtPrime p.asIdeal)
     (Localization.AtPrime p.asIdeal ⊗[R] S):=finite_of_isArtinianRing_of_isLocalRing
   .trans (Localization.AtPrime p.asIdeal) _
 exact .of_surjective e'.symm.toLinearMap e'.symm.surjective
lemma iff_of_isArtinianRing [IsArtinianRing R]:
   QuasiFinite R S ↔ Module.Finite R S:=
 ⟨fun _↦.of_quasiFinite,fun _↦inferInstance⟩
attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
@[stacks 00PO]
lemma «trans» [QuasiFinite R S] [QuasiFinite S T]:QuasiFinite R T:=by
 refine ⟨fun P hP↦?_⟩
 have:Module.Finite (P.Fiber S) ((P.Fiber S) ⊗[S] T):=
   (iff_of_isArtinianRing (R:=P.Fiber S) (S:=(P.Fiber S) ⊗[S] T)).mp inferInstance
 have:Module.Finite P.ResidueField ((P.Fiber S) ⊗[S] T):=
   .trans (P.Fiber S) _
 let e:P.Fiber S ≃ₐ[S] S ⊗[R] P.ResidueField:=
   { __:=Algebra.TensorProduct.comm _ _ _,commutes' _:=rfl}
 let e':(P.Fiber S) ⊗[S] T ≃ₐ[R] P.Fiber T:=
   ((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans <|
   ((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans <|
   ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
   (Algebra.TensorProduct.comm _ _ _)
 let e'':(P.Fiber S) ⊗[S] T ≃ₐ[P.ResidueField] P.Fiber T:=
   { __:=e',commutes' _:=by simp [e',e]}
 exact .of_surjective e''.toLinearMap e''.surjective
omit [Algebra S T] in
lemma of_surjective_algHom [QuasiFinite R S] (f:S →ₐ[R] T) (hf:Function.Surjective f):
   QuasiFinite R T:=
 let:=f.toRingHom.toAlgebra
 let:=IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
 have:Module.Finite S T:=.of_surjective (Algebra.linearMap _ _) hf
 Algebra.QuasiFinite.trans R S T
instance (I:Ideal S) [QuasiFinite R S]:QuasiFinite R (S ⧸ I):=
 of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective
omit [Algebra S T] in
lemma iff_of_algEquiv (e:S ≃ₐ[R] T):
   Algebra.QuasiFinite R S ↔ Algebra.QuasiFinite R T:=
 ⟨fun _↦.of_surjective_algHom e.toAlgHom e.surjective,
   fun _↦.of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩
lemma of_isLocalization (M:Submonoid S) [IsLocalization M T] [QuasiFinite R S]:
   QuasiFinite R T:=
 letI:QuasiFinite S T:=by
   refine ⟨fun P hP↦.of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
   letI:DecidableEq P.ResidueField:=Classical.decEq P.ResidueField
   rw [←LinearMap.coe_restrictScalars (R:=S), ←LinearMap.range_eq_top,
     ←top_le_iff, ←TensorProduct.span_tmul_eq_top,Submodule.span_le]
   rintro _ ⟨p,s,rfl⟩
   obtain ⟨s,t,rfl⟩:=IsLocalization.exists_mk'_eq M s
   use s • p/algebraMap _ _ t.1
   apply ((IsLocalization.map_units T t).map
     Algebra.TensorProduct.includeRight).mul_left_injective
   by_cases ht:algebraMap _ P.ResidueField t.1=0
   · simp [ht]
   trans (s • p) ⊗ₜ[S] 1
   · simp [div_mul_cancel₀ _ ht]
   · dsimp;simp [Algebra.algebraMap_eq_smul_one,smul_tmul]
 Algebra.QuasiFinite.trans R S T
instance (M:Submonoid S) [QuasiFinite R S]:QuasiFinite R (Localization M):=of_isLocalization M
instance (priority:=low) [IsFractionRing R S]:QuasiFinite R S:=
 of_isLocalization (nonZeroDivisors R)
instance [QuasiFinite R S] (p:Ideal R) [p.IsPrime] (q:Ideal (p.Fiber S)) [q.IsPrime]:
   Module.Finite p.ResidueField (Localization.AtPrime q):=
 Module.Finite.of_quasiFinite (R:=p.ResidueField) (S:=Localization.AtPrime q)
instance (P:Ideal S) [P.IsPrime] [QuasiFinite R S]:QuasiFinite R P.ResidueField:=
 .trans _ (S ⧸ P) _
variable (R S T) in
lemma of_restrictScalars [QuasiFinite R T]:QuasiFinite S T:=by
 refine ⟨fun P hP↦?_⟩
 let f:P.ResidueField ⊗[R] T →ₐ[P.ResidueField] P.Fiber T:=
   Algebra.TensorProduct.lift (Algebra.ofId _ _)
     (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _↦.all _ _
 have hf:Function.Surjective f:=by
   rw [←AlgHom.coe_restrictScalars' (R:=S), ←AlgHom.coe_toLinearMap, ←LinearMap.range_eq_top,
     ←top_le_iff, ←TensorProduct.span_tmul_eq_top,Submodule.span_le]
   rintro _ ⟨a,b,rfl⟩
   exact ⟨a ⊗ₜ b,by simp [f]⟩
 have:Module.Finite P.ResidueField (P.ResidueField ⊗[R] T):=.of_quasiFinite
 exact .of_surjective f.toLinearMap hf
variable (R S) in
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S]:
   DiscreteTopology (PrimeSpectrum S):=
 isDiscrete_univ_iff.mp
   (isDiscrete_comap_preimage (R:=R) (S:=S) (isDiscrete_univ_iff.mpr ‹_›))
variable (R S) in
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S]:
   Finite (PrimeSpectrum S):=
 Set.finite_univ_iff.mp
   (finite_comap_preimage (Set.finite_univ (α:=PrimeSpectrum R)))
omit [Algebra S T] in
lemma of_forall_exists_mul_mem_range [QuasiFinite R S] (f:S →ₐ[R] T)
   (H:∀ x:T,∃ s:S,IsUnit (f s)∧x*f s∈f.range):
   QuasiFinite R T:=by
 let φ:Localization ((IsUnit.submonoid T).comap f) →ₐ[R] T:=
   IsLocalization.liftAlgHom (M:=(IsUnit.submonoid T).comap f) (f:=f)
     (by simp [IsUnit.mem_submonoid_iff])
 suffices Function.Surjective φ from .of_surjective_algHom φ this
 intro x
 obtain ⟨s,hs,t,ht⟩:=H x
 refine ⟨IsLocalization.mk' (M:=(IsUnit.submonoid T).comap f) _ t ⟨s,hs⟩,?_⟩
 simpa [φ,IsLocalization.lift_mk',Units.mul_inv_eq_iff_eq_mul,IsUnit.coe_liftRight]
omit [Algebra S T] in
lemma eq_of_le_of_under_eq [QuasiFinite R S] (P Q:Ideal S) [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) (h₂:P.under R=Q.under R):P=Q:=
 congr($((isDiscrete_comap_preimage_singleton ⟨_,inferInstance⟩).eq_of_specializes
   (a:=⟨P,‹_›⟩) (b:=⟨Q,‹_›⟩) (by simpa [←PrimeSpectrum.le_iff_specializes]) rfl
   (PrimeSpectrum.ext h₂.symm)).1)
instance [QuasiFinite R S] (P:Ideal R) [P.IsPrime] (Q:Ideal S) [Q.IsPrime] [Q.LiesOver P]
   [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
   [Localization.AtPrime.IsLiesOverAlgebra P Q]:
   Module.Finite P.ResidueField Q.ResidueField:=
 have:QuasiFinite P.ResidueField Q.ResidueField:=.of_restrictScalars R _ _
 .of_quasiFinite
section Finite
lemma iff_finite_comap_preimage_singleton [FiniteType R S]:
   QuasiFinite R S ↔ ∀ x,(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite:=by
 refine ⟨fun H _↦finite_comap_preimage_singleton _,fun H↦⟨fun P _↦?_⟩⟩
 rw [Module.finite_iff_isArtinianRing,isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
 have:IsJacobsonRing (P.Fiber S):=isJacobsonRing_of_finiteType (A:=P.ResidueField)
 have:Finite (PrimeSpectrum (P.Fiber S)):=
   (PrimeSpectrum.preimageEquivFiber R S ⟨P,‹_›⟩).finite_iff.mp (H ⟨P,‹_›⟩)
 exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
   (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩
lemma iff_finite_primesOver [FiniteType R S]:
   QuasiFinite R S ↔ ∀ I:Ideal R,I.IsPrime → (I.primesOver S).Finite:=by
 rw [iff_finite_comap_preimage_singleton,
   (PrimeSpectrum.equivSubtype R).forall_congr_left,Subtype.forall]
 refine forall₂_congr fun I hI↦?_
 rw [←Set.finite_image_iff (Function.Injective.injOn fun _ _↦PrimeSpectrum.ext)]
 congr!
 ext J
 simp [(PrimeSpectrum.equivSubtype S).exists_congr_left,PrimeSpectrum.ext_iff,eq_comm,
   PrimeSpectrum.equivSubtype,Ideal.primesOver,and_comm,Ideal.liesOver_iff,Ideal.under]
lemma of_isIntegral_of_finiteType [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
   (s:S) [IsLocalization.Away s T]:Algebra.QuasiFinite R T:=by
 let A:=Algebra.adjoin R {s}
 let sA:A:=⟨s,Algebra.subset_adjoin (by simp)⟩
 let f:Localization.Away sA →+*T:=IsLocalization.Away.lift sA (g:=algebraMap _ _)
   (IsLocalization.Away.algebraMap_isUnit s)
 let:=f.toAlgebra
 let:Algebra A (Localization.Away sA):=OreLocalization.instAlgebra
 let:SMul A (Localization.Away sA):=Algebra.toSMul
 let:MulAction A (Localization.Away sA):=Algebra.toModule.toDistribMulAction.toMulAction
 have:IsScalarTower R A (Localization.Away sA):=OreLocalization.instIsScalarTower
 have:IsScalarTower A (Localization.Away sA) T:=
   .of_algebraMap_eq (by simp [f,RingHom.algebraMap_toAlgebra,A])
 have:IsScalarTower R (Localization.Away sA) T:=.to₁₃₄ R A (Localization.Away sA) T
 have:Algebra.IsIntegral (Localization.Away sA) T:=by
   refine ⟨fun x↦?_⟩
   obtain ⟨x,⟨_,n,rfl⟩,rfl⟩:=IsLocalization.exists_mk'_eq (.powers s) x
   have:_root_.IsIntegral (Localization.Away sA) (algebraMap S T x):=
     (Algebra.IsIntegral.isIntegral (R:=R) x).algebraMap.tower_top
   convert! this.smul (Localization.Away.invSelf sA^n)
   rw [IsLocalization.mk'_eq_iff_eq_mul]
   simp only [map_pow,Algebra.smul_mul_assoc]
   trans (sA • Localization.Away.invSelf sA)^n • (algebraMap S T x)
   · simp [Algebra.smul_def, -map_pow,Localization.Away.invSelf,Localization.mk_eq_mk']
   · simp only [Algebra.smul_def,map_pow,map_mul,mul_pow,
       ←IsScalarTower.algebraMap_apply,Subalgebra.algebraMap_def,sA]
     ring
 have:Module.Finite (Localization.Away sA) T:=
   have:Algebra.FiniteType (Localization.Away sA) T:=.of_restrictScalars_finiteType R _ _
   Algebra.IsIntegral.finite
 have:Module.Finite R A:=
   Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
 have:Algebra.QuasiFinite R (Localization.Away sA):=.of_isLocalization (.powers sA)
 exact .trans _ (Localization.Away sA) _
end Finite
end QuasiFinite
section QuasiFiniteAt
variable (R) in
abbrev QuasiFiniteAt (p:Ideal S) [p.IsPrime]:Prop:=
 QuasiFinite R (Localization.AtPrime p)
lemma QuasiFiniteAt.baseChange (p:Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
   {A:Type*} [CommRing A] [Algebra R A] (q:Ideal (A ⊗[R] S)) [q.IsPrime]
   (hq:p=q.comap Algebra.TensorProduct.includeRight.toRingHom):
   QuasiFiniteAt A q:=by
 let f:A ⊗[R] Localization.AtPrime p →ₐ[A] Localization.AtPrime q:=
   Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq,by
     simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
       IsScalarTower.algebraMap_apply R (A ⊗[R] S) (Localization.AtPrime q)]⟩ fun _ _↦.all _ _
 let g:A ⊗[R] S →ₐ[A] A ⊗[R] Localization.AtPrime p:=
   Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
 have:f.comp g=IsScalarTower.toAlgHom _ _ _:=by ext;simp [f,g]
 replace this (x:_):f (g x)=algebraMap _ _ x:=DFunLike.congr_fun this x
 refine .of_forall_exists_mul_mem_range f fun x↦?_
 obtain ⟨x,⟨s,hs⟩,rfl⟩:=IsLocalization.exists_mk'_eq q.primeCompl x
 refine ⟨g s,this s ▸ IsLocalization.map_units _ ⟨s,hs⟩,?_⟩
 rw [this,IsLocalization.mk'_spec_mk]
 exact ⟨g x,this x⟩
set_option backward.isDefEq.respectTransparency false in
omit [Algebra S T] in
lemma QuasiFiniteAt.of_surjectiveOnStalks (p:Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
   (f:S →ₐ[R] T) (hf:f.SurjectiveOnStalks) (q:Ideal T) [q.IsPrime]
   (hq:p=q.comap f.toRingHom):
   QuasiFiniteAt R q:=by
 subst hq
 refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl,?_⟩ (hf q ‹_›)
 simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
   IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]
lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver (p:Ideal S) [p.IsPrime]
   [QuasiFiniteAt R p] (hf:(algebraMap S T).SurjectiveOnStalks) (q:Ideal T) [q.IsPrime]
   [q.LiesOver p]:QuasiFiniteAt R q:=
 .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)
instance QuasiFiniteAt.comap_algEquiv (p:Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
   (f:T ≃ₐ[R] S):QuasiFiniteAt R (p.comap f.toRingHom):=
 .of_surjectiveOnStalks p f.symm.toAlgHom
   (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext;simp)
omit [Algebra S T] in
lemma QuasiFiniteAt.of_le {P Q:Ideal S} [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) [QuasiFiniteAt R Q]:
   QuasiFiniteAt R P:=by
 let f:Localization.AtPrime Q →ₐ[R] Localization.AtPrime P:=
   IsLocalization.liftAlgHom (M:=Q.primeCompl) (f:=IsScalarTower.toAlgHom _ _ _) <| by
     simp only [IsScalarTower.coe_toAlgHom',Subtype.forall,Ideal.mem_primeCompl_iff]
     exact fun a ha↦IsLocalization.map_units (M:=P.primeCompl) _ ⟨a,fun h↦ha (h₁ h)⟩
 refine .of_forall_exists_mul_mem_range f fun x↦?_
 obtain ⟨x,⟨s,hs⟩,rfl⟩:=IsLocalization.exists_mk'_eq P.primeCompl x
 exact ⟨algebraMap _ _ s,by simpa [f] using IsLocalization.map_units _ ⟨s,hs⟩,
   algebraMap _ _ x,by simp [f]⟩
omit [Algebra S T] in
lemma QuasiFiniteAt.eq_of_le_of_under_eq {P Q:Ideal S} [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) (h₂:P.under R=Q.under R) [QuasiFiniteAt R Q]:
   P=Q:=by
 have:=Q.isPrime_map_of_isLocalizationAtPrime h₁ (S:=Localization.AtPrime Q)
 have H:=QuasiFinite.eq_of_le_of_under_eq (R:=R)
   (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
   (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
     convert! h₂ <;> rw [←Ideal.under_under (B:=S)]
     · rw [Q.under_map_of_isLocalizationAtPrime h₁]
     · rw [Localization.AtPrime.under_maximalIdeal])
 rw [←Localization.AtPrime.under_maximalIdeal (I:=Q), ←H,
   Q.under_map_of_isLocalizationAtPrime h₁]
instance (p:Ideal R) [p.IsPrime] (P:Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
   [Localization.AtPrime.IsLiesOverAlgebra p P]:
   Module.Finite p.ResidueField P.ResidueField:=by
 let m:=IsLocalRing.maximalIdeal (Localization.AtPrime P)
 let:m.LiesOver p:=.trans _ P _
 let:=Localization.AtPrime.algebraOfLiesOver p m
 let:=Localization.AtPrime.algebraOfLiesOver P m
 let e:=AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
   m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
       P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
 exact .of_surjective e.symm.toLinearMap e.symm.surjective
set_option backward.defeqAttrib.useBackward true in
lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
   (p:Ideal S) [p.IsPrime] [IsArtinianRing R] [Algebra.EssFiniteType R S]
   [Algebra.QuasiFiniteAt R p]:
   ∃ f∉p,(PrimeSpectrum.basicOpen f:Set (PrimeSpectrum S))={⟨p,‹_›⟩}:=by
 have:IsLocalizedModule p.primeCompl (.id (R:=S) (M:=Localization.AtPrime p)):=
   ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
     fun y↦⟨⟨y,1⟩,by simp⟩,by simpa using ⟨1,p.primeCompl.one_mem⟩⟩
 have:Module.Finite R (Localization.AtPrime p):=.of_quasiFinite
 have:Module.Finite S (Localization.AtPrime p):=.of_restrictScalars_finite R _ _
 have:IsArtinianRing (Localization.AtPrime p):=.of_finite R _
 have:IsNoetherianRing S:=Algebra.EssFiniteType.isNoetherianRing R S
 have:Module.FinitePresentation S (Localization.AtPrime p):=
   Module.finitePresentation_of_finite _ _
 obtain ⟨r,hrp,H⟩:=IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
   p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
 have:IsLocalization (.powers r) (Localization.AtPrime p):=
   (isLocalizedModule_iff_isLocalization' _ _).mp H
 let φ:Localization.Away r ≃ₐ[S] Localization.AtPrime p:=
   IsLocalization.algEquiv (.powers r) _ _
 refine ⟨r,hrp,subset_antisymm (fun q hrq↦?_) (Set.singleton_subset_iff.mpr hrp)⟩
 obtain ⟨q,rfl⟩:=(PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
 obtain ⟨q,rfl⟩:=(PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
 obtain rfl:q=IsLocalRing.closedPoint _:=Subsingleton.elim _ _
 ext1
 dsimp [-RingEquiv.symm_mk]
 rw [Ideal.comap_comap, ←AlgEquiv.toAlgHom_toRingHom,AlgHom.comp_algebraMap]
 exact IsLocalization.AtPrime.under_maximalIdeal _ _
lemma QuasiFiniteAt.isClopen_singleton
   (p:PrimeSpectrum S) [IsArtinianRing R] [Algebra.FiniteType R S]
   [Algebra.QuasiFiniteAt R p.asIdeal]:IsClopen {p}:=by
 have:IsJacobsonRing S:=isJacobsonRing_of_finiteType (A:=R)
 have:IsNoetherianRing S:=Algebra.FiniteType.isNoetherianRing R S
 refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
 obtain ⟨f,hf,e⟩:=exists_basicOpen_eq_singleton (R:=R) p.asIdeal
 exact e ▸ (PrimeSpectrum.basicOpen f).isOpen
lemma QuasiFiniteAt.of_isOpen_singleton
   [IsArtinianRing R] (p:PrimeSpectrum S) [Algebra.FiniteType R S]
   (H:IsOpen {p}):Algebra.QuasiFiniteAt R p.asIdeal:=by
 have:IsNoetherianRing S:=Algebra.FiniteType.isNoetherianRing R S
 have:IsJacobsonRing S:=isJacobsonRing_of_finiteType (A:=R)
 rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out
   0 1 rfl rfl] at H
 obtain ⟨e,he,H⟩:=PrimeSpectrum.isClopen_iff.mp H
 have hep:e∉p.asIdeal:=H.le rfl
 let f:Localization.Away e →ₐ[S] Localization.AtPrime p.asIdeal:=
   IsLocalization.Away.liftAlgHom e (f:=Algebra.ofId _ _)
     (IsLocalization.map_units (M:=p.asIdeal.primeCompl) _ ⟨e,hep⟩)
 have h₁:=(PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).trans H.symm
 have:Subsingleton (PrimeSpectrum (Localization.Away e)):=
   Function.Injective.subsingleton
   (f:=Set.codRestrict (PrimeSpectrum.comap (algebraMap S (Localization.Away e))) {p} fun x↦
     h₁.le ⟨x,rfl⟩)
   ((Set.injective_codRestrict ..).mpr (PrimeSpectrum.localization_comap_injective _ (.powers e)))
 have hf:Function.Surjective f:=by
   intro x
   obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
   suffices IsUnit (algebraMap _ (Localization.Away e) s.1) by
     refine ⟨algebraMap _ _ x*this.unit⁻¹,(this.map f).mul_right_cancel ?_⟩
     simp only [←map_mul,mul_assoc,IsUnit.val_inv_mul]
     simp
   by_contra H
   obtain ⟨M,hM,H⟩:=
     Ideal.exists_le_maximal (.span {algebraMap _ (Localization.Away e) s.1}) (by simpa)
   have:=Subsingleton.elim ((IsLocalRing.closedPoint _).comap f.toRingHom) ⟨M,inferInstance⟩
   have:=congr(($this).1).ge (H (Ideal.mem_span_singleton_self _))
   simp [IsLocalRing.closedPoint,IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal] at this
 have:Algebra.FiniteType R (Localization.AtPrime p.asIdeal):=
   .of_surjective (f.restrictScalars R) hf
 have:=(PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).subsingleton
 exact QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _↦
   Set.subsingleton_of_subsingleton.finite
attribute [local instance] RingHom.ker_isPrime in
lemma _root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
   (p:Ideal R) [p.IsPrime] (q:Ideal S) [q.IsPrime] [q.LiesOver p]
   [Algebra.EssFiniteType R S] [Algebra.QuasiFiniteAt R q]:
   ∃ s∉q,∀ q':Ideal S,q'.IsPrime → q'≠q → q'.LiesOver p → s∈q':=by
 classical
 let e:=PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p,inferInstance⟩
 let qF:PrimeSpectrum (p.Fiber S):=e ⟨⟨q,‹_›⟩,PrimeSpectrum.ext (q.over_def p).symm⟩
 have:Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal:=.baseChange q _
   congr($(e.symm_apply_apply ⟨⟨q,‹_›⟩,PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
 obtain ⟨r,hr,hrq⟩:=Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
   (R:=p.ResidueField) qF.asIdeal
 obtain ⟨s,hs,x,hsx⟩:=Ideal.Fiber.exists_smul_eq_one_tmul _ r
 have:x∉q:=by
   have:r∉_:=hrq.ge rfl
   simp only [PrimeSpectrum.preimageHomeomorphFiber,PrimeSpectrum.preimageOrderIsoFiber,
     Homeomorph.homeomorph_mk_coe,qF,e] at this
   rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
       ←Ideal.IsPrime.mul_mem_left_iff (x:=algebraMap _ _ s), ←Algebra.smul_def,hsx] at this
   · simpa using this
   · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField,q.over_def p] using hs
 refine ⟨x,this,fun q' _ hq' _↦not_not.mp fun hxq'↦hq' ?_⟩
 refine congr($(e.injective (a₁ :=⟨⟨q',‹_›⟩,PrimeSpectrum.ext (q'.over_def p).symm⟩)
   (a₂:=⟨⟨q,‹_›⟩,PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
 simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl,PrimeSpectrum.preimageHomeomorphFiber,
   PrimeSpectrum.preimageOrderIsoFiber,Homeomorph.homeomorph_mk_coe,Set.mem_compl_iff,
   PrimeSpectrum.mem_zeroLocus,Set.singleton_subset_iff,SetLike.mem_coe,e]
 rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
   ←Ideal.IsPrime.mul_mem_left_iff (x:=algebraMap _ _ s), ←Algebra.smul_def,hsx]
 · simpa
 · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ←Ideal.mem_comap, ←q'.over_def p]
lemma _root_.Ideal.Fiber.lift_residueField_surjective [Algebra.FiniteType R S]
   (p:Ideal R) [p.IsPrime] (q:Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra p q]:
   Function.Surjective (Algebra.TensorProduct.lift (Algebra.ofId _ _)
     (IsScalarTower.toAlgHom _ _ _) fun _ _↦.all _ _:
     p.Fiber S →ₐ[p.ResidueField] q.ResidueField):=by
 let q':Ideal (p.Fiber S):=(PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q,‹_›,‹_›⟩).asIdeal
 have hq':q=q'.comap Algebra.TensorProduct.includeRight.toRingHom:=
   congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q,‹_›,‹_›⟩).1).symm
 have:Algebra.QuasiFiniteAt p.ResidueField q':=.baseChange q _ hq'
 have:q'.IsMaximal:=(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
   (QuasiFiniteAt.isClopen_singleton (R:=p.ResidueField) _).isClosed
 refine .of_comp_left ?_
   (p.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q q' hq').1
 rw [←AlgHom.coe_toRingHom, ←RingHom.coe_comp]
 convert! q'.algebraMap_residueField_surjective
 ext <;> simp [IsScalarTower.algebraMap_apply R S q.ResidueField]
end QuasiFiniteAt
end Algebra
end ProximityFlatProofPort
end PackedLegacy_F5

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier01 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.F7. -/
section PackedLegacy_F7
section ProximityFlatProofPort
namespace Ideal
section
variable {S:Type*} [CommRing S] (q:Ideal S) (R:Type*) [CommRing R] [Algebra R S]
open scoped Classical in
noncomputable def inertiaDeg:ℕ:=
 if _:q.IsPrime then
   letI:=Localization.AtPrime.algebraOfLiesOver (q.under R) q
   Module.finrank (q.under R).ResidueField q.ResidueField else 0
theorem inertiaDeg_def [hq:q.IsPrime]
   [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q]:
   q.inertiaDeg R=Module.finrank (q.under R).ResidueField q.ResidueField:=by
 convert! dif_pos hq
 simp [Algebra.algebra_ext_iff,Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_def:=inertiaDeg_def
theorem inertiaDeg_of_not_isPrime (hq:¬ q.IsPrime):q.inertiaDeg R=0:=
 dif_neg hq
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_of_not_isPrime:=
 inertiaDeg_of_not_isPrime
theorem inertiaDeg_pos [hq:q.IsPrime] [Module.Finite R S]:0 < q.inertiaDeg R:=by
 let:=Localization.AtPrime.algebraOfLiesOver (q.under R) q
 rw [inertiaDeg_def]
 apply Module.finrank_pos
end
section
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
 (p:Ideal R) (q:Ideal S) (r:Ideal T)
theorem inertiaDeg_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra p q]:
   q.inertiaDeg R=Module.finrank p.ResidueField q.ResidueField:=by
 have:=Ideal.over_def q p
 subst this
 exact inertiaDeg_def q R
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_eq:=inertiaDeg_eq
theorem inertiaDeg_eq_of_isFractionRing [q.LiesOver p] [p.IsPrime] [q.IsPrime]
   (K L:Type*) [Field K] [Field L]
   [Algebra (R ⧸ p) K] [IsFractionRing (R ⧸ p) K]
   [Algebra (S ⧸ q) L] [IsFractionRing (S ⧸ q) L]
   [Algebra R K] [IsScalarTower R (R ⧸ p) K]
   [Algebra S L] [IsScalarTower S (S ⧸ q) L]
   [Algebra R L] [IsScalarTower R S L]
   [Algebra K L] [IsScalarTower R K L]:
   q.inertiaDeg R=Module.finrank K L:=by
 let:=Localization.AtPrime.algebraOfLiesOver p q
 rw [inertiaDeg_eq p q]
 apply Algebra.finrank_eq_of_equiv_equiv
   (IsFractionRing.algEquivOfAlgEquiv (R:=R) (A:=R ⧸ p) (K:=p.ResidueField) (L:=K) .refl)
   (IsFractionRing.algEquivOfAlgEquiv (R:=S) (A:=S ⧸ q) (K:=q.ResidueField) (L:=L) .refl)
 apply IsFractionRing.ringHom_ext (A:=R ⧸ p)
 intro x
 obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective x
 simp [←IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField,
   IsScalarTower.algebraMap_apply R S q.ResidueField,
   ←IsScalarTower.algebraMap_apply R K L, ←IsScalarTower.algebraMap_apply R S L]
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_eq_of_isFractionRing:=
inertiaDeg_eq_of_isFractionRing
theorem inertiaDeg_eq_of_isMaximal [q.LiesOver p] [p.IsMaximal] [q.IsMaximal]:
   q.inertiaDeg R=Module.finrank (R ⧸ p) (S ⧸ q):=by
 let:Field (R ⧸ p):=Quotient.field p
 let:Field (S ⧸ q):=Quotient.field q
 exact inertiaDeg_eq_of_isFractionRing p q (R ⧸ p) (S ⧸ q)
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_eq_of_isMaximal:=
 inertiaDeg_eq_of_isMaximal
theorem inertiaDeg'_eq_inertiaDeg [q.LiesOver p] [p.IsMaximal] [q.IsMaximal]:
   p.inertiaDeg' q=q.inertiaDeg R:=by
 rw [inertiaDeg'_algebraMap,inertiaDeg_eq_of_isMaximal p q]
@[deprecated (since:="2026-07-03")] alias inertiaDeg_eq_inertiaDeg':=inertiaDeg'_eq_inertiaDeg
theorem inertiaDeg_tower [r.LiesOver q]:
   r.inertiaDeg R=q.inertiaDeg R*r.inertiaDeg S:=by
 by_cases hr:r.IsPrime
 · have:q.IsPrime:=isPrime_of_liesOver r q
   have:q.LiesOver (r.under R):=LiesOver.tower_bot r q (r.under R)
   let:=Localization.AtPrime.algebraOfLiesOver (r.under R) r
   let:=Localization.AtPrime.algebraOfLiesOver (r.under R) q
   let:=Localization.AtPrime.algebraOfLiesOver q r
   rw [inertiaDeg_def,inertiaDeg_eq (r.under R),inertiaDeg_eq q,eq_comm]
   apply Module.finrank_mul_finrank
 · rw [inertiaDeg_of_not_isPrime r R hr,inertiaDeg_of_not_isPrime r S hr,mul_zero]
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_tower:=inertiaDeg_tower
theorem inertiaDeg_below_dvd [r.LiesOver q]:
   q.inertiaDeg R∣r.inertiaDeg R:=by
 use r.inertiaDeg S
 rw [←inertiaDeg_tower]
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_below_dvd:=inertiaDeg_below_dvd
theorem inertiaDeg_above_dvd [r.LiesOver q]:
   r.inertiaDeg S∣r.inertiaDeg R:=by
 use q.inertiaDeg R
 rw [mul_comm, ←inertiaDeg_tower]
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_above_dvd:=inertiaDeg_above_dvd
theorem inertiaDeg_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T]:
   q.inertiaDeg R ≤ r.inertiaDeg R:=
 Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_below_dvd r)
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_below_le:=inertiaDeg_below_le
theorem inertiaDeg_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T]:
   r.inertiaDeg S ≤ r.inertiaDeg R:=
 Nat.le_of_dvd (r.inertiaDeg_pos R) (q.inertiaDeg_above_dvd r)
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_above_le:=inertiaDeg_above_le
variable (R) in
open Pointwise in
@[simp]
theorem inertiaDeg_smul {G:Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
   (g:G):(g • q).inertiaDeg R=q.inertiaDeg R:=by
 by_cases hq:q.IsPrime;swap
 · rw [inertiaDeg_of_not_isPrime,inertiaDeg_of_not_isPrime] <;> simpa
 · let p:=q.under R
   let f₀:=MulSemiringAction.toAlgAut G R S g
   let:=Localization.AtPrime.algebraOfLiesOver p q
   let:=Localization.AtPrime.algebraOfLiesOver p (g • q)
   rw [inertiaDeg_eq p q,inertiaDeg_eq p (g • q)]
   let e₂:=Ideal.residueFieldAlgEquiv' p (g • q) q f₀.symm (comap_symm f₀.toRingEquiv).symm
   exact e₂.toLinearEquiv.finrank_eq
@[deprecated (since:="2026-07-03")] alias inertiaDeg'_smul:=inertiaDeg_smul
theorem cardQuot_pow_inertiaDeg [Module.Finite R S] [p.IsMaximal] [q.IsMaximal] [q.LiesOver p]:
   p.cardQuot^q.inertiaDeg R=q.cardQuot:=by
 let _:Field (R ⧸ p):=Quotient.field p
 rw [←inertiaDeg'_eq_inertiaDeg p q,inertiaDeg'_algebraMap p q]
 exact Module.natCard_eq_pow_finrank.symm
@[deprecated (since:="2026-07-03")] alias cardQuot_pow_inertiaDeg':=cardQuot_pow_inertiaDeg
theorem absNorm_pow_inertiaDeg [Module.Finite R S] [q.IsPrime] [q.LiesOver p]
   [IsDedekindDomain R] [IsDedekindDomain S] [Module.Free ℤ R] [Module.Free ℤ S]:
   p.absNorm^q.inertiaDeg R=q.absNorm:=by
 by_cases hp:p=⊥
 · subst hp
   simpa [eq_bot_of_liesOver_bot R q] using (inertiaDeg_pos q R).ne'
 have:=isPrime_of_liesOver q p
 have:=isMaximal_of_isPrime_of_ne_bot p hp
 have:=IsMaximal.of_liesOver_isMaximal q p
 exact cardQuot_pow_inertiaDeg p q
@[deprecated (since:="2026-07-03")] alias absNorm_pow_inertiaDeg':=absNorm_pow_inertiaDeg
theorem natAbs_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p:ℤ)
   (P:Ideal R) [P.IsPrime] [P.LiesOver (span {p})]:
   p.natAbs^P.inertiaDeg ℤ=absNorm P:=by
 simpa using absNorm_pow_inertiaDeg (span {p}) P
@[deprecated (since:="2026-07-03")] alias natAbs_pow_inertiaDeg':=natAbs_pow_inertiaDeg
theorem pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] (p:ℕ)
   (P:Ideal R) [P.IsPrime] [P.LiesOver (span {(p:ℤ)})]:
   p^P.inertiaDeg ℤ=absNorm P:=
 natAbs_pow_inertiaDeg p P
end
end Ideal
end ProximityFlatProofPort
end PackedLegacy_F7

/-! Packed from ProximityPrize.SubmissionLower.JA. -/
section PackedLegacy_JA
namespace ProximityPrize.SubmissionLower.RCN373
open scoped Classical
noncomputable section
variable {K R S:Type*} [Field K] [CommRing R] [CommRing S]
 [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
 [Algebra.IsIntegral R S]
theorem pointFiber_quotient_integral (phi:R →ₐ[K] K) (P:Ideal S)
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   Algebra.IsIntegral K (S ⧸ P):=by
 have hcomp:(algebraMap K (S ⧸ P)).comp phi.toRingHom=
     (Ideal.Quotient.mk P).comp (algebraMap R S):=by
   ext r
   exact (RCN354.quotient_scalar_compatibility phi P hP r).symm
 constructor
 intro z
 obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective z
 exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk P) hcomp
   (Algebra.IsIntegral.isIntegral (R:=R) s)
variable [IsAlgClosed K]
theorem pointFiber_constants_surjective (phi:R →ₐ[K] K) (P:Ideal S)
   [P.IsMaximal]
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   Function.Surjective (algebraMap K (S ⧸ P)):=by
 letI:Algebra.IsIntegral K (S ⧸ P):=pointFiber_quotient_integral phi P hP
 exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S ⧸ P)).2
theorem inertiaDeg_eq_one_of_point_fiber (phi:R →ₐ[K] K) (P:Ideal S)
   [P.IsMaximal]
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   P.inertiaDeg R=1:=by
 let p:Ideal R:=RingHom.ker phi.toRingHom
 letI:p.IsMaximal:=RCN354.pointKernel_isMaximal phi
 letI:P.LiesOver p:=⟨hP.symm⟩
 letI:Field (R ⧸ p):=Ideal.Quotient.field p
 letI:Field (S ⧸ P):=Ideal.Quotient.field P
 have hsurj:Function.Surjective (algebraMap (R ⧸ p) (S ⧸ P)):=by
   intro z
   obtain ⟨c,hc⟩:=pointFiber_constants_surjective phi P hP z
   refine ⟨algebraMap K (R ⧸ p) c,?_⟩
   rw [←IsScalarTower.algebraMap_apply K (R ⧸ p) (S ⧸ P),hc]
 rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
 exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
   ⟨(algebraMap (R ⧸ p) (S ⧸ P)).injective,hsurj⟩
theorem inertiaDeg'_eq_one_of_point_fiber (phi:R →ₐ[K] K) (P:Ideal S)
   [P.IsMaximal]
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   (RingHom.ker phi.toRingHom).inertiaDeg' P=1:=by
 letI:(RingHom.ker phi.toRingHom).IsMaximal:=
   RCN354.pointKernel_isMaximal phi
 letI:P.LiesOver (RingHom.ker phi.toRingHom):=⟨hP.symm⟩
 rw [Ideal.inertiaDeg'_eq_inertiaDeg]
 exact inertiaDeg_eq_one_of_point_fiber phi P hP
end
end ProximityPrize.SubmissionLower.RCN373
end PackedLegacy_JA

/-! Packed from ProximityPrize.SubmissionLower.HV. -/
section PackedLegacy_HV
section ProximityFlatProofPort
noncomputable section
universe u
variable {K:Type u}
namespace RatFunc
section IntDegree
open Polynomial
variable [Field K]
def intDegree (x:K⟮X⟯):ℤ:=
 natDegree x.num-natDegree x.denom
@[simp]
theorem intDegree_zero:intDegree (0:K⟮X⟯)=0:=by
 rw [intDegree,num_zero,natDegree_zero,denom_zero,natDegree_one,sub_self]
@[simp]
theorem intDegree_one:intDegree (1:K⟮X⟯)=0:=by
 rw [intDegree,num_one,denom_one,sub_self]
@[simp]
theorem intDegree_C (k:K):intDegree (C k)=0:=by
 rw [intDegree,num_C,natDegree_C,denom_C,natDegree_one,sub_self]
@[simp]
theorem intDegree_X:intDegree (RatFunc.X:K⟮X⟯)=1:=by
 rw [intDegree,num_X,Polynomial.natDegree_X,denom_X,Polynomial.natDegree_one,
   Int.ofNat_one,Int.ofNat_zero,sub_zero]
@[simp]
theorem intDegree_polynomial {p:K[X]}:
   intDegree (algebraMap K[X] K⟮X⟯ p)=natDegree p:=by
 rw [intDegree,RatFunc.num_algebraMap,RatFunc.denom_algebraMap,Polynomial.natDegree_one,
   Int.ofNat_zero,sub_zero]
theorem intDegree_mul {x y:K⟮X⟯} (hx:x≠0) (hy:y≠0):
   intDegree (x*y)=intDegree x+intDegree y:=by
 simp only [intDegree,add_sub,sub_add,sub_sub_eq_add_sub,sub_sub,sub_eq_sub_iff_add_eq_add]
 norm_cast
 rw [←Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero, ←
   Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
     (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
   ←Polynomial.natDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy), ←
   Polynomial.natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
     (x*y).denom_ne_zero,
   RatFunc.num_denom_mul]
@[simp]
theorem intDegree_inv (x:K⟮X⟯):intDegree (x⁻¹)= -intDegree x:=by
 by_cases hx:x=0 <;> simp [hx,eq_neg_iff_add_eq_zero, ←intDegree_mul (inv_ne_zero hx) hx]
lemma intDegree_div {x y:RatFunc K} (hx:x≠0) (hy:y≠0):
   (x/y).intDegree=x.intDegree-y.intDegree:=by
 rw [div_eq_mul_inv,intDegree_mul,intDegree_inv, ←sub_eq_add_neg] <;> grind
@[simp]
theorem intDegree_neg (x:K⟮X⟯):intDegree (-x)=intDegree x:=by
 by_cases hx:x=0
 · rw [hx,neg_zero]
 · rw [intDegree,intDegree, ←natDegree_neg x.num]
   exact
     natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
       (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)
theorem intDegree_add {x y:K⟮X⟯} (hxy:x+y≠0):
   (x+y).intDegree=
     (x.num*y.denom+x.denom*y.num).natDegree-(x.denom*y.denom).natDegree:=
 natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x+y).denom_ne_zero
   (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
   (num_denom_add x y)
theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x:K⟮X⟯}
   (hx:x≠0) {s:K[X]} (hs:s≠0):
   ((x.num*s).natDegree:ℤ)-(s*x.denom).natDegree=x.intDegree:=by
 apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
   (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
 rw [mul_assoc]
theorem intDegree_add_le {x y:K⟮X⟯} (hy:y≠0) (hxy:x+y≠0):
   intDegree (x+y) ≤ max (intDegree x) (intDegree y):=by
 by_cases hx:x=0
 · simp [hx]
 rw [intDegree_add hxy, ←
   natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero,
   mul_comm y.denom, ←
   natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero,
   le_max_iff,sub_le_sub_iff_right,Int.ofNat_le,sub_le_sub_iff_right,Int.ofNat_le, ←
   le_max_iff,mul_comm y.num]
 exact natDegree_add_le _ _
end IntDegree
end RatFunc
end
end ProximityFlatProofPort
end PackedLegacy_HV

/-! Packed from ProximityPrize.SubmissionLower.AP. -/
section PackedLegacy_AP
section ProximityFlatProofPort
noncomputable section
namespace RatFunc
variable (F K:Type*) [Field F] [Field K]
section InftyValuation
open Multiplicative WithZero Polynomial
variable [DecidableEq (RatFunc F)]
def inftyValuationDef (r:RatFunc F):ℤᵐ⁰:=
 if r=0 then 0 else exp r.intDegree
theorem InftyValuation.map_zero':inftyValuationDef F 0=0:=
 if_pos rfl
theorem InftyValuation.map_one':inftyValuationDef F 1=1:=
 (if_neg one_ne_zero).trans <| by simp
theorem InftyValuation.map_mul' (x y:RatFunc F):
   inftyValuationDef F (x*y)=inftyValuationDef F x*inftyValuationDef F y:=by
 rw [inftyValuationDef,inftyValuationDef,inftyValuationDef]
 by_cases hx:x=0
 · rw [hx,zero_mul,if_pos (Eq.refl _),zero_mul]
 · by_cases hy:y=0
   · rw [hy,mul_zero,if_pos (Eq.refl _),mul_zero]
   · simp_all [RatFunc.intDegree_mul]
theorem InftyValuation.map_add_le_max' (x y:RatFunc F):
   inftyValuationDef F (x+y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y):=by
 unfold inftyValuationDef
 have:=@RatFunc.intDegree_add_le F
 aesop
@[simp]
theorem inftyValuation_of_nonzero {x:RatFunc F} (hx:x≠0):
   inftyValuationDef F x=exp x.intDegree:=by
 rw [inftyValuationDef,if_neg hx]
def inftyValuation:Valuation (RatFunc F) ℤᵐ⁰ where
 toFun:=inftyValuationDef F
 map_zero':=InftyValuation.map_zero' F
 map_one':=InftyValuation.map_one' F
 map_mul':=InftyValuation.map_mul' F
 map_add_le_max':=InftyValuation.map_add_le_max' F
theorem inftyValuation_apply {x:RatFunc F}:inftyValuation F x=inftyValuationDef F x:=
 rfl
@[simp]
theorem inftyValuation.C {k:F} (hk:k≠0):
   inftyValuation F (RatFunc.C k)=1:=by
 simp [inftyValuation_apply,hk]
@[simp]
theorem inftyValuation.X:inftyValuation F RatFunc.X=exp 1:=by
 simp [inftyValuation_apply,inftyValuationDef,if_neg RatFunc.X_ne_zero,RatFunc.intDegree_X]
lemma inftyValuation.X_zpow (m:ℤ):inftyValuation F (RatFunc.X^m)=exp m:=by simp
theorem inftyValuation.X_inv:inftyValuation F (1/RatFunc.X)=exp (-1):=by
 rw [one_div, ←zpow_neg_one,inftyValuation.X_zpow]
theorem inftyValuation.polynomial {p:F[X]} (hp:p≠0):
   inftyValuationDef F (algebraMap F[X] (RatFunc F) p)=exp (p.natDegree:ℤ):=by
 rw [inftyValuationDef,if_neg (by simpa),RatFunc.intDegree_polynomial]
instance:Valuation.IsNontrivial (inftyValuation F):=⟨RatFunc.X,by simp⟩
instance:Valuation.IsTrivialOn F (inftyValuation F):=
 ⟨fun _ hx↦by simp [inftyValuation.C _ hx]⟩
@[implicit_reducible]
def inftyValued:Valued (RatFunc F) ℤᵐ⁰:=
 Valued.mk' <| inftyValuation F
theorem inftyValued.def {x:RatFunc F}:
   (inftyValued F).v x=inftyValuationDef F x:=
 rfl
namespace CompletionAtInfty
attribute [-instance] RatFunc.valuedRatFunc
scoped instance:UniformSpace (RatFunc F):=(inftyValued F).toUniformSpace
def _root_.RatFunc.CompletionAtInfty:=UniformSpace.Completion (RatFunc F)
deriving Field,Algebra (RatFunc F),Coe (RatFunc F),Inhabited
instance:Valued (CompletionAtInfty F) ℤᵐ⁰:=
 inferInstanceAs <| Valued (UniformSpace.Completion (RatFunc F)) ℤᵐ⁰
end CompletionAtInfty
theorem valuedCompletionAtInfty.def {x:CompletionAtInfty F}:
 Valued.v x=(inftyValued F).extensionValuation x:=rfl
end InftyValuation
end RatFunc
end
end ProximityFlatProofPort
end PackedLegacy_AP

/-! Packed from ProximityPrize.SubmissionLower.G1. -/
section PackedLegacy_G1
section ProximityFlatProofPort
namespace IsDiscreteValuationRing
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
 IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation
variable (A K:Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
 [Algebra A K] [IsFractionRing A K]
def maximalIdeal:HeightOneSpectrum A where
 asIdeal:=IsLocalRing.maximalIdeal A
 isPrime:=Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
 ne_bot:=by simpa [ne_eq, ←isField_iff_maximalIdeal_eq] using not_isField A
instance isRankOneDiscrete:
   IsRankOneDiscrete ((maximalIdeal A).valuation K):=by
 have:Nontrivial (valueGroup
     (.ofClass (valuation K (maximalIdeal A)))):=by
   let v:=(maximalIdeal A).valuation K
   let π:=valuation_exists_uniformizer K (maximalIdeal A) |>.choose
   have hπ:v π=↑(ofAdd (-1:ℤ)):=
     valuation_exists_uniformizer K (maximalIdeal A) |>.choose_spec
   rw [Subgroup.nontrivial_iff_exists_ne_one]
   use Units.mk0 (v π) (by simp [hπ])
   constructor
   · apply mem_valueGroup
     use π
     simp [v]
   · simpa [hπ] using not_eq_of_beq_eq_false rfl
 infer_instance
variable {A K}
open scoped WithZero
theorem exists_lift_of_le_one {x:K} (H:((maximalIdeal A).valuation K) x ≤ (1:ℤᵐ⁰)):
   ∃ a:A,algebraMap A K a=x:=by
 letI:DecidableEq A:=Classical.decEq A
 obtain ⟨π,hπ⟩:=exists_irreducible A
 obtain ⟨a,b,hb,h_frac⟩:=IsFractionRing.div_surjective A x
 by_cases ha:a=0
 · rw [←h_frac]
   use 0
   rw [ha,map_zero,zero_div]
 · rw [←h_frac] at H
   obtain ⟨n,u,rfl⟩:=eq_unit_mul_pow_irreducible ha hπ
   obtain ⟨m,w,rfl⟩:=eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
   replace hb:=(mul_mem_nonZeroDivisors.mp hb).2
   rw [mul_comm (w:A) _,map_mul _ (u:A) _,map_mul _ _ (w:A),div_eq_mul_inv,mul_assoc,
     Valuation.map_mul,Integers.one_of_isUnit' u.isUnit (valuation_le_one _),one_mul,
     mul_inv, ←mul_assoc,Valuation.map_mul,map_mul,map_inv₀,map_inv₀,
     Integers.one_of_isUnit' w.isUnit (valuation_le_one _),inv_one,mul_one, ←div_eq_mul_inv,
     ←map_div₀, ←IsFractionRing.mk'_mk_eq_div hb,
     valuation_of_mk',map_pow,map_pow] at H
   have h_mn:m ≤ n:=by
     have v_π_lt_one:=(intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
         (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
     have v_π_ne_zero:(maximalIdeal A).intValuation π≠0:=intValuation_ne_zero _ _ hπ.ne_zero
     zify
     rw [←WithZero.coe_one,div_eq_mul_inv, ←zpow_natCast, ←zpow_natCast, ←ofAdd_zero,
       ←zpow_neg, ←zpow_add₀ v_π_ne_zero, ←sub_eq_add_neg] at H
     rwa [←sub_nonneg, ←zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.mpr v_π_ne_zero)
       v_π_lt_one]
   use u*π^(n-m)*w.2
   simp only [←h_frac,Units.inv_eq_val_inv,_root_.map_mul,_root_.map_pow,map_units_inv,
     mul_assoc,mul_div_assoc ((algebraMap A _) ↑u) _ _]
   congr 1
   rw [div_eq_mul_inv,mul_inv,mul_comm ((algebraMap A _) ↑w)⁻¹ _, ←
     mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
   congr
   rw [pow_sub₀ _ _ h_mn]
   apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
   rw [mem_nonZeroDivisors_iff_ne_zero]
   exact hπ.ne_zero
lemma mker_valuation_eq_isUnitSubmonoid:
   MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).valuation K)=
   (IsUnit.submonoid A).map (algebraMap A K):=by
 ext a
 simp only [MonoidHom.mem_mker,Submonoid.mem_map]
 refine ⟨fun h↦?_,fun h↦?_⟩
 · obtain ⟨b,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one h.le
   rw [valuation_eq_one_iff_notMem] at h
   simp only [IsDiscreteValuationRing.maximalIdeal,IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,
     not_not] at h
   use b,h
 · obtain ⟨x,h,rfl⟩:=h
   simpa [IsDiscreteValuationRing.maximalIdeal] using! h
theorem associated_of_valuation_eq (x y:K)
   (h:((maximalIdeal A).valuation K) x=
   ((maximalIdeal A).valuation K) y):∃ u:Aˣ,u • x=y:=by
 letI:DecidableEq K:=Classical.decEq K
 by_cases hx:x=0
 · rw [eq_comm] at h
   simp_all
 by_cases hy:y=0
 · simp_all
 have:(y/x)∈MonoidHom.mker (((maximalIdeal A).valuation K)):=by simp_all
 rw [mker_valuation_eq_isUnitSubmonoid] at this
 obtain ⟨u,h⟩:=this
 use IsUnit.unit h.1
 simp only [Units.smul_def,Algebra.smul_def,IsUnit.unit_spec,h.2]
 field_simp
theorem map_algebraMap_eq_valuationSubring:Subring.map (algebraMap A K) ⊤=
   ((maximalIdeal A).valuation K).valuationSubring.toSubring:=by
 ext
 refine ⟨fun h↦?_,fun h↦?_⟩
 · obtain ⟨_,_,rfl⟩:=Subring.mem_map.mp h
   apply valuation_le_one
 · obtain ⟨y,rfl⟩:=exists_lift_of_le_one h
   rw [Subring.mem_map]
   exact ⟨y,mem_top _,rfl⟩
noncomputable def equivValuationSubring:
   A ≃+*((maximalIdeal A).valuation K).valuationSubring:=
 (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
   (IsFractionRing.injective A _))).trans
     (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)
lemma intValuation_maximalIdeal (x:A):
   (maximalIdeal A).intValuation x=
     (ENat.recTopCoe 0 (WithZero.coe <| Multiplicative.ofAdd <| Nat.cast ·) (addVal A x))⁻¹:=by
 letI:DecidableEq A:=Classical.decEq A
 by_cases hx:x=0
 · simp [hx]
 obtain ⟨ϖ,hϖ⟩:=exists_irreducible A
 obtain ⟨n,u,rfl⟩:=eq_unit_mul_pow_irreducible hx hϖ
 have:(maximalIdeal A).intValuation ↑u=1:=by simp [maximalIdeal]
 simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
   hϖ.maximalIdeal_eq,hϖ,this,WithZero.exp_eq_coe_ofAdd (n:ℤ)]
end IsDiscreteValuationRing
end ProximityFlatProofPort
end PackedLegacy_G1

/-! Packed from ProximityPrize.SubmissionLower.CL. -/
section PackedLegacy_CL
namespace ProximityPrize.SubmissionLower.RCN353
open scoped Classical
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=(RatFunc.inftyValuation K).valuationSubring
instance infinity_isRankOneDiscrete:
   Valuation.IsRankOneDiscrete (RatFunc.inftyValuation K):=inferInstance
instance infinityRing_isDiscreteValuationRing:
   IsDiscreteValuationRing (InfinityRing K):=inferInstance
theorem infinityRing_isFractionRing:
   IsFractionRing (InfinityRing K) (RatFunc K):=inferInstance
def infinityUniformizer:InfinityRing K:=by
 refine ⟨(RatFunc.X:RatFunc K)⁻¹,?_⟩
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹ ≤ 1
 rw [show RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=
     WithZero.exp (-1:ℤ) by
   simpa only [one_div] using RatFunc.inftyValuation.X_inv K]
 rw [←WithZero.exp_zero,WithZero.exp_le_exp]
 norm_num
theorem infinityUniformizer_value:
   RatFunc.inftyValuation K
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K))=
     WithZero.exp (-1:ℤ):=by
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=_
 simpa only [one_div] using RatFunc.inftyValuation.X_inv K
theorem infinityUniformizer_isUniformizer:
   (RatFunc.inftyValuation K).IsUniformizer
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K)):=by
 unfold Valuation.IsUniformizer
 rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
   (v:=RatFunc.inftyValuation K)
   ⟨algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K),
     infinityUniformizer_value K⟩]
 exact infinityUniformizer_value K
theorem infinityUniformizer_ne_zero:infinityUniformizer K≠0:=by
 intro hzero
 have h:=(infinityUniformizer_isUniformizer K).ne_zero
 exact h (by rw [hzero,map_zero])
theorem infinity_maximalIdeal_eq_span:
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).asIdeal=
     Ideal.span {infinityUniformizer K}:=
 (infinityUniformizer_isUniformizer K).is_generator
theorem infinityUniformizer_irreducible:Irreducible (infinityUniformizer K):=
 (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
   (infinity_maximalIdeal_eq_span K)
theorem infinity_intValuation_eq (x:InfinityRing K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation x=
     RatFunc.inftyValuation K (algebraMap (InfinityRing K) (RatFunc K) x):=by
 by_cases hx:x=0
 · simp [hx]
 obtain ⟨n,u,rfl⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
   hx (infinityUniformizer_irreducible K)
 have hunit:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (u:InfinityRing K)=1:=by
   simp [IsDiscreteValuationRing.maximalIdeal]
 have hunit':
     RatFunc.inftyValuation K
       (algebraMap (InfinityRing K) (RatFunc K) (u:InfinityRing K))=1:=
   Valuation.Integers.one_of_isUnit
     (Valuation.valuationSubring.integers (RatFunc.inftyValuation K)) u.isUnit
 have hparameter:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (infinityUniformizer K)=WithZero.exp (-1:ℤ):=
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation_singleton
     (infinityUniformizer_ne_zero K) (infinity_maximalIdeal_eq_span K)
 simp only [map_mul,map_pow,hunit,hunit',hparameter,
   infinityUniformizer_value,one_mul]
theorem infinity_valuation_eq (x:RatFunc K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).valuation (RatFunc K) x=
     RatFunc.inftyValuation K x:=by
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=InfinityRing K) x
 simp only [map_div₀,
   IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
   infinity_intValuation_eq]
end
end ProximityPrize.SubmissionLower.RCN353
end PackedLegacy_CL

/-! Packed from ProximityPrize.SubmissionLower.R8. -/
section PackedLegacy_R8
namespace ProximityPrize.SubmissionLower.RCN352
open scoped Classical WithZero
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=RCN353.InfinityRing K
def constantMap:K →+*InfinityRing K where
 toFun c:=⟨RatFunc.C c,by
   change RatFunc.inftyValuation K (RatFunc.C c) ≤ 1
   by_cases hc:c=0
   · simp [hc]
   · exact le_of_eq (RatFunc.inftyValuation.C K hc)⟩
 map_zero':=Subtype.ext (map_zero RatFunc.C)
 map_one':=Subtype.ext (map_one RatFunc.C)
 map_add' c d:=Subtype.ext (map_add RatFunc.C c d)
 map_mul' c d:=Subtype.ext (map_mul RatFunc.C c d)
theorem constantMap_value (c:K):
   (constantMap K c).val=RatFunc.C c:=rfl
theorem polynomial_quotient_value_lt_one
   (f g:Polynomial K) (hg:g≠0) (hdeg:f.degree < g.degree):
   RatFunc.inftyValuation K
     (algebraMap (Polynomial K) (RatFunc K) f/
       algebraMap (Polynomial K) (RatFunc K) g) < 1:=by
 by_cases hf:f=0
 · simp [hf]
 have hfmap:algebraMap (Polynomial K) (RatFunc K) f≠0:=by
   simpa using hf
 have hgmap:algebraMap (Polynomial K) (RatFunc K) g≠0:=by
   simpa using hg
 have hquot:=div_ne_zero hfmap hgmap
 have hnat:f.natDegree < g.natDegree:=by
   rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg] at hdeg
   exact_mod_cast hdeg
 rw [RatFunc.inftyValuation_apply,
   RatFunc.inftyValuation_of_nonzero K hquot,
   RatFunc.intDegree_div hfmap hgmap,
   RatFunc.intDegree_polynomial,RatFunc.intDegree_polynomial,
   ←WithZero.exp_zero,WithZero.exp_lt_exp]
 exact sub_neg.mpr (Int.ofNat_lt.mpr hnat)
theorem exists_constant_difference_lt_one (r:InfinityRing K):
   ∃ c:K,RatFunc.inftyValuation K (r.val-RatFunc.C c) < 1:=by
 by_cases hr:r.val=0
 · exact ⟨0,by simp [hr]⟩
 have hf:r.val.num≠0:=RatFunc.num_ne_zero hr
 have hg:r.val.denom≠0:=r.val.denom_ne_zero
 have hdegree:r.val.num.natDegree ≤ r.val.denom.natDegree:=by
   have hmem:RatFunc.inftyValuation K r.val ≤ 1:=r.property
   rw [RatFunc.inftyValuation_apply,
     RatFunc.inftyValuation_of_nonzero K hr,
     ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
   dsimp [RatFunc.intDegree] at hmem
   omega
 by_cases hstrict:r.val.num.natDegree < r.val.denom.natDegree
 · refine ⟨0,?_⟩
   have hd:r.val.num.degree < r.val.denom.degree:=by
     rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg]
     exact_mod_cast hstrict
   have h:=polynomial_quotient_value_lt_one K r.val.num r.val.denom hg hd
   simpa only [RatFunc.num_div_denom,map_zero,sub_zero] using h
 · have hsame:r.val.num.natDegree=r.val.denom.natDegree:=by omega
   have hdegfg:r.val.num.degree=r.val.denom.degree:=by
     rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg,hsame]
   let c:K:=r.val.num.leadingCoeff
   have hc:c≠0:=Polynomial.leadingCoeff_ne_zero.mpr hf
   have hpc:r.val.num.degree=(Polynomial.C c*r.val.denom).degree:=by
     rw [Polynomial.degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc)]
     exact hdegfg
   have hlc:r.val.num.leadingCoeff=
       (Polynomial.C c*r.val.denom).leadingCoeff:=by
     rw [(RatFunc.monic_denom r.val).leadingCoeff_C_mul]
   have hcancel:
       (r.val.num-Polynomial.C c*r.val.denom).degree < r.val.denom.degree:=
     (Polynomial.degree_sub_lt hpc hf hlc).trans_eq hdegfg
   have hgmap:algebraMap (Polynomial K) (RatFunc K) r.val.denom≠0:=by
     simpa using hg
   have hquot:r.val-RatFunc.C c=
       algebraMap (Polynomial K) (RatFunc K)
         (r.val.num-Polynomial.C c*r.val.denom)/
       algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
     calc
       r.val-RatFunc.C c=
           algebraMap (Polynomial K) (RatFunc K) r.val.num/
             algebraMap (Polynomial K) (RatFunc K) r.val.denom-RatFunc.C c:=by
         rw [RatFunc.num_div_denom]
       _=(algebraMap (Polynomial K) (RatFunc K) r.val.num-
             RatFunc.C c*algebraMap (Polynomial K) (RatFunc K) r.val.denom)/
             algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
         rw [sub_div,mul_div_cancel_right₀ _ hgmap]
       _=_:=by rw [map_sub,map_mul,RatFunc.algebraMap_C]
   refine ⟨c,?_⟩
   rw [hquot]
   exact polynomial_quotient_value_lt_one K
     (r.val.num-Polynomial.C c*r.val.denom) r.val.denom hg hcancel
theorem exists_constant_difference_mem_maximalIdeal (r:InfinityRing K):
   ∃ c:K,r-constantMap K c∈IsLocalRing.maximalIdeal (InfinityRing K):=by
 obtain ⟨c,hc⟩:=exists_constant_difference_lt_one K r
 refine ⟨c,?_⟩
 apply (Valuation.mem_maximalIdeal_iff (RatFunc K) (RatFunc.inftyValuation K)).mpr
 exact hc
abbrev ResidueField:=InfinityRing K ⧸ IsLocalRing.maximalIdeal (InfinityRing K)
def residueConstant:K →+*ResidueField K:=
 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K))).comp (constantMap K)
theorem residueConstant_injective:Function.Injective (residueConstant K):=
 (residueConstant K).injective
theorem residueConstant_surjective:Function.Surjective (residueConstant K):=by
 intro y
 obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y
 obtain ⟨c,hc⟩:=exists_constant_difference_mem_maximalIdeal K r
 refine ⟨c,?_⟩
 have hz:=Ideal.Quotient.eq_zero_iff_mem.mpr hc
 have heq:Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K)) r=
     residueConstant K c:=by
   apply sub_eq_zero.mp
   simpa only [map_sub,residueConstant,RingHom.comp_apply] using hz
 exact heq.symm
def residueEquiv:K ≃+*ResidueField K:=
 RingEquiv.ofBijective (residueConstant K)
   ⟨residueConstant_injective K,residueConstant_surjective K⟩
theorem residueEquiv_apply (c:K):residueEquiv K c=residueConstant K c:=rfl
end
end ProximityPrize.SubmissionLower.RCN352
end PackedLegacy_R8

/-! Packed from ProximityPrize.SubmissionLower.V6. -/
section PackedLegacy_V6
section ProximityFlatProofPort
universe u v w
namespace Valuation
namespace Integers
section CommRing
variable {R:Type u} {Γ₀:Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
 {v:Valuation R Γ₀} {O:Type w} [CommRing O] [Algebra O R] (hv:Integers v O)
include hv
open Polynomial
lemma isIntegral_iff_v_le_one {x:R}:
   IsIntegral O x ↔ v x ≤ 1:=by
 nontriviality R
 have:Nontrivial O:=hv.nontrivial_iff.mpr inferInstance
 constructor
 · rintro ⟨f,hm,hf⟩
   by_cases hn:f.natDegree=0
   · rw [Polynomial.natDegree_eq_zero] at hn
     obtain ⟨c,rfl⟩:=hn
     simp [map_eq_zero_iff _ hv.hom_inj,hm.ne_zero_of_C] at hf
   simp only [Polynomial.eval₂_eq_sum_range,Finset.sum_range_succ,hm.coeff_natDegree,map_one,
     one_mul,add_eq_zero_iff_eq_neg] at hf
   apply_fun v at hf
   simp only [map_neg,map_pow] at hf
   contrapose! hf
   refine ne_of_lt (v.map_sum_lt ?_ ?_)
   · simp [hn,(hf.trans' (zero_lt_one)).ne']
   · simp only [Finset.mem_range,map_mul,map_pow]
     intro _ hi
     exact mul_lt_of_le_one_of_lt (hv.map_le_one _) <| pow_lt_pow_right₀ hf hi
 · intro h
   obtain ⟨y,rfl⟩:=hv.exists_of_le_one h
   exact ⟨Polynomial.X-.C y,by monicity,by simp⟩
theorem mem_of_integral {x:R} (hx:IsIntegral O x):x∈v.integer:=
 hv.isIntegral_iff_v_le_one.mp hx
protected theorem integralClosure:integralClosure O R=⊥:=
 bot_unique fun _ hr =>
   let ⟨x,hx⟩:=hv.3 (hv.mem_of_integral hr)
   Algebra.mem_bot.2 ⟨x,hx⟩
end CommRing
section FractionField
variable {K:Type u} {Γ₀:Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
 {v:Valuation K Γ₀} {O:Type w} [CommRing O]
 [Algebra O K]
 (hv:Integers v O)
include hv in
theorem isIntegrallyClosed:IsIntegrallyClosed O:=by
 have:IsFractionRing O K:=hv.isFractionRing
 exact
   (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)
instance isIntegrallyClosed_integers (v:Valuation K Γ₀):
   IsIntegrallyClosed v.integer:=
 (Valuation.integer.integers v).isIntegrallyClosed
end FractionField
end Integers
end Valuation
end ProximityFlatProofPort
end PackedLegacy_V6

/-! Packed from ProximityPrize.SubmissionLower.W5. -/
section PackedLegacy_W5
namespace ProximityPrize.SubmissionLower.RCN359
open scoped Classical nonZeroDivisors WithZero
open IsDedekindDomain
noncomputable section
section NormalizedEquality
variable {L:Type*} [Field L]
local instance:DecidableEq L:=Classical.decEq L
theorem value_le_exp_neg_one {z:ℤᵐ⁰} (hz:z < 1):
   z ≤ WithZero.exp (-1:ℤ):=by
 by_cases hz0:z=0
 · simp [hz0]
 have hlog:z.log < 0:=by
   have h:WithZero.exp z.log < WithZero.exp (0:ℤ):=by
     simpa only [WithZero.exp_log hz0,WithZero.exp_zero] using hz
   exact WithZero.exp_lt_exp.mp h
 calc
   z=WithZero.exp z.log:=(WithZero.exp_log hz0).symm
   _ ≤ WithZero.exp (-1:ℤ):=WithZero.exp_le_exp.mpr (by omega)
theorem eq_of_equiv_surjective (v w:Valuation L ℤᵐ⁰)
   (hv:Function.Surjective v) (hw:Function.Surjective w)
   (h:v.IsEquiv w):v=w:=by
 have hneg:WithZero.exp (-1:ℤ) < 1:=by
   rw [←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hvπlt:v π < 1:=hπ ▸ hneg
 have hwπlt:w π < 1:=h.lt_one_iff_lt_one.mp hvπlt
 have hlower:WithZero.exp (-1:ℤ) ≤ w π:=by
   obtain ⟨a,ha⟩:=hw (WithZero.exp (-1:ℤ))
   have haw:w a < 1:=ha ▸ hneg
   have hav:v a < 1:=h.lt_one_iff_lt_one.mpr haw
   have hal:v a ≤ v π:=hπ ▸ value_le_exp_neg_one hav
   have hal':w a ≤ w π:=(h a π).mp hal
   simpa only [ha] using hal'
 have hwπ:w π=WithZero.exp (-1:ℤ):=
   le_antisymm (value_le_exp_neg_one hwπlt) hlower
 ext x
 by_cases hx:x=0
 · simp [hx]
 have hvx:v x≠0:=(Valuation.ne_zero_iff v).mpr hx
 have hpower:v (π^(-(v x).log))=v x:=by
   simp [hπ,WithZero.exp_log hvx]
 have hpower':w (π^(-(v x).log))=v x:=by
   simp [hwπ,WithZero.exp_log hvx]
 exact hpower'.symm.trans (h.eq_iff.mp hpower)
end NormalizedEquality
section UnitBall
variable (R L:Type*) [CommRing R] [Field L] [Algebra R L]
 (v:Valuation L ℤᵐ⁰) (hR:∀ r:R,v (algebraMap R L r) ≤ 1)
def unitBallMap:R →+*v.valuationSubring where
 toFun r:=⟨algebraMap R L r,hR r⟩
 map_zero':=Subtype.ext (map_zero _)
 map_one':=Subtype.ext (map_one _)
 map_add' r s:=Subtype.ext (map_add _ r s)
 map_mul' r s:=Subtype.ext (map_mul _ r s)
include hR in
theorem integral_le_one {x:L} (hx:IsIntegral R x):v x ≤ 1:=by
 letI:Algebra R v.valuationSubring:=(unitBallMap R L v hR).toAlgebra
 letI:IsScalarTower R v.valuationSubring L:=
   IsScalarTower.of_algebraMap_eq' rfl
 have hx':IsIntegral v.valuationSubring x:=hx.tower_top
 exact (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp hx'
def centerIdeal:Ideal R:=
 Ideal.comap (unitBallMap R L v hR) (IsLocalRing.maximalIdeal v.valuationSubring)
instance centerIdeal_isPrime:(centerIdeal R L v hR).IsPrime:=by
 unfold centerIdeal
 infer_instance
theorem mem_centerIdeal (r:R):
   r∈centerIdeal R L v hR ↔ v (algebraMap R L r) < 1:=by
 change unitBallMap R L v hR r∈IsLocalRing.maximalIdeal v.valuationSubring ↔ _
 exact Valuation.mem_maximalIdeal_iff L v
end UnitBall
section Center
variable (S L:Type*) [CommRing S] [IsDedekindDomain S] [Field L]
 [Algebra S L] [IsFractionRing S L]
 (v:Valuation L ℤᵐ⁰) (hS:∀ s:S,v (algebraMap S L s) ≤ 1)
theorem centerIdeal_ne_bot (hv:Function.Surjective v):
   centerIdeal S L v hS≠⊥:=by
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hπ0:π≠0:=by
   apply (Valuation.ne_zero_iff v).mp
   rw [hπ]
   exact WithZero.exp_ne_zero
 obtain ⟨a,b,hb,hfrac⟩:=IsFractionRing.div_surjective (A:=S) π
 have hb0:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have ha0:a≠0:=by
   intro hzero
   apply hπ0
   simpa [hzero] using hfrac.symm
 have hvb0:v (algebraMap S L b)≠0:=
   (Valuation.ne_zero_iff v).mpr (by
     simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0)
 have hfraclt:v (algebraMap S L a)/v (algebraMap S L b) < 1:=by
   rw [←map_div₀,hfrac,hπ, ←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 have halt:v (algebraMap S L a) < 1:=
   ((div_lt_one₀ (zero_lt_iff.mpr hvb0)).mp hfraclt).trans_le (hS b)
 intro hbot
 have ha:=(mem_centerIdeal S L v hS a).mpr halt
 exact ha0 (by simpa only [hbot,Ideal.mem_bot] using ha)
def centerPlace (hv:Function.Surjective v):HeightOneSpectrum S:=
 ⟨centerIdeal S L v hS,inferInstance,centerIdeal_ne_bot S L v hS hv⟩
theorem centerPlace_membership (hv:Function.Surjective v) (s:S):
   s∈(centerPlace S L v hS hv).asIdeal ↔
     v (algebraMap S L s) < 1:=
 mem_centerIdeal S L v hS s
open scoped algebraMap in
theorem center_localization_le (hv:Function.Surjective v):
   HeightOneSpectrum.valuationSubringAtPrime L (centerPlace S L v hS hv) ≤
     v.valuationSubring:=by
 rintro x ⟨a,s,hs,rfl⟩
 have hsnot:s∉(centerPlace S L v hS hv).asIdeal:=hs
 have hsvalue:v (algebraMap S L s)=1:=by
   apply le_antisymm (hS s)
   exact le_of_not_gt fun hlt↦hsnot ((centerPlace_membership S L v hS hv s).mpr hlt)
 suffices v ((algebraMap S L a)/(algebraMap S L s)) ≤ 1 by
   rwa [division_def] at this
 rw [map_div₀,hsvalue,div_one]
 exact hS a
theorem centerPlace_valuation (hv:Function.Surjective v):
   v=(centerPlace S L v hS hv).valuation L:=by
 let p:=centerPlace S L v hS hv
 have hnontrivial:v.IsNontrivial:=by
   obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
   refine ⟨π,?_⟩
   simp [hπ]
 have htop:v.valuationSubring≠⊤:=by
   simpa only [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not] using hnontrivial
 have hring:HeightOneSpectrum.valuationSubringAtPrime L p=v.valuationSubring:=
   ValuationSubring.eq_of_le_of_ne_top _
     (center_localization_le S L v hS hv) htop
 rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hring
 have hequiv:(p.valuation L).IsEquiv v:=
   (Valuation.isEquiv_iff_valuationSubring _ _).mpr hring
 exact (eq_of_equiv_surjective (p.valuation L) v
   (p.valuation_surjective L) hv hequiv).symm
include hS in
theorem exists_unique_place (hv:Function.Surjective v):
   ∃! p:HeightOneSpectrum S,v=p.valuation L:=by
 refine ⟨centerPlace S L v hS hv,centerPlace_valuation S L v hS hv,?_⟩
 intro q hq
 apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K:=L)
 exact Valuation.IsEquiv.of_eq
   (hq.symm.trans (centerPlace_valuation S L v hS hv))
end Center
end
end ProximityPrize.SubmissionLower.RCN359
end PackedLegacy_W5

/-! Packed from ProximityPrize.SubmissionLower.F8. -/
section PackedLegacy_F8
section ProximityFlatProofPort
namespace RingHom
open scoped TensorProduct
open TensorProduct Algebra.TensorProduct
theorem finite_stableUnderComposition:StableUnderComposition @Finite:=by
 introv R hf hg
 exact hg.comp hf
theorem finite_respectsIso:RespectsIso @Finite:=by
 apply finite_stableUnderComposition.respectsIso
 intros
 exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective
lemma finite_containsIdentities:ContainsIdentities @Finite:=Finite.id
theorem finite_isStableUnderBaseChange:IsStableUnderBaseChange @Finite:=by
 refine IsStableUnderBaseChange.mk finite_respectsIso ?_
 simp only [finite_algebraMap]
 intros
 infer_instance
end RingHom
open scoped Pointwise
universe u
variable {R S:Type*} [CommRing R] [CommRing S] (M:Submonoid R) (f:R →+*S)
 (R' S':Type*) [CommRing R'] [CommRing S']
 [Algebra R R'] [Algebra S S']
theorem RingHom.finite_localizationPreserves:RingHom.LocalizationPreserves @RingHom.Finite:=by
 introv R hf
 letI:=f.toAlgebra
 letI:=((algebraMap S S').comp f).toAlgebra
 let f':R' →+*S':=IsLocalization.map S' f (Submonoid.le_comap_map M)
 letI:=f'.toAlgebra
 have:IsScalarTower R R' S':=IsScalarTower.of_algebraMap_eq'
   (IsLocalization.map_comp M.le_comap_map).symm
 have:IsScalarTower R S S':=IsScalarTower.of_algebraMap_eq' rfl
 have:IsLocalization (Algebra.algebraMapSubmonoid S M) S':=by
   rwa [Algebra.algebraMapSubmonoid,RingHom.algebraMap_toAlgebra]
 have:Module.Finite R S:=hf
 exact .of_isLocalization R S M
theorem RingHom.localization_away_map_finite (R S R' S':Type u) [CommRing R] [CommRing S]
   [CommRing R'] [CommRing S'] [Algebra R R'] (f:R →+*S) [Algebra S S']
   (r:R) [IsLocalization.Away r R']
   [IsLocalization.Away (f r) S'] (hf:f.Finite):(IsLocalization.Away.map R' S' f r).Finite:=
 finite_localizationPreserves.away f r _ _ hf
theorem RingHom.finite_ofLocalizationSpan:RingHom.OfLocalizationSpan @RingHom.Finite:=by
 classical
 rw [RingHom.ofLocalizationSpan_iff_finite]
 introv R hs H
 letI:DecidableEq S:=Classical.decEq S
 letI:=f.toAlgebra
 letI:=fun r:s => (Localization.awayMap f r).toAlgebra
 have (r:s):IsLocalization ((Submonoid.powers (r:R)).map (algebraMap R S))
     (Localization.Away (f r)):=by
   rw [Submonoid.map_powers];exact Localization.isLocalization
 haveI:∀ r:s,IsScalarTower R (Localization.Away (r:R)) (Localization.Away (f r)):=
   fun r => IsScalarTower.of_algebraMap_eq'
     (IsLocalization.map_comp (Submonoid.powers (r:R)).le_comap_map).symm
 constructor
 replace H:=fun r => (H r).1
 choose s₁ s₂ using H
 let sf:=fun x:s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
 use s.attach.biUnion sf
 rw [Submodule.span_attach_biUnion,eq_top_iff]
 rintro x-
 apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s:Set R) hs _ _
 intro r
 obtain ⟨⟨_,n₁,rfl⟩,hn₁⟩:=
   multiple_mem_span_of_mem_localization_span (Submonoid.powers (r:R))
     (Localization.Away (r:R)) (s₁ r:Set (Localization.Away (f r))) (algebraMap S _ x)
     (by rw [s₂ r];trivial)
 dsimp only at hn₁
 rw [Submonoid.smul_def,Algebra.smul_def,IsScalarTower.algebraMap_apply R S, ←map_mul] at hn₁
 obtain ⟨⟨_,n₂,rfl⟩,hn₂⟩:=
   IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r:R))
     (Localization.Away (f r)) _ (s₁ r) hn₁
 rw [Submonoid.smul_def, ←Algebra.smul_def,smul_smul, ←pow_add] at hn₂
 simp_rw [Submonoid.map_powers] at hn₂
 use n₂+n₁
 exact le_iSup (fun x:s => Submodule.span R (sf x:Set S)) r hn₂
end ProximityFlatProofPort
end PackedLegacy_F8

/-! Packed from ProximityPrize.SubmissionLower.IR. -/
section PackedLegacy_IR
section ProximityFlatProofPort
variable {R S A n m:Type*} [CommRing R] [CommRing S]
 (M:Matrix m m S) [DecidableEq m] [DecidableEq n] (k:m)
open Matrix Polynomial
namespace Algebra.Norm.Transitivity
def auxMat:Matrix m m S:=
 of fun i j↦
   if j=k then
     if i=k then 1 else 0
   else if i=k then-M k j
   else if i=j then M k k
   else 0
lemma auxMat_blockTriangular:(auxMat M k).BlockTriangular (·≠k):=
 fun i j lt↦by
   simp_rw [lt_iff_not_ge,le_Prop_eq,Classical.not_imp,not_not] at lt
   rw [auxMat,of_apply,if_pos lt.2,if_neg lt.1]
lemma auxMat_toSquareBlock_ne:(auxMat M k).toSquareBlock (·≠k) True=M k k • 1:=by
 ext i j
 simp [auxMat,toSquareBlock_def,if_neg (of_eq_true i.2),if_neg (of_eq_true j.2),
   Matrix.one_apply,Subtype.ext_iff]
lemma auxMat_toSquareBlock_eq:(auxMat M k).toSquareBlock (·≠k) False=1:=by
 ext ⟨i,hi⟩ ⟨j,hj⟩
 rw [eq_iff_iff,iff_false,not_not] at hi hj
 simp [auxMat,toSquareBlock_def,if_pos hi,if_pos hj,Matrix.one_apply,if_pos (hj ▸ hi)]
variable [Fintype m]
lemma mul_auxMat_blockTriangular:(M*auxMat M k).BlockTriangular (·=k):=
 fun i j lt↦by
   simp_rw [lt_iff_not_ge,le_Prop_eq,Classical.not_imp] at lt
   simp_rw [Matrix.mul_apply,auxMat,of_apply,if_neg lt.2,mul_ite,mul_neg,mul_zero]
   rw [Finset.sum_ite,Finset.filter_eq',if_pos (Finset.mem_univ _),Finset.sum_singleton,
     Finset.sum_ite_eq',if_pos,lt.1,mul_comm,neg_add_cancel]
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt.2⟩
lemma mul_auxMat_corner:(M*auxMat M k) k k=M k k:=by simp [Matrix.mul_apply,auxMat]
lemma mul_auxMat_toSquareBlock_eq:
   (M*auxMat M k).toSquareBlock (·=k) True=M k k • 1:=by
 ext ⟨i,hi⟩ ⟨j,hj⟩
 rw [eq_iff_iff,iff_true] at hi hj
 simp [toSquareBlock_def,hi,hj,mul_auxMat_corner]
set_option quotPrecheck false in
scoped notation "mulAuxMatBlock" => (M*auxMat M k).toSquareBlock (·=k) False
lemma det_mul_corner_pow:
   M.det*M k k^(Fintype.card m-1)=M k k*(mulAuxMatBlock).det:=by
 letI:DecidableEq Prop:=Classical.decEq Prop
 trans (M*auxMat M k).det
 · simp [det_mul,(auxMat_blockTriangular M k).det_fintype,
     auxMat_toSquareBlock_ne,auxMat_toSquareBlock_eq]
 rw [(mul_auxMat_blockTriangular M k).det_fintype,Fintype.prod_Prop,mul_auxMat_toSquareBlock_eq]
 simp_rw [det_smul_of_tower,eq_iff_iff,iff_true,Fintype.card_unique,
   pow_one,det_one,smul_eq_mul,mul_one]
 convert! rfl
noncomputable def cornerAddX:Matrix m m S[X]:=
 (diagonal fun i↦if i=k then Polynomial.X else 0)+M.map Polynomial.C
variable [Fintype n] (f:S →+*Matrix n n R)
omit [Fintype m] in
lemma polyToMatrix_cornerAddX:
   f.polyToMatrix (cornerAddX M k k k)=(-f (M k k)).charmatrix:=by
 simp [cornerAddX,Matrix.add_apply,charmatrix,
   RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv,map_neg]
lemma eval_zero_det_det:eval 0 (f.polyToMatrix (cornerAddX M k).det).det=(f M.det).det:=by
 rw [←coe_evalRingHom,RingHom.map_det, ←RingHom.comp_apply,
   evalRingHom_mapMatrix_comp_polyToMatrix,f.comp_apply,RingHom.map_det]
 congr;ext;simp [cornerAddX,diagonal,apply_ite]
lemma eval_zero_comp_det:
   eval 0 (comp m m n n R[X] <| (cornerAddX M k).map f.polyToMatrix).det=
     (comp m m n n R <| M.map f).det:=by
 simp_rw [←coe_evalRingHom,RingHom.map_det, ←compRingEquiv_apply, ←RingEquiv.coe_toRingHom,
   ←RingHom.mapMatrix_apply, ←RingHom.comp_apply, ←RingHom.comp_assoc,
   evalRingHom_mapMatrix_comp_compRingEquiv,RingHom.comp_assoc,RingHom.mapMatrix_comp,
   evalRingHom_mapMatrix_comp_polyToMatrix, ←RingHom.mapMatrix_comp,RingHom.comp_apply]
 congr with i j
 simp [cornerAddX,diagonal,apply_ite]
theorem comp_det_mul_pow:
   ((M.map f).comp m m n n R).det*(f (M k k)).det^(Fintype.card m-1)=
     (f (M k k)).det*(((mulAuxMatBlock).map f).comp _ _ n n R).det:=by
 letI:DecidableEq Prop:=Classical.decEq Prop
 trans (((M*auxMat M k).map f).comp m m n n R).det
 · simp_rw [←f.mapMatrix_apply, ←compRingEquiv_apply,map_mul,det_mul,f.mapMatrix_apply,
     compRingEquiv_apply,((auxMat_blockTriangular M k).map f).comp.det_fintype,Fintype.prod_Prop,
     comp_toSquareBlock (b:=(·≠k)),det_reindex_self,map_toSquareBlock,
     auxMat_toSquareBlock_eq,auxMat_toSquareBlock_ne,smul_one_eq_diagonal, ←diagonal_one,
     diagonal_map (map_zero _),comp_diagonal,det_reindex_self]
   simp
 · simp_rw [((mul_auxMat_blockTriangular M k).map f).comp.det_fintype,Fintype.prod_Prop,
     comp_toSquareBlock (b:=(·=k)),det_reindex_self,map_toSquareBlock,
     mul_auxMat_toSquareBlock_eq,smul_one_eq_diagonal,
     diagonal_map (map_zero _),comp_diagonal,det_reindex_self]
   simp
   convert! rfl
variable {M f} in
lemma det_det_aux
   (ih:∀ M,(f (det M)).det=((M.map f).comp {a//(a=k)=False} _ n n R).det):
   ((f M.det).det-((M.map f).comp m m n n R).det)*
     (f (M k k)).det^(Fintype.card m-1)=0:=by
 rw [sub_mul,comp_det_mul_pow, ←det_pow, ←map_pow, ←det_mul, ←map_mul,
   det_mul_corner_pow,map_mul,det_mul,ih,sub_self]
end Algebra.Norm.Transitivity
open Algebra.Norm.Transitivity
theorem Matrix.det_det [Fintype m] [Fintype n] (f:S →+*Matrix n n R):
   (f M.det).det=((M.map f).comp m m n n R).det:=by
 induction l:Fintype.card m generalizing R S m with
 | zero =>
   rw [Fintype.card_eq_zero_iff] at l
   simp_rw [Matrix.det_isEmpty,map_one,det_one]
 | succ l ih =>
   have ⟨k⟩:=Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ l)
   let f':=f.polyToMatrix
   let M':=cornerAddX M k
   have:(f' M'.det).det=((M'.map f').comp m m n n R[X]).det:=by
     refine sub_eq_zero.mp <| mem_nonZeroDivisors_iff_right.mp
       (pow_mem ?_ _) _ (det_det_aux k fun M↦ih _ _ <| by
         grind [Fintype.card_subtype_compl,Fintype.card_unique])
     rw [polyToMatrix_cornerAddX, ←charpoly]
     exact (Matrix.charpoly_monic _).mem_nonZeroDivisors
   rw [←eval_zero_det_det,congr_arg (eval 0) this,eval_zero_comp_det]
variable [Algebra R S] [Module.Free R S]
theorem LinearMap.det_restrictScalars [AddCommGroup A] [Module R A] [Module S A]
   [IsScalarTower R S A] [Module.Free S A] {f:A →ₗ[S] A}:
   (f.restrictScalars R).det=Algebra.norm R f.det:=by
 classical
 nontriviality R
 nontriviality A
 have:=Module.nontrivial S A
 let ⟨ιS,bS⟩:=Module.Free.exists_basis (R:=R) (M:=S)
 let ⟨ιA,bA⟩:=Module.Free.exists_basis (R:=S) (M:=A)
 letI:DecidableEq ιS:=Classical.decEq ιS
 letI:DecidableEq ιA:=Classical.decEq ιA
 have:=bS.index_nonempty
 have:=bA.index_nonempty
 cases fintypeOrInfinite ιS;swap
 · rw [Algebra.norm_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bS),
     det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
 cases fintypeOrInfinite ιA;swap
 · rw [det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bA),map_one,
     det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
 rw [Algebra.norm_eq_matrix_det bS, ←AlgHom.coe_toRingHom, ←det_toMatrix bA,det_det,
   ←det_toMatrix (bS.smulTower' bA),restrictScalars_toMatrix,RingHom.coe_coe]
theorem Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra S A]
   [IsScalarTower R S A] [Module.Free S A] {a:A}:
   norm R (norm S a)=norm R a:=by
 rw [norm_apply S,norm_apply R a, ←LinearMap.det_restrictScalars];rfl
variable {L:Type*} (K:Type*) [Field K] [Field L] [Algebra K L]
open Module IntermediateField AdjoinSimple
namespace Algebra
theorem isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] {x:L}
   (hx:IsIntegral R x):IsIntegral R (norm K x):=by
 by_cases h:FiniteDimensional K L
 swap
 · simpa [norm_eq_one_of_not_module_finite h] using isIntegral_one
 let F:=K⟮x⟯
 rw [←norm_norm (S:=F), ←coe_gen K x, ←IntermediateField.algebraMap_apply,
   norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x),map_pow]
 apply IsIntegral.pow
 rw [←isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure F)).injective,
   norm_gen_eq_prod_roots _ (IsAlgClosed.splits _)]
 refine IsIntegral.multiset_prod (fun y hy↦⟨minpoly R x,minpoly.monic hx,?_⟩)
 suffices (aeval y) ((minpoly R x).map (algebraMap R K))=0 by simpa
 obtain ⟨P,hP⟩:=minpoly.dvd K x (show aeval x ((minpoly R x).map (algebraMap R K))=0 by simp)
 simp [hP,aeval_mul,(mem_aroots'.mp hy).2]
theorem norm_eq_norm_adjoin (x:L):
   norm K x=norm K (AdjoinSimple.gen K x)^finrank K⟮x⟯ L:=by
 by_cases h:FiniteDimensional K L
 swap
 · rw [norm_eq_one_of_not_module_finite h]
   by_cases hx:IsIntegral K x
   · have h₁:¬ FiniteDimensional K⟮x⟯ L:=fun H↦h <| by
       have:FiniteDimensional K K⟮x⟯:=adjoin.finiteDimensional hx
       exact Finite.trans K⟮x⟯ L
     simp [finrank_of_not_finite h₁]
   · rw [norm_eq_one_of_not_module_finite]
     · simp
     · refine fun H↦hx ?_
       rw [←isIntegral_gen]
       exact IsIntegral.isIntegral (gen K x)
 let F:=K⟮x⟯
 nth_rw 1 [←coe_gen K x]
 rw [←norm_norm (S:=F), ←IntermediateField.algebraMap_apply,
   norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x),map_pow,
   finrank_eq_card_chooseBasisIndex]
variable (F E:Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable {K} in
theorem norm_eq_prod_roots {x:L} (hF:((minpoly K x).map (algebraMap K F)).Splits):
   algebraMap K F (norm K x)=
     ((minpoly K x).aroots F).prod^finrank K⟮x⟯ L:=by
 rw [norm_eq_norm_adjoin K x,map_pow,IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]
variable [FiniteDimensional K L]
theorem norm_eq_prod_embeddings [Algebra.IsSeparable K L] [IsAlgClosed E]
   (x:L):algebraMap K E (norm K x)=∏ σ:L →ₐ[K] E,σ x:=by
 have hx:=Algebra.IsSeparable.isIntegral K x
 rw [norm_eq_norm_adjoin K x,map_pow, ←adjoin.powerBasis_gen hx,
   norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits _)]
 · exact (prod_embeddings_eq_finrank_pow L (L:=K⟮x⟯) E (adjoin.powerBasis hx)).symm
 · haveI:=Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
   exact Algebra.IsSeparable.isSeparable K _
theorem norm_eq_prod_automorphisms [IsGalois K L] (x:L):
   algebraMap K L (norm K x)=∏ σ:Gal(L/K),σ x:=by
 apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
 rw [map_prod (algebraMap L (AlgebraicClosure L))]
 rw [←Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
 · rw [←norm_eq_prod_embeddings _ _ x, ←IsScalarTower.algebraMap_apply]
 · intro σ
   simp only [Normal.algHomEquivAut,AlgHom.restrictNormal',Equiv.coe_fn_mk,
     AlgEquiv.coe_ofBijective,AlgHom.restrictNormal_commutes,algebraMap_self,RingHom.id_apply]
end Algebra
end ProximityFlatProofPort
end PackedLegacy_IR

/-! Packed from ProximityPrize.SubmissionLower.T1. -/
section PackedLegacy_T1
section ProximityFlatProofPort
universe u v w z
open scoped Matrix
open Matrix Module Fintype Polynomial Finset IntermediateField
namespace Algebra
variable (A:Type u) {B:Type v} (C:Type z) {ι:Type w} [DecidableEq ι]
 [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
section Discr
noncomputable def discr (A:Type u) {B:Type v} [CommRing A] [CommRing B] [Algebra A B]
   [Fintype ι] (b:ι → B):=(traceMatrix A b).det
theorem discr_def [Fintype ι] (b:ι → B):discr A b=(traceMatrix A b).det:=rfl
variable {A C} in
theorem discr_eq_discr_of_algEquiv [Fintype ι] (b:ι → B) (f:B ≃ₐ[A] C):
   Algebra.discr A b=Algebra.discr A (f ∘ b):=by
 rw [discr_def];congr;ext
 simp_rw [traceMatrix_apply,traceForm_apply,Function.comp, ←map_mul f,trace_eq_of_algEquiv]
variable {ι':Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']
section Basic
@[simp]
theorem discr_reindex (b:Basis ι A B) (f:ι ≃ ι'):discr A (b ∘ ⇑f.symm)=discr A b:=by
 classical rw [←Basis.coe_reindex,discr_def,traceMatrix_reindex,det_reindex_self, ←discr_def]
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b:ι → B}
   (hli:¬LinearIndependent A b):discr A b=0:=by
 classical
 obtain ⟨g,hg,i,hi⟩:=Fintype.not_linearIndependent_iff.1 hli
 have:(traceMatrix A b)*ᵥ g=0:=by
   ext i
   have:∀ j,(trace A B) (b i*b j)*g j=(trace A B) (g j • b j*b i):=by
     intro j
     simp [mul_comm]
   simp only [mulVec,dotProduct,traceMatrix_apply,Pi.zero_apply,traceForm_apply,fun j =>
     this j, ←map_sum, ←sum_mul,hg,zero_mul,map_zero]
 by_contra h
 rw [discr_def] at h
 simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi
variable {A}
theorem discr_of_matrix_vecMul (b:ι → B) (P:Matrix ι ι A):
   discr A (b ᵥ*P.map (algebraMap A B))=P.det^2*discr A b:=by
 rw [discr_def,traceMatrix_of_matrix_vecMul,det_mul,det_mul,det_transpose,mul_comm, ←
   mul_assoc,discr_def,pow_two]
theorem discr_of_matrix_mulVec (b:ι → B) (P:Matrix ι ι A):
   discr A (P.map (algebraMap A B)*ᵥ b)=P.det^2*discr A b:=by
 rw [discr_def,traceMatrix_of_matrix_mulVec,det_mul,det_mul,det_transpose,mul_comm, ←
   mul_assoc,discr_def,pow_two]
end Basic
section Field
variable (K:Type u) {L:Type v} (E:Type z) [Field K] [Field L] [Field E]
 [Algebra K L] [Algebra K E]
 [Module.Finite K L] [IsAlgClosed E]
theorem discr_not_zero_of_basis [Algebra.IsSeparable K L] (b:Basis ι K L):
   discr K b≠0:=by
 rw [discr_def,traceMatrix_of_basis, ←LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
 exact traceForm_nondegenerate _ _
theorem discr_isUnit_of_basis [Algebra.IsSeparable K L] (b:Basis ι K L):IsUnit (discr K b):=
 IsUnit.mk0 _ (discr_not_zero_of_basis _ _)
variable (b:ι → L) (pb:PowerBasis K L)
theorem discr_eq_det_embeddingsMatrixReindex_pow_two
   [Algebra.IsSeparable K L] (e:ι ≃ (L →ₐ[K] E)):
   algebraMap K E (discr K b)=(embeddingsMatrixReindex K E b e).det^2:=by
 rw [discr_def,RingHom.map_det,RingHom.mapMatrix_apply,
   traceMatrix_eq_embeddingsMatrixReindex_mul_trans,det_mul,det_transpose,pow_two]
theorem discr_powerBasis_eq_prod (e:Fin pb.dim ≃ (L →ₐ[K] E)) [Algebra.IsSeparable K L]:
   algebraMap K E (discr K pb.basis)=
     ∏ i:Fin pb.dim,∏ j∈Ioi i,(e j pb.gen-e i pb.gen)^2:=by
 rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e,
   embeddingsMatrixReindex_eq_vandermonde,det_transpose,det_vandermonde, ←prod_pow]
 congr;ext i
 rw [←prod_pow]
theorem discr_powerBasis_eq_prod' [Algebra.IsSeparable K L] (e:Fin pb.dim ≃ (L →ₐ[K] E)):
   algebraMap K E (discr K pb.basis)=
     ∏ i:Fin pb.dim,∏ j∈Ioi i, -((e j pb.gen-e i pb.gen)*(e i pb.gen-e j pb.gen)):=by
 rw [discr_powerBasis_eq_prod _ _ _ e]
 congr;ext i;congr;ext j
 ring
local notation "n" => finrank K L
theorem discr_powerBasis_eq_prod'' [Algebra.IsSeparable K L] (e:Fin pb.dim ≃ (L →ₐ[K] E)):
   algebraMap K E (discr K pb.basis)=
     (-1)^(n*(n-1)/2)*
       ∏ i:Fin pb.dim,∏ j∈Ioi i,(e j pb.gen-e i pb.gen)*(e i pb.gen-e j pb.gen):=by
 rw [discr_powerBasis_eq_prod' _ _ _ e]
 simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen-e i pb.gen)*(e i pb.gen-e j pb.gen)),
   prod_mul_distrib]
 congr
 simp only [prod_pow_eq_pow_sum,prod_const]
 congr
 rw [←@Nat.cast_inj ℚ,Nat.cast_sum]
 have:∀ x:Fin pb.dim,↑x+1 ≤ pb.dim:=by simp [Fin.is_lt]
 simp_rw [Fin.card_Ioi,Nat.sub_sub,add_comm 1]
 simp only [Nat.cast_sub,this,Finset.card_fin,nsmul_eq_mul,sum_const,sum_sub_distrib,
   Nat.cast_add,Nat.cast_one,sum_add_distrib,mul_one]
 rw [←Nat.cast_sum, ←@Finset.sum_range ℕ _ pb.dim fun i => i,sum_range_id]
 have hn:n=pb.dim:=by
   rw [←AlgHom.card K L E, ←Fintype.card_fin pb.dim]
   exact Fintype.card_congr e.symm
 have h₂:2∣pb.dim*(pb.dim-1):=pb.dim.even_mul_pred_self.two_dvd
 have hne:((2:ℕ):ℚ)≠0:=by simp
 have hle:1 ≤ pb.dim:=by
   rw [←hn,Nat.one_le_iff_ne_zero, ←zero_lt_iff,Module.finrank_pos_iff]
   infer_instance
 rw [hn,Nat.cast_div h₂ hne,Nat.cast_mul,Nat.cast_sub hle]
 ring
theorem discr_powerBasis_eq_norm [Algebra.IsSeparable K L]:
   discr K pb.basis=
     (-1)^(n*(n-1)/2)*
     norm K (aeval pb.gen (minpoly K pb.gen).derivative):=by
 let E:=AlgebraicClosure L
 letI:=fun a b:E => Classical.propDecidable (Eq a b)
 have e:Fin pb.dim ≃ (L →ₐ[K] E):=by
   refine equivOfCardEq ?_
   rw [Fintype.card_fin,AlgHom.card]
   exact (PowerBasis.finrank pb).symm
 have hnodup:((minpoly K pb.gen).aroots E).Nodup:=
   nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
 have hroots:∀ σ:L →ₐ[K] E,σ pb.gen∈(minpoly K pb.gen).aroots E:=by
   intro σ
   rw [mem_roots,IsRoot.def,eval_map_algebraMap,aeval_algHom_apply]
   repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
 apply (algebraMap K E).injective
 rw [map_mul,map_pow,map_neg,map_one,discr_powerBasis_eq_prod'' _ _ _ e]
 congr
 rw [norm_eq_prod_embeddings,prod_prod_Ioi_mul_eq_prod_prod_off_diag]
 conv_rhs =>
   congr
   rfl
   ext σ
   rw [←aeval_algHom_apply, ←eval_map_algebraMap, ←derivative_map,
     (IsAlgClosed.splits _).eval_root_derivative ((minpoly.monic pb.isIntegral_gen).map _)
     (hroots σ), ←Finset.prod_mk _ (hnodup.erase _)]
 rw [Finset.prod_sigma',Finset.prod_sigma']
 refine prod_bij' (fun i _↦⟨e i.2,e i.1 pb.gen⟩)
   (fun σ hσ↦⟨e.symm (PowerBasis.lift pb σ.2 ?_),e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _↦by simp)
   <;> simp only [mem_sigma,mem_univ,Finset.mem_mk,hnodup.mem_erase_iff,IsRoot.def,
     mem_roots',mem_singleton,true_and,mem_compl,Sigma.forall,Equiv.apply_symm_apply,
     PowerBasis.lift_gen,implies_true,Equiv.symm_apply_apply,
     Sigma.ext_iff,Equiv.symm_apply_eq,heq_eq_eq,and_true] at*
 · simpa only [aeval_def,eval₂_eq_eval_map] using hσ.2.2
 · exact fun a b hba↦⟨fun h↦hba <| e.injective <| pb.algHom_ext h.symm,hroots _⟩
 · rintro a b hba ha
   rw [ha,PowerBasis.lift_gen] at hba
   exact hba.1 rfl
 · exact fun a b _↦pb.algHom_ext <| pb.lift_gen _ _
section Integral
variable {R:Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
theorem discr_isIntegral {b:ι → L} (h:∀ i,IsIntegral R (b i)):IsIntegral R (discr K b):=by
 classical
 rw [discr_def]
 exact IsIntegral.det fun i j↦isIntegral_trace ((h i).mul (h j))
theorem discr_mul_isIntegral_mem_adjoin [Algebra.IsSeparable K L] [IsIntegrallyClosed R]
   [IsFractionRing R K] {B:PowerBasis K L} (hint:IsIntegral R B.gen) {z:L}
   (hz:IsIntegral R z):discr K B.basis • z∈adjoin R ({B.gen}:Set L):=by
 have hinv:IsUnit (traceMatrix K B.basis).det:=by
   simpa [←discr_def] using discr_isUnit_of_basis _ B.basis
 have H:
   (traceMatrix K B.basis).det • (traceMatrix K B.basis)*ᵥ (B.basis.equivFun z)=
     (traceMatrix K B.basis).det • fun i => trace K L (z*B.basis i):=by
   congr;exact traceMatrix_of_basis_mulVec _ _
 have cramer:=mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z*B.basis i)
 suffices ∀ i,((traceMatrix K B.basis).det • B.basis.equivFun z) i∈(⊥:Subalgebra R K) by
   rw [←B.basis.sum_repr z,Finset.smul_sum]
   refine Subalgebra.sum_mem _ fun i _ => ?_
   replace this:=this i
   rw [←discr_def,Pi.smul_apply,mem_bot] at this
   obtain ⟨r,hr⟩:=this
   rw [Basis.equivFun_apply] at hr
   rw [←smul_assoc, ←hr,algebraMap_smul]
   refine Subalgebra.smul_mem _ ?_ _
   rw [B.basis_eq_pow i]
   exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
 intro i
 rw [←H, ←mulVec_smul] at cramer
 replace cramer:=congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
 rw [mulVec_mulVec,nonsing_inv_mul _ hinv,mulVec_mulVec,nonsing_inv_mul _ hinv,one_mulVec,
   one_mulVec] at cramer
 rw [←congr_fun cramer i,cramer_apply,det_apply]
 refine
   Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
 by_cases hji:j=i
 · simp only [updateCol_apply,hji,PowerBasis.coe_basis]
   exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
 · simp only [updateCol_apply,hji,PowerBasis.coe_basis]
   exact mem_bot.2
     (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))
end Integral
end Field
section Int
theorem discr_eq_discr (b:Basis ι ℤ A) (b':Basis ι ℤ A):
   Algebra.discr ℤ b=Algebra.discr ℤ b':=by
 convert! Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
 · rw [Basis.toMatrix_map_vecMul]
 · suffices IsUnit (b'.toMatrix b).det by
     rw [Int.isUnit_iff, ←sq_eq_one_iff] at this
     rw [this,one_mul]
   rw [←LinearMap.toMatrix_id_eq_basis_toMatrix b b']
   exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ A) b b'
end Int
end Discr
end Algebra
end ProximityFlatProofPort
end PackedLegacy_T1

/-! Packed from ProximityPrize.SubmissionLower.IM. -/
section PackedLegacy_IM
section ProximityFlatProofPort
open Module
open scoped nonZeroDivisors
variable (R:Type*) {S:Type*} [CommRing R] [CommRing S] [Algebra R S]
 {Rₘ Sₘ:Type*} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
 (M:Submonoid R)
 [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
 [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
include M
open Algebra
theorem Algebra.map_leftMulMatrix_localization {ι:Type*} [Fintype ι] [DecidableEq ι]
   (b:Basis ι R S) (a:S):
   (algebraMap R Rₘ).mapMatrix (leftMulMatrix b a)=
   leftMulMatrix (b.localizationLocalization Rₘ M Sₘ) (algebraMap S Sₘ a):=by
 ext i j
 simp only [Matrix.map_apply,RingHom.mapMatrix_apply,leftMulMatrix_eq_repr_mul, ←map_mul,
   Basis.localizationLocalization_apply,Basis.localizationLocalization_repr_algebraMap]
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a:S):
   Algebra.norm Rₘ (algebraMap S Sₘ a)=algebraMap R Rₘ (Algebra.norm R a):=by
 cases subsingleton_or_nontrivial R
 · haveI:Subsingleton Rₘ:=Module.subsingleton R Rₘ
   simp [eq_iff_true_of_subsingleton]
 let b:=Module.Free.chooseBasis R S
 letI:=Classical.decEq (Module.Free.ChooseBasisIndex R S)
 rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M Sₘ),
   Algebra.norm_eq_matrix_det b,RingHom.map_det, ←Algebra.map_leftMulMatrix_localization]
variable {M} in
lemma Algebra.norm_eq_iff [Module.Free R S] [Module.Finite R S] {a:S} {b:R}
   (hM:M ≤ nonZeroDivisors R):Algebra.norm R a=b ↔
     (Algebra.norm Rₘ) ((algebraMap S Sₘ) a)=algebraMap R Rₘ b:=
 ⟨fun h↦h.symm ▸ Algebra.norm_localization _ M _,fun h↦
   IsLocalization.injective Rₘ hM <| h.symm ▸ (Algebra.norm_localization R M a).symm⟩
theorem Algebra.trace_localization [Module.Free R S] [Module.Finite R S] (a:S):
   Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a)=algebraMap R Rₘ (Algebra.trace R S a):=by
 cases subsingleton_or_nontrivial R
 · haveI:Subsingleton Rₘ:=Module.subsingleton R Rₘ
   simp [eq_iff_true_of_subsingleton]
 let b:=Module.Free.chooseBasis R S
 letI:=Classical.decEq (Module.Free.ChooseBasisIndex R S)
 rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ M Sₘ),
   Algebra.trace_eq_matrix_trace b, ←Algebra.map_leftMulMatrix_localization]
 exact (AddMonoidHom.map_trace (algebraMap R Rₘ).toAddMonoidHom _).symm
section LocalizationLocalization
variable (Sₘ:Type*) [CommRing Sₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
 [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
 [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem Algebra.traceMatrix_localizationLocalization (b:Basis ι R S):
   Algebra.traceMatrix Rₘ (b.localizationLocalization Rₘ M Sₘ)=
     (algebraMap R Rₘ).mapMatrix (Algebra.traceMatrix R b):=by
 have:Module.Finite R S:=Module.Finite.of_basis b
 have:Module.Free R S:=Module.Free.of_basis b
 ext i j:2
 simp_rw [RingHom.mapMatrix_apply,Matrix.map_apply,traceMatrix_apply,traceForm_apply,
   Basis.localizationLocalization_apply, ←map_mul]
 exact Algebra.trace_localization R M _
theorem Algebra.discr_localizationLocalization (b:Basis ι R S):
   Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ)=
   algebraMap R Rₘ (Algebra.discr R b):=by
 rw [Algebra.discr_def,Algebra.discr_def,RingHom.map_det,
   Algebra.traceMatrix_localizationLocalization]
end LocalizationLocalization
end ProximityFlatProofPort
end PackedLegacy_IM

/-! Packed from ProximityPrize.SubmissionLower.IB. -/
section PackedLegacy_IB
section ProximityFlatProofPort
open Module nonZeroDivisors
variable (A K L L₂ L₃ B B₂ B₃:Type*)
 [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]
 [Algebra A B] [Algebra A B₂] [Algebra A B₃]
 [Field K] [Field L] [Field L₂] [Field L₃]
 [Algebra A K] [IsFractionRing A K]
 [Algebra K L] [Algebra A L] [IsScalarTower A K L]
 [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
 [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]
 [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
 [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
 [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]
section galois
section galRestrict'
variable {K L L₂ L₃}
omit [IsFractionRing A K]
noncomputable
def galRestrict' (f:L →ₐ[K] L₂):(B →ₐ[A] B₂):=
 (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
     (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
       (integralClosure A L₂) (fun x↦IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))
@[simp]
lemma algebraMap_galRestrict'_apply (σ:L →ₐ[K] L₂) (x:B):
   algebraMap B₂ L₂ (galRestrict' A B B₂ σ x)=σ (algebraMap B L x):=by
 simp [galRestrict',galRestrict',Subalgebra.algebraMap_eq]
@[simp]
theorem galRestrict'_id:galRestrict' A B B (.id K L)=.id A B:=by
 ext
 apply IsIntegralClosure.algebraMap_injective B A L
 simp
theorem galRestrict'_comp (σ:L →ₐ[K] L₂) (σ':L₂ →ₐ[K] L₃):
   galRestrict' A B B₃ (σ'.comp σ)=(galRestrict' A B₂ B₃ σ').comp (galRestrict' A B B₂ σ):=by
 ext x
 apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
 ext
 simp [galRestrict',Subalgebra.algebraMap_eq]
end galRestrict'
variable [Algebra.IsAlgebraic K L]
section galLift
variable {A B B₂ B₃}
noncomputable
def galLift (σ:B →ₐ[A] B₂):L →ₐ[K] L₂:=
 haveI:=(IsFractionRing.injective A K).isDomain
 haveI:=IsTorsionFree.trans_faithfulSMul A K L₂
 haveI:=IsIntegralClosure.isLocalization A K L B
 haveI H:∀ (y:Algebra.algebraMapSubmonoid B A⁰),
     IsUnit (((algebraMap B₂ L₂).comp σ) (y:B)):=by
   rintro ⟨_,x,hx,rfl⟩
   simpa only [RingHom.coe_comp,RingHom.coe_coe,Function.comp_apply,AlgHom.commutes,
     isUnit_iff_ne_zero,ne_eq,map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
     ←IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
 haveI H_eq:(IsLocalization.lift (S:=L) H).comp (algebraMap K L)=(algebraMap K L₂):=by
   apply IsLocalization.ringHom_ext A⁰
   ext
   simp only [RingHom.coe_comp,Function.comp_apply, ←IsScalarTower.algebraMap_apply A K L,
     ←IsScalarTower.algebraMap_apply A K L₂,
     IsScalarTower.algebraMap_apply A B L,IsScalarTower.algebraMap_apply A B₂ L₂,
     IsLocalization.lift_eq,RingHom.coe_coe,AlgHom.commutes]
 { IsLocalization.lift (S:=L) H with commutes':=DFunLike.congr_fun H_eq}
omit [IsIntegralClosure B₂ A L₂] in
@[simp]
theorem galLift_algebraMap_apply (σ:B →ₐ[A] B₂) (x:B):
   galLift K L L₂ σ (algebraMap B L x)=algebraMap B₂ L₂ (σ x):=by
 simp [galLift]
@[simp]
theorem galLift_id:galLift K L L (.id A B)=.id K L:=by
 ext;simp [galLift]
omit [IsIntegralClosure B₃ A L₃] in
theorem galLift_comp [Algebra.IsAlgebraic K L₂] (σ:B →ₐ[A] B₂) (σ':B₂ →ₐ[A] B₃):
   galLift K L L₃ (σ'.comp σ)=(galLift K L₂ L₃ σ').comp (galLift K L L₂ σ):=
 have:=(IsFractionRing.injective A K).isDomain
 have:=IsIntegralClosure.isLocalization A K L B
 AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
   <| RingHom.ext fun x↦by simp
@[simp]
theorem galLift_galRestrict' (σ:L →ₐ[K] L₂):
   galLift K L L₂ (galRestrict' A B B₂ σ)=σ:=
 have:=(IsFractionRing.injective A K).isDomain
 have:=IsIntegralClosure.isLocalization A K L B
 AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
   <| RingHom.ext fun x↦by simp [galRestrict',Subalgebra.algebraMap_eq,galLift]
@[simp]
theorem galRestrict'_galLift (σ:B →ₐ[A] B₂):
   galRestrict' A B B₂ (galLift K L L₂ σ)=σ:=
 have:=(IsFractionRing.injective A K).isDomain
 have:=IsIntegralClosure.isLocalization A K L B
 AlgHom.ext fun x↦IsIntegralClosure.algebraMap_injective B₂ A L₂
   (by simp)
@[simps!-fullyApplied apply symm_apply]
noncomputable
def galLiftEquiv [Algebra.IsAlgebraic K L₂] (σ:B ≃ₐ[A] B₂):L ≃ₐ[K] L₂:=
 AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
 (by simp [←galLift_comp]) (by simp [←galLift_comp])
theorem galLiftEquiv_algebraMap_apply [Algebra.IsAlgebraic K L₂] (σ:B ≃ₐ[A] B₂) (x:B):
   galLiftEquiv K L L₂ σ (algebraMap B L x)=algebraMap B₂ L₂ (σ x):=by
 simp [galLiftEquiv]
end galLift
@[simps-isSimp]
noncomputable
def galRestrictHom:(L →ₐ[K] L) ≃*(B →ₐ[A] B) where
 toFun f:=galRestrict' A B B f
 map_mul' σ₁ σ₂:=galRestrict'_comp _ _ _ _ σ₂ σ₁
 invFun:=galLift K L L
 left_inv σ:=galLift_galRestrict' _ _ _ σ
 right_inv σ:=galRestrict'_galLift _ _ _ σ
@[simp]
lemma algebraMap_galRestrictHom_apply (σ:L →ₐ[K] L) (x:B):
   algebraMap B L (galRestrictHom A K L B σ x)=σ (algebraMap B L x):=
 algebraMap_galRestrict'_apply _ _ _ _ _
@[simp,nolint unusedHavesSuffices]
lemma galRestrictHom_symm_algebraMap_apply (σ:B →ₐ[A] B) (x:B):
   (galRestrictHom A K L B).symm σ (algebraMap B L x)=algebraMap B L (σ x):=
 galLift_algebraMap_apply _ _ _ _ _
noncomputable
def galRestrict:Gal(L/K) ≃*(B ≃ₐ[A] B):=
 (AlgEquiv.algHomUnitsEquiv K L).symm.trans
   ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))
variable {K L}
lemma coe_galRestrict_apply (σ:Gal(L/K)):
   (galRestrict A K L B σ:B →ₐ[A] B)=galRestrictHom A K L B σ:=rfl
variable {B}
lemma galRestrict_apply (σ:Gal(L/K)) (x:B):
   galRestrict A K L B σ x=galRestrictHom A K L B σ x:=rfl
lemma algebraMap_galRestrict_apply (σ:Gal(L/K)) (x:B):
   algebraMap B L (galRestrict A K L B σ x)=σ (algebraMap B L x):=
 algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x
variable (K) in
lemma galRestrict_symm_algebraMap_apply (σ:B ≃ₐ[A] B) (x:B):
   (galRestrict A K L B).symm σ (algebraMap B L x)=algebraMap B L (σ x):=
 galRestrictHom_symm_algebraMap_apply A K L B σ x
end galois
variable [FiniteDimensional K L]
lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x:B):
   (∏ σ:Gal(L/K),galRestrict A K L B σ x)=
   algebraMap A B (IsIntegralClosure.mk' (R:=A) A (Algebra.norm K <| algebraMap B L x)
     (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral A L x).algebraMap)):=by
 apply IsIntegralClosure.algebraMap_injective B A L
 rw [←IsScalarTower.algebraMap_apply,IsScalarTower.algebraMap_eq A K L]
 simp only [map_prod,algebraMap_galRestrict_apply,IsIntegralClosure.algebraMap_mk',
   Algebra.norm_eq_prod_automorphisms,RingHom.coe_comp,Function.comp_apply]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
noncomputable
instance (priority:=900) [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
   [Module.Finite A B] [IsTorsionFree A B]:Fintype (B ≃ₐ[A] B):=
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 haveI:IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B):=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 Fintype.ofEquiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv
variable {Aₘ Bₘ} [CommRing Aₘ] [CommRing Bₘ] [Algebra Aₘ Bₘ] [Algebra A Aₘ] [Algebra B Bₘ]
 [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
 (M:Submonoid A) [IsLocalization M Aₘ]
 [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]
section trace
noncomputable
def Algebra.intTraceAux [IsIntegrallyClosed A]:
   B →ₗ[A] A:=
 (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
   ((((Algebra.trace K L).restrictScalars A).comp
     (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
       (Subalgebra.toSubmodule <| integralClosure A K) (fun x↦isIntegral_trace
         (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))
variable {A K L B}
lemma Algebra.map_intTraceAux [IsIntegrallyClosed A] (x:B):
   algebraMap A K (Algebra.intTraceAux A K L B x)=Algebra.trace K L (algebraMap B L x):=
 IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _
variable (A B)
 [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
 [Module.Finite A B] [IsTorsionFree A B]
noncomputable
def Algebra.intTrace:B →ₗ[A] A:=
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 haveI:IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B):=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 Algebra.intTraceAux A (FractionRing A) (FractionRing B) B
variable {A B}
lemma Algebra.algebraMap_intTrace (x:B):
   algebraMap A K (Algebra.intTrace A B x)=Algebra.trace K L (algebraMap B L x):=by
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 haveI:IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B):=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 haveI:=IsIntegralClosure.isFractionRing_of_finite_extension A K L B
 apply (FractionRing.algEquiv A K).symm.injective
 rw [AlgEquiv.commutes,Algebra.intTrace,Algebra.map_intTraceAux,
   ←AlgEquiv.commutes (FractionRing.algEquiv B L)]
 apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
   (FractionRing.algEquiv B L).toRingEquiv
 ext
 exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
lemma Algebra.algebraMap_intTrace_fractionRing (x:B):
   algebraMap A (FractionRing A) (Algebra.intTrace A B x)=
     Algebra.trace (FractionRing A) (FractionRing B) (algebraMap B _ x):=by
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 haveI:IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B):=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 exact Algebra.map_intTraceAux x
variable (A B)
lemma Algebra.intTrace_eq_trace [Module.Free A B]:Algebra.intTrace A B=Algebra.trace A B:=by
 ext x
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 haveI:IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B):=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 apply IsFractionRing.injective A (FractionRing A)
 rw [Algebra.algebraMap_intTrace_fractionRing,Algebra.trace_localization A A⁰]
open nonZeroDivisors
variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
 [IsTorsionFree Aₘ Bₘ] [Module.Finite Aₘ Bₘ]
include M in
lemma Algebra.intTrace_eq_of_isLocalization
   (x:B):
   algebraMap A Aₘ (Algebra.intTrace A B x)=Algebra.intTrace Aₘ Bₘ (algebraMap B Bₘ x):=by
 by_cases hM:0∈M
 · subsingleton [IsLocalization.uniqueOfZeroMem (S:=Aₘ) hM]
 replace hM:M ≤ A⁰:=fun x hx↦mem_nonZeroDivisors_iff_ne_zero.mpr (fun e↦hM (e ▸ hx))
 let K:=FractionRing A
 let L:=FractionRing B
 have:IsIntegralClosure B A L:=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 haveI:Algebra.IsAlgebraic (FractionRing A) (FractionRing B):=
   isAlgebraic_of_isFractionRing A B ..
 have:IsLocalization (algebraMapSubmonoid B A⁰) L:=
   IsIntegralClosure.isLocalization _ (FractionRing A) _ _
 let f:Aₘ →+*K:=IsLocalization.map _ (T:=A⁰) (RingHom.id A) hM
 letI:=f.toAlgebra
 have:IsScalarTower A Aₘ K:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 letI:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
 let g:Bₘ →+*L:=IsLocalization.map _
     (M:=algebraMapSubmonoid B M) (T:=algebraMapSubmonoid B A⁰)
     (RingHom.id B) (Submonoid.monotone_map hM)
 letI:=g.toAlgebra
 have:IsScalarTower B Bₘ L:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 letI:=((algebraMap K L).comp f).toAlgebra
 have:IsScalarTower Aₘ K L:=IsScalarTower.of_algebraMap_eq' rfl
 have:IsScalarTower Aₘ Bₘ L:=by
   apply IsScalarTower.of_algebraMap_eq'
   apply IsLocalization.ringHom_ext M
   rw [RingHom.algebraMap_toAlgebra,RingHom.algebraMap_toAlgebra (R:=Bₘ),RingHom.comp_assoc,
     RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq,IsScalarTower.algebraMap_eq A B Bₘ,
     IsLocalization.map_comp,RingHom.comp_id, ←RingHom.comp_assoc,IsLocalization.map_comp,
     RingHom.comp_id, ←IsScalarTower.algebraMap_eq, ←IsScalarTower.algebraMap_eq]
 letI:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
   (algebraMapSubmonoid B M) Bₘ L
 have:FiniteDimensional K L:=.of_isLocalization A B A⁰
 have:IsIntegralClosure Bₘ Aₘ L:=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 apply IsFractionRing.injective Aₘ K
 rw [←IsScalarTower.algebraMap_apply,Algebra.algebraMap_intTrace_fractionRing,
   Algebra.algebraMap_intTrace (L:=L), ←IsScalarTower.algebraMap_apply]
end trace
section norm
variable [IsIntegrallyClosed A]
noncomputable
def Algebra.intNormAux:
   B →*A where
 toFun:=fun s↦IsIntegralClosure.mk' (R:=A) A (Algebra.norm K (algebraMap B L s))
   (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
     (IsIntegralClosure.isIntegral A L s))
 map_one':=by simp
 map_mul':=fun x y↦by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _
variable {A K L B}
omit [FiniteDimensional K L] in
lemma Algebra.map_intNormAux (x:B):
   algebraMap A K (Algebra.intNormAux A K L B x)=Algebra.norm K (algebraMap B L x):=by
 dsimp [Algebra.intNormAux]
 exact IsIntegralClosure.algebraMap_mk' _ _ _
variable (A B)
 [IsDomain A] [IsDomain B] [IsIntegrallyClosed B] [Algebra.IsIntegral A B]
 [IsTorsionFree A B]
noncomputable
def Algebra.intNorm:B →*A:=Algebra.intNormAux A (FractionRing A) (FractionRing B) B
variable {A B}
lemma Algebra.algebraMap_intNorm (x:B):
   algebraMap A K (Algebra.intNorm A B x)=Algebra.norm K (algebraMap B L x):=by
 haveI:=IsIntegralClosure.isFractionRing_of_finite_extension A K L B
 apply (FractionRing.algEquiv A K).symm.injective
 rw [AlgEquiv.commutes,Algebra.intNorm,Algebra.map_intNormAux,
   ←AlgEquiv.commutes (FractionRing.algEquiv B L)]
 apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
   (FractionRing.algEquiv B L).toRingEquiv
 ext
 exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
@[simp]
lemma Algebra.algebraMap_intNorm_fractionRing (x:B):
   algebraMap A (FractionRing A) (Algebra.intNorm A B x)=
     Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) x):=
 Algebra.map_intNormAux x
variable (A B)
theorem Algebra.intNorm_intNorm {C:Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
   [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.IsIntegral A C]
   [Algebra.IsIntegral B C] [IsTorsionFree A C] [IsTorsionFree B C] (x:C):
   intNorm A B (intNorm B C x)=intNorm A C x:=by
 apply FaithfulSMul.algebraMap_injective A (FractionRing A)
 rw [algebraMap_intNorm_fractionRing,algebraMap_intNorm_fractionRing,
   algebraMap_intNorm_fractionRing,Algebra.norm_norm]
lemma Algebra.intNorm_eq_norm [Module.Free A B] [Module.Finite A B]:
   Algebra.intNorm A B=Algebra.norm A:=by
 ext x
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 apply IsFractionRing.injective A (FractionRing A)
 rw [Algebra.algebraMap_intNorm_fractionRing,Algebra.norm_localization A A⁰]
@[simp]
lemma Algebra.intNorm_zero [FiniteDimensional (FractionRing A) (FractionRing B)]:
   Algebra.intNorm A B 0=0:=by
 haveI:IsIntegralClosure B A (FractionRing B):=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 apply IsFractionRing.injective A (FractionRing A)
 simp
variable {A B}
attribute [local instance] FractionRing.liftAlgebra
@[simp]
theorem Algebra.intNorm_map_algEquiv [IsDomain B₂] [IsIntegrallyClosed B₂] [Algebra.IsIntegral A B₂]
   [IsTorsionFree A B₂] [Algebra.IsAlgebraic (FractionRing A) (FractionRing B)]
   [Algebra.IsAlgebraic (FractionRing A) (FractionRing B₂)]
   (x:B) (σ:B ≃ₐ[A] B₂):
   Algebra.intNorm A B₂ (σ x)=Algebra.intNorm A B x:=by
 apply FaithfulSMul.algebraMap_injective A (FractionRing A)
 rw [algebraMap_intNorm_fractionRing,algebraMap_intNorm_fractionRing,
   ←galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B),norm_eq_of_algEquiv]
@[simp]
lemma Algebra.intNorm_eq_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x:B}:
   Algebra.intNorm A B x=0 ↔ x=0:=by
 rw [←(IsFractionRing.injective A (FractionRing A)).eq_iff,
   ←(IsFractionRing.injective B (FractionRing B)).eq_iff]
 simp only [algebraMap_intNorm_fractionRing,map_zero,norm_eq_zero_iff]
lemma Algebra.intNorm_ne_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x:B}:
   Algebra.intNorm A B x≠0 ↔ x≠0:=by simp
variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
 [IsTorsionFree Aₘ Bₘ] [Algebra.IsIntegral Aₘ Bₘ]
include M in
lemma Algebra.intNorm_eq_of_isLocalization [FiniteDimensional (FractionRing A) (FractionRing B)]
   (x:B):
   algebraMap A Aₘ (Algebra.intNorm A B x)=Algebra.intNorm Aₘ Bₘ (algebraMap B Bₘ x):=by
 by_cases hM:0∈M
 · subsingleton [IsLocalization.uniqueOfZeroMem (S:=Aₘ) hM]
 replace hM:M ≤ A⁰:=fun x hx↦mem_nonZeroDivisors_iff_ne_zero.mpr (fun e↦hM (e ▸ hx))
 let K:=FractionRing A
 let L:=FractionRing B
 let f:Aₘ →+*K:=IsLocalization.map _ (T:=A⁰) (RingHom.id A) hM
 letI:=f.toAlgebra
 have:IsScalarTower A Aₘ K:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 letI:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
 let g:Bₘ →+*L:=IsLocalization.map _
     (M:=algebraMapSubmonoid B M) (T:=algebraMapSubmonoid B A⁰)
     (RingHom.id B) (Submonoid.monotone_map hM)
 letI:=g.toAlgebra
 have:IsScalarTower B Bₘ L:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 letI:=((algebraMap K L).comp f).toAlgebra
 have:IsScalarTower Aₘ K L:=IsScalarTower.of_algebraMap_eq' rfl
 have:IsScalarTower Aₘ Bₘ L:=by
   apply IsScalarTower.of_algebraMap_eq'
   apply IsLocalization.ringHom_ext M
   rw [RingHom.algebraMap_toAlgebra,RingHom.algebraMap_toAlgebra (R:=Bₘ),RingHom.comp_assoc,
     RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq,IsScalarTower.algebraMap_eq A B Bₘ,
     IsLocalization.map_comp,RingHom.comp_id, ←RingHom.comp_assoc,IsLocalization.map_comp,
     RingHom.comp_id, ←IsScalarTower.algebraMap_eq, ←IsScalarTower.algebraMap_eq]
 letI:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
   (algebraMapSubmonoid B M) Bₘ L
 have:IsIntegralClosure Bₘ Aₘ L:=
   IsIntegralClosure.of_isIntegrallyClosed _ _ _
 apply IsFractionRing.injective Aₘ K
 rw [←IsScalarTower.algebraMap_apply,Algebra.algebraMap_intNorm_fractionRing,
   Algebra.algebraMap_intNorm (L:=L), ←IsScalarTower.algebraMap_apply]
end norm
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
 [Module.Finite A B] [IsTorsionFree A B]
lemma Algebra.algebraMap_intNorm_of_isGalois [IsGalois (FractionRing A) (FractionRing B)] {x:B}:
   algebraMap A B (Algebra.intNorm A B x)=∏ σ:B ≃ₐ[A] B,σ x:=by
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 rw [←(galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
 simp only [MulEquiv.toEquiv_eq_coe,EquivLike.coe_coe]
 convert! (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm
open Polynomial IsScalarTower in
theorem Algebra.dvd_algebraMap_intNorm_self (x:B):x∣algebraMap A B (intNorm A B x):=by
 classical
 letI:DecidableEq B:=Classical.decEq B
 haveI:FiniteDimensional (FractionRing A) (FractionRing B):=.of_isLocalization A B A⁰
 by_cases hx:x=0
 · exact ⟨1,by simp [hx]⟩
 let K:=FractionRing A
 let L:=FractionRing B
 let E:=AlgebraicClosure L
 suffices IsIntegral A ((algebraMap B L x)⁻¹*(algebraMap A L (intNorm A B x))) by
   obtain ⟨y,hy⟩:=IsIntegrallyClosed.isIntegral_iff.mp <|
     _root_.IsIntegral.tower_top (A:=B) this
   refine ⟨y,?_⟩
   apply FaithfulSMul.algebraMap_injective B L
   rw [←algebraMap_apply,map_mul,hy,mul_inv_cancel_left₀]
   exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
 rw [←isIntegral_algHom_iff (toAlgHom A L E)
   (FaithfulSMul.algebraMap_injective L E),coe_toAlgHom',map_mul,map_inv₀,
   algebraMap_apply A K L,algebraMap_intNorm (L:=L), ←algebraMap_apply, ←algebraMap_apply,
   norm_eq_prod_roots _ (IsAlgClosed.splits _), ←Multiset.prod_erase
   (a:=algebraMap B E x)]
 · have:=IsTorsionFree.trans_faithfulSMul B L E
   rw [mul_pow, ←mul_pow_sub_one (Nat.pos_iff_ne_zero.1 Module.finrank_pos) (algebraMap B E x),
     mul_assoc,inv_mul_cancel_left₀]
   · refine IsIntegral.mul (IsIntegral.pow ?_ _)
       (IsIntegral.pow (IsIntegral.multiset_prod (fun a ha↦⟨minpoly A x,minpoly.monic
         (IsIntegral.isIntegral x),?_⟩)) _)
     · exact (isIntegral_algebraMap_iff (isTorsionFree_iff_algebraMap_injective.1 this)).mpr
         (IsIntegral.isIntegral x)
     · replace ha:=Multiset.erase_subset _ _ ha
       suffices (aeval a) ((minpoly A x).map (algebraMap A K))=0 by simpa
       rw [←minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.isIntegral x)]
       simp only [mem_roots',ne_eq,Polynomial.map_eq_zero,IsRoot.def,eval_map_algebraMap] at ha
       exact ha.2
   · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
 · simp only [mem_roots',ne_eq,Polynomial.map_eq_zero,IsRoot.def,eval_map_algebraMap]
   refine ⟨minpoly.ne_zero (IsIntegral.isIntegral _),?_⟩
   simp [algebraMap_apply B L E,aeval_algebraMap_apply]
end ProximityFlatProofPort
end PackedLegacy_IB

/-! Packed from ProximityPrize.SubmissionLower.IC. -/
section PackedLegacy_IC
section ProximityFlatProofPort
open scoped Pointwise
section Galois
variable (A K L B:Type*) [CommRing A] [CommRing B] [Field K] [Field L]
 [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
 [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
 [IsIntegrallyClosed A] [IsIntegralClosure B A L]
@[implicit_reducible]
noncomputable def IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L]:
   MulSemiringAction Gal(L/K) B:=
 MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom
instance [Algebra.IsAlgebraic K L]:let:=IsIntegralClosure.MulSemiringAction A K L B
   SMulDistribClass Gal(L/K) B L:=
 let:=IsIntegralClosure.MulSemiringAction A K L B
 ⟨fun g b l↦by
   simp only [Algebra.smul_def,smul_mul',mul_eq_mul_right_iff]
   exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h:IsGalois K L]:
   letI:=IsIntegralClosure.MulSemiringAction A K L B
   Algebra.IsInvariant A B Gal(L/K):=by
 replace h:=((IsGalois.tfae (F:=K) (E:=L)).out 0 1).mp h
 letI:=IsIntegralClosure.MulSemiringAction A K L B
 refine ⟨fun b hb↦?_⟩
 replace hb:algebraMap B L b∈IntermediateField.fixedField (⊤:Subgroup Gal(L/K)):=by
   rintro ⟨g, -⟩
   exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
 rw [h,IntermediateField.mem_bot] at hb
 obtain ⟨k,hk⟩:=hb
 have hb:IsIntegral A b:=IsIntegralClosure.isIntegral A L b
 rw [←isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L), ←hk,
   isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
 obtain ⟨a,rfl⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral hb
 rw [←IsScalarTower.algebraMap_apply,IsScalarTower.algebraMap_apply A B L,
   (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
 exact ⟨a,hk⟩
theorem Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L]:
   Algebra.IsInvariant A B (B ≃ₐ[A] B):=
 ⟨fun b h↦(isInvariant_of_isGalois A K L B).1 b (fun g↦h (galRestrict A K L B g))⟩
end Galois
section normal
variable {A B:Type*} [CommRing A] [CommRing B] [Algebra A B]
 (G:Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
 (P:Ideal A) (Q:Ideal B) [Q.LiesOver P]
namespace Ideal.IsFractionRing
variable [P.IsPrime] [Q.IsPrime] (K L:Type*) [Field K] [Field L] [Algebra K L]
   [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
   [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L] [IsScalarTower (A ⧸ P) K L]
open Polynomial in
include P Q G in
lemma normal:Normal K L:=by
 have:=Algebra.IsInvariant.isIntegral A B G
 have:=isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
 constructor
 intro x
 obtain ⟨x,y,hy,rfl⟩:=IsFractionRing.div_surjective (B ⧸ Q) x
 obtain ⟨b,a,ha,h⟩:=(Algebra.IsAlgebraic.isAlgebraic (R:=A ⧸ P) y).exists_smul_eq_mul x hy
 obtain ⟨a,rfl⟩:=Quotient.mk_surjective a
 obtain ⟨b,rfl⟩:=Quotient.mk_surjective b
 simp_rw [←Quotient.algebraMap_eq] at*
 cases nonempty_fintype G
 obtain ⟨p,hp, -,h_monic⟩:=lifts_and_natDegree_eq_and_monic
   (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
 have h_eval:p.aeval b=0:=by
   rw [←eval_map_algebraMap,hp,MulSemiringAction.eval_charpoly]
 let q:=p.comp (C a*_root_.Polynomial.X)
 let d:=(algebraMap (B ⧸ Q) L) x/(algebraMap (B ⧸ Q) L) y
 have comm₁:(algebraMap K L).comp (algebraMap (A ⧸ P) K)=
     (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)):=by
   simp_rw [←IsScalarTower.algebraMap_eq]
 have comm₂:(algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P))=
     (algebraMap B (B ⧸ Q)).comp (algebraMap A B):=by
   simp_rw [←IsScalarTower.algebraMap_eq]
 replace h_eval:((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d=0:=by
   simp_rw [q,map_comp,Polynomial.map_mul,map_C,map_X,aeval_comp,aeval_mul,aeval_C,aeval_X,
     ←RingHom.comp_apply, ←RingHom.comp_assoc,comm₁,RingHom.comp_apply,d,mul_div, ←map_mul]
   rw [←Algebra.smul_def,h,map_mul,mul_div_cancel_left₀ _ (by simpa using hy),
     aeval_map_algebraMap,aeval_algebraMap_apply,aeval_map_algebraMap,aeval_algebraMap_apply,
     h_eval,map_zero,map_zero]
 replace h_splits:(p.map (algebraMap A B)).Splits:=by
   rw [hp]
   exact MulSemiringAction.splits_charpoly G b
 refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
 · simp_rw [q,map_comp,Polynomial.map_mul,map_C,map_X]
   refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
   rw [Polynomial.map_map,Polynomial.map_map,comm₁,RingHom.comp_assoc,comm₂,
     ←RingHom.comp_assoc, ←Polynomial.map_map]
   apply h_splits.map
 · simp_rw [q,map_comp,Polynomial.map_mul,map_C,map_X,Polynomial.map_map]
   exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)
include P Q in
lemma finite_of_isInvariant [SMulCommClass G A B] [Algebra.IsSeparable K L]:
   Module.Finite K L:=by
 have:IsGalois K L:={ __:=normal G P Q K L}
 have:=Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
 apply IsGalois.finiteDimensional_of_finite
end Ideal.IsFractionRing
attribute [local instance] Ideal.Quotient.field in
include G in
lemma Ideal.Quotient.normal [P.IsMaximal] [Q.IsMaximal]:
   Normal (A ⧸ P) (B ⧸ Q):=
 IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)
attribute [local instance] Ideal.Quotient.field in
include G in
lemma Ideal.Quotient.finite_of_isInvariant [P.IsMaximal] [Q.IsMaximal]
   [SMulCommClass G A B] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]:
   Module.Finite (A ⧸ P) (B ⧸ Q):=
 IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)
end normal
end ProximityFlatProofPort
end PackedLegacy_IC

/-! Packed from ProximityPrize.SubmissionLower.U5. -/
section PackedLegacy_U5
section ProximityFlatProofPort
variable {R:Type*} [CommRing R]
namespace Ideal
open Submodule Associates
open scoped nonZeroDivisors
variable (R) in
def isPrincipalSubmonoid:Submonoid (Ideal R) where
 carrier:={I | IsPrincipal I}
 mul_mem':=by
   rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
   exact ⟨x*y,span_singleton_mul_span_singleton x y⟩
 one_mem':=⟨1,one_eq_span⟩
theorem mem_isPrincipalSubmonoid_iff {I:Ideal R}:
   I∈isPrincipalSubmonoid R ↔ IsPrincipal I:=Iff.rfl
theorem span_singleton_mem_isPrincipalSubmonoid (a:R):
   span {a}∈isPrincipalSubmonoid R:=mem_isPrincipalSubmonoid_iff.mpr ⟨a,rfl⟩
variable (R) in
def isPrincipalNonZeroDivisorsSubmonoid:Submonoid (Ideal R)⁰ where
 carrier:={I | IsPrincipal I.val}
 mul_mem':=by
   rintro ⟨_,_⟩ ⟨_,_⟩ ⟨x,rfl⟩ ⟨y,rfl⟩
   exact ⟨x*y,by
     simp_rw [Submonoid.mk_mul_mk,submodule_span_eq,span_singleton_mul_span_singleton]⟩
 one_mem':=⟨1,by simp⟩
variable [IsDomain R]
variable (R) in
noncomputable def associatesEquivIsPrincipal:
   Associates R ≃ {I:Ideal R//IsPrincipal I} where
 toFun:=_root_.Quotient.lift (fun x↦⟨span {x},x,rfl⟩)
   (fun _ _ _↦by simpa [span_singleton_eq_span_singleton])
 invFun I:=.mk I.2.generator
 left_inv:=Quotient.ind fun (x:R)↦by
   exact Associates.mk_eq_mk_iff_associated.mpr
     (Ideal.span_singleton_eq_span_singleton.mp
       (@Ideal.span_singleton_generator R _ (Ideal.span {x}) ⟨x,rfl⟩))
 right_inv I:=by simp only [_root_.Quotient.lift_mk,span_singleton_generator,Subtype.coe_eta]
@[simp]
theorem associatesEquivIsPrincipal_apply (x:R):
   associatesEquivIsPrincipal R (.mk x)=span {x}:=rfl
@[simp]
theorem associatesEquivIsPrincipal_symm_apply {I:Ideal R} (hI:IsPrincipal I):
   (associatesEquivIsPrincipal R).symm ⟨I,hI⟩=.mk hI.generator:=rfl
theorem associatesEquivIsPrincipal_mul (x y:Associates R):
   (associatesEquivIsPrincipal R (x*y):Ideal R)=
     (associatesEquivIsPrincipal R x)*(associatesEquivIsPrincipal R y):=by
 rw [←quot_out x, ←quot_out y]
 simp_rw [mk_mul_mk,associatesEquivIsPrincipal_apply,span_singleton_mul_span_singleton]
@[simp]
theorem associatesEquivIsPrincipal_map_zero:
   (associatesEquivIsPrincipal R 0:Ideal R)=0:=by
 rw [←mk_zero,associatesEquivIsPrincipal_apply,Submodule.zero_eq_bot,span_singleton_eq_bot]
@[simp]
theorem associatesEquivIsPrincipal_map_one:
   (associatesEquivIsPrincipal R 1:Ideal R)=1:=by
 rw [one_eq_mk_one,associatesEquivIsPrincipal_apply,span_singleton_one,one_eq_top]
set_option backward.isDefEq.respectTransparency false in
variable (R) in
noncomputable def associatesMulEquivIsPrincipal:
   Associates R ≃*isPrincipalSubmonoid R where
 __:=associatesEquivIsPrincipal R
 map_mul' _ _:=by
   rw [Subtype.ext_iff]
   erw [associatesEquivIsPrincipal_mul]
   rfl
variable (R) in
noncomputable def associatesNonZeroDivisorsEquivIsPrincipal:
   Associates R⁰ ≃ {I:(Ideal R)⁰//IsPrincipal (I:Ideal R)}:=
 calc Associates R⁰ ≃ (Associates R)⁰:=associatesNonZeroDivisorsEquiv.toEquiv.symm
   _ ≃ {I:{I:Ideal R//IsPrincipal I}//I.1∈(Ideal R)⁰}:=
     Equiv.subtypeEquiv (associatesEquivIsPrincipal R)
       (fun x↦by rw [←quot_out x,mk_mem_nonZeroDivisors_associates,
         associatesEquivIsPrincipal_apply,span_singleton_nonZeroDivisors])
   _ ≃ {I:Ideal R//IsPrincipal I∧I∈(Ideal R)⁰}:=
     Equiv.subtypeSubtypeEquivSubtypeInter (fun I↦IsPrincipal I) (fun I↦I∈(Ideal R)⁰)
   _ ≃ {I:Ideal R//I∈(Ideal R)⁰∧IsPrincipal I}:=
     .subtypeEquivProp <| by simp_rw [and_comm]
   _ ≃ {I:(Ideal R)⁰//IsPrincipal I.1}:=(Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
@[simp]
theorem associatesNonZeroDivisorsEquivIsPrincipal_apply (x:R⁰):
   associatesNonZeroDivisorsEquivIsPrincipal R (.mk x)=Ideal.span {(x:R)}:=rfl
theorem associatesNonZeroDivisorsEquivIsPrincipal_coe (x:Associates R⁰):
   (associatesNonZeroDivisorsEquivIsPrincipal R x:Ideal R)=
     (associatesEquivIsPrincipal R (associatesNonZeroDivisorsEquiv.symm x)):=rfl
theorem associatesNonZeroDivisorsEquivIsPrincipal_mul (x y:Associates R⁰):
   (associatesNonZeroDivisorsEquivIsPrincipal R (x*y):Ideal R)=
     (associatesNonZeroDivisorsEquivIsPrincipal R x)*
       (associatesNonZeroDivisorsEquivIsPrincipal R y):=by
 simp_rw [associatesNonZeroDivisorsEquivIsPrincipal_coe,map_mul,Submonoid.coe_mul,
   associatesEquivIsPrincipal_mul]
@[simp]
theorem associatesNonZeroDivisorsEquivIsPrincipal_map_one:
   (associatesNonZeroDivisorsEquivIsPrincipal R 1:Ideal R)=1:=by
 rw [associatesNonZeroDivisorsEquivIsPrincipal_coe,map_one,OneMemClass.coe_one,
   associatesEquivIsPrincipal_map_one]
set_option backward.isDefEq.respectTransparency false in
variable (R) in
noncomputable def associatesNonZeroDivisorsMulEquivIsPrincipal:
   Associates R⁰ ≃*(isPrincipalNonZeroDivisorsSubmonoid R) where
 __:=associatesNonZeroDivisorsEquivIsPrincipal R
 map_mul' _ _:=by
   rw [Subtype.ext_iff,Subtype.ext_iff,Equiv.toFun_as_coe,
     associatesNonZeroDivisorsEquivIsPrincipal_mul]
   rfl
noncomputable def isoBaseOfIsPrincipal {I:Ideal R}
   [hprinc:I.IsPrincipal] (hI:I≠⊥):R ≃ₗ[R] I:=
 letI x:=IsPrincipal.generator I
 have hx:x≠0:=by rwa [Ne, ←IsPrincipal.eq_bot_iff_generator_eq_zero]
 (LinearEquiv.toSpanNonzeroSingleton R R x hx).trans
   (LinearEquiv.ofEq (Submodule.span R {x}) I (IsPrincipal.span_singleton_generator I))
@[simp]
theorem isoBaseOfIsPrincipal_apply {I:Ideal R} [hprinc:I.IsPrincipal] (hI:I≠⊥) (x:R):
   (Ideal.isoBaseOfIsPrincipal hI) x=x*IsPrincipal.generator I:=
 rfl
theorem subtype_isoBaseOfIsPrincipal_eq_mul {I:Ideal R}
   [hprinc:I.IsPrincipal] (h:I≠⊥):
   (Submodule.subtype I).comp (Ideal.isoBaseOfIsPrincipal h).toLinearMap=
   LinearMap.mul R R (IsPrincipal.generator I):=by
 ext
 simp
end Ideal
end ProximityFlatProofPort
end PackedLegacy_U5

/-! Packed from ProximityPrize.SubmissionLower.T8. -/
section PackedLegacy_T8
section ProximityFlatProofPort
open Function (Injective Surjective)
open LinearMap (lsmul rTensor lTensor)
open Submodule (IsPrincipal torsion)
open TensorProduct
namespace Module.Flat
section Semiring
variable {R M:Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
open LinearMap in
lemma isSMulRegular_of_isRegular {r:R} (hr:IsRegular r) [Flat R M]:
   IsSMulRegular M r:=by
 have h:=Flat.rTensor_preserves_injective_linearMap (M:=M)
   (toSpanSingleton R R r) <| hr.right
 have h2:(fun (x:M)↦r • x)=
     (TensorProduct.lid R M).toLinearMap.comp
       ((rTensor M (toSpanSingleton R R r)).comp
         (TensorProduct.lid R M).symm.toLinearMap):=by ext;simp
 rw [IsSMulRegular,h2]
 simp [h,LinearEquiv.injective]
instance isTorsionFree [Flat R M]:IsTorsionFree R M:=
 ⟨fun _ hr↦isSMulRegular_of_isRegular hr⟩
end Semiring
section Ring
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
open scoped nonZeroDivisors
open LinearMap in
lemma isSMulRegular_of_nonZeroDivisors {r:R} (hr:r∈R⁰) [Flat R M]:IsSMulRegular M r:=by
 apply isSMulRegular_of_isRegular
 exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r,hr⟩
theorem torsion_eq_bot [Flat R M]:torsion R M=⊥:=by
 rw [eq_bot_iff]
 rintro m ⟨⟨r,hr⟩,h⟩
 exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)
@[stacks 0539 "Generalized valuation ring to Bezout domain"]
theorem flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R]:
   Flat R M ↔ torsion R M=⊥:=by
 refine ⟨fun _↦torsion_eq_bot,?_⟩
 intro htors
 rw [iff_lift_lsmul_comp_subtype_injective]
 rintro I hFG
 obtain (rfl | h):=eq_or_ne I ⊥
 · rintro x y-
   apply Subsingleton.elim
 ·
   have hprinc:I.IsPrincipal:=IsBezout.isPrincipal_of_FG I hFG
   have:IsPrincipal.generator I≠0:=by
     rwa [ne_eq, ←IsPrincipal.eq_bot_iff_generator_eq_zero]
   apply Function.Injective.of_comp_right _
     (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
   rw [←LinearEquiv.coe_toLinearMap, ←LinearMap.coe_comp,LinearEquiv.coe_rTensor,rTensor,
     lift_comp_map,LinearMap.compl₂_id,LinearMap.comp_assoc,
     Ideal.subtype_isoBaseOfIsPrincipal_eq_mul,LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul,
     LinearMap.coe_comp]
   rw [←Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
   refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
   rw [←Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
   convert! Function.injective_id
   ext
   simp
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain R]
   (h:∀ (P:Ideal R),[P.IsMaximal] → ValuationRing (Localization P.primeCompl)):
   Flat R M ↔ torsion R M=⊥:=by
 refine ⟨fun _↦Flat.torsion_eq_bot,fun h↦?_⟩
 apply flat_of_localized_maximal
 intro P hP
 rw [←Submodule.isTorsionFree_iff_torsion_eq_bot] at h
 rw [←flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl,
   Flat.flat_iff_torsion_eq_bot_of_isBezout, ←Submodule.isTorsionFree_iff_torsion_eq_bot]
 infer_instance
@[stacks 0AUW "(1)"]
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot [IsDedekindDomain R]:
   Flat R M ↔ torsion R M=⊥:=by
 apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
 exact fun P↦inferInstance
instance [IsDedekindDomain R] [IsTorsionFree R M]:Flat R M:=by
 rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ←Submodule.isTorsionFree_iff_torsion_eq_bot]
 infer_instance
end Ring
end Module.Flat
end ProximityFlatProofPort
end PackedLegacy_T8

/-! Packed from ProximityPrize.SubmissionLower.HD. -/
section PackedLegacy_HD
section ProximityFlatProofPort
variable {M:Type*} [CommMonoidWithZero M]
theorem IsMulTorsionFree.mk' [NoZeroDivisors M]
   (ih:∀ x≠0,∀ y≠0,∀ n≠0,(x^n:M)=y^n → x=y):
   IsMulTorsionFree M:=by
 classical
 refine ⟨fun n hn x y hxy↦?_⟩
 rcases Classical.em (x≠0∧y≠0) with h | h
 · exact ih x h.1 y h.2 n hn hxy
 have:IsReduced M:=inferInstance
 grind [eq_zero_of_pow_eq_zero,zero_pow]
variable [UniqueFactorizationMonoid M] [NormalizationMonoid M] [IsMulTorsionFree Mˣ]
namespace UniqueFactorizationMonoid
instance:IsMulTorsionFree M:=by
 refine .mk' fun x hx y hy n hn hxy↦?_
 obtain ⟨u,hu⟩:Associated x y:=by
   have:=(Associated.of_eq hxy).normalizedFactors_eq
   rwa [normalizedFactors_pow,normalizedFactors_pow,nsmul_right_inj hn,
     ←associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
 replace hx:IsLeftRegular (x^n):=(IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx).pow n
 rw [←hu,mul_pow,eq_comm,IsLeftRegular.mul_left_eq_self_iff hx, ←Units.val_pow_eq_pow_val,
   Units.val_eq_one,pow_eq_one_iff_left hn] at hxy
 rwa [hxy,Units.val_one,mul_one] at hu
end UniqueFactorizationMonoid
end ProximityFlatProofPort
end PackedLegacy_HD

/-! Packed from ProximityPrize.SubmissionLower.AR. -/
section PackedLegacy_AR
section ProximityFlatProofPort
namespace Ideal
universe u v
variable {R:Type u} [CommRing R]
 {S:Type v} [CommRing S] [Algebra R S]
 (p:Ideal R) (P:Ideal S)
local notation "f" => algebraMap R S
open Module UniqueFactorizationMonoid
attribute [local instance] Ideal.Quotient.field
section DecEq
noncomputable def ramificationIdx':ℕ:=sSup {n | map f p ≤ P^n}
variable {p P}
theorem ramificationIdx'_eq_find [DecidablePred fun n↦∀ (k:ℕ),map f p ≤ P^k → k ≤ n]
   (h:∃ n,∀ k,map f p ≤ P^k → k ≤ n):
   ramificationIdx' p P=Nat.find h:=by
 convert! Nat.sSup_def h
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_find:=ramificationIdx'_eq_find
theorem ramificationIdx'_eq_zero (h:∀ n:ℕ,∃ k,map f p ≤ P^k∧n < k):
   ramificationIdx' p P=0:=
 dif_neg (by push Not;exact h)
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_zero:=ramificationIdx'_eq_zero
theorem ramificationIdx'_spec {n:ℕ} (hle:map f p ≤ P^n) (hgt:¬map f p ≤ P^(n+1)):
   ramificationIdx' p P=n:=by
 classical
 let Q:ℕ → Prop:=fun m => ∀ k:ℕ,map f p ≤ P^k → k ≤ m
 have:Q n:=by
   intro k hk
   refine le_of_not_gt fun hnk => ?_
   exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
 rw [ramificationIdx'_eq_find ⟨n,this⟩]
 refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h:Nat.find _ < n => ?_)
 obtain this':=Nat.find_spec ⟨n,this⟩
 exact h.not_ge (this' _ hle)
@[deprecated (since:="2026-07-01")] alias ramificationIdx_spec:=ramificationIdx'_spec
theorem ramificationIdx'_lt {n:ℕ} (hgt:¬map f p ≤ P^n):ramificationIdx' p P < n:=by
 classical
 rcases n with-| n
 · simp at hgt
 · rw [Nat.lt_succ_iff]
   have:∀ k,map f p ≤ P^k → k ≤ n:=by
     refine fun k hk => le_of_not_gt fun hnk => ?_
     exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
   rw [ramificationIdx'_eq_find ⟨n,this⟩]
   exact Nat.find_min' ⟨n,this⟩ this
@[deprecated (since:="2026-07-01")] alias ramificationIdx_lt:=ramificationIdx'_lt
@[simp]
theorem ramificationIdx'_bot:ramificationIdx' (⊥:Ideal R) P=0:=
 dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))
@[deprecated (since:="2026-07-01")] alias ramificationIdx_bot:=ramificationIdx'_bot
@[simp]
theorem ramificationIdx'_of_not_le (h:¬map f p ≤ P):ramificationIdx' p P=0:=
 ramificationIdx'_spec (by simp) (by simpa using h)
@[deprecated (since:="2026-07-01")] alias ramificationIdx_of_not_le:=ramificationIdx'_of_not_le
theorem ramificationIdx'_bot' (hp:p≠⊥) (hf:Function.Injective f):
   ramificationIdx' p (⊥:Ideal S)=0:=
 ramificationIdx'_of_not_le <| le_bot_iff.not.mpr <| (map_eq_bot_iff_of_injective hf).not.mpr hp
@[deprecated (since:="2026-07-01")] alias ramificationIdx_bot':=ramificationIdx'_bot'
theorem ramificationIdx'_ne_zero {e:ℕ} (he:e≠0) (hle:map f p ≤ P^e)
   (hnle:¬map f p ≤ P^(e+1)):ramificationIdx' p P≠0:=by
 rwa [ramificationIdx'_spec hle hnle]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_ne_zero:=ramificationIdx'_ne_zero
theorem le_pow_of_le_ramificationIdx' {n:ℕ} (hn:n ≤ ramificationIdx' p P):
   map f p ≤ P^n:=by
 contrapose! hn
 exact ramificationIdx'_lt hn
@[deprecated (since:="2026-07-01")] alias le_pow_of_le_ramificationIdx:=
 le_pow_of_le_ramificationIdx'
theorem le_pow_ramificationIdx':map f p ≤ P^ramificationIdx' p P:=
 le_pow_of_le_ramificationIdx' (le_refl _)
@[deprecated (since:="2026-07-01")] alias le_pow_ramificationIdx:=le_pow_ramificationIdx'
theorem le_comap_pow_ramificationIdx':p ≤ comap f (P^ramificationIdx' p P):=
 map_le_iff_le_comap.mp le_pow_ramificationIdx'
@[deprecated (since:="2026-07-01")] alias le_comap_pow_ramificationIdx:=
 le_comap_pow_ramificationIdx'
theorem le_comap_of_ramificationIdx'_ne_zero (h:ramificationIdx' p P≠0):p ≤ comap f P:=
 Ideal.map_le_iff_le_comap.mp <| le_pow_ramificationIdx'.trans <| Ideal.pow_le_self <| h
@[deprecated (since:="2026-07-01")] alias le_comap_of_ramificationIdx_ne_zero:=
 le_comap_of_ramificationIdx'_ne_zero
variable {S₁:Type*} [CommRing S₁] [Algebra R S₁]
variable (p) in
lemma ramificationIdx'_comap_eq (e:S ≃ₐ[R] S₁) (P:Ideal S₁):
   ramificationIdx' p (P.comap e)=ramificationIdx' p P:=by
 dsimp only [ramificationIdx']
 congr 1
 ext n
 simp only [Set.mem_setOf_eq,Ideal.map_le_iff_le_comap]
 rw [←comap_coe e, ←e.toRingEquiv_toRingHom,comap_coe, ←RingEquiv.symm_symm (e:S ≃+*S₁),
   ←map_comap_of_equiv, ←Ideal.map_pow,map_comap_of_equiv, ←comap_coe (RingEquiv.symm _),
   comap_comap,RingEquiv.symm_symm,e.toRingEquiv_toRingHom, ←e.toAlgHom_toRingHom,
   AlgHom.comp_algebraMap]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_comap_eq:=ramificationIdx'_comap_eq
variable (p) in
lemma ramificationIdx'_map_eq {E:Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
   (P:Ideal S) (e:E):
   ramificationIdx' p (P.map e)=ramificationIdx' p P:=by
 rw [show P.map e=_ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e:S ≃+*S₁)]
 exact p.ramificationIdx'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P
@[deprecated (since:="2026-07-01")] alias ramificationIdx_map_eq:=ramificationIdx'_map_eq
lemma ramificationIdx'_ne_one_iff (hp:map f p ≤ P):
   ramificationIdx' p P≠1 ↔ p.map f ≤ P^2:=by
 classical
 by_cases! H:∀ n:ℕ,∃ k,p.map f ≤ P^k∧n < k
 · obtain ⟨k,hk,h2k⟩:=H 2
   simp [Ideal.ramificationIdx'_eq_zero H,hk.trans (Ideal.pow_le_pow_right h2k.le)]
 rw [Ideal.ramificationIdx'_eq_find H]
 constructor
 · intro he
   have:1 ≤ Nat.find H:=Nat.find_spec H 1 (by simpa)
   have:=Nat.find_min H (m:=1) (by lia)
   push Not at this
   obtain ⟨k,hk,h1k⟩:=this
   exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
 · intro he
   have:=Nat.find_spec H 2 he
   lia
@[deprecated (since:="2026-07-01")] alias ramificationIdx_ne_one_iff:=
 ramificationIdx'_ne_one_iff
open IsLocalRing in
lemma ramificationIdx'_eq_one_of_map_localization
   {p:Ideal R} {P:Ideal S} [P.IsPrime] [IsNoetherianRing S]
   (hpP:map (algebraMap R S) p ≤ P) (hp:P≠⊥) (hp':P.primeCompl ≤ nonZeroDivisors S)
   (H:p.map (algebraMap R (Localization.AtPrime P))=maximalIdeal (Localization.AtPrime P)):
   ramificationIdx' p P=1:=by
 rw [←not_ne_iff (b:=1),Ideal.ramificationIdx'_ne_one_iff hpP]
 intro h₂
 replace h₂:=Ideal.map_mono («f»:=algebraMap S (Localization.AtPrime P)) h₂
 rw [Ideal.map_pow,Localization.AtPrime.map_eq_maximalIdeal,Ideal.map_map,
   ←IsScalarTower.algebraMap_eq,H,pow_two] at h₂
 have:=Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
   (maximalIdeal_le_jacobson _)
 rw [←Localization.AtPrime.map_eq_maximalIdeal,Ideal.map_eq_bot_iff_of_injective] at this
 · exact hp this
 · exact IsLocalization.injective _ hp'
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_one_of_map_localization:=
 ramificationIdx'_eq_one_of_map_localization
theorem ramificationIdx'_map_self_eq_one [IsDedekindDomain S]
   (h₁:map f p≠⊤) (h₂:map f p≠⊥):ramificationIdx' p (map f p)=1:=by
 refine ramificationIdx'_spec (by simp) fun h↦?_
 have:map f p^1=(map f p)^2:=by
   rw [pow_one]
   exact le_antisymm h <| pow_le_self two_ne_zero
 have:=IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
 simp_all
@[deprecated (since:="2026-07-01")] alias ramificationIdx_map_self_eq_one:=
 ramificationIdx'_map_self_eq_one
variable (p P) in
theorem ramificationIdx'_le_ramificationIdx' {T:Type*} [CommRing T] [Algebra R T]
   [Algebra S T] [IsScalarTower R S T] (Q:Ideal T) (hp:p=comap f P)
   (h:ramificationIdx' p Q≠0):ramificationIdx' P Q ≤ ramificationIdx' p Q:=by
 simp_rw [ramificationIdx',Ne] at*
 refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn↦?_
 simp_rw [hp,IsScalarTower.algebraMap_eq R S T, ←map_map,map_le_iff_le_comap]
 exact comap_mono <| by rwa [←map_le_iff_le_comap]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_le_ramificationIdx:=
 ramificationIdx'_le_ramificationIdx'
namespace IsDedekindDomain
variable [IsDedekindDomain S]
theorem ramificationIdx'_eq_normalizedFactors_count
   (hp0:map f p≠⊥) (hP:P.IsPrime)
   (hP0:P≠⊥):ramificationIdx' p P=(normalizedFactors (map f p)).count P:=by
 have hPirr:=(Ideal.prime_of_isPrime hP0 hP).irreducible
 refine ramificationIdx'_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
   rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
     normalizedFactors_pow,normalizedFactors_irreducible hPirr,normalize_eq,
     Multiset.nsmul_singleton, ←Multiset.le_count_iff_replicate_le]
 exact (Nat.lt_succ_self _).not_ge
theorem ramificationIdx'_eq_multiplicity (hp:map f p≠⊥) (hP:P.IsPrime):
   ramificationIdx' p P=multiplicity P (Ideal.map f p):=by
 classical
 by_cases hP₂:P=⊥
 · rw [hP₂, ←Ideal.zero_eq_bot,multiplicity_zero_eq_zero_of_ne_zero _ hp]
   exact Ideal.ramificationIdx'_of_not_le (mt le_bot_iff.mp hp)
 rw [multiplicity_eq_of_emultiplicity_eq_some]
 rw [ramificationIdx'_eq_normalizedFactors_count hp hP hP₂, ←normalize_eq P,
   ←UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp,normalize_eq]
 exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP
theorem ramificationIdx'_eq_factors_count
   (hp0:map f p≠⊥) (hP:P.IsPrime) (hP0:P≠⊥):
   ramificationIdx' p P=(factors (map f p)).count P:=by
 rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0,
   factors_eq_normalizedFactors]
theorem ramificationIdx'_ne_zero (hp0:map f p≠⊥) (hP:P.IsPrime) (le:map f p ≤ P):
   ramificationIdx' p P≠0:=by
 classical
 have hP0:P≠⊥:=by
   rintro rfl
   exact hp0 (le_bot_iff.mp le)
 have hPirr:=(Ideal.prime_of_isPrime hP0 hP).irreducible
 rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
 obtain ⟨P',hP',P'_eq⟩:=
   exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
 rwa [Multiset.count_ne_zero,associated_iff_eq.mp P'_eq]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_ne_zero:=ramificationIdx'_ne_zero
theorem ramificationIdx'_ne_zero_of_liesOver [IsDomain R] [IsTorsionFree R S]
   (P:Ideal S) [hP:P.IsPrime] {p:Ideal R} (hp:p≠⊥) [hPp:P.LiesOver p]:
   ramificationIdx' p P≠0:=
 IsDedekindDomain.ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hp) hP <|
   map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp
@[deprecated (since:="2026-07-01")] alias ramificationIdx_ne_zero_of_liesOver:=
 ramificationIdx'_ne_zero_of_liesOver
open IsLocalRing in
lemma ramificationIdx'_eq_one_iff
   {p:Ideal R} {P:Ideal S} [P.IsPrime]
   (hp:P≠⊥) (hpP:p.map (algebraMap R S) ≤ P):
   ramificationIdx' p P=1 ↔
     p.map (algebraMap R (Localization.AtPrime P))=maximalIdeal (Localization.AtPrime P):=by
 refine ⟨?_,ramificationIdx'_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
 let Sₚ:=Localization.AtPrime P
 rw [←not_ne_iff (b:=1),ramificationIdx'_ne_one_iff hpP,pow_two]
 intro H₁
 obtain ⟨a,ha⟩:P∣p.map (algebraMap R S):=Ideal.dvd_iff_le.mpr hpP
 have ha':¬ a ≤ P:=fun h↦H₁ (ha.trans_le (Ideal.mul_mono_right h))
 rw [IsScalarTower.algebraMap_eq _ S, ←Ideal.map_map,ha,Ideal.map_mul,
   Localization.AtPrime.map_eq_maximalIdeal]
 convert! Ideal.mul_top _
 on_goal 2 => infer_instance
 rw [←not_ne_iff,IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
 simpa [primeCompl,Set.disjoint_compl_left_iff_subset]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_one_iff:=
 ramificationIdx'_eq_one_iff
theorem ramificationIdx'_le_ramificationIdx' [IsDomain R] [IsTorsionFree R S] {S₀:Type*}
   [CommRing S₀] [Algebra R S₀] [Algebra S₀ S] [IsScalarTower R S₀ S] (p:Ideal R)
   (P:Ideal S₀) (Q:Ideal S) [Q.LiesOver p] [hP:P.LiesOver p] [Q.IsPrime] (hp:p≠⊥):
   Ideal.ramificationIdx' P Q ≤ Ideal.ramificationIdx' p Q:=
 p.ramificationIdx'_le_ramificationIdx' P Q ((liesOver_iff ..).mp hP) <|
   ramificationIdx'_ne_zero_of_liesOver _ hp
@[deprecated (since:="2026-07-01")] alias ramificationIdx_le_ramificationIdx:=
 ramificationIdx'_le_ramificationIdx'
theorem emultiplicity_map_eq_zero_of_ne [IsDedekindDomain R] {v:Ideal R}
   {w:Ideal S} {p:Ideal R} (hv:Irreducible v) (hp:Prime p) (hvp:v≠p) [w.LiesOver v]:
   emultiplicity w (p.map (algebraMap R S))=0:=by
 refine emultiplicity_eq_zero.2 fun h↦hvp.symm ?_
 rw [Ideal.dvd_iff_le,Ideal.map_le_iff_le_comap, ←under_def, ←Ideal.over_def w v] at h
 exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h
private theorem emultiplicity_map_eq_ramificationIdx'_mul_of_prime [IsDedekindDomain R]
   [FaithfulSMul R S] {v:Ideal R} {w:Ideal S} {p:Ideal R}
   (hv:Irreducible v) (hp:Prime p) (hw:Irreducible w) (hw_bot:w≠⊥)
   [w.LiesOver v]:emultiplicity w (p.map (algebraMap R S))=
     v.ramificationIdx' w*emultiplicity v p:=by
 have hp_bot:p.map (algebraMap R S)≠⊥:=map_ne_bot_of_ne_bot hp.ne_zero
 by_cases hvp:v=p
 · simp [hvp,(FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
     ramificationIdx'_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
     emultiplicity_eq_count_normalizedFactors hw hp_bot]
 · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp,mul_zero,
     emultiplicity_map_eq_zero_of_ne hv hp hvp]
theorem emultiplicity_map_eq_ramificationIdx'_mul [IsDedekindDomain R]
   [FaithfulSMul R S] {v:Ideal R} {w:Ideal S} {I:Ideal R} (h:I≠⊥)
   (hv:Irreducible v) (hw:Irreducible w) (hw_bot:w≠⊥) [w.LiesOver v]:
   emultiplicity w (I.map (algebraMap R S))=
     v.ramificationIdx' w*emultiplicity v I:=by
 induction I using induction_on_prime with
 | h₁ => aesop
 | h₂ I hI =>
   obtain rfl:I=⊤:=by simpa using hI
   simp_rw [Ideal.map_top,emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
     emultiplicity_eq_count_normalizedFactors hv h, ←Ideal.one_eq_top,normalizedFactors_one]
   simp
 | h₃ I p hI hp IH =>
   rw [Ideal.map_mul,emultiplicity_mul hw.prime,emultiplicity_mul hv.prime,IH hI,mul_add,
     emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp hw hw_bot]
@[deprecated (since:="2026-07-01")] alias emultiplicity_map_eq_ramificationIdx_mul:=
 emultiplicity_map_eq_ramificationIdx'_mul
end IsDedekindDomain
end DecEq
section tower
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
theorem ramificationIdx'_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
   {p:Ideal R} {P:Ideal S} {Q:Ideal T} [hpm:P.IsPrime] [hqm:Q.IsPrime]
   (hg0:map (algebraMap S T) P≠⊥)
   (hfg:map (algebraMap R T) p≠⊥) (hg:map (algebraMap S T) P ≤ Q):
   ramificationIdx' p Q=
   ramificationIdx' p P*ramificationIdx' P Q:=by
 classical
 have hf0:map (algebraMap R S) p≠⊥:=by
   rw [IsScalarTower.algebraMap_eq R S T, ←map_map] at hfg
   exact ne_bot_of_map_ne_bot hfg
 have hp0:P≠⊥:=ne_bot_of_map_ne_bot hg0
 have hq0:Q≠⊥:=ne_bot_of_le_ne_bot hg0 hg
 letI:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hp0 hpm
 rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hf0 hpm hp0,
   IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hg0 hqm hq0,
   IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hfg hqm hq0,
   IsScalarTower.algebraMap_eq R S T, ←map_map]
 rcases eq_prime_pow_mul_coprime hf0 P with ⟨I,hcp,heq⟩
 have hcp:⊤=map (algebraMap S T) P ⊔ map (algebraMap S T) I:=by rw [←map_sup,hcp,map_top]
 have hntq:¬ ⊤ ≤ Q:=fun ht↦IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
 nth_rw 1 [heq,Ideal.map_mul,Ideal.map_pow,normalizedFactors_mul (pow_ne_zero _ hg0) <| by
   by_contra h
   simp only [h,Submodule.zero_eq_bot,bot_le,sup_of_le_left] at hcp
   exact hntq (hcp.trans_le hg),Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul]
 exact add_eq_left.mpr <| Decidable.byContradiction fun h↦hntq <| hcp.trans_le <|
   sup_le hg <| le_of_dvd <| dvd_of_mem_normalizedFactors <| Multiset.count_ne_zero.mp h
@[deprecated (since:="2026-07-01")] alias ramificationIdx_algebra_tower:=
 ramificationIdx'_algebra_tower
theorem ramificationIdx'_algebra_tower' [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
   [Module.IsTorsionFree R S] [Module.IsTorsionFree S T] (p:Ideal R) (P:Ideal S) (Q:Ideal T)
   [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p]:
   ramificationIdx' p Q=
     ramificationIdx' p P*ramificationIdx' P Q:=by
 obtain rfl | hp:=eq_or_ne p ⊥
 · simp
 have:P.IsPrime:=isPrime_of_liesOver Q P
 have:Module.IsTorsionFree R T:=by
   refine Module.IsTorsionFree.of_smul_eq_zero fun r m h↦?_
   rwa [algebra_compatible_smul S,smul_eq_zero,FaithfulSMul.algebraMap_eq_zero_iff] at h
 have hP:P≠⊥:=ne_bot_of_liesOver_of_ne_bot hp _
 exact ramificationIdx'_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
   <| map_le_iff_le_comap.mpr <| le_of_eq <| over_def Q P
@[deprecated (since:="2026-07-01")] alias ramificationIdx_algebra_tower':=
 ramificationIdx'_algebra_tower'
end tower
end Ideal
end ProximityFlatProofPort
end PackedLegacy_AR

/-! Packed from ProximityPrize.SubmissionLower.AS. -/
section PackedLegacy_AS
section ProximityFlatProofPort
open IsLocalRing LinearMap Module Submodule TensorProduct AlgebraTensorModule
variable {A B M:Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
 [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M]
section tower
variable [Module B M] [IsScalarTower A B M]
variable (A) in
theorem CovBy.length_restrictScalars {p q:Submodule B M} (h:p ⋖ q):
   length A q=Module.length A p+Module.length (ResidueField A) (ResidueField B):=by
 let f:p →ₗ[B] q:=inclusion h.le
 have key:IsSimpleModule B (q ⧸ f.range):=by
   rwa [range_inclusion, ←covBy_iff_quot_is_simple h.le]
 obtain ⟨m,hm,⟨e⟩⟩:=isSimpleModule_iff_quot_maximal.mp key
 rw [eq_maximalIdeal hm] at e
 let g:q →ₗ[B] ResidueField B:=e.comp f.range.mkQ
 have:Function.Injective f:=inclusion_injective _
 have:Function.Surjective g:=e.surjective.comp f.range.mkQ_surjective
 have:Function.Exact f g:=exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
 rw [length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A)
   (by simpa) (by simpa) (by simpa),Module.length_eq_of_surjective (M:=ResidueField B)
     (residue_surjective (R:=A)),Module.length_eq_rank]
variable (A B M) in
theorem IsLocalRing.length_restrictScalars:
   length A M=length B M*Module.length (ResidueField A) (ResidueField B):=by
 by_cases h:IsFiniteLength B M
 · obtain ⟨s,hs_bot,hs_top⟩:=isFiniteLength_iff_exists_compositionSeries.mp h
   rw [←length_compositionSeries s hs_bot hs_top]
   suffices ∀ k,length A (s k)=k*Module.length (ResidueField A) (ResidueField B) by
     rw [←Fin.val_last s.length, ←this, ←RelSeries.last,hs_top]
     exact length_top.symm
   intro k
   induction k using Fin.induction with
   | zero => rw [←RelSeries.head,hs_bot];simp
   | succ i hi => simpa [hi,add_one_mul] using (s.step i).length_restrictScalars A
 · have:¬ IsFiniteLength A M:=by
     contrapose! h
     rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
     exact h.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
   rw [←length_ne_top_iff,not_ne_iff] at h this
   have ne:length (ResidueField A) (ResidueField B)≠0:=by
     simpa [pos_iff_ne_zero] using Module.length_pos
   rw [h,this,ENat.top_mul ne]
end tower
section flat
variable [Flat A B]
variable (B) in
theorem CovBy.length_baseChange {p q:Submodule A M} (h:p ⋖ q):
   length B (q.baseChange B)=
     length B (p.baseChange B)+length B (B ⧸ (maximalIdeal A).map (algebraMap A B)):=by
 have hp:length B (B ⊗[A] p)=length B (p.baseChange B):=
   (toBaseChange.toLinearEquiv B p).length_eq
 have hq:length B (B ⊗[A] q)=length B (q.baseChange B):=
   (toBaseChange.toLinearEquiv B q).length_eq
 rw [←hp, ←hq]
 let f:p →ₗ[A] q:=inclusion h.le
 have key:IsSimpleModule A (q ⧸ f.range):=by
   rwa [range_inclusion, ←covBy_iff_quot_is_simple h.le]
 obtain ⟨m,hm,⟨e⟩⟩:=isSimpleModule_iff_quot_maximal.mp key
 obtain rfl:=eq_maximalIdeal hm
 let g:=e.comp f.range.mkQ
 have:Function.Injective f:=inclusion_injective _
 have:Function.Surjective g:=e.surjective.comp f.range.mkQ_surjective
 have:Function.Exact f g:=exact_iff.mpr (by simp [f,g])
 have:FaithfullyFlat A B:=FaithfullyFlat.of_flat_of_isLocalHom
 rw [length_eq_add_of_exact (lTensor B B f) (lTensor B B g) (by simpa) (by simpa) (by simpa),
   (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toLinearEquiv.length_eq]
variable (A B M) in
theorem IsLocalRing.length_baseChange:
   length B (B ⊗[A] M)=length A M*length B (B ⧸ (maximalIdeal A).map (algebraMap A B)):=by
 by_cases h:IsFiniteLength A M
 · obtain ⟨s,hs_bot,hs_top⟩:=isFiniteLength_iff_exists_compositionSeries.mp h
   rw [←length_compositionSeries s hs_bot hs_top]
   suffices ∀ k,length B ((s k).baseChange B)=
       k*length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) by
     rw [←Fin.val_last s.length, ←this, ←RelSeries.last,hs_top,baseChange_top,length_top]
   intro k
   induction k using Fin.induction with
   | zero => rw [←RelSeries.head,hs_bot,baseChange_bot];simp
   | succ i hi => simpa [hi,add_one_mul] using (s.step i).length_baseChange B
 · have:¬ IsFiniteLength B (B ⊗[A] M):=by
     contrapose! h
     rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
     have:FaithfullyFlat A B:=FaithfullyFlat.of_flat_of_isLocalHom
     exact h.imp IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
       IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
   rw [←length_ne_top_iff,not_ne_iff] at h this
   have ne:length B (B ⧸ (maximalIdeal A).map (algebraMap A B))≠0:=by
     simpa [←pos_iff_ne_zero,length_pos_iff] using (map_maximalIdeal_lt_top (algebraMap A B)).ne
   rw [h,this,ENat.top_mul ne]
end flat
end ProximityFlatProofPort
end PackedLegacy_AS

/-! Packed from ProximityPrize.SubmissionLower.IJ. -/
section PackedLegacy_IJ
section ProximityFlatProofPort
variable {R A B:Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
   [Algebra R B] [IsScalarTower R A B]
variable (p:Ideal A) (q:Ideal B) [q.LiesOver p]
section maximal
variable [p.IsMaximal] [q.IsMaximal] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
 [Localization.AtPrime.IsLiesOverAlgebra p q]
attribute [local instance] Ideal.Quotient.field
instance [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)]:
   Algebra.IsSeparable p.ResidueField q.ResidueField:=by
 refine Algebra.IsSeparable.of_equiv_equiv
   (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
   (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
 ext x
 simp [RingHom.algebraMap_toAlgebra, ←IsScalarTower.algebraMap_apply]
instance [Algebra.IsSeparable p.ResidueField q.ResidueField]:
   Algebra.IsSeparable (A ⧸ p) (B ⧸ q):=by
 refine Algebra.IsSeparable.of_equiv_equiv
   (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
   (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
 apply RingHom.ext fun x↦?_
 obtain ⟨x,rfl⟩:=
   (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
 obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective x
 apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
 simp only [RingHom.coe_comp,RingHom.coe_coe,Function.comp_apply,RingEquiv.symm_apply_apply,
   RingEquiv.apply_symm_apply]
 simp [RingHom.algebraMap_toAlgebra, ←IsScalarTower.algebraMap_apply]
variable {p q} in
lemma Algebra.isSeparable_residueField_iff:
   Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q):=
 ⟨fun _↦inferInstance,fun _↦inferInstance⟩
end maximal
section prime
variable [p.IsPrime] [q.IsPrime] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
 [Localization.AtPrime.IsLiesOverAlgebra p q]
instance:Algebra.IsAlgebraic (A ⧸ p) p.ResidueField:=
 IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))
instance [Algebra.IsIntegral A B]:
   Algebra.IsAlgebraic p.ResidueField q.ResidueField:=by
 have:Algebra.IsIntegral (A ⧸ p) (B ⧸ q):=
   .tower_top A
 letI:=((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
 haveI:IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField:=.of_algebraMap_eq' rfl
 haveI:Algebra.IsAlgebraic (A ⧸ p) q.ResidueField:=.trans _ (B ⧸ q) _
 haveI:IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField:=by
   refine .of_algebraMap_eq fun x↦?_
   obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective x
   simp [RingHom.algebraMap_toAlgebra, ←IsScalarTower.algebraMap_apply]
 refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)
end prime
namespace IsLocalRing
variable {R k:Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]
instance ResidueField.algebraOfIsIntegral [Algebra.IsIntegral R k]:Algebra (ResidueField R) k:=
 fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
   (by simp [←eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra
instance ResidueField.isScalarTowerOfIsIntegral [Algebra.IsIntegral R k]:
   IsScalarTower R (ResidueField R) k:=
 .of_algebraMap_eq fun _↦rfl
instance [Module.Finite R k]:Module.Finite (ResidueField R) k:=.of_equiv_equiv
 (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥=maximalIdeal R by
   rw [←eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k),RingHom.ker]))
 (RingEquiv.quotientBot k) (by ext;rfl)
end IsLocalRing
end ProximityFlatProofPort
end PackedLegacy_IJ

/-! Packed from ProximityPrize.SubmissionLower.V2. -/
section PackedLegacy_V2
section ProximityFlatProofPort
open Algebra Module
open scoped TensorProduct
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
 (M:Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
namespace Algebra.FormallyUnramified
theorem iff_exists_tensorProduct [EssFiniteType R S]:
   FormallyUnramified R S ↔ ∃ t:S ⊗[R] S,
     (∀ s,((1:S) ⊗ₜ[R] s-s ⊗ₜ[R] (1:S))*t=0)∧TensorProduct.lmul' R t=1:=by
 rw [formallyUnramified_iff,KaehlerDifferential,
   Ideal.cotangent_subsingleton_iff,Ideal.isIdempotentElem_iff_of_fg _
     (KaehlerDifferential.ideal_fg R S)]
 have:∀ t:S ⊗[R] S,TensorProduct.lmul' R t=1 ↔ 1-t∈KaehlerDifferential.ideal R S:=by
   intro t
   simp only [KaehlerDifferential.ideal,RingHom.mem_ker,map_sub,map_one,
     sub_eq_zero,@eq_comm S 1]
 simp_rw [this, ←KaehlerDifferential.span_range_eq_ideal]
 constructor
 · rintro ⟨e,he₁,he₂:_=Ideal.span _⟩
   refine ⟨1-e,?_,?_⟩
   · intro s
     obtain ⟨x,hx⟩:e∣1 ⊗ₜ[R] s-s ⊗ₜ[R] 1:=by
       rw [←Ideal.mem_span_singleton, ←he₂]
       exact Ideal.subset_span ⟨s,rfl⟩
     rw [hx,mul_comm, ←mul_assoc,sub_mul,one_mul,he₁.eq,sub_self,zero_mul]
   · rw [sub_sub_cancel,he₂,Ideal.mem_span_singleton]
 · rintro ⟨t,ht₁,ht₂⟩
   use 1-t
   rw [←sub_sub_self 1 t] at ht₁;generalize 1-t=e at*
   constructor
   · suffices e∈(Submodule.span (S ⊗[R] S) {1-e}).annihilator by
       simpa [IsIdempotentElem,mul_sub,sub_eq_zero,eq_comm,
         Submodule.mem_annihilator_span_singleton] using this
     exact (show Ideal.span _ ≤ _ by simpa only [Ideal.span_le,Set.range_subset_iff,
       Submodule.mem_annihilator_span_singleton,SetLike.mem_coe]) ht₂
   · apply le_antisymm <;> simp only [Ideal.submodule_span_eq,Ideal.mem_span_singleton,ht₂,
       Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe,Set.range_subset_iff]
     intro s
     use 1 ⊗ₜ[R] s-s ⊗ₜ[R] 1
     linear_combination ht₁ s
lemma finite_of_free_aux (I) [DecidableEq I] (b:Basis I R S)
   (f:I →₀ S) (x:S) (a:I → I →₀ R) (ha:a=fun i↦b.repr (b i*x)):
   (1 ⊗ₜ[R] x*Finsupp.sum f fun i y↦y ⊗ₜ[R] b i)=
     Finset.sum (f.support.biUnion fun i↦(a i).support) fun k↦
     Finsupp.sum (b.repr (f.sum fun i y↦a i k • y)) fun j c↦c • b j ⊗ₜ[R] b k:=by
 rw [Finsupp.sum,Finset.mul_sum]
 subst ha
 let a i:=b.repr (b i*x)
 conv_lhs =>
   simp only [TensorProduct.tmul_mul_tmul,one_mul,mul_comm x (b _),
     ←show ∀ i,Finsupp.linearCombination _ b (a i)=b i*x from
         fun _↦b.linearCombination_repr _]
 conv_lhs => simp only [Finsupp.linearCombination,Finsupp.coe_lsum,
   LinearMap.coe_smulRight,LinearMap.id_coe,id_eq,Finsupp.sum,TensorProduct.tmul_sum,
   ←TensorProduct.smul_tmul]
 have h₁:∀ k,
   (Finsupp.sum (Finsupp.sum f fun i y↦a i k • b.repr y) fun j z↦z • b j ⊗ₜ[R] b k)=
     (f.sum fun i y↦(b.repr y).sum fun j z↦a i k • z • b j ⊗ₜ[R] b k):=by
   intro i
   rw [Finsupp.sum_sum_index]
   · congr
     ext j s
     rw [Finsupp.sum_smul_index]
     · simp only [mul_smul,Finsupp.sum, ←Finset.smul_sum]
     intro;simp only [zero_smul]
   · intro;simp only [zero_smul]
   · intros;simp only [add_smul]
 have h₂:∀ (x:S),((b.repr x).support.sum fun a↦b.repr x a • b a)=x:=by
   simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using b.linearCombination_repr
 simp only [a] at h₁
 simp_rw [map_finsuppSum,map_smul,h₁,Finsupp.sum,Finset.sum_comm (t:=f.support),
   TensorProduct.smul_tmul', ←TensorProduct.sum_tmul, ←Finset.smul_sum,h₂]
 apply Finset.sum_congr rfl
 intro i hi
 apply Finset.sum_subset_zero_on_sdiff
 · exact Finset.subset_biUnion_of_mem (fun i↦(a i).support) hi
 · simp only [a,Finset.mem_sdiff,Finset.mem_biUnion,Finsupp.mem_support_iff,ne_eq,not_not,
     and_imp,forall_exists_index]
   simp+contextual
 · exact fun _ _↦rfl
variable [FormallyUnramified R S] [EssFiniteType R S]
variable (R S) in
noncomputable
def elem:S ⊗[R] S:=
 (iff_exists_tensorProduct.mp inferInstance).choose
lemma one_tmul_sub_tmul_one_mul_elem
   (s:S):(1 ⊗ₜ s-s ⊗ₜ 1)*elem R S=0:=
 (iff_exists_tensorProduct.mp inferInstance).choose_spec.1 s
lemma one_tmul_mul_elem
   (s:S):(1 ⊗ₜ s)*elem R S=(s ⊗ₜ 1)*elem R S:=by
 rw [←sub_eq_zero, ←sub_mul,one_tmul_sub_tmul_one_mul_elem]
lemma lmul_elem:
   TensorProduct.lmul' R (elem R S)=1:=
 (iff_exists_tensorProduct.mp inferInstance).choose_spec.2
variable (R S)
lemma finite_of_free [Module.Free R S]:Module.Finite R S:=by
 classical
 letI:DecidableEq S:=Classical.decEq S
 let I:=Module.Free.ChooseBasisIndex R S
 let b:Basis I R S:=Module.Free.chooseBasis R S
 have ⟨f,hf⟩:∃ (a:I →₀ S),elem R S=a.sum (fun i x↦x ⊗ₜ b i):=by
   let b':=((Basis.singleton PUnit.{1} S).tensorProduct b).reindex (Equiv.punitProd I)
   use b'.repr (elem R S)
   conv_lhs => rw [←b'.linearCombination_repr (elem R S),Finsupp.linearCombination_apply]
   congr! with _ i x
   simp [b',Basis.tensorProduct,TensorProduct.smul_tmul']
 constructor
 use Finset.image₂ (fun i j↦f i*b j) f.support f.support
 rw [←top_le_iff]
 rintro x-
 let a:I → I →₀ R:=fun i↦b.repr (b i*x)
 let F:I →₀ I →₀ R:=Finsupp.onFinset f.support (fun j↦b.repr (x*f j))
   (fun j↦not_imp_comm.mp fun hj↦by simp [Finsupp.notMem_support_iff.mp hj])
 have hG:∀ j∉(Finset.biUnion f.support fun i↦(a i).support),
     b.repr (f.sum (fun i y↦a i j • y))=0:=by
   intro j hj
   simp only [Finset.mem_biUnion,Finsupp.mem_support_iff,ne_eq,not_exists,not_and,
     not_not] at hj
   simp only [Finsupp.sum]
   trans b.repr (f.support.sum (fun _↦0))
   · refine congr_arg b.repr (Finset.sum_congr rfl ?_)
     simp only [Finsupp.mem_support_iff]
     intro i hi
     rw [hj i hi,zero_smul]
   · simp only [Finset.sum_const_zero,map_zero]
 let G:I →₀ I →₀ R:=Finsupp.onFinset (Finset.biUnion f.support (fun i↦(a i).support))
   (fun j↦b.repr (f.sum (fun i y↦a i j • y)))
   (fun j↦not_imp_comm.mp (hG j))
 have:F=G:=by
   apply Finsupp.curryEquiv.symm.injective
   apply (Finsupp.equivCongrLeft (Equiv.prodComm I I)).injective
   apply (b.tensorProduct b).repr.symm.injective
   suffices (F.sum fun a f↦f.sum fun b' c↦c • b b' ⊗ₜ[R] b a)=
       G.sum fun a f↦f.sum fun b' c↦c • b b' ⊗ₜ[R] b a by
     simpa [Finsupp.linearCombination_apply,Finsupp.sum_uncurry_index]
   have:∀ i,((b.repr (x*f i)).sum fun j k↦k • b j ⊗ₜ[R] b i)=(x*f i) ⊗ₜ[R] b i:=by
     intro i
     simp_rw [Finsupp.sum,TensorProduct.smul_tmul', ←TensorProduct.sum_tmul]
     congr 1
     exact b.linearCombination_repr _
   rw [Finsupp.onFinset_sum,Finsupp.onFinset_sum]
   · trans (x ⊗ₜ 1)*elem R S
     · simp_rw [this,hf,Finsupp.sum,Finset.mul_sum,TensorProduct.tmul_mul_tmul,one_mul]
     · rw [←one_tmul_mul_elem,hf,finite_of_free_aux]
       rfl
   · intro;simp
   · intro;simp
 have:∀ j,x*f j=f.sum fun i y↦a i j • y:=by
   intro j
   apply b.repr.injective
   exact DFunLike.congr_fun this j
 rw [←mul_one x, ←@lmul_elem R,hf,map_finsuppSum,Finsupp.sum,Finset.mul_sum]
 simp only [TensorProduct.lmul'_apply_tmul,Finset.coe_image₂, ←mul_assoc,this,
   Finsupp.sum,Finset.sum_mul,smul_mul_assoc]
 apply Submodule.sum_mem;intro i hi
 apply Submodule.sum_mem;intro j hj
 apply Submodule.smul_mem
 apply Submodule.subset_span
 use j,hj,i,hi
noncomputable
def sec:
   M →ₗ[S] S ⊗[R] M where
 __:=((TensorProduct.AlgebraTensorModule.mapBilinear R S S S S S M
   LinearMap.id).flip (elem R S)).comp (lsmul R R M).toLinearMap.flip
 map_smul' r m:=by
   simp only [AddHom.toFun_eq_coe,LinearMap.coe_toAddHom,LinearMap.coe_comp,Function.comp_apply,
     LinearMap.flip_apply,TensorProduct.AlgebraTensorModule.mapBilinear_apply,RingHom.id_apply]
   trans (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R:=S) (M:=S))
     ((LinearMap.flip (AlgHom.toLinearMap (lsmul R R M))) m)) ((1 ⊗ₜ r)*elem R S)
   · induction elem R S using TensorProduct.induction_on
     · simp
     · simp [smul_comm r]
     · simp only [map_add,mul_add, *]
   · have:=one_tmul_sub_tmul_one_mul_elem (R:=R) r
     rw [sub_mul,sub_eq_zero] at this
     rw [this]
     induction elem R S using TensorProduct.induction_on
     · simp
     · simp [TensorProduct.smul_tmul']
     · simp only [map_add,smul_add,mul_add, *]
lemma comp_sec:
   (TensorProduct.AlgebraTensorModule.lift
     ((lsmul S S M).toLinearMap.flip.restrictScalars R).flip).comp (sec R S M)=
     LinearMap.id:=by
 ext x
 simp only [sec,LinearMap.coe_comp,LinearMap.coe_mk,LinearMap.coe_toAddHom,
   Function.comp_apply,LinearMap.flip_apply,TensorProduct.AlgebraTensorModule.mapBilinear_apply,
   TensorProduct.AlgebraTensorModule.lift_apply,LinearMap.id_coe,id_eq]
 trans (TensorProduct.lmul' R (elem R S)) • x
 · induction elem R S using TensorProduct.induction_on with
   | zero => simp
   | tmul r s => simp [mul_smul,smul_comm r s]
   | add y z hy hz => simp [hy,hz,add_smul]
 · rw [lmul_elem,one_smul]
lemma flat_of_restrictScalars [Module.Flat R M]:Module.Flat S M:=
 Module.Flat.of_retract _ _ (comp_sec R S M)
lemma projective_of_restrictScalars [Module.Projective R M]:Module.Projective S M:=
 Module.Projective.of_split _ _ (comp_sec R S M)
end Algebra.FormallyUnramified
end ProximityFlatProofPort
end PackedLegacy_V2

/-! Packed from ProximityPrize.SubmissionLower.V4. -/
section PackedLegacy_V4
section ProximityFlatProofPort
universe u
namespace Algebra
section
variable {R A B:Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
   [Algebra R B] [IsScalarTower R A B]
variable (R) in
abbrev IsUnramifiedAt (q:Ideal A) [q.IsPrime]:Prop:=
 FormallyUnramified R (Localization.AtPrime q)
variable (R A) in
def unramifiedLocus:Set (PrimeSpectrum A):=
 { p | IsUnramifiedAt R p.asIdeal}
lemma IsUnramifiedAt.comp
   (p:Ideal A) (P:Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
   [IsUnramifiedAt R p] [IsUnramifiedAt A P]:IsUnramifiedAt R P:=by
 let:=Localization.AtPrime.algebraOfLiesOver p P
 have:FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P):=
   .of_restrictScalars A _ _
 exact FormallyUnramified.comp R (Localization.AtPrime p) _
variable (R) in
lemma IsUnramifiedAt.of_restrictScalars (P:Ideal B) [P.IsPrime]
   [IsUnramifiedAt R P]:IsUnramifiedAt A P:=
 FormallyUnramified.of_restrictScalars R _ _
instance (p:Ideal R) [p.IsPrime] (q:Ideal A) [q.IsPrime] [q.LiesOver p] [IsUnramifiedAt R q]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra p q]:
   FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q):=
 .of_restrictScalars R _ _
open _root_.TensorProduct in
theorem IsUnramifiedAt.residueField
   (P:Ideal R) [P.IsPrime] (Q:Ideal A) [Q.IsPrime]
   [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
   (Q':Ideal (P.Fiber A)) [Q'.IsPrime]
   (hQ':Q=Q'.comap Algebra.TensorProduct.includeRight.toRingHom):
   IsUnramifiedAt P.ResidueField Q':=by
 let f₀:Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q':=
   Localization.localAlgHom Q Q' _ hQ'
 have hf₀:Function.Surjective f₀:=by
   subst hQ';exact P.surjectiveOnStalks_residueField.baseChange' _ _
 let f:P.Fiber (Localization.AtPrime Q) →ₐ[P.ResidueField] Localization.AtPrime Q':=
   Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _↦.all _ _
 have hf:Function.Surjective f:=hf₀.forall.mpr fun x↦⟨1 ⊗ₜ x,by simp [f]⟩
 exact .of_surjective _ hf
end
section IsUnramifiedIn
variable {R:Type*} [CommRing R]
def IsUnramifiedIn (A:Type*) [CommRing A] [Algebra R A] (𝔭:Ideal R):Prop:=
 ∀ (𝔓:Ideal A) (_:𝔓.IsPrime),𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt R 𝔓
variable (A:Type*) [CommRing A] [Algebra R A]
theorem isUnramifiedIn_top:IsUnramifiedIn A (⊤:Ideal R):=
 fun P hP _↦(hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤:Ideal R)).mpr rfl)).elim
end IsUnramifiedIn
section
variable {R A:Type*} [CommRing R] [CommRing A] [Algebra R A]
lemma unramifiedLocus_eq_compl_support:
   unramifiedLocus R A=(Module.support A Ω[A⁄R])ᶜ:=by
 ext p
 simp only [Set.mem_compl_iff,Module.notMem_support_iff]
 have:=IsLocalizedModule.iso p.asIdeal.primeCompl
   (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
 exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm
lemma basicOpen_subset_unramifiedLocus_iff {f:A}:
   ↑(PrimeSpectrum.basicOpen f) ⊆ unramifiedLocus R A ↔
     Algebra.FormallyUnramified R (Localization.Away f):=by
 rw [unramifiedLocus_eq_compl_support,Set.subset_compl_comm,
   PrimeSpectrum.basicOpen_eq_zeroLocus_compl,compl_compl,
   ←LocalizedModule.subsingleton_iff_support_subset,Algebra.formallyUnramified_iff]
 exact (IsLocalizedModule.iso (.powers f)
   (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
lemma unramifiedLocus_eq_univ_iff:
   unramifiedLocus R A=Set.univ ↔ Algebra.FormallyUnramified R A:=by
 rw [unramifiedLocus_eq_compl_support,compl_eq_comm,Set.compl_univ,eq_comm,
   Module.support_eq_empty_iff,Algebra.formallyUnramified_iff]
theorem formallyUnramified_iff_forall:
   FormallyUnramified R A ↔ ∀ q:PrimeSpectrum A,IsUnramifiedAt R q.1:=
 unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall
theorem unramified_iff_forall [FiniteType R A]:
   Unramified R A ↔ ∀ q:PrimeSpectrum A,IsUnramifiedAt R q.1:=
 .trans ⟨fun h↦h.formallyUnramified,fun h↦⟨h,inferInstance⟩⟩ formallyUnramified_iff_forall
lemma isOpen_unramifiedLocus [EssFiniteType R A]:IsOpen (unramifiedLocus R A):=by
 rw [unramifiedLocus_eq_compl_support,Module.support_eq_zeroLocus]
 exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
lemma exists_formallyUnramified_of_isUnramifiedAt [EssFiniteType R A] (p:Ideal A) [p.IsPrime]
   [IsUnramifiedAt R p]:∃ f∉p,Algebra.FormallyUnramified R (Localization.Away f):=by
 obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hpr,hr⟩:=
   PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
     (show ⟨p,‹_›⟩∈unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
 exact ⟨r,hpr,basicOpen_subset_unramifiedLocus_iff.mp hr⟩
lemma exists_unramified_of_isUnramifiedAt [Algebra.FiniteType R A] (p:Ideal A) [p.IsPrime]
   [IsUnramifiedAt R p]:∃ f∉p,Algebra.Unramified R (Localization.Away f):=by
 obtain ⟨f,hfp,H⟩:=exists_formallyUnramified_of_isUnramifiedAt (R:=R) p
 exact ⟨f,hfp,⟨H,.trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩
end
end Algebra
end ProximityFlatProofPort
end PackedLegacy_V4

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier02 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.G0. -/
section PackedLegacy_G0
section ProximityFlatProofPort
open Algebra Module Polynomial
open scoped TensorProduct
universe u
variable (K A L:Type*) [Field K] [Field L] [CommRing A] [Algebra K A] [Algebra K L]
namespace Algebra.FormallyUnramified
theorem of_isSeparable [Algebra.IsSeparable K L]:FormallyUnramified K L:=by
 rw [iff_comp_injective]
 intro B _ _ I hI f₁ f₂ e
 ext x
 have:f₁ x-f₂ x∈I:=by
   simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e x
 have:=Polynomial.eval_add_of_sq_eq_zero ((minpoly K x).map (algebraMap K B)) (f₂ x)
   (f₁ x-f₂ x) (show (f₁ x-f₂ x)^2∈⊥ from hI ▸ Ideal.pow_mem_pow this 2)
 simp only [add_sub_cancel,eval_map_algebraMap,aeval_algHom_apply,minpoly.aeval,map_zero,
   derivative_map,zero_add] at this
 rwa [eq_comm,((isUnit_iff_ne_zero.mpr
   ((Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero
     (minpoly.aeval K x))).map f₂).mul_right_eq_zero,sub_eq_zero] at this
variable [FormallyUnramified K A] [EssFiniteType K A]
 [FormallyUnramified K L] [EssFiniteType K L]
theorem bijective_of_isAlgClosed_of_isLocalRing
   [IsAlgClosed K] [IsLocalRing A]:
   Function.Bijective (algebraMap K A):=by
 have:=finite_of_free (R:=K) (S:=A)
 have:IsArtinianRing A:=isArtinian_of_tower K inferInstance
 have hA:IsNilpotent (IsLocalRing.maximalIdeal A):=by
   rw [←IsLocalRing.jacobson_eq_maximalIdeal ⊥]
   · exact IsArtinianRing.isNilpotent_jacobson_bot
   · exact bot_ne_top
 let e:K ≃ₐ[K] A ⧸ IsLocalRing.maximalIdeal A:={
   __:=Algebra.ofId K (A ⧸ IsLocalRing.maximalIdeal A)
   __:=Equiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral}
 let e':A ⊗[K] (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[A] A:=
   (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans (Algebra.TensorProduct.rid K A A)
 let f:A ⧸ IsLocalRing.maximalIdeal A →ₗ[A] A:=e'.toLinearMap.comp (sec K A _)
 have hf:LinearMap.comp
     (Algebra.ofId A (A ⧸ IsLocalRing.maximalIdeal A)).toLinearMap f=LinearMap.id:=by
   dsimp [f]
   rw [←LinearMap.comp_assoc, ←comp_sec K A]
   congr 1
   apply LinearMap.restrictScalars_injective K
   apply _root_.TensorProduct.ext'
   intro r s
   obtain ⟨s,rfl⟩:=e.surjective s
   suffices s • (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) r=r • e s by
     simpa [ofId,e']
   simp [Algebra.smul_def,e,ofId,mul_comm]
 have hf₁:f 1 • (1:A ⧸ IsLocalRing.maximalIdeal A)=1:=by
   rw [←algebraMap_eq_smul_one]
   exact LinearMap.congr_fun hf 1
 have hf₂:1-f 1∈IsLocalRing.maximalIdeal A:=by
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_one, ←Ideal.Quotient.algebraMap_eq,
    algebraMap_eq_smul_one,hf₁,sub_self]
 have hf₃:IsIdempotentElem (1-f 1):=by
   apply IsIdempotentElem.one_sub
   rw [IsIdempotentElem, ←smul_eq_mul, ←map_smul,hf₁]
 have hf₄:f 1=1:=by
   obtain ⟨n,hn⟩:=hA
   have:(1-f 1)^n=0:=by
     rw [←Ideal.mem_bot, ←Ideal.zero_eq_bot, ←hn]
     exact Ideal.pow_mem_pow hf₂ n
   rw [eq_comm, ←sub_eq_zero, ←hf₃.pow_succ_eq n,pow_succ,this,zero_mul]
 refine Equiv.bijective ⟨algebraMap K A,⇑e.symm ∘ ⇑(algebraMap A _),fun x↦by simp,fun x↦?_⟩
 have:⇑(algebraMap K A)=⇑f ∘ ⇑e:=by
   ext k
   conv_rhs => rw [←mul_one k, ←smul_eq_mul,Function.comp_apply,map_smul,
     LinearMap.map_smul_of_tower,map_one,hf₄, ←algebraMap_eq_smul_one]
 rw [this]
 simp only [Function.comp_apply,AlgEquiv.apply_symm_apply,algebraMap_eq_smul_one,
   map_smul,hf₄,smul_eq_mul,mul_one]
theorem isField_of_isAlgClosed_of_isLocalRing
   [IsAlgClosed K] [IsLocalRing A]:IsField A:=by
 rw [IsLocalRing.isField_iff_maximalIdeal_eq,eq_bot_iff]
 intro x hx
 obtain ⟨x,rfl⟩:=(bijective_of_isAlgClosed_of_isLocalRing K A).surjective x
 change _=0
 rw [←(algebraMap K A).map_zero]
 by_contra hx'
 exact hx ((isUnit_iff_ne_zero.mpr
   (fun e↦hx' ((algebraMap K A).congr_arg e))).map (algebraMap K A))
include K in
theorem isReduced_of_field:
   IsReduced A:=by
 constructor
 intro x hx
 let f:=(Algebra.TensorProduct.includeRight (R:=K) (A:=AlgebraicClosure K) (B:=A))
 have:Function.Injective f:=by
   have:⇑f=(LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap).comp
       (Algebra.TensorProduct.lid K A).symm.toLinearMap:=by
     ext x;simp [f]
   rw [this]
   suffices Function.Injective
       (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap) by
     exact this.comp (Algebra.TensorProduct.lid K A).symm.injective
   apply Module.Flat.rTensor_preserves_injective_linearMap
   exact (algebraMap K _).injective
 apply this
 rw [map_zero]
 apply eq_zero_of_localization
 intro M hM
 have hy:=(hx.map f).map (algebraMap _ (Localization.AtPrime M))
 generalize algebraMap _ (Localization.AtPrime M) (f x)=y at*
 have:=EssFiniteType.of_isLocalization (Localization.AtPrime M) M.primeCompl
 have:=of_isLocalization (Rₘ:=Localization.AtPrime M) M.primeCompl
 have:=EssFiniteType.comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
   (Localization.AtPrime M)
 have:=comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
   (Localization.AtPrime M)
 letI:=(isField_of_isAlgClosed_of_isLocalRing (AlgebraicClosure K)
   (A:=Localization.AtPrime M)).toField
 exact hy.eq_zero
theorem isRadical_map_isMaximal (B:Type*) [CommRing B] [Algebra A B]
   [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] (p:Ideal A) [p.IsMaximal]:
   (p.map (algebraMap A B)).IsRadical:=by
 let:Field (A ⧸ p):=Ideal.Quotient.field p
 rw [Ideal.isRadical_iff_quotient_reduced]
 exact Algebra.FormallyUnramified.isReduced_of_field (A ⧸ p) (B ⧸ p.map (algebraMap A B))
theorem range_eq_top_of_isPurelyInseparable
   [IsPurelyInseparable K L]:(algebraMap K L).range=⊤:=by
 classical
 have:Nontrivial (L ⊗[K] L):=by
   rw [←not_subsingleton_iff_nontrivial, ←rank_zero_iff (R:=K),rank_tensorProduct',
     mul_eq_zero,or_self,rank_zero_iff,not_subsingleton_iff_nontrivial]
   infer_instance
 rw [←top_le_iff]
 intro x _
 obtain ⟨n,hn⟩:=IsPurelyInseparable.pow_mem K (ringExpChar K) x
 have:ExpChar (L ⊗[K] L) (ringExpChar K):=by
   refine expChar_of_injective_ringHom (algebraMap K _).injective (ringExpChar K)
 have:(1 ⊗ₜ x-x ⊗ₜ 1:L ⊗[K] L)^(ringExpChar K)^n=0:=by
   rw [sub_pow_expChar_pow,TensorProduct.tmul_pow,one_pow,TensorProduct.tmul_pow,one_pow]
   obtain ⟨r,hr⟩:=hn
   rw [←hr,algebraMap_eq_smul_one,TensorProduct.smul_tmul,sub_self]
 have H:(1 ⊗ₜ x:L ⊗[K] L)=x ⊗ₜ 1:=by
   have inst:IsReduced (L ⊗[K] L):=isReduced_of_field L _
   exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨_,this⟩)
 by_cases h':LinearIndependent K ![1,x]
 · have h:=h'.linearIndepOn_id
   let S:=h.extend (Set.subset_univ _)
   let a:S:=⟨1,h.subset_extend _ (by simp)⟩
   have ha:Basis.extend h a=1:=by simp [a]
   let b:S:=⟨x,h.subset_extend _ (by simp)⟩
   have hb:Basis.extend h b=x:=by simp [b]
   by_cases e:a=b
   · obtain rfl:1=x:=congr_arg Subtype.val e
     exact ⟨1,map_one _⟩
   have:=DFunLike.congr_fun
     (DFunLike.congr_arg ((Basis.extend h).tensorProduct (Basis.extend h)).repr H) (a,b)
   simp only [Basis.tensorProduct_repr_tmul_apply, ←ha, ←hb,Basis.repr_self,smul_eq_mul,
     Finsupp.single_apply,e,Ne.symm e,↓reduceIte,mul_one,mul_zero,one_ne_zero] at this
 · rw [LinearIndependent.pair_iff] at h'
   simp only [not_forall,not_and,exists_prop] at h'
   obtain ⟨a,b,e,hab⟩:=h'
   have:IsUnit b:=by
     rw [isUnit_iff_ne_zero]
     rintro rfl
     rw [zero_smul, ←algebraMap_eq_smul_one,add_zero,
       (injective_iff_map_eq_zero' _).mp (algebraMap K L).injective] at e
     cases hab e rfl
   use (-this.unit⁻¹*a)
   rw [map_mul, ←Algebra.smul_def,algebraMap_eq_smul_one,eq_neg_iff_add_eq_zero.mpr e,
     smul_neg,neg_smul,neg_neg,smul_smul,this.val_inv_mul,one_smul]
theorem isSeparable:Algebra.IsSeparable K L:=by
 have:=finite_of_free (R:=K) (S:=L)
 rw [←separableClosure.eq_top_iff]
 have:=of_restrictScalars K (separableClosure K L) L
 have:=EssFiniteType.of_comp K (separableClosure K L) L
 ext
 change _ ↔ _∈(⊤:Subring _)
 rw [←range_eq_top_of_isPurelyInseparable (separableClosure K L) L]
 simp
theorem iff_isSeparable (L:Type u) [Field L] [Algebra K L] [EssFiniteType K L]:
   FormallyUnramified K L ↔ Algebra.IsSeparable K L:=
 ⟨fun _↦isSeparable K L,fun _↦of_isSeparable K L⟩
end Algebra.FormallyUnramified
variable {K A} in
theorem Algebra.IsUnramifiedAt.not_minpoly_sq_dvd
   (Q:Ideal A) [Q.IsPrime] [Algebra.IsUnramifiedAt K Q] (x:A) (p:K[X])
   (hp₁:Ideal.span {p}=RingHom.ker (aeval x).toRingHom)
   (hp₂:Function.Surjective (aeval (R:=K) x)):
   ¬ minpoly K (algebraMap A Q.ResidueField x)^2∣p:=by
 have:Algebra.FiniteType K A:=.of_surjective _ hp₂
 have:=Algebra.FormallyUnramified.finite_of_free K (Localization.AtPrime Q)
 have:IsField (Localization.AtPrime Q):=
   have:=IsArtinianRing.of_finite K (Localization.AtPrime Q)
   have:=Algebra.FormallyUnramified.isReduced_of_field K (Localization.AtPrime Q)
   IsArtinianRing.isField_of_isReduced_of_isLocalRing _
 letI:=this.toField
 set q:=minpoly K (algebraMap A Q.ResidueField x)
 have:algebraMap A (Localization.AtPrime Q) (aeval x q)=0:=by
   apply (algebraMap (Localization.AtPrime Q) Q.ResidueField).injective
   rw [←IsScalarTower.algebraMap_apply, ←aeval_algebraMap_apply,minpoly.aeval,map_zero]
 obtain ⟨⟨m,hm⟩,hm'⟩:=(IsLocalization.map_eq_zero_iff Q.primeCompl _ _).mp this
 obtain ⟨m,rfl⟩:=hp₂ m
 simp_rw [←map_mul, ←AlgHom.coe_toRingHom, ←AlgHom.toRingHom_eq_coe, ←RingHom.mem_ker,
   ←hp₁,Ideal.mem_span_singleton] at hm'
 rw [pow_two]
 rintro H
 have:=(mul_dvd_mul_iff_right (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))).mp
   (H.trans hm')
 rw [minpoly.dvd_iff,aeval_algebraMap_apply,Q.algebraMap_residueField_eq_zero] at this
 exact hm this
end ProximityFlatProofPort
end PackedLegacy_G0

/-! Packed from ProximityPrize.SubmissionLower.V3. -/
section PackedLegacy_V3
section ProximityFlatProofPort
open IsLocalRing
namespace Algebra
section IsLocalRing
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
 [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
instance:FormallyUnramified S (ResidueField S):=.quotient _
instance [FormallyUnramified R S]:
   FormallyUnramified (ResidueField R) (ResidueField S):=
 have:FormallyUnramified R (ResidueField S):=.comp _ S _
 .of_restrictScalars R _ _
variable [EssFiniteType R S]
@[stacks 00UW "(2)"]
instance [FormallyUnramified R S]:
   Module.Finite (ResidueField R) (ResidueField S):=
 have:EssFiniteType R (ResidueField S):=.comp _ S _
 have:EssFiniteType (ResidueField R) (ResidueField S):=.of_comp R _ _
 FormallyUnramified.finite_of_free _ _
@[stacks 00UW "(2)"]
instance [FormallyUnramified R S]:
   Algebra.IsSeparable (ResidueField R) (ResidueField S):=
 FormallyUnramified.isSeparable _ _
set_option backward.inferInstanceAs.wrap.data false in
lemma FormallyUnramified.isField_quotient_map_maximalIdeal [FormallyUnramified R S]:
   IsField (S ⧸ (maximalIdeal R).map (algebraMap R S)):=by
 let mR:=(maximalIdeal R).map (algebraMap R S)
 have hmR:mR ≤ maximalIdeal S:=((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
 letI:Algebra (ResidueField R) (S ⧸ mR):=(inferInstanceAs <| Algebra (R ⧸ _) _)
 have:IsScalarTower R (ResidueField R) (S ⧸ mR):=(inferInstanceAs <| IsScalarTower R (R ⧸ _) _)
 have:FormallyUnramified (ResidueField R) (S ⧸ mR):=.of_restrictScalars R _ _
 have:EssFiniteType (ResidueField R) (S ⧸ mR):=.of_comp R _ _
 have:Module.Finite (ResidueField R) (S ⧸ mR):=FormallyUnramified.finite_of_free _ _
 have:IsReduced (S ⧸ mR):=FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
 have:IsArtinianRing (S ⧸ mR):=isArtinian_of_tower (ResidueField R) inferInstance
 have:Nontrivial (S ⧸ mR):=
   Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hmR
 have:IsLocalRing (S ⧸ mR):=.of_surjective' _ Ideal.Quotient.mk_surjective
 have:maximalIdeal (S ⧸ mR)=⊥:=by
   rw [←jacobson_eq_maximalIdeal _ bot_ne_top,IsArtinianRing.jacobson_eq_radical,
     ←Ideal.zero_eq_bot, ←nilradical,nilradical_eq_zero]
 rwa [←isField_iff_maximalIdeal_eq] at this
@[stacks 00UW "(1)"]
lemma FormallyUnramified.map_maximalIdeal [FormallyUnramified R S]:
   (maximalIdeal R).map (algebraMap R S)=maximalIdeal S:=by
 apply eq_maximalIdeal
 rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
 exact isField_quotient_map_maximalIdeal
@[stacks 02FM]
lemma FormallyUnramified.of_map_maximalIdeal
   [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
   (H:(maximalIdeal R).map (algebraMap R S)=maximalIdeal S):
   Algebra.FormallyUnramified R S:=by
 constructor
 have:FormallyUnramified (ResidueField R) (ResidueField S):=.of_isSeparable _ _
 have:FormallyUnramified R (ResidueField S):=.comp _ (ResidueField R) _
 rw [←subsingleton_tensorProduct (R:=S)]
 refine subsingleton_of_forall_eq 0 fun x↦?_
 obtain ⟨x,rfl⟩:=(KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
   (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
 obtain ⟨⟨x,hx⟩,rfl⟩:=Ideal.toCotangent_surjective _ x
 simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
 replace hx:x∈Ideal.map (algebraMap R S) (maximalIdeal R):=by simpa [H] using hx
 induction hx using Submodule.span_induction with
 | zero => simp
 | mem x h => obtain ⟨x,hx,rfl⟩:=h;simp
 | add x y hx hy _ _ => simp [*,TensorProduct.tmul_add]
 | smul a x hx _ =>
   have:residue S x=0:=by rwa [residue_eq_zero_iff, ←H]
   simp [*,TensorProduct.tmul_add,TensorProduct.smul_tmul', ←Algebra.algebraMap_eq_smul_one]
lemma FormallyUnramified.iff_map_maximalIdeal_eq:
   Algebra.FormallyUnramified R S ↔
     Algebra.IsSeparable (ResidueField R) (ResidueField S)∧
     (maximalIdeal R).map (algebraMap R S)=maximalIdeal S:=
 ⟨fun _↦⟨inferInstance,map_maximalIdeal⟩,fun ⟨_,e⟩↦of_map_maximalIdeal e⟩
end IsLocalRing
section IsUnramifiedAt
variable (R:Type*) {S:Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [EssFiniteType R S] (p:Ideal R) [p.IsPrime] (q:Ideal S) [q.IsPrime] [q.LiesOver p]
 [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
 [Localization.AtPrime.IsLiesOverAlgebra p q]
lemma isUnramifiedAt_iff_map_eq:
   Algebra.IsUnramifiedAt R q ↔
     Algebra.IsSeparable p.ResidueField q.ResidueField∧
     p.map (algebraMap R (Localization.AtPrime q))=maximalIdeal _:=by
 have:EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q):=.of_comp R _ _
 trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
 · exact ⟨fun _↦.of_restrictScalars R _ _,
     fun _↦Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
 rw [FormallyUnramified.iff_map_maximalIdeal_eq]
 congr!
 rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq,
   ←Localization.AtPrime.map_eq_maximalIdeal,Ideal.map_map,Localization.localRingHom,
   IsLocalization.map_comp, ←IsScalarTower.algebraMap_eq]
instance [Algebra.IsUnramifiedAt R q]:Algebra.IsSeparable p.ResidueField q.ResidueField:=
 ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1
instance [Algebra.IsUnramifiedAt R q]:Module.Finite p.ResidueField q.ResidueField:=
 Algebra.FormallyUnramified.finite_of_free _ _
end IsUnramifiedAt
end Algebra
section UniquePrimeOver
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] {p:Ideal R} [p.IsPrime]
 {q:Ideal S} [q.IsPrime] (hq:p.primesOver S={q})
include hq
namespace Localization
lemma localRingHom_injective_of_primesOver_eq_singleton
   [Algebra.IsIntegral R S] [FaithfulSMul R S]:
   Function.Injective (localRingHom p q (algebraMap R S) (hq.ge rfl).2.1):=by
 rw [injective_iff_map_eq_zero]
 intro x hx
 obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq p.primeCompl x
 obtain ⟨a,haq,e⟩:∃ a∉q,a*(algebraMap R S) x=0:=by
   simpa [Localization.localRingHom_mk',IsLocalization.mk'_eq_zero_iff] using hx
 obtain ⟨r,hrp,t,e'⟩:=Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
 refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
   ⟨⟨r,hrp⟩,FaithfulSMul.algebraMap_injective R S ?_⟩
 grind
lemma finite_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
 [Localization.AtPrime.IsLiesOverAlgebra p q]:
   Module.Finite (Localization.AtPrime p) (Localization.AtPrime q):=by
 classical
 letI:DecidableEq (Localization.AtPrime q):=Classical.decEq _
 obtain ⟨s,hs⟩:=Module.Finite.fg_top (R:=R) (M:=S)
 refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap,?_⟩
 rw [Finset.coe_image, ←Submodule.span_span_of_tower R, ←Submodule.map_span,hs,
   Submodule.map_top,LinearMap.coe_range,AlgHom.coe_toLinearMap,IsScalarTower.coe_toAlgHom',
   ←top_le_iff]
 rintro x-
 obtain ⟨x,⟨s,hsq⟩,rfl⟩:=IsLocalization.exists_mk'_eq q.primeCompl x
 obtain ⟨r,hr,t,e'⟩:=Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
 rw [←Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M:=p.primeCompl) _ ⟨r,hr⟩),
   Algebra.smul_def, ←IsScalarTower.algebraMap_apply,IsScalarTower.algebraMap_apply _ S,e',
     map_mul,mul_assoc,mul_left_comm,IsLocalization.mk'_spec'_mk, ←map_mul]
 exact Submodule.subset_span ⟨_,rfl⟩
lemma localRingHom_surjective_of_primesOver_eq_singleton
   [Module.Finite R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra p q]
   (H:Function.Surjective (algebraMap p.ResidueField q.ResidueField)):
   Function.Surjective (localRingHom p q (algebraMap R S) (q.over_def p)):=by
 have:=Localization.finite_of_primesOver_eq_singleton hq
 rw [←Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
 change Function.Surjective (Algebra.linearMap _ _)
 rw [←LinearMap.range_eq_top, ←top_le_iff]
 apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
 rw [Ideal.smul_top_eq_map,Algebra.FormallyUnramified.map_maximalIdeal]
 rintro x-
 obtain ⟨a,ha⟩:=H (algebraMap _ _ x)
 obtain ⟨a,rfl⟩:=residue_surjective a
 rw [←ResidueField.algebraMap_eq, ←IsScalarTower.algebraMap_apply,
   IsScalarTower.algebraMap_apply _ (Localization.AtPrime q),ResidueField.algebraMap_eq,
   ←sub_eq_zero, ←map_sub,residue_eq_zero_iff] at ha
 rw [←sub_sub_self (algebraMap _ _ a) x]
 refine sub_mem (Submodule.mem_sup_left ⟨_,rfl⟩) (Submodule.mem_sup_right ha)
omit hq in
lemma exists_awayMap_injective_of_localRingHom_injective
   (hRS:(RingHom.ker (algebraMap R S)).FG) [q.LiesOver p]
   (H:Function.Injective (localRingHom p q (algebraMap R S) (q.over_def p))):
   ∃ r∉p,∀ r',r∣r' → Function.Injective (awayMap (algebraMap R S) r'):=by
 classical
 obtain ⟨s,hs⟩:=hRS
 have (x:s):algebraMap R (Localization.AtPrime p) x.1=0:=by
   apply H
   simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
     show algebraMap R S _=0 from hs.le (Ideal.subset_span x.2)]
 choose m hm using fun x↦(IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
 have H:RingHom.ker (algebraMap R S) ≤ RingHom.ker
     (algebraMap R (Localization.Away (∏ i,m i).1)):=by
   rw [←hs,Ideal.span_le]
   intro x hxs
   refine (IsLocalization.map_eq_zero_iff (.powers (∏ i,m i).1) _ _).mpr ⟨⟨_,1,rfl⟩,?_⟩
   simp only [pow_one]
   rw [Fintype.prod_eq_mul_prod_compl ⟨x,hxs⟩,Submonoid.coe_mul,mul_assoc,mul_left_comm,hm,
     mul_zero]
 refine ⟨_,(∏ i:s,m i).2,?_⟩
 rintro r' ⟨s,e⟩
 rw [injective_iff_map_eq_zero]
 intro x hx
 obtain ⟨x,_,rfl⟩:=IsLocalization.exists_mk'_eq (.powers r') x
 simp only [awayMap,IsLocalization.Away.map,IsLocalization.map_mk',
   IsLocalization.mk'_eq_zero_iff] at hx
 obtain ⟨⟨_,n,rfl⟩,hn⟩:=hx
 simp only [←map_pow, ←map_mul] at hn
 obtain ⟨⟨_,k,rfl⟩,hk⟩:=(IsLocalization.map_eq_zero_iff (.powers (∏ i,m i).1) _ _).mp (H hn)
 refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_,k+n,rfl⟩,?_⟩
 dsimp only at hk ⊢
 rw [pow_add,mul_assoc,e,mul_pow, ←e,mul_assoc,mul_left_comm,hk,mul_zero]
set_option backward.isDefEq.respectTransparency false in
lemma exists_awayMap_bijective_of_localRingHom_bijective
   [Module.Finite R S] [q.LiesOver p] (hRS:(RingHom.ker (algebraMap R S)).FG)
   (H:Function.Bijective (localRingHom p q (algebraMap R S) (q.over_def p))):
   ∃ r∉p,∀ r',r∣r' → Function.Bijective (awayMap (algebraMap R S) r'):=by
 classical
 letI:DecidableEq S:=Classical.decEq S
 obtain ⟨s,hs⟩:=Algebra.FiniteType.out (R:=R) (A:=S)
 have (x:S):∃ a,∃ b∉p,algebraMap R S a=x*algebraMap R S b:=by
   have:=(IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
   simp only [localRingHom_mk',Prod.exists,Subtype.exists,Ideal.mem_primeCompl_iff,
     IsLocalization.mk'_eq_iff_eq_mul,exists_prop, ←map_mul,
     IsLocalization.eq_iff_exists q.primeCompl] at this
   obtain ⟨a,b,hbp,c,hcq,hc⟩:=this
   obtain ⟨d,hd,e,he⟩:=Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
   exact ⟨d*a,d*b,‹p.IsPrime›.mul_notMem hd hbp,by grind⟩
 choose a b hbp e using this
 obtain ⟨r,hrp,hr⟩:=Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
 refine ⟨r*∏ i∈s,b i,mul_mem (s:=p.primeCompl) hrp (prod_mem fun _ _↦hbp _),?_⟩
 refine fun r' hr'↦⟨hr _ (.trans ⟨_,rfl⟩ hr'),?_⟩
 have H:(IsScalarTower.toAlgHom R S _).range ≤ (awayMapₐ (Algebra.ofId R S) r').range:=by
   rw [←Algebra.map_top,Subalgebra.map_le, ←hs,Algebra.adjoin_le_iff]
   intro x hxs
   obtain ⟨r'',hr'⟩:=hr'
   refine ⟨IsLocalization.mk' (M:=.powers r') _
     (r''*r*(∏ i∈s.erase x,b i)*a x) ⟨_,1,rfl⟩,?_⟩
   dsimp [awayMapₐ,IsLocalization.Away.map]
   simp only [pow_one,IsLocalization.map_mk',IsLocalization.mk'_eq_iff_eq_mul,
     ←map_mul (algebraMap S _),map_mul (algebraMap R _),e]
   congr 1
   rw [hr', ←Finset.prod_erase_mul s b hxs,map_mul,map_mul,map_mul]
   ring_nf
 intro x
 obtain ⟨x,⟨_,n,rfl⟩,rfl⟩:=IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
 obtain ⟨y,hy:awayMap _ _ _=_⟩:=H ⟨x,rfl⟩
 dsimp at hy
 refine ⟨y*Localization.Away.invSelf _^n,?_⟩
 simp only [map_mul,hy]
 simp [Away.invSelf,Localization.mk_eq_mk',awayMap,IsLocalization.Away.map,
   IsLocalization.map_mk', ←Algebra.smul_def,IsLocalization.smul_mk', ←IsLocalization.mk'_pow]
lemma exists_awayMap_bijective_of_residueField_surjective
   [Module.Finite R S] [FaithfulSMul R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
   [Localization.AtPrime.IsLiesOverAlgebra p q]
   (H:Function.Surjective (algebraMap p.ResidueField q.ResidueField)):
   ∃ r∉p,∀ r',r∣r' → Function.Bijective (awayMap (algebraMap R S) r'):=
 exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using! Submodule.fg_bot)
   ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
     localRingHom_surjective_of_primesOver_eq_singleton hq H⟩
end Localization
end UniquePrimeOver
end ProximityFlatProofPort
end PackedLegacy_V3

/-! Packed from ProximityPrize.SubmissionLower.IU. -/
section PackedLegacy_IU
section ProximityFlatProofPort
namespace Ideal
section
variable {S:Type*} [CommRing S] (q:Ideal S) (R:Type*) [CommRing R] [Algebra R S]
open scoped Classical in
noncomputable def ramificationIdx:ℕ:=
 if _:q.IsPrime then
   letI Sq:=Localization.AtPrime q
   (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
 else 0
theorem ramificationIdx_def [q.IsPrime]:
   letI Sq:=Localization.AtPrime q
   q.ramificationIdx R=(Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat:=
 dif_pos _
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_def:=ramificationIdx_def
theorem ramificationIdx_of_not_isPrime (hq:¬ q.IsPrime):q.ramificationIdx R=0:=
 dif_neg hq
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_of_not_isPrime:=
 ramificationIdx_of_not_isPrime
theorem ramificationIdx_pos [q.IsPrime] [Module.Finite R S]:0 < q.ramificationIdx R:=by
 let p:=q.under R
 let Sq:=Localization.AtPrime q
 rw [ramificationIdx_def]
 apply ENat.toNat_pos
 · rw [←pos_iff_ne_zero,Module.length_pos_iff,Submodule.Quotient.nontrivial_iff,
     IsScalarTower.algebraMap_eq R S, ←map_map, ←lt_top_iff_ne_top]
   grw [map_mono map_comap_le,Localization.AtPrime.map_eq_maximalIdeal]
   exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
 · let r:=PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
   have:q=r.1.comap Algebra.TensorProduct.includeRight:=by
     rw [←PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,OrderIso.symm_apply_apply]
   let:=Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
   have:IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p):=by
     convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
   rwa [Module.length_eq_of_surjective (R:=Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
     Module.length_ne_top_iff, ←isArtinianRing_iff_isFiniteLength]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_pos:=ramificationIdx_pos
theorem ramificationIdx_eq_one [q.IsPrime] [Algebra.EssFiniteType R S]
   [Algebra.IsUnramifiedAt R q]:q.ramificationIdx R=1:=by
 let p:=q.under R
 let Rp:=Localization.AtPrime p
 let Sq:=Localization.AtPrime q
 let:Algebra Rp Sq:=Localization.AtPrime.algebraOfLiesOver p q
 have:Algebra.EssFiniteType Rp Sq:=Algebra.EssFiniteType.of_comp R Rp Sq
 rw [ramificationIdx_def,ENat.toNat_eq_iff_eq_coe,Nat.cast_one,Module.length_eq_one_iff,
   isSimpleModule_iff_isCoatom, ←Ideal.isMaximal_def,IsLocalRing.isMaximal_iff,
   IsScalarTower.algebraMap_eq R Rp Sq, ←map_map,Localization.AtPrime.map_eq_maximalIdeal]
 exact Algebra.FormallyUnramified.map_maximalIdeal
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_eq_one:=ramificationIdx_eq_one
variable {q R} in
theorem ramificationIdx_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
   [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField]:
   q.ramificationIdx R=1 ↔ Algebra.IsUnramifiedAt R q:=by
 refine ⟨fun h↦?_,fun _↦ramificationIdx_eq_one q R⟩
 rw [ramificationIdx_def,ENat.toNat_eq_iff_eq_coe,Nat.cast_one,Module.length_eq_one_iff,
   isSimpleModule_iff_isCoatom, ←Ideal.isMaximal_def,IsLocalRing.isMaximal_iff] at h
 let p:=q.under R
 let Rp:=Localization.AtPrime p
 let Sq:=Localization.AtPrime q
 let:=Localization.AtPrime.algebraOfLiesOver p q
 have:=Algebra.EssFiniteType.of_comp R Rp Sq
 suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
 rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
   ←Localization.AtPrime.map_eq_maximalIdeal,map_map, ←IsScalarTower.algebraMap_eq]
 exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField,h⟩
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_eq_one_iff:=
 ramificationIdx_eq_one_iff
end
section
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
 (p:Ideal R) (q:Ideal S) (r:Ideal T)
theorem ramificationIdx_eq [q.LiesOver p] [q.IsPrime]:
   letI Sq:=Localization.AtPrime q
   q.ramificationIdx R=(Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat:=by
 rw [ramificationIdx_def,over_def q p]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_eq:=ramificationIdx_eq
open Localization IsLocalization.AtPrime in
theorem ramificationIdx'_eq_ramificationIdx' [IsDedekindDomain S]
   [q.LiesOver p] [hq:q.IsPrime] (hpS:p.map (algebraMap R S)≠⊥):
   p.ramificationIdx' q=q.ramificationIdx R:=by
 have hq':q≠⊥:=ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
 have:q.IsMaximal:=hq.isMaximal hq'
 obtain ⟨I,hqI,h⟩:=Ideal.eq_prime_pow_mul_coprime hpS q
 replace hqI:¬ I ≤ q:=by
   contrapose! hqI
   rw [sup_of_le_left hqI]
   exact hq.ne_top
 rw [←IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
 apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
 rw [map_map, ←IsScalarTower.algebraMap_eq,Ideal.map_mul,Ideal.map_pow,
   map_eq_top_of_not_le (Localization.AtPrime q) hqI,mul_top,AtPrime.map_eq_maximalIdeal] at h
 have hSq:=isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
 rw [ramificationIdx_eq p q,h,hSq.length_quotient_pow_maximalIdeal,ENat.toNat_coe]
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_ramificationIdx'':=
 ramificationIdx'_eq_ramificationIdx'
theorem ramificationIdx'_eq_ramificationIdx [IsDomain R] [IsDedekindDomain S]
   [Module.IsTorsionFree R S] [q.LiesOver p] [hq:q.IsPrime] (hp:p≠⊥):
   p.ramificationIdx' q=q.ramificationIdx R:=by
 have hpS:p.map (algebraMap R S)≠⊥:=map_ne_bot_of_ne_bot hp
 exact ramificationIdx'_eq_ramificationIdx' p q hpS
@[deprecated (since:="2026-07-01")] alias ramificationIdx_eq_ramificationIdx':=
 ramificationIdx'_eq_ramificationIdx
namespace IsDedekindDomain
open UniqueFactorizationMonoid
theorem ramificationIdx_eq_factors_count [IsDedekindDomain S]
   [q.LiesOver p] (hp0:p.map (algebraMap R S)≠⊥):
   q.ramificationIdx R=(factors (p.map (algebraMap R S))).count q:=by
 by_cases hq:q.IsPrime;swap
 · rw [ramificationIdx_of_not_isPrime q R hq,eq_comm,Multiset.count_eq_zero]
   contrapose! hq
   exact isPrime_of_prime (prime_of_factor q hq)
 have hq0:q≠⊥:=ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
 rw [←ramificationIdx'_eq_ramificationIdx' p q hp0,ramificationIdx'_eq_factors_count hp0 ‹_› hq0]
open UniqueFactorizationMonoid in
theorem ramificationIdx_eq_normalizedFactors_count [IsDedekindDomain S]
   [q.LiesOver p] (hp0:p.map (algebraMap R S)≠⊥):
   q.ramificationIdx R=(normalizedFactors (p.map (algebraMap R S))).count q:=by
 rw [←factors_eq_normalizedFactors, ←ramificationIdx_eq_factors_count p q hp0]
open UniqueFactorizationMonoid in
theorem ramificationIdx_eq_multiplicity [IsDedekindDomain S]
   [q.IsPrime] [q.LiesOver p] (hp:p.map (algebraMap R S)≠⊥):
   q.ramificationIdx R=multiplicity q (p.map (algebraMap R S)):=by
 have hq:q≠⊥:=ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
 rw [ramificationIdx_eq_normalizedFactors_count p q hp,
   multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
     (prime_of_isPrime hq inferInstance).irreducible hp),normalize_eq]
end IsDedekindDomain
theorem ramificationIdx_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
   [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
   [Localization.AtPrime.IsLiesOverAlgebra q r]
   [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)]:
   r.ramificationIdx R=q.ramificationIdx R*r.ramificationIdx S:=by
 have:q.LiesOver (r.under R):=LiesOver.tower_bot r q (r.under R)
 let f:=(Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
   (by rw [map_map, ←IsScalarTower.algebraMap_eq])).trans
     (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
       ((r.under R).map (algebraMap R (Localization.AtPrime q))))
 rw [ramificationIdx_def,ramificationIdx_eq (r.under R),ramificationIdx_eq q,
   f.toLinearEquiv.length_eq,IsLocalRing.length_baseChange,ENat.toNat_mul,
   ←Localization.AtPrime.map_eq_maximalIdeal,map_map, ←IsScalarTower.algebraMap_eq]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_tower':=ramificationIdx_tower'
theorem ramificationIdx_tower [r.LiesOver q] [Module.Flat S T]:
   r.ramificationIdx R=q.ramificationIdx R*r.ramificationIdx S:=by
 by_cases hr:r.IsPrime
 · have:q.IsPrime:=isPrime_of_liesOver r q
   let:=Localization.AtPrime.algebraOfLiesOver q r
   apply ramificationIdx_tower'
 · rw [ramificationIdx_of_not_isPrime r R hr,ramificationIdx_of_not_isPrime r S hr,mul_zero]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_tower:=ramificationIdx_tower
theorem ramificationIdx_below_dvd [r.LiesOver q] [Module.Flat S T]:
   q.ramificationIdx R∣r.ramificationIdx R:=by
 use r.ramificationIdx S
 rw [←ramificationIdx_tower]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_below_dvd:=ramificationIdx_below_dvd
theorem ramificationIdx_above_dvd [r.LiesOver q] [Module.Flat S T]:
   r.ramificationIdx S∣r.ramificationIdx R:=by
 use q.ramificationIdx R
 rw [mul_comm, ←ramificationIdx_tower]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_above_dvd:=ramificationIdx_above_dvd
theorem ramificationIdx_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T]:
   q.ramificationIdx R ≤ r.ramificationIdx R:=
 Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_below_le:=
 ramificationIdx_below_le
theorem ramificationIdx_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T]:
   r.ramificationIdx S ≤ r.ramificationIdx R:=
 Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_above_le:=ramificationIdx_above_le
variable (R) in
open Pointwise in
@[simp]
theorem ramificationIdx_smul {G:Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
   (g:G):(g • q).ramificationIdx R=q.ramificationIdx R:=by
 by_cases hq:q.IsPrime;swap
 · rw [ramificationIdx_of_not_isPrime,ramificationIdx_of_not_isPrime] <;> simpa
 · let p:=q.under R
   let f₀:=MulSemiringAction.toAlgAut G R S g
   have hg:g • q=q.map f₀:=q.pointwise_smul_def
   let Sq:=Localization.AtPrime q
   let Sq':=Localization.AtPrime (q.map f₀)
   let f:Sq ≃ₐ[R] Sq':=
     Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
   let:Algebra Sq Sq':=f.toRingHom.toAlgebra
   have:IsScalarTower R Sq Sq':=IsScalarTower.of_algHom f.toAlgHom
   let e:(Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq'):=
     Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
       (by rw [IsScalarTower.algebraMap_eq R Sq Sq',Ideal.map_map,
         ←AlgEquiv.toAlgHom_toRingHom,AlgEquiv.toAlgHom_ofBijective,Algebra.toRingHom_ofId])
   rw [hg,ramificationIdx_eq p q,ramificationIdx_eq p (q.map f₀),
     e.toLinearEquiv.length_eq,Module.length_eq_of_surjective f.surjective]
@[deprecated (since:="2026-07-01")] alias ramificationIdx'_smul:=ramificationIdx_smul
end
end Ideal
end ProximityFlatProofPort
end PackedLegacy_IU

/-! Packed from ProximityPrize.SubmissionLower.II. -/
section PackedLegacy_II
section ProximityFlatProofPort
universe uM
variable {R N N':Type*} {M:Type uM} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
 [Module R N] [AddCommGroup N'] [Module R N'] (S:Submonoid R)
theorem Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
   [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
   (S) (f:M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]:
   Module.Free Rₛ Mₛ:=
 Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv
universe uR' uM' in
theorem Module.lift_rank_of_isLocalizedModule_of_free
   (Rₛ:Type uR') {Mₛ:Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
   [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S:Submonoid R)
   (f:M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
   [Nontrivial Rₛ]:
   Cardinal.lift.{uM} (Module.rank Rₛ Mₛ)=Cardinal.lift.{uM'} (Module.rank R M):=by
 apply Cardinal.lift_injective.{max uM' uR'}
 have:=(algebraMap R Rₛ).domain_nontrivial
 have:=(IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
 simp only [rank_tensorProduct,rank_self,
   Cardinal.lift_one,one_mul,Cardinal.lift_lift] at this ⊢
 convert! this
 exact Cardinal.lift_umax
theorem Module.finrank_of_isLocalizedModule_of_free
   (Rₛ:Type*) {Mₛ:Type*} [AddCommGroup Mₛ] [Module R Mₛ]
   [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S:Submonoid R)
   (f:M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
   [Nontrivial Rₛ]:
   Module.finrank Rₛ Mₛ=Module.finrank R M:=by
 simpa using! congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))
theorem Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
   [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
   (S) (f:M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective R M]:
   Module.Projective Rₛ Mₛ:=
 Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv
instance [Module.Projective R M]:Module.Projective (Localization S) (LocalizedModule S M):=
 Module.projective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
instance {A:Type*} [CommRing A] [Algebra R A] [Module.Projective R A]:
   Module.Projective (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)):=
 Module.projective_of_isLocalizedModule S (IsScalarTower.toAlgHom R A _).toLinearMap
theorem LinearMap.split_surjective_of_localization_maximal
   (f:M →ₗ[R] N) [Module.FinitePresentation R N]
   (H:∀ (I:Ideal R) (_:I.IsMaximal),
   ∃ (g:_ →ₗ[Localization.AtPrime I] _),
     (LocalizedModule.map I.primeCompl f).comp g=LinearMap.id):
   ∃ (g:N →ₗ[R] M),f.comp g=LinearMap.id:=by
 change LinearMap.id∈LinearMap.range (LinearMap.llcomp R N M N f)
 refine Submodule.mem_of_localization_maximal _ (fun P _↦LocalizedModule.map P.primeCompl) _ _
   fun I hI↦?_
 rw [LocalizedModule.map_id]
 have:LinearMap.id∈LinearMap.range (LinearMap.llcomp _
   (LocalizedModule I.primeCompl N) _ _ (LocalizedModule.map I.primeCompl f)):=H I hI
 convert! this
 · ext f
   constructor
   · intro hf
     obtain ⟨a,ha,c,rfl⟩:=hf
     obtain ⟨g,rfl⟩:=ha
     use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) g c
     apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
       (LocalizedModule.map I.primeCompl) c).injective
     dsimp
     conv_rhs => rw [←Submonoid.smul_def]
     conv_lhs => rw [←LinearMap.map_smul_of_tower]
     rw [←Submonoid.smul_def,IsLocalizedModule.mk'_cancel',IsLocalizedModule.mk'_cancel']
     apply LinearMap.restrictScalars_injective R
     apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
     · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
     ext
     simp only [LocalizedModule.map_mk,LinearMap.coe_comp,LinearMap.coe_restrictScalars,
       Function.comp_apply,LocalizedModule.mkLinearMap_apply,LinearMap.llcomp_apply,
       LocalizedModule.map_mk]
   · rintro ⟨g,rfl⟩
     obtain ⟨⟨g,s⟩,rfl⟩:=
       IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.map I.primeCompl) g
     simp only [Function.uncurry_apply_pair]
     refine ⟨f.comp g,⟨g,rfl⟩,s,?_⟩
     apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
        (LocalizedModule.map I.primeCompl) s).injective
     simp only [Module.algebraMap_end_apply, ←Submonoid.smul_def,IsLocalizedModule.mk'_cancel',
       ←LinearMap.map_smul_of_tower]
     apply LinearMap.restrictScalars_injective R
     apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
     · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
     ext
     simp only [coe_comp,coe_restrictScalars,Function.comp_apply,
       LocalizedModule.mkLinearMap_apply,LocalizedModule.map_mk,llcomp_apply]
theorem Module.projective_of_localization_maximal (H:∀ (I:Ideal R) (_:I.IsMaximal),
   Module.Projective (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
   [Module.FinitePresentation R M]:Module.Projective R M:=by
 have:Module.Finite R M:=by infer_instance
 obtain ⟨s,hs⟩:=this
 let N:=s →₀ R
 let f:N →ₗ[R] M:=Finsupp.linearCombination R (Subtype.val:s → M)
 have hf:Function.Surjective f:=by
   rw [←LinearMap.range_eq_top,Finsupp.range_linearCombination,Subtype.range_val]
   convert! hs
 have (I:Ideal R) (hI:I.IsMaximal):=
   letI:=H I hI
   Module.projective_lifting_property (LocalizedModule.map I.primeCompl f) LinearMap.id
   (LocalizedModule.map_surjective _ _ hf)
 obtain ⟨g,hg⟩:=LinearMap.split_surjective_of_localization_maximal _ this
 exact Module.Projective.of_split _ _ hg
variable
 (Rₚ:∀ (P:Ideal R) [P.IsMaximal],Type*)
 [∀ (P:Ideal R) [P.IsMaximal],CommRing (Rₚ P)]
 [∀ (P:Ideal R) [P.IsMaximal],Algebra R (Rₚ P)]
 [∀ (P:Ideal R) [P.IsMaximal],IsLocalization.AtPrime (Rₚ P) P]
 (Mₚ:∀ (P:Ideal R) [P.IsMaximal],Type*)
 [∀ (P:Ideal R) [P.IsMaximal],AddCommGroup (Mₚ P)]
 [∀ (P:Ideal R) [P.IsMaximal],Module R (Mₚ P)]
 [∀ (P:Ideal R) [P.IsMaximal],Module (Rₚ P) (Mₚ P)]
 [∀ (P:Ideal R) [P.IsMaximal],IsScalarTower R (Rₚ P) (Mₚ P)]
 (f:∀ (P:Ideal R) [P.IsMaximal],M →ₗ[R] Mₚ P)
 [inst:∀ (P:Ideal R) [P.IsMaximal],IsLocalizedModule P.primeCompl (f P)]
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
include f in
theorem Module.projective_of_localization_maximal'
   (H:∀ (I:Ideal R) (_:I.IsMaximal),Module.Projective (Rₚ I) (Mₚ I))
   [Module.FinitePresentation R M]:Module.Projective R M:=by
 apply Module.projective_of_localization_maximal
 intro P hP
 set e:=(IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
 refine Module.Projective.of_equiv (M:=Mₚ P) (R:=Rₚ P)
   (σ:=e)
   { __:=IsLocalizedModule.linearEquiv P.primeCompl (f P)
       (LocalizedModule.mkLinearMap P.primeCompl M)
     map_smul':=?_}
 · intro r m
   obtain ⟨r,s,rfl⟩:=IsLocalization.exists_mk'_eq P.primeCompl r
   apply ((Module.End.isUnit_iff _).mp
     (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
   dsimp [e]
   simp only [←map_smul, ←smul_assoc,IsLocalization.smul_mk'_self,algebraMap_smul,
     IsLocalization.map_id_mk']
end ProximityFlatProofPort
end PackedLegacy_II

/-! Packed from ProximityPrize.SubmissionLower.IL. -/
section PackedLegacy_IL
section ProximityFlatProofPort
variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
 (S:Submonoid R) [AddCommGroup N'] [Module R N']
 {M':Type*} [AddCommGroup M'] [Module R M'] (f:M →ₗ[R] M') [IsLocalizedModule S f]
 {N':Type*} [AddCommGroup N'] [Module R N'] (g:N →ₗ[R] N') [IsLocalizedModule S g]
include f in
lemma Module.FinitePresentation.exists_basis_localizedModule_powers
   (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M']
   [IsLocalization S Rₛ] [Module.FinitePresentation R M]
   {I} [Finite I] (b:Basis I Rₛ M'):
   ∃ (r:R) (hr:r∈S)
     (b':Basis I (Localization (.powers r)) (LocalizedModule.Away r M)),
     ∀ i,(LocalizedModule.lift (.powers r) f fun s↦IsLocalizedModule.map_units f
       ⟨s.1,SetLike.le_def.mp (Submonoid.powers_le.mpr hr) s.2⟩) (b' i)=b i:=by
 have:Module.FinitePresentation R (I →₀ R):=Module.finitePresentation_of_projective _ _
 obtain ⟨r,hr,e,he⟩:=Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule S f
   (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ)) (b.repr.restrictScalars R)
 let e':=IsLocalizedModule.iso (.powers r) (Finsupp.mapRange.linearMap (α:=I)
   (Algebra.linearMap R (Localization (.powers r))))
 refine ⟨r,hr,.ofRepr (e ≪≫ₗ ?_),?_⟩
 · exact
   { __:=e',
     toLinearMap:=e'.extendScalarsOfIsLocalization (.powers r) (Localization (.powers r))}
 · intro i
   have:e'.symm _=_:=LinearMap.congr_fun (IsLocalizedModule.iso_symm_comp (.powers r)
     (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization (.powers r)))))
     (Finsupp.single i 1)
   simp only [Finsupp.mapRange.linearMap_apply,Finsupp.mapRange_single,Algebra.linearMap_apply,
     map_one,LocalizedModule.mkLinearMap_apply] at this
   change LocalizedModule.lift _ _ _ (e.symm (e'.symm _))=_
   replace he:=LinearMap.congr_fun he (e.symm (e'.symm (Finsupp.single i 1)))
   simp only [LinearMap.coe_comp,LinearMap.coe_restrictScalars,LinearEquiv.coe_coe,
     Function.comp_apply,LinearEquiv.apply_symm_apply,LinearEquiv.restrictScalars_apply] at he
   apply b.repr.injective
   rw [←he,Basis.repr_self,this,LocalizedModule.lift_mk]
   simp
include f in
lemma Module.FinitePresentation.exists_free_localizedModule_powers
   (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M'] [Nontrivial Rₛ]
   [IsLocalization S Rₛ] [Module.FinitePresentation R M] [Module.Free Rₛ M']:
   ∃ r,r∈S∧
     Module.Free (Localization (.powers r)) (LocalizedModule.Away r M)∧
     Module.finrank (Localization (.powers r)) (LocalizedModule.Away r M)=
       Module.finrank Rₛ M':=by
 let I:=Module.Free.ChooseBasisIndex Rₛ M'
 let b:Basis I Rₛ M':=Module.Free.chooseBasis Rₛ M'
 have:Module.Finite Rₛ M':=Module.Finite.of_isLocalizedModule S (Rₚ:=Rₛ) f
 obtain ⟨r,hr,b',_⟩:=Module.FinitePresentation.exists_basis_localizedModule_powers S f Rₛ b
 have:=(show Localization (.powers r) →+*Rₛ from IsLocalization.map (M:=.powers r) (T:=S) _
   (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
 refine ⟨r,hr,.of_basis b',?_⟩
 rw [Module.finrank_eq_nat_card_basis b,Module.finrank_eq_nat_card_basis b']
end ProximityFlatProofPort
end PackedLegacy_IL

/-! Packed from ProximityPrize.SubmissionLower.W1. -/
section PackedLegacy_W1
section ProximityFlatProofPort
variable {«X» «Y» «Z» α:Type*} [TopologicalSpace «X»]
open Set Filter
open scoped Topology
def IsLocallyConstant (f:«X» → «Y»):Prop:=
 ∀ s:Set «Y»,IsOpen (f ⁻¹' s)
namespace IsLocallyConstant
open List in
protected theorem tfae (f:«X» → «Y»):
   TFAE [IsLocallyConstant f,
     ∀ x,∀ᶠ x' in 𝓝 x,f x'=f x,
     ∀ x,IsOpen { x' | f x'=f x},
     ∀ y,IsOpen (f ⁻¹' {y}),
     ∀ x,∃ U:Set «X»,IsOpen U∧x∈U∧∀ x'∈U,f x'=f x]:=by
 tfae_have 1 → 4:=fun h y => h {y}
 tfae_have 4 → 3:=fun h x => h (f x)
 tfae_have 3 → 2:=fun h x => IsOpen.mem_nhds (h x) rfl
 tfae_have 2 → 5
 | h,x => by
   rcases mem_nhds_iff.1 (h x) with ⟨U,eq,hU,hx⟩
   exact ⟨U,hU,hx,eq⟩
 tfae_have 5 → 1
 | h,s => by
   refine isOpen_iff_forall_mem_open.2 fun x hx↦?_
   rcases h x with ⟨U,hU,hxU,eq⟩
   exact ⟨U,fun x' hx' => mem_preimage.2 <| (eq x' hx').symm ▸ hx,hU,hxU⟩
 tfae_finish
@[nontriviality]
theorem of_discrete [DiscreteTopology «X»] (f:«X» → «Y»):IsLocallyConstant f:=fun _ =>
 isOpen_discrete _
theorem isOpen_fiber {f:«X» → «Y»} (hf:IsLocallyConstant f) (y:«Y»):IsOpen { x | f x=y}:=
 hf {y}
theorem isClosed_fiber {f:«X» → «Y»} (hf:IsLocallyConstant f) (y:«Y»):IsClosed { x | f x=y}:=
 ⟨hf {y}ᶜ⟩
theorem isClopen_fiber {f:«X» → «Y»} (hf:IsLocallyConstant f) (y:«Y»):IsClopen { x | f x=y}:=
 ⟨isClosed_fiber hf _,isOpen_fiber hf _⟩
theorem iff_exists_open (f:«X» → «Y»):
   IsLocallyConstant f ↔ ∀ x,∃ U:Set «X»,IsOpen U∧x∈U∧∀ x'∈U,f x'=f x:=
 (IsLocallyConstant.tfae f).out 0 4
theorem iff_eventually_eq (f:«X» → «Y»):IsLocallyConstant f ↔ ∀ x,∀ᶠ y in 𝓝 x,f y=f x:=
 (IsLocallyConstant.tfae f).out 0 1
theorem exists_open {f:«X» → «Y»} (hf:IsLocallyConstant f) (x:«X»):
   ∃ U:Set «X»,IsOpen U∧x∈U∧∀ x'∈U,f x'=f x:=
 (iff_exists_open f).1 hf x
protected theorem eventually_eq {f:«X» → «Y»} (hf:IsLocallyConstant f) (x:«X»):
   ∀ᶠ y in 𝓝 x,f y=f x:=
 (iff_eventually_eq f).1 hf x
theorem iff_isOpen_fiber_apply {f:«X» → «Y»}:IsLocallyConstant f ↔ ∀ x,IsOpen (f ⁻¹' {f x}):=
 (IsLocallyConstant.tfae f).out 0 2
theorem iff_isOpen_fiber {f:«X» → «Y»}:IsLocallyConstant f ↔ ∀ y,IsOpen (f ⁻¹' {y}):=
 (IsLocallyConstant.tfae f).out 0 3
protected theorem continuous [TopologicalSpace «Y»] {f:«X» → «Y»} (hf:IsLocallyConstant f):
   Continuous f:=
 ⟨fun _ _ => hf _⟩
theorem iff_continuous {_:TopologicalSpace «Y»} [DiscreteTopology «Y»] (f:«X» → «Y»):
   IsLocallyConstant f ↔ Continuous f:=
 ⟨IsLocallyConstant.continuous,fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩
theorem of_constant (f:«X» → «Y») (h:∀ x y,f x=f y):IsLocallyConstant f:=
 (iff_eventually_eq f).2 fun _ => Eventually.of_forall fun _ => h _ _
protected theorem const (y:«Y»):IsLocallyConstant (Function.const «X» y):=
 of_constant _ fun _ _ => rfl
protected theorem comp {f:«X» → «Y»} (hf:IsLocallyConstant f) (g:«Y» → «Z»):
   IsLocallyConstant (g ∘ f):=fun s => by
 rw [Set.preimage_comp]
 exact hf _
theorem prodMk {Y'} {f:«X» → «Y»} {f':«X» → Y'} (hf:IsLocallyConstant f)
   (hf':IsLocallyConstant f'):IsLocallyConstant fun x => (f x,f' x):=
 (iff_eventually_eq _).2 fun x =>
   (hf.eventually_eq x).mp <| (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'
theorem comp₂ {Y₁ Y₂ «Z»:Type*} {f:«X» → Y₁} {g:«X» → Y₂} (hf:IsLocallyConstant f)
   (hg:IsLocallyConstant g) (h:Y₁ → Y₂ → «Z»):IsLocallyConstant fun x => h (f x) (g x):=
 (hf.prodMk hg).comp fun x:Y₁ × Y₂ => h x.1 x.2
theorem comp_continuous [TopologicalSpace «Y»] {g:«Y» → «Z»} {f:«X» → «Y»} (hg:IsLocallyConstant g)
   (hf:Continuous f):IsLocallyConstant (g ∘ f):=fun s => by
 rw [Set.preimage_comp]
 exact hf.isOpen_preimage _ (hg _)
theorem apply_eq_of_isPreconnected {f:«X» → «Y»} (hf:IsLocallyConstant f) {s:Set «X»}
   (hs:IsPreconnected s) {x y:«X»} (hx:x∈s) (hy:y∈s):f x=f y:=by
 let U:=f ⁻¹' {f y}
 suffices x∉Uᶜ from Classical.not_not.1 this
 intro hxV
 specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y,⟨hy,rfl⟩⟩ ⟨x,⟨hx,hxV⟩⟩
 · simp only [union_compl_self,subset_univ]
 · simp only [inter_empty,Set.not_nonempty_empty,inter_compl_self] at hs
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace «X»] {f:«X» → «Y»} (hf:IsLocallyConstant f)
   (x y:«X»):f x=f y:=
 hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
theorem eq_const [PreconnectedSpace «X»] {f:«X» → «Y»} (hf:IsLocallyConstant f) (x:«X»):
   f=Function.const «X» (f x):=
 funext fun y => hf.apply_eq_of_preconnectedSpace y x
theorem exists_eq_const [PreconnectedSpace «X»] [Nonempty «Y»] {f:«X» → «Y»} (hf:IsLocallyConstant f):
   ∃ y,f=Function.const «X» y:=by
 rcases isEmpty_or_nonempty «X» with h | h
 · exact ⟨Classical.arbitrary «Y»,funext <| h.elim⟩
 · exact ⟨f (Classical.arbitrary «X»),hf.eq_const _⟩
theorem iff_is_const [PreconnectedSpace «X»] {f:«X» → «Y»}:IsLocallyConstant f ↔ ∀ x y,f x=f y:=
 ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial,of_constant _⟩
theorem range_finite [CompactSpace «X»] {f:«X» → «Y»} (hf:IsLocallyConstant f):
   (Set.range f).Finite:=by
 letI:TopologicalSpace «Y»:=⊥;haveI:=discreteTopology_bot «Y»
 exact (isCompact_range hf.continuous).finite_of_discrete
@[to_additive]
theorem one [One «Y»]:IsLocallyConstant (1:«X» → «Y»):=IsLocallyConstant.const 1
@[to_additive]
theorem inv [Inv «Y»] ⦃f:«X» → «Y»⦄ (hf:IsLocallyConstant f):IsLocallyConstant f⁻¹:=
 hf.comp fun x => x⁻¹
@[to_additive]
theorem mul [Mul «Y»] ⦃f g:«X» → «Y»⦄ (hf:IsLocallyConstant f) (hg:IsLocallyConstant g):
   IsLocallyConstant (f*g):=
 hf.comp₂ hg (·*·)
@[to_additive]
theorem div [Div «Y»] ⦃f g:«X» → «Y»⦄ (hf:IsLocallyConstant f) (hg:IsLocallyConstant g):
   IsLocallyConstant (f/g):=
 hf.comp₂ hg (·/·)
theorem desc {α β:Type*} (f:«X» → α) (g:α → β) (h:IsLocallyConstant (g ∘ f))
   (inj:Function.Injective g):IsLocallyConstant f:=fun s => by
 rw [←preimage_image_eq s inj,preimage_preimage]
 exact h (g '' s)
theorem of_constant_on_connected_components [LocallyConnectedSpace «X»] {f:«X» → «Y»}
   (h:∀ x,∀ y∈connectedComponent x,f y=f x):IsLocallyConstant f:=
 (iff_exists_open _).2 fun x =>
   ⟨connectedComponent x,isOpen_connectedComponent,mem_connectedComponent,h x⟩
theorem of_constant_on_connected_clopens [LocallyConnectedSpace «X»] {f:«X» → «Y»}
   (h:∀ U:Set «X»,IsConnected U → IsClopen U → ∀ x∈U,∀ y∈U,f y=f x):
   IsLocallyConstant f:=
 of_constant_on_connected_components fun x =>
   h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
     mem_connectedComponent
theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace «X»] {f:«X» → «Y»}
   (h:∀ U:Set «X»,IsPreconnected U → IsClopen U → ∀ x∈U,∀ y∈U,f y=f x):
   IsLocallyConstant f:=
 of_constant_on_connected_clopens fun U hU↦h U hU.isPreconnected
end IsLocallyConstant
structure LocallyConstant («X» «Y»:Type*) [TopologicalSpace «X»] where
 protected toFun:«X» → «Y»
 protected isLocallyConstant:IsLocallyConstant toFun
namespace LocallyConstant
instance [Inhabited «Y»]:Inhabited (LocallyConstant «X» «Y»):=
 ⟨⟨_,IsLocallyConstant.const default⟩⟩
instance:FunLike (LocallyConstant «X» «Y») «X» «Y» where
 coe:=LocallyConstant.toFun
 coe_injective:=by rintro ⟨_,_⟩ ⟨_,_⟩ _;congr
def Simps.apply (f:LocallyConstant «X» «Y»):«X» → «Y»:=f
initialize_simps_projections LocallyConstant (toFun → apply)
@[simp]
theorem toFun_eq_coe (f:LocallyConstant «X» «Y»):f.toFun=f:=
 rfl
@[simp]
theorem coe_mk (f:«X» → «Y») (h):⇑(⟨f,h⟩:LocallyConstant «X» «Y»)=f:=
 rfl
protected theorem congr_fun {f g:LocallyConstant «X» «Y»} (h:f=g) (x:«X»):f x=g x:=
 DFunLike.congr_fun h x
protected theorem congr_arg (f:LocallyConstant «X» «Y») {x y:«X»} (h:x=y):f x=f y:=
 DFunLike.congr_arg f h
theorem coe_injective:@Function.Injective (LocallyConstant «X» «Y») («X» → «Y») (↑):=fun _ _ =>
 DFunLike.ext'
@[norm_cast]
theorem coe_inj {f g:LocallyConstant «X» «Y»}:(f:«X» → «Y»)=g ↔ f=g:=
 coe_injective.eq_iff
@[ext]
theorem ext ⦃f g:LocallyConstant «X» «Y»⦄ (h:∀ x,f x=g x):f=g:=
 DFunLike.ext _ _ h
section CodomainTopologicalSpace
variable [TopologicalSpace «Y»] (f:LocallyConstant «X» «Y»)
protected theorem continuous:Continuous f:=
 f.isLocallyConstant.continuous
@[coe] def toContinuousMap:C(«X»,«Y»):=
 ⟨f,f.continuous⟩
instance:Coe (LocallyConstant «X» «Y») C(«X»,«Y»):=⟨toContinuousMap⟩
@[simp] theorem coe_continuousMap:((f:C(«X»,«Y»)):«X» → «Y»)=(f:«X» → «Y»):=rfl
theorem toContinuousMap_injective:
   Function.Injective (toContinuousMap:LocallyConstant «X» «Y» → C(«X»,«Y»)):=fun _ _ h =>
 ext (ContinuousMap.congr_fun h)
end CodomainTopologicalSpace
def const («X»:Type*) {«Y»:Type*} [TopologicalSpace «X»] (y:«Y»):LocallyConstant «X» «Y»:=
 ⟨Function.const «X» y,IsLocallyConstant.const _⟩
@[simp]
theorem coe_const (y:«Y»):(const «X» y:«X» → «Y»)=Function.const «X» y:=
 rfl
@[simps]
def eval {ι:Type*} {«X»:ι → Type*}
   [∀ i,TopologicalSpace («X» i)] (i:ι) [DiscreteTopology («X» i)]:
   LocallyConstant (Π i,«X» i) («X» i) where
 toFun:=fun f↦f i
 isLocallyConstant:=(IsLocallyConstant.iff_continuous _).mpr <| continuous_apply i
def ofIsClopen {«X»:Type*} [TopologicalSpace «X»] {U:Set «X»} [∀ x,Decidable (x∈U)]
   (hU:IsClopen U):LocallyConstant «X» (Fin 2) where
 toFun x:=if x∈U then 0 else 1
 isLocallyConstant:=by
   refine IsLocallyConstant.iff_isOpen_fiber.2 <| Fin.forall_fin_two.2 ⟨?_,?_⟩
   · convert! hU.2 using 1
     ext
     simp only [mem_singleton_iff,Fin.one_eq_zero_iff,mem_preimage,ite_eq_left_iff,
       Nat.succ_succ_ne_one]
     tauto
   · rw [←isClosed_compl_iff]
     convert! hU.1
     ext
     simp
@[simp]
theorem ofIsClopen_fiber_zero {«X»:Type*} [TopologicalSpace «X»] {U:Set «X»} [∀ x,Decidable (x∈U)]
   (hU:IsClopen U):ofIsClopen hU ⁻¹' ({0}:Set (Fin 2))=U:=by
 ext
 simp only [ofIsClopen,mem_singleton_iff,Fin.one_eq_zero_iff,coe_mk,mem_preimage,
   ite_eq_left_iff,Nat.succ_succ_ne_one]
 tauto
@[simp]
theorem ofIsClopen_fiber_one {«X»:Type*} [TopologicalSpace «X»] {U:Set «X»} [∀ x,Decidable (x∈U)]
   (hU:IsClopen U):ofIsClopen hU ⁻¹' ({1}:Set (Fin 2))=Uᶜ:=by
 ext
 simp only [ofIsClopen,mem_singleton_iff,coe_mk,Fin.zero_eq_one_iff,mem_preimage,
   ite_eq_right_iff,mem_compl_iff,Nat.succ_succ_ne_one]
theorem locallyConstant_eq_of_fiber_zero_eq {«X»:Type*} [TopologicalSpace «X»]
   (f g:LocallyConstant «X» (Fin 2)) (h:f ⁻¹' ({0}:Set (Fin 2))=g ⁻¹' {0}):f=g:=by
 simp only [Set.ext_iff,mem_singleton_iff,mem_preimage] at h
 ext1 x
 exact Fin.fin_two_eq_of_eq_zero_iff (h x)
theorem range_finite [CompactSpace «X»] (f:LocallyConstant «X» «Y»):(Set.range f).Finite:=
 f.isLocallyConstant.range_finite
theorem apply_eq_of_isPreconnected (f:LocallyConstant «X» «Y») {s:Set «X»} (hs:IsPreconnected s)
   {x y:«X»} (hx:x∈s) (hy:y∈s):f x=f y:=
 f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace «X»] (f:LocallyConstant «X» «Y») (x y:«X»):
   f x=f y:=
 f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
theorem eq_const [PreconnectedSpace «X»] (f:LocallyConstant «X» «Y») (x:«X»):f=const «X» (f x):=
 ext fun _ => apply_eq_of_preconnectedSpace f _ _
theorem exists_eq_const [PreconnectedSpace «X»] [Nonempty «Y»] (f:LocallyConstant «X» «Y»):
   ∃ y,f=const «X» y:=by
 rcases Classical.em (Nonempty «X») with (⟨⟨x⟩⟩ | hX)
 · exact ⟨f x,f.eq_const x⟩
 · exact ⟨Classical.arbitrary «Y»,ext fun x => (hX ⟨x⟩).elim⟩
def map (f:«Y» → «Z») (g:LocallyConstant «X» «Y»):LocallyConstant «X» «Z»:=
 ⟨f ∘ g,g.isLocallyConstant.comp f⟩
@[simp]
theorem map_apply (f:«Y» → «Z») (g:LocallyConstant «X» «Y»):⇑(map f g)=f ∘ g:=
 rfl
@[simp]
theorem map_id:@map «X» «Y» «Y» _ id=id:=rfl
@[simp]
theorem map_comp {Y₁ Y₂ Y₃:Type*} (g:Y₂ → Y₃) (f:Y₁ → Y₂):
   @map «X» _ _ _ g ∘ map f=map (g ∘ f):=rfl
def flip {«X» α β:Type*} [TopologicalSpace «X»] (f:LocallyConstant «X» (α → β)) (a:α):
   LocallyConstant «X» β:=
 f.map fun f => f a
def unflip {«X» α β:Type*} [Finite α] [TopologicalSpace «X»] (f:α → LocallyConstant «X» β):
   LocallyConstant «X» (α → β) where
 toFun x a:=f a x
 isLocallyConstant:=IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
   have:(fun (x:«X») (a:α) => f a x) ⁻¹' {g}=⋂ a:α,f a ⁻¹' {g a}:=by
     ext;simp [funext_iff]
   rw [this]
   exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _
@[simp]
theorem unflip_flip {«X» α β:Type*} [Finite α] [TopologicalSpace «X»]
   (f:LocallyConstant «X» (α → β)):unflip f.flip=f:=rfl
@[simp]
theorem flip_unflip {«X» α β:Type*} [Finite α] [TopologicalSpace «X»]
   (f:α → LocallyConstant «X» β):(unflip f).flip=f:=rfl
section Comap
variable [TopologicalSpace «Y»]
def comap (f:C(«X»,«Y»)) (g:LocallyConstant «Y» «Z»):LocallyConstant «X» «Z»:=
 ⟨g ∘ f,g.isLocallyConstant.comp_continuous f.continuous⟩
@[simp]
theorem coe_comap (f:C(«X»,«Y»)) (g:LocallyConstant «Y» «Z»):
   (comap f g)=g ∘ f:=rfl
theorem coe_comap_apply (f:C(«X»,«Y»)) (g:LocallyConstant «Y» «Z») (x:«X»):
   comap f g x=g (f x):=rfl
@[simp]
theorem comap_id:comap (@ContinuousMap.id «X» _)=@id (LocallyConstant «X» «Z»):=rfl
theorem comap_comp {W:Type*} [TopologicalSpace W] (f:C(W,«X»)) (g:C(«X»,«Y»)):
   comap («Z»:=«Z») (g.comp f)=comap f ∘ comap g:=rfl
theorem comap_comap {W:Type*} [TopologicalSpace W] (f:C(W,«X»)) (g:C(«X»,«Y»))
   (x:LocallyConstant «Y» «Z»):comap f (comap g x)=comap (g.comp f) x:=rfl
theorem comap_const (f:C(«X»,«Y»)) (y:«Y») (h:∀ x,f x=y):
   (comap f:LocallyConstant «Y» «Z» → LocallyConstant «X» «Z»)=fun g => const «X» (g y):=by
 ext;simp [h]
lemma comap_injective (f:C(«X»,«Y»)) (hfs:f.1.Surjective):
   (comap («Z»:=«Z») f).Injective:=by
 intro a b h
 ext y
 obtain ⟨x,hx⟩:=hfs y
 simpa [←hx] using LocallyConstant.congr_fun h x
end Comap
section Desc
def desc {«X» α β:Type*} [TopologicalSpace «X»] {g:α → β} (f:«X» → α) (h:LocallyConstant «X» β)
   (cond:g ∘ f=h) (inj:Function.Injective g):LocallyConstant «X» α where
 toFun:=f
 isLocallyConstant:=IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj
@[simp]
theorem coe_desc {«X» α β:Type*} [TopologicalSpace «X»] (f:«X» → α) (g:α → β)
   (h:LocallyConstant «X» β) (cond:g ∘ f=h) (inj:Function.Injective g):
   ⇑(desc f h cond inj)=f:=
 rfl
end Desc
section Indicator
variable {R:Type*} [One R] {U:Set «X»} (f:LocallyConstant «X» R)
@[to_additive (attr:=simps)
  ]
noncomputable def mulIndicator (hU:IsClopen U):LocallyConstant «X» R where
 toFun:=Set.mulIndicator U f
 isLocallyConstant:=fun s => by
   rw [mulIndicator_preimage,Set.ite,Set.sdiff_eq]
   exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)
variable (a:«X»)
open scoped Classical in
@[to_additive]
theorem mulIndicator_apply_eq_if (hU:IsClopen U):
   mulIndicator f hU a=if a∈U then f a else 1:=
 Set.mulIndicator_apply U f a
variable {a}
@[to_additive]
theorem mulIndicator_of_mem (hU:IsClopen U) (h:a∈U):f.mulIndicator hU a=f a:=
 Set.mulIndicator_of_mem h _
@[to_additive]
theorem mulIndicator_of_notMem (hU:IsClopen U) (h:a∉U):f.mulIndicator hU a=1:=
 Set.mulIndicator_of_notMem h _
end Indicator
section Equiv
@[simps]
def congrLeft [TopologicalSpace «Y»] (e:«X» ≃ₜ «Y»):LocallyConstant «X» «Z» ≃ LocallyConstant «Y» «Z» where
 toFun:=comap e.symm
 invFun:=comap e
 left_inv:=by
   intro
   simp [comap_comap]
 right_inv:=by
   intro
   simp [comap_comap]
@[simps]
def congrRight (e:«Y» ≃ «Z»):LocallyConstant «X» «Y» ≃ LocallyConstant «X» «Z» where
 toFun:=map e
 invFun:=map e.symm
 left_inv:=by intro;ext;simp
 right_inv:=by intro;ext;simp
variable («X») in
def equivClopens [∀ (s:Set «X») x,Decidable (x∈s)]:
   LocallyConstant «X» (Fin 2) ≃ TopologicalSpace.Clopens «X» where
 toFun f:=⟨f ⁻¹' {0},f.2.isClopen_fiber _⟩
 invFun s:=ofIsClopen s.2
 left_inv _:=locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
 right_inv _:=by simp
end Equiv
section Piecewise
def piecewise {C₁ C₂:Set «X»} (h₁:IsClosed C₁) (h₂:IsClosed C₂) (h:C₁ ∪ C₂=Set.univ)
   (f:LocallyConstant C₁ «Z») (g:LocallyConstant C₂ «Z»)
   (hfg:∀ (x:«X») (hx:x∈C₁ ∩ C₂),f ⟨x,hx.1⟩=g ⟨x,hx.2⟩)
   [DecidablePred (·∈C₁)]:LocallyConstant «X» «Z» where
 toFun i:=if hi:i∈C₁ then f ⟨i,hi⟩ else g ⟨i,(Set.compl_subset_iff_union.mpr h) hi⟩
 isLocallyConstant:=by
   let dZ:TopologicalSpace «Z»:=⊥
   haveI:DiscreteTopology «Z»:=discreteTopology_bot «Z»
   obtain ⟨f,hf⟩:=f
   obtain ⟨g,hg⟩:=g
   rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
   dsimp only [coe_mk]
   rw [Set.union_eq_iUnion] at h
   refine (locallyFinite_of_finite _).continuous h (fun i↦?_) (fun i↦?_)
   · cases i <;> [exact h₂;exact h₁]
   · cases i <;> rw [continuousOn_iff_continuous_restrict]
     · convert! hg
       ext x
       simp only [cond_false,restrict_apply,Subtype.coe_eta,dite_eq_right_iff]
       exact fun hx↦hfg x ⟨hx,x.prop⟩
     · simp only [cond_true,restrict_dite,Subtype.coe_eta]
       exact hf
@[simp]
lemma piecewise_apply_left {C₁ C₂:Set «X»} (h₁:IsClosed C₁) (h₂:IsClosed C₂)
   (h:C₁ ∪ C₂=Set.univ) (f:LocallyConstant C₁ «Z») (g:LocallyConstant C₂ «Z»)
   (hfg:∀ (x:«X») (hx:x∈C₁ ∩ C₂),f ⟨x,hx.1⟩=g ⟨x,hx.2⟩)
   [DecidablePred (·∈C₁)] (x:«X») (hx:x∈C₁):
   piecewise h₁ h₂ h f g hfg x=f ⟨x,hx⟩:=by
 simp only [piecewise,
   coe_mk]
 rw [dif_pos hx]
@[simp]
lemma piecewise_apply_right {C₁ C₂:Set «X»} (h₁:IsClosed C₁) (h₂:IsClosed C₂)
   (h:C₁ ∪ C₂=Set.univ) (f:LocallyConstant C₁ «Z») (g:LocallyConstant C₂ «Z»)
   (hfg:∀ (x:«X») (hx:x∈C₁ ∩ C₂),f ⟨x,hx.1⟩=g ⟨x,hx.2⟩)
   [DecidablePred (·∈C₁)] (x:«X») (hx:x∈C₂):
   piecewise h₁ h₂ h f g hfg x=g ⟨x,hx⟩:=by
 simp only [piecewise,
   coe_mk]
 split_ifs with h
 · exact hfg x ⟨h,hx⟩
 · rfl
def piecewise' {C₀ C₁ C₂:Set «X»} (h₀:C₀ ⊆ C₁ ∪ C₂) (h₁:IsClosed C₁)
   (h₂:IsClosed C₂) (f₁:LocallyConstant C₁ «Z») (f₂:LocallyConstant C₂ «Z»)
   [DecidablePred (·∈C₁)] (hf:∀ x (hx:x∈C₁ ∩ C₂),f₁ ⟨x,hx.1⟩=f₂ ⟨x,hx.2⟩):
   LocallyConstant C₀ «Z»:=
 letI:∀ j:C₀,Decidable (j∈Subtype.val ⁻¹' C₁):=fun j↦decidable_of_iff (↑j∈C₁) Iff.rfl
 piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
   (by simpa [eq_univ_iff_forall] using! h₀)
   (f₁.comap ⟨(restrictPreimage C₁ ((↑):C₀ → «X»)),continuous_subtype_val.restrictPreimage⟩)
   (f₂.comap ⟨(restrictPreimage C₂ ((↑):C₀ → «X»)),continuous_subtype_val.restrictPreimage⟩) <| by
     rintro ⟨x,hx₀⟩ ⟨hx₁:x∈C₁,hx₂:x∈C₂⟩
     simpa using hf x ⟨hx₁,hx₂⟩
@[simp]
lemma piecewise'_apply_left {C₀ C₁ C₂:Set «X»} (h₀:C₀ ⊆ C₁ ∪ C₂) (h₁:IsClosed C₁)
   (h₂:IsClosed C₂) (f₁:LocallyConstant C₁ «Z») (f₂:LocallyConstant C₂ «Z»)
   [DecidablePred (·∈C₁)] (hf:∀ x (hx:x∈C₁ ∩ C₂),f₁ ⟨x,hx.1⟩=f₂ ⟨x,hx.2⟩)
   (x:C₀) (hx:x.val∈C₁):
   piecewise' h₀ h₁ h₂ f₁ f₂ hf x=f₁ ⟨x.val,hx⟩:=by
 letI:∀ j:C₀,Decidable (j∈Subtype.val ⁻¹' C₁):=fun j↦decidable_of_iff (↑j∈C₁) Iff.rfl
 rw [piecewise',piecewise_apply_left (f:=(f₁.comap
   ⟨(restrictPreimage C₁ ((↑):C₀ → «X»)),continuous_subtype_val.restrictPreimage⟩))
   (hx:=hx)]
 rfl
@[simp]
lemma piecewise'_apply_right {C₀ C₁ C₂:Set «X»} (h₀:C₀ ⊆ C₁ ∪ C₂) (h₁:IsClosed C₁)
   (h₂:IsClosed C₂) (f₁:LocallyConstant C₁ «Z») (f₂:LocallyConstant C₂ «Z»)
   [DecidablePred (·∈C₁)] (hf:∀ x (hx:x∈C₁ ∩ C₂),f₁ ⟨x,hx.1⟩=f₂ ⟨x,hx.2⟩)
   (x:C₀) (hx:x.val∈C₂):
   piecewise' h₀ h₁ h₂ f₁ f₂ hf x=f₂ ⟨x.val,hx⟩:=by
 letI:∀ j:C₀,Decidable (j∈Subtype.val ⁻¹' C₁):=fun j↦decidable_of_iff (↑j∈C₁) Iff.rfl
 rw [piecewise',piecewise_apply_right (f:=(f₁.comap
   ⟨(restrictPreimage C₁ ((↑):C₀ → «X»)),continuous_subtype_val.restrictPreimage⟩))
   (hx:=hx)]
 rfl
end Piecewise
end LocallyConstant
end ProximityFlatProofPort
end PackedLegacy_W1

/-! Packed from ProximityPrize.SubmissionLower.U8. -/
section PackedLegacy_U8
section ProximityFlatProofPort
variable {R S:Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
namespace IsBaseChange
open TensorProduct
lemma prodMap {M N M' N':Type*}
   [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
   [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
   [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
   (f:M →ₗ[R] M') (g:N →ₗ[R] N') (hf:IsBaseChange S f) (hg:IsBaseChange S g):
   IsBaseChange S (f.prodMap g):=by
 apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
 intro p
 simp [equiv_tmul]
lemma pi {ι:Type*} [Finite ι]
   {M M':ι → Type*} [∀ i,AddCommMonoid (M i)] [∀ i,AddCommMonoid (M' i)]
   [∀ i,Module R (M i)] [∀ i,Module R (M' i)] [∀ i,Module S (M' i)]
   [∀ i,IsScalarTower R S (M' i)]
   (f:∀ i,M i →ₗ[R] M' i) (hf:∀ i,IsBaseChange S (f i)):
   IsBaseChange S (.pi fun i↦f i ∘ₗ .proj i):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 cases nonempty_fintype ι
 apply of_equiv <| piRight R S _ M ≪≫ₗ .piCongrRight fun i↦(hf i).equiv
 intro x
 ext i
 simp [equiv_tmul]
theorem finitePow (ι:Type*) [Finite ι]
   {M M':Type*} [AddCommMonoid M] [AddCommMonoid M']
   [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
   {f:M →ₗ[R] M'} (hf:IsBaseChange S f):
   IsBaseChange S (f.compLeft ι):=
 IsBaseChange.pi (f:=fun _↦f) (fun _↦hf)
end IsBaseChange
namespace IsLocalizedModule
variable (S:Submonoid R)
attribute [local instance] IsLocalizedModule.isScalarTower_module
instance prodMap {M N M' N':Type*}
   [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
   [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
   (f:M →ₗ[R] M') (g:N →ₗ[R] N')
   [IsLocalizedModule S f] [IsLocalizedModule S g]:
   IsLocalizedModule S (f.prodMap g):=by
 letI:Module (Localization S) M':=IsLocalizedModule.module S f
 letI:Module (Localization S) N':=IsLocalizedModule.module S g
 rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
 apply IsBaseChange.prodMap
 · rw [←isLocalizedModule_iff_isBaseChange S]
   infer_instance
 · rw [←isLocalizedModule_iff_isBaseChange S]
   infer_instance
instance pi {ι:Type*} [Finite ι]
   {M M':ι → Type*} [∀ i,AddCommMonoid (M i)] [∀ i,AddCommMonoid (M' i)]
   [∀ i,Module R (M i)] [∀ i,Module R (M' i)]
   (f:∀ i,M i →ₗ[R] M' i) [∀ i,IsLocalizedModule S (f i)]:
   IsLocalizedModule S (.pi fun i↦f i ∘ₗ .proj i):=by
 letI (i:ι):Module (Localization S) (M' i):=IsLocalizedModule.module S (f i)
 rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
 apply IsBaseChange.pi
 intro i
 rw [←isLocalizedModule_iff_isBaseChange S]
 infer_instance
end IsLocalizedModule
namespace IsBaseChange
section DirectSum
open TensorProduct LinearMap DirectSum
variable {ι:Type*}
   {N:ι → Type*} [(i:ι) → AddCommMonoid (N i)] [(i:ι) → Module R (N i)]
   {P:ι → Type*} [∀ i,AddCommMonoid (P i)] [∀ i,Module R (P i)]
   [∀ i,Module S (P i)] [∀ i,IsScalarTower R S (P i)]
   {ε:(i:ι) → N i →ₗ[R] P i}
theorem directSum (ibc:∀ i,IsBaseChange S (ε i)):
   IsBaseChange S (lmap ε):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 apply of_equiv <| directSumRight R S S N ≪≫ₗ congrLinearEquiv fun i↦(ibc i).equiv
 intros;ext
 simp [coe_directSumRight,coe_congrLinearEquiv,equiv_tmul]
variable (ι)
   {M M':Type*} [AddCommMonoid M] [AddCommMonoid M']
   [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
   {ε:M →ₗ[R] M'}
theorem directSumPow (ibc:IsBaseChange S ε):
   IsBaseChange S (lmap fun _:ι↦ε):=
 directSum (fun _:ι↦ibc)
theorem finsuppPow (ibc:IsBaseChange S ε):
   IsBaseChange S (Finsupp.mapRange.linearMap (α:=ι) ε):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 apply of_equiv <|
   LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
     (directSum (fun _↦ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
 intro x
 rw [LinearEquiv.trans_apply,Finsupp.mapRange.linearMap_apply,
   LinearEquiv.symm_apply_eq]
 ext
 simp [LinearEquiv.baseChange_tmul,IsBaseChange.equiv_tmul,lmap_finsuppLEquivDirectSum_eq]
end DirectSum
end IsBaseChange
end ProximityFlatProofPort
end PackedLegacy_U8

/-! Packed from ProximityPrize.SubmissionLower.IX. -/
section PackedLegacy_IX
section ProximityFlatProofPort
universe uR uM
variable (R:Type uR) (M:Type uM) [CommRing R] [AddCommGroup M] [Module R M]
namespace Module
open PrimeSpectrum TensorProduct
def freeLocus:Set (PrimeSpectrum R):=
 { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)}
variable {R M}
lemma mem_freeLocus {p}:p∈freeLocus R M ↔
   Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M):=
 Iff.rfl
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_of_isLocalization (p:PrimeSpectrum R)
   (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
   [AddCommGroup Mₚ] [Module R Mₚ] (f:M →ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
   [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]:
   p∈freeLocus R M ↔ Module.Free Rₚ Mₚ:=by
 set e:=(IsLocalization.algEquiv p.asIdeal.primeCompl
     (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
 apply Module.Free.iff_of_equiv (σ:=e)
 refine { __:=IsLocalizedModule.iso p.asIdeal.primeCompl f,map_smul':=?_}
 intro r x
 obtain ⟨r,s,rfl⟩:=IsLocalization.exists_mk'_eq p.asIdeal.primeCompl r
 apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
 simp [e, ←map_smul, ←smul_assoc]
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_iff_tensor (p:PrimeSpectrum R)
   (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]:
   p∈freeLocus R M ↔ Module.Free Rₚ (Rₚ ⊗[R] M):=by
 exact mem_freeLocus_of_isLocalization p Rₚ (f:=TensorProduct.mk R Rₚ M 1)
lemma freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e:M ≃ₗ[R] M'):
   freeLocus R M=freeLocus R M':=by
 ext p
 exact mem_freeLocus_of_isLocalization _ _ _
   (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
lemma comap_freeLocus_le {A} [CommRing A] [Algebra R A]:
   comap (algebraMap R A) ⁻¹' freeLocus R M ≤ freeLocus A (A ⊗[R] M):=by
 intro p hp
 let Rₚ:=Localization.AtPrime (comap (algebraMap R A) p).asIdeal
 let Aₚ:=Localization.AtPrime p.asIdeal
 rw [Set.mem_preimage,mem_freeLocus_iff_tensor _ Rₚ] at hp
 rw [mem_freeLocus_iff_tensor _ Aₚ]
 letI algebra:Algebra Rₚ Aₚ:=(Localization.localRingHom
   (comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) rfl).toAlgebra
 have:IsScalarTower R Rₚ Aₚ:=IsScalarTower.of_algebraMap_eq'
   (by simp [Rₚ,Aₚ,algebra,RingHom.algebraMap_toAlgebra,Localization.localRingHom,
       ←IsScalarTower.algebraMap_eq])
 let e:=AlgebraTensorModule.cancelBaseChange R Rₚ Aₚ Aₚ M ≪≫ₗ
   (AlgebraTensorModule.cancelBaseChange R A Aₚ Aₚ M).symm
 exact .of_equiv e
lemma freeLocus_localization (S:Submonoid R):
   freeLocus (Localization S) (LocalizedModule S M)=
     comap (algebraMap R _) ⁻¹' freeLocus R M:=by
 ext p
 simp only [Set.mem_preimage]
 let p':=p.asIdeal.comap (algebraMap R _)
 have hp':S ≤ p'.primeCompl:=fun x hx H↦
   p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x,hx⟩))
 let Rₚ:=Localization.AtPrime p'
 let Mₚ:=LocalizedModule p'.primeCompl M
 letI:Algebra (Localization S) Rₚ:=
   IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S p'.primeCompl hp'
 have:IsScalarTower R (Localization S) Rₚ:=
   IsLocalization.localization_isScalarTower_of_submonoid_le ..
 have:IsLocalization.AtPrime Rₚ p.asIdeal:=by
   have:=IsLocalization.isLocalization_of_submonoid_le (Localization S) Rₚ _ _ hp'
   apply IsLocalization.isLocalization_of_is_exists_mul_mem _
     (Submonoid.map (algebraMap R (Localization S)) p'.primeCompl)
   · rintro _ ⟨x,hx,rfl⟩;exact hx
   · rintro ⟨x,hx⟩
     obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq S x
     refine ⟨algebraMap _ _ s.1,x,fun H↦hx ?_,by simp⟩
     rw [IsLocalization.mk'_eq_mul_mk'_one]
     exact Ideal.mul_mem_right _ _ H
 letI:Module (Localization S) Mₚ:=Module.compHom Mₚ (algebraMap _ Rₚ)
 have:IsScalarTower R (Localization S) Mₚ:=
   ⟨fun r r' m↦show algebraMap _ Rₚ (r • r') • m=_ by
     simp [p',Rₚ,Mₚ,Algebra.smul_def, ←IsScalarTower.algebraMap_apply,mul_smul];rfl⟩
 have:IsScalarTower (Localization S) Rₚ Mₚ:=
   ⟨fun r r' m↦show _=algebraMap _ Rₚ r • r' • m by rw [←mul_smul, ←Algebra.smul_def]⟩
 let l:=(IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
   (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization S
   (Localization S)
 have:IsLocalizedModule p.asIdeal.primeCompl l:=by
   have:IsLocalizedModule p'.primeCompl (l.restrictScalars R):=
     inferInstanceAs (IsLocalizedModule p'.primeCompl
       (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
       (LocalizedModule.mkLinearMap p'.primeCompl M)))
   have:IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl) l:=
     IsLocalizedModule.of_restrictScalars p'.primeCompl ..
   apply IsLocalizedModule.of_exists_mul_mem
     (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl)
   · rintro _ ⟨x,hx,rfl⟩;exact hx
   · rintro ⟨x,hx⟩
     obtain ⟨x,s,rfl⟩:=IsLocalization.exists_mk'_eq S x
     refine ⟨algebraMap _ _ s.1,x,fun H↦hx ?_,by simp⟩
     rw [IsLocalization.mk'_eq_mul_mk'_one]
     exact Ideal.mul_mem_right _ _ H
 rw [mem_freeLocus_of_isLocalization (R:=Localization S) p Rₚ Mₚ l]
 rfl
lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M]:
   freeLocus R M=Set.univ ↔ Module.Projective R M:=by
 simp_rw [Set.eq_univ_iff_forall,mem_freeLocus]
 exact ⟨fun H↦Module.projective_of_localization_maximal fun I hI↦
   have:=H ⟨I,hI.isPrime⟩;.of_free,fun H x↦Module.free_of_flat_of_isLocalRing⟩
lemma freeLocus_eq_univ [Module.Finite R M] [Module.Flat R M]:
   freeLocus R M=Set.univ:=by
 simp_rw [Set.eq_univ_iff_forall,mem_freeLocus]
 exact fun x↦Module.free_of_flat_of_isLocalRing
lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f:R}:
   (basicOpen f:Set (PrimeSpectrum R)) ⊆ freeLocus R M ↔
     Module.Projective (Localization.Away f) (LocalizedModule.Away f M):=by
 rw [←freeLocus_eq_univ_iff,freeLocus_localization,
   Set.preimage_eq_univ_iff,localization_away_comap_range _ f]
lemma isOpen_freeLocus [Module.FinitePresentation R M]:
   IsOpen (freeLocus R M):=by
 refine isOpen_iff_forall_mem_open.mpr fun x hx↦?_
 have:Module.Free _ _:=hx
 obtain ⟨r,hr,hr',_⟩:=Module.FinitePresentation.exists_free_localizedModule_powers
   x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
   (Localization.AtPrime x.asIdeal)
 exact ⟨basicOpen r,basicOpen_subset_freeLocus_iff.mpr inferInstance,(basicOpen r).2,hr⟩
variable (M) in
noncomputable
def rankAtStalk (p:PrimeSpectrum R):ℕ:=
 Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)
lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M]:
   IsLocallyConstant (fun x:freeLocus R M↦rankAtStalk M x.1):=by
 refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x,hx⟩↦?_
 have:Module.Free _ _:=hx
 obtain ⟨f,hf,hf',hf''⟩:=Module.FinitePresentation.exists_free_localizedModule_powers
   x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
   (Localization.AtPrime x.asIdeal)
 refine ⟨Subtype.val ⁻¹' basicOpen f,(basicOpen f).2.preimage continuous_subtype_val,hf,?_⟩
 rintro ⟨p,hp''⟩ hp
 let p':=Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
 have hp':Submonoid.powers f ≤ p.asIdeal.primeCompl:=by
   simpa [Submonoid.powers_le,Ideal.primeCompl]
 let Rₚ:=Localization.AtPrime p.asIdeal
 let Mₚ:=LocalizedModule p.asIdeal.primeCompl M
 letI:Algebra (Localization.Away f) Rₚ:=
   IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
 have:IsScalarTower R (Localization.Away f) Rₚ:=
   IsLocalization.localization_isScalarTower_of_submonoid_le ..
 letI:Module (Localization.Away f) Mₚ:=Module.compHom Mₚ (algebraMap _ Rₚ)
 have:IsScalarTower R (Localization.Away f) Mₚ:=
   ⟨fun r r' m↦show algebraMap _ Rₚ (r • r') • m=_ by
     simp [Rₚ,Mₚ,Algebra.smul_def, ←IsScalarTower.algebraMap_apply,mul_smul];rfl⟩
 have:IsScalarTower (Localization.Away f) Rₚ Mₚ:=
   ⟨fun r r' m↦show _=algebraMap _ Rₚ r • r' • m by rw [←mul_smul, ←Algebra.smul_def]⟩
 let l:=(IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
   (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
   (Localization.Away f)
 have:IsLocalization p' Rₚ:=
   IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
 have:IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R):=
   inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
   ((IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
     (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
 have:IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l:=
     IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
 have:=Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
 simp [Rₚ,rankAtStalk,this,hf'']
lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat R M]:
   IsLocallyConstant (rankAtStalk (R:=R) M):=by
 let e:freeLocus R M ≃ₜ PrimeSpectrum R:=
   (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
 convert! isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous
@[simp]
lemma rankAtStalk_eq_zero_of_subsingleton [Subsingleton M]:
   rankAtStalk (R:=R) M=0:=by
 ext p
 exact Module.finrank_zero_of_subsingleton
lemma nontrivial_of_rankAtStalk_pos (h:0 < rankAtStalk (R:=R) M):
   Nontrivial M:=by
 by_contra! hn
 simp at h
lemma rankAtStalk_eq_of_equiv {N:Type*} [AddCommGroup N] [Module R N] (e:M ≃ₗ[R] N):
   rankAtStalk (R:=R) M=rankAtStalk N:=by
 ext p
 exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
   (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
   (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e |>.finrank_eq
@[simp]
lemma rankAtStalk_eq_finrank_of_free [Module.Free R M]:
   rankAtStalk (R:=R) M=Module.finrank R M:=by
 ext p
 simp [rankAtStalk,finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
   (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]
lemma rankAtStalk_self [Nontrivial R]:rankAtStalk (R:=R) R=1:=by
 simp
open LocalizedModule Localization
lemma rankAtStalk_pi {ι:Type*} [Finite ι] (M:ι → Type*)
   [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] [∀ i,Module.Flat R (M i)]
   [∀ i,Module.Finite R (M i)] (p:PrimeSpectrum R):
   rankAtStalk (Π i,M i) p=∑ᶠ i,rankAtStalk (M i) p:=by
 cases nonempty_fintype ι
 let f:(Π i,M i) →ₗ[R] Π i,LocalizedModule p.asIdeal.primeCompl (M i):=
   .pi (fun i↦mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
 let e:LocalizedModule p.asIdeal.primeCompl (Π i,M i) ≃ₗ[Localization.AtPrime p.asIdeal]
     Π i,LocalizedModule p.asIdeal.primeCompl (M i):=
   IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
     (mkLinearMap _ _) f |>.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
 have (i:ι):Free (Localization.AtPrime p.asIdeal)
     (LocalizedModule p.asIdeal.primeCompl (M i)):=
   free_of_flat_of_isLocalRing
 simp_rw [rankAtStalk,e.finrank_eq,Module.finrank_pi_fintype,finsum_eq_sum_of_fintype]
lemma rankAtStalk_eq_finrank_tensorProduct (p:PrimeSpectrum R):
   rankAtStalk M p=
     finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M):=by
 let e:LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
     Localization.AtPrime p.asIdeal ⊗[R] M:=
   LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
 rw [rankAtStalk,e.finrank_eq]
variable [Flat R M] [Module.Finite R M]
attribute [local instance] free_of_flat_of_isLocalRing
lemma rankAtStalk_eq_zero_iff_notMem_support (p:PrimeSpectrum R):
   rankAtStalk M p=0 ↔ p∉support R M:=by
 rw [notMem_support_iff]
 refine ⟨fun h↦?_,fun h↦Module.finrank_zero_of_subsingleton⟩
 apply subsingleton_of_rank_zero (R:=Localization.AtPrime p.asIdeal)
 dsimp [rankAtStalk] at h
 simp [←finrank_eq_rank,h]
lemma rankAtStalk_pos_iff_mem_support (p:PrimeSpectrum R):
   0 < rankAtStalk M p ↔ p∈support R M:=
 Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left
lemma rankAtStalk_eq_zero_iff_subsingleton:
   rankAtStalk (R:=R) M=0 ↔ Subsingleton M:=by
 refine ⟨fun h↦?_,fun _↦rankAtStalk_eq_zero_of_subsingleton⟩
 simp_rw [←support_eq_empty_iff (R:=R),Set.eq_empty_iff_forall_notMem]
 intro p
 rw [←rankAtStalk_eq_zero_iff_notMem_support,h,Pi.zero_apply]
variable (M) in
lemma rankAtStalk_prod (N:Type*) [AddCommGroup N] [Module R N]
   [Module.Flat R N] [Module.Finite R N]:
   rankAtStalk (R:=R) (M × N)=rankAtStalk M+rankAtStalk N:=by
 ext p
 let e:LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
     LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N:=
   IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
     (.prodMap (mkLinearMap _ M) (mkLinearMap _ N)) |>.extendScalarsOfIsLocalization
     p.asIdeal.primeCompl _
 simp [rankAtStalk,e.finrank_eq]
lemma rankAtStalk_baseChange {S:Type*} [CommRing S] [Algebra R S] (p:PrimeSpectrum S):
   rankAtStalk (S ⊗[R] M) p=rankAtStalk M (p.comap (algebraMap R S)):=by
 let q:PrimeSpectrum R:=p.comap (algebraMap R S)
 let:=Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
 let e:LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
     Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime q.asIdeal]
       LocalizedModule q.asIdeal.primeCompl M:=
   LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
     (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
     (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
     (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
       (LocalizedModule.equivTensorProduct _ M).symm)
 rw [rankAtStalk,e.finrank_eq]
 apply Module.finrank_baseChange
lemma rankAtStalk_isBaseChange {S Mₛ:Type*} [CommRing S] [Algebra R S] [AddCommGroup Mₛ]
   [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ] {f:M →ₗ[R] Mₛ} (hf:IsBaseChange S f)
   (p:PrimeSpectrum S):rankAtStalk Mₛ p=rankAtStalk M (p.comap (algebraMap R S)):=by
 simp [rankAtStalk_eq_of_equiv hf.equiv.symm,rankAtStalk_baseChange]
variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat {p q:PrimeSpectrum R} (hpq:p ≤ q):
   rankAtStalk M p=rankAtStalk M q:=by
 let S:=Localization.AtPrime q.asIdeal
 obtain ⟨P,rfl⟩:p∈Set.range (PrimeSpectrum.comap (algebraMap R S)):=by
   rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
   exact disjoint_compl_left_iff.mpr hpq
 rw [←rankAtStalk_isBaseChange (LocalizedModule.isBaseChange q.asIdeal.primeCompl M),
   rankAtStalk_eq_finrank_of_free]
 simp [rankAtStalk]
variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat' {p q:Ideal R} [hp:p.IsPrime] [hq:q.IsPrime]
   (hpq:p ≤ q):rankAtStalk M ⟨p,hp⟩=rankAtStalk M ⟨q,hq⟩:=
 rankAtStalk_eq_of_le_of_finite_of_flat M hpq
lemma rankAtStalk_tensorProduct (N:Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
   [Module.Flat R N]:rankAtStalk (M ⊗[R] N)=rankAtStalk M*rankAtStalk (R:=R) N:=by
 ext p
 let e:Localization.AtPrime p.asIdeal ⊗[R] (M ⊗[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
     (Localization.AtPrime p.asIdeal ⊗[R] M) ⊗[Localization.AtPrime p.asIdeal]
       (Localization.AtPrime p.asIdeal ⊗[R] N):=
   (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ
     (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
 rw [rankAtStalk_eq_finrank_tensorProduct,e.finrank_eq,finrank_tensorProduct,
   ←rankAtStalk_eq_finrank_tensorProduct, ←rankAtStalk_eq_finrank_tensorProduct,Pi.mul_apply]
lemma rankAtStalk_tensorProduct_of_isScalarTower {S:Type*} [CommRing S] [Algebra R S]
   (N:Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
   [Module.Finite S N] [Module.Flat S N] (p:PrimeSpectrum S):
   rankAtStalk (N ⊗[R] M) p=rankAtStalk N p*rankAtStalk M (p.comap (algebraMap R S)):=by
 simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
   rankAtStalk_tensorProduct,rankAtStalk_baseChange]
lemma rankAtStalk_eq (p:PrimeSpectrum R):
   rankAtStalk M p=finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M):=by
 let k:=p.asIdeal.ResidueField
 let e:k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
     k ⊗[R] M:=
   AlgebraTensorModule.cancelBaseChange _ _ _ _ _
 rw [←e.finrank_eq,finrank_baseChange,rankAtStalk_eq_finrank_tensorProduct]
lemma _root_.Ideal.finrank_fiber_eq_rankAtStalk (p:Ideal R) [hp:p.IsPrime]:
   finrank p.ResidueField (p.Fiber M)=rankAtStalk M ⟨p,hp⟩:=
 (rankAtStalk_eq ⟨p,hp⟩).symm
lemma _root_.Ideal.finrank_fiber_eq_finrank [IsDomain R] (p:Ideal R) [p.IsPrime]:
   finrank p.ResidueField (p.Fiber M)=finrank R M:=by
 let K:=FractionRing R
 let Rp:=Localization.AtPrime p
 let Mp:=LocalizedModule.AtPrime p M
 rw [p.finrank_fiber_eq_rankAtStalk,rankAtStalk, ←(isBaseChange Rp Mp K).finrank_eq,
   (((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq,
   (AlgebraTensorModule.cancelBaseChange R Rp K K M).finrank_eq,(isBaseChange R M K).finrank_eq]
end Module
end ProximityFlatProofPort
end PackedLegacy_IX

/-! Packed from ProximityPrize.SubmissionLower.F6. -/
section PackedLegacy_F6
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
end
end ProximityFlatProofPort
end PackedLegacy_F6

/-! Packed from ProximityPrize.SubmissionLower.S4. -/
section PackedLegacy_S4
section ProximityFlatProofPort
open Algebra Module
open scoped Pointwise
attribute [local instance] FractionRing.liftAlgebra
namespace Ideal
open scoped Classical in
noncomputable def ramificationIdxIn {A:Type*} [CommRing A] (p:Ideal A)
   (B:Type*) [CommRing B] [Algebra A B]:ℕ:=
 if h:∃ P:Ideal B,P.IsPrime∧P.LiesOver p then h.choose.ramificationIdx A
 else 0
open scoped Classical in
noncomputable def inertiaDegIn {A:Type*} [CommRing A] (p:Ideal A)
   (B:Type*) [CommRing B] [Algebra A B]:ℕ:=
 if h:∃ P:Ideal B,P.IsPrime∧P.LiesOver p then h.choose.inertiaDeg A else 0
section MulAction
variable {A B:Type*} [CommRing A] [CommRing B] [Algebra A B] {p:Ideal A}
 {G:Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
instance:MulAction G (primesOver p B) where
 smul σ Q:=primesOver.mk p (σ • Q.1)
 one_smul Q:=Subtype.ext (one_smul G Q.1)
 mul_smul σ τ Q:=Subtype.ext (mul_smul σ τ Q.1)
@[simp]
theorem coe_smul_primesOver (σ:G) (P:primesOver p B):(σ • P).1=σ • P.1:=
 rfl
@[simp]
theorem coe_smul_primesOver_mk (σ:G) (P:Ideal B) [P.IsPrime] [P.LiesOver p]:
   (σ • primesOver.mk p P).1=σ • P:=
 rfl
variable (K L:Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
 [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
 [IsIntegralClosure B A L] [FiniteDimensional K L]
noncomputable instance:MulAction Gal(L/K) (primesOver p B) where
 smul σ Q:=primesOver.mk p (map (galRestrict A K L B σ) Q.1)
 one_smul Q:=by
   apply Subtype.val_inj.mp
   change map _ Q.1=Q.1
   simpa only [map_one] using! map_id Q.1
 mul_smul σ τ Q:=by
   apply Subtype.val_inj.mp
   change map _ Q.1=map _ (map _ Q.1)
   rw [map_mul]
   exact (Q.1.map_map ((galRestrict A K L B) τ).toRingHom ((galRestrict A K L B) σ).toRingHom).symm
theorem coe_smul_primesOver_eq_map_galRestrict (σ:Gal(L/K)) (P:primesOver p B):
   (σ • P).1=map (galRestrict A K L B σ) P:=
 rfl
theorem coe_smul_primesOver_mk_eq_map_galRestrict (σ:Gal(L/K)) (P:Ideal B) [P.IsPrime]
   [P.LiesOver p]:(σ • primesOver.mk p P).1=map (galRestrict A K L B σ) P:=
 rfl
end MulAction
section RamificationInertia
variable {A B:Type*} [CommRing A] [CommRing B] [Algebra A B] (p:Ideal A) (P Q:Ideal B)
 [hPp:P.IsPrime] [hp:P.LiesOver p] [hQp:Q.IsPrime] [Q.LiesOver p]
 (G:Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
include p in
theorem exists_smul_eq_of_isGaloisGroup:∃ σ:G,σ • P=Q:=by
 rcases IsInvariant.exists_smul_of_under_eq A B G P Q <|
   (over_def P p).symm.trans (over_def Q p) with ⟨σ,hs⟩
 exact ⟨σ,hs.symm⟩
instance isPretransitive_of_isGaloisGroup:MulAction.IsPretransitive G (primesOver p B) where
 exists_smul_eq:=by
   intro ⟨P,_,_⟩ ⟨Q,_,_⟩
   rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ,hs⟩
   exact ⟨σ,Subtype.val_inj.mp hs⟩
include p G in
theorem ramificationIdx_eq_of_isGaloisGroup:
   P.ramificationIdx A=Q.ramificationIdx A:=by
 rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ,rfl⟩
 rw [ramificationIdx_smul]
include p G in
theorem inertiaDeg_eq_of_isGaloisGroup:
   P.inertiaDeg A=Q.inertiaDeg A:=by
 rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ,rfl⟩
 rw [inertiaDeg_smul]
include p G in
theorem ramificationIdxIn_eq_ramificationIdx:
   ramificationIdxIn p B=P.ramificationIdx A:=by
 have h:∃ P:Ideal B,P.IsPrime∧P.LiesOver p:=⟨P,hPp,hp⟩
 obtain ⟨_,_⟩:=h.choose_spec
 rw [ramificationIdxIn,dif_pos h]
 exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G
include G in
theorem ramificationIdxIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p:Ideal A} [p.IsPrime]:
   p.ramificationIdxIn B≠0:=by
 obtain ⟨P⟩:=(inferInstance:Nonempty (primesOver p B))
 rw [ramificationIdxIn_eq_ramificationIdx p P G]
 exact (P.1.ramificationIdx_pos A).ne'
include G in
theorem inertiaDegIn_eq_inertiaDeg:
   inertiaDegIn p B=P.inertiaDeg A:=by
 have h:∃ P:Ideal B,P.IsPrime∧P.LiesOver p:=⟨P,hPp,hp⟩
 obtain ⟨_,_⟩:=h.choose_spec
 rw [inertiaDegIn,dif_pos h]
 exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G
include G in
theorem inertiaDegIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p:Ideal A} [p.IsPrime]:
   inertiaDegIn p B≠0:=by
 obtain ⟨P⟩:=(inferInstance:Nonempty (primesOver p B))
 rw [inertiaDegIn_eq_inertiaDeg p P G]
 exact (P.1.inertiaDeg_pos A).ne'
section tower
variable (C:Type*) [CommRing C] [Algebra A C] [Algebra B C]
 [Nonempty (P.primesOver C)] [IsScalarTower A B C]
 (GAC:Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]
 (GBC:Type*) [Group GBC] [Finite GBC] [MulSemiringAction GBC C] [IsGaloisGroup GBC B C]
include G GAC GBC in
theorem inertiaDegIn_mul_inertiaDegIn:
   p.inertiaDegIn B*P.inertiaDegIn C=p.inertiaDegIn C:=by
 obtain ⟨⟨Q,_,_⟩⟩:=(inferInstance:Nonempty (primesOver P C))
 have:Q.LiesOver p:=LiesOver.trans Q P p
 rw [inertiaDegIn_eq_inertiaDeg p P G,inertiaDegIn_eq_inertiaDeg p Q GAC,
   inertiaDegIn_eq_inertiaDeg P Q GBC, ←inertiaDeg_tower P Q]
variable {p} in
include G GAC GBC in
theorem ramificationIdxIn_mul_ramificationIdxIn [Flat B C]:
   p.ramificationIdxIn B*P.ramificationIdxIn C=p.ramificationIdxIn C:=by
 obtain ⟨⟨Q,_,hQ⟩⟩:=(inferInstance:Nonempty (primesOver P C))
 have:Q.LiesOver p:=LiesOver.trans Q P p
 rw [ramificationIdxIn_eq_ramificationIdx p P G,ramificationIdxIn_eq_ramificationIdx p Q GAC,
   ramificationIdxIn_eq_ramificationIdx P Q GBC, ←ramificationIdx_tower P Q]
@[deprecated (since:="2026-06-18")] alias ramificationIdxIn_mul_ramificationIdxIn':=
 ramificationIdxIn_mul_ramificationIdxIn
end tower
end RamificationInertia
section fundamental_identity
variable {A:Type*} [CommRing A] [IsDomain A] (p:Ideal A) [p.IsPrime]
 (B:Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Flat A B]
 (G:Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn:
   (primesOver p B).ncard*(ramificationIdxIn p B*inertiaDegIn p B)=Nat.card G:=by
 have:Fintype (primesOver p B):=(QuasiFinite.finite_primesOver p).fintype
 rw [←smul_eq_mul, ←Set.fintypeCard_eq_ncard, ←Finset.card_univ, ←Finset.sum_const,
   ←sum_ramification_inertia_eq_card p B]
 apply Finset.sum_congr rfl
 intro P hp
 rw [ramificationIdxIn_eq_ramificationIdx p P G,inertiaDegIn_eq_inertiaDeg p P G]
end fundamental_identity
section tower
variable {A B:Type*} [CommRing A] [CommRing B]
 [Algebra A B] [FaithfulSMul A B] {p:Ideal A} (P:Ideal B)
 [P.IsPrime] [P.LiesOver p] (G:Type*) [Group G] [Finite G] [MulSemiringAction G B]
 [IsGaloisGroup G A B] (C:Type*) [CommRing C] [IsDomain C] [Algebra A C]
 [Algebra B C] [FaithfulSMul B C] [IsScalarTower A B C]
 (GAC:Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]
include G GAC in
open IsGaloisGroup MulAction in
theorem ncard_primesOver_mul_ncard_primesOver:
   (p.primesOver B).ncard*(P.primesOver C).ncard=(p.primesOver C).ncard:=by
 have:Algebra.IsIntegral A C:=isInvariant.isIntegral A C GAC
 have:Algebra.IsIntegral B C:=Algebra.IsIntegral.tower_top A
 let f:=restrictHom GAC G A B C
 let H:=(stabilizer G P).comap f
 have key (Q Q':Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg:g • Q=Q'):g∈H:=by
   simpa [←restrictHom_smul_under GAC G A, ←over_def _ P,H] using congr_arg (Ideal.under B) hg
 obtain ⟨Q,_,_⟩:=(inferInstance:Nonempty (P.primesOver C))
 have:Q.LiesOver p:=.trans Q P p
 have orbit_eq:orbit H Q=P.primesOver C:=by
   ext Q'
   constructor
   · rintro ⟨g,rfl:g • Q=Q'⟩
     refine ⟨inferInstance,?_⟩
     rw [liesOver_iff,H.smul_def, ←restrictHom_smul_under GAC G A B C, ←Q.over_def P]
     exact g.2.symm
   · rintro ⟨_,_⟩
     have:Q'.LiesOver p:=.trans Q' P p
     obtain ⟨g,hg⟩:=
       IsInvariant.exists_smul_of_under_eq A C GAC Q Q' ((Q.over_def p).symm.trans (Q'.over_def p))
     exact ⟨⟨g,key Q Q' g hg.symm⟩,by simpa [Subgroup.smul_def] using hg.symm⟩
 have stabilizer_eq:stabilizer H Q=(stabilizer GAC Q).subgroupOf H:=by
   simp [Subgroup.ext_iff,Subgroup.mem_subgroupOf]
 rw [←IsInvariant.orbit_eq_primesOver A B G p P, ←index_stabilizer,
   ←orbit_eq, ←index_stabilizer,stabilizer_eq, ←Subgroup.relIndex,
   ←IsInvariant.orbit_eq_primesOver A C GAC p Q, ←index_stabilizer,
   ←(stabilizer G P).index_comap_of_surjective (restrictHom_surjective GAC G A B C),
   mul_comm,Subgroup.relIndex_mul_index]
 exact key Q Q
end tower
section inertia
variable {R S G:Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
 [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
open scoped Pointwise
open Algebra
attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank (p:Ideal R) [p.IsPrime]
   (P:Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField]:
   Nat.card (MulAction.stabilizer G P)=Nat.card (inertia G P)*P.inertiaDeg R:=by
 let:=Localization.AtPrime.algebraOfLiesOver p P
 have heq:(algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))=
     (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField):=by
   ext
   simp [←IsScalarTower.algebraMap_apply]
 let:=((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
 have:IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField:=.of_algebraMap_eq' rfl
 have:IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField:=.of_algebraMap_eq' heq
 have:IsGalois p.ResidueField P.ResidueField:=
   { __:=Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField}
 have:Module.Finite p.ResidueField P.ResidueField:=
   Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
 have:Subgroup.index _=_:=Nat.card_congr
   (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
 rw [inertiaDeg_eq p P, ←IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField, ←this,
   ←((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
   Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M:=G) P)).toEquiv,
   AddSubgroup.subgroupOf_inertia]
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p:Ideal R) [p.IsPrime]
   (P:Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField]:
   (p.primesOver S).ncard*Nat.card (P.inertia G)*P.inertiaDeg R=Nat.card G:=by
 rw [mul_assoc, ←card_stabilizer_eq_card_inertia_mul_finrank p P,
   ←IsInvariant.orbit_eq_primesOver R S G p P]
 simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
lemma card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
   (p:Ideal R) (P:Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
   [PerfectField p.ResidueField]:
   Nat.card (P.inertia G)=Ideal.ramificationIdxIn p S:=by
 have H:=ncard_primesOver_mul_card_inertia_mul_finrank (G:=G) p P
 rw [←inertiaDegIn_eq_inertiaDeg p P G] at H
 have h1:(p.primesOver S).ncard≠0:=by grind [Nat.card_pos]
 have h2:p.inertiaDegIn S≠0:=by grind [Nat.card_pos]
 rwa [←ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
   mul_assoc,mul_right_inj' h1,mul_left_inj' h2] at H
lemma card_stabilizer_eq [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
   (p:Ideal R) (P:Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
   [PerfectField p.ResidueField]:
   Nat.card (MulAction.stabilizer G P)=p.ramificationIdxIn S*p.inertiaDegIn S:=by
 rw [card_stabilizer_eq_card_inertia_mul_finrank p P,card_inertia_eq_ramificationIdxIn p,
   inertiaDegIn_eq_inertiaDeg p P G]
end inertia
section galRestrict
variable (R K L S:Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
   [Algebra R K] [IsFractionRing R K] [Algebra S L]
   [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
   [IsIntegralClosure S R L] [FiniteDimensional K L]
lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p:Ideal R}
   {P₁ P₂:Ideal S} (hP₁:P₁∈primesOver p S) (hP₂:P₂∈primesOver p S):
   ∃ σ,P₁.comap (galRestrict R K L S σ)=P₂:=by
 have:IsDomain S:=
   (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
 have:=IsIntegralClosure.isDedekindDomain R K L S
 have:Module.Finite R S:=IsIntegralClosure.finite R K L S
 have:=hP₁.1
 have:=hP₁.2
 have:=hP₂.1
 have:=hP₂.2
 have:IsFractionRing S L:=IsIntegralClosure.isFractionRing_of_finite_extension R K L S
 let:MulSemiringAction Gal(L/K) S:=IsIntegralClosure.MulSemiringAction R K L S
 have:IsGaloisGroup Gal(L/K) R S:=IsGaloisGroup.of_isFractionRing _ _ _ K L
 obtain ⟨σ,rfl⟩:=exists_smul_eq_of_isGaloisGroup p P₂ P₁ Gal(L/K)
 exact ⟨σ,comap_map_of_bijective _ ((galRestrict R K L S σ).bijective)⟩
end galRestrict
end Ideal
end ProximityFlatProofPort
end PackedLegacy_S4

/-! Packed from ProximityPrize.SubmissionLower.V0. -/
section PackedLegacy_V0
section ProximityFlatProofPort
variable {α:Type*}
local infixl:50 " ~ᵤ " => Associated
section Finsupp
variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
 [NormalizationMonoid α] [DecidableEq α]
open UniqueFactorizationMonoid
noncomputable def factorization (n:α):α →₀ ℕ:=
 Multiset.toFinsupp (normalizedFactors n)
theorem factorization_eq_count {n p:α}:
   factorization n p=Multiset.count p (normalizedFactors n):=by simp [factorization]
@[simp]
theorem factorization_zero:factorization (0:α)=0:=by simp [factorization]
@[simp]
theorem factorization_one:factorization (1:α)=0:=by simp [factorization]
@[simp]
theorem support_factorization {n:α}:
   (factorization n).support=(normalizedFactors n).toFinset:=by
 simp [factorization,Multiset.toFinsupp_support]
@[simp]
theorem factorization_mul {a b:α} (ha:a≠0) (hb:b≠0):
   factorization (a*b)=factorization a+factorization b:=by
 simp [factorization,normalizedFactors_mul ha hb]
theorem factorization_pow {x:α} {n:ℕ}:factorization (x^n)=n • factorization x:=by
 ext
 simp [factorization]
theorem associated_of_factorization_eq (a b:α) (ha:a≠0) (hb:b≠0)
   (h:factorization a=factorization b):Associated a b:=by
 simp_rw [factorization,AddEquiv.apply_eq_iff_eq] at h
 rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]
end Finsupp
end ProximityFlatProofPort
end PackedLegacy_V0

/-! Packed from ProximityPrize.SubmissionLower.S8. -/
section PackedLegacy_S8
section ProximityFlatProofPort
noncomputable section
open scoped nonZeroDivisors
open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R:Type*} [CommRing R] {K:Type*} [Field K] [Algebra R K] [IsFractionRing R K]
 [IsDedekindDomain R] (v:HeightOneSpectrum R)
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I:Ideal R):Ideal R:=
 v.asIdeal^(Associates.mk v.asIdeal).count (Associates.mk I).factors
open Associates in
theorem IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
   {I:Ideal R} (hI:I≠0):
   maxPowDividing v I=
     v.asIdeal^Multiset.count v.asIdeal (normalizedFactors I):=by
 classical
 rw [maxPowDividing,factors_mk _ hI,count_some (irreducible_mk.mpr v.irreducible),
   ←Multiset.count_map_eq_count' _ _ Subtype.val_injective,map_subtype_coe_factors',
   factors_eq_normalizedFactors, ←Multiset.count_map_eq_count' _ _ (mk_injective (M:=Ideal R))]
theorem Ideal.finite_factors {I:Ideal R} (hI:I≠0):
   {v:HeightOneSpectrum R | v.asIdeal∣I}.Finite:=by
 rw [←Set.finite_coe_iff,Set.coe_setOf]
 haveI h_fin:=fintypeSubtypeDvd I hI
 refine
   Finite.of_injective (fun v => (⟨(v:HeightOneSpectrum R).asIdeal,v.2⟩:{ x//x∣I})) ?_
 intro v w hvw
 exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))
theorem Associates.finite_factors {I:Ideal R} (hI:I≠0):
   ∀ᶠ v:HeightOneSpectrum R in Filter.cofinite,
     ((Associates.mk v.asIdeal).count (Associates.mk I).factors:ℤ)=0:=by
 have h_supp:{v:HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
     (Associates.mk I).factors:ℤ)=0}={v:HeightOneSpectrum R | v.asIdeal∣I}:=by
   ext v
   simp_rw [Int.natCast_eq_zero]
   exact Associates.count_ne_zero_iff_dvd hI v.irreducible
 rw [Filter.eventually_cofinite,h_supp]
 exact Ideal.finite_factors hI
namespace Ideal
@[fun_prop]
theorem hasFiniteMulSupport {I:Ideal R} (hI:I≠0):
   HasFiniteMulSupport fun v:HeightOneSpectrum R↦v.maxPowDividing I:=
 haveI h_subset:{v:HeightOneSpectrum R | v.maxPowDividing I≠1} ⊆
     {v:HeightOneSpectrum R |
       ((Associates.mk v.asIdeal).count (Associates.mk I).factors:ℤ)≠0}:=by
   intro v hv h_zero
   have hv':v.maxPowDividing I=1:=by
     rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing,Int.natCast_eq_zero.mp h_zero,
       pow_zero _]
   exact hv hv'
 Finite.subset (Filter.eventually_cofinite.mp (Associates.finite_factors hI)) h_subset
@[deprecated (since:="2026-03-03")] alias finite_mulSupport:=hasFiniteMulSupport
@[fun_prop]
theorem hasFiniteMulSupport_coe {I:Ideal R} (hI:I≠0):
   HasFiniteMulSupport fun v:HeightOneSpectrum R↦(v.asIdeal:FractionalIdeal R⁰ K)^
     ((Associates.mk v.asIdeal).count (Associates.mk I).factors:ℤ):=by
 rw [HasFiniteMulSupport,mulSupport]
 simp_rw [Ne,zpow_natCast, ←FractionalIdeal.coeIdeal_pow,FractionalIdeal.coeIdeal_eq_one]
 exact hasFiniteMulSupport hI
@[deprecated (since:="2026-03-03")] alias finite_mulSupport_coe:=hasFiniteMulSupport_coe
@[fun_prop]
theorem hasFiniteMulSupport_inv {I:Ideal R} (hI:I≠0):
   HasFiniteMulSupport fun v:HeightOneSpectrum R↦(v.asIdeal:FractionalIdeal R⁰ K)^
     (-((Associates.mk v.asIdeal).count (Associates.mk I).factors:ℤ)):=by
 rw [HasFiniteMulSupport,mulSupport]
 simp_rw [zpow_neg,Ne,inv_eq_one]
 exact hasFiniteMulSupport_coe hI
@[deprecated (since:="2026-03-03")] alias finite_mulSupport_inv:=hasFiniteMulSupport_inv
theorem finprod_not_dvd (I:Ideal R) (hI:I≠0):
   ¬v.asIdeal^((Associates.mk v.asIdeal).count (Associates.mk I).factors+1)∣
       ∏ᶠ v:HeightOneSpectrum R,v.maxPowDividing I:=by
 classical
 have hf:=hasFiniteMulSupport hI
 have h_ne_zero:v.maxPowDividing I≠0:=pow_ne_zero _ v.ne_bot
 rw [←mul_finprod_cond_ne v hf,pow_add,pow_one,finprod_cond_ne _ _ hf]
 intro h_contr
 have hv_prime:Prime v.asIdeal:=Ideal.prime_of_isPrime v.ne_bot v.isPrime
 obtain ⟨w,hw,hvw'⟩:=
   Prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr)
 have hw_prime:Prime w.asIdeal:=Ideal.prime_of_isPrime w.ne_bot w.isPrime
 have hvw:=Prime.dvd_of_dvd_pow hv_prime hvw'
 rw [Prime.dvd_prime_iff_associated hv_prime hw_prime,associated_iff_eq] at hvw
 exact (Finset.mem_erase.mp hw).1 (HeightOneSpectrum.ext hvw.symm)
end Ideal
theorem Associates.finprod_ne_zero (I:Ideal R):
   Associates.mk (∏ᶠ v:HeightOneSpectrum R,v.maxPowDividing I)≠0:=by
 classical
 rw [Associates.mk_ne_zero,finprod_def]
 split_ifs
 · rw [Finset.prod_ne_zero_iff]
   intro v _
   apply pow_ne_zero _ v.ne_bot
 · exact one_ne_zero
namespace Ideal
theorem finprod_count (I:Ideal R) (hI:I≠0):(Associates.mk v.asIdeal).count
   (Associates.mk (∏ᶠ v:HeightOneSpectrum R,v.maxPowDividing I)).factors=
   (Associates.mk v.asIdeal).count (Associates.mk I).factors:=by
 have h_ne_zero:=Associates.finprod_ne_zero I
 have hv:Irreducible (Associates.mk v.asIdeal):=v.associates_irreducible
 have h_dvd:=finprod_mem_dvd v (hasFiniteMulSupport hI)
 have h_not_dvd:=Ideal.finprod_not_dvd v I hI
 simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h_dvd h_ne_zero h_not_dvd
 rw [←Associates.mk_dvd_mk] at h_dvd h_not_dvd
 simp only [Associates.dvd_eq_le] at h_dvd h_not_dvd
 rw [Associates.mk_pow,Associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd
 rw [not_le] at h_not_dvd
 apply Nat.eq_of_le_of_lt_succ h_dvd h_not_dvd
theorem finprod_heightOneSpectrum_factorization {I:Ideal R} (hI:I≠0):
   ∏ᶠ v:HeightOneSpectrum R,v.maxPowDividing I=I:=by
 rw [←associated_iff_eq, ←Associates.mk_eq_mk_iff_associated]
 classical
 apply Associates.eq_of_eq_counts
 · apply Associates.finprod_ne_zero I
 · apply Associates.mk_ne_zero.mpr hI
 intro v hv
 obtain ⟨J,hJv⟩:=Associates.exists_rep v
 rw [←hJv,Associates.irreducible_mk] at hv
 rw [←hJv]
 apply Ideal.finprod_count
   ⟨J,Ideal.isPrime_of_prime (irreducible_iff_prime.mp hv),Irreducible.ne_zero hv⟩ I hI
theorem iInf_maxPowDividing_eq {I:Ideal R} (h0:I≠0):
   ⨅ i:HeightOneSpectrum R,i.maxPowDividing I=I:=by
 nth_rw 2 [←Ideal.finprod_heightOneSpectrum_factorization h0]
 classical
 rw [finprod_def,dif_pos (Ideal.hasFiniteMulSupport h0),Ideal.prod_eq_iInf_of_pairwise_isCoprime]
 · ext x
   constructor
   · aesop
   · simp only [Finite.mem_toFinset,mem_mulSupport,one_eq_top,ne_eq,Submodule.mem_iInf]
     intro h i
     by_cases i.maxPowDividing I=⊤ <;> simp_all
 · intro x hx y hy hxy
   apply IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne _ _ hxy
variable (K)
theorem finprod_heightOneSpectrum_factorization_coe {I:Ideal R} (hI:I≠0):
   (∏ᶠ v:HeightOneSpectrum R,(v.asIdeal:FractionalIdeal R⁰ K)^
     ((Associates.mk v.asIdeal).count (Associates.mk I).factors:ℤ))=I:=by
 conv_rhs => rw [←Ideal.finprod_heightOneSpectrum_factorization hI]
 rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
 simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing,FractionalIdeal.coeIdeal_pow,
   zpow_natCast]
end Ideal
namespace FractionalIdeal
open Int IsLocalization
open Ideal in
theorem finprod_heightOneSpectrum_factorization {I:FractionalIdeal R⁰ K} (hI:I≠0) {a:R}
   {J:Ideal R} (haJ:I=spanSingleton R⁰ ((algebraMap R K) a)⁻¹*↑J):
   ∏ᶠ v:HeightOneSpectrum R,(v.asIdeal:FractionalIdeal R⁰ K)^
     ((Associates.mk v.asIdeal).count (Associates.mk J).factors-
       (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors:ℤ)=I:=by
 have hJ_ne_zero:J≠0:=ideal_factor_ne_zero hI haJ
 have hJ:=Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
 have ha_ne_zero:Ideal.span {a}≠0:=constant_factor_ne_zero hI haJ
 have ha:=Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
 rw [haJ, ←div_spanSingleton,div_eq_mul_inv, ←coeIdeal_span_singleton, ←hJ, ←ha,
   ←finprod_inv_distrib]
 simp_rw [←zpow_neg]
 rw [←finprod_mul_distrib (by fun_prop) (by fun_prop)]
 apply finprod_congr
 intro v
 rw [←zpow_add₀ ((@coeIdeal_ne_zero R _ K _ _ _ _).mpr v.ne_bot),sub_eq_add_neg]
theorem finprod_heightOneSpectrum_factorization_principal_fraction {n:R} (hn:n≠0) (d:↥R⁰):
   ∏ᶠ v:HeightOneSpectrum R,(v.asIdeal:FractionalIdeal R⁰ K)^
     ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n}:Ideal R)).factors-
       (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑d:R)}):
       Ideal R)).factors:ℤ)=spanSingleton R⁰ (mk' K n d):=by
 have hd_ne_zero:(algebraMap R K) (d:R)≠0:=
   map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
 have h0:spanSingleton R⁰ (mk' K n d)≠0:=by
   rw [spanSingleton_ne_zero_iff,IsFractionRing.mk'_eq_div,ne_eq,div_eq_zero_iff,not_or]
   exact ⟨(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hn,hd_ne_zero⟩
 have hI:spanSingleton R⁰ (mk' K n d)=
     spanSingleton R⁰ ((algebraMap R K) d)⁻¹*↑(Ideal.span {n}:Ideal R):=by
   rw [coeIdeal_span_singleton,spanSingleton_mul_spanSingleton]
   apply congr_arg
   rw [IsFractionRing.mk'_eq_div,div_eq_mul_inv,mul_comm]
 exact finprod_heightOneSpectrum_factorization h0 hI
open Classical in
theorem finprod_heightOneSpectrum_factorization_principal {I:FractionalIdeal R⁰ K} (hI:I≠0)
   (k:K) (hk:I=spanSingleton R⁰ k):
   ∏ᶠ v:HeightOneSpectrum R,(v.asIdeal:FractionalIdeal R⁰ K)^
     ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {choose
         (exists_mk'_eq R⁰ k)}:Ideal R)).factors-
       (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(choose
         (choose_spec (exists_mk'_eq R⁰ k)):↥R⁰):R)}):Ideal R)).factors:ℤ)=I:=by
 set n:R:=choose (exists_mk'_eq R⁰ k)
 set d:↥R⁰:=choose (choose_spec (exists_mk'_eq R⁰ k))
 have hnd:mk' K n d=k:=choose_spec (choose_spec (exists_mk'_eq R⁰ k))
 have hn0:n≠0:=by
   by_contra h
   rw [←hnd,h,IsFractionRing.mk'_eq_div,map_zero,zero_div,spanSingleton_zero] at hk
   exact hI hk
 rw [finprod_heightOneSpectrum_factorization_principal_fraction hn0 d,hk,hnd]
variable (K)
open Classical in
def count (I:FractionalIdeal R⁰ K):ℤ:=
 dite (I=0) (fun _:I=0 => 0) fun _:¬I=0 =>
   let a:=choose (exists_eq_spanSingleton_mul I)
   let J:=choose (choose_spec (exists_eq_spanSingleton_mul I))
   ((Associates.mk v.asIdeal).count (Associates.mk J).factors-
       (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors:ℤ)
lemma count_zero:count K v (0:FractionalIdeal R⁰ K)=0:=by simp only [count,dif_pos]
open Classical in
lemma count_ne_zero {I:FractionalIdeal R⁰ K} (hI:I≠0):
   count K v I=((Associates.mk v.asIdeal).count (Associates.mk
     (choose (choose_spec (exists_eq_spanSingleton_mul I)))).factors-
     (Associates.mk v.asIdeal).count
       (Associates.mk (Ideal.span {choose (exists_eq_spanSingleton_mul I)})).factors:ℤ):=by
 simp only [count,dif_neg hI]
open Classical in
theorem count_well_defined {I:FractionalIdeal R⁰ K} (hI:I≠0) {a:R}
   {J:Ideal R} (h_aJ:I=spanSingleton R⁰ ((algebraMap R K) a)⁻¹*↑J):
   count K v I=((Associates.mk v.asIdeal).count (Associates.mk J).factors-
     (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors:ℤ):=by
 set a₁:=choose (exists_eq_spanSingleton_mul I)
 set J₁:=choose (choose_spec (exists_eq_spanSingleton_mul I))
 have h_a₁J₁:I=spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹*↑J₁:=
   (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
 have h_a₁_ne_zero:a₁≠0:=(choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).1
 have h_J₁_ne_zero:J₁≠0:=ideal_factor_ne_zero hI h_a₁J₁
 have h_a_ne_zero:Ideal.span {a}≠0:=constant_factor_ne_zero hI h_aJ
 have h_J_ne_zero:J≠0:=ideal_factor_ne_zero hI h_aJ
 have h_a₁':spanSingleton R⁰ ((algebraMap R K) a₁)≠0:=by
   rw [ne_eq,spanSingleton_eq_zero_iff, ←(algebraMap R K).map_zero,
     Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
   exact h_a₁_ne_zero
 have h_a':spanSingleton R⁰ ((algebraMap R K) a)≠0:=by
   rw [ne_eq,spanSingleton_eq_zero_iff, ←(algebraMap R K).map_zero,
     Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
   rw [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] at h_a_ne_zero
   exact h_a_ne_zero
 have hv:Irreducible (Associates.mk v.asIdeal):=by
   exact Associates.irreducible_mk.mpr v.irreducible
 rw [h_a₁J₁, ←div_spanSingleton, ←div_spanSingleton,div_eq_div_iff h_a₁' h_a',
   ←coeIdeal_span_singleton, ←coeIdeal_span_singleton, ←coeIdeal_mul, ←coeIdeal_mul] at h_aJ
 rw [count,dif_neg hI,sub_eq_sub_iff_add_eq_add, ←natCast_add, ←natCast_add,natCast_inj,
   ←Associates.count_mul _ _ hv, ←Associates.count_mul _ _ hv,Associates.mk_mul_mk,
   Associates.mk_mul_mk,coeIdeal_injective h_aJ]
 · rw [ne_eq,Associates.mk_eq_zero];exact h_J_ne_zero
 · rw [ne_eq,Associates.mk_eq_zero,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
   exact h_a₁_ne_zero
 · rw [ne_eq,Associates.mk_eq_zero];exact h_J₁_ne_zero
 · rw [ne_eq,Associates.mk_eq_zero];exact h_a_ne_zero
theorem count_mul {I I':FractionalIdeal R⁰ K} (hI:I≠0) (hI':I'≠0):
   count K v (I*I')=count K v I+count K v I':=by
 classical
 have hv:Irreducible (Associates.mk v.asIdeal):=by apply v.associates_irreducible
 obtain ⟨a,J,ha,haJ⟩:=exists_eq_spanSingleton_mul I
 have ha_ne_zero:Associates.mk (Ideal.span {a}:Ideal R)≠0:=by
   rw [ne_eq,Associates.mk_eq_zero,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];exact ha
 have hJ_ne_zero:Associates.mk J≠0:=Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI haJ)
 obtain ⟨a',J',ha',haJ'⟩:=exists_eq_spanSingleton_mul I'
 have ha'_ne_zero:Associates.mk (Ideal.span {a'}:Ideal R)≠0:=by
   rw [ne_eq,Associates.mk_eq_zero,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];exact ha'
 have hJ'_ne_zero:Associates.mk J'≠0:=
   Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI' haJ')
 have h_prod:I*I'=spanSingleton R⁰ ((algebraMap R K) (a*a'))⁻¹*↑(J*J'):=by
   rw [haJ,haJ',mul_assoc,mul_comm (J:FractionalIdeal R⁰ K),mul_assoc, ←mul_assoc,
     spanSingleton_mul_spanSingleton,coeIdeal_mul,map_mul,mul_inv,
     mul_comm (J:FractionalIdeal R⁰ K)]
 rw [count_well_defined K v hI haJ,count_well_defined K v hI' haJ',
   count_well_defined K v (mul_ne_zero hI hI') h_prod, ←Associates.mk_mul_mk,
   Associates.count_mul hJ_ne_zero hJ'_ne_zero hv, ←Ideal.span_singleton_mul_span_singleton,
   ←Associates.mk_mul_mk,Associates.count_mul ha_ne_zero ha'_ne_zero hv]
 push_cast
 ring
theorem count_mul' (I I':FractionalIdeal R⁰ K) [Decidable (I≠0∧I'≠0)]:
   count K v (I*I')=if I≠0∧I'≠0 then count K v I+count K v I' else 0:=by
 split_ifs with h
 · exact count_mul K v h.1 h.2
 · rw [←mul_ne_zero_iff,not_ne_iff] at h
   rw [h,count_zero]
theorem count_one:count K v (1:FractionalIdeal R⁰ K)=0:=by
 have h1:(1:FractionalIdeal R⁰ K)=
     spanSingleton R⁰ ((algebraMap R K) 1)⁻¹*↑(1:Ideal R):=by
   rw [(algebraMap R K).map_one,Ideal.one_eq_top,coeIdeal_top,mul_one,inv_one,
     spanSingleton_one]
 rw [count_well_defined K v one_ne_zero h1,Ideal.span_singleton_one,Ideal.one_eq_top,sub_self]
theorem count_prod {ι} (s:Finset ι) (I:ι → FractionalIdeal R⁰ K) (hS:∀ i∈s,I i≠0):
   count K v (∏ i∈s,I i)=∑ i∈s,count K v (I i):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 induction s using Finset.induction with
 | empty => rw [Finset.prod_empty,Finset.sum_empty,count_one]
 | insert i s hi hrec =>
   have hS':∀ i∈s,I i≠0:=fun j hj => hS j (Finset.mem_insert_of_mem hj)
   have hS0:∏ i∈s,I i≠0:=Finset.prod_ne_zero_iff.mpr hS'
   have hi0:I i≠0:=hS i (Finset.mem_insert_self i s)
   rw [Finset.prod_insert hi,Finset.sum_insert hi,count_mul K v hi0 hS0,hrec hS']
theorem count_pow (n:ℕ) (I:FractionalIdeal R⁰ K):
   count K v (I^n)=n*count K v I:=by
 induction n with
 | zero => rw [pow_zero,ofNat_zero,zero_mul,count_one]
 | succ n h =>
   classical rw [pow_succ,count_mul']
   by_cases hI:I=0
   · have h_neg:¬(I^n≠0∧I≠0):=by order
     rw [if_neg h_neg,hI,count_zero,mul_zero]
   · rw [if_pos (And.intro (pow_ne_zero n hI) hI),h,Nat.cast_add,
       Nat.cast_one]
     ring
theorem count_self:count K v (v.asIdeal:FractionalIdeal R⁰ K)=1:=by
 have hv:(v.asIdeal:FractionalIdeal R⁰ K)≠0:=coeIdeal_ne_zero.mpr v.ne_bot
 have h_self:(v.asIdeal:FractionalIdeal R⁰ K)=
     spanSingleton R⁰ ((algebraMap R K) 1)⁻¹*↑v.asIdeal:=by
   rw [(algebraMap R K).map_one,inv_one,spanSingleton_one,one_mul]
 have hv_irred:Irreducible (Associates.mk v.asIdeal):=by apply v.associates_irreducible
 classical rw [count_well_defined K v hv h_self,Associates.count_self hv_irred,
   Ideal.span_singleton_one, ←Ideal.one_eq_top,Associates.mk_one,Associates.factors_one,
   Associates.count_zero hv_irred,ofNat_zero,sub_zero,ofNat_one]
theorem count_pow_self (n:ℕ):
   count K v ((v.asIdeal:FractionalIdeal R⁰ K)^n)=n:=by
 rw [count_pow,count_self,mul_one]
theorem count_neg_zpow (n:ℤ) (I:FractionalIdeal R⁰ K):
   count K v (I^(-n))= -count K v (I^n):=by
 by_cases hI:I=0
 · by_cases hn:n=0
   · rw [hn,neg_zero,zpow_zero,count_one,neg_zero]
   · rw [hI,zero_zpow n hn,zero_zpow (-n) (neg_ne_zero.mpr hn),count_zero,neg_zero]
 · rw [eq_neg_iff_add_eq_zero, ←count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
     ←zpow_add₀ hI,neg_add_cancel,zpow_zero]
   exact count_one K v
theorem count_inv (I:FractionalIdeal R⁰ K):
   count K v (I⁻¹)= -count K v I:=by
 rw [←zpow_neg_one,count_neg_zpow K v (1:ℤ) I,zpow_one]
theorem count_zpow (n:ℤ) (I:FractionalIdeal R⁰ K):
   count K v (I^n)=n*count K v I:=by
 obtain n | n:=n
 · rw [ofNat_eq_natCast,zpow_natCast]
   exact count_pow K v n I
 · rw [negSucc_eq,count_neg_zpow, ←Int.natCast_succ,zpow_natCast,count_pow]
   ring
theorem count_zpow_self (n:ℤ):
   count K v ((v.asIdeal:FractionalIdeal R⁰ K)^n)=n:=by
 rw [count_zpow,count_self,mul_one]
theorem count_maximal_coprime {w:HeightOneSpectrum R} (hw:w≠v):
   count K v (w.asIdeal:FractionalIdeal R⁰ K)=0:=by
 have hw_fact:(w.asIdeal:FractionalIdeal R⁰ K)=
     spanSingleton R⁰ ((algebraMap R K) 1)⁻¹*↑w.asIdeal:=by
   rw [(algebraMap R K).map_one,inv_one,spanSingleton_one,one_mul]
 have hw_ne_zero:(w.asIdeal:FractionalIdeal R⁰ K)≠0:=
   coeIdeal_ne_zero.mpr w.ne_bot
 have hv:Irreducible (Associates.mk v.asIdeal):=by apply v.associates_irreducible
 have hw':Irreducible (Associates.mk w.asIdeal):=by apply w.associates_irreducible
 classical
 rw [count_well_defined K v hw_ne_zero hw_fact,Ideal.span_singleton_one, ←Ideal.one_eq_top,
   Associates.mk_one,Associates.factors_one,Associates.count_zero hv,ofNat_zero,sub_zero,
   natCast_eq_zero, ←pow_one (Associates.mk w.asIdeal),Associates.factors_prime_pow hw',
   Associates.count_some hv,Multiset.replicate_one,Multiset.count_eq_zero,
   Multiset.mem_singleton]
 simp only [Subtype.mk.injEq]
 rw [Associates.mk_eq_mk_iff_associated,associated_iff_eq, ←HeightOneSpectrum.ext_iff]
 exact Ne.symm hw
theorem count_maximal (w:HeightOneSpectrum R) [Decidable (w=v)]:
   count K v (w.asIdeal:FractionalIdeal R⁰ K)=if w=v then 1 else 0:=by
 split_ifs with h
 · rw [h,count_self]
 · exact count_maximal_coprime K v h
theorem count_finprod_coprime (exps:HeightOneSpectrum R → ℤ):
   count K v (∏ᶠ (w:HeightOneSpectrum R) (_:w≠v),
     (w.asIdeal:(FractionalIdeal R⁰ K))^exps w)=0:=by
 apply finprod_mem_induction fun I => count K v I=0
 · exact count_one K v
 · intro I I' hI hI'
   classical
   by_cases h:I≠0∧I'≠0
   · rw [count_mul' K v,if_pos h,hI,hI',add_zero]
   · rw [count_mul' K v,if_neg h]
 · intro w hw
   rw [count_zpow,count_maximal_coprime K v hw,mul_zero]
theorem count_finsuppProd (exps:HeightOneSpectrum R →₀ ℤ):
   count K v (exps.prod (HeightOneSpectrum.asIdeal ·^·))=exps v:=by
 rw [Finsupp.prod,count_prod]
 · classical simp only [count_zpow,count_maximal,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
     exps.mem_support_iff,ne_eq,ite_not,ite_eq_right_iff,@eq_comm ℤ 0,imp_self]
 · exact fun v hv↦zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
theorem count_finprod (exps:HeightOneSpectrum R → ℤ)
   (h_exps:∀ᶠ v:HeightOneSpectrum R in Filter.cofinite,exps v=0):
   count K v (∏ᶠ v:HeightOneSpectrum R,
     (v.asIdeal:FractionalIdeal R⁰ K)^exps v)=exps v:=by
 convert! count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _↦h_exps.mem_toFinset))
 rw [finprod_eq_finsetProd_of_mulSupport_subset (s:=h_exps.toFinset),Finsupp.prod]
 · rfl
 · rw [Finite.coe_toFinset]
   intro v hv h
   rw [mem_mulSupport,h,zpow_zero] at hv
   exact hv (Eq.refl 1)
theorem count_coe {J:Ideal R} (hJ:J≠0):
   count K v J=(Associates.mk v.asIdeal).count (Associates.mk J).factors:=by
 rw [count_well_defined K (J:=J) (a:=1),Ideal.span_singleton_one,sub_eq_self,
   Nat.cast_eq_zero, ←Ideal.one_eq_top,Associates.mk_one,Associates.factors_one,
   Associates.count_zero v.associates_irreducible]
 · simpa only [ne_eq,coeIdeal_eq_zero]
 · simp only [map_one,inv_one,spanSingleton_one,one_mul]
theorem count_coe_nonneg (J:Ideal R):0 ≤ count K v J:=by
 by_cases hJ:J=0
 · simp only [hJ,Submodule.zero_eq_bot,coeIdeal_bot,count_zero,le_refl]
 · classical simp only [count_coe K v hJ,Nat.cast_nonneg]
theorem count_mono {I J} (hI:I≠0) (h:I ≤ J):count K v J ≤ count K v I:=by
 by_cases hJ:J=0
 · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
 have:=mul_le_mul_right h J⁻¹
 rw [inv_mul_cancel₀ hJ,FractionalIdeal.le_one_iff_exists_coeIdeal] at this
 obtain ⟨J',hJ'⟩:=this
 rw [←mul_inv_cancel_left₀ hJ I, ←hJ',count_mul K v hJ,le_add_iff_nonneg_right]
 · exact count_coe_nonneg K v J'
 · exact hJ' ▸ mul_ne_zero (inv_ne_zero hJ) hI
theorem finprod_heightOneSpectrum_factorization' {I:FractionalIdeal R⁰ K} (hI:I≠0):
   ∏ᶠ v:HeightOneSpectrum R,(v.asIdeal:FractionalIdeal R⁰ K)^(count K v I)=I:=by
 have h:=(Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
 conv_rhs => rw [←finprod_heightOneSpectrum_factorization hI h]
 apply finprod_congr
 intro w
 apply congr_arg
 rw [count_ne_zero K w hI]
variable {K}
theorem finite_factors' {I:FractionalIdeal R⁰ K} (hI:I≠0) {a:R}
   {J:Ideal R} (haJ:I=spanSingleton R⁰ ((algebraMap R K) a)⁻¹*↑J):
   ∀ᶠ v:HeightOneSpectrum R in Filter.cofinite,
     ((Associates.mk v.asIdeal).count (Associates.mk J).factors:ℤ)-
       (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors=0:=by
 have ha_ne_zero:Ideal.span {a}≠0:=constant_factor_ne_zero hI haJ
 have hJ_ne_zero:J≠0:=ideal_factor_ne_zero hI haJ
 have h_subset:
   {v:HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors:ℤ)-
     ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors)=0} ⊆
   {v:HeightOneSpectrum R | v.asIdeal∣J} ∪
     {v:HeightOneSpectrum R | v.asIdeal∣Ideal.span {a}}:=by
   intro v hv
   have hv_irred:Irreducible v.asIdeal:=v.irreducible
   by_contra h_notMem
   rw [mem_union,mem_setOf_eq,mem_setOf_eq] at h_notMem
   push Not at h_notMem
   rw [←Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred,not_not,
     ←Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred,not_not] at h_notMem
   rw [mem_setOf_eq,h_notMem.1,h_notMem.2,sub_self] at hv
   exact hv (Eq.refl 0)
 exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
   (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset
open Classical in
theorem finite_factors (I:FractionalIdeal R⁰ K):
   ∀ᶠ v:HeightOneSpectrum R in Filter.cofinite,count K v I=0:=by
 by_cases hI:I=0
 · simp only [hI,count_zero,Filter.eventually_cofinite,not_true_eq_false,setOf_false,
     finite_empty]
 · convert! finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
   rw [count_ne_zero K _ hI]
end FractionalIdeal
section div
lemma IsDedekindDomain.exists_sup_span_eq {I J:Ideal R} (hIJ:I ≤ J) (hI:I≠0):
   ∃ a,I ⊔ Ideal.span {a}=J:=by
 classical
 obtain ⟨I,rfl⟩:=Ideal.dvd_iff_le.mpr hIJ
 simp only [ne_eq,mul_eq_zero,not_or] at hI
 obtain ⟨hJ,hI⟩:=hI
 suffices ∃ a,∃ K,J*K=Ideal.span {a}∧I+K=⊤ by
   obtain ⟨a,K,e,e'⟩:=this
   exact ⟨a,by rw [←e, ←Ideal.add_eq_sup, ←mul_add,e',Ideal.mul_top]⟩
 let s:=(I.finite_factors hI).toFinset
 have:∀ p∈s,J*∏ q∈s,q.asIdeal < J*∏ q∈s \ {p},q.asIdeal:=by
   intro p hps
   conv_rhs => rw [←mul_one (J*_)]
   rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hps, ←mul_assoc,
     mul_right_comm _ p.asIdeal]
   refine mul_lt_mul_of_pos_left ?_ ?_
   · rw [Ideal.one_eq_top,lt_top_iff_ne_top]
     exact p.2.ne_top
   · rw [Ideal.zero_eq_bot,bot_lt_iff_ne_bot, ←Ideal.zero_eq_bot,
       mul_ne_zero_iff,Finset.prod_ne_zero_iff]
     exact ⟨hJ,fun x _↦x.3⟩
 choose! a ha ha' using fun p hps↦SetLike.exists_of_lt (this p hps)
 obtain ⟨K,hK⟩:J∣Ideal.span {∑ p∈s,a p}:=by
   rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_iff_mem]
   exact sum_mem fun p hp↦Ideal.mul_le_right (ha p hp)
 refine ⟨_,_,hK.symm,?_⟩
 by_contra H
 obtain ⟨p,hp,h⟩:=Ideal.exists_le_maximal _ H
 let p':HeightOneSpectrum R:=⟨p,hp.isPrime,fun e↦hI (by simp_all)⟩
 have hp's:p'∈s:=by simpa [p',s,Ideal.dvd_iff_le] using le_sup_left.trans h
 have H₁:J*K ≤ J*p:=Ideal.mul_mono_right (le_sup_right.trans h)
 replace H₁:=hK.trans_le H₁ (Ideal.mem_span_singleton_self _)
 have H₂:∑ q∈s \ {p'},a q∈J*p:=by
   refine sum_mem fun q hq↦?_
   rw [Finset.mem_sdiff,Finset.mem_singleton] at hq
   refine Ideal.mul_mono_right ?_ (ha q hq.1)
   exact Ideal.prod_le_inf.trans (Finset.inf_le (b:=p') (by simpa [hp's] using Ne.symm hq.2))
 apply ha' _ hp's
 have:=IsDedekindDomain.inf_pow_eq_prod_of_prime s (fun i↦i.asIdeal) (fun _↦1)
   (fun i _↦i.prime) (fun i _ j _ e↦mt HeightOneSpectrum.ext e)
 simp only [pow_one] at this
 have inst:Nonempty {x//x∈s}:=⟨_,hp's⟩
 rw [←this,Finset.inf_eq_iInf,iInf_subtype',Ideal.mul_iInf,Ideal.mem_iInf]
 rintro ⟨q,hq⟩
 by_cases hqp:q=p'
 · subst hqp
   convert! sub_mem H₁ H₂
   rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hp's,add_sub_cancel_right]
 · refine Ideal.mul_mono_right ?_ (ha p' hp's)
   exact Ideal.prod_le_inf.trans (Finset.inf_le (b:=q) (by simpa [hq] using hqp))
lemma IsDedekindDomain.exists_eq_span_pair {I:Ideal R} {x:R} (hxI:x∈I) (hx:x≠0):
   ∃ y,I=.span {x,y}:=by
 obtain ⟨y,rfl⟩:=exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
 simp_rw [←Ideal.span_union,Set.union_singleton,Set.pair_comm x]
 use y
lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
   {a b c:FractionalIdeal R⁰ K} (hac:a ≤ c) (ha:a≠0) (hb:b≠0):
   ∃ x:K,a+FractionalIdeal.spanSingleton R⁰ x*b=c:=by
 wlog hb':b=1
 · obtain ⟨x,e⟩:=this (a:=b⁻¹*a) (b:=1) (c:=b⁻¹*c) (by gcongr) (by simp [ha,hb])
     one_ne_zero rfl
   use x
   simpa [hb, ←mul_assoc,mul_add,mul_comm b (.spanSingleton _ _)] using congr(b*$e)
 subst hb'
 have H:Ideal.span {c.den.1}*a.num ≤ c.num*Ideal.span {a.den.1}:=by
   rw [←FractionalIdeal.coeIdeal_le_coeIdeal K]
   simp only [FractionalIdeal.coeIdeal_mul,FractionalIdeal.coeIdeal_span_singleton, ←
     FractionalIdeal.den_mul_self_eq_num']
   ring_nf
   gcongr
 obtain ⟨x,hx⟩:=exists_sup_span_eq H
   (by simpa using FractionalIdeal.num_eq_zero_iff.not.mpr ha)
 refine ⟨algebraMap R K x/algebraMap R K (a.den.1*c.den.1),?_⟩
 refine mul_left_injective₀ (b:=.spanSingleton _
   (algebraMap R K (a.den.1*c.den.1))) ?_ ?_
 · simp [FractionalIdeal.spanSingleton_eq_zero_iff]
 · simp only [map_mul,mul_one,add_mul,FractionalIdeal.spanSingleton_mul_spanSingleton,
     isUnit_iff_ne_zero,ne_eq,mul_eq_zero,FaithfulSMul.algebraMap_eq_zero_iff,
     nonZeroDivisors.coe_ne_zero,or_self,not_false_eq_true,IsUnit.div_mul_cancel]
   rw [←FractionalIdeal.spanSingleton_mul_spanSingleton, ←mul_assoc,mul_comm a,
     FractionalIdeal.den_mul_self_eq_num', ←mul_assoc,mul_right_comm,
     mul_comm c,FractionalIdeal.den_mul_self_eq_num',mul_comm]
   simp_rw [←FractionalIdeal.coeIdeal_span_singleton, ←FractionalIdeal.coeIdeal_mul,
     ←hx, ←FractionalIdeal.coeIdeal_sup]
namespace FractionalIdeal
noncomputable
def divMod (c b a:FractionalIdeal R⁰ K):K:=
 letI:=Classical.propDecidable
 if h:a ≤ c∧a≠0∧b≠0 then
   (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0
lemma divMod_spec
   {a b c:FractionalIdeal R⁰ K} (hac:a ≤ c) (ha:a≠0) (hb:b≠0):
   a+spanSingleton R⁰ (c.divMod b a)*b=c:=by
 rw [divMod,dif_pos ⟨hac,ha,hb⟩]
 exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec
@[simp]
lemma divMod_zero_left {I J:FractionalIdeal R⁰ K}:I.divMod 0 J=0:=by
 simp [divMod]
@[simp]
lemma divMod_zero_right {I J:FractionalIdeal R⁰ K}:I.divMod J 0=0:=by
 simp [divMod]
@[simp]
lemma zero_divMod {I J:FractionalIdeal R⁰ K}:
   (0:FractionalIdeal R⁰ K).divMod I J=0:=by
 simp [divMod, ←and_assoc]
lemma divMod_zero_of_not_le {a b c:FractionalIdeal R⁰ K} (hac:¬ a ≤ c):
   c.divMod b a=0:=by
 simp [divMod,hac]
noncomputable
def quotientEquiv (I J I' J':FractionalIdeal R⁰ K)
   (H:I*J'=I'*J) (h:J ≤ I) (h':J' ≤ I') (hJ':J'≠0) (hI:I≠0):
   (I ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype) ≃ₗ[R]
     I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmodule.subtype:=by
 letI:DecidableEq K:=Classical.decEq K
 haveI:J' ⊓ spanSingleton R⁰ (I'.divMod I J')*I=spanSingleton R⁰ (I'.divMod I J')*J:=by
   have:=FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J')*I)
   rwa [FractionalIdeal.sup_eq_add,divMod_spec h' hJ' hI,mul_left_comm,mul_comm J' I,H,
     mul_comm I' J, ←mul_assoc,(mul_left_injective₀ _).eq_iff] at this
   rintro rfl
   exact hJ' (by simpa using h')
 refine .ofBijective (Submodule.mapQ _ _ (LinearMap.restrict
   (Algebra.lsmul R _ _ (I'.divMod I J')) ?_) ?_) ⟨?_,?_⟩
 · intro x hx
   refine (divMod_spec h' hJ' hI).le ?_
   exact Submodule.mem_sup_right (mul_mem_mul (mem_spanSingleton_self _ _) hx)
 · rw [←Submodule.comap_comp,LinearMap.subtype_comp_restrict,LinearMap.domRestrict,
     Submodule.comap_comp]
   refine Submodule.comap_mono ?_
   intro x hx
   refine (Submodule.mem_inf.mp (this.ge ?_)).1
   simp only [Algebra.lsmul_coe,smul_eq_mul]
   exact mul_mem_mul (mem_spanSingleton_self _ _) hx
 · rw [←LinearMap.ker_eq_bot,Submodule.mapQ,Submodule.ker_liftQ,
     LinearMap.ker_comp,Submodule.ker_mkQ, ←Submodule.comap_comp,
     LinearMap.subtype_comp_restrict, ←le_bot_iff,Submodule.map_le_iff_le_comap,
     Submodule.comap_bot,Submodule.ker_mkQ,LinearMap.domRestrict,
     Submodule.comap_comp, ←Submodule.map_le_iff_le_comap,
     Submodule.map_comap_eq,Submodule.range_subtype]
   by_cases H':I'.divMod I J'=0
   · obtain rfl:J'=I':=by simpa [H'] using divMod_spec h' hJ' hI
     obtain rfl:I=J:=mul_left_injective₀ hJ' (H.trans (mul_comm _ _))
     exact inf_le_left
   rw [←inv_mul_eq_iff_eq_mul₀ (by simpa [spanSingleton_eq_zero_iff] using H'),mul_inf₀
     (zero_le _),inv_mul_cancel_left₀ (by simpa [spanSingleton_eq_zero_iff] using H')] at this
   rw [←this,inf_comm,coe_inf]
   refine inf_le_inf ?_ le_rfl
   intro x hx
   rw [spanSingleton_inv]
   convert! mul_mem_mul (mem_spanSingleton_self _ _) hx
   simp [H']
 · have H:Submodule.map (Algebra.lsmul R R K (I'.divMod I J')) ↑I=
       (spanSingleton R⁰ (I'.divMod I J')*I):=by
     ext x
     simp [Submodule.mem_span_singleton_mul]
   rw [←LinearMap.range_eq_top,Submodule.mapQ,Submodule.range_liftQ,
     LinearMap.range_comp,LinearMap.restrict,LinearMap.range_codRestrict,
     LinearMap.range_domRestrict, ←top_le_iff,H,
     ←LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
     ←Submodule.map_top,Submodule.map_le_iff_le_comap,Submodule.comap_map_eq,Submodule.ker_mkQ,
     ←Submodule.map_le_map_iff_of_injective I'.coeToSubmodule.injective_subtype,
     Submodule.map_top,Submodule.map_sup,
     Submodule.map_comap_eq,Submodule.map_comap_eq,Submodule.range_subtype,sup_comm,
     inf_eq_right.mpr,inf_eq_right.mpr]
   · exact le_trans (divMod_spec h' hJ' hI).ge (by simp)
   · exact le_trans (by simp) (divMod_spec h' hJ' hI).le
   · exact h'
end FractionalIdeal
end div
section primesOver
variable {S:Type*} [CommRing S] [Algebra S R] [Algebra.IsIntegral S R] [IsDomain S]
 [Module.IsTorsionFree S R]
open IsDedekindDomain Ideal.IsDedekindDomain HeightOneSpectrum
theorem Ideal.map_algebraMap_eq_finsetProd_pow {p:Ideal S} [p.IsMaximal] (hp:p≠0):
   map (algebraMap S R) p=∏ P∈p.primesOver R,P^P.ramificationIdx S:=by
 classical
 have h:map (algebraMap S R) p≠0:=map_ne_bot_of_ne_bot hp
 rw [←finprod_heightOneSpectrum_factorization (I:=p.map (algebraMap S R)) h]
 let hF:Fintype {v:HeightOneSpectrum R | v.asIdeal∣map (algebraMap S R) p}:=
   (finite_factors h).fintype
 rw [finprod_eq_finsetProd_of_mulSupport_subset
   (s:={v | v.asIdeal∣p.map (algebraMap S R)}.toFinset), ←Finset.prod_set_coe,
   ←Finset.prod_set_coe]
 · let _:Fintype {v:HeightOneSpectrum R//v.asIdeal∣map (algebraMap S R) p}:=hF
   refine Fintype.prod_equiv (equivPrimesOver _ hp) _ _ fun ⟨v,_⟩↦?_
   have:v.asIdeal.LiesOver p:=by rwa [Ideal.liesOver_iff_dvd_map v.2.ne_top]
   simp [maxPowDividing_eq_pow_multiset_count _ h,ramificationIdx_eq_factors_count p v h]
 · intro v hv
   simpa [maxPowDividing,Function.mem_mulSupport,IsPrime.ne_top _,
     Associates.count_ne_zero_iff_dvd h (irreducible v)] using hv
@[deprecated (since:="2026-04-08")]
alias Ideal.map_algebraMap_eq_finset_prod_pow:=Ideal.map_algebraMap_eq_finsetProd_pow
end primesOver
section conversion
variable {R:Type*} [CommRing R] [IsDedekindDomain R]
namespace IsDedekindDomain.HeightOneSpectrum
variable {I:Ideal R} (hI:I≠⊥) (p:HeightOneSpectrum R)
include hI
open UniqueFactorizationMonoid in
@[simp]
lemma count_normalizedFactors_eq_multiplicity:
   Multiset.count p.asIdeal (normalizedFactors I)=multiplicity p.asIdeal I:=by
 have:=emultiplicity_eq_count_normalizedFactors (irreducible p) hI
 rw [normalize_eq p.asIdeal] at this
 apply_fun ((↑):ℕ → ℕ∞) using CharZero.cast_injective
 rw [←this]
 exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity
lemma maxPowDividing_eq_pow_multiplicity:
   p.maxPowDividing I=p.asIdeal^multiplicity p.asIdeal I:=by
 classical
 rw [maxPowDividing_eq_pow_multiset_count _ hI,count_normalizedFactors_eq_multiplicity hI]
@[simp]
lemma factorization_eq_multiplicity:
   factorization I p.asIdeal=multiplicity p.asIdeal I:=by
 rw [factorization_eq_count,count_normalizedFactors_eq_multiplicity hI]
end IsDedekindDomain.HeightOneSpectrum
end conversion
section multiplicity
@[simp]
lemma Ideal.emultiplicity_bot {R:Type*} [CommSemiring R] (I:Ideal R):emultiplicity I ⊥=⊤:=
 Submodule.zero_eq_bot (R:=R) (M:=R) ▸ emultiplicity_zero I
variable {R:Type*} [CommRing R] [IsDedekindDomain R]
lemma Ideal.finprod_heightOneSpectrum_pow_multiplicity {I:Ideal R} (hI:I≠⊥):
   ∏ᶠ p:HeightOneSpectrum R,p.asIdeal^multiplicity p.asIdeal I=I:=by
 simpa only [maxPowDividing_eq_pow_multiplicity hI]
   using finprod_heightOneSpectrum_factorization hI
namespace IsDedekindDomain.HeightOneSpectrum
variable (p:HeightOneSpectrum R) {I J:Ideal R}
lemma multiplicity_le_of_ideal_ge (h:J ≤ I) (hJ:J≠⊥):
   multiplicity p.asIdeal I ≤ multiplicity p.asIdeal J:=by
 rw [←count_normalizedFactors_eq_multiplicity hJ,
   ←count_normalizedFactors_eq_multiplicity <| ne_bot_of_le_ne_bot hJ h]
 exact Ideal.count_le_of_ideal_ge h hJ _
open UniqueFactorizationMonoid Multiset in
lemma multiplicity_sup (hI:I≠⊥) (hJ:J≠⊥):
   multiplicity p.asIdeal (I ⊔ J)=multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J:=by
 rw [Ideal.sup_eq_prod_inf_factors hI hJ, ←count_normalizedFactors_eq_multiplicity ?h,
   ←count_normalizedFactors_eq_multiplicity hI, ←count_normalizedFactors_eq_multiplicity hJ]
 case h => exact prod_inter_normalizedFactors_ne_zero I J
 rw [normalizedFactors_prod_inter_eq_inter]
 exact count_inter ..
variable (I J) in
lemma emultiplicity_sup:
   emultiplicity p.asIdeal (I ⊔ J)=emultiplicity p.asIdeal I ⊓ emultiplicity p.asIdeal J:=by
 rcases eq_or_ne I ⊥ with rfl | hI
 · simp
 rcases eq_or_ne J ⊥ with rfl | hJ
 · simp
 have:I ⊔ J≠⊥:=by grind
 have H {I':Ideal R} (h:I'≠⊥):FiniteMultiplicity p.asIdeal I':=
   FiniteMultiplicity.of_prime_left (prime p) h
 rw [(H this).emultiplicity_eq_multiplicity,(H hI).emultiplicity_eq_multiplicity,
   (H hJ).emultiplicity_eq_multiplicity,multiplicity_sup _ hI hJ]
 norm_cast
variable {ι:Type*} [Finite ι]
lemma emultiplicity_iSup (I:ι → Ideal R):
   emultiplicity p.asIdeal (⨆ i,I i)=⨅ i,emultiplicity p.asIdeal (I i):=by
 induction ι using Finite.induction_empty_option with
 | h_empty =>
   rw [iSup_of_empty,iInf_of_empty]
   exact emultiplicity_zero _
 | of_equiv e ih =>
   specialize ih (I ∘ e)
   rw [←sSup_range, ←sInf_range] at ih ⊢
   rw [EquivLike.range_comp I e] at ih
   rw [ih]
   exact congrArg _ <| EquivLike.range_comp (emultiplicity p.asIdeal <| I ·) e
 | h_option ih =>
   rw [iSup_option,emultiplicity_sup p ..,ih,iInf_option]
lemma multiplicity_iSup [Nonempty ι] {I:ι → Ideal R} (hI:∀ i,I i≠⊥):
   multiplicity p.asIdeal (⨆ i,I i)=⨅ i,multiplicity p.asIdeal (I i):=by
 have H i:FiniteMultiplicity p.asIdeal (I i):=
   FiniteMultiplicity.of_prime_left (prime p) <| hI i
 have H':FiniteMultiplicity p.asIdeal (⨆ i,I i):=by
   refine FiniteMultiplicity.of_prime_left (prime p) ?_
   contrapose! hI
   rw [←bot_eq_zero,iSup_eq_bot] at hI
   exact ⟨Classical.ofNonempty,hI _⟩
 have:=emultiplicity_iSup p I
 simp only [H'.emultiplicity_eq_multiplicity,(H _).emultiplicity_eq_multiplicity] at this
 exact_mod_cast this
end IsDedekindDomain.HeightOneSpectrum
end multiplicity
end
end ProximityFlatProofPort
end PackedLegacy_S8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier03 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.T0. -/
section PackedLegacy_T0
section ProximityFlatProofPort
variable {R:Type*} [CommRing R]
open Ideal UniqueFactorizationMonoid
open scoped nonZeroDivisors
theorem Ideal.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne {P:Ideal R}
   (hP:P.IsPrime) [IsDedekindDomain R] {x:R} (x_mem:x∈P) (hxP2:x∉P^2)
   (hxQ:∀ Q:Ideal R,IsPrime Q → Q≠P → x∉Q):P=Ideal.span {x}:=by
 classical
 by_cases hP0:P=⊥
 · subst hP0
   rwa [eq_comm,span_singleton_eq_bot, ←mem_bot]
 have hspan0:span {x}≠⊥:=mt Ideal.span_singleton_eq_bot.mp (hxP2 <| · ▸ zero_mem _)
 rw [←associated_iff_eq,associated_iff_normalizedFactors_eq_normalizedFactors hP0 hspan0]
 refine Multiset.ext' fun Q↦?_
 rw [normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible,normalize_eq,
   Multiset.count_singleton]
 symm
 split_ifs with hQ
 · subst hQ
   apply Ideal.count_normalizedFactors_eq <;> simpa
 by_cases hQp:IsPrime Q
 · apply Ideal.count_normalizedFactors_eq <;> simp [hxQ _ hQp hQ]
 exact Multiset.count_eq_zero.mpr fun hQi↦
   hQp <| isPrime_of_prime <| irreducible_iff_prime.mp <| irreducible_of_normalized_factor _ hQi
theorem FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top {R A:Type*}
   [CommRing R] [CommRing A] [Algebra R A] {S:Submonoid R} [IsLocalization S A]
   (I:(FractionalIdeal S A)ˣ) {v:A} (hv:v∈(↑I⁻¹:FractionalIdeal S A))
   (h:Submodule.comap (Algebra.linearMap R A) ((I:Submodule R A)*Submodule.span R {v})=⊤):
   Submodule.IsPrincipal (I:Submodule R A):=by
 have hinv:=I.mul_inv
 set J:=Submodule.comap (Algebra.linearMap R A) ((I:Submodule R A)*Submodule.span R {v})
 have hJ:IsLocalization.coeSubmodule A J=↑I*Submodule.span R {v}:=by
   rw [coe_ext_iff,coe_mul,coe_one] at hinv
   apply Submodule.map_comap_eq_self
   grw [←Submodule.one_eq_range, ←hinv,(Submodule.span_singleton_le_iff_mem _ _).2 hv]
 have:(1:A)∈↑I*Submodule.span R {v}:=by
   rw [←hJ,h,IsLocalization.coeSubmodule_top,Submodule.mem_one]
   exact ⟨1,(algebraMap R _).map_one⟩
 obtain ⟨w,hw,hvw⟩:=Submodule.mem_mul_span_singleton.1 this
 refine ⟨⟨w,?_⟩⟩
 rw [←FractionalIdeal.coe_spanSingleton S, ←inv_inv I,eq_comm]
 refine congr_arg coeToSubmodule (Units.eq_inv_of_mul_eq_one_left (le_antisymm ?_ ?_))
 · conv_rhs => rw [←hinv,mul_comm]
   grw [FractionalIdeal.spanSingleton_le_iff_mem.mpr hw]
 · rw [FractionalIdeal.one_le, ←hvw,mul_comm]
   exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hv
theorem FractionalIdeal.isPrincipal.of_finite_maximals_of_inv {A:Type*} [CommRing A]
   [Algebra R A] {S:Submonoid R} [IsLocalization S A] (hS:S ≤ R⁰)
   (hf:{I:Ideal R | I.IsMaximal}.Finite) (I I':FractionalIdeal S A) (hinv:I*I'=1):
   Submodule.IsPrincipal (I:Submodule R A):=by
 have hinv':=hinv
 rw [coe_ext_iff,coe_mul] at hinv
 let s:=hf.toFinset
 haveI:=Classical.decEq (Ideal R)
 have coprime:∀ M∈s,∀ M'∈s.erase M,M ⊔ M'=⊤:=by
   simp_rw [s,Finset.mem_erase,hf.mem_toFinset]
   rintro M hM M' ⟨hne,hM'⟩
   exact Ideal.IsMaximal.coprime_of_ne hM hM' hne.symm
 have nle:∀ M∈s,¬⨅ M'∈s.erase M,M' ≤ M:=fun M hM =>
   left_lt_sup.1
     ((hf.mem_toFinset.1 hM).lt_top.trans_eq (Ideal.sup_iInf_eq_top <| coprime M hM).symm)
 have:∀ M∈s,∃ a∈I,∃ b∈I',a*b∉IsLocalization.coeSubmodule A M:=by
   intro M hM;by_contra! h
   obtain ⟨x,hx,hxM⟩:=
     SetLike.exists_of_lt
       ((IsLocalization.coeSubmodule_strictMono hS (hf.mem_toFinset.1 hM).lt_top).trans_eq
         hinv.symm)
   exact hxM (Submodule.mul_le.2 h hx)
 choose! a ha b hb hm using this
 choose! u hu hum using fun M hM => SetLike.not_le_iff_exists.1 (nle M hM)
 let v:=∑ M∈s,u M • b M
 have hv:v∈I':=Submodule.sum_mem _ fun M hM => Submodule.smul_mem _ _ <| hb M hM
 refine
   FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
     (Units.mkOfMulEqOne I I' hinv') hv (of_not_not fun h => ?_)
 obtain ⟨M,hM,hJM⟩:=Ideal.exists_le_maximal _ h
 replace hM:=hf.mem_toFinset.2 hM
 have:∀ a∈I,∀ b∈I',∃ c,algebraMap R _ c=a*b:=by
   intro a ha b hb;have hi:=hinv.le
   obtain ⟨c, -,hc⟩:=hi (Submodule.mul_mem_mul ha hb)
   exact ⟨c,hc⟩
 have hmem:a M*v∈IsLocalization.coeSubmodule A M:=by
   obtain ⟨c,hc⟩:=this _ (ha M hM) v hv
   refine IsLocalization.coeSubmodule_mono _ hJM ⟨c,?_,hc⟩
   have:=Submodule.mul_mem_mul (ha M hM) (Submodule.mem_span_singleton_self v)
   rwa [←hc] at this
 simp_rw [v,Finset.mul_sum,mul_smul_comm] at hmem
 rw [←s.add_sum_erase _ hM,Submodule.add_mem_iff_left] at hmem
 · refine hm M hM ?_
   obtain ⟨c,hc:algebraMap R A c=a M*b M⟩:=this _ (ha M hM) _ (hb M hM)
   rw [←hc] at hmem ⊢
   rw [Algebra.smul_def, ←map_mul] at hmem
   obtain ⟨d,hdM,he⟩:=hmem
   rw [IsLocalization.injective _ hS he] at hdM
   exact Submodule.mem_map_of_mem <|
       ((hf.mem_toFinset.1 hM).isPrime.mem_or_mem hdM).resolve_left <| hum M hM
 · refine Submodule.sum_mem _ fun M' hM' => ?_
   rw [Finset.mem_erase] at hM'
   obtain ⟨c,hc⟩:=this _ (ha M hM) _ (hb M' hM'.2)
   rw [←hc,Algebra.smul_def, ←map_mul]
   specialize hu M' hM'.2
   simp_rw [Ideal.mem_iInf,Finset.mem_erase] at hu
   exact Submodule.mem_map_of_mem <| M.mul_mem_right _ <| hu M ⟨hM'.1.symm,hM⟩
theorem Ideal.IsPrincipal.of_finite_maximals_of_isUnit (hf:{I:Ideal R | I.IsMaximal}.Finite)
   {I:Ideal R} (hI:IsUnit (I:FractionalIdeal R⁰ (FractionRing R))):I.IsPrincipal:=
 (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
   (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
     (↑hI.unit⁻¹:FractionalIdeal R⁰ (FractionRing R)) hI.unit.mul_inv)
theorem IsPrincipalIdealRing.of_finite_maximals [IsDedekindDomain R]
   (h:{I:Ideal R | I.IsMaximal}.Finite):IsPrincipalIdealRing R:=
 ⟨fun I => by
   obtain rfl | hI:=eq_or_ne I ⊥
   · exact bot_isPrincipal
   apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit h
   exact .of_mul_eq_one _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩
theorem IsPrincipalIdealRing.of_finite_primes [IsDedekindDomain R]
   (h:{I:Ideal R | I.IsPrime}.Finite):IsPrincipalIdealRing R:=
 IsPrincipalIdealRing.of_finite_maximals <| h.subset fun _ hi↦hi.isPrime
section
variable [IsDedekindDomain R]
 (S:Type*) [CommRing S]
 [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
 (p:Ideal R) (hp0:p≠⊥) [IsPrime p]
 {Sₚ:Type*} [CommRing Sₚ] [Algebra S Sₚ]
 [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
 [Algebra R Sₚ] [IsScalarTower R S Sₚ]
include hp0
variable [IsDedekindDomain Sₚ]
theorem IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime [IsDomain S]
   {P:Ideal Sₚ} (hP:IsPrime P) (hP0:P≠⊥):
   P∈normalizedFactors (Ideal.map (algebraMap R Sₚ) p):=by
 have non_zero_div:Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰:=
   map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
     p.primeCompl_le_nonZeroDivisors
 letI:Algebra (Localization.AtPrime p) Sₚ:=localizationAlgebra p.primeCompl S
 haveI:IsScalarTower R (Localization.AtPrime p) Sₚ:=
   IsScalarTower.of_algebraMap_eq fun x => by
     rw [IsScalarTower.algebraMap_apply R S]
     exact (IsLocalization.map_eq (T:=Algebra.algebraMapSubmonoid S (primeCompl p))
       (Submonoid.le_comap_map _) x).symm
 obtain ⟨pid,p',⟨hp'0,hp'p⟩,hpu⟩:=
   (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime p)).mp
     (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp0 _)
 have:IsLocalRing.maximalIdeal (Localization.AtPrime p)≠⊥:=by
   rw [Submodule.ne_bot_iff] at hp0 ⊢
   obtain ⟨x,x_mem,x_ne⟩:=hp0
   exact
     ⟨algebraMap _ _ x,(IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr x_mem,
       IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors
         (mem_nonZeroDivisors_of_ne_zero x_ne)⟩
 rw [←Multiset.singleton_le, ←normalize_eq P, ←
   normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible, ←
   dvd_iff_normalizedFactors_le_normalizedFactors hP0,dvd_iff_le,
   IsScalarTower.algebraMap_eq R (Localization.AtPrime p) Sₚ, ←Ideal.map_map,
   Localization.AtPrime.map_eq_maximalIdeal,Ideal.map_le_iff_le_comap,
   hpu (IsLocalRing.maximalIdeal _) ⟨this,_⟩,hpu (comap _ _) ⟨_,_⟩]
 · have:Algebra.IsIntegral (Localization.AtPrime p) Sₚ:=⟨isIntegral_localization⟩
   exact mt (Ideal.eq_bot_of_comap_eq_bot) hP0
 · exact Ideal.comap_isPrime (algebraMap (Localization.AtPrime p) Sₚ) P
 · exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
 · rw [Ne,zero_eq_bot,Ideal.map_eq_bot_iff_of_injective]
   · assumption
   rw [IsScalarTower.algebraMap_eq R S Sₚ]
   exact
     (IsLocalization.injective Sₚ non_zero_div).comp (FaithfulSMul.algebraMap_injective _ _)
theorem IsDedekindDomain.isPrincipalIdealRing_localization_over_prime [IsDomain S]:
   IsPrincipalIdealRing Sₚ:=by
 letI:=Classical.decEq (Ideal Sₚ)
 letI:=Classical.decPred fun P:Ideal Sₚ => P.IsPrime
 refine
   IsPrincipalIdealRing.of_finite_primes
     (Set.Finite.ofFinset
       {P∈{⊥} ∪ (normalizedFactors (Ideal.map (algebraMap R Sₚ) p)).toFinset | P.IsPrime}
       fun P => ?_)
 rw [Finset.mem_filter,Finset.mem_union,Finset.mem_singleton,Set.mem_setOf,
   Multiset.mem_toFinset]
 exact
   and_iff_right_of_imp fun hP =>
     or_iff_not_imp_left.mpr (IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime S p hp0 hP)
end
theorem IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
   (R:Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R]:
   IsPrincipalIdealRing R:=by
 refine .of_prime_ne_bot fun P hp hp₀↦?_
 obtain ⟨x,hx₁,hx₂⟩:=hp.exists_mem_prime_of_ne_bot hp₀
 suffices Ideal.span {x}=P from this ▸ inferInstance
 have:=(Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
 exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp <|
   P.span_singleton_le_iff_mem.mpr hx₁
end ProximityFlatProofPort
end PackedLegacy_T0

/-! Packed from ProximityPrize.SubmissionLower.S9. -/
section PackedLegacy_S9
section ProximityFlatProofPort
open nonZeroDivisors IsLocalization Algebra Module IsFractionRing IsScalarTower
attribute [local instance] FractionRing.liftAlgebra
variable {R:Type*} (S:Type*) (T:Type*) [CommRing R] [CommRing S] [CommRing T] [IsDomain R]
 [IsDomain S] [IsDomain T] [Algebra R S]
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "F" => FractionRing T
section
theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A:Type*} (B:Type*)
   [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B]
   {S:Submonoid A} (hS:S ≤ A⁰):algebraMapSubmonoid B S ≤ B⁰:=
 map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS
variable (Rₘ Sₘ:Type*) [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [IsTorsionFree R S]
   [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M:Submonoid R} [IsLocalization M Rₘ]
   [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
   [IsScalarTower R S Sₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
   [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
   [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]
set_option backward.isDefEq.respectTransparency false in
include R S in
theorem FractionRing.isSeparable_of_isLocalization (hM:M ≤ R⁰):
   Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ):=by
 let M':=algebraMapSubmonoid S M
 have hM':algebraMapSubmonoid S M ≤ S⁰:=algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
   _ hM
 let f₁:Rₘ →+*K:=map _ (T:=R⁰) (RingHom.id R) hM
 let f₂:Sₘ →+*L:=map _ (T:=S⁰) (RingHom.id S) hM'
 algebraize [f₁,f₂]
 have:=localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
 have:=localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
 have:=isFractionRing_of_isDomain_of_isLocalization M Rₘ K
 have:=isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
 have:IsDomain Rₘ:=isDomain_of_le_nonZeroDivisors _ hM
 apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
   (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
 apply IsLocalization.ringHom_ext R⁰
 ext
 simp only [RingHom.coe_comp,
     RingHom.coe_coe,Function.comp_apply, ←algebraMap_apply]
 rw [algebraMap_apply R Rₘ (FractionRing R),AlgEquiv.coe_ringEquiv,AlgEquiv.commutes,
   algebraMap_apply R S L,algebraMap_apply S Sₘ L,AlgEquiv.coe_ringEquiv,AlgEquiv.commutes]
 simp only [←algebraMap_apply]
 rw [algebraMap_apply R Rₘ (FractionRing Rₘ), ←algebraMap_apply Rₘ, ←algebraMap_apply]
end
variable {P:Ideal R} [P.IsPrime]
local notation3 "P'" => algebraMapSubmonoid S P.primeCompl
local notation3 "Rₚ" => Localization.AtPrime P
local notation3 "Sₚ" => Localization P'
variable [FaithfulSMul R S]
instance:IsTorsionFree S Sₚ:=by
 rw [isTorsionFree_iff_algebraMap_injective,
   injective_iff_isRegular (algebraMapSubmonoid S P.primeCompl)]
 exact fun ⟨x,hx⟩↦isRegular_iff_ne_zero'.mpr <|
   ne_of_mem_of_not_mem hx <| by simp [Algebra.algebraMapSubmonoid]
instance:IsTorsionFree R Sₚ:=by
 have:=IsLocalization.AtPrime.faithfulSMul Rₚ R P
 exact IsTorsionFree.trans_faithfulSMul R Rₚ _
noncomputable abbrev Localization.AtPrime.liftAlgebra:Algebra Sₚ L:=
 (map _ (T:=S⁰) (RingHom.id S)
   (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
     P.primeCompl_le_nonZeroDivisors)).toAlgebra
attribute [local instance] Localization.AtPrime.liftAlgebra
instance:IsScalarTower S Sₚ L:=
 localization_isScalarTower_of_submonoid_le _ _ _ _
   (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
     P.primeCompl_le_nonZeroDivisors)
instance:IsFractionRing Rₚ K:=
 isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _
instance:IsFractionRing Sₚ L:=
 isFractionRing_of_isDomain_of_isLocalization P' _ _
noncomputable instance proximityPortAlgebraAtPrimeFractionRing:Algebra Rₚ L:=
 (lift (M:=P.primeCompl) (g:=algebraMap R L) <|
   fun ⟨x,hx⟩↦by simpa using fun h↦hx <| by simp [h]).toAlgebra
example:instAlgebraLocalizationAtPrime P=proximityPortAlgebraAtPrimeFractionRing (S:=R):=by
 with_reducible_and_instances rfl
instance:IsScalarTower Rₚ K L:=
 of_algebraMap_eq' (IsLocalization.ringHom_ext P.primeCompl
   (RingHom.ext fun x↦by simp [RingHom.algebraMap_toAlgebra]))
instance:IsScalarTower R Rₚ K:=
 of_algebraMap_eq' (RingHom.ext fun x↦by simp [RingHom.algebraMap_toAlgebra])
instance:IsScalarTower Rₚ Sₚ L:=by
 refine IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext P.primeCompl ?_
 rw [RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq R Rₚ Sₚ,IsScalarTower.algebraMap_eq R S Sₚ,
   ←RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq S Sₚ L,IsScalarTower.algebraMap_eq Rₚ K L,
   RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq, ←IsScalarTower.algebraMap_eq,
   ←IsScalarTower.algebraMap_eq]
set_option linter.overlappingInstances false in
instance [IsDedekindDomain S]:IsDedekindDomain Sₚ:=
 isDedekindDomain S
   (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _
set_option linter.overlappingInstances false in
instance [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [hP:NeZero P]:
   IsPrincipalIdealRing Sₚ:=
 IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h↦hP.1 h)
instance [Algebra.IsSeparable K L]:
   letI:Algebra Rₚ (FractionRing Sₚ):=OreLocalization.instAlgebra
   Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ):=
 let _:Algebra Rₚ (FractionRing Sₚ):=OreLocalization.instAlgebra
 FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors
local notation3 "P''" => algebraMapSubmonoid T P.primeCompl
local notation3 "Tₚ" => Localization P''
variable [Algebra S T] [Algebra R T] [IsScalarTower R S T]
instance:IsLocalization (algebraMapSubmonoid T P') Tₚ:=by
 rw [show algebraMapSubmonoid T P'=P'' by simp]
 exact Localization.isLocalization
noncomputable abbrev Localization.AtPrime.algebra_localization_localization:
   Algebra Sₚ Tₚ:=localizationAlgebra P' T
attribute [local instance] Localization.AtPrime.algebra_localization_localization
instance:IsScalarTower S Sₚ Tₚ:=
 IsScalarTower.of_algebraMap_eq' <|
   by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp, ←IsScalarTower.algebraMap_eq]
instance:IsScalarTower R Sₚ Tₚ:=
 IsScalarTower.of_algebraMap_eq' <|
   by rw [IsScalarTower.algebraMap_eq R S Sₚ, ←RingHom.comp_assoc,
     ←IsScalarTower.algebraMap_eq S, ←IsScalarTower.algebraMap_eq]
instance [Module.Finite S T]:Module.Finite Sₚ Tₚ:=Module.Finite.of_isLocalization S T P'
instance [IsTorsionFree S T]:IsTorsionFree Sₚ Tₚ:=
 .of_isLocalization S T <| algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ <|
   Ideal.primeCompl_le_nonZeroDivisors P
instance [Algebra.IsIntegral R S]:Algebra.IsIntegral Rₚ Sₚ:=
 Algebra.isIntegral_def.mpr <| (algebraMap_eq_map_map_submonoid P.primeCompl S Rₚ Sₚ ▸
   isIntegral_localization:(algebraMap Rₚ Sₚ).IsIntegral)
variable [IsTorsionFree R T]
instance:IsScalarTower Rₚ Sₚ Tₚ:=by
 refine ⟨fun a b c↦a.ind fun ⟨a₁,a₂⟩↦?_⟩
 have:a₂.val≠0:=nonZeroDivisors.ne_zero <| Ideal.primeCompl_le_nonZeroDivisors P <| a₂.prop
 rw [←smul_right_inj this, ←_root_.smul_assoc (M:=R) (N:=Sₚ), ←_root_.smul_assoc (M:=R)
   (α:=Sₚ), ←_root_.smul_assoc (M:=R) (α:=Tₚ),Localization.smul_mk,smul_eq_mul,
   Localization.mk_eq_mk',IsLocalization.mk'_mul_cancel_left,algebraMap_smul,algebraMap_smul,
   _root_.smul_assoc]
instance [IsTorsionFree S T] [Algebra.IsSeparable L F]:
   Algebra.IsSeparable (FractionRing Sₚ) (FractionRing Tₚ):=by
 refine FractionRing.isSeparable_of_isLocalization T Sₚ Tₚ (M:=P') ?_
 apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
 exact fun _ h↦mem_nonZeroDivisors_of_ne_zero <| ne_of_mem_of_not_mem h <| by simp
end ProximityFlatProofPort
end PackedLegacy_S9

/-! Packed from ProximityPrize.SubmissionLower.U4. -/
section PackedLegacy_U4
section ProximityFlatProofPort
theorem Int.card_ideal_quot (n:ℕ):Nat.card (ℤ ⧸ (Ideal.span {(n:ℤ)}))=n:=by
 simp [←Submodule.cardQuot_apply, ←Ideal.absNorm_apply]
instance Int.ideal_span_isMaximal_of_prime (p:ℕ) [Fact (Nat.Prime p)]:
   (Ideal.span {(p:ℤ)}).IsMaximal:=
 Ideal.Quotient.maximal_of_isField _ <|
   (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField (Field.toIsField _)
theorem Int.ringChar_idealQuot (n:ℕ):ringChar (ℤ ⧸ Ideal.span {(n:ℤ)})=n:=by
 refine ringChar.eq_iff.mpr <| (charP_iff _ _).mpr fun x↦?_
 change Ideal.Quotient.mk (Ideal.span {(n:ℤ)}) x=0 ↔ _
 rw [Ideal.Quotient.eq_zero_iff_mem, ←Int.cast_natCast,Ideal.mem_span_singleton,
   Int.cast_natCast,Int.natCast_dvd_natCast]
open Ideal
variable {R:Type*}
namespace Int
section Ring
variable [Ring R] {I:Ideal R}
instance liesOver_span_absNorm (I:Ideal R):
   I.LiesOver (span {(absNorm (_root_.Ideal.under ℤ I):ℤ)}):=by
 rw [liesOver_iff,under_def,Int.ideal_span_absNorm_eq_self]
theorem cast_mem_ideal_iff {d:ℤ}:
   (d:R)∈I ↔ (absNorm (_root_.Ideal.under ℤ I):ℤ)∣d:=by
 rw [←mem_span_singleton,ideal_span_absNorm_eq_self,under_def,mem_comap,eq_intCast]
variable (I)
theorem absNorm_under_mem:
   (absNorm (_root_.Ideal.under ℤ I):R)∈I:=by
 rw [←cast_natCast,cast_mem_ideal_iff]
theorem absNorm_under_eq_sInf:
   absNorm (_root_.Ideal.under ℤ I)=sInf {d:ℕ | 0 < d∧(d:R)∈I}:=by
 by_cases h:absNorm (_root_.Ideal.under ℤ I)=0
 · have:{d:ℕ | 0 < d∧↑d∈I}=∅:=by
     refine Set.eq_empty_of_forall_notMem ?_
     intro x ⟨hx₁,hx₂⟩
     rw [←cast_natCast,cast_mem_ideal_iff,h,natCast_dvd_natCast,Nat.zero_dvd] at hx₂
     rw [Nat.pos_iff_ne_zero] at hx₁
     exact hx₁ hx₂
   rw [h,this,Nat.sInf_empty]
 · have h₁:absNorm (_root_.Ideal.under ℤ I)∈{d:ℕ | 0 < d∧↑d∈I}:=
     ⟨Nat.pos_of_ne_zero h,absNorm_under_mem I⟩
   refine le_antisymm ?_ (Nat.sInf_le h₁)
   by_contra! h₀
   have h₂:=(Nat.sInf_mem (Set.nonempty_of_mem h₁)).2
   rw [←cast_natCast,cast_mem_ideal_iff,natCast_dvd_natCast] at h₂
   exact lt_iff_not_ge.mp h₀ <| Nat.le_of_dvd (Nat.sInf_mem (Set.nonempty_of_mem h₁)).1 h₂
theorem absNorm_under_dvd_absNorm {S:Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
   (I:Ideal S):
   absNorm (_root_.Ideal.under ℤ I)∣absNorm I:=by
 cases finite_or_infinite (S ⧸ I)
 · have:Fintype (S ⧸ I):=Fintype.ofFinite (S ⧸ I)
   have h_main {d:ℕ}:(d:S)∈I ↔ ∀ (x:S ⧸ I),d • x=0:=by
     simp_rw [nsmul_eq_mul, ←map_natCast (Ideal.Quotient.mk I), ←Quotient.eq_zero_iff_mem]
     exact ⟨fun h _↦by simp [h],fun h↦by simpa using h 1⟩
   rw [Ideal.absNorm_apply I,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
   simp_rw [absNorm_under_eq_sInf,h_main, ←AddMonoid.exponent_eq_sInf]
   exact AddGroup.exponent_dvd_card (G:=S ⧸ I)
 · rw [absNorm_apply I,Submodule.cardQuot_apply,Nat.card_eq_zero_of_infinite]
   exact Nat.dvd_zero _
theorem _root_.Ideal.ringChar_quot {S:Type*} [CommRing S] (I:Ideal S):
   ringChar (S ⧸ I)=absNorm (_root_.Ideal.under ℤ I):=by
 refine ringChar.eq_iff.mpr <| (charP_iff _ _).mpr fun x↦?_
 change Ideal.Quotient.mk I x=0 ↔ _
 rw [Quotient.eq_zero_iff_mem, ←Int.cast_natCast,cast_mem_ideal_iff,natCast_dvd_natCast]
end Ring
end Int
section CommRing
variable [CommRing R] [IsDomain R] [Algebra.IsIntegral ℤ R]
theorem Nat.absNorm_under_prime (P:Ideal R) [P.IsPrime] [NeZero P]:
   (absNorm (_root_.Ideal.under ℤ P)).Prime:=by
 rw [Nat.prime_iff_prime_int, ←span_singleton_prime,Int.ideal_span_absNorm_eq_self]
 · infer_instance
 · refine Int.natCast_ne_zero.mpr <| absNorm_eq_zero_iff.not.mpr ?_
   have:P≠⊥:=NeZero.ne _
   contrapose this
   exact eq_bot_of_comap_eq_bot this
end CommRing
end ProximityFlatProofPort
end PackedLegacy_U4

/-! Packed from ProximityPrize.SubmissionLower.IS. -/
section PackedLegacy_IS
section ProximityFlatProofPort
namespace Ring
noncomputable section NormalClosure
variable (R S:Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
 [Algebra R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=FractionRing.liftAlgebra _ _
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
   (AlgebraicClosure (FractionRing S))
local instance:Algebra S E:=((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance:IsScalarTower S L E:=IsScalarTower.of_algebraMap_eq' rfl
def NormalClosure:Type _:=integralClosure S E
local notation3 "T" => NormalClosure R S
instance:CommRing T:=inferInstanceAs (CommRing (integralClosure S E))
instance:IsDomain T:=inferInstanceAs (IsDomain (integralClosure S E))
instance:Nontrivial T:=inferInstanceAs (Nontrivial (integralClosure S E))
instance:Algebra S T:=inferInstanceAs (Algebra S (integralClosure S E))
local instance:Algebra T E:=inferInstanceAs (Algebra (integralClosure S E) E)
instance:Algebra R T:=((algebraMap S T).comp (algebraMap R S)).toAlgebra
local instance:IsScalarTower S T E:=
 inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance:IsIntegralClosure T S E:=integralClosure.isIntegralClosure S E
instance:IsScalarTower R S T:=IsScalarTower.of_algebraMap_eq' rfl
local instance:IsScalarTower R L E:=IsScalarTower.to₁₃₄ R K L E
local instance:IsScalarTower R S E:=IsScalarTower.to₁₂₄ R S L E
local instance:IsScalarTower R T E:=IsScalarTower.to₁₃₄ R S T E
local instance:FaithfulSMul S E:=(faithfulSMul_iff_algebraMap_injective S E).mpr <|
     (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)
instance:Module.IsTorsionFree S T:=Subalgebra.instIsTorsionFree (integralClosure S E)
instance:FaithfulSMul R T:=
 (faithfulSMul_iff_algebraMap_injective R T).mpr <|
     (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)
variable [Module.Finite R S]
local instance:FiniteDimensional L E:=Module.Finite.right K L E
local instance:IsFractionRing T E:=
 integralClosure.isFractionRing_of_finite_extension L E
instance:IsIntegrallyClosed T:=
 integralClosure.isIntegrallyClosedOfFiniteExtension L
variable [PerfectField (FractionRing R)]
local instance:Algebra.IsSeparable L E:=
 Algebra.isSeparable_tower_top_of_isSeparable K L E
instance:IsGalois K (FractionRing T):=by
 refine IsGalois.of_equiv_equiv (F:=K) («E»:=E)
   (f:=(FractionRing.algEquiv R K).symm.toRingEquiv)
   (g:=(FractionRing.algEquiv T E).symm.toRingEquiv) ?_
 ext
 simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
   (FractionRing.algEquiv T E).symm _
variable [IsDedekindDomain S]
set_option linter.overlappingInstances false
instance:Module.Finite S T:=
 IsIntegralClosure.finite S L E T
instance:Module.Finite R T:=
 Module.Finite.trans S T
instance:IsDedekindDomain T:=
 integralClosure.isDedekindDomain S L E
end Ring.NormalClosure
end ProximityFlatProofPort
end PackedLegacy_IS

/-! Packed from ProximityPrize.SubmissionLower.U6. -/
section PackedLegacy_U6
section ProximityFlatProofPort
open Module
open scoped nonZeroDivisors
section SpanNorm
namespace Ideal
open Submodule
variable (R S:Type*) [CommRing R] [IsDomain R] {S:Type*} [CommRing S] [IsDomain S]
 [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
 [IsTorsionFree R S]
attribute [local instance] FractionRing.liftAlgebra
noncomputable def spanNorm (I:Ideal S):Ideal R:=
 Ideal.map (Algebra.intNorm R S) I
@[simp]
theorem spanNorm_bot:
   spanNorm R (⊥:Ideal S)=⊥:=span_eq_bot.mpr fun x hx => by simpa using hx
variable {R} in
@[simp]
theorem spanNorm_eq_bot_iff {I:Ideal S}:spanNorm R I=⊥ ↔ I=⊥:=by
 simp only [spanNorm,span_eq_bot,Set.mem_image,SetLike.mem_coe,forall_exists_index,and_imp,
   forall_apply_eq_imp_iff₂,Algebra.intNorm_eq_zero,@eq_bot_iff _ _ _ I,SetLike.le_def,map,
   mem_bot]
theorem intNorm_mem_spanNorm {I:Ideal S} {x:S} (hx:x∈I):
   Algebra.intNorm R S x∈I.spanNorm R:=
 subset_span (Set.mem_image_of_mem _ hx)
theorem norm_mem_spanNorm [Module.Free R S] {I:Ideal S} (x:S) (hx:x∈I):
   Algebra.norm R x∈I.spanNorm R:=by
 refine subset_span ⟨x,hx,?_⟩
 rw [Algebra.intNorm_eq_norm]
@[simp]
theorem spanNorm_singleton {r:S}:
   spanNorm R (span ({r}:Set S))=span {Algebra.intNorm R S r}:=
 le_antisymm
   (span_le.mpr fun x hx =>
     mem_span_singleton.mpr
       (by
         obtain ⟨x,hx',rfl⟩:=(Set.mem_image _ _ _).mp hx
         exact map_dvd _ (mem_span_singleton.mp hx')))
   ((span_singleton_le_iff_mem _).mpr (intNorm_mem_spanNorm _ (mem_span_singleton_self _)))
@[simp]
theorem spanNorm_top:spanNorm R (⊤:Ideal S)=⊤:=by
 simp [←Ideal.span_singleton_one]
theorem map_spanIntNorm (I:Ideal S) {T:Type*} [Semiring T] (f:R →+*T):
   map f (spanNorm R I)=span (f ∘ Algebra.intNorm R S '' (I:Set S)):=by
 rw [spanNorm]
 nth_rw 2 [map]
 simp [map_span,Set.image_image]
@[gcongr,mono]
theorem spanNorm_mono {I J:Ideal S} (h:I ≤ J):spanNorm R I ≤ spanNorm R J:=
 Ideal.span_mono (Set.monotone_image h)
theorem spanIntNorm_localization (I:Ideal S) (M:Submonoid R) (hM:M ≤ R⁰)
   {Rₘ:Type*} (Sₘ:Type*) [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
   [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
   [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
   [IsIntegrallyClosed Rₘ] [IsDomain Rₘ] [IsDomain Sₘ] [IsTorsionFree Rₘ Sₘ]
   [Module.Finite Rₘ Sₘ] [IsIntegrallyClosed Sₘ]:
   spanNorm Rₘ (I.map (algebraMap S Sₘ))=(spanNorm R I).map (algebraMap R Rₘ):=by
 let K:=FractionRing R
 let f:Rₘ →+*K:=IsLocalization.map _ (T:=R⁰) (RingHom.id R) hM
 let L:=FractionRing S
 let g:Sₘ →+*L:=IsLocalization.map _ (M:=Algebra.algebraMapSubmonoid S M) (T:=S⁰)
     (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
     (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
       (FaithfulSMul.algebraMap_injective _ _)))
 algebraize [f,g,(algebraMap K L).comp f]
 have:IsScalarTower R Rₘ K:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 let _:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
 have:IsScalarTower S Sₘ L:=IsScalarTower.of_algebraMap_eq'
   (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
 have:IsScalarTower Rₘ Sₘ L:=by
   apply IsScalarTower.of_algebraMap_eq'
   apply IsLocalization.ringHom_ext M
   rw [RingHom.algebraMap_toAlgebra,RingHom.algebraMap_toAlgebra (R:=Sₘ),RingHom.comp_assoc,
     RingHom.comp_assoc, ←IsScalarTower.algebraMap_eq,IsScalarTower.algebraMap_eq R S Sₘ,
     IsLocalization.map_comp,RingHom.comp_id, ←RingHom.comp_assoc,IsLocalization.map_comp,
     RingHom.comp_id, ←IsScalarTower.algebraMap_eq, ←IsScalarTower.algebraMap_eq]
 let _:=IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
   (Algebra.algebraMapSubmonoid S M) Sₘ L
 rw [map_spanIntNorm]
 refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
 · intro a' ha'
   simp only [Set.mem_preimage,submodule_span_eq, ←map_spanIntNorm,SetLike.mem_coe,
     IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
     IsLocalization.mem_map_algebraMap_iff M Rₘ,Prod.exists] at ha' ⊢
   obtain ⟨⟨a,ha⟩,⟨_,⟨s,hs,rfl⟩⟩,has⟩:=ha'
   refine ⟨⟨Algebra.intNorm R S a,intNorm_mem_spanNorm _ ha⟩,
     ⟨s^Module.finrank K L,pow_mem hs _⟩,?_⟩
   simp only [map_pow] at has ⊢
   apply_fun algebraMap _ L at has
   apply_fun Algebra.norm K at has
   simp only [map_mul] at has
   rw [←IsScalarTower.algebraMap_apply, ←IsScalarTower.algebraMap_apply,
     ←IsScalarTower.algebraMap_apply,
     IsScalarTower.algebraMap_apply R K L,
     Algebra.norm_algebraMap] at has
   apply IsFractionRing.injective Rₘ K
   simp only [map_mul,map_pow]
   rwa [Algebra.algebraMap_intNorm (L:=L), ←IsScalarTower.algebraMap_apply,
     ←IsScalarTower.algebraMap_apply,Algebra.algebraMap_intNorm (L:=L)]
 · intro a ha
   rw [Set.mem_preimage,Function.comp_apply,Algebra.intNorm_eq_of_isLocalization M (Bₘ:=Sₘ)]
   exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))
theorem spanNorm_mul_spanNorm_le (I J:Ideal S):
   spanNorm R I*spanNorm R J ≤ spanNorm R (I*J):=by
 rw [spanNorm,spanNorm,spanNorm]
 nth_rw 1 [map];nth_rw 1 [map]
 rw [Ideal.span_mul_span', ←Set.image_mul]
 refine Ideal.span_mono (Set.monotone_image ?_)
 rintro _ ⟨x,hxI,y,hyJ,rfl⟩
 exact Ideal.mul_mem_mul hxI hyJ
theorem spanNorm_mul_of_bot_or_top (eq_bot_or_top:∀ I:Ideal R,I=⊥∨I=⊤) (I J:Ideal S):
   spanNorm R (I*J)=spanNorm R I*spanNorm R J:=by
 refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
 rcases eq_bot_or_top (spanNorm R I) with hI | hI
 · rw [hI,spanNorm_eq_bot_iff.mp hI,bot_mul,spanNorm_bot]
   exact bot_le
 rw [hI,Ideal.top_mul]
 rcases eq_bot_or_top (spanNorm R J) with hJ | hJ
 · rw [hJ,spanNorm_eq_bot_iff.mp hJ,mul_bot,spanNorm_bot]
 rw [hJ]
 exact le_top
theorem spanNorm_le_comap (I:Ideal S):spanNorm R I ≤ comap (algebraMap R S) I:=by
 rw [spanNorm,Ideal.map,Ideal.span_le, ←Submodule.span_le]
 intro x hx
 induction hx using Submodule.span_induction with
 | mem _ h =>
     obtain ⟨x,hx,rfl⟩:=h
     exact mem_comap.mpr <| mem_of_dvd _ (Algebra.dvd_algebraMap_intNorm_self _ _ x) hx
 | zero => simp
 | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
 | smul _ _ _ hx => exact Submodule.smul_mem _ _ hx
set_option linter.overlappingInstances false
theorem spanNorm_mul [IsDedekindDomain R] [IsDedekindDomain S] (I J:Ideal S):
   spanNorm R (I*J)=spanNorm R I*spanNorm R J:=by
 nontriviality R
 cases subsingleton_or_nontrivial S
 · have:∀ I:Ideal S,I=⊤:=fun I↦Subsingleton.elim I ⊤
   simp [this I,this J]
 refine eq_of_localization_maximal (fun P hP↦?_)
 by_cases hP0:P=⊥
 · subst hP0
   rw [spanNorm_mul_of_bot_or_top]
   intro I
   exact or_iff_not_imp_right.mpr fun hI↦(hP.eq_of_le hI bot_le).symm
 have:NeZero P:=⟨hP0⟩
 let P':=Algebra.algebraMapSubmonoid S P.primeCompl
 simp only [Ideal.map_mul, ←spanIntNorm_localization (R:=R) (Sₘ:=Localization P')
   _ _ P.primeCompl_le_nonZeroDivisors]
 rw [←(I.map _).span_singleton_generator, ←(J.map _).span_singleton_generator,
   span_singleton_mul_span_singleton,spanNorm_singleton,spanNorm_singleton,
   spanNorm_singleton,span_singleton_mul_span_singleton,map_mul]
section spanNorm_spanNorm
variable (T:Type*) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [Algebra R T] [Algebra T S]
 [Module.Finite R T] [Module.Finite T S] [IsTorsionFree R T] [IsTorsionFree T S]
 [IsScalarTower R T S]
open _root_.Algebra
theorem le_spanNorm_spanNorm (I:Ideal S):spanNorm R I ≤ spanNorm R (spanNorm T I):=by
 simp_rw [spanNorm,map]
 refine span_mono ?_
 rintro _ ⟨x,hx,rfl⟩
 exact ⟨intNorm T S x,subset_span <| Set.mem_image_of_mem _ hx,by rw [intNorm_intNorm]⟩
theorem spanNorm_spanNorm_of_bot_or_top (eq_bot_or_top:∀ I:Ideal R,I=⊥∨I=⊤)
   (I:Ideal S):spanNorm R (spanNorm T I)=spanNorm R I:=by
 obtain h | h:=eq_bot_or_top (spanNorm R I)
 · rw [h,spanNorm_eq_bot_iff,spanNorm_eq_bot_iff,spanNorm_eq_bot_iff.mp h]
 · exact h ▸ (eq_top_iff_one _).mpr <| le_spanNorm_spanNorm R T I <| (eq_top_iff_one _).mp h
attribute [local instance] Localization.AtPrime.algebra_localization_localization
theorem spanNorm_spanNorm [IsDedekindDomain R] [IsDedekindDomain T] [IsDedekindDomain S]
   (I:Ideal S):spanNorm R (spanNorm T I)=spanNorm R I:=by
 refine eq_of_localization_maximal fun P hP↦?_
 by_cases hP:P=⊥
 · subst hP
   rw [spanNorm_spanNorm_of_bot_or_top]
   exact fun I↦or_iff_not_imp_right.mpr fun hI↦(hP.eq_of_le hI bot_le).symm
 let Rₚ:=Localization.AtPrime P
 let Tₚ:=Localization (algebraMapSubmonoid T P.primeCompl)
 let Sₚ:=Localization (algebraMapSubmonoid S P.primeCompl)
 have:NeZero P:=⟨hP⟩
 have h:algebraMapSubmonoid T P.primeCompl ≤ T⁰:=
     algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (primeCompl_le_nonZeroDivisors P)
 rw [←spanIntNorm_localization R (spanNorm T I) _ (primeCompl_le_nonZeroDivisors P) Tₚ,
   ←spanIntNorm_localization T (Rₘ:=Tₚ) I _ h Sₚ, ←spanIntNorm_localization R (Rₘ:=Rₚ) I _
   (primeCompl_le_nonZeroDivisors P) Sₚ, ←(I.map _).span_singleton_generator,spanNorm_singleton,
   spanNorm_singleton,intNorm_intNorm,spanNorm_singleton]
end spanNorm_spanNorm
variable [IsDedekindDomain R] [IsDedekindDomain S]
noncomputable def relNorm:Ideal S →*₀ Ideal R where
 toFun:=spanNorm R
 map_zero':=spanNorm_bot R
 map_one':=by rw [one_eq_top,spanNorm_top R,one_eq_top]
 map_mul':=spanNorm_mul R
theorem relNorm_apply (I:Ideal S):
   relNorm R I=span (Algebra.intNorm R S '' (I:Set S):Set R):=
 rfl
@[simp]
theorem spanNorm_eq (I:Ideal S):spanNorm R I=relNorm R I:=rfl
@[simp]
theorem relNorm_bot:relNorm R (⊥:Ideal S)=⊥:=by
 simpa only [zero_eq_bot] using map_zero (relNorm R:Ideal S →*₀ _)
@[simp]
theorem relNorm_top:relNorm R (⊤:Ideal S)=⊤:=by
 simpa only [one_eq_top] using map_one (relNorm R:Ideal S →*₀ _)
variable {R} in
@[simp]
theorem relNorm_eq_bot_iff {I:Ideal S}:relNorm R I=⊥ ↔ I=⊥:=
 spanNorm_eq_bot_iff
theorem norm_mem_relNorm [Module.Free R S] (I:Ideal S) {x:S} (hx:x∈I):
   Algebra.norm R x∈relNorm R I:=
 norm_mem_spanNorm R x hx
@[simp]
theorem relNorm_singleton (r:S):relNorm R (span ({r}:Set S))=span {Algebra.intNorm R S r}:=
 spanNorm_singleton R
theorem map_relNorm (I:Ideal S) {T:Type*} [Semiring T] (f:R →+*T):
   map f (relNorm R I)=span (f ∘ Algebra.intNorm R S '' (I:Set S)):=
 map_spanIntNorm R I f
@[gcongr,mono]
theorem relNorm_mono {I J:Ideal S} (h:I ≤ J):relNorm R I ≤ relNorm R J:=
 spanNorm_mono R h
variable {R}
private theorem relNorm_map_algEquiv_aux {T:Type*} [CommRing T] [IsDedekindDomain T]
   [IsIntegrallyClosed T] [Algebra R T] [Module.Finite R T] [IsTorsionFree R T]
   (σ:S ≃ₐ[R] T) (I:Ideal S):relNorm R (I.map σ) ≤ relNorm R I:=
 span_mono fun _ ⟨x,hx₁,hx₂⟩↦⟨σ.toRingEquiv.symm x,
   by rwa [SetLike.mem_coe,Ideal.symm_apply_mem_of_equiv_iff],
   hx₂ ▸ Algebra.intNorm_map_algEquiv _ x σ.symm⟩
@[simp]
theorem relNorm_map_algEquiv {T:Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
   [Algebra R T] [Module.Finite R T] [IsTorsionFree R T] (σ:S ≃ₐ[R] T) (I:Ideal S):
   relNorm R (I.map σ)=relNorm R I:=by
 refine le_antisymm (relNorm_map_algEquiv_aux σ I) ?_
 convert! relNorm_map_algEquiv_aux σ.symm (I.map σ)
 change I=map σ.symm.toAlgHom (map σ.toAlgHom I)
 simp [map_mapₐ]
@[simp]
theorem relNorm_comap_algEquiv {T:Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
   [Algebra R T] [Module.Finite R T] [IsTorsionFree R T] (σ:S ≃ₐ[R] T) (I:Ideal T):
   relNorm R (I.comap σ)=relNorm R I:=map_symm σ.toRingEquiv ▸ relNorm_map_algEquiv σ.symm I
variable (R)
open MulSemiringAction Pointwise in
@[simp]
theorem relNorm_smul {G:Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g:G)
   (I:Ideal S):relNorm R (g • I)=relNorm R I:=relNorm_map_algEquiv (toAlgEquiv R S g) I
theorem relNorm_le_comap (I:Ideal S):relNorm R I ≤ comap (algebraMap R S) I:=
 spanNorm_le_comap R I
theorem relNorm_relNorm (T:Type*) [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
   [Algebra R T] [Algebra T S] [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
   [IsTorsionFree R T] [IsTorsionFree T S]
   (I:Ideal S):relNorm R (relNorm T I)=relNorm R I:=
 spanNorm_spanNorm _ _ _
variable {R} (S)
attribute [local instance] Localization.AtPrime.liftAlgebra in
theorem relNorm_algebraMap (I:Ideal R):
   relNorm R (I.map (algebraMap R S))=
     I^Module.finrank (FractionRing R) (FractionRing S):=by
 rw [←spanNorm_eq]
 refine eq_of_localization_maximal (fun P hPd↦?_)
 let P':=Algebra.algebraMapSubmonoid S P.primeCompl
 let Rₚ:=Localization.AtPrime P
 let K:=FractionRing R
 rw [←spanIntNorm_localization R _ _ P.primeCompl_le_nonZeroDivisors (Localization P'),
     Ideal.map_pow,I.map_map, ←IsScalarTower.algebraMap_eq,IsScalarTower.algebraMap_eq R Rₚ,
     ←I.map_map, ←(I.map _).span_singleton_generator,Ideal.map_span,Set.image_singleton,
     spanNorm_singleton,Ideal.span_singleton_pow]
 congr 2
 apply IsFractionRing.injective Rₚ K
 rw [Algebra.algebraMap_intNorm (L:=FractionRing S), ←IsScalarTower.algebraMap_apply,
   IsScalarTower.algebraMap_apply Rₚ K,Algebra.norm_algebraMap,map_pow]
variable (R)
theorem relNorm_algebraMap' {R'} [CommRing R'] (I:Ideal R') [Algebra R' R]
   [Algebra R' S] [IsScalarTower R' R S]:relNorm R (I.map (algebraMap R' S))=
     I.map (algebraMap R' R)^Module.finrank (FractionRing R) (FractionRing S):=by
 rw [←relNorm_algebraMap,Ideal.map_map,IsScalarTower.algebraMap_eq R' R S]
section relNorm_prime
variable {R} {S} (P:Ideal S) (p:Ideal R) [hPp:P.LiesOver p]
theorem exists_relNorm_eq_pow_of_isPrime [p.IsPrime]:∃ s,relNorm R P=p^s:=by
 by_cases hp:p=⊥
 · refine ⟨1,?_⟩
   have:P.LiesOver ⊥:=hp ▸ hPp
   rw [hp,eq_bot_of_liesOver_bot R P,relNorm_bot,bot_pow (one_ne_zero)]
 have h:relNorm R (map (algebraMap R S) p) ≤ relNorm R P:=
   relNorm_mono _ <| map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp
 rw [relNorm_algebraMap S, ←dvd_iff_le,dvd_prime_pow (prime_of_isPrime hp inferInstance)] at h
 obtain ⟨s,_,hs⟩:=h
 exact ⟨s,by rwa [associated_iff_eq] at hs⟩
theorem relNorm_eq_pow_of_isPrime_isGalois [p.IsMaximal] [P.IsPrime]
   [IsGalois (FractionRing R) (FractionRing S)]:relNorm R P=p^P.inertiaDeg R:=by
 have:P.IsMaximal:=IsMaximal.of_liesOver_isMaximal P p
 let G:=Gal(FractionRing S/FractionRing R)
 let:=IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
 have:=IsGaloisGroup.of_isFractionRing G R S (FractionRing R) (FractionRing S)
 by_cases hp:p=⊥
 · have h:P.inertiaDeg R≠0:=(inertiaDeg_pos P R).ne'
   have hP:P=⊥:=by
     rw [hp] at hPp
     exact eq_bot_of_liesOver_bot R P
   rw [hp,hP,relNorm_bot,bot_pow]
   rwa [hP] at h
 obtain ⟨s,hs⟩:=exists_relNorm_eq_pow_of_isPrime P p
 suffices s=P.inertiaDeg R by rwa [this] at hs
 have h₀:∀ Q∈(p.primesOver S).toFinset,
     relNorm R Q^Q.ramificationIdx R=p^((p.ramificationIdxIn S)*s):=by
   intro Q hQ
   rw [Set.mem_toFinset] at hQ
   have:Q.IsPrime:=hQ.1
   have:Q.LiesOver p:=hQ.2
   rw [←ramificationIdxIn_eq_ramificationIdx p Q G]
   obtain ⟨σ,rfl⟩:=Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
   rw [relNorm_smul,hs, ←pow_mul,mul_comm]
 have h:=(congr_arg (relNorm R ·) <|
   map_algebraMap_eq_finsetProd_pow hp).symm.trans <| relNorm_algebraMap S p
 simp+contextual only [map_prod,map_pow,h₀,Finset.prod_const, ←pow_mul] at h
 rwa [←IsGaloisGroup.card_eq_finrank G (FractionRing R) (FractionRing S),
   ←Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,mul_comm,
   ←Set.ncard_eq_toFinset_card',
   ((IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp).pow_injective _).eq_iff,
   mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero p S),
   mul_right_inj' (ramificationIdxIn_ne_zero G),inertiaDegIn_eq_inertiaDeg p P G] at h
 rw [one_eq_top]
 exact IsMaximal.ne_top inferInstance
theorem relNorm_eq_pow_of_isMaximal [PerfectField (FractionRing R)] [P.IsMaximal] [p.IsMaximal]:
   relNorm R P=p^P.inertiaDeg R:=by
 let T:=Ring.NormalClosure R S
 obtain ⟨Q,hQ₁,hQ₂⟩:∃ Q:Ideal T,Q.IsMaximal∧Q.LiesOver P:=
   exists_maximal_ideal_liesOver_of_isIntegral P
 have:Q.LiesOver p:=LiesOver.trans Q P p
 have h:=relNorm_eq_pow_of_isPrime_isGalois Q p
 have:IsGalois (FractionRing S) (FractionRing T):=
   IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
 rwa [←relNorm_relNorm R S,relNorm_eq_pow_of_isPrime_isGalois Q P,map_pow,
   inertiaDeg_tower (R:=R) P Q,pow_mul,pow_left_inj (inertiaDeg_pos Q S).ne'] at h
end relNorm_prime
section absNorm
variable [Module.Free ℤ R] [Module.Free ℤ S] [Module.Finite ℤ S]
open UniqueFactorizationMonoid in
theorem absNorm_relNorm [PerfectField (FractionRing R)] (I:Ideal S):
   absNorm (relNorm R I)=absNorm I:=by
 have:Module.Finite ℤ R:=Module.Finite.left ℤ R S
 by_cases hI:I=⊥
 · simp [hI]
 rw [←prod_normalizedFactors_eq_self hI]
 refine Multiset.prod_induction (fun I↦absNorm (relNorm R I)=absNorm I) _ ?_ ?_ ?_
 · intro _ _ hx hy
   rw [map_mul,map_mul,map_mul,hx,hy]
 · simp
 · intro Q hQ
   have hQ':Q≠⊥:=ne_zero_of_mem_normalizedFactors hQ
   rw [Ideal.mem_normalizedFactors_iff hI] at hQ
   have:Q.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
   let P:=Ideal.under R Q
   let p:=absNorm (Ideal.under ℤ P)
   have:Q.LiesOver (span {(p:ℤ)}):=LiesOver.trans Q P _
   rw [relNorm_eq_pow_of_isMaximal Q P,map_pow, ←pow_inertiaDeg p, ←pow_inertiaDeg p,
     ←pow_mul, ←inertiaDeg_tower]
theorem relNorm_int (I:Ideal S):
   relNorm ℤ I=Ideal.span {(absNorm I:ℤ)}:=by
 rw [←Int.ideal_span_absNorm_eq_self (relNorm ℤ I),absNorm_relNorm]
theorem absNorm_algebraMap (I:Ideal R) [Module.Finite ℤ R]:
   absNorm (I.map (algebraMap R S))=
     (absNorm I)^Module.finrank (FractionRing R) (FractionRing S):=by
 rw [←absNorm_relNorm ℤ, ←relNorm_relNorm ℤ R,relNorm_algebraMap,absNorm_relNorm,map_pow]
end absNorm
end Ideal
end SpanNorm
end ProximityFlatProofPort
end PackedLegacy_U6

/-! Packed from ProximityPrize.SubmissionLower.W9. -/
section PackedLegacy_W9
namespace ProximityPrize.SubmissionLower.RCN367
noncomputable section
section Fields
variable (F E Ω:Type*) [Field F] [Field E] [Field Ω]
 [Algebra F E] [Algebra F Ω] [Algebra.IsSeparable F E]
theorem normalClosure_isSeparable:
   Algebra.IsSeparable F (IntermediateField.normalClosure F E Ω):=by
 letI:∀ σ:E →ₐ[F] Ω,Algebra.IsSeparable F σ.fieldRange:=
   fun σ↦AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField σ)
 change Algebra.IsSeparable F
   (⨆ σ:E →ₐ[F] Ω,σ.fieldRange:IntermediateField F Ω)
 infer_instance
end Fields
section Domains
variable (R S:Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
 [Algebra R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R)
 (FractionRing S) (AlgebraicClosure (FractionRing S))
local notation3 "T" => Ring.NormalClosure R S
local instance:Algebra S E:=
 ((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance:IsScalarTower S L E:=IsScalarTower.of_algebraMap_eq' rfl
local instance:Algebra T E:=
 inferInstanceAs (Algebra (integralClosure S E) E)
local instance:IsScalarTower S T E:=
 inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance:IsIntegralClosure T S E:=integralClosure.isIntegralClosure S E
local instance:IsScalarTower R L E:=IsScalarTower.to₁₃₄ R K L E
local instance:IsScalarTower R S E:=IsScalarTower.to₁₂₄ R S L E
local instance:IsScalarTower R T E:=IsScalarTower.to₁₃₄ R S T E
local instance:FaithfulSMul S E:=
 (faithfulSMul_iff_algebraMap_injective S E).mpr <|
   (FaithfulSMul.algebraMap_injective L E).comp
     (FaithfulSMul.algebraMap_injective S L)
variable [Module.Finite R S]
 [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
local instance:FiniteDimensional L E:=Module.Finite.right K L E
local instance:IsFractionRing T E:=
 integralClosure.isFractionRing_of_finite_extension L E
local instance:Algebra.IsSeparable K E:=
 normalClosure_isSeparable K L (AlgebraicClosure L)
local instance:IsGalois K E where
local instance:Algebra.IsSeparable L E:=
 Algebra.isSeparable_tower_top_of_isSeparable K L E
theorem normalClosure_fractionRing_isGalois:
   IsGalois K (FractionRing T):=by
 refine IsGalois.of_equiv_equiv (F:=K) («E»:=E)
   (f:=(FractionRing.algEquiv R K).symm.toRingEquiv)
   (g:=(FractionRing.algEquiv T E).symm.toRingEquiv) ?_
 ext
 simpa using! IsFractionRing.algEquiv_commutes
   (FractionRing.algEquiv R K).symm (FractionRing.algEquiv T E).symm _
variable [IsDedekindDomain S]
theorem normalClosure_finite:Module.Finite S T:=
 IsIntegralClosure.finite S L E T
local instance:Module.Finite S T:=normalClosure_finite R S
local instance:Module.Finite R T:=Module.Finite.trans S T
theorem normalClosure_isDedekindDomain:IsDedekindDomain T:=
 integralClosure.isDedekindDomain S L E
local instance:IsDedekindDomain T:=normalClosure_isDedekindDomain R S
local instance:IsGalois K (FractionRing T):=
 normalClosure_fractionRing_isGalois R S
variable [IsDedekindDomain R]
attribute [local instance] FractionRing.liftAlgebra
theorem relNorm_prime_eq_pow
   (P:Ideal S) (p:Ideal R) [P.LiesOver p]
   [P.IsMaximal] [p.IsMaximal]:
   Ideal.relNorm R P=p^P.inertiaDeg R:=by
 obtain ⟨Q,hQmax,hQP⟩:
     ∃ Q:Ideal T,Q.IsMaximal∧Q.LiesOver P:=
   Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
 have:Q.LiesOver p:=Ideal.LiesOver.trans Q P p
 have h:=Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
 have:IsGalois (FractionRing S) (FractionRing T):=
   IsGalois.tower_top_of_isGalois
     (FractionRing R) (FractionRing S) (FractionRing T)
 rwa [←Ideal.relNorm_relNorm R S,
   Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P,map_pow,
   Ideal.inertiaDeg_tower (R:=R) P Q,pow_mul,
   pow_left_inj (Ideal.inertiaDeg_pos Q S).ne'] at h
theorem relNorm_eq_prod_prime_powers
   (I:Ideal S) (hI:I≠⊥):
   Ideal.relNorm R I=
     ((UniqueFactorizationMonoid.normalizedFactors I).map
       (fun P:Ideal S↦(P.under R)^P.inertiaDeg R)).prod:=by
 classical
 calc
   Ideal.relNorm R I=
       Ideal.relNorm R (UniqueFactorizationMonoid.normalizedFactors I).prod:=by
     rw [Ideal.prod_normalizedFactors_eq_self hI]
   _=((UniqueFactorizationMonoid.normalizedFactors I).map
       (Ideal.relNorm R)).prod:=map_multiset_prod (Ideal.relNorm R) _
   _=_:=by
     congr 1
     apply Multiset.map_congr rfl
     intro P hP
     have hPzero:P≠⊥:=
       UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hP
     have hPprime:P.IsPrime:=(Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
     letI:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
     exact relNorm_prime_eq_pow R S P (P.under R)
theorem span_intNorm_eq_prod_prime_powers
   (x:S) (hx:x≠0):
   Ideal.span {Algebra.intNorm R S x}=
     ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).map
       (fun P:Ideal S↦(P.under R)^P.inertiaDeg R)).prod:=by
 rw [←Ideal.relNorm_singleton]
 exact relNorm_eq_prod_prime_powers R S (Ideal.span {x})
   (by simpa using hx)
theorem intNorm_maps_to_fieldNorm (x:S):
   algebraMap R (FractionRing R) (Algebra.intNorm R S x)=
     Algebra.norm (FractionRing R)
       (algebraMap S (FractionRing S) x):=
 Algebra.algebraMap_intNorm_fractionRing x
end Domains
end
end ProximityPrize.SubmissionLower.RCN367
end PackedLegacy_W9

/-! Packed from ProximityPrize.SubmissionLower.G2. -/
section PackedLegacy_G2
namespace ProximityPrize.SubmissionLower.RCN356
open scoped BigOperators nonZeroDivisors
open UniqueFactorizationMonoid IsDedekindDomain
noncomputable section
section Orders
variable {A:Type*} [CommRing A] [IsDedekindDomain A]
def orderAt (v:HeightOneSpectrum A) (x:FractionRing A):ℤ:=
 -(v.valuation (FractionRing A) x).log
theorem orderAt_algebraMap (v:HeightOneSpectrum A) (x:A) (hx:x≠0):
   orderAt v (algebraMap A (FractionRing A) x)=
     ((normalizedFactors (Ideal.span {x})).count v.asIdeal:ℤ):=by
 rw [orderAt,v.valuation_of_algebraMap,v.intValuation_if_neg hx,
   WithZero.log_exp,neg_neg,
   Ideal.count_associates_factors_eq (by simpa using hx) v.isPrime v.ne_bot]
theorem orderAt_div (v:HeightOneSpectrum A) (x y:FractionRing A)
   (hx:x≠0) (hy:y≠0):
   orderAt v (x/y)=orderAt v x-orderAt v y:=by
 unfold orderAt
 rw [map_div₀,WithZero.log_div (by simpa using hx) (by simpa using hy)]
 ring
end Orders
section FixedExtension
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
def primeFiber (v:HeightOneSpectrum R):Finset (Ideal S):=
 IsDedekindDomain.primesOverFinset v.asIdeal S
theorem mem_primeFiber_iff (v:HeightOneSpectrum R) (P:Ideal S):
   P∈primeFiber R S v ↔ P.IsPrime∧P.LiesOver v.asIdeal:=
 IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S
def fiberPlace (v:HeightOneSpectrum R)
   (P:{P:Ideal S//P∈primeFiber R S v}):HeightOneSpectrum S:=
 ⟨P.1,((mem_primeFiber_iff R S v P.1).mp P.2).1,
   Ideal.ne_bot_of_mem_primesOver v.ne_bot
     ((mem_primeFiber_iff R S v P.1).mp P.2)⟩
theorem factorCount_relNorm_prime (v:HeightOneSpectrum R)
   (P:Ideal S) (hPzero:P≠⊥) (hPprime:P.IsPrime):
   (normalizedFactors (Ideal.relNorm R P)).count v.asIdeal=
     if P.under R=v.asIdeal then P.inertiaDeg R else 0:=by
 classical
 letI:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
 have hUnderZero:P.under R≠⊥:=
   mt Ideal.eq_bot_of_comap_eq_bot hPzero
 have hUnderPrime:(P.under R).IsPrime:=inferInstance
 have hUnderIrred:Irreducible (P.under R):=
   (Ideal.prime_of_isPrime hUnderZero hUnderPrime).irreducible
 rw [RCN367.relNorm_prime_eq_pow R S P (P.under R),
   hUnderIrred.normalizedFactors_pow,normalize_eq,Multiset.count_replicate]
theorem factorCount_relNorm (v:HeightOneSpectrum R)
   (I:Ideal S) (hI:I≠⊥):
   (normalizedFactors (Ideal.relNorm R I)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors I).count P:=by
 classical
 let C:Ideal S → Prop:=fun J↦J≠0∧
   (normalizedFactors (Ideal.relNorm R J)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors J).count P
 have hC:C (normalizedFactors I).prod:=by
   refine Multiset.prod_induction C (normalizedFactors I) ?_ ?_ ?_
   · intro J K hJ hK
     change _∧_ at hJ hK ⊢
     refine ⟨mul_ne_zero hJ.1 hK.1,?_⟩
     have hNJ:Ideal.relNorm R J≠0:=by simpa using hJ.1
     have hNK:Ideal.relNorm R K≠0:=by simpa using hK.1
     rw [map_mul,normalizedFactors_mul hNJ hNK,Multiset.count_add,
       hJ.2,hK.2,normalizedFactors_mul hJ.1 hK.1]
     simp only [Multiset.count_add,mul_add,Finset.sum_add_distrib]
   · change _∧_
     exact ⟨one_ne_zero,by
       simp only [map_one,normalizedFactors_one,Multiset.count_zero,
         mul_zero,Finset.sum_const_zero]⟩
   · intro P hP
     have hPzero:P≠⊥:=ne_zero_of_mem_normalizedFactors hP
     have hPprime:P.IsPrime:=(Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
     have hPirred:Irreducible P:=
       (Ideal.prime_of_isPrime hPzero hPprime).irreducible
     have hFactors:normalizedFactors P={P}:=by
       simpa using normalizedFactors_irreducible hPirred
     change _∧_
     refine ⟨hPzero,?_⟩
     rw [factorCount_relNorm_prime R S v P hPzero hPprime,hFactors]
     by_cases hUnder:P.under R=v.asIdeal
     · letI:P.LiesOver v.asIdeal:=by rw [←hUnder];infer_instance
       have hMem:P∈primeFiber R S v:=
         (mem_primeFiber_iff R S v P).mpr ⟨hPprime,inferInstance⟩
       simp [hUnder,Multiset.count_singleton,hMem]
     · have hNotMem:P∉primeFiber R S v:=by
         intro hMem
         letI:P.LiesOver v.asIdeal:=
           ((mem_primeFiber_iff R S v P).mp hMem).2
         exact hUnder (Ideal.over_def P v.asIdeal).symm
       simp [hUnder,Multiset.count_singleton,hNotMem]
 have hCI:C I:=by
   rwa [Ideal.prod_normalizedFactors_eq_self hI] at hC
 exact hCI.2
theorem orderAt_intNorm (v:HeightOneSpectrum R) (x:S) (hx:x≠0):
   orderAt v (algebraMap R (FractionRing R) (Algebra.intNorm R S x))=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x):=by
 classical
 have hCount:=factorCount_relNorm R S v (Ideal.span {x}) (by simpa using hx)
 rw [Ideal.relNorm_singleton] at hCount
 have hTerms:
     (∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x))=
     ∑ P∈primeFiber R S v,
       (P.inertiaDeg R:ℤ)*((normalizedFactors (Ideal.span {x})).count P:ℤ):=by
   calc
     _=∑ P∈(primeFiber R S v).attach,
         (P.1.inertiaDeg R:ℤ)*
           ((normalizedFactors (Ideal.span {x})).count P.1:ℤ):=by
       apply Finset.sum_congr rfl
       intro P _
       rw [orderAt_algebraMap _ x hx]
       rfl
     _=_:=Finset.sum_attach (primeFiber R S v)
       (fun P:Ideal S↦(P.inertiaDeg R:ℤ)*
         ((normalizedFactors (Ideal.span {x})).count P:ℤ))
 rw [hTerms,orderAt_algebraMap v (Algebra.intNorm R S x) (by simpa using hx)]
 exact_mod_cast hCount
theorem orderAt_fieldNorm (v:HeightOneSpectrum R)
   (x:FractionRing S) (hx:x≠0):
   orderAt v (Algebra.norm (FractionRing R) x)=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*orderAt (fiberPlace R S v P) x:=by
 classical
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=S) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hNorm:
     Algebra.norm (FractionRing R)
         (algebraMap S (FractionRing S) a/algebraMap S (FractionRing S) b)=
       algebraMap R (FractionRing R) (Algebra.intNorm R S a)/
         algebraMap R (FractionRing R) (Algebra.intNorm R S b):=by
   simp [div_eq_mul_inv,Algebra.norm_inv,Algebra.algebraMap_intNorm_fractionRing]
 rw [hNorm,orderAt_div v _ _ (by simpa using hazero) (by simpa using hbzero),
   orderAt_intNorm R S v a hazero,orderAt_intNorm R S v b hbzero,
   ←Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro P _
 rw [orderAt_div _ _ _ (by simpa using hazero) (by simpa using hbzero),mul_sub]
end FixedExtension
end
end ProximityPrize.SubmissionLower.RCN356
end PackedLegacy_G2

/-! Packed from ProximityPrize.SubmissionLower.W3. -/
section PackedLegacy_W3
namespace ProximityPrize.SubmissionLower.RCN357
open scoped BigOperators Classical
open IsDedekindDomain
noncomputable section
section OneRing
variable (A F:Type*) [CommRing A] [IsDedekindDomain A] [Field F]
 [Algebra A F] [IsFractionRing A F]
def fieldOrder (v:HeightOneSpectrum A) (x:F):ℤ:=
 -(v.valuation F x).log
theorem valuation_transport (v:HeightOneSpectrum A) (x:F):
   v.valuation F x=v.valuation (FractionRing A)
     ((FractionRing.algEquiv A F).symm x):=by
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=A) x
 simp only [map_div₀,AlgEquiv.commutes,
   HeightOneSpectrum.valuation_of_algebraMap]
theorem fieldOrder_transport (v:HeightOneSpectrum A) (x:F):
   fieldOrder A F v x=RCN356.orderAt v
     ((FractionRing.algEquiv A F).symm x):=by
 rw [fieldOrder,valuation_transport]
 rfl
end OneRing
section TwoRings
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
def placeAbove (v:HeightOneSpectrum R)
   (P:{P:Ideal S//P∈IsDedekindDomain.primesOverFinset v.asIdeal S}):
   HeightOneSpectrum S:=
 ⟨P.1,((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2).1,
   Ideal.ne_bot_of_mem_primesOver v.ne_bot
     ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2)⟩
variable (F L:Type*) [Field F] [Field L]
 [Algebra R F] [IsFractionRing R F]
 [Algebra S L] [IsFractionRing S L]
 [Algebra F L] [Algebra R L]
 [IsScalarTower R F L] [IsScalarTower R S L]
theorem norm_transport (x:L):
   Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
     (FractionRing.algEquiv R F).symm (Algebra.norm F x):=by
 have h:=Algebra.norm_eq_of_equiv_equiv
   (FractionRing.algEquiv R F).toRingEquiv
   (FractionRing.algEquiv S L).toRingEquiv
   (by
     ext y
     exact IsFractionRing.algEquiv_commutes
       (FractionRing.algEquiv R F) (FractionRing.algEquiv S L) y)
   ((FractionRing.algEquiv S L).symm x)
 change Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
   (FractionRing.algEquiv R F).symm
     (Algebra.norm F ((FractionRing.algEquiv S L)
       ((FractionRing.algEquiv S L).symm x))) at h
 simpa only [AlgEquiv.apply_symm_apply] using h
variable [Algebra.IsSeparable F L]
include F L in
theorem canonical_separable:
   Algebra.IsSeparable (FractionRing R) (FractionRing S):=by
 apply Algebra.IsSeparable.of_equiv_equiv
   (A₁:=F) (B₁:=L) (A₂:=FractionRing R) (B₂:=FractionRing S)
   (FractionRing.algEquiv R F).symm.toRingEquiv
   (FractionRing.algEquiv S L).symm.toRingEquiv
 ext y
 exact IsFractionRing.algEquiv_commutes
   (FractionRing.algEquiv R F).symm (FractionRing.algEquiv S L).symm y
theorem fieldOrder_norm (v:HeightOneSpectrum R) (x:L) (hx:x≠0):
   fieldOrder R F v (Algebra.norm F x)=
     ∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*fieldOrder S L (placeAbove R S v P) x:=by
 letI:Algebra.IsSeparable (FractionRing R) (FractionRing S):=
   canonical_separable R S F L
 have h:=RCN356.orderAt_fieldNorm R S v
   ((FractionRing.algEquiv S L).symm x) (by simpa using hx)
 calc
   fieldOrder R F v (Algebra.norm F x)=
       RCN356.orderAt v
         ((FractionRing.algEquiv R F).symm (Algebra.norm F x)):=
     fieldOrder_transport R F v (Algebra.norm F x)
   _=∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*RCN356.orderAt (placeAbove R S v P)
         ((FractionRing.algEquiv S L).symm x):=by
     simpa only [norm_transport R S F L x,RCN356.primeFiber,
       RCN356.fiberPlace,placeAbove] using h
   _=_:=by
     apply Finset.sum_congr rfl
     intro P _
     congr 1
     exact (fieldOrder_transport S L (placeAbove R S v P) x).symm
end TwoRings
end
end ProximityPrize.SubmissionLower.RCN357
end PackedLegacy_W3

/-! Packed from ProximityPrize.SubmissionLower.W8. -/
section PackedLegacy_W8
namespace ProximityPrize.SubmissionLower.RCN366
open scoped BigOperators Classical
open UniqueFactorizationMonoid IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
def primePlace (p:Polynomial K) (hp:Irreducible p):
   HeightOneSpectrum (Polynomial K):=
 ⟨Ideal.span {p},(Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime,
   by simpa using hp.ne_zero⟩
def asFraction (x:RatFunc K):FractionRing (Polynomial K):=
 RatFunc.toFractionRingAlgEquiv K (Polynomial K) x
def finiteOrder (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):ℤ:=
 RCN356.orderAt (primePlace K p hp) (asFraction K x)
def infinityOrder (x:RatFunc K):ℤ:=
 -(RatFunc.inftyValuation K x).log
theorem finiteOrder_eq_factorCounts
   (p:Polynomial K) (hp:Irreducible p) (hmonic:p.Monic)
   (x:RatFunc K) (hx:x≠0):
   finiteOrder K p hp x=
     ((normalizedFactors x.num).count p:ℤ)-
       ((normalizedFactors x.denom).count p:ℤ):=by
 classical
 have hrepr:asFraction K x=
     algebraMap (Polynomial K) (FractionRing (Polynomial K)) x.num/
       algebraMap (Polynomial K) (FractionRing (Polynomial K)) x.denom:=by
   have h:=congrArg (RatFunc.toFractionRingAlgEquiv K (Polynomial K))
     (RatFunc.num_div_denom x)
   simpa only [asFraction,map_div₀,AlgEquiv.commutes] using h.symm
 rw [finiteOrder,hrepr,
   RCN356.orderAt_div _ _ _ (by simp [RatFunc.num_ne_zero hx])
     (by simp [x.denom_ne_zero]),
   RCN356.orderAt_algebraMap _ x.num (RatFunc.num_ne_zero hx),
   RCN356.orderAt_algebraMap _ x.denom x.denom_ne_zero]
 change ((normalizedFactors (Ideal.span {x.num})).count (Ideal.span {p}):ℤ)-
     ((normalizedFactors (Ideal.span {x.denom})).count (Ideal.span {p}):ℤ)=_
 rw [Ideal.count_span_normalizedFactors_eq (RatFunc.num_ne_zero hx) hp.prime,
   Ideal.count_span_normalizedFactors_eq x.denom_ne_zero hp.prime,
   hmonic.normalize_eq_self]
theorem infinityOrder_eq_neg_intDegree (x:RatFunc K) (hx:x≠0):
   infinityOrder K x= -x.intDegree:=by
 rw [infinityOrder,RatFunc.inftyValuation_apply,
   RatFunc.inftyValuation_of_nonzero K hx,WithZero.log_exp]
theorem exists_monic_primePlace (v:HeightOneSpectrum (Polynomial K)):
   ∃ p:Polynomial K,∃ hp:Irreducible p,
     p.Monic∧primePlace K p hp=v:=by
 classical
 let g:=Submodule.IsPrincipal.generator v.asIdeal
 have hg:Prime g:=Ideal.prime_generator_of_prime v.prime
 have hp:Irreducible (normalize g):=
   (normalize_associated g).irreducible_iff.mpr hg.irreducible
 refine ⟨normalize g,hp,
   Polynomial.monic_normalize (R:=K) (p:=g) hg.ne_zero,?_⟩
 apply HeightOneSpectrum.ext_iff.mpr
 change Ideal.span {normalize g}=v.asIdeal
 calc
   _=Ideal.span {g}:=
     Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated g)
   _=_:=Ideal.span_singleton_generator v.asIdeal
theorem primePlace_injective
   (p q:Polynomial K) (hp:Irreducible p) (hq:Irreducible q)
   (hpm:p.Monic) (hqm:q.Monic)
   (h:primePlace K p hp=primePlace K q hq):p=q:=by
 have hassoc:Associated p q:=Ideal.span_singleton_eq_span_singleton.mp
   (congrArg HeightOneSpectrum.asIdeal h)
 exact hassoc.eq_of_normalized hpm.normalize_eq_self hqm.normalize_eq_self
theorem sum_factor_degrees (p:Polynomial K) (hp:p≠0):
   ((normalizedFactors p).map Polynomial.natDegree).sum=p.natDegree:=by
 have h:=Polynomial.natDegree_eq_of_degree_eq <|
   Polynomial.degree_eq_degree_of_associated (prod_normalizedFactors hp)
 rw [Polynomial.natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)] at h
 exact h
theorem sum_factorCounts_mul_degree
   (p:Polynomial K) (hp:p≠0) (s:Finset (Polynomial K))
   (hs:(normalizedFactors p).toFinset ⊆ s):
   ∑ q∈s,q.natDegree*(normalizedFactors p).count q=p.natDegree:=by
 classical
 have h:=sum_factor_degrees K p hp
 rw [Finset.sum_multiset_map_count] at h
 simp only [nsmul_eq_mul] at h
 norm_cast at h
 have hsum:
     (∑ q∈(normalizedFactors p).toFinset,
       (normalizedFactors p).count q*q.natDegree)=
     ∑ q∈s,(normalizedFactors p).count q*q.natDegree:=by
   apply Finset.sum_subset hs
   intro q _ hq
   have hc:(normalizedFactors p).count q=0:=
     Multiset.count_eq_zero.mpr (by simpa using hq)
   simp [hc]
 rw [hsum] at h
 simpa only [Nat.mul_comm] using h
def factorSupport (x:RatFunc K):Finset (Polynomial K):=by
 classical
 exact (normalizedFactors x.num).toFinset ∪ (normalizedFactors x.denom).toFinset
theorem factorSupport_primes (x:RatFunc K) (hx:x≠0)
   (p:Polynomial K) (hp:p∈factorSupport K x):Irreducible p∧p.Monic:=by
 classical
 rcases Finset.mem_union.mp hp with hnum | hden
 · have h:=(Polynomial.mem_normalizedFactors_iff
     (R:=K) (p:=p) (q:=x.num) (RatFunc.num_ne_zero hx)).mp
     (Multiset.mem_toFinset.mp hnum)
   exact ⟨h.1,h.2.1⟩
 · have h:=(Polynomial.mem_normalizedFactors_iff
     (R:=K) (p:=p) (q:=x.denom) x.denom_ne_zero).mp
     (Multiset.mem_toFinset.mp hden)
   exact ⟨h.1,h.2.1⟩
theorem finiteOrder_eq_zero_of_not_mem
   (p:Polynomial K) (hp:Irreducible p) (hmonic:p.Monic)
   (x:RatFunc K) (hx:x≠0) (hout:p∉factorSupport K x):
   finiteOrder K p hp x=0:=by
 classical
 have hn:p∉normalizedFactors x.num:=by
   intro h
   exact hout (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr h))
 have hd:p∉normalizedFactors x.denom:=by
   intro h
   exact hout (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr h))
 rw [finiteOrder_eq_factorCounts K p hp hmonic x hx,
   Multiset.count_eq_zero.mpr hn,Multiset.count_eq_zero.mpr hd]
 simp
theorem nonzero_order_has_supported_representative
   (x:RatFunc K) (hx:x≠0) (v:HeightOneSpectrum (Polynomial K))
   (hv:RCN356.orderAt v (asFraction K x)≠0):
   ∃ p∈factorSupport K x,∃ hp:Irreducible p,
     p.Monic∧primePlace K p hp=v:=by
 obtain ⟨p,hp,hm,hplace⟩:=exists_monic_primePlace K v
 refine ⟨p,?_,hp,hm,hplace⟩
 by_contra hout
 have hzero:=finiteOrder_eq_zero_of_not_mem K p hp hm x hx hout
 exact hv (by simpa [finiteOrder,hplace] using hzero)
theorem finite_support_actual_orders (x:RatFunc K) (hx:x≠0):
   Function.HasFiniteSupport
     (fun v:HeightOneSpectrum (Polynomial K)↦
       RCN356.orderAt v (asFraction K x)):=by
 classical
 let f:{p:Polynomial K//p∈factorSupport K x} →
     HeightOneSpectrum (Polynomial K):=fun p↦
   primePlace K p.1 (factorSupport_primes K x hx p.1 p.2).1
 apply (Set.finite_range f).subset
 intro v hv
 obtain ⟨p,hmem,hp,_,hplace⟩:=
   nonzero_order_has_supported_representative K x hx v hv
 exact ⟨⟨p,hmem⟩,hplace⟩
theorem weighted_finite_order_sum
   (x:RatFunc K) (hx:x≠0) (s:Finset (Polynomial K))
   (hs:∀ p∈s,Irreducible p∧p.Monic)
   (hnum:(normalizedFactors x.num).toFinset ⊆ s)
   (hden:(normalizedFactors x.denom).toFinset ⊆ s):
   (∑ p∈s.attach,(p.1.natDegree:ℤ)*
     finiteOrder K p.1 (hs p.1 p.2).1 x)=x.intDegree:=by
 classical
 have hterms:
     (∑ p∈s.attach,(p.1.natDegree:ℤ)*
       finiteOrder K p.1 (hs p.1 p.2).1 x)=
     ∑ p∈s,(p.natDegree:ℤ)*
       (((normalizedFactors x.num).count p:ℤ)-
         ((normalizedFactors x.denom).count p:ℤ)):=by
   calc
     _=∑ p∈s.attach,(p.1.natDegree:ℤ)*
         (((normalizedFactors x.num).count p.1:ℤ)-
           ((normalizedFactors x.denom).count p.1:ℤ)):=by
       apply Finset.sum_congr rfl
       intro p _
       rw [finiteOrder_eq_factorCounts K p.1 (hs p.1 p.2).1 (hs p.1 p.2).2 x hx]
     _=_:=Finset.sum_attach s (fun p:Polynomial K↦
       (p.natDegree:ℤ)*
         (((normalizedFactors x.num).count p:ℤ)-
           ((normalizedFactors x.denom).count p:ℤ)))
 rw [hterms]
 simp only [mul_sub,Finset.sum_sub_distrib]
 have hn:(∑ p∈s,(p.natDegree:ℤ)*
     ((normalizedFactors x.num).count p:ℤ))=(x.num.natDegree:ℤ):=by
   exact_mod_cast sum_factorCounts_mul_degree K x.num (RatFunc.num_ne_zero hx) s hnum
 have hd:(∑ p∈s,(p.natDegree:ℤ)*
     ((normalizedFactors x.denom).count p:ℤ))=(x.denom.natDegree:ℤ):=by
   exact_mod_cast sum_factorCounts_mul_degree K x.denom x.denom_ne_zero s hden
 rw [hn,hd]
 rfl
theorem projective_line_order_sum (x:RatFunc K) (hx:x≠0):
   (∑ p∈(factorSupport K x).attach,(p.1.natDegree:ℤ)*
     finiteOrder K p.1 (factorSupport_primes K x hx p.1 p.2).1 x)+
     infinityOrder K x=0:=by
 classical
 rw [weighted_finite_order_sum K x hx (factorSupport K x)
   (factorSupport_primes K x hx)
   Finset.subset_union_left Finset.subset_union_right,
   infinityOrder_eq_neg_intDegree K x hx,add_neg_cancel]
end
end ProximityPrize.SubmissionLower.RCN366
end PackedLegacy_W8

/-! Packed from ProximityPrize.SubmissionLower.HW. -/
section PackedLegacy_HW
variable {K:Type*} [Field K]
namespace RatFunc
open IntermediateField algebraAdjoinAdjoin Polynomial Algebra
section
variable (f:K⟮X⟯)
theorem adjoin_X:K⟮(RatFunc.X:K⟮X⟯)⟯=⊤:=
 eq_top_iff.mpr fun g _↦(mem_adjoin_simple_iff _ _).mpr ⟨g.num,g.denom,by simp⟩
theorem IntermediateField.adjoin_X (E:IntermediateField K K⟮X⟯):
   E⟮(RatFunc.X:K⟮X⟯)⟯=⊤:=by
 rw [←restrictScalars_eq_top_iff (K:=K),IntermediateField.restrictScalars_adjoin,
   _root_.eq_top_iff]
 exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))
noncomputable def IntermediateField.adjoinXEquiv (E:IntermediateField K K⟮X⟯):
   E⟮(RatFunc.X:K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯:=
 (equivOfEq (adjoin_X E)).trans topEquiv
noncomputable abbrev minpolyX (A:Type*) [CommRing A] [Algebra K A] [Algebra K[f] A]:A[X]:=
 f.num.map (algebraMap K A)-
 Polynomial.C (algebraMap K[f] A (⟨f,self_mem_adjoin_singleton K f⟩:K[f]))*
   f.denom.map (algebraMap K A)
theorem minpolyX_map (A:Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
   (B:Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
   [IsScalarTower K[f] A B]:(f.minpolyX A).map (algebraMap A B)=f.minpolyX B:=by
 simp [minpolyX,Polynomial.map_map, ←IsScalarTower.algebraMap_eq,
   ←IsScalarTower.algebraMap_apply]
@[simp]
theorem C_minpolyX (x:K):(C x).minpolyX K⟮C x⟯=0:=by
 simp [minpolyX,sub_eq_zero,Subtype.ext_iff]
theorem minpolyX_aeval_X:(f.minpolyX K⟮f⟯).aeval (RatFunc.X:K⟮X⟯)=0:=by
 simp only [aeval_sub,aeval_map_algebraMap,aeval_X_left_eq_algebraMap,map_mul,aeval_C,
   IntermediateField.algebraMap_apply,coe_algebraMap]
 nth_rw 2 [←num_div_denom f]
 rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
 exact sub_self _
theorem eq_C_of_minpolyX_coeff_eq_zero
 (hf:(f.minpolyX K⟮f⟯).coeff f.denom.natDegree=(0:K⟮X⟯)):∃ c,f=C c:=by
 use f.num.coeff f.denom.natDegree/f.denom.leadingCoeff
 rw [map_div₀,eq_div_iff ((_root_.map_ne_zero C).mpr
   (leadingCoeff_ne_zero.mpr f.denom_ne_zero)),eq_comm]
 simpa [sub_eq_zero] using hf
theorem minpolyX_eq_zero_iff:(f.minpolyX K⟮f⟯)=0 ↔ ∃ c,f=C c:=
 ⟨fun h↦f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]),by rintro ⟨c,rfl⟩;simp⟩
theorem isAlgebraic_adjoin_simple_X (hf:¬∃ c,f=C c):
   IsAlgebraic K⟮f⟯ (RatFunc.X:K⟮X⟯):=
 ⟨f.minpolyX K⟮f⟯,fun H↦hf (f.minpolyX_eq_zero_iff.mp H),f.minpolyX_aeval_X⟩
theorem isAlgebraic_adjoin_simple_X' (hf:¬∃ c,f=C c):
   Algebra.IsAlgebraic K⟮f⟯ K⟮X⟯:=by
 have:Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(RatFunc.X:K⟮X⟯)⟯:=
   isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
 exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic
theorem natDegree_denom_le_natDegree_minpolyX (hf:¬∃ c,f=C c):
   f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree:=
 le_natDegree_of_ne_zero fun H↦hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))
set_option backward.isDefEq.respectTransparency false in
theorem natDegree_num_le_natDegree_minpolyX (hf:¬∃ c,f=C c):
   f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree:=by
 have f_ne_zero:f≠0:=by
   rintro rfl
   exact hf ⟨0,(RingHom.map_zero C).symm⟩
 apply le_natDegree_of_ne_zero
 intro H
 replace H :=congr($(H).val)
 simp only [coeff_sub,coeff_map,coeff_natDegree,coeff_C_mul,AddSubgroupClass.coe_sub,
   SubalgebraClass.coe_algebraMap,algebraMap_eq_C,MulMemClass.coe_mul,coe_algebraMap,
   ZeroMemClass.coe_zero] at H
 rw [sub_eq_zero, ←mul_right_inj' (inv_ne_zero f_ne_zero), ←mul_assoc,inv_mul_cancel₀ f_ne_zero,
   one_mul, ←eq_div_iff <| (_root_.map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
   (num_ne_zero f_ne_zero), ←inv_inj,inv_inv, ←map_div₀, ←map_inv₀] at H
 exact hf ⟨_,H⟩
theorem natDegree_minpolyX:
   (f.minpolyX K⟮f⟯).natDegree=max f.num.natDegree f.denom.natDegree:=by
 by_cases hf:∃ c,f=C c
 · obtain ⟨c,rfl⟩:=hf
   simp
 apply le_antisymm
 · have:(f.minpolyX K⟮f⟯).natDegree ≤ _:=natDegree_sub_le _ _
   rw [natDegree_map,natDegree_C_mul fun H↦hf ⟨0,by simpa [map_zero] using congr($(H).val)⟩,
     natDegree_map] at this
   exact this
 · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| le_natDegree_of_ne_zero
     fun H↦hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))
theorem transcendental_of_ne_C (hf:¬∃ c,f=C c):Transcendental K f:=by
 intro H
 have:=isAlgebraic_adjoin_simple H.isIntegral
 have tr:Algebra.Transcendental K K⟮X⟯:=by infer_instance
 rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
 exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg:=f.isAlgebraic_adjoin_simple_X' hf)
theorem irreducible_minpolyX' (hf:¬∃ c,f=C c):Irreducible (f.minpolyX K[f]):=by
 let e:=Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
 let φ:K[X][X]:=f.num.map (algebraMap ..)-
   Polynomial.C Polynomial.X*f.denom.map (algebraMap ..)
 have φ_map:φ.mapEquiv e.toRingEquiv=(f.minpolyX K[f]):=by
   simp only [algebraMap_eq,map_sub,mapEquiv_apply,
     AlgEquiv.toRingEquiv_toRingHom,algEquivOfTranscendental_coe,Polynomial.map_map,map_mul,
     map_C,RingHom.coe_coe,aeval_X,e,φ]
   congr 2 <;> ext <;> simp
 rw [←φ_map,MulEquiv.irreducible_iff]
 have:φ=Bivariate.swap
     (Polynomial.C f.num-Polynomial.X*Polynomial.C f.denom):=by
   simp only [map_sub,map_mul,Bivariate.swap_C,Bivariate.swap_Y]
   rfl
 rw [this,MulEquiv.irreducible_iff]
 convert!
   irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
     ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
 rw [add_comm,X_mul_C,map_neg,neg_mul]
 exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom*Polynomial.X)
theorem irreducible_minpolyX (hf:¬∃ c,f=C c):Irreducible (f.minpolyX K⟮f⟯):=by
 haveI:UniqueFactorizationMonoid K[f]:=
   (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
 rw [←f.minpolyX_map K[f] K⟮f⟯,
   ←IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
 · exact f.irreducible_minpolyX' hf
 · apply (f.irreducible_minpolyX' hf).isPrimitive
   intro H
   have:=natDegree_map_le (f:=algebraMap K[f] K⟮f⟯) (p:=f.minpolyX K[f])
   rw [f.minpolyX_map K[f] K⟮f⟯,H,nonpos_iff_eq_zero,f.natDegree_minpolyX,
     Nat.max_eq_zero_iff, ←f.eq_C_iff] at this
   exact hf this
theorem finrank_eq_max_natDegree:
   Module.finrank K⟮f⟯ K⟮X⟯=max f.num.natDegree f.denom.natDegree:=by
 by_cases hf:∃ c,f=C c
 · obtain ⟨c,rfl⟩:=hf
   rw [adjoin_simple_eq_bot_iff.mpr (show C c∈⊥ from ⟨c,rfl⟩),finrank_bot',
     Module.finrank_of_not_finite fun H↦Algebra.transcendental_iff_not_isAlgebraic.mp
     transcendental <| Algebra.IsAlgebraic.of_finite K K⟮X⟯]
   simp
 rw [←(IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
   adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
   ←minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X,mul_comm,
   natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H↦
   hf ((minpolyX_eq_zero_iff f).mp H),natDegree_minpolyX]
theorem IntermediateField.isAlgebraic_X {E:IntermediateField K K⟮X⟯} (hE:E≠⊥):
   IsAlgebraic E (RatFunc.X:K⟮X⟯):=by
 rw [ne_eq, ←le_bot_iff,SetLike.not_le_iff_exists] at hE
 obtain ⟨f,hf₁,hf₂⟩:=hE
 exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
   f.isAlgebraic_adjoin_simple_X (by rintro ⟨c,rfl⟩;exact hf₂ ⟨c,rfl⟩)
end
end RatFunc
end PackedLegacy_HW

/-! Packed from ProximityPrize.SubmissionLower.S7. -/
section PackedLegacy_S7
noncomputable section
namespace Polynomial.Bivariate
open Polynomial Bivariate Algebra Transcendental
variable {R A:Type*} [CommRing R]
section Ring
variable [Ring A] [Algebra R A] {x:A}
def Transcendental.algEquivAdjoin (hx:Transcendental R x):
   R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X]:=
 mapAlgEquiv (algEquivOfTranscendental _ x hx)
theorem Transcendental.algEquivAdjoin_apply (hx:Transcendental R x) (p:R[X][Y]):
   hx.algEquivAdjoin p=mapAlgHom (aeval ⟨x,self_mem_adjoin_singleton R x⟩) p:=
 rfl
attribute [local instance] algebra in
theorem Transcendental.algEquivAdjoin_swap_eq_aeval (hx:Transcendental R x) (p:R[X][Y]):
   hx.algEquivAdjoin (swap p)=aeval (C ⟨x,self_mem_adjoin_singleton R x⟩) p:=by
 simp [algEquivAdjoin,Bivariate.aveal_eq_map_swap]
end Ring
section CommRing
variable [CommRing A] [Algebra R A]
 {B:Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
attribute [local instance] Polynomial.algebra in
theorem aeval_aeval_eq_aeval_algEquivAdjoin {x:A} (y:B)
   (hx:Transcendental R x) (p:R[X][Y]):
   aeval (algebraMap A B x) (aeval (C (⟨y,self_mem_adjoin_singleton R y⟩:
     adjoin R {y})) p)=aeval y (hx.algEquivAdjoin p):=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => simp_all [map_add]
 | monomial n a =>
   simp_all [aeval_algebraMap_apply,Transcendental.algEquivAdjoin,Subalgebra.algebraMap_def]
theorem _root_.IsAlgebraic.adjoin_singleton {x:A} {y:B} (hx:Transcendental R x)
   (hy:Transcendental R y) (h:IsAlgebraic (adjoin R {x}) y):
   IsAlgebraic (adjoin R {y}) (algebraMap A B x):=by
 obtain ⟨f,hnezero,halg⟩:=h
 refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
   by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)],?_⟩
 simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy,aeval_aeval_eq_aeval_algEquivAdjoin y hx]
end CommRing
end Polynomial.Bivariate
end
end PackedLegacy_S7

/-! Packed from ProximityPrize.SubmissionLower.AQ. -/
section PackedLegacy_AQ
section ProximityFlatProofPort
noncomputable section
open scoped nonZeroDivisors Polynomial WithZero RatFunc
variable (F K:Type*) [Field F] [Field K]
abbrev FunctionField [Algebra F⟮X⟯ K]:Prop:=
 FiniteDimensional F⟮X⟯ K
theorem functionField_iff (Ft:Type*) [Field Ft] [Algebra F[X] Ft]
   [IsFractionRing F[X] Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra F[X] K]
   [IsScalarTower F[X] Ft K] [IsScalarTower F[X] F⟮X⟯ K]:
   FunctionField F K ↔ FiniteDimensional Ft K:=by
 let e:=IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
 have:∀ (c) (x:K),e c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   congr
   refine congr_fun (f:=fun c => algebraMap Ft K (e c)) ?_ c
   refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
     simp only [map_one,map_mul,AlgEquiv.commutes, ←IsScalarTower.algebraMap_apply]
 constructor <;> intro h
 · let b:=Module.finBasis F⟮X⟯ K
   exact (b.mapCoeffs e this).finiteDimensional_of_finite
 · let b:=Module.finBasis Ft K
   refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
   intro c x;convert! (this (e.symm c) x).symm;simp only [e.apply_symm_apply]
namespace FunctionField
theorem algebraMap_injective [Algebra F[X] K] [Algebra F⟮X⟯ K]
   [IsScalarTower F[X] F⟮X⟯ K]:Function.Injective (algebraMap F[X] K):=by
 rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
 exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
def ringOfIntegers [Algebra F[X] K]:=
 integralClosure F[X] K
namespace ringOfIntegers
variable [Algebra F[X] K]
instance:IsDomain (ringOfIntegers F K):=
 (ringOfIntegers F K).isDomain
instance:IsIntegralClosure (ringOfIntegers F K) F[X] K:=
 integralClosure.isIntegralClosure _ _
variable [Algebra F⟮X⟯ K] [IsScalarTower F[X] F⟮X⟯ K]
theorem algebraMap_injective:Function.Injective (algebraMap F[X] (ringOfIntegers F K)):=by
 have hinj:Function.Injective (algebraMap F[X] K):=by
   rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
   exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
 rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
 intro p hp
 rw [←Subtype.coe_inj,Subalgebra.coe_zero] at hp
 rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
 exact hinj p hp
theorem not_isField:¬IsField (ringOfIntegers F K):=by
 simpa [←(IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
     (algebraMap_injective F K)] using
   Polynomial.not_isField F
variable [FunctionField F K]
instance:IsFractionRing (ringOfIntegers F K) K:=
 integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K
instance:IsIntegrallyClosed (ringOfIntegers F K):=
 integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯
instance [Algebra.IsSeparable F⟮X⟯ K]:IsNoetherian F[X] (ringOfIntegers F K):=
 IsIntegralClosure.isNoetherian _ F⟮X⟯ K _
instance [Algebra.IsSeparable F⟮X⟯ K]:IsDedekindDomain (ringOfIntegers F K):=
 IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _
end ringOfIntegers
section deprecated
@[deprecated RatFunc.inftyValuationDef (since:="2026-04-14")]
alias inftyValuationDef:=RatFunc.inftyValuationDef
@[deprecated RatFunc.InftyValuation.map_zero' (since:="2026-04-14")]
alias InftyValuation.map_zero':=RatFunc.InftyValuation.map_zero'
@[deprecated RatFunc.InftyValuation.map_one' (since:="2026-04-14")]
alias InftyValuation.map_one':=RatFunc.InftyValuation.map_one'
@[deprecated RatFunc.InftyValuation.map_mul' (since:="2026-04-14")]
alias InftyValuation.map_mul':=RatFunc.InftyValuation.map_mul'
@[deprecated RatFunc.InftyValuation.map_add_le_max' (since:="2026-04-14")]
alias InftyValuation.map_add_le_max':=RatFunc.InftyValuation.map_add_le_max'
@[deprecated RatFunc.inftyValuation_of_nonzero (since:="2026-04-14")]
alias inftyValuation_of_nonzero:=RatFunc.inftyValuation_of_nonzero
@[deprecated RatFunc.inftyValuation (since:="2026-04-14")]
alias inftyValuation:=RatFunc.inftyValuation
@[deprecated RatFunc.inftyValuation_apply (since:="2026-04-14")]
alias inftyValuation_apply:=RatFunc.inftyValuation_apply
@[deprecated RatFunc.inftyValuation.C (since:="2026-04-14")]
alias inftyValuation.C:=RatFunc.inftyValuation.C
@[deprecated RatFunc.inftyValuation.X (since:="2026-04-14")]
alias inftyValuation.X:=RatFunc.inftyValuation.X
@[deprecated RatFunc.inftyValuation.X_zpow (since:="2026-04-14")]
alias inftyValuation.X_zpow:=RatFunc.inftyValuation.X_zpow
@[deprecated RatFunc.inftyValuation.X_inv (since:="2026-04-14")]
alias inftyValuation.X_inv:=RatFunc.inftyValuation.X_inv
@[deprecated RatFunc.inftyValuation.polynomial (since:="2026-04-14")]
alias inftyValuation.polynomial:=RatFunc.inftyValuation.polynomial
@[deprecated RatFunc.inftyValued (since:="2026-04-14")]
alias inftyValuedFqt:=RatFunc.inftyValued
@[deprecated RatFunc.inftyValued.def (since:="2026-04-14")]
alias inftyValuedFqt.def:=RatFunc.inftyValued.def
@[deprecated RatFunc.CompletionAtInfty (since:="2026-04-14")]
alias FqtInfty:=RatFunc.CompletionAtInfty
@[deprecated "Use the anonymous `Valued` instance on `RatFunc.CompletionAtInfty`"
(since:="2026-04-14")]
instance valuedFqtInfty [DecidableEq F⟮X⟯]:
   Valued (RatFunc.CompletionAtInfty F) ℤᵐ⁰:=
 inferInstance
@[deprecated RatFunc.valuedCompletionAtInfty.def (since:="2026-04-14")]
alias valuedFqtInfty.def:=RatFunc.valuedCompletionAtInfty.def
end deprecated
section AdjoinTranscendental
open IntermediateField RatFunc
variable {F K:Type*} [Field F] [Field K] [Algebra F⟮X⟯ K] [FunctionField F K]
instance FiniteDimensional.adjoin_X:FiniteDimensional F⟮(RatFunc.X:F⟮X⟯)⟯ K:=
 have:Module.Finite (⊤:IntermediateField F F⟮X⟯) F⟮X⟯:=
   .top_left F⟮X⟯ F⟮X⟯
 RatFunc.adjoin_X (K:=F) ▸ Module.Finite.trans F⟮X⟯ _
variable [Algebra F K] [IsScalarTower F F⟮X⟯ K]
theorem FiniteDimensional.adjoin_algebraMap_X:
   FiniteDimensional F⟮algebraMap _ K (RatFunc.X:F⟮X⟯)⟯ K:=
 .of_restrictScalars_finite F⟮(RatFunc.X:F⟮X⟯)⟯ _ _
theorem Algebra.IsAlgebraic.adjoin_algebraMap_X:
   Algebra.IsAlgebraic F⟮algebraMap _ K (RatFunc.X:F⟮X⟯)⟯ K:=by
 exact .tower_top (K:=F⟮(RatFunc.X:F⟮X⟯)⟯) _
variable {y:K}
theorem isAlgebraic_X_over_adjoin_transcendental (hy:Transcendental F y):
   IsAlgebraic F⟮y⟯ (algebraMap _ K (RatFunc.X:F⟮X⟯)):=
 isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
   (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))
lemma finiteDimensional_of_adjoin_transcendental (hy:Transcendental F y):
   FiniteDimensional F⟮y⟯ K:=
 let x:=algebraMap _ K (RatFunc.X:F⟮X⟯)
 let Fyx:=restrictScalars F F⟮y⟯⟮x⟯
 let Fxy:=restrictScalars F F⟮x⟯⟮y⟯
 let:Algebra F⟮y⟯ Fyx:=F⟮y⟯⟮x⟯.algebra
 let:Module F⟮y⟯ Fyx:=Algebra.toModule
 let:SMul F⟮y⟯ Fyx:=Algebra.toSMul
 let:Algebra F⟮x⟯ Fxy:=F⟮x⟯⟮y⟯.algebra
 let:Module F⟮x⟯ Fxy:=Algebra.toModule
 let:SMul F⟮x⟯ Fxy:=Algebra.toSMul
 have:FiniteDimensional F⟮y⟯ Fyx:=
   adjoin.finiteDimensional
     (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
 have:FiniteDimensional Fyx K:=by
   have:=FiniteDimensional.adjoin_algebraMap_X (F:=F) (K:=K)
   unfold Fyx
   rw [adjoin_simple_comm]
   have:IsScalarTower F⟮x⟯ Fxy K:=isScalarTower_mid' F⟮x⟯⟮y⟯
   exact .right F⟮x⟯ Fxy K
 have:IsScalarTower F⟮y⟯ Fyx K:=isScalarTower_mid' F⟮y⟯⟮x⟯
 .trans F⟮y⟯ Fyx K
end AdjoinTranscendental
section constantExtension
open RatFunc
variable {F}
 [Algebra F[X] K] [FaithfulSMul F[X] K] [FunctionField F K]
attribute [local instance] Polynomial.algebra
section Unbundled
open Polynomial
variable {E:Type*} [Field E] [Algebra F E] [Algebra E[X] K] [FaithfulSMul E[X] K]
theorem finiteDimensional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K]:
   FiniteDimensional F⟮X⟯ E⟮X⟯:=
 .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm
theorem finiteDimensional_of_constantExtension [IsScalarTower F[X] E[X] K]
   [Algebra.IsAlgebraic F E]:FiniteDimensional F E:=
 have:=finiteDimensional_ratFunc_of_constantExtension (F:=F) (E:=E) K
 Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)
end Unbundled
section IntermediateField
variable [Algebra F K] (E:IntermediateField F K) [Algebra E[X] K] [FaithfulSMul E[X] K]
 [IsScalarTower F[X] E[X] K]
instance:FiniteDimensional F⟮X⟯ E⟮X⟯:=
 finiteDimensional_ratFunc_of_constantExtension K
instance [Algebra.IsAlgebraic F E]:FiniteDimensional F E:=
 finiteDimensional_of_constantExtension K
end IntermediateField
end constantExtension
end FunctionField
end
end ProximityFlatProofPort
end PackedLegacy_AQ

/-! Packed from ProximityPrize.SubmissionLower.R5. -/
section PackedLegacy_R5
namespace ProximityPrize.SubmissionLower.RCN349
open scoped BigOperators Classical nonZeroDivisors
open IsDedekindDomain RCN357
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
abbrev FiniteNormalization:=FunctionField.ringOfIntegers K L
instance finiteNormalization_finite:
   Module.Finite (Polynomial K) (FiniteNormalization K L):=
 IsIntegralClosure.finite (Polynomial K) (RatFunc K) L (FiniteNormalization K L)
instance finiteNormalization_torsionFree:
   Module.IsTorsionFree (Polynomial K) (FiniteNormalization K L):=by
 letI:Module.IsTorsionFree (Polynomial K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (Polynomial K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (Polynomial K) L
abbrev InfinityBase:=RCN353.InfinityRing K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=integralClosure (InfinityBase K) L
instance infiniteNormalization_finite:
   Module.Finite (InfinityBase K) (InfiniteNormalization K L):=
 IsIntegralClosure.finite (InfinityBase K) (RatFunc K) L (InfiniteNormalization K L)
instance infiniteNormalization_torsionFree:
   Module.IsTorsionFree (InfinityBase K) (InfiniteNormalization K L):=by
 letI:Module.IsTorsionFree (InfinityBase K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (InfinityBase K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (InfinityBase K) L
instance infiniteNormalization_isDedekindDomain:
   IsDedekindDomain (InfiniteNormalization K L):=
 integralClosure.isDedekindDomain (InfinityBase K) (RatFunc K) L
instance infiniteNormalization_isFractionRing:
   IsFractionRing (InfiniteNormalization K L) L:=
 integralClosure.isFractionRing_of_finite_extension (RatFunc K) L
def infinityPlace:HeightOneSpectrum (InfinityBase K):=
 IsDiscreteValuationRing.maximalIdeal (InfinityBase K)
def infinityContribution (x:L):ℤ:=
 ∑ P∈(IsDedekindDomain.primesOverFinset
     (infinityPlace K).asIdeal (InfiniteNormalization K L)).attach,
   (P.1.inertiaDeg (InfinityBase K):ℤ)*
     fieldOrder (InfiniteNormalization K L) L
       (placeAbove (InfinityBase K) (InfiniteNormalization K L) (infinityPlace K) P) x
theorem infinityContribution_eq_normOrder (x:L) (hx:x≠0):
   infinityContribution K L x=
     RCN366.infinityOrder K (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (InfinityBase K) (InfiniteNormalization K L)
   (RatFunc K) L (infinityPlace K) x hx
 change-((infinityPlace K).valuation (RatFunc K)
     (Algebra.norm (RatFunc K) x)).log=infinityContribution K L x at h
 rw [infinityPlace,RCN353.infinity_valuation_eq] at h
 exact h.symm
theorem asFraction_eq_canonical (x:RatFunc K):
   RCN366.asFraction K x=
     (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm x:=by
 letI:Subsingleton
     ((RatFunc K) →ₐ[Polynomial K] FractionRing (Polynomial K)):=
   IsLocalization.algHom_subsingleton (nonZeroDivisors (Polynomial K))
 have h:=Subsingleton.elim
   (RatFunc.toFractionRingAlgEquiv K (Polynomial K)).toAlgHom
   (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm.toAlgHom
 exact DFunLike.congr_fun h x
theorem finiteOrder_eq_specifiedOrder
   (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):
   RCN366.finiteOrder K p hp x=
     fieldOrder (Polynomial K) (RatFunc K) (RCN366.primePlace K p hp) x:=by
 rw [RCN366.finiteOrder,asFraction_eq_canonical K]
 exact (fieldOrder_transport (Polynomial K) (RatFunc K)
   (RCN366.primePlace K p hp) x).symm
theorem finitePrimeContribution_eq_normOrder
   (p:Polynomial K) (hp:Irreducible p) (x:L) (hx:x≠0):
   (∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RCN366.primePlace K p hp) P) x)=
     RCN366.finiteOrder K p hp (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (Polynomial K) (FiniteNormalization K L) (RatFunc K) L
   (RCN366.primePlace K p hp) x hx
 rw [←finiteOrder_eq_specifiedOrder K p hp] at h
 exact h.symm
def finiteContribution (s:Finset (Polynomial K))
   (hs:∀ p∈s,Irreducible p∧p.Monic) (x:L):ℤ:=
 ∑ p∈s.attach,(p.1.natDegree:ℤ)*
   ∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
       (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RCN366.primePlace K p.1 (hs p.1 p.2).1) P) x
theorem finiteContribution_eq_normOrders
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0):
   finiteContribution K L s hs x=
     ∑ p∈s.attach,(p.1.natDegree:ℤ)*
       RCN366.finiteOrder K p.1 (hs p.1 p.2).1
         (Algebra.norm (RatFunc K) x):=by
 unfold finiteContribution
 apply Finset.sum_congr rfl
 intro p _
 rw [finitePrimeContribution_eq_normOrder K L p.1 (hs p.1 p.2).1 x hx]
theorem balanced_fiber_sum
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0)
   (hnum:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).num).toFinset ⊆ s)
   (hden:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).denom).toFinset ⊆ s):
   finiteContribution K L s hs x+infinityContribution K L x=0:=by
 have hnorm:Algebra.norm (RatFunc K) x≠0:=Algebra.norm_ne_zero_iff.mpr hx
 rw [finiteContribution_eq_normOrders K L s hs x hx,
   infinityContribution_eq_normOrder K L x hx,
   RCN366.weighted_finite_order_sum K _ hnorm s hs hnum hden,
   RCN366.infinityOrder_eq_neg_intDegree K _ hnorm,
   add_neg_cancel]
theorem finite_orders_support_finite (x:L) (hx:x≠0):
   Function.HasFiniteSupport
     (fun w:HeightOneSpectrum (FiniteNormalization K L)↦
       fieldOrder (FiniteNormalization K L) L w x):=by
 obtain ⟨a,b,hb,rfl⟩:=
   IsFractionRing.div_surjective (A:=FiniteNormalization K L) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hspanA:(Ideal.span {a}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hazero
 have hspanB:(Ideal.span {b}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hbzero
 have hA:{w:HeightOneSpectrum (FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {a}}.Finite:=Ideal.finite_factors hspanA
 have hB:{w:HeightOneSpectrum (FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {b}}.Finite:=Ideal.finite_factors hspanB
 apply (hA.union hB).subset
 intro w hw
 by_contra hout
 have hn:=not_or.mp hout
 have hna:a∉w.asIdeal:=fun ha↦hn.1 (Ideal.dvd_span_singleton.mpr ha)
 have hnb:b∉w.asIdeal:=fun hb↦hn.2 (Ideal.dvd_span_singleton.mpr hb)
 have hva:w.intValuation a=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hna
 have hvb:w.intValuation b=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hnb
 apply hw
 simp only [fieldOrder,map_div₀,HeightOneSpectrum.valuation_of_algebraMap,
   hva,hvb,div_self one_ne_zero,WithZero.log_one,neg_zero]
def finiteOrderSupport (x:L) (hx:x≠0):
   Finset (HeightOneSpectrum (FiniteNormalization K L)):=
 (finite_orders_support_finite K L x hx).toFinset
theorem mem_finiteOrderSupport (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L)):
   w∈finiteOrderSupport K L x hx ↔
     fieldOrder (FiniteNormalization K L) L w x≠0:=by
 simp [finiteOrderSupport]
def baseRepresentative (w:HeightOneSpectrum (FiniteNormalization K L)):Polynomial K:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose
theorem baseRepresentative_spec (w:HeightOneSpectrum (FiniteNormalization K L)):
   ∃ hp:Irreducible (baseRepresentative K L w),
     (baseRepresentative K L w).Monic∧
       RCN366.primePlace K (baseRepresentative K L w) hp=
         HeightOneSpectrum.under (Polynomial K) w:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose_spec
def basePrimesFor (x:L) (hx:x≠0):Finset (Polynomial K):=
 (finiteOrderSupport K L x hx).image (baseRepresentative K L) ∪
   RCN366.factorSupport K (Algebra.norm (RatFunc K) x)
theorem basePrimesFor_primes (x:L) (hx:x≠0)
   (p:Polynomial K) (hp:p∈basePrimesFor K L x hx):Irreducible p∧p.Monic:=by
 rcases Finset.mem_union.mp hp with hleft | hright
 · obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hleft
   obtain ⟨hp,hm,_⟩:=baseRepresentative_spec K L w
   exact ⟨hp,hm⟩
 · exact RCN366.factorSupport_primes K _
     (Algebra.norm_ne_zero_iff.mpr hx) p hright
theorem basePrimesFor_covers (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L))
   (hw:fieldOrder (FiniteNormalization K L) L w x≠0):
   ∃ p∈basePrimesFor K L x hx,∃ hp:Irreducible p,
     w.asIdeal∈IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (FiniteNormalization K L):=by
 obtain ⟨hp,hm,hplace⟩:=baseRepresentative_spec K L w
 refine ⟨baseRepresentative K L w,
   Finset.mem_union_left _ (Finset.mem_image.mpr
     ⟨w,(mem_finiteOrderSupport K L x hx w).mpr hw,rfl⟩),hp,?_⟩
 rw [hplace]
 letI:w.asIdeal.LiesOver (HeightOneSpectrum.under (Polynomial K) w).asIdeal:=by
   change w.asIdeal.LiesOver (w.asIdeal.under (Polynomial K))
   infer_instance
 exact (IsDedekindDomain.mem_primesOverFinset_iff
   (HeightOneSpectrum.under (Polynomial K) w).ne_bot (FiniteNormalization K L)).mpr
     ⟨w.isPrime,inferInstance⟩
theorem projective_curve_order_sum (x:L) (hx:x≠0):
   finiteContribution K L (basePrimesFor K L x hx)
     (basePrimesFor_primes K L x hx) x+infinityContribution K L x=0:=by
 apply balanced_fiber_sum K L (basePrimesFor K L x hx)
   (basePrimesFor_primes K L x hx) x hx
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_right _ hp)
end
end ProximityPrize.SubmissionLower.RCN349
end PackedLegacy_R5

/-! Packed from ProximityPrize.SubmissionLower.HP. -/
section PackedLegacy_HP
section ProximityFlatProofPort
variable {M:Type*}
 [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
theorem mul_smul_one_lt_iff {num:ℤ} {n den:ℕ} (hn:0 < n) {x:M}:
   (num*n) • 1 < (n*den:ℤ) • x ↔ num • 1 < den • x:=by
 rw [mul_comm num,mul_smul,mul_smul,natCast_zsmul x den]
 exact ⟨fun h↦lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
   fun h↦zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩
theorem num_smul_one_lt_den_smul_add {u v:ℚ} {x y:M}
   (hu:u.num • 1 < u.den • x) (hv:v.num • 1 < v.den • y):
   (u+v).num • 1 < (u+v).den • (x+y):=by
 have hu':(u.num*v.den) • 1 < (u.den*v.den:ℤ) • x:=by
   simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
 suffices ((u+v).num*u.den*v.den) • 1 <
     ((u+v).den:ℤ) • (u.den*v.den:ℤ) • (x+y) by
   refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.den_pos)).mp ?_
   rwa [Nat.cast_mul, ←mul_assoc,mul_comm _ ((u+v).den:ℤ), ←smul_eq_mul ((u+v).den:ℤ),
     smul_assoc]
 rw [Rat.add_num_den',mul_comm, ←smul_smul]
 rw [smul_lt_smul_iff_of_pos_left (by simpa using (u+v).den_pos)]
 rw [add_smul,smul_add]
 exact add_lt_add hu' ((mul_smul_one_lt_iff u.den_pos).mpr hv)
theorem num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1:M)]
   {num:ℤ} {den:ℕ} {x:M} (h:num • 1 ≤ den • x)
   {n:ℤ} (hn:x ≤ n • 1):num ≤ n*den:=by
 refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
 rw [mul_comm, ←smul_smul]
 simpa using nsmul_le_nsmul_right hn den
namespace Archimedean
abbrev ratLt (x:M):Set ℚ:={r | r.num • 1 < r.den • x}
theorem mkRat_mem_ratLt {num:ℤ} {den:ℕ} (hden:den≠0) {x:M}:
   mkRat num den∈ratLt x ↔ num • 1 < den • x:=by
 rw [Set.mem_setOf]
 obtain ⟨m,hm0,hnum,hden⟩:=Rat.mkRat_num_den hden (show mkRat num den=_ by rfl)
 conv in num • 1 => rw [hnum,mul_comm, ←smul_smul,natCast_zsmul]
 conv in den • x => rw [hden,mul_comm, ←smul_smul]
 exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm0)).symm
abbrev ratLt' (x:M):Set ℝ:=(Rat.castHom ℝ) '' (ratLt x)
noncomputable
abbrev embedRealFun (x:M):=sSup (ratLt' x)
variable [ZeroLEOneClass M] [NeZero (1:M)] [Archimedean M]
theorem ratLt_bddAbove (x:M):BddAbove (ratLt x):=by
 obtain ⟨n,hn⟩:=Archimedean.arch x zero_lt_one
 use n
 rw [ratLt,mem_upperBounds]
 intro ⟨num,den,_,_⟩
 rw [Rat.le_iff]
 suffices num • 1 < den • x → num ≤ n*den by simpa using this
 intro h
 exact num_le_nat_mul_den h.le (by simpa using hn)
theorem ratLt_nonempty (x:M):(ratLt x).Nonempty:=by
 obtain hneg | rfl | hxpos:=lt_trichotomy x 0
 · obtain ⟨n,hn⟩:=Archimedean.arch (-x-x) zero_lt_one
   use Rat.ofInt (-n)
   suffices-(n • 1) < x by simpa using this
   exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
 · exact ⟨Rat.ofInt (-1),by simp⟩
 · obtain ⟨n,hn⟩:=Archimedean.arch 1 hxpos
   use Rat.mk' 1 (n+1) (by simp) (by simp)
   simpa using hn.trans_lt <| (nsmul_lt_nsmul_iff_left hxpos).mpr (by simp)
open scoped Pointwise in
theorem ratLt_add (x y:M):ratLt (x+y)=ratLt x+ratLt y:=by
 ext a
 rw [Set.mem_add]
 constructor
 ·
   intro h
   rw [Set.mem_setOf_eq] at h
   obtain ⟨k,hk⟩:=Archimedean.arch (1+1) <| sub_pos.mpr h
   have hk0:k≠0:=by
     contrapose! hk
     simp [hk]
   have hka0:k*a.den≠0:=mul_ne_zero hk0 a.den_ne_zero
   obtain ⟨m,⟨hm1,hm2⟩,_⟩:=existsUnique_add_zsmul_mem_Ico zero_lt_one 0 (k • a.den • x-1)
   refine ⟨mkRat m (k*a.den),?_,mkRat (k*a.num-m) (k*a.den),?_,?_⟩
   · rw [mkRat_mem_ratLt hka0, ←smul_smul]
     simpa using hm2
   · have hk':1+(k • a.num • 1-k • a.den • y) ≤ k • a.den • x-1:=by
       rw [smul_add,smul_sub,smul_add,le_sub_iff_add_le, ←sub_le_iff_le_add] at hk
       rw [le_sub_iff_add_le]
       convert! hk using 1
       abel
     have:k • a.num • 1-k • a.den • y < m • 1:=
       lt_of_lt_of_le (lt_add_of_pos_left _ zero_lt_one) (by simpa using hk'.trans hm1)
     rw [mkRat_mem_ratLt hka0,sub_smul,sub_lt_comm, ←smul_smul, ←smul_smul,natCast_zsmul]
     exact this
   · rw [Rat.mkRat_add_mkRat_of_den _ _ hka0]
     rw [add_sub_cancel,Rat.mkRat_mul_left hk0,Rat.mkRat_num_den']
 ·
   intro ⟨u,hu,v,hv,huv⟩
   rw [←huv]
   rw [Set.mem_setOf_eq] at hu hv ⊢
   exact num_smul_one_lt_den_smul_add hu hv
theorem ratLt'_bddAbove (x:M):BddAbove (ratLt' x):=
 Monotone.map_bddAbove Rat.cast_mono <| ratLt_bddAbove x
theorem ratLt'_nonempty (x:M):(ratLt' x).Nonempty:=Set.image_nonempty.mpr (ratLt_nonempty x)
open scoped Pointwise in
theorem ratLt'_add (x y:M):ratLt' (x+y)=ratLt' x+ratLt' y:=by
 rw [ratLt',ratLt_add,Set.image_add]
variable (M) in
theorem embedRealFun_zero:embedRealFun (0:M)=0:=by
 apply le_antisymm
 · apply csSup_le (ratLt'_nonempty 0)
   intro x
   unfold ratLt' ratLt
   suffices ∀ (y:ℚ),y.num • (1:M) < 0 → y=x → x ≤ 0 by simpa using this
   intro y hy hyx
   rw [←hyx,Rat.cast_nonpos, ←Rat.num_nonpos]
   exact (neg_of_smul_neg_right hy zero_le_one).le
 · rw [le_csSup_iff (ratLt'_bddAbove (0:M)) (ratLt'_nonempty 0)]
   intro x
   rw [mem_upperBounds]
   suffices (∀ (y:ℚ),y.num • (1:M) < 0 → y ≤ x) → 0 ≤ x by simpa using this
   intro h
   have h' (y:ℚ) (hy:y < 0):y ≤ x:=by
     exact h _ <| (smul_neg_iff_of_neg_left (by simpa using hy)).mpr zero_lt_one
   contrapose! h'
   obtain ⟨y,hxy,hy⟩:=exists_rat_btwn h'
   exact ⟨y,by simpa using hy,hxy⟩
theorem embedRealFun_add (x y:M):embedRealFun (x+y)=embedRealFun x+embedRealFun y:=by
 rw [embedRealFun,ratLt'_add,csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
   (ratLt'_nonempty y) (ratLt'_bddAbove y)]
variable (M) in
theorem embedRealFun_strictMono:StrictMono (embedRealFun (M:=M)):=by
 intro x y h
 have hyz:0 < y-x:=sub_pos.mpr h
 have hy:y=y-x+x:=(sub_add_cancel y x).symm
 apply lt_of_sub_pos
 rw [hy,embedRealFun_add,add_sub_cancel_right]
 obtain ⟨n,hn⟩:=Archimedean.arch 1 hyz
 have:(Rat.mk' 1 (n+1) (by simp) (by simp):ℝ)∈ratLt' (y-x):=by
   simpa using hn.trans_lt <| nsmul_lt_nsmul_left hyz (show n < n+1 by simp)
 exact lt_csSup_of_lt (ratLt'_bddAbove (y-x)) this (by simp [←Rat.num_pos])
variable (M) in
noncomputable
def embedReal:M →+o ℝ where
 toFun:=embedRealFun
 map_zero':=embedRealFun_zero M
 map_add':=embedRealFun_add
 monotone':=(embedRealFun_strictMono M).monotone
theorem embedReal_apply (a:M):embedReal M a=embedRealFun a:=by rfl
variable (M) in
theorem embedReal_injective:Function.Injective (embedReal M):=
 (embedRealFun_strictMono M).injective
@[simp]
theorem embedReal_one:(embedReal M) 1=1:=by
 rw [embedReal_apply]
 apply le_antisymm
 · apply csSup_le (ratLt'_nonempty 1)
   suffices ∀ (x:ℚ),x.num • (1:M) < (x.den:ℤ) • (1:M) → (x:ℝ) ≤ 1 by simpa using this
   intro x hx
   suffices x ≤ 1 by norm_cast
   simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_right zero_lt_one).mp hx).le
 · rw [le_csSup_iff (ratLt'_bddAbove (1:M)) (ratLt'_nonempty 1)]
   simp_rw [mem_upperBounds]
   suffices ∀ (x:ℝ),(∀ (y:ℚ),y.num • (1:M) < (y.den:ℤ) • 1 → y ≤ x) → 1 ≤ x by
     simpa using this
   intro x h
   have h' (y:ℚ) (hy:y < 1):y ≤ x:=
     h _ ((smul_lt_smul_iff_of_pos_right zero_lt_one).mpr (by simpa using (Rat.lt_iff _ _).mp hy))
   contrapose! h'
   obtain ⟨y,hxy,hy⟩:=exists_rat_btwn h'
   exact ⟨y,(by norm_cast at hy),hxy⟩
omit [One M] [ZeroLEOneClass M] [NeZero (1:M)] in
variable (M) in
theorem exists_orderAddMonoidHom_real_injective:
   ∃ f:M →+o ℝ,Function.Injective f:=by
 cases subsingleton_or_nontrivial M
 · exact ⟨0,Function.injective_of_subsingleton _⟩
 · obtain ⟨a,ha⟩:=exists_ne (0:M)
   let one:One M:=⟨|a|⟩
   have:ZeroLEOneClass M:=⟨abs_nonneg a⟩
   have:NeZero (1:M):=⟨abs_ne_zero.mpr ha⟩
   exact ⟨embedReal M,embedReal_injective M⟩
end Archimedean
end ProximityFlatProofPort
end PackedLegacy_HP

/-! Packed from ProximityPrize.SubmissionLower.V7. -/
section PackedLegacy_V7
section ProximityFlatProofPort
noncomputable section
open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open scoped NNReal
variable {R Γ₀:Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
namespace Valuation
class RankLeOne (v:Valuation R Γ₀) where
 hom' (v):ValueGroup₀ (.ofClass v) →*₀ ℝ≥0
 strictMono':StrictMono hom'
class RankOne (v:Valuation R Γ₀) extends RankLeOne v,Valuation.IsNontrivial v
open WithZero
lemma nonempty_rankOne_iff_mulArchimedean {v:Valuation R Γ₀} [v.IsNontrivial]:
   Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ (.ofClass v)):=by
 letI:DecidableEq ℝ≥0:=Classical.decEq ℝ≥0
 constructor
 · intro h
   obtain hv:=Nonempty.some h
   exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
 · intro _
   obtain ⟨f,hf⟩:=
     Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ (.ofClass v))ˣ)
   let e:=AddMonoidHom.toMultiplicativeRight (α:=(ValueGroup₀ (.ofClass v))ˣ) (β:=ℝ) f
   have he:StrictMono e:=by
     simp only [AddMonoidHom.coe_toMultiplicativeRight,AddMonoidHom.coe_coe,e]
     exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
   let rf:Multiplicative ℝ →*ℝ≥0ˣ:={
     toFun x:=Units.mk0 (.mk ((2:ℝ)^(log (M:=ℝ) x)) (by positivity)) <| by
       simp only [ne_eq,NNReal.eq_iff,NNReal.coe_mk,NNReal.coe_zero]
       positivity
     map_one':=by ext;simp
     map_mul' _ _:=by ext;simp [Real.rpow_add]
     }
   have H:StrictMono (map' (rf.comp e)):=by
     refine map'_strictMono ?_
     intro a b h
     simpa [←Units.val_lt_val, ←NNReal.coe_lt_coe,rf] using he h
   exact ⟨{
     hom':=withZeroUnitsEquiv.toMonoidWithZeroHom.comp <| (map' (rf.comp e)).comp
       withZeroUnitsEquiv.symm.toMonoidWithZeroHom
     strictMono':=withZeroUnitsEquiv_strictMono.comp <| H.comp
       withZeroUnitsEquiv_symm_strictMono
   }⟩
namespace RankOne
variable (v:Valuation R Γ₀) [hv:RankOne v]
abbrev hom:=RankLeOne.hom' v
lemma strictMono:StrictMono (hom v):=hv.strictMono'
lemma nontrivial:∃ r:R,v r≠0∧v r≠1:=IsNontrivial.exists_val_nontrivial
theorem zero_of_hom_zero {x:ValueGroup₀ (.ofClass v)} (hx:hom v x=0):x=0:=by
 refine (eq_of_le_of_not_lt (zero_le (a:=x)) fun h_lt↦?_).symm
 have hs:=strictMono v h_lt
 rw [map_zero,hx] at hs
 exact hs.false
theorem hom_eq_zero_iff {x:ValueGroup₀ (.ofClass v)}:hom v x=0 ↔ x=0:=
 ⟨fun h↦zero_of_hom_zero v h,fun h↦by rw [h,map_zero]⟩
def unit:Γ₀ˣ:=
 Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1
theorem unit_ne_one:unit v≠1:=by
 rw [Ne, ←Units.val_inj,Units.val_one]
 exact ((nontrivial v).choose_spec).2
instance:IsNontrivial v where
 exists_val_nontrivial:=RankOne.nontrivial v
section Restrict
instance isNontrivial_restrict:(v.restrict).IsNontrivial where
 exists_val_nontrivial:=by
   obtain ⟨x,⟨hx0,hx1⟩⟩:=IsNontrivial.exists_val_nontrivial (v:=v)
   exact ⟨x,by simp [hx0],by simpa⟩
variable (K:Type*) [DivisionRing K] (v:Valuation K Γ₀) [RankOne v]
instance restrict_RankOne:RankOne (v.restrict) where
 hom':=(RankOne.hom v).comp embedding
 strictMono':=(strictMono v).comp embedding_strictMono
@[simp]
lemma restrict_RankOne_hom_eq:
 RankOne.hom v.restrict=(RankOne.hom v).comp embedding:=rfl
set_option backward.defeqAttrib.useBackward true in
variable {K} in
theorem exists_val_lt {γ:ℝ≥0} (hγ:γ≠0):∃ x≠0,RankOne.hom v (v.restrict x) < γ:=by
 have hγ_pos:0 < γ:=pos_iff_ne_zero.mpr hγ
 obtain ⟨x,h⟩:=NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
 obtain ⟨k,hk⟩:=ValueGroup₀.restrict₀_surjective _ x.val
 refine ⟨k,?_,?_⟩
 · simp only [restrict₀_apply,MonoidWithZeroHom.coe_ofClass,restrict_def,map_eq_zero,
     dite_eq_left_iff,coe_ne_zero,imp_false,not_not] at hk
   by_contra h0
   rw [dif_pos (by rw [dif_pos ((zero_iff v).mpr h0)]),eq_comm] at hk
   simp at hk
 · convert! h
   simp only [restrict_RankOne_hom_eq,coe_comp,Function.comp_apply, ←hk]
   congr 1
   exact (embedding_restrict₀ k).symm
end Restrict
end RankOne
namespace RankLeOne
variable {K:Type*} [DivisionRing K] (v:Valuation K Γ₀) [RankLeOne v]
@[implicit_reducible]
def rankOne_of_exists (H:∃ x≠0,v x≠1):RankOne v where
 exists_val_nontrivial:=by
   by_contra! H'
   obtain ⟨x,hx,hx'⟩:=H
   exact hx' (H' x ((ne_zero_iff v).mpr hx))
@[implicit_reducible]
def rankOne_of_nontrivial (H:Nontrivial (ValueGroup₀ (.ofClass v))ˣ):RankOne v where
 exists_val_nontrivial:=by
   by_contra! H'
   rw [nontrivial_iff_exists_ne 1] at H
   obtain ⟨x,hx⟩:=H
   obtain ⟨k,hk⟩:=ValueGroup₀.restrict₀_surjective _ x.val
   have h0:v k≠0:=by
     apply_fun embedding at hk
     simp only [embedding_restrict₀,MonoidWithZeroHom.coe_ofClass] at hk
     simp [hk]
   have h1:v k≠1:=by
     apply_fun embedding at hk
     simp only [embedding_restrict₀,MonoidWithZeroHom.coe_ofClass] at hk
     apply_fun Units.val at hx using
         Units.val_injective (α:=(MonoidWithZeroHom.ofClass v).ValueGroup₀)
     intro h
     apply_fun embedding at hx using embedding_injective (f:=.ofClass v)
     simp [←hk,h] at hx
   exact h1 (H' k h0)
theorem exists_val_lt {K:Type*} [DivisionRing K] (v:Valuation K Γ₀) [RankLeOne v]:
   Subsingleton ((ValueGroup₀ (.ofClass v))ˣ)∨
     ∀ {γ:ℝ≥0} (_:γ≠0),∃ (x:K),x≠0∧(RankLeOne.hom' v) (v.restrict x) < γ:=by
 simp only [ne_eq,or_iff_not_imp_left,not_subsingleton_iff_nontrivial]
 exact fun H↦(rankOne_of_nontrivial v H).exists_val_lt
end RankLeOne
end Valuation
section ValuativeRel
open ValuativeRel
variable {R:Type*} [Ring R] [ValuativeRel R]
@[implicit_reducible]
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e:RankLeOneStruct R):
   Valuation.RankOne (valuation R) where
 hom':=e.emb.comp embedding
 strictMono':=e.strictMono.comp embedding_strictMono
instance [IsNontrivial R] [IsRankLeOne R]:
   Valuation.RankOne (valuation R):=
 Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some
def Valuation.RankOne.rankLeOneStruct (e:Valuation.RankOne (valuation R)):
   RankLeOneStruct R where
 emb:=e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v:=valuation R))
 strictMono:=e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))
lemma ValuativeRel.isRankLeOne_of_rankOne [h:(valuation R).RankOne]:
   IsRankLeOne R:=⟨⟨h.rankLeOneStruct⟩⟩
lemma ValuativeRel.isNontrivial_of_rankOne [h:(valuation R).RankOne]:
   ValuativeRel.IsNontrivial R:=
 (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial
open WithZero
lemma ValuativeRel.isRankLeOne_iff_mulArchimedean:
   IsRankLeOne R ↔ MulArchimedean (ValueGroupWithZero R):=by
 letI:DecidableEq (ValueGroupWithZero R):=Classical.decEq (ValueGroupWithZero R)
 letI:Decidable (IsNontrivial R):=Classical.propDecidable _
 constructor
 · rintro ⟨⟨f,hf⟩⟩
   exact .comap f.toMonoidHom hf
 · intro h
   by_cases H:IsNontrivial R
   · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
     have h':MulArchimedean (ValueGroup₀ (.ofClass (valuation R))):=
       MulArchimedean.comap embedding.toMonoidHom embedding_strictMono
     rw [←(valuation R).nonempty_rankOne_iff_mulArchimedean] at h'
     obtain ⟨f⟩:=h'
     exact isRankLeOne_of_rankOne
   · refine ⟨⟨{ emb:=1,strictMono:=?_}⟩⟩
     intro a b
     contrapose! H
     obtain ⟨H,H'⟩:=H
     rcases eq_or_ne a 0 with rfl | ha
     · simp_all
     rcases eq_or_ne a 1 with rfl | ha'
     · exact ⟨⟨b,(H.trans' zero_lt_one).ne',H.ne'⟩⟩
     · exact ⟨⟨a,ha,ha'⟩⟩
lemma ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀]
   (v:Valuation R Γ₀) [v.Compatible]:
   ValuativeRel.IsRankLeOne R:=by
 rw [isRankLeOne_iff_mulArchimedean]
 exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
   (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))
end ValuativeRel
end
end ProximityFlatProofPort
end PackedLegacy_V7

/-! Packed from ProximityPrize.SubmissionLower.V5. -/
section PackedLegacy_V5
section ProximityFlatProofPort
namespace Valuation.IsRankOneDiscrete
open WithZero MonoidWithZeroHom NNReal WithZeroMulInt
variable {Γ:Type*} [LinearOrderedCommGroupWithZero Γ]
section Ring
variable {R:Type*} [Ring R]
section LinearOrderedCommGroupWithZero
variable (v:Valuation R Γ) [hv:v.IsRankOneDiscrete]
@[simps!]
noncomputable def valueGroup₀_equiv_withZeroMulInt:ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ where
 __:=MulEquiv.withZero (intEquivOfZPowersEqTop _
   (Subgroup.zpowers_inv (g:=hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
 map_le_map_iff' {x y}:=by
   rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
   (Subgroup.zpowers_inv (g:=hv.generator') ▸ hv.generator'_zpowers_eq_top)
   (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le]
lemma valueGroup₀_equiv_withZeroMulInt_apply_zero:
   valueGroup₀_equiv_withZeroMulInt v 0=0:=by simp
lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k:ℤ):
   valueGroup₀_equiv_withZeroMulInt v (hv.generator'^k)=WithZero.exp (-k):=by
 simp only [map_zpow₀,valueGroup₀_equiv_withZeroMulInt_apply,WithZero.map'_coe,
   MonoidHom.coe_coe]
 rw [←WithZero.coe_zpow,WithZero.exp,WithZero.coe_inj, ←map_zpow]
 simp [←mulintEquivOfZPowersEqTop_symm_apply_zpow
   (Subgroup.zpowers_inv (g:=hv.generator') ▸ hv.generator'_zpowers_eq_top)]
lemma valueGroup₀_equiv_withZeroMulInt_strictMono:
   StrictMono (valueGroup₀_equiv_withZeroMulInt v):=by
 intro x y hxy
 rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
   (Subgroup.zpowers_inv (g:=hv.generator') ▸ hv.generator'_zpowers_eq_top)
   (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]
@[implicit_reducible]
noncomputable def rankOne {e:ℝ≥0} (he:1 < e):v.RankOne where
 hom':=(toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
     (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
 strictMono':=(toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
 exists_val_nontrivial:=IsNontrivial.exists_val_nontrivial
end LinearOrderedCommGroupWithZero
section WithZeroMulInt
variable {v:Valuation R ℤᵐ⁰} [hv:v.IsRankOneDiscrete]
lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj:Function.Surjective v)
   (x:R):(valueGroup₀_equiv_withZeroMulInt v) (v.restrict x)=v x:=by
 simp only [Valuation.restrict_def,ValueGroup₀.restrict₀_apply,
   valueGroup₀_equiv_withZeroMulInt_apply]
 split_ifs with h0 <;>
 simp only [MonoidWithZeroHom.coe_ofClass] at h0
 · simp [h0]
 · simp only [WithZero.map'_coe,MonoidHom.coe_coe]
   conv_rhs => rw [←coe_unzero h0]
   rw [WithZero.coe_inj, ←(MulEquiv.injective (intEquivOfZPowersEqTop _
     (Subgroup.zpowers_inv (g:=hv.generator') ▸ hv.generator'_zpowers_eq_top))).eq_iff,
     MulEquiv.apply_symm_apply]
   ext
   simp only [Units.val_mk0,intEquivOfZPowersEqTop_apply,inv_zpow',generator',
     SubgroupClass.coe_zpow]
   have hg:hv.generator=Units.mk0 (WithZero.exp (-1:ℤ):ℤᵐ⁰) (by simp):=
     generator_eq_exp_neg_one_of_surjective hsurj
   rw [hg]
   conv_lhs => rw [MonoidWithZeroHom.coe_ofClass, ←coe_unzero h0]
   simp only [coe_unzero,Int.reduceNeg,exp_neg,zpow_neg,Units.val_inv_eq_inv_val,
     Units.val_zpow_eq_zpow_val,Units.val_mk0,inv_zpow', ←exp_zsmul,Int.zsmul_eq_mul,mul_one,
     inv_inv]
   simp [WithZero.exp]
end WithZeroMulInt
end Ring
end Valuation.IsRankOneDiscrete
end ProximityFlatProofPort
end PackedLegacy_V5

/-! Packed from ProximityPrize.SubmissionLower.S5. -/
section PackedLegacy_S5
section ProximityFlatProofPort
namespace IsDedekindDomain.HeightOneSpectrum
open WithZero Ideal.IsDedekindDomain Valuation.IsRankOneDiscrete
section AKLB
variable {A K:Type*} (L:Type*) {B:Type*}
 [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
 [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
 [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
 [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
 (v:HeightOneSpectrum A) (w:HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
theorem intValuation_liesOver (x:A):
   v.intValuation x^(v.asIdeal.ramificationIdx' w.asIdeal)=
     w.intValuation (algebraMap A B x):=by
 rcases eq_or_ne x 0 with rfl | hx
 · simp [ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
 rw [intValuation_eq_exp_neg_multiplicity v hx,intValuation_eq_exp_neg_multiplicity w (by simpa),
   ←Set.image_singleton, ←Ideal.map_span,exp_neg,exp_neg,inv_pow, ←exp_nsmul,
   Int.nsmul_eq_mul,inv_inj,exp_inj, ←Nat.cast_mul,Nat.cast_inj]
 refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
 replace hx:Ideal.span {x}≠⊥:=by simp [hx]
 rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot,
   Nat.cast_mul,(FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]
theorem valuation_liesOver (x:K):
   v.valuation K x^v.asIdeal.ramificationIdx' w.asIdeal=
     w.valuation L (algebraMap K L x):=by
 obtain ⟨x,y,hy,rfl⟩:=IsFractionRing.div_surjective (A:=A) x
 simp [valuation_of_algebraMap,div_pow, ←IsScalarTower.algebraMap_apply A K L,
   IsScalarTower.algebraMap_apply A B L,intValuation_liesOver v w]
variable (K)
theorem uniformContinuous_algebraMap_liesOver:
   UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))):=by
 refine uniformContinuous_of_continuousAt_zero _ ?_
 rw [ContinuousAt,map_zero,(IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
   (IsValuativeTopology.hasBasis_nhds_zero _)]
 intro γL _
 let e:=v.asIdeal.ramificationIdx' w.asIdeal
 let σL:=WithVal.valueGroupOrderIso₀ (w.valuation L)
 let σw:=valueGroup₀_equiv_withZeroMulInt (w.valuation L)
 let σwV:=ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
 let m:ℤᵐ⁰:=σw (σL (σwV γL))
 let σvV:=ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
 let σv:=valueGroup₀_equiv_withZeroMulInt (v.valuation K)
 let σK:=WithVal.valueGroupOrderIso₀ (v.valuation K)
 let γK:=σvV.symm (σK.symm (σv.symm (exp (m.log/e))))
 have hγK:γK≠0:=by simp [γK,EmbeddingLike.map_eq_zero_iff (f:=σK.symm)]
 use .mk0 _ hγK
 simp only [Units.val_mk0,Set.mem_setOf_eq,true_and]
 intro x hx
 rcases eq_or_ne x 0 with rfl | hx₀;· simp
 rw [σvV.lt_symm_apply,σK.lt_symm_apply,σv.lt_symm_apply,
   ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀,
   ←Valuation.restrict_def,WithVal.valueGroupOrderIso₀_restrict,
   valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
   ←log_lt_log (by simp_all) (by simp)] at hx
 rw [←σwV.strictMono.lt_iff_lt, ←σL.strictMono.lt_iff_lt,
   ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀, ←Valuation.restrict_def,
   WithVal.valueGroupOrderIso₀_restrict, ←σw.strictMono.lt_iff_lt,
   valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
   WithVal.algebraMap_left_apply,WithVal.algebraMap_right_apply, ←valuation_liesOver L v,
   ←log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f:=σwV)]),log_pow,
   nsmul_eq_mul,mul_comm]
 exact Int.mul_lt_of_lt_ediv
   (mod_cast pos_of_ne_zero (ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx
end AKLB
end IsDedekindDomain.HeightOneSpectrum
end ProximityFlatProofPort
end PackedLegacy_S5

/-! Packed from ProximityPrize.SubmissionLower.R1. -/
section PackedLegacy_R1
namespace ProximityPrize.SubmissionLower.RCN345
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
def parameter:L:=algebraMap (Polynomial K) L Polynomial.X
theorem parameter_eq_ratFunc:
   parameter K L=algebraMap (RatFunc K) L (RatFunc.X:RatFunc K):=by
 change algebraMap (Polynomial K) L Polynomial.X=
   algebraMap (RatFunc K) L (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 exact IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L Polynomial.X
theorem aeval_parameter (f:Polynomial K):
   Polynomial.aeval (parameter K L) f=algebraMap (Polynomial K) L f:=by
 rw [parameter,Polynomial.aeval_algebraMap_apply,Polynomial.aeval_X_left_apply]
theorem polynomial_C_map (c:K):
   algebraMap (Polynomial K) L (Polynomial.C c)=algebraMap K L c:=
 (IsScalarTower.algebraMap_apply K (Polynomial K) L c).symm
section GivenValuation
variable (v:Valuation L ℤᵐ⁰) [htriv:v.IsTrivialOn K]
theorem coefficient_le_one (c:K):v (algebraMap K L c) ≤ 1:=by
 by_cases hc:c=0
 · simp [hc]
 · rw [htriv.eq_one c hc]
theorem polynomial_le_one (ht:v (parameter K L) ≤ 1) (f:Polynomial K):
   v (algebraMap (Polynomial K) L f) ≤ 1:=by
 induction f using Polynomial.induction_on' with
 | add f g hf hg =>
     rw [map_add]
     exact (v.map_add _ _).trans (max_le hf hg)
 | monomial n c =>
     rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
       map_mul,map_pow,polynomial_C_map]
     exact mul_le_one₀ (coefficient_le_one K L v c) zero_le
       (pow_le_one₀ zero_le ht)
theorem finiteNormalization_le_one (ht:v (parameter K L) ≤ 1)
   (s:FiniteNormalization K L):
   v (algebraMap (FiniteNormalization K L) L s) ≤ 1:=by
 exact RCN359.integral_le_one (Polynomial K) L v
   (polynomial_le_one K L v ht) s.property
theorem polynomial_value_of_parameter_gt_one (ht:1 < v (parameter K L))
   (f:Polynomial K) (hf:f≠0):
   v (algebraMap (Polynomial K) L f)=v (parameter K L)^f.natDegree:=by
 rw [←aeval_parameter K L f]
 exact Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
   (v:=v) (parameter K L) ht hf
theorem infinityBase_le_one (ht:1 < v (parameter K L)) (r:InfinityBase K):
   v (algebraMap (InfinityBase K) L r) ≤ 1:=by
 change v (algebraMap (RatFunc K) L r.val) ≤ 1
 by_cases hr:r.val=0
 · simp [hr]
 have hdegree:r.val.num.natDegree ≤ r.val.denom.natDegree:=by
   have hmem:RatFunc.inftyValuation K r.val ≤ 1:=r.property
   rw [RatFunc.inftyValuation_apply,RatFunc.inftyValuation_of_nonzero K hr,
     ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
   dsimp [RatFunc.intDegree] at hmem
   omega
 have hnum:=polynomial_value_of_parameter_gt_one K L v ht
   r.val.num (RatFunc.num_ne_zero hr)
 have hden:=polynomial_value_of_parameter_gt_one K L v ht
   r.val.denom r.val.denom_ne_zero
 rw [←RatFunc.num_div_denom r.val,map_div₀,map_div₀,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   hnum,hden]
 apply (div_le_one₀ (pow_pos (zero_lt_one.trans ht) _)).mpr
 exact pow_le_pow_right₀ ht.le hdegree
theorem infiniteNormalization_le_one (ht:1 < v (parameter K L))
   (s:InfiniteNormalization K L):
   v (algebraMap (InfiniteNormalization K L) L s) ≤ 1:=by
 exact RCN359.integral_le_one (InfinityBase K) L v
   (infinityBase_le_one K L v ht) s.property
theorem exists_unique_finite_place (hv:Function.Surjective v)
   (ht:v (parameter K L) ≤ 1):
   ∃! p:HeightOneSpectrum (FiniteNormalization K L),v=p.valuation L:=
 RCN359.exists_unique_place (FiniteNormalization K L) L v
   (finiteNormalization_le_one K L v ht) hv
theorem exists_unique_infinite_place (hv:Function.Surjective v)
   (ht:1 < v (parameter K L)):
   ∃! q:HeightOneSpectrum (InfiniteNormalization K L),v=q.valuation L:=
 RCN359.exists_unique_place (InfiniteNormalization K L) L v
   (infiniteNormalization_le_one K L v ht) hv
theorem finite_or_infinite_place (hv:Function.Surjective v):
   (∃ p:HeightOneSpectrum (FiniteNormalization K L),v=p.valuation L)∨
   (∃ q:HeightOneSpectrum (InfiniteNormalization K L),v=q.valuation L):=by
 by_cases ht:v (parameter K L) ≤ 1
 · exact Or.inl (exists_unique_finite_place K L v hv ht).exists
 · exact Or.inr (exists_unique_infinite_place K L v hv (lt_of_not_ge ht)).exists
end GivenValuation
theorem infinitePlace_liesOver
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.asIdeal.LiesOver (RCN349.infinityPlace K).asIdeal:=by
 have hbase:HeightOneSpectrum.under (InfinityBase K) q=
     RCN349.infinityPlace K:=by
   apply HeightOneSpectrum.ext
   exact IsLocalRing.eq_maximalIdeal
     ((HeightOneSpectrum.under (InfinityBase K) q).isPrime.isMaximal
       (HeightOneSpectrum.under (InfinityBase K) q).ne_bot)
 have hq:q.asIdeal.LiesOver
     (HeightOneSpectrum.under (InfinityBase K) q).asIdeal:=by
   change q.asIdeal.LiesOver (q.asIdeal.under (InfinityBase K))
   infer_instance
 rwa [hbase] at hq
theorem finitePlace_parameter_le_one
   (p:HeightOneSpectrum (FiniteNormalization K L)):
   p.valuation L (parameter K L) ≤ 1:=by
 rw [parameter,IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L]
 exact p.valuation_le_one _
theorem infinitePlace_parameter_value
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.valuation L (parameter K L)=
     WithZero.exp ((RCN349.infinityPlace K).asIdeal.ramificationIdx'
       q.asIdeal:ℤ):=by
 letI:=infinitePlace_liesOver K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.infinityPlace K) q (RatFunc.X:RatFunc K)
 rw [RCN349.infinityPlace,RCN353.infinity_valuation_eq,
   RatFunc.inftyValuation.X] at h
 rw [parameter_eq_ratFunc]
 simpa [RCN349.infinityPlace] using h.symm
theorem infinitePlace_parameter_gt_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   1 < q.valuation L (parameter K L):=by
 letI:=infinitePlace_liesOver K L q
 rw [infinitePlace_parameter_value, ←WithZero.exp_zero,WithZero.exp_lt_exp]
 exact_mod_cast Nat.pos_iff_ne_zero.mpr
   (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal
     (RCN349.infinityPlace K).ne_bot)
theorem finitePlace_trivial
   (p:HeightOneSpectrum (FiniteNormalization K L)):
   (p.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 let cS:FiniteNormalization K L:=
   algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c)
 have hunit:IsUnit cS:=
   ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C).map
     (algebraMap (Polynomial K) (FiniteNormalization K L))
 have hval:p.valuation L (algebraMap (FiniteNormalization K L) L cS)=1:=
   Valuation.Integers.one_of_isUnit' hunit (p.valuation_le_one (K:=L))
 change p.valuation L (algebraMap (FiniteNormalization K L) L
   (algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c)))=1 at hval
 rw [←IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L,
   polynomial_C_map] at hval
 exact hval
theorem infinitePlace_trivial
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   (q.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 letI:=infinitePlace_liesOver K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.infinityPlace K) q (algebraMap K (RatFunc K) c)
 rw [RCN349.infinityPlace,RCN353.infinity_valuation_eq] at h
 have hC:RatFunc.inftyValuation K (algebraMap K (RatFunc K) c)=1:=
   RatFunc.inftyValuation.C K hc
 rw [hC,one_pow, ←IsScalarTower.algebraMap_apply K (RatFunc K) L] at h
 exact h.symm
abbrev ChartPlace:=
 Sum (HeightOneSpectrum (FiniteNormalization K L))
   (HeightOneSpectrum (InfiniteNormalization K L))
def chartValuation:ChartPlace K L → Valuation L ℤᵐ⁰:=
 Sum.elim (fun p↦p.valuation L) (fun q↦q.valuation L)
theorem chartValuation_surjective (p:ChartPlace K L):
   Function.Surjective (chartValuation K L p):=by
 rcases p with p | q
 · exact p.valuation_surjective L
 · exact q.valuation_surjective L
theorem chartValuation_trivial (p:ChartPlace K L):
   (chartValuation K L p).IsTrivialOn K:=by
 rcases p with p | q
 · exact finitePlace_trivial K L p
 · exact infinitePlace_trivial K L q
theorem chartValuation_injective:Function.Injective (chartValuation K L):=by
 intro p q h
 rcases p with p | p <;> rcases q with q | q
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
 · have hp:=finitePlace_parameter_le_one K L p
   have hq:=infinitePlace_parameter_gt_one K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hp hq)
 · have hp:=infinitePlace_parameter_gt_one K L p
   have hq:=finitePlace_parameter_le_one K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hq hp)
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
def NormalizedValuation:=
 {v:Valuation L ℤᵐ⁰//Function.Surjective v∧v.IsTrivialOn K}
def chartMap (p:ChartPlace K L):NormalizedValuation K L:=
 ⟨chartValuation K L p,chartValuation_surjective K L p,chartValuation_trivial K L p⟩
theorem chartMap_bijective:Function.Bijective (chartMap K L):=by
 constructor
 · intro p q h
   exact chartValuation_injective K L (congrArg Subtype.val h)
 · intro v
   letI:v.val.IsTrivialOn K:=v.property.2
   rcases finite_or_infinite_place K L v.val v.property.1 with ⟨p,hp⟩ | ⟨q,hq⟩
   · refine ⟨Sum.inl p,?_⟩
     apply Subtype.ext
     exact hp.symm
   · refine ⟨Sum.inr q,?_⟩
     apply Subtype.ext
     exact hq.symm
def chartEquiv:ChartPlace K L ≃ NormalizedValuation K L:=
 Equiv.ofBijective (chartMap K L) (chartMap_bijective K L)
end
end ProximityPrize.SubmissionLower.RCN345
end PackedLegacy_R1

/-! Packed from ProximityPrize.SubmissionLower.W4. -/
section PackedLegacy_W4
namespace ProximityPrize.SubmissionLower.RCN358
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:Algebra K (InfinityBase K):=
 (RCN352.constantMap K).toAlgebra
def infinityBasePoint:InfinityBase K →ₐ[K] K where
 toRingHom:=(RCN352.residueEquiv K).symm.toRingHom.comp
   (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)))
 commutes' c:=by
   change (RCN352.residueEquiv K).symm
     (RCN352.residueConstant K c)=c
   rw [←RCN352.residueEquiv_apply,RingEquiv.symm_apply_apply]
theorem infinityBasePoint_kernel:
   RingHom.ker (infinityBasePoint K).toRingHom=
     (RCN349.infinityPlace K).asIdeal:=by
 ext r
 change (RCN352.residueEquiv K).symm
     (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)) r)=0 ↔
   r∈IsLocalRing.maximalIdeal (InfinityBase K)
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply (RCN352.residueEquiv K).symm.injective
   simpa only [map_zero] using h
 · intro h
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]
variable [IsAlgClosed K]
theorem finiteBase_natDegree_eq_one (f:Polynomial K) (hf:Irreducible f):
   f.natDegree=1:=
 Polynomial.natDegree_eq_of_degree_eq_some
   (IsAlgClosed.degree_eq_one_of_irreducible K hf)
theorem finiteBase_exists_point (p:HeightOneSpectrum (Polynomial K)):
   ∃ phi:Polynomial K →ₐ[K] K,RingHom.ker phi.toRingHom=p.asIdeal:=by
 obtain ⟨f,hf,hm,hplace⟩:=RCN366.exists_monic_primePlace K p
 obtain ⟨alpha,hroot⟩:=IsAlgClosed.exists_root f (by
   rw [IsAlgClosed.degree_eq_one_of_irreducible K hf]
   exact one_ne_zero)
 let phi:Polynomial K →ₐ[K] K:=Polynomial.aeval alpha
 have hkermax:(RingHom.ker phi.toRingHom).IsMaximal:=
   RCN354.pointKernel_isMaximal phi
 have hle:p.asIdeal ≤ RingHom.ker phi.toRingHom:=by
   rw [←hplace]
   change Ideal.span {f} ≤ RingHom.ker phi.toRingHom
   apply (Ideal.span_singleton_le_iff_mem (I:=RingHom.ker phi.toRingHom)).mpr
   change f.eval alpha=0
   exact hroot
 refine ⟨phi,?_⟩
 exact ((p.isPrime.isMaximal p.ne_bot).eq_of_le hkermax.ne_top hle).symm
variable (L:Type*) [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
theorem finitePlace_inertia_one
   (q:HeightOneSpectrum (FiniteNormalization K L)):
   q.asIdeal.inertiaDeg (Polynomial K)=1:=by
 letI:Algebra K (FiniteNormalization K L):=
   ((algebraMap (Polynomial K) (FiniteNormalization K L)).comp Polynomial.C).toAlgebra
 letI:IsScalarTower K (Polynomial K) (FiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 obtain ⟨phi,hphi⟩:=finiteBase_exists_point K
   (HeightOneSpectrum.under (Polynomial K) q)
 apply RCN373.inertiaDeg_eq_one_of_point_fiber phi q.asIdeal
 exact hphi.symm
theorem infinitePlace_inertia_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.asIdeal.inertiaDeg (InfinityBase K)=1:=by
 letI:Algebra K (InfiniteNormalization K L):=
   ((algebraMap (InfinityBase K) (InfiniteNormalization K L)).comp
     (algebraMap K (InfinityBase K))).toAlgebra
 letI:IsScalarTower K (InfinityBase K) (InfiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 apply RCN373.inertiaDeg_eq_one_of_point_fiber
   (infinityBasePoint K) q.asIdeal
 rw [infinityBasePoint_kernel]
 exact (Ideal.over_def q.asIdeal (RCN349.infinityPlace K).asIdeal).symm
theorem infinitePlace_inertia'_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   (RCN349.infinityPlace K).asIdeal.inertiaDeg' q.asIdeal=1:=by
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 rw [Ideal.inertiaDeg'_eq_inertiaDeg]
 exact infinitePlace_inertia_one K L q
theorem finiteFiber_weight_one (f:Polynomial K) (hf:Irreducible f)
   (Q:{Q:Ideal (FiniteNormalization K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K f hf).asIdeal (FiniteNormalization K L)}):
   (f.natDegree:ℤ)*(Q.1.inertiaDeg (Polynomial K):ℤ)=1:=by
 have hQ:=finitePlace_inertia_one K L
   (RCN357.placeAbove (Polynomial K) (FiniteNormalization K L)
     (RCN366.primePlace K f hf) Q)
 change Q.1.inertiaDeg (Polynomial K)=1 at hQ
 rw [finiteBase_natDegree_eq_one K f hf,hQ]
 norm_num
theorem infiniteFiber_weight_one
   (Q:{Q:Ideal (InfiniteNormalization K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN349.infinityPlace K).asIdeal (InfiniteNormalization K L)}):
   (Q.1.inertiaDeg (InfinityBase K):ℤ)=1:=by
 have hQ:=infinitePlace_inertia_one K L
   (RCN357.placeAbove (InfinityBase K) (InfiniteNormalization K L)
     (RCN349.infinityPlace K) Q)
 exact_mod_cast hQ
end
end ProximityPrize.SubmissionLower.RCN358
end PackedLegacy_W4

/-! Packed from ProximityPrize.SubmissionLower.Z7. -/
section PackedLegacy_Z7
namespace ProximityPrize.SubmissionLower.RCN187
open scoped BigOperators
noncomputable section
section Multiplicative
variable {K L σ Γ₀:Type*} [Field K] [Field L] [Fintype σ]
 [LinearOrderedCommGroupWithZero Γ₀]
theorem valuation_monomial_le (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (d:σ →₀ ℕ) (c:K) (hd:∀ i,d i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _ => pow_zero _),map_mul,map_prod]
 simp only [map_pow]
 calc
   v (coeff c)*(∏ i,v (x i)^d i) ≤
       1*(∏ i,max 1 (v (x i))^cap i):=by
     apply mul_le_mul' (hcoeff c)
     apply Finset.prod_le_prod (fun _ _ => zero_le)
     intro i _
     exact (pow_le_pow_left₀ zero_le (le_max_right _ _) (d i)).trans
       (pow_le_pow_right₀ (le_max_left _ _) (hd i))
   _=_:=one_mul _
theorem valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 apply valuation_monomial_le v coeff hcoeff x cap d
 intro i
 exact (MvPolynomial.monomial_le_degreeOf i hd).trans (hcap i)
theorem max_one_valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 apply max_le
 · exact Finset.one_le_prod fun _ _ => one_le_pow₀ (le_max_left _ _)
 · exact valuation_eval_le_box v coeff hcoeff x cap F hcap
end Multiplicative
section IntegerPole
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
def poleOrder (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L):ℤ:=
 max 0 (v x).log
theorem log_max_one (z:WithZero (Multiplicative ℤ)):
   (max 1 z).log=max 0 z.log:=by
 by_cases hz:z=0
 · simp [hz]
 rcases le_total 1 z with h | h
 · have hlog:(0:ℤ) ≤ z.log:=by
     simpa using (WithZero.log_le_log (by simp) hz).2 h
   simp only [max_eq_right h,max_eq_right hlog]
 · have hlog:z.log ≤ (0:ℤ):=by
     simpa using (WithZero.log_le_log hz (by simp)).2 h
   simp only [max_eq_left h,WithZero.log_one,max_eq_left hlog]
theorem log_prod_of_one_le {ι:Type*} (s:Finset ι)
   (f:ι → WithZero (Multiplicative ℤ)):
   (∀ i∈s,1 ≤ f i) →
     (∏ i∈s,f i).log=∑ i∈s,(f i).log:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 induction s using Finset.induction_on with
 | empty => intro _;simp
 | @insert i s hi ih =>
     intro hf
     have hfi:1 ≤ f i:=hf i (Finset.mem_insert_self i s)
     have hfs:∀ j∈s,1 ≤ f j:=
       fun j hj => hf j (Finset.mem_insert_of_mem hj)
     have hfi0:f i≠0:=ne_of_gt (zero_lt_one.trans_le hfi)
     have hprod0:(∏ j∈s,f j)≠0:=
       ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfs))
     rw [Finset.prod_insert hi,WithZero.log_mul hfi0 hprod0,
       Finset.sum_insert hi,ih hfs]
theorem poleOrder_eval_le_box
   (v:Valuation L (WithZero (Multiplicative ℤ))) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∑ i,(cap i:ℤ)*poleOrder v (x i):=by
 classical
 have hfactor:∀ i∈(Finset.univ:Finset σ),
     1 ≤ max 1 (v (x i))^cap i:=
   fun _ _ => one_le_pow₀ (le_max_left _ _)
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hright0:(∏ i,max 1 (v (x i))^cap i)≠0:=
   ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfactor))
 have hlog:=(WithZero.log_le_log hleft0 hright0).2
   (max_one_valuation_eval_le_box v coeff hcoeff x cap F hcap)
 rw [log_prod_of_one_le Finset.univ _ hfactor] at hlog
 simpa only [WithZero.log_pow,log_max_one,nsmul_eq_mul,poleOrder] using hlog
theorem weighted_poleOrder_eval_le_box {τ:Type*} (S:Finset τ)
   (weight:τ → ℕ) (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ t∈S,(weight t:ℤ)*poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ i,(cap i:ℤ)*(∑ t∈S,(weight t:ℤ)*poleOrder (v t) (x i)):=by
 classical
 calc
   _ ≤ ∑ t∈S,(weight t:ℤ)*
       (∑ i,(cap i:ℤ)*poleOrder (v t) (x i)):=by
     apply Finset.sum_le_sum
     intro t ht
     exact mul_le_mul_of_nonneg_left
       (poleOrder_eval_le_box (v t) coeff (hcoeff t ht) x cap F hcap)
       (Int.natCast_nonneg (weight t))
   _=_:=by
     simp_rw [Finset.mul_sum]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro i _
     apply Finset.sum_congr rfl
     intro t _
     ring
end IntegerPole
end
end ProximityPrize.SubmissionLower.RCN187
end PackedLegacy_Z7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier04 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.S3. -/
section PackedLegacy_S3
section ProximityFlatProofPort
namespace Ideal
universe u v
variable {R:Type u} [CommRing R]
 {S:Type v} [CommRing S] [Algebra R S]
 (p:Ideal R) (P:Ideal S)
local notation "f" => algebraMap R S
open Module UniqueFactorizationMonoid
attribute [local instance] Ideal.Quotient.field
section FinrankQuotientMap
open scoped nonZeroDivisors
variable {K:Type*} [Field K] [Algebra R K]
 {L:Type*} [Field L] [Algebra S L] [IsFractionRing S L]
 {V V' V'':Type*}
 [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
 [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']
 [AddCommGroup V''] [Module R V'']
variable (K)
open scoped Matrix
variable {K} in
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [Module.Finite R S]
   [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Algebra.IsAlgebraic R S]
   [IsTorsionFree R K] (hp:p≠⊤) (b:Set S)
   (hb':Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R=⊤):
   Submodule.span K (algebraMap S L '' b)=⊤:=by
 have hRL:Function.Injective (algebraMap R L):=by
   rw [IsScalarTower.algebraMap_eq R K L]
   exact (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective R K)
 let M:Submodule R S:=Submodule.span R b
 obtain ⟨n,a,ha⟩:=@Module.Finite.exists_fin R (S ⧸ M) _ _ _ _
 have smul_top_eq:p • (⊤:Submodule R (S ⧸ M))=⊤:=by
   calc
     p • ⊤=Submodule.map M.mkQ (p • ⊤):=by
       rw [Submodule.map_smul'',Submodule.map_top,M.range_mkQ]
     _=⊤:=by rw [Ideal.smul_top_eq_map,(Submodule.map_mkQ_eq_top M _).mpr hb']
 have exists_sum:∀ x:S ⧸ M,∃ a':Fin n → R,(∀ i,a' i∈p)∧∑ i,a' i • a i=x:=by
   intro x
   obtain ⟨a'',ha'',hx⟩:=(Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1
     (by { rw [ha,smul_top_eq];exact Submodule.mem_top}:
       x∈p • Submodule.span R (Set.range a))
   · refine ⟨fun i => a'' i,fun i => ha'' _,?_⟩
     rw [←hx,Finsupp.sum_fintype]
     exact fun _ => zero_smul _ _
 choose A' hA'p hA' using fun i => exists_sum (a i)
 let A:Matrix (Fin n) (Fin n) R:=Matrix.of A'-1
 let B:=A.adjugate
 have A_smul:∀ i,∑ j,A i j • a j=0:=by
   intros
   simp [A,Matrix.sub_apply,Matrix.of_apply,Matrix.one_apply,sub_smul,
     Finset.sum_sub_distrib,hA',sub_self]
 have d_smul:∀ i,A.det • a i=0:=by
   intro i
   calc
     A.det • a i=∑ j,(B*A) i j • a j:=?_
     _=∑ k,B i k • ∑ j,A k j • a j:=?_
     _=0:=Finset.sum_eq_zero fun k _ => ?_
   · simp only [B,Matrix.adjugate_mul,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,ite_true,
       mul_ite,mul_one,mul_zero,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ]
   · simp only [Matrix.mul_apply,Finset.smul_sum,Finset.sum_smul,smul_smul]
     rw [Finset.sum_comm]
   · rw [A_smul,smul_zero]
 have span_d:(Submodule.span S ({algebraMap R S A.det}:Set S)).restrictScalars R ≤ M:=by
   intro x hx
   rw [Submodule.restrictScalars_mem] at hx
   obtain ⟨x',rfl⟩:=Submodule.mem_span_singleton.mp hx
   rw [smul_eq_mul,mul_comm, ←Algebra.smul_def] at hx ⊢
   rw [←Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_smul]
   obtain ⟨a',_,quot_x_eq⟩:=exists_sum (Submodule.Quotient.mk x')
   rw [←quot_x_eq,Finset.smul_sum]
   conv =>
     lhs;congr;next => skip
     intro x;rw [smul_comm A.det,d_smul,smul_zero]
   exact Finset.sum_const_zero
 refine top_le_iff.mp
     (calc
       ⊤=(Ideal.span {algebraMap R L A.det}).restrictScalars K:=?_
       _ ≤ Submodule.span K (algebraMap S L '' b):=?_)
 · rw [eq_comm,Submodule.restrictScalars_eq_top_iff,Ideal.span_singleton_eq_top]
   refine IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr ?_)
   refine ne_zero_of_map («f»:=Ideal.Quotient.mk p) ?_
   have:=Ideal.Quotient.nontrivial_iff.mpr hp
   calc
     Ideal.Quotient.mk p A.det=Matrix.det ((Ideal.Quotient.mk p).mapMatrix A):=by
       rw [RingHom.map_det]
     _=Matrix.det ((Ideal.Quotient.mk p).mapMatrix (Matrix.of A'-1)):=rfl
     _=Matrix.det fun i j =>
         (Ideal.Quotient.mk p) (A' i j)-(1:Matrix (Fin n) (Fin n) (R ⧸ p)) i j:=?_
     _=Matrix.det (-1:Matrix (Fin n) (Fin n) (R ⧸ p)):=?_
     _=(-1:R ⧸ p)^n:=by rw [Matrix.det_neg,Fintype.card_fin,Matrix.det_one,mul_one]
     _≠0:=IsUnit.ne_zero (isUnit_one.neg.pow _)
   · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
     rw [map_sub,RingHom.mapMatrix_apply,map_one]
     simp
   · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
     rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hA'p i j),zero_sub,Matrix.neg_apply]
 · intro x hx
   rw [Submodule.restrictScalars_mem,IsScalarTower.algebraMap_apply R S L] at hx
   exact IsFractionRing.ideal_span_singleton_map_subset R hRL span_d hx
variable [hRK:IsFractionRing R K]
theorem FinrankQuotientMap.linearIndependent_of_nontrivial [IsDedekindDomain R]
   (hRS:RingHom.ker (algebraMap R S)≠⊤) (F:V'' →ₗ[R] V) (hf:Function.Injective F)
   (f':V'' →ₗ[R] V') {ι:Type*} {b:ι → V''} (hb':LinearIndependent S (f' ∘ b)):
   LinearIndependent K (F ∘ b):=by
 contrapose hb' with hb
 simp only [linearIndependent_iff',not_forall] at hb ⊢
 obtain ⟨s,g,eq,j',hj's,hj'g⟩:=hb
 use s
 obtain ⟨a,hag,j,hjs,hgI⟩:=Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
 choose g'' hg'' using hag
 letI:=Classical.propDecidable
 let g' i:=if h:i∈s then g'' i h else 0
 have hg':∀ i∈s,algebraMap _ _ (g' i)=a*g i:=by
   intro i hi;exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
 have hgI:algebraMap R S (g' j)≠0:=by
   simp only [FractionalIdeal.mem_coeIdeal,not_exists,not_and'] at hgI
   exact hgI _ (hg' j hjs)
 refine ⟨fun i => algebraMap R S (g' i),?_,j,hjs,hgI⟩
 have eq:F (∑ i∈s,g' i • b i)=0:=by
   rw [map_sum, ←smul_zero a, ←eq,Finset.smul_sum]
   refine Finset.sum_congr rfl ?_
   intro i hi
   rw [map_smul, ←IsScalarTower.algebraMap_smul K,hg' i hi, ←smul_assoc,
     smul_eq_mul,Function.comp_apply]
 simp only [IsScalarTower.algebraMap_smul, ←map_smul, ←map_sum,
   (F.map_eq_zero_iff hf).mp eq,map_zero,(· ∘ ·)]
variable (L)
theorem finrank_quotient_map [IsDomain S] [IsDedekindDomain R] [Algebra K L]
   [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
   [hp:p.IsMaximal] [Module.Finite R S]:
   finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p)=finrank K L:=by
 let ι:=Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
 let b:Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p):=Module.Free.chooseBasis _ _
 let b':ι → S:=fun i => (Ideal.Quotient.mk_surjective (b i)).choose
 have b_eq_b':⇑b=(Submodule.mkQ (map (algebraMap R S) p)).restrictScalars R ∘ b':=
   funext fun i => (Ideal.Quotient.mk_surjective (b i)).choose_spec.symm
 let b'':ι → L:=algebraMap S L ∘ b'
 have b''_li:LinearIndependent K b'':=?_
 · have b''_sp:Submodule.span K (Set.range b'')=⊤:=?_
   · let c:Basis ι K L:=Basis.mk b''_li b''_sp.ge
     rw [finrank_eq_card_basis b,finrank_eq_card_basis c]
   · rw [Set.range_comp]
     refine FinrankQuotientMap.span_eq_top p hp.ne_top _ (top_le_iff.mp ?_)
     intro x _
     have mem_span_b:((Submodule.mkQ (map (algebraMap R S) p)) x:S ⧸ map (algebraMap R S) p)∈
         Submodule.span (R ⧸ p) (Set.range b):=b.mem_span _
     rw [←@Submodule.restrictScalars_mem R,
       Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective,b_eq_b',
       Set.range_comp, ←Submodule.map_span] at mem_span_b
     obtain ⟨y,y_mem,y_eq⟩:=Submodule.mem_map.mp mem_span_b
     suffices y+ -(y-x)∈_ by simpa
     rw [LinearMap.restrictScalars_apply,Submodule.mkQ_apply,Submodule.mkQ_apply,
       Submodule.Quotient.eq] at y_eq
     exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
 · have:=b.linearIndependent;rw [b_eq_b'] at this
   convert!
     FinrankQuotientMap.linearIndependent_of_nontrivial K _
       ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkQ _).restrictScalars R) this
   · rw [Quotient.algebraMap_eq,Ideal.mk_ker]
     exact hp.ne_top
   · exact IsFractionRing.injective S L
end FinrankQuotientMap
section FactLeComap
local notation "e" => ramificationIdx' p P
noncomputable instance Quotient.algebraQuotientPowRamificationIdx:Algebra (R ⧸ p) (S ⧸ P^e):=
 Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx')
@[simp]
theorem Quotient.algebraMap_quotient_pow_ramificationIdx (x:R):
   algebraMap (R ⧸ p) (S ⧸ P^e) (Ideal.Quotient.mk p x)=Ideal.Quotient.mk (P^e) (f x):=rfl
@[instance_reducible]
def Quotient.algebraQuotientOfRamificationIdxNeZero [hfp:NeZero e]:
   Algebra (R ⧸ p) (S ⧸ P):=
 Quotient.algebraQuotientOfLEComap (le_comap_of_ramificationIdx'_ne_zero hfp.out)
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
@[simp]
theorem Quotient.algebraMap_quotient_of_ramificationIdx_neZero
   [NeZero e] (x:R):
   algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x)=Ideal.Quotient.mk P (f x):=rfl
@[simps]
noncomputable def powQuotSuccInclusion (i:ℕ):
   Ideal.map (Ideal.Quotient.mk (P^e)) (P^(i+1)) →ₗ[R ⧸ p]
   Ideal.map (Ideal.Quotient.mk (P^e)) (P^i) where
 toFun x:=⟨x,Ideal.map_mono (Ideal.pow_le_pow_right i.le_succ) x.2⟩
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
theorem powQuotSuccInclusion_injective (i:ℕ):
   Function.Injective (powQuotSuccInclusion p P i):=by
 rw [←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
 rintro ⟨x,hx⟩ hx0
 rw [Subtype.ext_iff] at hx0 ⊢
 rwa [powQuotSuccInclusion_apply_coe] at hx0
noncomputable def quotientToQuotientRangePowQuotSuccAux {i:ℕ} {a:S} (a_mem:a∈P^i):
   S ⧸ P →
     (P^i).map (Ideal.Quotient.mk (P^e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i):=
 Quotient.map' (fun x:S => ⟨_,Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩)
   fun x y h => by
   rw [Submodule.quotientRel_def] at h ⊢
   simp only [map_mul,LinearMap.mem_range]
   refine ⟨⟨_,Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul a_mem h)⟩,?_⟩
   ext
   rw [powQuotSuccInclusion_apply_coe,Subtype.coe_mk,Submodule.coe_sub,Subtype.coe_mk,
     Subtype.coe_mk,map_mul,map_sub,mul_sub]
theorem quotientToQuotientRangePowQuotSuccAux_mk {i:ℕ} {a:S} (a_mem:a∈P^i) (x:S):
   quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quotient.mk x)=
     Submodule.Quotient.mk ⟨_,Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩:=by
 apply Quotient.map'_mk''
section
variable [hfp:NeZero (ramificationIdx' p P)]
noncomputable def quotientToQuotientRangePowQuotSucc
   {i:ℕ} {a:S} (a_mem:a∈P^i):
   S ⧸ P →ₗ[R ⧸ p]
     (P^i).map (Ideal.Quotient.mk (P^e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) where
 toFun:=quotientToQuotientRangePowQuotSuccAux p P a_mem
 map_add' x y:=by
   induction x,y using Quotient.inductionOn₂' with | _ x y
   simp only [Submodule.Quotient.mk''_eq_mk, ←Submodule.Quotient.mk_add,
     quotientToQuotientRangePowQuotSuccAux_mk,mul_add,map_add,map_mul,AddMemClass.mk_add_mk]
 map_smul' x y:=by
   induction x,y using Quotient.inductionOn₂' with | _ x y
   simp only [Submodule.Quotient.mk''_eq_mk,RingHom.id_apply,
     quotientToQuotientRangePowQuotSuccAux_mk]
   refine congr_arg Submodule.Quotient.mk ?_
   ext
   simp only [map_mul,Quotient.mk_eq_mk,Submodule.coe_smul_of_tower,
     Algebra.smul_def,Quotient.algebraMap_quotient_pow_ramificationIdx]
   ring
theorem quotientToQuotientRangePowQuotSucc_mk {i:ℕ} {a:S} (a_mem:a∈P^i) (x:S):
   quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk x)=
     Submodule.Quotient.mk ⟨_,Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩:=
 quotientToQuotientRangePowQuotSuccAux_mk p P a_mem x
theorem quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPrime]
   {i:ℕ} (hi:i < e) {a:S} (a_mem:a∈P^i) (a_notMem:a∉P^(i+1)):
   Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem):=fun x =>
 Quotient.inductionOn' x fun x y =>
   Quotient.inductionOn' y fun y h => by
     have Pe_le_Pi1:P^e ≤ P^(i+1):=Ideal.pow_le_pow_right hi
     simp only [Submodule.Quotient.mk''_eq_mk,quotientToQuotientRangePowQuotSucc_mk,
       Submodule.Quotient.eq,LinearMap.mem_range,Subtype.ext_iff,
       Submodule.coe_sub] at h ⊢
     rcases h with ⟨⟨⟨z⟩,hz⟩,h⟩
     rw [Submodule.Quotient.quot_mk_eq_mk,Ideal.Quotient.mk_eq_mk,Ideal.mem_quotient_iff_mem_sup,
       sup_eq_left.mpr Pe_le_Pi1] at hz
     rw [powQuotSuccInclusion_apply_coe,Subtype.coe_mk,Submodule.Quotient.quot_mk_eq_mk,
       Ideal.Quotient.mk_eq_mk, ←map_sub,Ideal.Quotient.eq, ←mul_sub] at h
     exact
       (Ideal.IsPrime.mem_pow_mul _
             ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_left
         a_notMem
theorem quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S]
   (hP0:P≠⊥) [hP:P.IsPrime] {i:ℕ} (hi:i < e) {a:S} (a_mem:a∈P^i)
   (a_notMem:a∉P^(i+1)):
   Function.Surjective (quotientToQuotientRangePowQuotSucc p P a_mem):=by
 rintro ⟨⟨⟨x⟩,hx⟩⟩
 have Pe_le_Pi:P^e ≤ P^i:=Ideal.pow_le_pow_right hi.le
 rw [Submodule.Quotient.quot_mk_eq_mk,Ideal.Quotient.mk_eq_mk,Ideal.mem_quotient_iff_mem_sup,
   sup_eq_left.mpr Pe_le_Pi] at hx
 suffices hx':x∈Ideal.span {a} ⊔ P^(i+1) by
   obtain ⟨y',hy',z,hz,rfl⟩:=Submodule.mem_sup.mp hx'
   obtain ⟨y,rfl⟩:=Ideal.mem_span_singleton.mp hy'
   refine ⟨Submodule.Quotient.mk y,?_⟩
   simp only [Submodule.Quotient.quot_mk_eq_mk,quotientToQuotientRangePowQuotSucc_mk,
     Submodule.Quotient.eq,LinearMap.mem_range,Subtype.ext_iff,
     Submodule.coe_sub]
   refine ⟨⟨_,Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩,?_⟩
   rw [powQuotSuccInclusion_apply_coe,Subtype.coe_mk,Ideal.Quotient.mk_eq_mk,map_add,
     sub_add_cancel_left,map_neg]
 rw [←Submodule.span_singleton_le_iff_mem,submodule_span_eq] at a_mem a_notMem
 have hspan0:span {a}≠⊥:=fun ha↦a_notMem (ha ▸ bot_le)
 rwa [sup_comm,irreducible_pow_sup hspan0 ((prime_iff_isPrime hP0).mpr hP).irreducible,
   count_normalizedFactors_eq a_mem a_notMem,min_eq_left i.le_succ]
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S]
   [P.IsPrime] (hP:P≠⊥) {i:ℕ} (hi:i < e):
   ((P^i).map (Ideal.Quotient.mk (P^e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i))
     ≃ₗ[R ⧸ p] S ⧸ P:=by
 choose a a_mem a_notMem using
   SetLike.exists_of_lt
     (Ideal.pow_right_strictAnti P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
 refine (LinearEquiv.ofBijective ?_ ⟨?_,?_⟩).symm
 · exact quotientToQuotientRangePowQuotSucc p P a_mem
 · exact quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem
 · exact quotientToQuotientRangePowQuotSucc_surjective p P hP hi a_mem a_notMem
theorem rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0:P≠⊥)
   {i:ℕ} (hi:i < e):
   Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P^e)) (P^i))=
     Module.rank (R ⧸ p) (S ⧸ P)+
       Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P^e)) (P^(i+1))):=by
 rw [←rank_range_of_injective _ (powQuotSuccInclusion_injective p P i),
   (quotientRangePowQuotSuccInclusionEquiv p P hP0 hi).symm.rank_eq]
 exact (Submodule.rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion p P i))).symm
theorem rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0:P≠⊥)
   (i:ℕ) (hi:i ≤ e):
   Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P^e)) (P^i))=
     (e-i) • Module.rank (R ⧸ p) (S ⧸ P):=by
 let Q:ℕ → Prop:=
   fun i => Module.rank (R ⧸ p) { x//x∈map (Quotient.mk (P^e)) (P^i)}
     =(e-i) • Module.rank (R ⧸ p) (S ⧸ P)
 refine Nat.decreasingInduction' (P:=Q) (fun j lt_e _le_j ih => ?_) hi ?_
 · dsimp only [Q]
   rw [rank_pow_quot_aux p P _ lt_e,ih, ←succ_nsmul',Nat.sub_succ, ←Nat.succ_eq_add_one,
     Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
   assumption
 · dsimp only [Q]
   rw [Nat.sub_self,zero_nsmul,map_quotient_self]
   exact rank_bot (R ⧸ p) (S ⧸ P^e)
end
theorem rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
   (hP0:P≠⊥) (he:e≠0):
   Module.rank (R ⧸ p) (S ⧸ P^e)=
     e •
       @Module.rank (R ⧸ p) (S ⧸ P) _ _
         (@Algebra.toModule _ _ _ _ <|
           @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩):=by
 letI:NeZero e:=⟨he⟩
 have:=rank_pow_quot p P hP0 0 (Nat.zero_le e)
 rw [pow_zero,Nat.sub_zero,Ideal.one_eq_top,Ideal.map_top] at this
 exact (rank_top (R ⧸ p) _).symm.trans this
theorem finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0:P≠⊥)
   [p.IsMaximal] [P.IsPrime] (he:e≠0):
   finrank (R ⧸ p) (S ⧸ P^e)=
     e*
       @finrank (R ⧸ p) (S ⧸ P) _ _
         (@Algebra.toModule _ _ _ _ <|
           @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩):=by
 letI:NeZero e:=⟨he⟩
 letI:Algebra (R ⧸ p) (S ⧸ P):=Quotient.algebraQuotientOfRamificationIdxNeZero p P
 have hdim:=rank_prime_pow_ramificationIdx _ _ hP0 he
 by_cases hP:FiniteDimensional (R ⧸ p) (S ⧸ P)
 · have:=(finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
   apply @Nat.cast_injective Cardinal
   rw [finrank_eq_rank',Nat.cast_mul,finrank_eq_rank',hdim,nsmul_eq_mul]
 have hPe:=mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
 simp only [finrank_of_infinite_dimensional hP,finrank_of_infinite_dimensional hPe,
   mul_zero]
end FactLeComap
section FactorsMap
variable [IsDedekindDomain S]
theorem Factors.ne_bot (P:(factors (map (algebraMap R S) p)).toFinset):(P:Ideal S)≠⊥:=
 (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero
instance Factors.isPrime (P:(factors (map (algebraMap R S) p)).toFinset):
   IsPrime (P:Ideal S):=
 Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))
theorem Factors.ramificationIdx_ne_zero (P:(factors (map (algebraMap R S) p)).toFinset):
   ramificationIdx' p P.1≠0:=
 IsDedekindDomain.ramificationIdx'_ne_zero (ne_zero_of_mem_factors (Multiset.mem_toFinset.mp P.2))
   (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2)))
instance Factors.fact_ramificationIdx_neZero (P:(factors (map (algebraMap R S) p)).toFinset):
   NeZero (ramificationIdx' p P.1):=
 ⟨Factors.ramificationIdx_ne_zero p P⟩
attribute [local instance] Quotient.algebraQuotientOfRamificationIdxNeZero
instance Factors.isScalarTower (P:(factors (map (algebraMap R S) p)).toFinset):
   IsScalarTower R (R ⧸ p) (S ⧸ (P:Ideal S)):=
 IsScalarTower.of_algebraMap_eq' rfl
instance Factors.liesOver [p.IsMaximal] (P:(factors (map (algebraMap R S) p)).toFinset):
   P.1.LiesOver p:=
 ⟨(comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P.1)).injective).symm⟩
theorem Factors.finrank_pow_ramificationIdx [p.IsMaximal]
   (P:(factors (map (algebraMap R S) p)).toFinset):
   finrank (R ⧸ p) (S ⧸ (P:Ideal S)^ramificationIdx' p P.1)=
     ramificationIdx' p P.1*inertiaDeg' p (P:Ideal S):=by
 rw [finrank_prime_pow_ramificationIdx,inertiaDeg'_algebraMap]
 exacts [Factors.ne_bot p P,NeZero.ne _]
instance Factors.finiteDimensional_quotient_pow [Module.Finite R S] [p.IsMaximal]
   (P:(factors (map (algebraMap R S) p)).toFinset):
   FiniteDimensional (R ⧸ p) (S ⧸ (P:Ideal S)^ramificationIdx' p P.1):=by
 refine .of_finrank_pos ?_
 rw [pos_iff_ne_zero,Factors.finrank_pow_ramificationIdx]
 exact mul_ne_zero (Factors.ramificationIdx_ne_zero p P) (inertiaDeg'_pos p P.1).ne'
universe w
noncomputable def Factors.piQuotientEquiv (p:Ideal R) (hp:map (algebraMap R S) p≠⊥):
   S ⧸ map (algebraMap R S) p ≃+*
     ∀ P:(factors (map (algebraMap R S) p)).toFinset,
       S ⧸ (P:Ideal S)^ramificationIdx' p P.1:=
 (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
   @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
     (fun P => S ⧸ (P:Ideal S)^(factors (map (algebraMap R S) p)).count (P:Ideal S))
     (fun P => S ⧸ (P:Ideal S)^ramificationIdx' p P.1) _ _
     fun P:(factors (map (algebraMap R S) p)).toFinset =>
     Ideal.quotEquivOfEq <| by
       rw [IsDedekindDomain.ramificationIdx'_eq_factors_count hp (Factors.isPrime p P)
           (Factors.ne_bot p P)]
@[simp]
theorem Factors.piQuotientEquiv_mk (p:Ideal R) (hp:map (algebraMap R S) p≠⊥) (x:S):
   Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x)=fun _ => Ideal.Quotient.mk _ x:=rfl
@[simp]
theorem Factors.piQuotientEquiv_map (p:Ideal R) (hp:map (algebraMap R S) p≠⊥) (x:R):
   Factors.piQuotientEquiv p hp (algebraMap _ _ x)=fun _ =>
     Ideal.Quotient.mk _ (algebraMap _ _ x):=rfl
variable (S)
noncomputable def Factors.piQuotientLinearEquiv (p:Ideal R) (hp:map (algebraMap R S) p≠⊥):
   (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
     ∀ P:(factors (map (algebraMap R S) p)).toFinset,
       S ⧸ (P:Ideal S)^ramificationIdx' p P.1:=
 { Factors.piQuotientEquiv p hp with
   map_smul':=by
     rintro ⟨c⟩ ⟨x⟩;ext P
     simp only [Submodule.Quotient.quot_mk_eq_mk,Quotient.mk_eq_mk,Algebra.smul_def,
       Quotient.algebraMap_quotient_map_quotient,Quotient.mk_algebraMap,
       RingHomCompTriple.comp_apply,Pi.mul_apply,Pi.algebraMap_apply]
     congr}
variable (K L:Type*) [Field K] [Field L] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
 [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
 [IsScalarTower R K L] [Module.Finite R S]
theorem sum_ramification_inertia {p:Ideal R} [p.IsMaximal] (hp0:p≠⊥):
   ∑ P∈IsDedekindDomain.primesOverFinset p S,
       ramificationIdx' p P*inertiaDeg' p P=finrank K L:=by
 set e:=ramificationIdx' p (S:=S)
 calc
   ∑ P∈(factors (map (algebraMap R S) p)).toFinset,e P*inertiaDeg' p P=
       ∑ P∈(factors (map (algebraMap R S) p)).toFinset.attach,
         finrank (R ⧸ p) (S ⧸ (P:Ideal S)^e P):=?_
   _=finrank (R ⧸ p)
         (∀ P:(factors (map (algebraMap R S) p)).toFinset,S ⧸ (P:Ideal S)^e P):=
     (finrank_pi_fintype (R ⧸ p)).symm
   _=finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p):=?_
   _=finrank K L:=?_
 · rw [←Finset.sum_attach]
   refine Finset.sum_congr rfl fun P _ => ?_
   rw [Factors.finrank_pow_ramificationIdx]
 · refine LinearEquiv.finrank_eq (Factors.piQuotientLinearEquiv S p ?_).symm
   rwa [Ne,Ideal.map_eq_bot_iff_le_ker,(RingHom.injective_iff_ker_eq_bot _).mp <|
     algebraMap_injective_of_field_isFractionRing R S K L,le_bot_iff]
 · exact finrank_quotient_map p K L
theorem inertiaDeg_le_finrank [NoZeroSMulDivisors R S] {p:Ideal R} [p.IsMaximal]
   (P:Ideal S) [hP₁:P.IsPrime] [hP₂:P.LiesOver p] (hp0:p≠⊥):
   p.inertiaDeg' P ≤ Module.finrank K L:=by
 classical
 have hP:P∈IsDedekindDomain.primesOverFinset p S:=
   (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁,hP₂⟩
 rw [←sum_ramification_inertia S K L hp0, ←Finset.add_sum_erase _ _ hP]
 refine le_trans (Nat.le_mul_of_pos_left _ ?_) (Nat.le_add_right _ _)
 exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0
theorem ramificationIdx_le_finrank [NoZeroSMulDivisors R S] {p:Ideal R} [p.IsMaximal]
   (P:Ideal S) [hP₁:P.IsPrime] [hP₂:P.LiesOver p]:
   p.ramificationIdx' P ≤ Module.finrank K L:=by
 classical
 by_cases hp0:p=⊥
 · simp [hp0]
 have hP:P∈IsDedekindDomain.primesOverFinset p S:=
   (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁,hP₂⟩
 rw [←sum_ramification_inertia S K L hp0, ←Finset.add_sum_erase _ _ hP]
 refine le_trans (Nat.le_mul_of_pos_right _ ?_) (Nat.le_add_right _ _)
 exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P
theorem card_primesOverFinset_le_finrank [NoZeroSMulDivisors R S] {p:Ideal R} [p.IsMaximal]
   (hp0:p≠⊥):Finset.card (IsDedekindDomain.primesOverFinset p S) ≤ Module.finrank K L:=by
 rw [←sum_ramification_inertia S K L hp0,Finset.card_eq_sum_ones]
 refine Finset.sum_le_sum fun P hP↦?_
 have:P.IsPrime:=((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).1
 have:P.LiesOver p:=((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).2
 refine Right.one_le_mul ?_ ?_
 · exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0
 · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P
lemma ramificationIdx_mul_inertiaDeg_of_isLocalRing [IsLocalRing S] {p:Ideal R} [p.IsMaximal]
   (hp0:p≠⊥):
   ramificationIdx' p (IsLocalRing.maximalIdeal S)*
     p.inertiaDeg' (IsLocalRing.maximalIdeal S)=Module.finrank K L:=by
 have:=FaithfulSMul.of_field_isFractionRing R S K L
 simp_rw [←sum_ramification_inertia S K L hp0,IsLocalRing.primesOverFinset_eq S hp0,
   Finset.sum_singleton]
end FactorsMap
end Ideal
end ProximityFlatProofPort
end PackedLegacy_S3

/-! Packed from ProximityPrize.SubmissionLower.R2. -/
section PackedLegacy_R2
namespace ProximityPrize.SubmissionLower.RCN346
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
def poleOrder (v:Place K L) (x:L):ℤ:=
 RCN187.poleOrder v.val x
theorem poleOrder_nonneg (v:Place K L) (x:L):0 ≤ poleOrder K L v x:=
 le_max_left _ _
theorem poleOrder_eq_zero_of_le_one (v:Place K L) (x:L) (h:v.val x ≤ 1):
   poleOrder K L v x=0:=by
 change max 0 (v.val x).log=0
 rw [←RCN187.log_max_one,max_eq_left h,WithZero.log_one]
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
def infinityFiber:Finset (Ideal (InfiniteNormalization K L)):=
 IsDedekindDomain.primesOverFinset (RCN349.infinityPlace K).asIdeal
   (InfiniteNormalization K L)
def infinityPlace
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   HeightOneSpectrum (InfiniteNormalization K L):=
 RCN357.placeAbove (InfinityBase K) (InfiniteNormalization K L)
   (RCN349.infinityPlace K) Q
def infinityValuation
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   Place K L:=
 RCN345.chartMap K L (Sum.inr (infinityPlace K L Q))
theorem infinityValuation_injective:Function.Injective (infinityValuation K L):=by
 intro P Q h
 apply Subtype.ext
 have hc:=(RCN345.chartMap_bijective K L).1 h
 have hp:=Sum.inr.inj hc
 exact congrArg (fun p:HeightOneSpectrum (InfiniteNormalization K L)↦p.asIdeal) hp
theorem infinity_pole_eq_ramification
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   poleOrder K L (infinityValuation K L Q) (RCN345.parameter K L)=
     ((RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1:ℤ):=by
 change max 0 (((infinityPlace K L Q).valuation L)
   (RCN345.parameter K L)).log=_
 rw [RCN345.infinitePlace_parameter_value,
   WithZero.log_exp,max_eq_right (Int.natCast_nonneg _)]
 rfl
theorem sum_infinity_ramification_eq_finrank:
   (∑ Q∈(infinityFiber K L).attach,
     (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1)=
     Module.finrank (RatFunc K) L:=by
 have h:=Ideal.sum_ramification_inertia (InfiniteNormalization K L) (RatFunc K) L
   (RCN349.infinityPlace K).ne_bot
 calc
   (∑ Q∈(infinityFiber K L).attach,
       (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1)=
     ∑ Q∈infinityFiber K L,
       (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q*
         (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q:=by
     rw [←Finset.sum_attach (infinityFiber K L)
       (fun Q:Ideal (InfiniteNormalization K L)↦
         (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q*
           (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q)]
     apply Finset.sum_congr rfl
     intro Q _
     have hf:=RCN358.infinitePlace_inertia'_one K L (infinityPlace K L Q)
     change (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q.1=1 at hf
     rw [hf,mul_one]
   _=Module.finrank (RatFunc K) L:=h
theorem sum_infinity_poles_eq_finrank:
   (∑ Q∈(infinityFiber K L).attach,
     poleOrder K L (infinityValuation K L Q) (RCN345.parameter K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 simp_rw [infinity_pole_eq_ramification]
 exact_mod_cast sum_infinity_ramification_eq_finrank K L
def infinityValues:Finset (Place K L):=
 (infinityFiber K L).attach.image (infinityValuation K L)
theorem sum_poles_infinityValues_eq_finrank:
   (∑ v∈infinityValues K L,
     poleOrder K L v (RCN345.parameter K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 rw [infinityValues,Finset.sum_image (fun _ _ _ _ h↦infinityValuation_injective K L h)]
 exact sum_infinity_poles_eq_finrank K L
theorem poleOrder_eq_zero_of_not_mem_infinity (v:Place K L)
   (hv:v∉infinityValues K L):
   poleOrder K L v (RCN345.parameter K L)=0:=by
 by_contra hnonzero
 have ht:1 < v.val (RCN345.parameter K L):=
   lt_of_not_ge fun hle↦hnonzero (poleOrder_eq_zero_of_le_one K L v _ hle)
 letI:v.val.IsTrivialOn K:=v.property.2
 obtain ⟨q,hq,_⟩:=
   RCN345.exists_unique_infinite_place K L v.val v.property.1 ht
 have hmem:q.asIdeal∈infinityFiber K L:=
   (IsDedekindDomain.mem_primesOverFinset_iff
     (RCN349.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
     ⟨q.isPrime,RCN345.infinitePlace_liesOver K L q⟩
 let Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}:=⟨q.asIdeal,hmem⟩
 have hplace:infinityPlace K L Q=q:=by
   apply HeightOneSpectrum.ext
   rfl
 have hvmap:infinityValuation K L Q=v:=by
   apply Subtype.ext
   change (infinityPlace K L Q).valuation L=v.val
   rw [hplace]
   exact hq.symm
 apply hv
 rw [←hvmap]
 exact Finset.mem_image.mpr ⟨Q,Finset.mem_attach _ Q,rfl⟩
theorem finite_sum_pole_le_finrank (W:Finset (Place K L)):
   (∑ v∈W,poleOrder K L v (RCN345.parameter K L)) ≤
     (Module.finrank (RatFunc K) L:ℤ):=by
 have htrim:
     (∑ v∈W,poleOrder K L v (RCN345.parameter K L))=
     ∑ v∈W ∩ infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=by
   symm
   apply Finset.sum_subset Finset.inter_subset_left
   intro v hvW hvnot
   apply poleOrder_eq_zero_of_not_mem_infinity K L v
   intro hvI
   exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvI⟩)
 calc
   _=∑ v∈W ∩ infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=htrim
   _ ≤ ∑ v∈infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact poleOrder_nonneg K L v _
   _=(Module.finrank (RatFunc K) L:ℤ):=sum_poles_infinityValues_eq_finrank K L
theorem finite_indexed_sum_pole_le_finrank
   {ι:Type*} [DecidableEq ι] (s:Finset ι) (v:ι → Place K L)
   (hv:Set.InjOn v (s:Set ι)):
   (∑ i∈s,poleOrder K L (v i) (RCN345.parameter K L)) ≤
     (Module.finrank (RatFunc K) L:ℤ):=by
 have h:=finite_sum_pole_le_finrank K L (s.image v)
 rwa [Finset.sum_image (fun _ hx _ hy heq↦hv hx hy heq)] at h
end
end ProximityPrize.SubmissionLower.RCN346
end PackedLegacy_R2

/-! Packed from ProximityPrize.SubmissionLower.DG. -/
section PackedLegacy_DG
namespace ProximityPrize.SubmissionLower.RCN026
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
def order (v:Place K L) (x:L):ℤ:= -(v.val x).log
def zeroOrder (v:Place K L) (x:L):ℤ:=max 0 (order K L v x)
theorem zeroOrder_nonneg (v:Place K L) (x:L):0 ≤ zeroOrder K L v x:=
 le_max_left _ _
theorem zeroOrder_sub_poleOrder (v:Place K L) (x:L):
   zeroOrder K L v x-RCN346.poleOrder K L v x=order K L v x:=by
 unfold zeroOrder order RCN346.poleOrder RCN187.poleOrder
 omega
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
variable (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
def finiteFiber (p:{p:Polynomial K//p∈s}):
   Finset (Ideal (FiniteNormalization K L)):=
 IsDedekindDomain.primesOverFinset
   (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
   (FiniteNormalization K L)
abbrev FiniteIndex:=
 Σ p:{p:Polynomial K//p∈s},
   {Q:Ideal (FiniteNormalization K L)//Q∈finiteFiber K L s hs p}
def finitePlace (i:FiniteIndex K L s hs):
   HeightOneSpectrum (FiniteNormalization K L):=
 RCN357.placeAbove (Polynomial K) (FiniteNormalization K L)
   (RCN366.primePlace K i.1.1 (hs i.1.1 i.1.2).1) i.2
theorem finitePlace_injective:Function.Injective (finitePlace K L s hs):=by
 rintro ⟨p,P⟩ ⟨q,Q⟩ h
 have hI:P.1=Q.1:=congrArg HeightOneSpectrum.asIdeal h
 let pbase:=RCN366.primePlace K p.1 (hs p.1 p.2).1
 let qbase:=RCN366.primePlace K q.1 (hs q.1 q.2).1
 letI:P.1.LiesOver pbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff pbase.ne_bot
     (FiniteNormalization K L)).mp P.2).2
 letI:Q.1.LiesOver qbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff qbase.ne_bot
     (FiniteNormalization K L)).mp Q.2).2
 have hbase:pbase=qbase:=by
   apply HeightOneSpectrum.ext
   calc
     pbase.asIdeal=P.1.under (Polynomial K):=Ideal.over_def P.1 pbase.asIdeal
     _=Q.1.under (Polynomial K):=congrArg (Ideal.under (Polynomial K)) hI
     _=qbase.asIdeal:=(Ideal.over_def Q.1 qbase.asIdeal).symm
 have hpq:p=q:=Subtype.ext <|
   RCN366.primePlace_injective K p.1 q.1
     (hs p.1 p.2).1 (hs q.1 q.2).1 (hs p.1 p.2).2 (hs q.1 q.2).2 hbase
 subst q
 have hPQ:P=Q:=Subtype.ext hI
 cases hPQ
 rfl
abbrev InfinityIndex:=
 {Q:Ideal (InfiniteNormalization K L)//Q∈RCN346.infinityFiber K L}
abbrev FamilyIndex:=FiniteIndex K L s hs ⊕ InfinityIndex K L
def familyChart:FamilyIndex K L s hs → RCN345.ChartPlace K L:=
 Sum.elim (fun i↦Sum.inl (finitePlace K L s hs i))
   (fun Q↦Sum.inr (RCN346.infinityPlace K L Q))
def familyValuation (i:FamilyIndex K L s hs):Place K L:=
 RCN345.chartMap K L (familyChart K L s hs i)
theorem familyValuation_injective:Function.Injective (familyValuation K L s hs):=by
 intro i j h
 have hc:=(RCN345.chartMap_bijective K L).1 h
 cases i with
 | inl i =>
   cases j with
   | inl j =>
     exact congrArg Sum.inl (finitePlace_injective K L s hs (Sum.inl.inj hc))
   | inr j => cases hc
 | inr i =>
   cases j with
   | inl j => cases hc
   | inr j =>
     have hI:i.1=j.1:=congrArg HeightOneSpectrum.asIdeal (Sum.inr.inj hc)
     exact congrArg Sum.inr (Subtype.ext hI)
theorem finiteContribution_eq_sum (x:L):
   RCN349.finiteContribution K L s hs x=
     ∑ i:FiniteIndex K L s hs,
       RCN357.fieldOrder (FiniteNormalization K L) L
         (finitePlace K L s hs i) x:=by
 rw [Fintype.sum_sigma]
 unfold RCN349.finiteContribution
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro p _
 rw [RCN358.finiteBase_natDegree_eq_one K p.1 (hs p.1 p.2).1]
 simp only [Nat.cast_one,one_mul]
 apply Finset.sum_congr rfl
 intro Q _
 have hweight:=RCN358.finitePlace_inertia_one K L
   (finitePlace K L s hs ⟨p,Q⟩)
 change Q.1.inertiaDeg (Polynomial K)=1 at hweight
 rw [hweight]
 simp only [Nat.cast_one,one_mul]
 rfl
theorem infinityContribution_eq_sum (x:L):
   RCN349.infinityContribution K L x=
     ∑ Q:InfinityIndex K L,
       RCN357.fieldOrder (InfiniteNormalization K L) L
         (RCN346.infinityPlace K L Q) x:=by
 unfold RCN349.infinityContribution
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro Q _
 rw [RCN358.infiniteFiber_weight_one K L Q,one_mul]
 rfl
theorem sum_family_order_eq_contributions (x:L):
   (∑ i:FamilyIndex K L s hs,order K L (familyValuation K L s hs i) x)=
     RCN349.finiteContribution K L s hs x+
       RCN349.infinityContribution K L x:=by
 rw [Fintype.sum_sum_type]
 change
   (∑ i:FiniteIndex K L s hs,
     RCN357.fieldOrder (FiniteNormalization K L) L
       (finitePlace K L s hs i) x)+
   (∑ Q:InfinityIndex K L,
     RCN357.fieldOrder (InfiniteNormalization K L) L
       (RCN346.infinityPlace K L Q) x)=_
 rw [←finiteContribution_eq_sum K L s hs x, ←infinityContribution_eq_sum K L x]
def familyValues:Finset (Place K L):=
 Finset.univ.image (familyValuation K L s hs)
theorem sum_familyValues_order_eq_contributions (x:L):
   (∑ v∈familyValues K L s hs,order K L v x)=
     RCN349.finiteContribution K L s hs x+
       RCN349.infinityContribution K L x:=by
 rw [familyValues,Finset.sum_image
   (fun _ _ _ _ h↦familyValuation_injective K L s hs h)]
 exact sum_family_order_eq_contributions K L s hs x
variable {s hs}
def placesFor (x:L) (hx:x≠0):Finset (Place K L):=
 familyValues K L (RCN349.basePrimesFor K L x hx)
   (RCN349.basePrimesFor_primes K L x hx)
theorem sum_placesFor_order_zero (x:L) (hx:x≠0):
   (∑ v∈placesFor K L x hx,order K L v x)=0:=by
 rw [placesFor,sum_familyValues_order_eq_contributions]
 exact RCN349.projective_curve_order_sum K L x hx
theorem placesFor_covers (x:L) (hx:x≠0) (v:Place K L)
   (hv:order K L v x≠0):v∈placesFor K L x hx:=by
 obtain ⟨c,rfl⟩:=(RCN345.chartMap_bijective K L).2 v
 let s:=RCN349.basePrimesFor K L x hx
 let hs:=RCN349.basePrimesFor_primes K L x hx
 change RCN345.chartMap K L c∈familyValues K L s hs
 rcases c with q | q
 · have hq:RCN357.fieldOrder (FiniteNormalization K L) L q x≠0:=hv
   obtain ⟨p,hp,hirred,hQ⟩:=RCN349.basePrimesFor_covers K L x hx q hq
   let pindex:{p:Polynomial K//p∈s}:=⟨p,hp⟩
   let Q:{Q:Ideal (FiniteNormalization K L)//Q∈finiteFiber K L s hs pindex}:=
     ⟨q.asIdeal,hQ⟩
   let i:FamilyIndex K L s hs:=Sum.inl ⟨pindex,Q⟩
   have heq:familyValuation K L s hs i=
       RCN345.chartMap K L (Sum.inl q):=by
     have hplace:finitePlace K L s hs ⟨pindex,Q⟩=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap K L
       (Sum.inl (finitePlace K L s hs ⟨pindex,Q⟩))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
 · have hQ:q.asIdeal∈RCN346.infinityFiber K L:=
     (IsDedekindDomain.mem_primesOverFinset_iff
       (RCN349.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
       ⟨q.isPrime,RCN345.infinitePlace_liesOver K L q⟩
   let Q:InfinityIndex K L:=⟨q.asIdeal,hQ⟩
   let i:FamilyIndex K L s hs:=Sum.inr Q
   have heq:familyValuation K L s hs i=
       RCN345.chartMap K L (Sum.inr q):=by
     have hplace:RCN346.infinityPlace K L Q=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap K L
       (Sum.inr (RCN346.infinityPlace K L Q))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
theorem sum_placesFor_zero_eq_pole (x:L) (hx:x≠0):
   (∑ v∈placesFor K L x hx,zeroOrder K L v x)=
     ∑ v∈placesFor K L x hx,RCN346.poleOrder K L v x:=by
 apply sub_eq_zero.mp
 rw [←Finset.sum_sub_distrib]
 simp_rw [zeroOrder_sub_poleOrder]
 exact sum_placesFor_order_zero K L x hx
theorem finite_zero_places_le_poleMass (x:L) (hx:x≠0)
   (U:Finset (Place K L)) (hU:∀ v∈U,1 ≤ order K L v x):
   (U.card:ℤ) ≤
     ∑ v∈placesFor K L x hx,RCN346.poleOrder K L v x:=by
 have hsub:U ⊆ placesFor K L x hx:=by
   intro v hv
   apply placesFor_covers K L x hx v
   have h:=hU v hv
   omega
 calc
   (U.card:ℤ)=∑ _v∈U,(1:ℤ):=by simp
   _ ≤ ∑ v∈U,zeroOrder K L v x:=by
     apply Finset.sum_le_sum
     intro v hv
     exact (hU v hv).trans (le_max_right _ _)
   _ ≤ ∑ v∈placesFor K L x hx,zeroOrder K L v x:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg hsub
     intro v _ _
     exact zeroOrder_nonneg K L v x
   _=_:=sum_placesFor_zero_eq_pole K L x hx
end
end ProximityPrize.SubmissionLower.RCN026
end PackedLegacy_DG

/-! Packed from ProximityPrize.SubmissionLower.H4. -/
section PackedLegacy_H4
namespace ProximityPrize.SubmissionLower.RCN017
open IsDedekindDomain
noncomputable section
section PointKernels
variable {K S:Type*} [Field K] [CommRing S] [Algebra K S]
def pointKernel (phi:S →ₐ[K] K):Ideal S:=RingHom.ker phi.toRingHom
@[simp] theorem mem_pointKernel (phi:S →ₐ[K] K) (s:S):
   s∈pointKernel phi ↔ phi s=0:=Iff.rfl
theorem point_surjective (phi:S →ₐ[K] K):Function.Surjective phi:=by
 intro c
 exact ⟨algebraMap K S c,by simpa using phi.commutes c⟩
theorem pointKernel_isPrime (phi:S →ₐ[K] K):(pointKernel phi).IsPrime:=
 RingHom.ker_isPrime phi.toRingHom
theorem pointKernel_isMaximal (phi:S →ₐ[K] K):(pointKernel phi).IsMaximal:=
 RingHom.ker_isMaximal_of_surjective phi.toRingHom (point_surjective phi)
theorem pointKernel_injective:
   Function.Injective (pointKernel:(S →ₐ[K] K) → Ideal S):=by
 intro phi psi hker
 apply AlgHom.ext
 intro s
 have hs:s-algebraMap K S (phi s)∈pointKernel phi:=by simp
 have hs':s-algebraMap K S (phi s)∈pointKernel psi:=hker ▸ hs
 have hz:=(mem_pointKernel psi _).mp hs'
 have heq:psi s=phi s:=sub_eq_zero.mp (by simpa using hz)
 exact heq.symm
variable [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
def parameterDifference (phi:S →ₐ[K] K):S:=
 algebraMap (Polynomial K) S
   (Polynomial.X-Polynomial.C (phi (algebraMap (Polynomial K) S Polynomial.X)))
theorem parameterDifference_mem (phi:S →ₐ[K] K):
   parameterDifference phi∈pointKernel phi:=by
 have hconstant (c:K):
     algebraMap (Polynomial K) S (Polynomial.C c)=algebraMap K S c:=
   (IsScalarTower.algebraMap_apply K (Polynomial K) S c).symm
 simp [parameterDifference,hconstant]
theorem parameterDifference_ne_zero
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):parameterDifference phi≠0:=by
 intro hz
 apply Polynomial.X_sub_C_ne_zero (phi (algebraMap (Polynomial K) S Polynomial.X))
 apply hinj
 simpa only [parameterDifference,map_zero] using hz
theorem pointKernel_ne_bot
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):pointKernel phi≠⊥:=by
 intro hbot
 have hzero:parameterDifference phi=0:=by
   simpa [hbot] using parameterDifference_mem phi
 exact parameterDifference_ne_zero hinj phi hzero
end PointKernels
section ActualPlaces
variable {K S L:Type*} [Field K] [CommRing S] [IsDedekindDomain S]
 [Algebra K S] [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
def pointPlace (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):HeightOneSpectrum S:=
 ⟨pointKernel phi,pointKernel_isPrime phi,pointKernel_ne_bot hinj phi⟩
@[simp] theorem pointPlace_asIdeal
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):(pointPlace hinj phi).asIdeal=pointKernel phi:=rfl
theorem pointPlace_injective
   (hinj:Function.Injective (algebraMap (Polynomial K) S)):
   Function.Injective (pointPlace hinj:(S →ₐ[K] K) → HeightOneSpectrum S):=by
 intro phi psi h
 apply pointKernel_injective
 exact congrArg HeightOneSpectrum.asIdeal h
variable [Field L] [Algebra S L] [IsFractionRing S L]
theorem point_valuation_lt_one_iff
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K) (h:S):
   (pointPlace hinj phi).valuation L (algebraMap S L h) < 1 ↔ phi h=0:=by
 rw [HeightOneSpectrum.valuation_of_algebraMap]
 rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
 exact mem_pointKernel phi h
theorem point_zero_order_ge_one
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K) (h:S) (hne:h≠0) (hzero:phi h=0):
   1 ≤-((pointPlace hinj phi).valuation L (algebraMap S L h)).log:=by
 rw [HeightOneSpectrum.valuation_of_algebraMap]
 have hv0:=(pointPlace hinj phi).intValuation_ne_zero h hne
 have hvlt:(pointPlace hinj phi).intValuation h < 1:=
   ((pointPlace hinj phi).intValuation_lt_one_iff_mem h).2 hzero
 have hlog:((pointPlace hinj phi).intValuation h).log < (0:ℤ):=by
   simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
 omega
end ActualPlaces
section ConcreteNormalization
variable (K L:Type*) [Field K] [Field L]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev ActualNormalization:=FunctionField.ringOfIntegers K L
local instance normalizationScalarAlgebra:Algebra K (ActualNormalization K L):=
 ((algebraMap (Polynomial K) (ActualNormalization K L)).comp
   (Polynomial.C:K →+*Polynomial K)).toAlgebra
local instance normalizationScalarTower:
   IsScalarTower K (Polynomial K) (ActualNormalization K L):=
 IsScalarTower.of_algebraMap_eq (fun _ => rfl)
theorem actual_normalization_finite:
   Module.Finite (Polynomial K) (ActualNormalization K L):=
 IsIntegralClosure.finite (Polynomial K) (RatFunc K) L (ActualNormalization K L)
theorem actual_normalization_dedekind:IsDedekindDomain (ActualNormalization K L):=
 inferInstance
theorem actual_normalization_fractionField:IsFractionRing (ActualNormalization K L) L:=
 inferInstance
theorem actual_normalization_base_injective:
   Function.Injective (algebraMap (Polynomial K) (ActualNormalization K L)):=
 FunctionField.ringOfIntegers.algebraMap_injective K L
def normalizationPointPlace (phi:ActualNormalization K L →ₐ[K] K):
   HeightOneSpectrum (ActualNormalization K L):=
 pointPlace (actual_normalization_base_injective K L) phi
theorem normalizationPointPlace_injective:
   Function.Injective (normalizationPointPlace K L):=
 pointPlace_injective (actual_normalization_base_injective K L)
theorem normalization_point_zero_order_ge_one
   (phi:ActualNormalization K L →ₐ[K] K) (h:ActualNormalization K L)
   (hne:h≠0) (hzero:phi h=0):
   1 ≤-((normalizationPointPlace K L phi).valuation L
     (algebraMap (ActualNormalization K L) L h)).log:=
 point_zero_order_ge_one (L:=L) (actual_normalization_base_injective K L)
   phi h hne hzero
end ConcreteNormalization
end
end ProximityPrize.SubmissionLower.RCN017
end PackedLegacy_H4

/-! Packed from ProximityPrize.SubmissionLower.H3. -/
section PackedLegacy_H3
namespace ProximityPrize.SubmissionLower.RCN016
open IsDedekindDomain
noncomputable section
section Fractions
variable {S L:Type*} [CommRing S] [IsDedekindDomain S] [Field L]
 [Algebra S L] [IsFractionRing S L]
theorem base_value_lt_one_iff (p:HeightOneSpectrum S) (a:S):
   p.valuation L (algebraMap S L a) < 1 ↔ a∈p.asIdeal:=by
 rw [HeightOneSpectrum.valuation_of_algebraMap,
   HeightOneSpectrum.intValuation_lt_one_iff_mem]
theorem denominator_value_one (p:HeightOneSpectrum S) (b:S)
   (hb:b∉p.asIdeal):p.valuation L (algebraMap S L b)=1:=by
 apply le_antisymm
 · rw [HeightOneSpectrum.valuation_of_algebraMap]
   exact p.intValuation_le_one b
 · exact le_of_not_gt fun h => hb ((base_value_lt_one_iff p b).mp h)
theorem denominator_ne_zero (p:HeightOneSpectrum S) (b:S)
   (hb:b∉p.asIdeal):algebraMap S L b≠0:=by
 have hb0:b≠0:=fun h => hb (h ▸ p.asIdeal.zero_mem)
 simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0
theorem fraction_of_value_le_one (p:HeightOneSpectrum S) (x:L)
   (hx:p.valuation L x ≤ 1):
   ∃ a b:S,b∉p.asIdeal∧x*algebraMap S L b=algebraMap S L a:=by
 have hm:x∈HeightOneSpectrum.valuationSubringAtPrime L p:=by
   rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
   exact hx
 rcases hm with ⟨a,b,hb,rfl⟩
 refine ⟨a,b,hb,?_⟩
 simp [denominator_ne_zero p b hb]
end Fractions
section Overring
variable {K S B L:Type*} [Field K] [CommRing S] [IsDedekindDomain S]
 [CommRing B] [Field L]
 [Algebra S B] [Algebra S L] [Algebra B L] [IsScalarTower S B L]
 [IsFractionRing S L]
variable (hinj:Function.Injective (algebraMap B L))
 (p:HeightOneSpectrum S) (Φ:B →+*K)
 (hker:RingHom.ker (Φ.comp (algebraMap S B))=p.asIdeal)
include hker in
theorem base_point_zero_iff (a:S):
   Φ (algebraMap S B a)=0 ↔ a∈p.asIdeal:=by
 rw [←hker]
 rfl
include hinj
theorem lift_multiplication (x:B) (a b:S)
   (h:algebraMap B L x*algebraMap S L a=algebraMap S L b):
   x*algebraMap S B a=algebraMap S B b:=by
 apply hinj
 simpa only [map_mul, ←IsScalarTower.algebraMap_apply S B L] using h
theorem inverse_fraction (x:B)
   (hx:1 ≤ p.valuation L (algebraMap B L x)):
   ∃ a b:S,b∉p.asIdeal∧
     x*algebraMap S B a=algebraMap S B b∧
     p.valuation L (algebraMap S L a)=
       (p.valuation L (algebraMap B L x))⁻¹:=by
 have hv0:p.valuation L (algebraMap B L x)≠0:=
   ne_of_gt (zero_lt_one.trans_le hx)
 have hx0:algebraMap B L x≠0:=(Valuation.ne_zero_iff _).mp hv0
 have hi:p.valuation L ((algebraMap B L x)⁻¹) ≤ 1:=by
   rw [map_inv₀]
   exact inv_le_one_of_one_le₀ hx
 obtain ⟨a,b,hb,hab⟩:=fraction_of_value_le_one p ((algebraMap B L x)⁻¹) hi
 have hmul:algebraMap B L x*algebraMap S L a=algebraMap S L b:=by
   rw [←hab, ←mul_assoc,mul_inv_cancel₀ hx0,one_mul]
 have hval:p.valuation L (algebraMap S L a)=
     (p.valuation L (algebraMap B L x))⁻¹:=by
   rw [←hab,map_mul,map_inv₀,denominator_value_one p b hb,mul_one]
 exact ⟨a,b,hb,lift_multiplication hinj x a b hmul,hval⟩
include hker in
theorem overring_value_le_one (x:B):
   p.valuation L (algebraMap B L x) ≤ 1:=by
 by_contra h
 have hx:1 < p.valuation L (algebraMap B L x):=lt_of_not_ge h
 obtain ⟨a,b,hb,hmul,hval⟩:=inverse_fraction hinj p x hx.le
 have ha:a∈p.asIdeal:=(base_value_lt_one_iff p a).mp (by
   rw [hval]
   exact inv_lt_one_of_one_lt₀ hx)
 have hzero:=(base_point_zero_iff p Φ hker a).mpr ha
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ hmul
 rw [map_mul,hzero,mul_zero] at heq
 exact hnonzero heq.symm
include hker in
theorem overring_value_lt_one_of_point_zero (x:B) (hzero:Φ x=0):
   p.valuation L (algebraMap B L x) < 1:=by
 by_contra h
 obtain ⟨a,b,hb,hmul,_⟩:=inverse_fraction hinj p x (le_of_not_gt h)
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ hmul
 rw [map_mul,hzero,zero_mul] at heq
 exact hnonzero heq.symm
include hker in
theorem point_zero_of_overring_value_lt_one (x:B)
   (hx:p.valuation L (algebraMap B L x) < 1):Φ x=0:=by
 obtain ⟨a,b,hb,hab⟩:=fraction_of_value_le_one p (algebraMap B L x) hx.le
 have hval:p.valuation L (algebraMap S L a) < 1:=by
   rw [←hab,map_mul,denominator_value_one p b hb,mul_one]
   exact hx
 have ha:=(base_value_lt_one_iff p a).mp hval
 have hzero:=(base_point_zero_iff p Φ hker a).mpr ha
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ (lift_multiplication hinj x b a hab)
 rw [map_mul,hzero] at heq
 exact (mul_eq_zero.mp heq).resolve_right hnonzero
include hker in
theorem overring_value_lt_one_iff (x:B):
   p.valuation L (algebraMap B L x) < 1 ↔ Φ x=0:=
 ⟨point_zero_of_overring_value_lt_one hinj p Φ hker x,
   overring_value_lt_one_of_point_zero hinj p Φ hker x⟩
include hker in
theorem overring_zero_order_ge_one (x:B) (hx:x≠0) (hzero:Φ x=0):
   1 ≤-(p.valuation L (algebraMap B L x)).log:=by
 have hv0:p.valuation L (algebraMap B L x)≠0:=
   (Valuation.ne_zero_iff _).mpr (by
     simpa only [map_zero] using hinj.ne hx)
 have hvlt:=overring_value_lt_one_of_point_zero hinj p Φ hker x hzero
 have hlog:(p.valuation L (algebraMap B L x)).log < (0:ℤ):=by
   simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
 omega
end Overring
end
end ProximityPrize.SubmissionLower.RCN016
end PackedLegacy_H3

/-! Packed from ProximityPrize.SubmissionLower.H2. -/
section PackedLegacy_H2
namespace ProximityPrize.SubmissionLower.RCN015
open IsDedekindDomain RCN017 RCN016
noncomputable section
abbrev ModelClosure (A L:Type*) [CommRing A] [Field L] [Algebra A L]:=
 integralClosure A L
section Construction
variable {K S A L:Type*} [Field K] [IsAlgClosed K]
 [CommRing S] [IsDedekindDomain S] [CommRing A] [Field L]
 [Algebra K S] [Algebra K A] [Algebra K L]
 [Algebra (Polynomial K) S] [Algebra (Polynomial K) A] [Algebra (Polynomial K) L]
 [Algebra S L] [Algebra A L]
 [IsScalarTower K (Polynomial K) S] [IsScalarTower K (Polynomial K) A]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K S L] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) S L] [IsScalarTower (Polynomial K) A L]
 [IsFractionRing S L] [Algebra.IsIntegral (Polynomial K) S]
def inclusionToModelClosure:S →ₐ[K] ModelClosure A L where
 toFun s:=⟨algebraMap S L s,by
   have hs:IsIntegral (Polynomial K) (algebraMap S L s):=
     (Algebra.IsIntegral.isIntegral (R:=Polynomial K) s).map
       (IsScalarTower.toAlgHom (Polynomial K) S L)
   exact hs.tower_top⟩
 map_zero':=Subtype.ext (map_zero _)
 map_one':=Subtype.ext (map_one _)
 map_add' a b:=Subtype.ext (map_add _ a b)
 map_mul' a b:=Subtype.ext (map_mul _ a b)
 commutes' c:=by
   apply Subtype.ext
   change algebraMap S L (algebraMap K S c)=algebraMap K L c
   exact (IsScalarTower.algebraMap_apply K S L c).symm
theorem modelClosure_base_injective
   (hinj:Function.Injective (algebraMap A L)):
   Function.Injective (algebraMap A (ModelClosure A L)):=by
 intro a b h
 apply hinj
 exact congrArg (fun x:ModelClosure A L => (x:L)) h
theorem modelClosure_embedding_injective:
   Function.Injective (algebraMap (ModelClosure A L) L):=
 Subtype.val_injective
def modelClosurePoint (hinj:Function.Injective (algebraMap A L))
   (φ:A →ₐ[K] K):ModelClosure A L →ₐ[K] K:=
 RCN354.chosenPointLift (modelClosure_base_injective hinj) φ
theorem modelClosurePoint_restrict
   (hinj:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   modelClosurePoint hinj φ (algebraMap A (ModelClosure A L) a)=φ a:=
 AlgHom.congr_fun
   (RCN354.chosenPointLift_spec (modelClosure_base_injective hinj) φ) a
def modelPointPlace
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K):
   HeightOneSpectrum S:=
 pointPlace hS ((modelClosurePoint hA φ).comp
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)))
theorem modelPointPlace_kernel
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K):
   RingHom.ker ((modelClosurePoint hA φ).toRingHom.comp
     (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom)=
     (modelPointPlace hS hA φ).asIdeal:=rfl
theorem model_value_le_one
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   (modelPointPlace hS hA φ).valuation L (algebraMap A L a) ≤ 1:=by
 letI:Algebra S (ModelClosure A L):=
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom.toAlgebra
 letI:IsScalarTower S (ModelClosure A L) L:=
   IsScalarTower.of_algebraMap_eq (fun _ => rfl)
 have h:=overring_value_le_one (L:=L) modelClosure_embedding_injective
   (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
   (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
 simpa only [←IsScalarTower.algebraMap_apply A (ModelClosure A L) L] using h
theorem model_value_lt_one_iff
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   (modelPointPlace hS hA φ).valuation L (algebraMap A L a) < 1 ↔ φ a=0:=by
 letI:Algebra S (ModelClosure A L):=
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom.toAlgebra
 letI:IsScalarTower S (ModelClosure A L) L:=
   IsScalarTower.of_algebraMap_eq (fun _ => rfl)
 have h:=overring_value_lt_one_iff (L:=L) modelClosure_embedding_injective
   (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
   (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
 simpa only [←IsScalarTower.algebraMap_apply A (ModelClosure A L) L,
   AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,modelClosurePoint_restrict] using h
theorem modelPointPlace_injective
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)):
   Function.Injective (modelPointPlace hS hA:(A →ₐ[K] K) → HeightOneSpectrum S):=by
 intro φ ψ h
 apply RCN017.pointKernel_injective
 apply Ideal.ext
 intro a
 change φ a=0 ↔ ψ a=0
 rw [←model_value_lt_one_iff hS hA φ a, ←model_value_lt_one_iff hS hA ψ a,h]
theorem model_zero_order_ge_one
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K)
   (a:A) (ha:a≠0) (hzero:φ a=0):
   1 ≤-((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log:=by
 have hv0:(modelPointPlace hS hA φ).valuation L (algebraMap A L a)≠0:=
   (Valuation.ne_zero_iff _).mpr (by simpa only [map_zero] using hA.ne ha)
 have hvlt:=(model_value_lt_one_iff hS hA φ a).mpr hzero
 have hlog:((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log < (0:ℤ):=by
   simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
 omega
end Construction
end
end ProximityPrize.SubmissionLower.RCN015
end PackedLegacy_H2

/-! Packed from ProximityPrize.SubmissionLower.G8. -/
section PackedLegacy_G8
namespace ProximityPrize.SubmissionLower.RCN000
open IsDedekindDomain
noncomputable section
variable (K A L:Type*) [Field K] [IsAlgClosed K]
 [CommRing A] [IsDomain A] [Field L]
 [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev Normalization:=FunctionField.ringOfIntegers K L
def actualPointPlace (φ:A →ₐ[K] K):HeightOneSpectrum (Normalization K L):=
 RCN015.modelPointPlace
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ
theorem actualPointPlace_injective:
   Function.Injective (actualPointPlace K A L):=
 RCN015.modelPointPlace_injective
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L)
theorem actual_model_value_le_one (φ:A →ₐ[K] K) (a:A):
   (actualPointPlace K A L φ).valuation L (algebraMap A L a) ≤ 1:=
 RCN015.model_value_le_one
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a
theorem actual_model_value_lt_one_iff (φ:A →ₐ[K] K) (a:A):
   (actualPointPlace K A L φ).valuation L (algebraMap A L a) < 1 ↔ φ a=0:=
 RCN015.model_value_lt_one_iff
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a
theorem actual_model_zero_order_ge_one
   (φ:A →ₐ[K] K) (a:A) (ha:a≠0) (hzero:φ a=0):
   1 ≤-((actualPointPlace K A L φ).valuation L (algebraMap A L a)).log:=
 RCN015.model_zero_order_ge_one
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a ha hzero
end
end ProximityPrize.SubmissionLower.RCN000
end PackedLegacy_G8

/-! Packed from ProximityPrize.SubmissionLower.R0. -/
section PackedLegacy_R0
namespace ProximityPrize.SubmissionLower.RCN344
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
structure SeparableCoordinate where
 embedding:RatFunc K →ₐ[K] L
 finite:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L
 separable:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc K) L
namespace SeparableCoordinate
def value (c:SeparableCoordinate K L):L:=
 c.embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
def degree (c:SeparableCoordinate K L):ℕ:=
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 Module.finrank (RatFunc K) L
variable [IsAlgClosed K]
theorem finite_sum_pole_le_degree (c:SeparableCoordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (value K L c)) ≤
     (degree K L c:ℤ):=by
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 letI:Algebra (Polynomial K) L:=
   (c.embedding.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
 letI:IsScalarTower (Polynomial K) (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦(c.embedding.commutes a).symm
 letI:IsScalarTower K (Polynomial K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦by
     change algebraMap K L a=
       c.embedding (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) a))
     rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
     exact (c.embedding.commutes a).symm
 letI:FiniteDimensional (RatFunc K) L:=c.finite
 letI:Algebra.IsSeparable (RatFunc K) L:=c.separable
 exact RCN346.finite_sum_pole_le_finrank K L W
end SeparableCoordinate
abbrev Coordinate:=K ⊕ SeparableCoordinate K L
def coordinateValue:Coordinate K L → L:=
 Sum.elim (algebraMap K L) (SeparableCoordinate.value K L)
def coordinateDegree:Coordinate K L → ℕ:=
 Sum.elim (fun _↦0) (SeparableCoordinate.degree K L)
theorem constant_value_le_one (v:Place K L) (c:K):
   v.val (algebraMap K L c) ≤ 1:=by
 letI:v.val.IsTrivialOn K:=v.property.2
 exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val c
variable [IsAlgClosed K]
theorem finite_sum_coordinate_pole_le_degree (c:Coordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L c)) ≤
     (coordinateDegree K L c:ℤ):=by
 rcases c with a | c
 · have hz:∀ v:Place K L,
       RCN346.poleOrder K L v (algebraMap K L a)=0:=
     fun v↦RCN346.poleOrder_eq_zero_of_le_one K L v _
       (constant_value_le_one K L v a)
   simp only [coordinateValue,coordinateDegree,Sum.elim_inl,hz,Finset.sum_const_zero,
     Nat.cast_zero,le_refl]
 · exact SeparableCoordinate.finite_sum_pole_le_degree K L c W
variable {σ:Type*} [Fintype σ]
theorem finite_sum_polynomial_pole_le_box (W:Finset (Place K L))
   (c:σ → Coordinate K L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ v∈W,RCN346.poleOrder K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)) ≤
     ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 have hlocal:=RCN187.weighted_poleOrder_eval_le_box
   W (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ a↦constant_value_le_one K L v a)
   (fun i↦coordinateValue K L (c i)) cap F hcap
 simp only [Nat.cast_one,one_mul] at hlocal
 calc
   _ ≤ ∑ i,(cap i:ℤ)*
       ∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L (c i)):=hlocal
   _ ≤ _:=by
     apply Finset.sum_le_sum
     intro i _
     exact mul_le_mul_of_nonneg_left
       (finite_sum_coordinate_pole_le_degree K L (c i) W) (Int.natCast_nonneg _)
section FixedSeparator
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
theorem finite_zero_places_le_box (c:σ → Coordinate K L)
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F≠0)
   (U:Finset (Place K L))
   (hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)):
   (U.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 exact (RCN026.finite_zero_places_le_poleMass K L _ hF U hU).trans
   (finite_sum_polynomial_pole_le_box K L _ c cap F hcap)
section AffineModel
variable (A:Type*) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
def modelPlace (φ:A →ₐ[K] K):Place K L:=
 RCN345.chartMap K L
   (Sum.inl (RCN000.actualPointPlace K A L φ))
theorem modelPlace_injective:Function.Injective (modelPlace K L A):=by
 intro φ ψ h
 have hchart:=(RCN345.chartMap_bijective K L).1 h
 exact RCN000.actualPointPlace_injective K A L (Sum.inl.inj hchart)
theorem map_model_eval (x:σ → A) (F:MvPolynomial σ K):
   algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)) F:=by
 have hhom:(algebraMap A L).comp (MvPolynomial.eval₂Hom (algebraMap K A) x)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)):=by
   ext a
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     exact (IsScalarTower.algebraMap_apply K A L a).symm
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
 exact DFunLike.congr_fun hhom F
theorem finite_model_zero_points_le_box
   (x:σ → A) (c:σ → Coordinate K L)
   (hc:∀ i,coordinateValue K L (c i)=algebraMap A L (x i))
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (S:Finset (A →ₐ[K] K))
   (hS:∀ φ∈S,φ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=by
   simp_rw [hc]
   exact (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F):=by
   intro v hv
   obtain ⟨φ,hφ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one K A L φ _ hF (hS φ hφ)
 have h:=finite_zero_places_le_box K L c cap F hcap hnonzero U hU
 have hcard:U.card=S.card:=Finset.card_image_of_injective _ (modelPlace_injective K L A)
 rwa [hcard] at h
end AffineModel
end FixedSeparator
end
end ProximityPrize.SubmissionLower.RCN344
end PackedLegacy_R0

/-! Packed from ProximityPrize.SubmissionLower.L. -/
section PackedLegacy_L
namespace ProximityPrize.SubmissionLower.RCN002
noncomputable section
abbrev CoordinateRing (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=MvPolynomial (Fin 3) K ⧸ P
abbrev CoordinateField (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=FractionRing (CoordinateRing K P)
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def coordinateEvaluation:MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mkₐ K P)
def coordinate (i:Fin 3):CoordinateField K P:=
 coordinateEvaluation K P (MvPolynomial.X i)
theorem coordinateEvaluation_eq_aeval:
   coordinateEvaluation K P=MvPolynomial.aeval (coordinate K P):=
 MvPolynomial.aeval_unique (coordinateEvaluation K P)
theorem aeval_coordinate_eq_quotient (f:MvPolynomial (Fin 3) K):
   MvPolynomial.aeval (coordinate K P) f=
     algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P f):=by
 rw [←coordinateEvaluation_eq_aeval]
 rfl
theorem coordinateEvaluation_ker:
   RingHom.ker (coordinateEvaluation K P).toRingHom=P:=by
 change RingHom.ker ((algebraMap (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mk P))=P
 rw [RingHom.ker_comp_of_injective _
   (IsFractionRing.injective (CoordinateRing K P) (CoordinateField K P)),Ideal.mk_ker]
theorem aeval_coordinate_ker:
   RingHom.ker (MvPolynomial.aeval (coordinate K P)).toRingHom=P:=by
 rw [←coordinateEvaluation_eq_aeval]
 exact coordinateEvaluation_ker K P
theorem adjoin_coordinates_eq_top:
   IntermediateField.adjoin K (Set.range (coordinate K P))=⊤:=by
 apply top_unique
 intro x _
 obtain ⟨a,b,_,hab⟩:=
   IsFractionRing.div_surjective (CoordinateRing K P) x
 obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective a
 obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective b
 apply (IntermediateField.mem_adjoin_range_iff K (coordinate K P) x).mpr
 refine ⟨f,g,?_⟩
 rw [aeval_coordinate_eq_quotient,aeval_coordinate_eq_quotient]
 exact hab.symm
section AlgebraicallyClosed
variable [IsAlgClosed K]
theorem coordinate_eq_scalar_of_isAlgebraic (i:Fin 3)
   (h:IsAlgebraic K (coordinate K P i)):
   ∃ c:K,algebraMap K (CoordinateField K P) c=coordinate K P i:=by
 let S:IntermediateField K (CoordinateField K P):=
   IntermediateField.adjoin K {coordinate K P i}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple h.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨coordinate K P i,IntermediateField.mem_adjoin_simple_self K _⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S (CoordinateField K P)) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
theorem eq_point_kernel_of_coordinates_algebraic
   (h:∀ i,IsAlgebraic K (coordinate K P i)):
   ∃ v:Fin 3 → K,P=RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 choose v hv using fun i => coordinate_eq_scalar_of_isAlgebraic K P i (h i)
 have heval:coordinateEvaluation K P=
     (IsScalarTower.toAlgHom K K (CoordinateField K P)).comp (MvPolynomial.aeval v):=by
   apply MvPolynomial.algHom_ext
   intro i
   simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]
   change coordinate K P i=algebraMap K (CoordinateField K P) (v i)
   exact (hv i).symm
 refine ⟨v,?_⟩
 calc
   P=RingHom.ker (coordinateEvaluation K P).toRingHom:=
     (coordinateEvaluation_ker K P).symm
   _=RingHom.ker ((algebraMap K (CoordinateField K P)).comp
       (MvPolynomial.aeval v).toRingHom):=by rw [heval];rfl
   _=RingHom.ker (MvPolynomial.aeval v).toRingHom:=
     RingHom.ker_comp_of_injective _ (algebraMap K (CoordinateField K P)).injective
theorem exists_transcendental_coordinate_of_ne_point_kernel
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   ∃ i:Fin 3,Transcendental K (coordinate K P i):=by
 classical
 by_contra hnone
 have halg:∀ i,IsAlgebraic K (coordinate K P i):=by
   intro i
   by_contra hi
   exact hnone ⟨i,hi⟩
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic K P halg
 exact hnonpoint v hv
end AlgebraicallyClosed
end
end ProximityPrize.SubmissionLower.RCN002
end PackedLegacy_L

/-! Packed from ProximityPrize.SubmissionLower.Z. -/
section PackedLegacy_Z
namespace ProximityPrize.SubmissionLower.RCN005
open RCN002
noncomputable section
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def rationalBaseEmbedding (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   RatFunc K →ₐ[K] CoordinateField K P:=
 RatFunc.liftAlgHom (Polynomial.aeval (coordinate K P i))
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval (coordinate K P i)).toRingHom
     (transcendental_iff_injective.mp hi))
theorem rationalBaseEmbedding_injective (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   Function.Injective (rationalBaseEmbedding K P i hi):=
 (rationalBaseEmbedding K P i hi).injective
theorem rationalBaseEmbedding_polynomial (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)) (f:Polynomial K):
   rationalBaseEmbedding K P i hi (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval (coordinate K P i) f:=by
 exact RatFunc.liftRingHom_algebraMap _ _ f
abbrev rationalBaseAlgebra (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   Algebra (RatFunc K) (CoordinateField K P):=
 (rationalBaseEmbedding K P i hi).toRingHom.toAlgebra
theorem rationalBaseScalarTower (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower K (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((rationalBaseEmbedding K P i hi).commutes c).symm
theorem rational_variable_image (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i:=by
 change rationalBaseEmbedding K P i hi
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i
 rw [rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
theorem adjoin_two_coordinates_over_ratFunc_eq_top
   (i j k:Fin 3) (hi:Transcendental K (coordinate K P i))
   (hcover:∀ l:Fin 3,l=i∨l=j∨l=k):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P j,coordinate K P k}:Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   rationalBaseScalarTower K P i hi
 let S:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K) {coordinate K P j,coordinate K P k}
 have hcoords:Set.range (coordinate K P) ⊆ S.restrictScalars K:=by
   rintro x ⟨l,rfl⟩
   rcases hcover l with hl | hl | hl
   · subst l
     have hmem:=S.algebraMap_mem
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
     rw [rational_variable_image K P i hi] at hmem
     exact hmem
   · subst l
     exact IntermediateField.mem_adjoin_pair_left (RatFunc K)
       (coordinate K P j) (coordinate K P k)
   · subst l
     exact IntermediateField.mem_adjoin_pair_right (RatFunc K)
       (coordinate K P j) (coordinate K P k)
 have htop:S.restrictScalars K=⊤:=by
   apply top_unique
   rw [←adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
theorem exists_complementary_coordinates (i:Fin 3):
   ∃ j k:Fin 3,j≠i∧k≠i∧j≠k∧
     ∀ l:Fin 3,l=i∨l=j∨l=k:=by
 fin_cases i <;> decide
theorem exists_two_generators_over_ratFunc (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   ∃ j k:Fin 3,j≠i∧k≠i∧j≠k∧
     IntermediateField.adjoin (RatFunc K)
       ({coordinate K P j,coordinate K P k}:Set (CoordinateField K P))=⊤:=by
 obtain ⟨j,k,hji,hki,hjk,hcover⟩:=exists_complementary_coordinates i
 exact ⟨j,k,hji,hki,hjk,
   adjoin_two_coordinates_over_ratFunc_eq_top K P i j k hi hcover⟩
end
end ProximityPrize.SubmissionLower.RCN005
end PackedLegacy_Z

/-! Packed from ProximityPrize.SubmissionLower.H0. -/
section PackedLegacy_H0
namespace ProximityPrize.SubmissionLower.RCN006
open RCN002 RCN005
noncomputable section
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
abbrev polynomialBaseAlgebra (i:Fin 3):
   Algebra (Polynomial K) (CoordinateField K P):=
 (Polynomial.aeval (coordinate K P i)).toRingHom.toAlgebra
theorem polynomial_algebraMap_eq (i:Fin 3) (f:Polynomial K):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   algebraMap (Polynomial K) (CoordinateField K P) f=
     Polynomial.aeval (coordinate K P i) f:=rfl
theorem polynomialBaseScalarTower (i:Fin 3):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   IsScalarTower K (Polynomial K) (CoordinateField K P):=by
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((Polynomial.aeval (coordinate K P i)).commutes c).symm
theorem polynomialBase_injective (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   Function.Injective (algebraMap (Polynomial K) (CoordinateField K P)):=
 transcendental_iff_injective.mp hi
theorem polynomial_variable_image (i:Fin 3):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   algebraMap (Polynomial K) (CoordinateField K P) Polynomial.X=coordinate K P i:=by
 exact Polynomial.aeval_X _
theorem polynomialRationalScalarTower (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 exact IsScalarTower.of_algebraMap_eq fun f =>
   (rationalBaseEmbedding_polynomial K P i hi f).symm
theorem actual_scalar_towers (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower K (Polynomial K) (CoordinateField K P)∧
     IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P)∧
     IsScalarTower K (RatFunc K) (CoordinateField K P):=by
 exact ⟨polynomialBaseScalarTower K P i,
   polynomialRationalScalarTower K P i hi,rationalBaseScalarTower K P i hi⟩
def quotientCoordinate (i:Fin 3):CoordinateRing K P:=
 Ideal.Quotient.mk P (MvPolynomial.X i)
abbrev quotientPolynomialAlgebra (i:Fin 3):
   Algebra (Polynomial K) (CoordinateRing K P):=
 (Polynomial.aeval (quotientCoordinate K P i)).toRingHom.toAlgebra
theorem quotientBaseScalarTower (i:Fin 3):
   letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
   IsScalarTower K (Polynomial K) (CoordinateRing K P):=by
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((Polynomial.aeval (quotientCoordinate K P i)).commutes c).symm
theorem quotientCoordinate_fraction (i:Fin 3):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i)=
     coordinate K P i:=rfl
theorem quotient_polynomial_fraction (i:Fin 3) (f:Polynomial K):
   algebraMap (CoordinateRing K P) (CoordinateField K P)
       (Polynomial.aeval (quotientCoordinate K P i) f)=
     Polynomial.aeval (coordinate K P i) f:=by
 have hhom:
     (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
         (Polynomial.aeval (quotientCoordinate K P i))=
       Polynomial.aeval (coordinate K P i):=by
   apply Polynomial.algHom_ext
   simp only [AlgHom.comp_apply,Polynomial.aeval_X]
   rfl
 exact AlgHom.congr_fun hhom f
theorem quotientFractionScalarTower (i:Fin 3):
   @IsScalarTower (Polynomial K) (CoordinateRing K P) (CoordinateField K P)
     (quotientPolynomialAlgebra K P i).toSMul
     (inferInstance:Algebra (CoordinateRing K P) (CoordinateField K P)).toSMul
     (polynomialBaseAlgebra K P i).toSMul:=by
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun f =>
   (quotient_polynomial_fraction K P i f).symm
theorem quotientBase_injective (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
   Function.Injective (algebraMap (Polynomial K) (CoordinateRing K P)):=by
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
 intro f g hfg
 apply transcendental_iff_injective.mp hi
 rw [←quotient_polynomial_fraction K P i f, ←quotient_polynomial_fraction K P i g]
 exact congrArg (algebraMap (CoordinateRing K P) (CoordinateField K P)) hfg
end
end ProximityPrize.SubmissionLower.RCN006
end PackedLegacy_H0

/-! Packed from ProximityPrize.SubmissionLower.M. -/
section PackedLegacy_M
namespace ProximityPrize.SubmissionLower.RCN007
open scoped Classical BigOperators
open RCN002 RCN005 RCN006
noncomputable section
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
abbrev PointOn:=
 {v:Fin 3 → K//P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom}
def pointHom (v:PointOn K P):CoordinateRing K P →ₐ[K] K:=
 Ideal.Quotient.liftₐ P (MvPolynomial.aeval v.1) (fun F hF↦v.2 hF)
theorem pointHom_mk (v:PointOn K P) (F:MvPolynomial (Fin 3) K):
   pointHom K P v (Ideal.Quotient.mk P F)=MvPolynomial.aeval v.1 F:=rfl
theorem pointHom_coordinate (v:PointOn K P) (i:Fin 3):
   pointHom K P v (quotientCoordinate K P i)=v.1 i:=by
 rw [quotientCoordinate,pointHom_mk,MvPolynomial.aeval_X]
theorem pointHom_injective:Function.Injective (pointHom K P):=by
 intro v w h
 apply Subtype.ext
 funext i
 have hi:=DFunLike.congr_fun h (quotientCoordinate K P i)
 simpa only [pointHom_coordinate] using hi
theorem quotient_eval_eq_mk (F:MvPolynomial (Fin 3) K):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
     (quotientCoordinate K P) F=Ideal.Quotient.mk P F:=by
 have hhom:MvPolynomial.aeval (quotientCoordinate K P)=Ideal.Quotient.mkₐ K P:=by
   apply MvPolynomial.algHom_ext
   intro i
   rw [MvPolynomial.aeval_X]
   rfl
 exact AlgHom.congr_fun hhom F
theorem quotient_eval_ne_zero_of_not_mem (F:MvPolynomial (Fin 3) K) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
     (quotientCoordinate K P) F≠0:=by
 rw [quotient_eval_eq_mk]
 intro hzero
 exact hF (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
theorem field_eval_ne_zero_iff (F:MvPolynomial (Fin 3) K):
   MvPolynomial.aeval (coordinate K P) F≠0 ↔ F∉P:=by
 change ¬ F∈RingHom.ker (MvPolynomial.aeval (coordinate K P)).toRingHom ↔ F∉P
 rw [aeval_coordinate_ker]
def ProjectionsFiniteSeparable:Prop:=
 ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
def actualCoordinateDegree (i:Fin 3):ℕ:=
 if hi:Transcendental K (coordinate K P i) then
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   Module.finrank (RatFunc K) (CoordinateField K P)
 else 0
theorem actualCoordinateDegree_of_transcendental (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   actualCoordinateDegree K P i=
     (letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
      Module.finrank (RatFunc K) (CoordinateField K P)):=by
 simp only [actualCoordinateDegree,dif_pos hi]
theorem actualCoordinateDegree_of_isAlgebraic (i:Fin 3)
   (hi:IsAlgebraic K (coordinate K P i)):actualCoordinateDegree K P i=0:=by
 exact dif_neg (not_not.mpr hi)
variable [IsAlgClosed K]
def coordinateData (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.Coordinate K (CoordinateField K P):=
 if hi:Transcendental K (coordinate K P i) then
   Sum.inr {
     embedding:=rationalBaseEmbedding K P i hi
     finite:=(hproj i hi).1
     separable:=(hproj i hi).2}
 else
   Sum.inl ((coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose)
theorem coordinateData_value (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.coordinateValue K (CoordinateField K P)
     (coordinateData K P hproj i)=coordinate K P i:=by
 unfold coordinateData
 split_ifs with hi
 · exact rational_variable_image K P i hi
 · exact (coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose_spec
theorem coordinateData_degree (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.coordinateDegree K (CoordinateField K P)
     (coordinateData K P hproj i)=actualCoordinateDegree K P i:=by
 unfold coordinateData actualCoordinateDegree
 split_ifs <;> rfl
theorem finite_zero_points_le_box_of_separator
   (hproj:ProjectionsFiniteSeparable K P)
   (i₀:Fin 3) (hi₀:Transcendental K (coordinate K P i₀))
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3 → ℕ) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(actualCoordinateDegree K P i:ℤ):=by
 classical
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=(hproj i₀ hi₀).1
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=(hproj i₀ hi₀).2
 let c:=coordinateData K P hproj
 have hc:∀ i,RCN344.coordinateValue K (CoordinateField K P) (c i)=
     algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i):=by
   intro i
   rw [quotientCoordinate_fraction]
   exact coordinateData_value K P hproj i
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w h
   have hvw:=pointHom_injective K P h
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) hvw
 let points:=S.attach.image liftPoint
 have hpoints:∀ φ∈points,φ (MvPolynomial.eval₂Hom
     (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F)=0:=by
   intro φ hφ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hφ
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hcount:=RCN344.finite_model_zero_points_le_box
   K (CoordinateField K P) (CoordinateRing K P) (quotientCoordinate K P)
   c hc cap F hcap (quotient_eval_ne_zero_of_not_mem K P F hF) points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rw [hcard] at hcount
 simpa only [c,coordinateData_degree] using hcount
theorem finite_zero_points_le_box
   (hproj:ProjectionsFiniteSeparable K P)
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3 → ℕ) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(actualCoordinateDegree K P i:ℤ):=by
 obtain ⟨i,hi⟩:=exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
 exact finite_zero_points_le_box_of_separator K P hproj i hi F hF cap hcap S hSP hSF
end
end ProximityPrize.SubmissionLower.RCN007
end PackedLegacy_M

/-! Packed from ProximityPrize.SubmissionLower.S6. -/
section PackedLegacy_S6
section ProximityFlatProofPort
variable {α β:Type*} {rα:α → α → Prop} {rβ:β → β → Prop} {a:α} {b:β}
namespace Prod
variable (rα rβ)
inductive GameAdd:α × β → α × β → Prop
 | fst {a₁ a₂ b}:rα a₁ a₂ → GameAdd (a₁,b) (a₂,b)
 | snd {a b₁ b₂}:rβ b₁ b₂ → GameAdd (a,b₁) (a,b₂)
theorem gameAdd_iff {rα rβ} {x y:α × β}:
   GameAdd rα rβ x y ↔ rα x.1 y.1∧x.2=y.2∨rβ x.2 y.2∧x.1=y.1:=by
 constructor
 · rintro (@⟨a₁,a₂,b,h⟩ | @⟨a,b₁,b₂,h⟩)
   exacts [Or.inl ⟨h,rfl⟩,Or.inr ⟨h,rfl⟩]
 · revert x y
   rintro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ (⟨h,rfl:b₁=b₂⟩ | ⟨h,rfl:a₁=a₂⟩)
   exacts [GameAdd.fst h,GameAdd.snd h]
theorem gameAdd_mk_iff {rα rβ} {a₁ a₂:α} {b₁ b₂:β}:
   GameAdd rα rβ (a₁,b₁) (a₂,b₂) ↔ rα a₁ a₂∧b₁=b₂∨rβ b₁ b₂∧a₁=a₂:=
 gameAdd_iff
@[simp]
theorem gameAdd_swap_swap:∀ a b:α × β,GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b:=
 fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ => by rw [Prod.swap,Prod.swap,gameAdd_mk_iff,gameAdd_mk_iff,or_comm]
theorem gameAdd_swap_swap_mk (a₁ a₂:α) (b₁ b₂:β):
   GameAdd rα rβ (a₁,b₁) (a₂,b₂) ↔ GameAdd rβ rα (b₁,a₁) (b₂,a₂):=
 gameAdd_swap_swap rβ rα (b₁,a₁) (b₂,a₂)
theorem gameAdd_le_lex:GameAdd rα rβ ≤ Prod.Lex rα rβ:=fun _ _ h =>
 h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)
theorem rprod_le_transGen_gameAdd:RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ)
 | _,_,h => h.rec (by
     intro _ _ _ _ hα hβ
     exact Relation.TransGen.tail (Relation.TransGen.single <| GameAdd.fst hα) (GameAdd.snd hβ))
end Prod
theorem Acc.prod_gameAdd (ha:Acc rα a) (hb:Acc rβ b):
   Acc (Prod.GameAdd rα rβ) (a,b):=by
 induction ha generalizing b with | _ a _ iha
 induction hb with | _ b hb ihb
 refine Acc.intro _ fun h => ?_
 rintro (⟨ra⟩ | ⟨rb⟩)
 exacts [iha _ ra (Acc.intro b hb),ihb _ rb]
theorem WellFounded.prod_gameAdd (hα:WellFounded rα) (hβ:WellFounded rβ):
   WellFounded (Prod.GameAdd rα rβ):=
 ⟨fun ⟨a,b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩
namespace Prod
@[elab_as_elim]
def GameAdd.recursion {C:α → β → Sort*} (hα:WellFounded rα) (hβ:WellFounded rβ)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a:α) (b:β):
   C a b:=
 @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
   (fun ⟨x₁,x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a',b'⟩) ⟨a,b⟩
@[deprecated (since:="2026-03-13")] alias GameAdd.fix:=GameAdd.recursion
theorem GameAdd.recursion_eq {C:α → β → Sort*} (hα:WellFounded rα) (hβ:WellFounded rβ)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a:α) (b:β):
   GameAdd.recursion hα hβ IH a b=IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b':=
 WellFounded.fix_eq _ _ _
@[deprecated (since:="2026-03-13")] alias GameAdd.fix_eq:=GameAdd.recursion_eq
@[deprecated GameAdd.recursion (since:="2026-03-13")]
theorem GameAdd.induction {C:α → β → Prop}:
   WellFounded rα →
     WellFounded rβ →
       (∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b,C a b:=
 GameAdd.recursion
end Prod
namespace Sym2
def GameAdd (rα:α → α → Prop):Sym2 α → Sym2 α → Prop:=
 Sym2.lift₂
   ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)∨Prod.GameAdd rα rα (b₁,a₁) (a₂,b₂),
     fun a₁ b₁ a₂ b₂ => by
       dsimp
       rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂,Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
       simp [or_comm]⟩
theorem gameAdd_iff:∀ {x y:α × α},
   GameAdd rα s(x.1,x.2) s(y.1,y.2) ↔ Prod.GameAdd rα rα x y∨Prod.GameAdd rα rα x.swap y:=by
 rintro ⟨_,_⟩ ⟨_,_⟩
 rfl
theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂:α}:
   GameAdd rα s(a₁,b₁) s(a₂,b₂) ↔
     Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)∨Prod.GameAdd rα rα (b₁,a₁) (a₂,b₂):=
 Iff.rfl
theorem _root_.Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂:α} (h:Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)):
   Sym2.GameAdd rα s(a₁,b₁) s(a₂,b₂):=
 gameAdd_iff.2 <| Or.inl <| h
theorem GameAdd.fst {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(a₁,b) s(a₂,b):=
 (Prod.GameAdd.fst h).to_sym2
theorem GameAdd.snd {a b₁ b₂:α} (h:rα b₁ b₂):GameAdd rα s(a,b₁) s(a,b₂):=
 (Prod.GameAdd.snd h).to_sym2
theorem GameAdd.fst_snd {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(a₁,b) s(b,a₂):=by
 rw [Sym2.eq_swap]
 exact GameAdd.snd h
theorem GameAdd.snd_fst {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(b,a₁) s(a₂,b):=by
 rw [Sym2.eq_swap]
 exact GameAdd.fst h
end Sym2
theorem Acc.sym2_gameAdd {a b} (ha:Acc rα a) (hb:Acc rα b):
   Acc (Sym2.GameAdd rα) s(a,b):=by
 induction ha generalizing b with | _ a _ iha
 induction hb with | _ b hb ihb
 refine Acc.intro _ fun s => ?_
 induction s with | _ c d
 rw [Sym2.GameAdd]
 dsimp
 rintro ((rc | rd) | (rd | rc))
 · exact iha c rc ⟨b,hb⟩
 · exact ihb d rd
 · rw [Sym2.eq_swap]
   exact iha d rd ⟨b,hb⟩
 · rw [Sym2.eq_swap]
   exact ihb c rc
theorem WellFounded.sym2_gameAdd (h:WellFounded rα):WellFounded (Sym2.GameAdd rα):=
 ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩
namespace Sym2
attribute [local instance] Sym2.Rel.setoid
@[elab_as_elim]
def GameAdd.recursion {C:α → α → Sort*} (hr:WellFounded rα)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a b:α):
   C a b:=
 @WellFounded.fix (α × α) (fun x => C x.1 x.2)
   (fun x y↦Prod.GameAdd rα rα x y∨Prod.GameAdd rα rα x.swap y)
   (by simpa [←Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
   (fun ⟨x₁,x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a',b'⟩) (a,b)
@[deprecated (since:="2026-03-13")] alias GameAdd.fix:=GameAdd.recursion
theorem GameAdd.recursion_eq {C:α → α → Sort*} (hr:WellFounded rα)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a b:α):
   GameAdd.recursion hr IH a b=IH a b fun a' b' _ => GameAdd.recursion hr IH a' b':=
 WellFounded.fix_eq ..
@[deprecated (since:="2026-03-13")] alias GameAdd.fix_eq:=GameAdd.recursion_eq
@[deprecated GameAdd.recursion (since:="2026-03-13")]
theorem GameAdd.induction {C:α → α → Prop}:
   WellFounded rα →
     (∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) →
       ∀ a b,C a b:=
 GameAdd.recursion
end Sym2
end ProximityFlatProofPort
end PackedLegacy_S6

/-! Packed from ProximityPrize.SubmissionLower.HK. -/
section PackedLegacy_HK
section ProximityFlatProofPort
variable {ι:Type*} {α:ι → Type*}
namespace DFinsupp
open Relation Prod
section Zero
variable [∀ i,Zero (α i)] (r:ι → ι → Prop) (s:∀ i,α i → α i → Prop)
theorem lex_fibration [∀ (i) (s:Set ι),Decidable (i∈s)]:
   Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
     fun x => piecewise x.2.1 x.2.2 x.1:=by
 rintro ⟨p,x₁,x₂⟩ x ⟨i,hr,hs⟩
 simp_rw [piecewise_apply] at hs hr
 split_ifs at hs with hp
 · refine ⟨⟨{ j | r j i → j∈p},piecewise x₁ x { j | r j i},x₂⟩,
     .fst ⟨i,fun j hj↦?_,?_⟩,?_⟩ <;> simp only [piecewise_apply,Set.mem_setOf_eq]
   · simp only [if_pos hj]
   · split_ifs with hi
     · rwa [hr i hi,if_pos hp] at hs
     · assumption
   · ext1 j
     simp only [piecewise_apply,Set.mem_setOf_eq]
     split_ifs with h₁ h₂ <;> try rfl
     · rw [hr j h₂,if_pos (h₁ h₂)]
     · rw [Classical.not_imp] at h₁
       rw [hr j h₁.1,if_neg h₁.2]
 · refine ⟨⟨{ j | r j i∧j∈p},x₁,piecewise x₂ x { j | r j i}⟩,
     .snd ⟨i,fun j hj↦?_,?_⟩,?_⟩ <;> simp only [piecewise_apply,Set.mem_setOf_eq]
   · exact if_pos hj
   · split_ifs with hi
     · rwa [hr i hi,if_neg hp] at hs
     · assumption
   · ext1 j
     simp only [piecewise_apply,Set.mem_setOf_eq]
     split_ifs with h₁ h₂ <;> try rfl
     · rw [hr j h₁.1,if_pos h₁.2]
     · rw [hr j h₂,if_neg]
       simpa [h₂] using h₁
variable {r s}
theorem Lex.acc_of_single_erase [DecidableEq ι] {x:Π₀ i,α i} (i:ι)
   (hs:Acc (DFinsupp.Lex r s) <| single i (x i)) (hu:Acc (DFinsupp.Lex r s) <| x.erase i):
   Acc (DFinsupp.Lex r s) x:=by
 classical
   convert!←
     @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i},_⟩
       (InvImage.accessible snd <| hs.prod_gameAdd hu)
   convert! piecewise_single_erase x i
theorem Lex.acc_zero (hbot:∀ ⦃i a⦄,¬s i a 0):Acc (DFinsupp.Lex r s) 0:=
 Acc.intro 0 fun _ ⟨_,_,h⟩ => (hbot h).elim
theorem Lex.acc_of_single (hbot:∀ ⦃i a⦄,¬s i a 0) [DecidableEq ι]
   [∀ (i) (x:α i),Decidable (x≠0)] (x:Π₀ i,α i):
   (∀ i∈x.support,Acc (DFinsupp.Lex r s) <| single i (x i)) → Acc (DFinsupp.Lex r s) x:=by
 generalize ht:x.support=t;revert x
 classical
   induction t using Finset.induction with
   | empty =>
     intro x ht
     rw [support_eq_empty.1 ht]
     exact fun _ => Lex.acc_zero hbot
   | insert b t hb ih =>
     refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
     refine ih _ (by rw [support_erase,ht,Finset.erase_insert hb]) fun a ha => ?_
     rw [erase_ne (ha.ne_of_notMem hb)]
     exact h a (Finset.mem_insert_of_mem ha)
theorem Lex.acc_single (hbot:∀ ⦃i a⦄,¬s i a 0) (hs:∀ i,WellFounded (s i))
   [DecidableEq ι] {i:ι} (hi:Acc (rᶜ ⊓ (·≠·)) i):
   ∀ a,Acc (DFinsupp.Lex r s) (single i a):=by
 induction hi with | _ i _ ih
 refine fun a => WellFounded.induction (hs i)
   (C:=fun x↦Acc (DFinsupp.Lex r s) (single i x)) a fun a ha↦?_
 refine Acc.intro _ fun x↦?_
 rintro ⟨k,hr,hs⟩
 rw [single_apply] at hs
 split_ifs at hs with hik
 swap
 · exact (hbot hs).elim
 subst hik
 classical
   refine Lex.acc_of_single hbot x fun j hj↦?_
   obtain rfl | hij:=eq_or_ne j i
   · exact ha _ hs
   by_cases h:r j i
   · rw [hr j h,single_eq_of_ne hij,single_zero]
     exact Lex.acc_zero hbot
   · exact ih _ ⟨h,hij⟩ _
theorem Lex.acc (hbot:∀ ⦃i a⦄,¬s i a 0) (hs:∀ i,WellFounded (s i))
   [DecidableEq ι] [∀ (i) (x:α i),Decidable (x≠0)] (x:Π₀ i,α i)
   (h:∀ i∈x.support,Acc (rᶜ ⊓ (·≠·)) i):Acc (DFinsupp.Lex r s) x:=
 Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _
theorem Lex.wellFounded (hbot:∀ ⦃i a⦄,¬s i a 0) (hs:∀ i,WellFounded (s i))
   (hr:WellFounded <| rᶜ ⊓ (·≠·)):WellFounded (DFinsupp.Lex r s):=
 ⟨fun x => by
   classical
   letI:DecidableEq ι:=Classical.decEq ι
   exact Lex.acc hbot hs x fun i _ => hr.apply i⟩
theorem Lex.wellFounded' (hbot:∀ ⦃i a⦄,¬s i a 0) (hs:∀ i,WellFounded (s i))
   [Std.Trichotomous r] (hr:WellFounded (Function.swap r)):WellFounded (DFinsupp.Lex r s):=
 Lex.wellFounded hbot hs <| Subrelation.wf
   (fun {i j} h↦Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr
end Zero
instance Lex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [hι:WellFoundedGT ι]
   [∀ i,AddMonoid (α i)] [∀ i,PartialOrder (α i)] [∀ i,IsBotZeroClass (α i)]
   [hα:∀ i,WellFoundedLT (α i)]:
   WellFoundedLT (Lex (Π₀ i,α i)):=
 ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩
instance Colex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [WellFoundedLT ι]
   [∀ i,AddMonoid (α i)] [∀ i,PartialOrder (α i)] [∀ i,IsBotZeroClass (α i)]
   [∀ i,WellFoundedLT (α i)]:
   WellFoundedLT (Colex (Π₀ i,α i)):=
 Lex.wellFoundedLT (ι:=ιᵒᵈ)
end DFinsupp
open DFinsupp
variable (r:ι → ι → Prop) {s:∀ i,α i → α i → Prop}
theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs:∀ i,WellFounded (s i)):
   WellFounded (Pi.Lex r (fun {i}↦s i)):=by
 obtain h | ⟨⟨x⟩⟩:=isEmpty_or_nonempty (∀ i,α i)
 · convert! emptyWf.wf
 letI:∀ i,Zero (α i):=fun i => ⟨(hs i).min ⊤ ⟨x i,trivial⟩⟩
 haveI:=Fintype.ofFinite ι
 refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
 exacts [(hs i).not_lt_min ⊤ trivial,Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]
instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i,LT (α i)]
   [hwf:∀ i,WellFoundedLT (α i)]:WellFoundedLT (Lex (∀ i,α i)):=
 ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩
instance Pi.Colex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i,LT (α i)]
   [∀ i,WellFoundedLT (α i)]:WellFoundedLT (Colex (∀ i,α i)):=
 Pi.Lex.wellFoundedLT (ι:=ιᵒᵈ)
instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α]:
   WellFoundedLT (Lex (ι → α)):=
 Pi.Lex.wellFoundedLT
theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i,Zero (α i)]
   (hs:∀ i,WellFounded (s i)):WellFounded (DFinsupp.Lex r s):=
 have:=Fintype.ofFinite ι
 InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)
instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i,Zero (α i)]
   [∀ i,LT (α i)] [hwf:∀ i,WellFoundedLT (α i)]:WellFoundedLT (Lex (Π₀ i,α i)):=
 ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩
instance DFinsupp.Colex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i,Zero (α i)]
   [∀ i,LT (α i)] [hwf:∀ i,WellFoundedLT (α i)]:WellFoundedLT (Colex (Π₀ i,α i)):=
 DFinsupp.Lex.wellFoundedLT_of_finite (ι:=ιᵒᵈ)
protected theorem DFinsupp.wellFoundedLT [∀ i,Zero (α i)] [∀ i,Preorder (α i)]
   [∀ i,WellFoundedLT (α i)] (hbot:∀ ⦃i⦄ ⦃a:α i⦄,¬a < 0):WellFoundedLT (Π₀ i,α i):=
 ⟨by
   set β:=fun i↦Antisymmetrization (α i) (· ≤ ·)
   set e:(i:ι) → α i → β i:=fun i↦toAntisymmetrization (· ≤ ·)
   let _:∀ i,Zero (β i):=fun i↦⟨e i 0⟩
   have:WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
       (fun _↦(· < ·):(i:ι) → β i → β i → Prop)):=by
     refine Lex.wellFounded' ?_ (fun i↦IsWellFounded.wf) ?_
     · rintro i ⟨a⟩
       apply hbot
     · simp+unfoldPartialApp only [Function.swap]
       exact IsWellFounded.wf
   refine Subrelation.wf (fun h => ?_) <| InvImage.wf (mapRange e fun _↦rfl) this
   obtain ⟨i,he,hl⟩:=lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
   exact ⟨i,fun j hj↦Quot.sound (he j hj),hl⟩⟩
instance DFinsupp.wellFoundedLT'
   [∀ i,AddMonoid (α i)] [∀ i,PartialOrder (α i)] [∀ i,IsBotZeroClass (α i)]
   [∀ i,WellFoundedLT (α i)]:WellFoundedLT (Π₀ i,α i):=
 DFinsupp.wellFoundedLT fun _ _ => not_lt_zero
instance Pi.wellFoundedLT [Finite ι] [∀ i,Preorder (α i)] [hw:∀ i,WellFoundedLT (α i)]:
   WellFoundedLT (∀ i,α i):=
 ⟨by
   obtain h | ⟨⟨x⟩⟩:=isEmpty_or_nonempty (∀ i,α i)
   · convert! emptyWf.wf
   letI:∀ i,Zero (α i):=fun i => ⟨(hw i).wf.min ⊤ ⟨x i,trivial⟩⟩
   haveI:=Fintype.ofFinite ι
   refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
   exact (hw i).wf.not_lt_min ⊤ trivial⟩
instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α]:
   WellFoundedLT (ι → α):=
 Pi.wellFoundedLT
instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [∀ i,Zero (α i)] [∀ i,Preorder (α i)]
   [∀ i,WellFoundedLT (α i)]:WellFoundedLT (Π₀ i,α i):=
 have:=Fintype.ofFinite ι
 ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩
end ProximityFlatProofPort
end PackedLegacy_HK

/-! Packed from ProximityPrize.SubmissionLower.HM. -/
section PackedLegacy_HM
section ProximityFlatProofPort
variable {α N:Type*}
namespace Finsupp
variable [Zero N] {r:α → α → Prop} {s:N → N → Prop}
theorem Lex.acc (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s) (x:α →₀ N)
   (h:∀ a∈x.support,Acc (rᶜ ⊓ (·≠·)) a):
   Acc (Finsupp.Lex r s) x:=by
 letI:DecidableEq α:=Classical.decEq α
 rw [lex_eq_invImage_dfinsupp_lex]
 classical
   refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
   simpa only [toDFinsupp_support] using h
theorem Lex.wellFounded (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s)
   (hr:WellFounded <| rᶜ ⊓ (·≠·)):WellFounded (Finsupp.Lex r s):=
 ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
theorem Lex.wellFounded' (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s)
   [Std.Trichotomous r] (hr:WellFounded (Function.swap r)):WellFounded (Finsupp.Lex r s):=
 (lex_eq_invImage_dfinsupp_lex r s).symm ▸
   InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)
instance Lex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα:WellFoundedGT α]
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
   [hN:WellFoundedLT N]:WellFoundedLT (Lex (α →₀ N)):=
 ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩
instance Colex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
   [WellFoundedLT N]:WellFoundedLT (Colex (α →₀ N)):=
 Lex.wellFoundedLT (α:=αᵒᵈ)
variable (r)
theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
   (hs:WellFounded s):WellFounded (Finsupp.Lex r s):=
 InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)
theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
   [hwf:WellFoundedLT N]:WellFoundedLT (Lex (α →₀ N)):=
 ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩
theorem Colex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
   [WellFoundedLT N]:WellFoundedLT (Colex (α →₀ N)):=
 Lex.wellFoundedLT_of_finite (α:=αᵒᵈ)
protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot:∀ n:N,¬n < 0):
   WellFoundedLT (α →₀ N):=
 ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩
instance wellFoundedLT' {N}
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N] [WellFoundedLT N]:
   WellFoundedLT (α →₀ N):=
 Finsupp.wellFoundedLT fun _ => not_lt_zero
instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N]:
   WellFoundedLT (α →₀ N):=
 ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩
end Finsupp
end ProximityFlatProofPort
end PackedLegacy_HM

/-! Packed from ProximityPrize.SubmissionLower.CP. -/
section PackedLegacy_CP
section ProximityFlatProofPort
structure MonomialOrder (σ:Type*) where
 syn:Type*
 addCommMonoidSyn:AddCommMonoid syn:=by infer_instance
 linearOrderSyn:LinearOrder syn:=by infer_instance
 isOrderedAddMonoid_syn:IsOrderedAddMonoid syn:=by infer_instance
 toSyn:(σ →₀ ℕ) ≃+syn
 toSyn_monotone:Monotone toSyn
 wellFoundedLT_syn:WellFoundedLT syn:=by infer_instance
attribute [instance] MonomialOrder.addCommMonoidSyn MonomialOrder.linearOrderSyn
 MonomialOrder.isOrderedAddMonoid_syn MonomialOrder.wellFoundedLT_syn
@[deprecated (since:="2026-07-07")] alias acm:=MonomialOrder.addCommMonoidSyn
@[deprecated (since:="2026-07-07")] alias lo:=MonomialOrder.linearOrderSyn
@[deprecated (since:="2026-07-07")] alias wf:=MonomialOrder.wellFoundedLT_syn
namespace MonomialOrder
variable {σ:Type*} (m:MonomialOrder σ)
instance:AddCancelCommMonoid m.syn where
 add_left_cancel:=m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _) |>.add_left_cancel
instance isOrderedCancelAddMonoid_syn:IsOrderedCancelAddMonoid m.syn:=
 IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'
@[deprecated (since:="2026-07-07")] alias iocam:=MonomialOrder.isOrderedCancelAddMonoid_syn
lemma le_add_right (a b:σ →₀ ℕ):
   m.toSyn a ≤ m.toSyn a+m.toSyn b:=by
 rw [←map_add]
 exact m.toSyn_monotone le_self_add
instance orderBot:OrderBot (m.syn) where
 bot:=0
 bot_le a:=by
   have:=m.le_add_right 0 (m.toSyn.symm a)
   simpa [map_add,zero_add]
@[simp]
theorem bot_eq_zero:(⊥:m.syn)=0:=rfl
@[simp]
lemma zero_le (a:m.syn):0 ≤ a:=bot_le
theorem eq_zero_iff {a:m.syn}:a=0 ↔ a ≤ 0:=eq_bot_iff
lemma toSyn_eq_zero_iff (a:σ →₀ ℕ):
   m.toSyn a=0 ↔ a=0:=AddEquiv.map_eq_zero_iff m.toSyn
lemma toSyn_lt_iff_ne_zero {a:m.syn}:
   0 < a ↔ a≠0:=bot_lt_iff_ne_bot
lemma toSyn_strictMono:StrictMono (m.toSyn):=by
 apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective
scoped
notation:50 c " ≺[" m:25 "] " d:50 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)
scoped
notation:50 c " ≼[" m:25 "] " d:50 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)
end MonomialOrder
section Lex
open Finsupp
open scoped MonomialOrder
noncomputable instance {α N:Type*} [LinearOrder α]
   [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]:
   IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
 le_of_add_le_add_left a b c h:=by simpa only [add_le_add_iff_left] using h
 add_le_add_left a b h c:=by simpa using h
example:toLex (Finsupp.single 0 2) > toLex (Finsupp.single 0 1+Finsupp.single 1 1):=by
 use 0;simp
example:toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 1):=by
 use 0;simp
example:toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 2):=by
 use 0;simp
variable {σ:Type*} [LinearOrder σ]
noncomputable def MonomialOrder.lex [WellFoundedGT σ]:
   MonomialOrder σ where
 syn:=Lex (σ →₀ ℕ)
 toSyn:=
 { toEquiv:=toLex
   map_add':=toLex_add}
 toSyn_monotone:=Finsupp.toLex_monotone
theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d:σ →₀ ℕ}:
   c ≼[lex] d ↔ toLex c ≤ toLex d:=Iff.rfl
theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d:σ →₀ ℕ}:
   c ≺[lex] d ↔ toLex c < toLex d:=Iff.rfl
theorem MonomialOrder.lex_lt_iff_of_unique [Unique σ] {c d:σ →₀ ℕ}:
   c ≺[lex] d ↔ c default < d default:=by
 simp only [MonomialOrder.lex_lt_iff,Finsupp.Lex.lt_iff_of_unique,ofLex_toLex]
theorem MonomialOrder.lex_le_iff_of_unique [Unique σ] {c d:σ →₀ ℕ}:
   c ≼[lex] d ↔ c default ≤ d default:=by
 simp only [MonomialOrder.lex_le_iff,Finsupp.Lex.le_iff_of_unique,ofLex_toLex]
end Lex
end ProximityFlatProofPort
end PackedLegacy_CP

/-! Packed from ProximityPrize.SubmissionLower.S1. -/
section PackedLegacy_S1
section ProximityFlatProofPort
universe uι uR uA uB
variable {ι:Type uι}
namespace DirectSum
open DirectSum
variable (R:Type uR) (A:ι → Type uA) {B:Type uB}
 [CommSemiring R] [∀ i,AddCommMonoid (A i)] [∀ i,Module R (A i)]
 [AddMonoid ι] [GSemiring A]
section
class GAlgebra where
 toFun:R →+A 0
 map_one:toFun 1=GradedMonoid.GOne.one
 map_mul:
   ∀ r s,GradedMonoid.mk _ (toFun (r*s))=.mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
 commutes:∀ (r) (x:GradedMonoid A),.mk _ (toFun r)*x=x*.mk _ (toFun r)
 smul_def:∀ (r) (x:GradedMonoid A),r • x=.mk _ (toFun r)*x
end
variable [Semiring B] [GAlgebra R A] [Algebra R B]
instance _root_.GradedMonoid.smulCommClass_right:
   SMulCommClass R (GradedMonoid A) (GradedMonoid A) where
 smul_comm s x y:=by
   dsimp
   rw [GAlgebra.smul_def,GAlgebra.smul_def, ←mul_assoc,GAlgebra.commutes,mul_assoc]
instance _root_.GradedMonoid.isScalarTower_right:
   IsScalarTower R (GradedMonoid A) (GradedMonoid A) where
 smul_assoc s x y:=by
   dsimp
   rw [GAlgebra.smul_def,GAlgebra.smul_def, ←mul_assoc]
variable [DecidableEq ι]
set_option backward.defeqAttrib.useBackward true in
instance:Algebra R (⨁ i,A i) where
 algebraMap:=
 { toFun:=(DirectSum.of A 0).comp GAlgebra.toFun
   map_zero':=map_zero _
   map_add':=map_add _
   map_one':=DFunLike.congr_arg (DirectSum.of A 0) GAlgebra.map_one
   map_mul' a b:=by
     simp only [AddMonoidHom.comp_apply]
     rw [of_mul_of]
     apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b)}
 commutes' r x:=by
   change AddMonoidHom.mul (DirectSum.of _ _ _) x=AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
   apply DFunLike.congr_fun _ x
   ext i xi:2
   dsimp only [AddMonoidHom.comp_apply,AddMonoidHom.mul_apply,AddMonoidHom.flip_apply]
   rw [of_mul_of,of_mul_of]
   apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i,xi⟩)
 smul_def' r x:=by
   change DistribSMul.toAddMonoidHom _ r x=AddMonoidHom.mul (DirectSum.of _ _ _) x
   apply DFunLike.congr_fun _ x
   ext i xi:2
   dsimp only [AddMonoidHom.comp_apply,DistribSMul.toAddMonoidHom_apply,
     AddMonoidHom.mul_apply]
   rw [DirectSum.of_mul_of, ←of_smul]
   apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i,xi⟩)
theorem algebraMap_apply (r:R):
   algebraMap R (⨁ i,A i) r=DirectSum.of A 0 (GAlgebra.toFun r):=
 rfl
theorem algebraMap_toAddMonoid_hom:
   ↑(algebraMap R (⨁ i,A i))=(DirectSum.of A 0).comp (GAlgebra.toFun:R →+A 0):=
 rfl
@[simps]
def toAlgebra (f:∀ i,A i →ₗ[R] B) (hone:f _ GradedMonoid.GOne.one=1)
   (hmul:∀ {i j} (ai:A i) (aj:A j),f _ (GradedMonoid.GMul.mul ai aj)=f _ ai*f _ aj):
   (⨁ i,A i) →ₐ[R] B:=
 { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
   toFun:=toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
   commutes':=fun r => by
     change toModule R _ _ f (algebraMap R _ r)=_
     rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,map_smul,one_def,
       ←lof_eq_of R,toModule_lof,hone]}
@[ext]
theorem algHom_ext' ⦃f g:(⨁ i,A i) →ₐ[R] B⦄
   (h:∀ i,f.toLinearMap.comp (lof _ _ A i)=g.toLinearMap.comp (lof _ _ A i)):f=g:=
 AlgHom.toLinearMap_injective <| DirectSum.linearMap_ext _ h
theorem algHom_ext ⦃f g:(⨁ i,A i) →ₐ[R] B⦄ (h:∀ i x,f (of A i x)=g (of A i x)):f=g:=
 algHom_ext' R A fun i => LinearMap.ext <| h i
@[simps]
def gMulLHom {i j}:A i →ₗ[R] A j →ₗ[R] A (i+j) where
 toFun a:=
   { toFun:=fun b => GradedMonoid.GMul.mul a b
     map_smul':=fun r x => by
       injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
     map_add':=GNonUnitalNonAssocSemiring.mul_add _}
 map_smul' r x:=LinearMap.ext fun y => by
   injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
 map_add' _ _:=LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _
end DirectSum
@[simps]
instance Algebra.directSumGAlgebra {R A:Type*} [AddMonoid ι] [CommSemiring R]
   [Semiring A] [Algebra R A]:DirectSum.GAlgebra R fun _:ι => A where
 toFun:=(algebraMap R A).toAddMonoidHom
 map_one:=(algebraMap R A).map_one
 map_mul a b:=Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
 commutes:=fun _ ⟨_,_⟩ =>
   Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
 smul_def:=fun _ ⟨_,_⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
end ProximityFlatProofPort
end PackedLegacy_S1

/-! Packed from ProximityPrize.SubmissionLower.HA. -/
section PackedLegacy_HA
section ProximityFlatProofPort
open DirectSum
variable {ι:Type*} {σ S R:Type*}
theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
   (A:ι → Submodule S R) [SetLike.GradedOne A] (s:S):algebraMap S R s∈A 0:=by
 rw [Algebra.algebraMap_eq_smul_one]
 exact (A 0).smul_mem s <| SetLike.one_mem_graded _
theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
   [AddSubmonoidClass σ R] (A:ι → σ) [SetLike.GradedOne A] (n:ℕ):(n:R)∈A 0:=by
 induction n with
 | zero =>
   rw [Nat.cast_zero]
   exact zero_mem (A 0)
 | succ _ n_ih =>
   rw [Nat.cast_succ]
   exact add_mem n_ih (SetLike.one_mem_graded _)
theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
   [AddSubgroupClass σ R] (A:ι → σ) [SetLike.GradedOne A] (z:ℤ):(z:R)∈A 0:=by
 cases z
 · rw [Int.ofNat_eq_natCast,Int.cast_natCast]
   exact SetLike.natCast_mem_graded _ _
 · rw [Int.cast_negSucc]
   exact neg_mem (SetLike.natCast_mem_graded _ _)
section DirectSum
variable [DecidableEq ι]
namespace SetLike
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
   [AddSubmonoidClass σ R] (A:ι → σ) [SetLike.GradedMul A]:
   DirectSum.GNonUnitalNonAssocSemiring fun i => A i where
 mul_zero _:=Subtype.ext (mul_zero _)
 zero_mul _:=Subtype.ext (zero_mul _)
 mul_add _ _ _:=Subtype.ext (mul_add _ _ _)
 add_mul _ _ _:=Subtype.ext (add_mul _ _ _)
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A:ι → σ)
   [SetLike.GradedMonoid A]:DirectSum.GSemiring fun i => A i where
 natCast n:=⟨n,SetLike.natCast_mem_graded _ _⟩
 natCast_zero:=Subtype.ext Nat.cast_zero
 natCast_succ n:=Subtype.ext (Nat.cast_succ n)
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
   (A:ι → σ) [SetLike.GradedMonoid A]:DirectSum.GCommSemiring fun i => A i where
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A:ι → σ)
   [SetLike.GradedMonoid A]:DirectSum.GRing fun i => A i where
 intCast z:=⟨z,SetLike.intCast_mem_graded _ _⟩
 intCast_ofNat n:=Subtype.ext <| Int.cast_natCast n
 intCast_negSucc_ofNat n:=Subtype.ext <| Int.cast_negSucc n
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A:ι → σ)
   [SetLike.GradedMonoid A]:DirectSum.GCommRing fun i => A i where
end SetLike
namespace DirectSum
section coe
variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A:ι → σ)
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A]:(⨁ i,A i) →+*R:=
 DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl
@[simp]
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i:ι) (x:A i):
   (coeRingHom A:_ →+*R) (of (fun i => A i) i x)=x:=
 DirectSum.toSemiring_of _ _ _ _ _
set_option backward.isDefEq.respectTransparency false in
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
   [∀ (i:ι) (x:A i),Decidable (x≠0)] (r r':⨁ i,A i) (n:ι):
   ((r*r') n:R)=
     ∑ ij∈r.support ×ˢ r'.support with ij.1+ij.2=n,(r ij.1*r' ij.2:R):=by
 rw [mul_eq_sum_support_ghas_mul,DFinsupp.finsetSum_apply,AddSubmonoidClass.coe_finsetSum]
 simp_rw [coe_of_apply,apply_ite,ZeroMemClass.coe_zero, ←Finset.sum_filter,SetLike.coe_gMul]
set_option backward.isDefEq.respectTransparency false in
theorem coe_mul_apply_eq_dfinsuppSum [AddMonoid ι] [SetLike.GradedMonoid A]
   [∀ (i:ι) (x:A i),Decidable (x≠0)] (r r':⨁ i,A i) (n:ι):
   ((r*r') n:R)=r.sum fun i ri => r'.sum fun j rj => if i+j=n then (ri*rj:R)
     else 0:=by
 rw [mul_eq_dfinsuppSum]
 iterate 2 rw [DFinsupp.sum_apply,DFinsupp.sum,AddSubmonoidClass.coe_finsetSum];congr;ext
 dsimp only
 split_ifs with h
 · subst h
   rw [of_eq_same]
   rfl
 · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
   rfl
open Finset in
theorem coe_mul_apply_eq_sum_antidiagonal [AddMonoid ι] [HasAntidiagonal ι]
   [SetLike.GradedMonoid A] (r r':⨁ i,A i) (n:ι):
   (r*r') n=∑ ij∈antidiagonal n,(r ij.1:R)*r' ij.2:=by
 classical
 rw [coe_mul_apply]
 apply Finset.sum_subset (fun _↦by simp)
 aesop (erase simp not_and) (add simp not_and_or)
theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i:ι} (r:A i)
   (r':⨁ i,A i) {j n:ι} (H:∀ x:ι,i+x=n ↔ x=j):
   ((of (fun i => A i) i r*r') n:R)=r*r' j:=by
 classical
   rw [coe_mul_apply_eq_dfinsuppSum]
   apply (DFinsupp.sum_single_index _).trans
   swap
   · simp_rw [ZeroMemClass.coe_zero,zero_mul,ite_self]
     exact DFinsupp.sum_zero
   simp_rw [DFinsupp.sum,H,Finset.sum_ite_eq']
   split_ifs with h
   · rfl
   rw [DFinsupp.notMem_support_iff.mp h,ZeroMemClass.coe_zero,mul_zero]
theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r:⨁ i,A i) {i:ι}
   (r':A i) {j n:ι} (H:∀ x:ι,x+i=n ↔ x=j):
   ((r*of (fun i => A i) i r') n:R)=r j*r':=by
 classical
   rw [coe_mul_apply_eq_dfinsuppSum,DFinsupp.sum_comm]
   apply (DFinsupp.sum_single_index _).trans
   swap
   · simp_rw [ZeroMemClass.coe_zero,mul_zero,ite_self]
     exact DFinsupp.sum_zero
   simp_rw [DFinsupp.sum,H,Finset.sum_ite_eq']
   split_ifs with h
   · rfl
   rw [DFinsupp.notMem_support_iff.mp h,ZeroMemClass.coe_zero,zero_mul]
theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i:ι} (r:A i)
   (r':⨁ i,A i) (j:ι):((of (fun i => A i) i r*r') (i+j):R)=r*r' j:=
 coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h,fun h => h ▸ rfl⟩
theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r:⨁ i,A i)
   {i:ι} (r':A i) (j:ι):((r*of (fun i => A i) i r') (j+i):R)=r j*r':=
 coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h,fun h => h ▸ rfl⟩
theorem coe_of_mul_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r:A 0)
   (r':⨁ i,A i) (j:ι):((of (fun i => A i) 0 r*r') j:R)=r*r' j:=
 coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]
theorem coe_mul_of_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r:⨁ i,A i)
   (r':A 0) (j:ι):((r*of (fun i => A i) 0 r') j:R)=r j*r':=
 coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]
end coe
section CanonicallyOrderedAddCommMonoid
variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A:ι → σ)
 [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]
theorem coe_of_mul_apply_of_not_le {i:ι} (r:A i) (r':⨁ i,A i) (n:ι) (h:¬i ≤ n):
   ((of (fun i => A i) i r*r') n:R)=0:=by
 classical
   rw [coe_mul_apply_eq_dfinsuppSum]
   apply (DFinsupp.sum_single_index _).trans
   swap
   · simp_rw [ZeroMemClass.coe_zero,zero_mul,ite_self]
     exact DFinsupp.sum_zero
   · rw [DFinsupp.sum,Finset.sum_ite_of_false,Finset.sum_const_zero]
     exact fun x _ H => h ((self_le_add_right i x).trans_eq H)
theorem coe_mul_of_apply_of_not_le (r:⨁ i,A i) {i:ι} (r':A i) (n:ι) (h:¬i ≤ n):
   ((r*of (fun i => A i) i r') n:R)=0:=by
 classical
   rw [coe_mul_apply_eq_dfinsuppSum,DFinsupp.sum_comm]
   apply (DFinsupp.sum_single_index _).trans
   swap
   · simp_rw [ZeroMemClass.coe_zero,mul_zero,ite_self]
     exact DFinsupp.sum_zero
   · rw [DFinsupp.sum,Finset.sum_ite_of_false,Finset.sum_const_zero]
     exact fun x _ H => h ((self_le_add_left i x).trans_eq H)
variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]
theorem coe_mul_of_apply_of_le (r:⨁ i,A i) {i:ι} (r':A i) (n:ι) (h:i ≤ n):
   ((r*of (fun i => A i) i r') n:R)=r (n-i)*r':=
 coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm
theorem coe_of_mul_apply_of_le {i:ι} (r:A i) (r':⨁ i,A i) (n:ι) (h:i ≤ n):
   ((of (fun i => A i) i r*r') n:R)=r*r' (n-i):=
 coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h,add_comm]
theorem coe_mul_of_apply (r:⨁ i,A i) {i:ι} (r':A i) (n:ι) [Decidable (i ≤ n)]:
   ((r*of (fun i => A i) i r') n:R)=if i ≤ n then (r (n-i):R)*r' else 0:=by
 split_ifs with h
 exacts [coe_mul_of_apply_of_le _ _ _ n h,coe_mul_of_apply_of_not_le _ _ _ n h]
theorem coe_of_mul_apply {i:ι} (r:A i) (r':⨁ i,A i) (n:ι) [Decidable (i ≤ n)]:
   ((of (fun i => A i) i r*r') n:R)=if i ≤ n then (r*r' (n-i):R) else 0:=by
 split_ifs with h
 exacts [coe_of_mul_apply_of_le _ _ _ n h,coe_of_mul_apply_of_not_le _ _ _ n h]
end CanonicallyOrderedAddCommMonoid
end DirectSum
namespace Submodule
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A:ι → Submodule S R)
   [SetLike.GradedMonoid A]:DirectSum.GAlgebra S fun i => A i where
 toFun:=
   ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
 map_one:=Subtype.ext <| (algebraMap S R).map_one
 map_mul _x _y:=Sigma.subtype_ext (add_zero 0).symm <| (algebraMap S R).map_mul _ _
 commutes:=fun _r ⟨i,_xi⟩ =>
   Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) <| Algebra.commutes _ _
 smul_def:=fun _r ⟨i,_xi⟩ => Sigma.subtype_ext (zero_add i).symm <| Algebra.smul_def _ _
@[simp]
theorem setLike.coe_galgebra_toFun {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
   (A:ι → Submodule S R) [SetLike.GradedMonoid A] (s:S):
   (DirectSum.GAlgebra.toFun (A:=fun i => A i) s)=(algebraMap S R s:R):=
 rfl
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p:Submodule S R):
   SetLike.GradedMonoid fun i:ℕ => p^i where
 one_mem:=by
   rw [←one_le,pow_zero]
 mul_mem i j p q hp hq:=by
   rw [pow_add]
   exact Submodule.mul_mem_mul hp hq
end Submodule
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
   (A:ι → Submodule S R) [SetLike.GradedMonoid A]:(⨁ i,A i) →ₐ[S] R:=
 DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
   [Algebra S R] (A:ι → Submodule S R) [SetLike.GradedMonoid A]:
   ⨆ i,A i=Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range:=
 (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl
@[simp]
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
   (A:ι → Submodule S R) [SetLike.GradedMonoid A] (i:ι) (x:A i):
   DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x)=x:=
 DirectSum.toSemiring_of _ rfl (fun _ _ => rfl) _ _
end DirectSum
namespace SetLike.GradeZero
section Semiring
variable [Semiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
 (A:ι → σ) [SetLike.GradedMonoid A]
def subsemiring:Subsemiring R where
 __:=submonoid A
 add_mem':=add_mem
 zero_mem':=zero_mem (A 0)
instance instSemiring:Semiring (A 0):=inferInstanceAs <| Semiring (subsemiring A)
@[simp,norm_cast] theorem coe_natCast (n:ℕ):(n:A 0)=(n:R):=rfl
@[simp,norm_cast] theorem coe_ofNat (n:ℕ) [n.AtLeastTwo]:
   (ofNat(n):A 0)=(ofNat(n):R):=rfl
end Semiring
section CommSemiring
variable [CommSemiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
 (A:ι → σ) [SetLike.GradedMonoid A]
instance instCommSemiring:CommSemiring (A 0):=inferInstanceAs <| CommSemiring (subsemiring A)
instance:Algebra (A 0) R:=
 inferInstanceAs <| Algebra (SetLike.GradeZero.subsemiring A) R
@[simp] lemma algebraMap_apply (x:A 0):algebraMap (A 0) R x=x:=rfl
end CommSemiring
section Ring
variable [Ring R] [AddMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
 (A:ι → σ) [SetLike.GradedMonoid A]
def subring:Subring R where
 __:=subsemiring A
 neg_mem':=neg_mem
instance instRing:Ring (A 0):=inferInstanceAs <| Ring (subring A)
theorem coe_intCast (z:ℤ):(z:A 0)=(z:R):=rfl
end Ring
section CommRing
variable [CommRing R] [AddCommMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
 (A:ι → σ) [SetLike.GradedMonoid A]
instance instCommRing:CommRing (A 0):=inferInstanceAs <| CommRing (subring A)
end CommRing
section Algebra
variable [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid ι]
 (A:ι → Submodule S R) [SetLike.GradedMonoid A]
def subalgebra:Subalgebra S R where
 __:=subsemiring A
 algebraMap_mem':=algebraMap_mem_graded A
instance instAlgebra:Algebra S (A 0):=inferInstanceAs <| Algebra S (subalgebra A)
@[simp,norm_cast] theorem coe_algebraMap (s:S):
   ↑(algebraMap _ (A 0) s)=algebraMap _ R s:=rfl
end Algebra
end SetLike.GradeZero
section HomogeneousElement
theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
   (A:ι → Submodule S R):SetLike.IsHomogeneousElem A (0:R):=
 ⟨0,Submodule.zero_mem _⟩
theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A:ι → Submodule S R}
   {s:S} {r:R} (hr:SetLike.IsHomogeneousElem A r):SetLike.IsHomogeneousElem A (s • r):=
 let ⟨i,hi⟩:=hr
 ⟨i,Submodule.smul_mem _ _ hi⟩
end HomogeneousElement
section LinearOrderedAddCommMonoid
variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]
section Semiring
variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
 {A:ι → σ} [SetLike.GradedMonoid A]
theorem mul_apply_eq_zero {r r':⨁ i,A i} {m n:ι}
   (hr:∀ i < m,r i=0) (hr':∀ i < n,r' i=0) ⦃k:ι⦄ (hk:k < m+n):
   (r*r') k=0:=by
 classical
 rw [Subtype.ext_iff,ZeroMemClass.coe_zero,coe_mul_apply]
 apply Finset.sum_eq_zero fun x hx↦?_
 obtain (hx | hx):x.1 < m∨x.2 < n:=by
   by_contra! ⟨hm,hn⟩
   obtain rfl:x.1+x.2=k:=by simp_all
   apply lt_irrefl (m+n) <| lt_of_le_of_lt (by gcongr) hk
 all_goals simp [hr,hr',hx]
variable [CanonicallyOrderedAdd ι]
theorem listProd_apply_eq_zero' {l:List ((⨁ i,A i) × ι)}
   (hl:∀ xn∈l,∀ k < xn.2,xn.1 k=0) ⦃n:ι⦄ (hn:n < (l.map Prod.snd).sum):
   (l.map Prod.fst).prod n=0:=by
 induction l generalizing n with
 | nil => simp at hn
 | cons head tail ih =>
   simp only [List.mem_cons,forall_eq_or_imp,List.map_cons,List.sum_cons,
     List.prod_cons] at hl hn ⊢
   exact mul_apply_eq_zero hl.1 (ih hl.2) hn
theorem listProd_apply_eq_zero {l:List (⨁ i,A i)} {m:ι}
   (hl:∀ x∈l,∀ k < m,x k=0) ⦃n:ι⦄ (hn:n < l.length • m):
   l.prod n=0:=by
 induction l generalizing n with
 | nil => simp at hn
 | cons head tail ih =>
   simp only [List.mem_cons,forall_eq_or_imp,List.length_cons,List.prod_cons] at hl hn ⊢
   refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
   simpa [add_smul,add_comm m] using hn
end Semiring
variable [CanonicallyOrderedAdd ι]
section CommSemiring
variable [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
 {A:ι → σ} [SetLike.GradedMonoid A]
theorem multisetProd_apply_eq_zero' {s:Multiset ((⨁ i,A i) × ι)}
   (hs:∀ xn∈s,∀ k < xn.2,xn.1 k=0) ⦃n:ι⦄ (hn:n < (s.map Prod.snd).sum):
   (s.map Prod.fst).prod n=0:=by
 have:=listProd_apply_eq_zero' (l:=s.toList) (by simpa using hs)
   (by simpa [←Multiset.sum_coe, ←Multiset.map_coe])
 simpa [←Multiset.prod_coe, ←Multiset.map_coe]
theorem multisetProd_apply_eq_zero {s:Multiset (⨁ i,A i)} {m:ι}
   (hs:∀ x∈s,∀ k < m,x k=0) ⦃n:ι⦄ (hn:n < s.card • m):
   s.prod n=0:=by
 have:=listProd_apply_eq_zero (l:=s.toList) (by simpa using hs)
   (by simpa [←Multiset.sum_coe, ←Multiset.map_coe])
 simpa [←Multiset.prod_coe, ←Multiset.map_coe]
theorem finsetProd_apply_eq_zero' {s:Finset ((⨁ i,A i) × ι)}
   (hs:∀ xn∈s,∀ k < xn.2,xn.1 k=0) ⦃n:ι⦄ (hn:n < ∑ xn∈s,xn.2):
   (∏ xn∈s,xn.1) n=0:=by
 simpa using listProd_apply_eq_zero' (l:=s.toList) (by simpa using hs) (by simpa)
theorem finsetProd_apply_eq_zero {s:Finset (⨁ i,A i)} {m:ι}
   (hs:∀ x∈s,∀ k < m,x k=0) ⦃n:ι⦄ (hn:n < s.card • m):
   (∏ x∈s,x) n=0:=by
 simpa using listProd_apply_eq_zero (l:=s.toList) (by simpa using hs) (by simpa)
end CommSemiring
end LinearOrderedAddCommMonoid
end ProximityFlatProofPort
end PackedLegacy_HA

/-! Packed from ProximityPrize.SubmissionLower.T9. -/
section PackedLegacy_T9
section ProximityFlatProofPort
open DirectSum
variable {ι R A σ:Type*}
section GradedRing
variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ)
open DirectSum
class GradedRing (𝒜:ι → σ) extends SetLike.GradedMonoid 𝒜,DirectSum.Decomposition 𝒜
variable [GradedRing 𝒜]
namespace DirectSum
def decomposeRingEquiv:A ≃+*⨁ i,𝒜 i:=
 RingEquiv.symm
   { (decomposeAddEquiv 𝒜).symm with
     map_mul':=(coeRingHom 𝒜).map_mul}
@[simp]
theorem decompose_one:decompose 𝒜 (1:A)=1:=
 map_one (decomposeRingEquiv 𝒜)
@[simp]
theorem decompose_symm_one:(decompose 𝒜).symm 1=(1:A):=
 map_one (decomposeRingEquiv 𝒜).symm
@[simp]
theorem decompose_mul (x y:A):decompose 𝒜 (x*y)=decompose 𝒜 x*decompose 𝒜 y:=
 map_mul (decomposeRingEquiv 𝒜) x y
@[simp]
theorem decompose_symm_mul (x y:⨁ i,𝒜 i):
   (decompose 𝒜).symm (x*y)=(decompose 𝒜).symm x*(decompose 𝒜).symm y:=
 map_mul (decomposeRingEquiv 𝒜).symm x y
end DirectSum
def GradedRing.proj (i:ι):A →+A:=
 (AddSubmonoidClass.subtype (𝒜 i)).comp <|
   (DFinsupp.evalAddMonoidHom i).comp <|
     RingHom.toAddMonoidHom <| RingEquiv.toRingHom <| DirectSum.decomposeRingEquiv 𝒜
@[simp]
theorem GradedRing.proj_apply (i:ι) (r:A):
   GradedRing.proj 𝒜 i r=(decompose 𝒜 r:⨁ i,𝒜 i) i:=
 rfl
theorem GradedRing.proj_recompose (a:⨁ i,𝒜 i) (i:ι):
   GradedRing.proj 𝒜 i ((decompose 𝒜).symm a)=(decompose 𝒜).symm (DirectSum.of _ i (a i)):=by
 rw [GradedRing.proj_apply,decompose_symm_of,Equiv.apply_symm_apply]
theorem GradedRing.mem_support_iff [∀ (i) (x:𝒜 i),Decidable (x≠0)] (r:A) (i:ι):
   i∈(decompose 𝒜 r).support ↔ GradedRing.proj 𝒜 i r≠0:=
 DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm
end GradedRing
section AddCancelMonoid
open DirectSum
variable [DecidableEq ι] [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ)
 {i j:ι}
namespace DirectSum
theorem coe_decompose_mul_add_of_left_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b:A}
   (a_mem:a∈𝒜 i):(decompose 𝒜 (a*b) (i+j):A)=a*decompose 𝒜 b j:=by
 lift a to 𝒜 i using a_mem
 rw [decompose_mul,decompose_coe,coe_of_mul_apply_add]
theorem coe_decompose_mul_add_of_right_mem [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b:A}
   (b_mem:b∈𝒜 j):(decompose 𝒜 (a*b) (i+j):A)=decompose 𝒜 a i*b:=by
 lift b to 𝒜 j using b_mem
 rw [decompose_mul,decompose_coe,coe_mul_of_apply_add]
theorem decompose_mul_add_left [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a:𝒜 i) {b:A}:
   decompose 𝒜 (↑a*b) (i+j)=
     @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ a (decompose 𝒜 b j):=
 Subtype.ext <| coe_decompose_mul_add_of_left_mem 𝒜 a.2
theorem decompose_mul_add_right [AddRightCancelMonoid ι] [GradedRing 𝒜] {a:A} (b:𝒜 j):
   decompose 𝒜 (a*↑b) (i+j)=
     @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ (decompose 𝒜 a i) b:=
 Subtype.ext <| coe_decompose_mul_add_of_right_mem 𝒜 b.2
theorem coe_decompose_mul_of_left_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b:A}
   (a_mem:a∈𝒜 0):(decompose 𝒜 (a*b) j:A)=a*decompose 𝒜 b j:=by
 lift a to 𝒜 0 using a_mem
 rw [decompose_mul,decompose_coe,coe_of_mul_apply_of_mem_zero]
theorem coe_decompose_mul_of_right_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b:A}
   (b_mem:b∈𝒜 0):(decompose 𝒜 (a*b) i:A)=decompose 𝒜 a i*b:=by
 lift b to 𝒜 0 using b_mem
 rw [decompose_mul,decompose_coe,coe_mul_of_apply_of_mem_zero]
end DirectSum
end AddCancelMonoid
section GradedAlgebra
variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
 (𝒜:ι → Submodule R A)
abbrev GradedAlgebra:=
 GradedRing 𝒜
abbrev GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose:A →ₐ[R] ⨁ i,𝒜 i)
   (right_inv:(DirectSum.coeAlgHom 𝒜).comp decompose=AlgHom.id R A)
   (left_inv:∀ i (x:𝒜 i),decompose (x:A)=DirectSum.of (fun i => ↥(𝒜 i)) i x):
   GradedAlgebra 𝒜 where
 decompose':=decompose
 left_inv:=AlgHom.congr_fun right_inv
 right_inv:=by
   suffices decompose.comp (DirectSum.coeAlgHom 𝒜)=AlgHom.id _ _ from AlgHom.congr_fun this
   ext i x:2
   exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)
instance (R₀:Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]
   [i:GradedAlgebra 𝒜]:GradedAlgebra (𝒜 · |>.restrictScalars R₀):={ i with}
variable [GradedAlgebra 𝒜]
namespace DirectSum
def decomposeAlgEquiv:A ≃ₐ[R] ⨁ i,𝒜 i:=
 AlgEquiv.symm
   { (decomposeAddEquiv 𝒜).symm with
     map_mul':=map_mul (coeAlgHom 𝒜)
     commutes':=(coeAlgHom 𝒜).commutes}
@[simp]
lemma decomposeAlgEquiv_apply (a:A):
   decomposeAlgEquiv 𝒜 a=decompose 𝒜 a:=rfl
@[simp]
lemma decomposeAlgEquiv_symm_apply (a:⨁ i,𝒜 i):
   (decomposeAlgEquiv 𝒜).symm a=(decompose 𝒜).symm a:=rfl
@[simp]
lemma decompose_algebraMap (r:R):
   decompose 𝒜 (algebraMap R A r)=algebraMap R (⨁ i,𝒜 i) r:=
 (decomposeAlgEquiv 𝒜).commutes r
@[simp]
lemma decompose_symm_algebraMap (r:R):
   (decompose 𝒜).symm (algebraMap R (⨁ i,𝒜 i) r)=algebraMap R A r:=
 (decomposeAlgEquiv 𝒜).symm.commutes r
end DirectSum
open DirectSum
def GradedAlgebra.proj (𝒜:ι → Submodule R A) [GradedAlgebra 𝒜] (i:ι):A →ₗ[R] A:=
 (𝒜 i).subtype.comp <| (DFinsupp.lapply i).comp <| (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap
@[simp]
theorem GradedAlgebra.proj_apply (i:ι) (r:A):
   GradedAlgebra.proj 𝒜 i r=(decompose 𝒜 r:⨁ i,𝒜 i) i:=
 rfl
theorem GradedAlgebra.proj_recompose (a:⨁ i,𝒜 i) (i:ι):
   GradedAlgebra.proj 𝒜 i ((decompose 𝒜).symm a)=(decompose 𝒜).symm (of _ i (a i)):=by
 rw [GradedAlgebra.proj_apply,decompose_symm_of,Equiv.apply_symm_apply]
theorem GradedAlgebra.mem_support_iff [DecidableEq A] (r:A) (i:ι):
   i∈(decompose 𝒜 r).support ↔ GradedAlgebra.proj 𝒜 i r≠0:=
 DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm
end GradedAlgebra
section CanonicalOrder
open SetLike.GradedMonoid DirectSum
variable [Semiring A] [DecidableEq ι]
 [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
@[simps]
def GradedRing.projZeroRingHom:A →+*A where
 toFun a:=decompose 𝒜 a 0
 map_one':=decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
 map_zero':=by rw [decompose_zero,DirectSum.zero_apply,ZeroMemClass.coe_zero]
 map_add' _ _:=by rw [decompose_add,DirectSum.add_apply,AddMemClass.coe_add]
 map_mul':=by
   refine DirectSum.Decomposition.inductionOn 𝒜 (fun x => ?_) ?_ ?_
   · simp only [zero_mul,decompose_zero,DirectSum.zero_apply,ZeroMemClass.coe_zero]
   · rintro i ⟨c,hc⟩
     refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
     · simp only [mul_zero,decompose_zero,DirectSum.zero_apply,ZeroMemClass.coe_zero]
     · rintro j ⟨c',hc'⟩
       simp only
       by_cases h:i+j=0
       · rw [decompose_of_mem_same 𝒜
             (show c*c'∈𝒜 0 from h ▸ SetLike.GradedMul.mul_mem hc hc'),
           decompose_of_mem_same 𝒜 (show c∈𝒜 0 from (add_eq_zero.mp h).1 ▸ hc),
           decompose_of_mem_same 𝒜 (show c'∈𝒜 0 from (add_eq_zero.mp h).2 ▸ hc')]
       · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
         rcases show i≠0∨j≠0 by rwa [add_eq_zero,not_and_or] at h with h' | h'
         · simp only [decompose_of_mem_ne 𝒜 hc h',zero_mul]
         · simp only [decompose_of_mem_ne 𝒜 hc' h',mul_zero]
     · intro _ _ hd he
       simp only [mul_add,decompose_add,DirectSum.add_apply,AddMemClass.coe_add,hd,he]
   · rintro _ _ ha hb _
     simp only [add_mul,decompose_add,DirectSum.add_apply,AddMemClass.coe_add,ha,hb]
section GradeZero
def GradedRing.projZeroRingHom':A →+*𝒜 0:=
 ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _:
 A →+*SetLike.GradeZero.subsemiring 𝒜)
@[simp] lemma GradedRing.coe_projZeroRingHom'_apply (a:A):
   (GradedRing.projZeroRingHom' 𝒜 a:A)=GradedRing.projZeroRingHom 𝒜 a:=rfl
@[simp] lemma GradedRing.projZeroRingHom'_apply_coe (a:𝒜 0):
   GradedRing.projZeroRingHom' 𝒜 a=a:=by
 ext;simp only [coe_projZeroRingHom'_apply,projZeroRingHom_apply,decompose_coe,of_eq_same]
lemma GradedRing.projZeroRingHom'_surjective:
   Function.Surjective (GradedRing.projZeroRingHom' 𝒜):=
 Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)
end GradeZero
variable {a b:A} {n i:ι}
namespace DirectSum
theorem coe_decompose_mul_of_left_mem_of_not_le (a_mem:a∈𝒜 i) (h:¬i ≤ n):
   (decompose 𝒜 (a*b) n:A)=0:=by
 lift a to 𝒜 i using a_mem
 rwa [decompose_mul,decompose_coe,coe_of_mul_apply_of_not_le]
theorem coe_decompose_mul_of_right_mem_of_not_le (b_mem:b∈𝒜 i) (h:¬i ≤ n):
   (decompose 𝒜 (a*b) n:A)=0:=by
 lift b to 𝒜 i using b_mem
 rwa [decompose_mul,decompose_coe,coe_mul_of_apply_of_not_le]
variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]
theorem coe_decompose_mul_of_left_mem_of_le (a_mem:a∈𝒜 i) (h:i ≤ n):
   (decompose 𝒜 (a*b) n:A)=a*decompose 𝒜 b (n-i):=by
 lift a to 𝒜 i using a_mem
 rwa [decompose_mul,decompose_coe,coe_of_mul_apply_of_le]
theorem coe_decompose_mul_of_right_mem_of_le (b_mem:b∈𝒜 i) (h:i ≤ n):
   (decompose 𝒜 (a*b) n:A)=decompose 𝒜 a (n-i)*b:=by
 lift b to 𝒜 i using b_mem
 rwa [decompose_mul,decompose_coe,coe_mul_of_apply_of_le]
theorem coe_decompose_mul_of_left_mem (n) [Decidable (i ≤ n)] (a_mem:a∈𝒜 i):
   (decompose 𝒜 (a*b) n:A)=if i ≤ n then a*decompose 𝒜 b (n-i) else 0:=by
 lift a to 𝒜 i using a_mem
 rw [decompose_mul,decompose_coe,coe_of_mul_apply]
theorem coe_decompose_mul_of_right_mem (n) [Decidable (i ≤ n)] (b_mem:b∈𝒜 i):
   (decompose 𝒜 (a*b) n:A)=if i ≤ n then decompose 𝒜 a (n-i)*b else 0:=by
 lift b to 𝒜 i using b_mem
 rw [decompose_mul,decompose_coe,coe_mul_of_apply]
end DirectSum
end CanonicalOrder
namespace DirectSum.IsInternal
variable {R:Type*} [CommSemiring R] {A:Type*} [Semiring A] [Algebra R A]
 {ι:Type*} [DecidableEq ι] [AddMonoid ι]
 {M:ι → Submodule R A} [SetLike.GradedMonoid M]
noncomputable def coeAlgEquiv (hM:DirectSum.IsInternal M):
   (DirectSum ι fun i => ↥(M i)) ≃ₐ[R] A:=
 { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes':=fun r => by simp}
@[implicit_reducible]
noncomputable def gradedAlgebra (hM:DirectSum.IsInternal M):GradedAlgebra M:=
 { (inferInstance:SetLike.GradedMonoid M) with
   decompose':=hM.coeAlgEquiv.symm
   left_inv:=hM.coeAlgEquiv.symm.left_inv
   right_inv:=hM.coeAlgEquiv.left_inv}
end DirectSum.IsInternal
end ProximityFlatProofPort
end PackedLegacy_T9

/-! Packed from ProximityPrize.SubmissionLower.U1. -/
section PackedLegacy_U1
section ProximityFlatProofPort
open SetLike DirectSum Pointwise Set
variable {ιA ιM σA σM A M:Type*}
 [Semiring A] [AddCommMonoid M] [Module A M]
section HomogeneousDef
def Submodule.IsHomogeneous (p:Submodule A M) (ℳ:ιM → σM)
   [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]:Prop:=
 SetLike.IsHomogeneous ℳ p
theorem Submodule.IsHomogeneous.mem_iff {p:Submodule A M}
   (ℳ:ιM → σM)
   [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
   (hp:p.IsHomogeneous ℳ) {x}:
   x∈p ↔ ∀ i,(decompose ℳ x i:M)∈p:=
 AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp
structure HomogeneousSubmodule (𝒜:ιA → σA) (ℳ:ιM → σM)
   [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
   [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
   [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
   extends Submodule A M where
 is_homogeneous':toSubmodule.IsHomogeneous ℳ
variable (𝒜:ιA → σA) (ℳ:ιM → σM)
 [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
 [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
 [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
instance:SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
 coe «X»:=«X».toSubmodule
 coe_injective:=by
   rintro ⟨p,hp⟩ ⟨q,hq⟩ (h:(p:Set M)=q)
   simpa using h
instance:PartialOrder (HomogeneousSubmodule 𝒜 ℳ):=.ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M
instance:AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M where
 zero_mem p:=p.toSubmodule.zero_mem
 add_mem hx hy:=Submodule.add_mem _ hx hy
instance:SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M where
 smul_mem:=by
   intro x r m hm
   exact Submodule.smul_mem x.toSubmodule r hm
variable {𝒜 ℳ} in
theorem HomogeneousSubmodule.isHomogeneous (p:HomogeneousSubmodule 𝒜 ℳ):
   p.toSubmodule.IsHomogeneous ℳ:=
 p.is_homogeneous'
theorem HomogeneousSubmodule.toSubmodule_injective:
   Function.Injective
     (HomogeneousSubmodule.toSubmodule:HomogeneousSubmodule 𝒜 ℳ → Submodule A M):=
 fun ⟨x,hx⟩ ⟨y,hy⟩↦fun (h:x=y)↦by simp [h]
instance HomogeneousSubmodule.setLike:SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
 coe p:=p.toSubmodule
 coe_injective _ _ h:=HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ <| SetLike.coe_injective h
instance:PartialOrder (HomogeneousSubmodule 𝒜 ℳ):=.ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M
@[ext]
theorem HomogeneousSubmodule.ext
   {I J:HomogeneousSubmodule 𝒜 ℳ} (h:I.toSubmodule=J.toSubmodule):I=J:=
 HomogeneousSubmodule.toSubmodule_injective _ _ h
theorem HomogeneousSubmodule.ext' {I J:HomogeneousSubmodule 𝒜 ℳ}
   (h:∀ i,∀ x∈ℳ i,x∈I ↔ x∈J):
   I=J:=by
 ext
 rw [I.isHomogeneous.mem_iff,J.isHomogeneous.mem_iff]
 apply forall_congr'
 exact fun i↦h i _ (decompose ℳ _ i).2
@[simp]
theorem HomogeneousSubmodule.mem_toSubmodule_iff {I:HomogeneousSubmodule 𝒜 ℳ} {x:M}:
   x∈I.toSubmodule (A:=A) ↔ x∈I:=
 Iff.rfl
end HomogeneousDef
end ProximityFlatProofPort
end PackedLegacy_U1

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier05 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.U0. -/
section PackedLegacy_U0
section ProximityFlatProofPort
open SetLike DirectSum Set
open scoped Pointwise
variable {ι σ A:Type*}
section HomogeneousDef
variable [Semiring A]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ)
 [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
 (I:Ideal A)
abbrev Ideal.IsHomogeneous:Prop:=Submodule.IsHomogeneous I 𝒜
theorem Ideal.IsHomogeneous.mem_iff {I} (hI:Ideal.IsHomogeneous 𝒜 I) {x}:
   x∈I ↔ ∀ i,(decompose 𝒜 x i:A)∈I:=
 AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI
abbrev HomogeneousIdeal:=HomogeneousSubmodule 𝒜 𝒜
variable {𝒜}
abbrev HomogeneousIdeal.toIdeal (I:HomogeneousIdeal 𝒜):Ideal A:=
 I.toSubmodule
@[simp] lemma coe_toIdeal (I:HomogeneousIdeal 𝒜):(I.toIdeal:Set A)=I:=rfl
theorem HomogeneousIdeal.isHomogeneous (I:HomogeneousIdeal 𝒜):
   I.toIdeal.IsHomogeneous 𝒜:=I.is_homogeneous'
theorem HomogeneousIdeal.toIdeal_injective:
   Function.Injective (HomogeneousIdeal.toIdeal:HomogeneousIdeal 𝒜 → Ideal A):=
 HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜
@[simp] lemma toIdeal_le_toIdeal_iff {I J:HomogeneousIdeal 𝒜}:
   I.toIdeal ≤ J.toIdeal ↔ I ≤ J:=Iff.rfl
instance HomogeneousIdeal.setLike:SetLike (HomogeneousIdeal 𝒜) A:=
 HomogeneousSubmodule.setLike 𝒜 𝒜
instance:PartialOrder (HomogeneousIdeal 𝒜):=.ofSetLike (HomogeneousIdeal 𝒜) A
@[ext]
theorem HomogeneousIdeal.ext {I J:HomogeneousIdeal 𝒜} (h:I.toIdeal=J.toIdeal):I=J:=
 HomogeneousIdeal.toIdeal_injective h
theorem HomogeneousIdeal.ext' {I J:HomogeneousIdeal 𝒜} (h:∀ i,∀ x∈𝒜 i,x∈I ↔ x∈J):
   I=J:=HomogeneousSubmodule.ext' 𝒜 𝒜 h
@[simp high]
theorem HomogeneousIdeal.mem_iff {I:HomogeneousIdeal 𝒜} {x:A}:x∈I.toIdeal ↔ x∈I:=
 Iff.rfl
end HomogeneousDef
section HomogeneousCore
variable [Semiring A]
 [SetLike σ A] (𝒜:ι → σ)
 (I:Ideal A)
def Ideal.homogeneousCore' (I:Ideal A):Ideal A:=
 Ideal.span ((↑) '' (((↑):Subtype (SetLike.IsHomogeneousElem 𝒜) → A) ⁻¹' I))
theorem Ideal.homogeneousCore'_mono:Monotone (Ideal.homogeneousCore' 𝒜):=
 fun _ _ I_le_J => Ideal.span_mono <| Set.image_mono fun _ => @I_le_J _
theorem Ideal.homogeneousCore'_le:I.homogeneousCore' 𝒜 ≤ I:=
 Ideal.span_le.2 <| image_preimage_subset _ _
end HomogeneousCore
section IsHomogeneousIdealDefs
variable [Semiring A]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ)
 [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
 (I:Ideal A)
theorem Ideal.isHomogeneous_iff_forall_subset:
   I.IsHomogeneous 𝒜 ↔ ∀ i,(I:Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' I:=
 Iff.rfl
theorem Ideal.isHomogeneous_iff_subset_iInter:
   I.IsHomogeneous 𝒜 ↔ (I:Set A) ⊆ ⋂ i,GradedRing.proj 𝒜 i ⁻¹' ↑I:=
 subset_iInter_iff.symm
theorem Ideal.mul_homogeneous_element_mem_of_mem
   {I:Ideal A} (r x:A) (hx₁:SetLike.IsHomogeneousElem 𝒜 x)
   (hx₂:x∈I) (j:ι):GradedRing.proj 𝒜 j (r*x)∈I:=by
 classical
 rw [←DirectSum.sum_support_decompose 𝒜 r,Finset.sum_mul,map_sum]
 apply Ideal.sum_mem
 intro k _
 obtain ⟨i,hi⟩:=hx₁
 have mem₁:(DirectSum.decompose 𝒜 r k:A)*x∈𝒜 (k+i):=
   GradedMul.mul_mem (SetLike.coe_mem _) hi
 rw [GradedRing.proj_apply,DirectSum.decompose_of_mem 𝒜 mem₁,coe_of_apply]
 split_ifs
 · exact I.mul_mem_left _ hx₂
 · exact I.zero_mem
set_option backward.isDefEq.respectTransparency false in
theorem Ideal.homogeneous_span (s:Set A) (h:∀ x∈s,SetLike.IsHomogeneousElem 𝒜 x):
   (Ideal.span s).IsHomogeneous 𝒜:=by
 rintro i r hr
 rw [Ideal.span,Finsupp.span_eq_range_linearCombination] at hr
 rw [LinearMap.mem_range] at hr
 obtain ⟨s,rfl⟩:=hr
 rw [Finsupp.linearCombination_apply,Finsupp.sum,decompose_sum,DFinsupp.finsetSum_apply,
   AddSubmonoidClass.coe_finsetSum]
 refine Ideal.sum_mem _ ?_
 rintro z hz1
 rw [smul_eq_mul]
 refine Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z ?_ ?_ i
 · rcases z with ⟨z,hz2⟩
   apply h _ hz2
 · exact Ideal.subset_span z.2
def Ideal.homogeneousCore:HomogeneousIdeal 𝒜:=
 ⟨Ideal.homogeneousCore' 𝒜 I,
   Ideal.homogeneous_span _ _ fun _ h => by
     have:=Subtype.image_preimage_coe (setOf (SetLike.IsHomogeneousElem 𝒜)) (I:Set A)
     exact (cast congr(_∈$this) h).1⟩
theorem Ideal.homogeneousCore_mono:Monotone (Ideal.homogeneousCore 𝒜):=
 Ideal.homogeneousCore'_mono 𝒜
theorem Ideal.toIdeal_homogeneousCore_le:(I.homogeneousCore 𝒜).toIdeal ≤ I:=
 Ideal.homogeneousCore'_le 𝒜 I
variable {𝒜 I}
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x:A} (h:SetLike.IsHomogeneousElem 𝒜 x)
   (hmem:x∈I):x∈I.homogeneousCore 𝒜:=
 Ideal.subset_span ⟨⟨x,h⟩,hmem,rfl⟩
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h:I.IsHomogeneous 𝒜):
   (I.homogeneousCore 𝒜).toIdeal=I:=by
 apply le_antisymm (I.homogeneousCore'_le 𝒜) _
 intro x hx
 classical
 rw [←DirectSum.sum_support_decompose 𝒜 x]
 exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_,isHomogeneousElem_coe _⟩,h _ hx,rfl⟩
@[simp]
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I:HomogeneousIdeal 𝒜):
   I.toIdeal.homogeneousCore 𝒜=I:=by
 ext1
 convert! Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous
variable (𝒜 I)
theorem Ideal.IsHomogeneous.iff_eq:I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal=I:=
 ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self,fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩
theorem Ideal.IsHomogeneous.iff_exists:
   I.IsHomogeneous 𝒜 ↔ ∃ S:Set (homogeneousSubmonoid 𝒜),I=Ideal.span ((↑) '' S):=by
 rw [Ideal.IsHomogeneous.iff_eq,eq_comm]
 exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm
end IsHomogeneousIdealDefs
section Operations
section Semiring
variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
namespace Ideal.IsHomogeneous
theorem bot:Ideal.IsHomogeneous 𝒜 ⊥:=fun i r hr => by
 simp only [Ideal.mem_bot] at hr
 rw [hr,decompose_zero,zero_apply]
 apply Ideal.zero_mem
theorem top:Ideal.IsHomogeneous 𝒜 ⊤:=fun i r _ => by simp only [Submodule.mem_top]
variable {𝒜}
theorem inf {I J:Ideal A} (HI:I.IsHomogeneous 𝒜) (HJ:J.IsHomogeneous 𝒜):
   (I ⊓ J).IsHomogeneous 𝒜:=
 fun _ _ hr => ⟨HI _ hr.1,HJ _ hr.2⟩
theorem sup {I J:Ideal A} (HI:I.IsHomogeneous 𝒜) (HJ:J.IsHomogeneous 𝒜):
   (I ⊔ J).IsHomogeneous 𝒜:=by
 rw [iff_exists] at HI HJ ⊢
 obtain ⟨⟨s₁,rfl⟩,⟨s₂,rfl⟩⟩:=HI,HJ
 refine ⟨s₁ ∪ s₂,?_⟩
 rw [Set.image_union]
 exact (Submodule.span_union _ _).symm
protected theorem iSup {κ:Sort*} {f:κ → Ideal A} (h:∀ i,(f i).IsHomogeneous 𝒜):
   (⨆ i,f i).IsHomogeneous 𝒜:=by
 simp_rw [iff_exists] at h ⊢
 choose s hs using h
 refine ⟨⋃ i,s i,?_⟩
 simp_rw [Set.image_iUnion,Ideal.span_iUnion]
 congr
 exact funext hs
protected theorem iInf {κ:Sort*} {f:κ → Ideal A} (h:∀ i,(f i).IsHomogeneous 𝒜):
   (⨅ i,f i).IsHomogeneous 𝒜:=by
 intro i x hx
 simp only [Ideal.mem_iInf] at hx ⊢
 exact fun j => h _ _ (hx j)
theorem iSup₂ {κ:Sort*} {κ':κ → Sort*} {f:∀ i,κ' i → Ideal A}
   (h:∀ i j,(f i j).IsHomogeneous 𝒜):(⨆ (i) (j),f i j).IsHomogeneous 𝒜:=
 IsHomogeneous.iSup fun i => IsHomogeneous.iSup <| h i
theorem iInf₂ {κ:Sort*} {κ':κ → Sort*} {f:∀ i,κ' i → Ideal A}
   (h:∀ i j,(f i j).IsHomogeneous 𝒜):(⨅ (i) (j),f i j).IsHomogeneous 𝒜:=
 IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i
theorem sSup {ℐ:Set (Ideal A)} (h:∀ I∈ℐ,Ideal.IsHomogeneous 𝒜 I):
   (sSup ℐ).IsHomogeneous 𝒜:=by
 rw [sSup_eq_iSup]
 exact iSup₂ h
theorem sInf {ℐ:Set (Ideal A)} (h:∀ I∈ℐ,Ideal.IsHomogeneous 𝒜 I):
   (sInf ℐ).IsHomogeneous 𝒜:=by
 rw [sInf_eq_iInf]
 exact iInf₂ h
end Ideal.IsHomogeneous
variable {𝒜}
namespace HomogeneousIdeal
instance:Top (HomogeneousIdeal 𝒜):=
 ⟨⟨⊤,Ideal.IsHomogeneous.top 𝒜⟩⟩
instance:Bot (HomogeneousIdeal 𝒜):=
 ⟨⟨⊥,Ideal.IsHomogeneous.bot 𝒜⟩⟩
instance:Max (HomogeneousIdeal 𝒜):=
 ⟨fun I J => ⟨_,I.isHomogeneous.sup J.isHomogeneous⟩⟩
instance:Min (HomogeneousIdeal 𝒜):=
 ⟨fun I J => ⟨_,I.isHomogeneous.inf J.isHomogeneous⟩⟩
instance:SupSet (HomogeneousIdeal 𝒜):=
 ⟨fun S => ⟨⨆ s∈S,toIdeal s,Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩
instance:InfSet (HomogeneousIdeal 𝒜):=
 ⟨fun S => ⟨⨅ s∈S,toIdeal s,Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩
@[simp]
theorem coe_top:((⊤:HomogeneousIdeal 𝒜):Set A)=univ:=
 rfl
@[simp]
theorem coe_bot:((⊥:HomogeneousIdeal 𝒜):Set A)=0:=
 rfl
@[simp]
theorem coe_sup (I J:HomogeneousIdeal 𝒜):↑(I ⊔ J)=(I+J:Set A):=
 Submodule.coe_sup _ _
@[simp]
theorem coe_inf (I J:HomogeneousIdeal 𝒜):(↑(I ⊓ J):Set A)=↑I ∩ ↑J:=
 rfl
@[simp]
theorem toIdeal_top:(⊤:HomogeneousIdeal 𝒜).toIdeal=(⊤:Ideal A):=
 rfl
@[simp]
theorem toIdeal_bot:(⊥:HomogeneousIdeal 𝒜).toIdeal=(⊥:Ideal A):=
 rfl
@[simp]
theorem toIdeal_sup (I J:HomogeneousIdeal 𝒜):(I ⊔ J).toIdeal=I.toIdeal ⊔ J.toIdeal:=
 rfl
@[simp]
theorem toIdeal_inf (I J:HomogeneousIdeal 𝒜):(I ⊓ J).toIdeal=I.toIdeal ⊓ J.toIdeal:=
 rfl
@[simp]
theorem toIdeal_sSup (ℐ:Set (HomogeneousIdeal 𝒜)):(sSup ℐ).toIdeal=⨆ s∈ℐ,toIdeal s:=
 rfl
@[simp]
theorem toIdeal_sInf (ℐ:Set (HomogeneousIdeal 𝒜)):(sInf ℐ).toIdeal=⨅ s∈ℐ,toIdeal s:=
 rfl
@[simp]
theorem toIdeal_iSup {κ:Sort*} (s:κ → HomogeneousIdeal 𝒜):
   (⨆ i,s i).toIdeal=⨆ i,(s i).toIdeal:=by
 rw [iSup,toIdeal_sSup,iSup_range]
@[simp]
theorem toIdeal_iInf {κ:Sort*} (s:κ → HomogeneousIdeal 𝒜):
   (⨅ i,s i).toIdeal=⨅ i,(s i).toIdeal:=by
 rw [iInf,toIdeal_sInf,iInf_range]
theorem toIdeal_iSup₂ {κ:Sort*} {κ':κ → Sort*} (s:∀ i,κ' i → HomogeneousIdeal 𝒜):
   (⨆ (i) (j),s i j).toIdeal=⨆ (i) (j),(s i j).toIdeal:=by
 simp_rw [toIdeal_iSup]
theorem toIdeal_iInf₂ {κ:Sort*} {κ':κ → Sort*} (s:∀ i,κ' i → HomogeneousIdeal 𝒜):
   (⨅ (i) (j),s i j).toIdeal=⨅ (i) (j),(s i j).toIdeal:=by
 simp_rw [toIdeal_iInf]
@[simp]
theorem eq_top_iff (I:HomogeneousIdeal 𝒜):I=⊤ ↔ I.toIdeal=⊤:=
 toIdeal_injective.eq_iff.symm
@[simp]
theorem eq_bot_iff (I:HomogeneousIdeal 𝒜):I=⊥ ↔ I.toIdeal=⊥:=
 toIdeal_injective.eq_iff.symm
instance completeLattice:CompleteLattice (HomogeneousIdeal 𝒜):=
 toIdeal_injective.completeLattice _ .rfl .rfl toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf
   toIdeal_top toIdeal_bot
instance:Add (HomogeneousIdeal 𝒜):=
 ⟨(· ⊔ ·)⟩
@[simp]
theorem toIdeal_add (I J:HomogeneousIdeal 𝒜):(I+J).toIdeal=I.toIdeal+J.toIdeal:=
 rfl
instance:Inhabited (HomogeneousIdeal 𝒜) where default:=⊥
end HomogeneousIdeal
end Semiring
section CommSemiring
variable [CommSemiring A]
 [DecidableEq ι] [AddMonoid ι]
 [SetLike σ A] [AddSubmonoidClass σ A] {𝒜:ι → σ} [GradedRing 𝒜]
 (I:Ideal A)
theorem Ideal.IsHomogeneous.mul {I J:Ideal A} (HI:I.IsHomogeneous 𝒜) (HJ:J.IsHomogeneous 𝒜):
   (I*J).IsHomogeneous 𝒜:=by
 rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
 obtain ⟨⟨s₁,rfl⟩,⟨s₂,rfl⟩⟩:=HI,HJ
 rw [Ideal.span_mul_span']
 exact ⟨s₁*s₂,congr_arg _ <| (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩
instance:Mul (HomogeneousIdeal 𝒜) where
 mul I J:=⟨I.toIdeal*J.toIdeal,I.isHomogeneous.mul J.isHomogeneous⟩
@[simp]
theorem HomogeneousIdeal.toIdeal_mul (I J:HomogeneousIdeal 𝒜):
   (I*J).toIdeal=I.toIdeal*J.toIdeal:=
 rfl
end CommSemiring
end Operations
section homogeneousCore
open HomogeneousIdeal
variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
 (I:Ideal A)
theorem Ideal.homogeneousCore.gc:GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜):=fun I _ =>
 ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
   fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩
def Ideal.homogeneousCore.gi:GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
 choice I HI:=
   ⟨I,le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
 gc:=Ideal.homogeneousCore.gc 𝒜
 u_l_le _:=Ideal.homogeneousCore'_le _ _
 choice_eq I H:=le_antisymm H (I.toIdeal_homogeneousCore_le _)
theorem Ideal.homogeneousCore_eq_sSup:
   I.homogeneousCore 𝒜=sSup { J:HomogeneousIdeal 𝒜 | J.toIdeal ≤ I}:=
 Eq.symm <| IsLUB.sSup_eq <| (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB
theorem Ideal.homogeneousCore'_eq_sSup:
   I.homogeneousCore' 𝒜=sSup { J:Ideal A | J.IsHomogeneous 𝒜∧J ≤ I}:=by
 refine (IsLUB.sSup_eq ?_).symm
 apply IsGreatest.isLUB
 have coe_mono:Monotone (toIdeal:HomogeneousIdeal 𝒜 → Ideal A):=fun x y => id
 convert! coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
 ext x
 rw [mem_image,mem_setOf_eq]
 refine ⟨fun hI => ⟨⟨x,hI.1⟩,⟨hI.2,rfl⟩⟩,?_⟩
 rintro ⟨x,⟨hx,rfl⟩⟩
 exact ⟨x.isHomogeneous,hx⟩
end homogeneousCore
section HomogeneousHull
open HomogeneousIdeal
variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
 (I:Ideal A)
def Ideal.homogeneousHull:HomogeneousIdeal 𝒜:=
 ⟨Ideal.span { r:A | ∃ (i:ι) (x:I),(DirectSum.decompose 𝒜 (x:A) i:A)=r},by
   refine Ideal.homogeneous_span _ _ fun x hx => ?_
   obtain ⟨i,x,rfl⟩:=hx
   apply SetLike.isHomogeneousElem_coe⟩
theorem Ideal.le_toIdeal_homogeneousHull:I ≤ (Ideal.homogeneousHull 𝒜 I).toIdeal:=by
 intro r hr
 classical
 rw [←DirectSum.sum_support_decompose 𝒜 r]
 refine Ideal.sum_mem _ ?_
 intro j _
 apply Ideal.subset_span
 use j
 use ⟨r,hr⟩
theorem Ideal.homogeneousHull_mono:Monotone (Ideal.homogeneousHull 𝒜):=fun I J I_le_J => by
 apply Ideal.span_mono
 rintro r ⟨hr1,⟨x,hx⟩,rfl⟩
 exact ⟨hr1,⟨⟨x,I_le_J hx⟩,rfl⟩⟩
variable {I 𝒜}
theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h:I.IsHomogeneous 𝒜):
   (Ideal.homogeneousHull 𝒜 I).toIdeal=I:=by
 apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
 apply Ideal.span_le.2
 rintro _ ⟨i,x,rfl⟩
 exact h _ x.prop
@[simp]
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I:HomogeneousIdeal 𝒜):
   I.toIdeal.homogeneousHull 𝒜=I:=
 HomogeneousIdeal.toIdeal_injective <| I.isHomogeneous.toIdeal_homogeneousHull_eq_self
variable (I 𝒜)
theorem Ideal.toIdeal_homogeneousHull_eq_iSup:
   (I.homogeneousHull 𝒜).toIdeal=⨆ i,Ideal.span (GradedRing.proj 𝒜 i '' I):=by
 rw [←Ideal.span_iUnion]
 apply congr_arg Ideal.span _
 ext1
 simp only [Set.mem_iUnion,Set.mem_image,mem_setOf_eq,GradedRing.proj_apply,SetLike.exists,
   exists_prop,SetLike.mem_coe]
theorem Ideal.homogeneousHull_eq_iSup:
   I.homogeneousHull 𝒜=
     ⨆ i,⟨Ideal.span (GradedRing.proj 𝒜 i '' I),Ideal.homogeneous_span 𝒜 _ (by
       rintro _ ⟨x, -,rfl⟩
       apply SetLike.isHomogeneousElem_coe)⟩:=by
 ext1
 rw [Ideal.toIdeal_homogeneousHull_eq_iSup,toIdeal_iSup]
end HomogeneousHull
section GaloisConnection
open HomogeneousIdeal
variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
theorem Ideal.homogeneousHull.gc:GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal:=fun _ J =>
 ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
   fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩
def Ideal.homogeneousHull.gi:GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
 choice I H:=⟨I,le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
 gc:=Ideal.homogeneousHull.gc 𝒜
 le_l_u _:=Ideal.le_toIdeal_homogeneousHull _ _
 choice_eq I H:=le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H
theorem Ideal.homogeneousHull_eq_sInf (I:Ideal A):
   Ideal.homogeneousHull 𝒜 I=sInf { J:HomogeneousIdeal 𝒜 | I ≤ J.toIdeal}:=
 Eq.symm <| IsGLB.sInf_eq <| (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB
end GaloisConnection
section IrrelevantIdeal
namespace HomogeneousIdeal
variable [Semiring A]
 [DecidableEq ι]
 [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
 [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ) [GradedRing 𝒜]
open GradedRing SetLike.GradedMonoid DirectSum
def irrelevant:HomogeneousIdeal 𝒜:=
 ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜),fun i r (hr:(decompose 𝒜 r 0:A)=0) => by
   change (decompose 𝒜 (decompose 𝒜 r _:A) 0:A)=0
   by_cases h:i=0
   · rw [h,hr,decompose_zero,zero_apply,ZeroMemClass.coe_zero]
   · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩
@[inherit_doc] scoped notation 𝒜 "₊" => irrelevant 𝒜
@[simp]
theorem mem_irrelevant_iff (a:A):
   a∈𝒜₊ ↔ proj 𝒜 0 a=0:=
 Iff.rfl
@[simp]
theorem toIdeal_irrelevant:
   𝒜₊.toIdeal=RingHom.ker (GradedRing.projZeroRingHom 𝒜):=
 rfl
lemma mem_irrelevant_of_mem {x:A} {i:ι} (hi:0 < i) (hx:x∈𝒜 i):x∈𝒜₊:=by
 rw [mem_irrelevant_iff,GradedRing.proj_apply,DirectSum.decompose_of_mem _ hx,
   DirectSum.of_eq_of_ne _ _ _ (by aesop),ZeroMemClass.coe_zero]
lemma irrelevant_eq_iSup:𝒜₊.toAddSubmonoid=⨆ i > 0,.ofClass (𝒜 i):=by
 refine le_antisymm (fun x hx↦?_) <| iSup₂_le fun i hi x hx↦mem_irrelevant_of_mem _ hi hx
 classical rw [←DirectSum.sum_support_decompose 𝒜 x]
 refine sum_mem fun j hj↦?_
 by_cases hj₀:j=0
 · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
 · exact AddSubmonoid.mem_iSup_of_mem j <| AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀) <|
     Subtype.prop _
open AddSubmonoid Set in
lemma irrelevant_eq_closure:𝒜₊.toAddSubmonoid=.closure (⋃ i > 0,𝒜 i):=by
 rw [irrelevant_eq_iSup]
 exact le_antisymm (iSup_le fun i↦iSup_le fun hi _ hx↦subset_closure <| mem_biUnion hi hx) <|
   closure_le.mpr <| iUnion_subset fun i↦iUnion_subset fun hi↦le_biSup (ofClass <| 𝒜 ·) hi
open AddSubmonoid Set in
lemma irrelevant_eq_span:𝒜₊.toIdeal=.span (⋃ i > 0,𝒜 i):=
 le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span) <|
   Ideal.span_le.mpr <| iUnion_subset fun _↦iUnion_subset fun hi _ hx↦
   mem_irrelevant_of_mem _ hi hx
lemma toAddSubmonoid_irrelevant_le {P:AddSubmonoid A}:
   𝒜₊.toAddSubmonoid ≤ P ↔ ∀ i > 0,.ofClass (𝒜 i) ≤ P:=by
 rw [irrelevant_eq_iSup,iSup₂_le_iff]
lemma toIdeal_irrelevant_le {I:Ideal A}:
   𝒜₊.toIdeal ≤ I ↔ ∀ i > 0,.ofClass (𝒜 i) ≤ I.toAddSubmonoid:=
 toAddSubmonoid_irrelevant_le _
lemma irrelevant_le {P:HomogeneousIdeal 𝒜}:
   𝒜₊ ≤ P ↔ ∀ i > 0,.ofClass (𝒜 i) ≤ P.toAddSubmonoid:=
 toIdeal_irrelevant_le _
end HomogeneousIdeal
end IrrelevantIdeal
end ProximityFlatProofPort
end PackedLegacy_U0

/-! Packed from ProximityPrize.SubmissionLower.IP. -/
section PackedLegacy_IP
section ProximityFlatProofPort
noncomputable section
open Set Function Finset Finsupp AddMonoidAlgebra
variable {R M:Type*} [CommSemiring R]
namespace MvPolynomial
variable {σ:Type*}
section AddCommMonoid
variable [AddCommMonoid M]
section SemilatticeSup
variable [SemilatticeSup M]
def weightedTotalDegree' (w:σ → M) (p:MvPolynomial σ R):WithBot M:=
 p.support.sup fun s => weight w s
theorem weightedTotalDegree'_eq_bot_iff (w:σ → M) (p:MvPolynomial σ R):
   weightedTotalDegree' w p=⊥ ↔ p=0:=by
 simp only [weightedTotalDegree',Finset.sup_eq_bot_iff,mem_support_iff,WithBot.coe_ne_bot,
   MvPolynomial.eq_zero_iff]
 exact forall_congr' fun _ => Classical.not_not
theorem weightedTotalDegree'_zero (w:σ → M):
   weightedTotalDegree' w (0:MvPolynomial σ R)=⊥:=by
 simp only [weightedTotalDegree',support_zero,Finset.sup_empty]
section OrderBot
variable [OrderBot M]
def weightedTotalDegree (w:σ → M) (p:MvPolynomial σ R):M:=
 p.support.sup fun s => weight w s
theorem weightedTotalDegree_coe (w:σ → M) (p:MvPolynomial σ R) (hp:p≠0):
   weightedTotalDegree' w p=↑(weightedTotalDegree w p):=by
 rw [Ne, ←weightedTotalDegree'_eq_bot_iff w p, ←Ne,WithBot.ne_bot_iff_exists] at hp
 obtain ⟨m,hm⟩:=hp
 apply le_antisymm
 · simp only [weightedTotalDegree,weightedTotalDegree',Finset.sup_le_iff,WithBot.coe_le_coe]
   intro b
   exact Finset.le_sup
 · simp only [weightedTotalDegree]
   have hm':weightedTotalDegree' w p ≤ m:=le_of_eq hm.symm
   rw [←hm]
   simpa [weightedTotalDegree'] using hm'
theorem weightedTotalDegree_zero (w:σ → M):
   weightedTotalDegree w (0:MvPolynomial σ R)=⊥:=by
 simp only [weightedTotalDegree,support_zero,Finset.sup_empty]
theorem le_weightedTotalDegree (w:σ → M) {φ:MvPolynomial σ R} {d:σ →₀ ℕ}
   (hd:d∈φ.support):weight w d ≤ φ.weightedTotalDegree w:=
 le_sup hd
end OrderBot
end SemilatticeSup
def IsWeightedHomogeneous (w:σ → M) (φ:MvPolynomial σ R) (m:M):Prop:=
 ∀ ⦃d⦄,coeff d φ≠0 → weight w d=m
variable (R)
set_option backward.isDefEq.respectTransparency false in
def weightedHomogeneousSubmodule (w:σ → M) (m:M):Submodule R (MvPolynomial σ R) where
 carrier:={ x | x.IsWeightedHomogeneous w m}
 smul_mem' r a ha c hc:=by
   rw [coeff_smul] at hc
   exact ha (right_ne_zero_of_mul hc)
 zero_mem' _ hd:=False.elim (hd <| coeff_zero _)
 add_mem' {a} {b} ha hb c hc:=by
   rw [coeff_add] at hc
   obtain h | h:coeff c a≠0∨coeff c b≠0:=by
     contrapose! hc
     simp only [hc,add_zero]
   · exact ha h
   · exact hb h
@[simp]
theorem mem_weightedHomogeneousSubmodule (w:σ → M) (m:M) (p:MvPolynomial σ R):
   p∈weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m:=
 Iff.rfl
set_option backward.isDefEq.respectTransparency false in
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w:σ → M) (m:M):
   weightedHomogeneousSubmodule R w m=AddMonoidAlgebra.supported R R {d | weight w d=m}:=by
 ext x
 simp [IsWeightedHomogeneous]
 simp [AddMonoidAlgebra.mem_supported,Set.subset_def,MvPolynomial,coeff]
lemma weightedHomogeneousSubmodule_fg [Finite σ] (w:σ → ℕ) (hw:∀ (x:σ),w x≠0) (n:ℕ):
   (weightedHomogeneousSubmodule R w n).FG:=by
 rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ←Module.Finite.iff_fg]
 have:=(Finsupp.finite_of_nat_weight_eq w hw n).to_subtype
 exact Module.Finite.of_basis (basisRestrictSupport R {d | Finsupp.weight w d=n})
variable {R}
set_option backward.isDefEq.respectTransparency false in
theorem weightedHomogeneousSubmodule_mul (w:σ → M) (m n:M):
   weightedHomogeneousSubmodule R w m*weightedHomogeneousSubmodule R w n ≤
     weightedHomogeneousSubmodule R w (m+n):=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 letI:DecidableEq R:=Classical.decEq R
 rw [Submodule.mul_le]
 intro φ hφ ψ hψ c hc
 rw [coeff_mul] at hc
 obtain ⟨⟨d,e⟩,hde,H⟩:=Finset.exists_ne_zero_of_sum_ne_zero hc
 have aux:coeff d φ≠0∧coeff e ψ≠0:=by
   contrapose! H
   by_cases h:coeff d φ=0 <;>
     simp_all only [Ne,not_false_iff,zero_mul,mul_zero]
 rw [←mem_antidiagonal.mp hde, ←hφ aux.1, ←hψ aux.2,map_add]
theorem isWeightedHomogeneous_monomial (w:σ → M) (d:σ →₀ ℕ) (r:R) {m:M}
   (hm:weight w d=m):IsWeightedHomogeneous w (monomial d r) m:=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 intro c hc
 rw [coeff_monomial] at hc
 split_ifs at hc with h
 · subst c
   exact hm
 · contradiction
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w:σ → M)
   {p:MvPolynomial σ R} (hp:weightedTotalDegree w p=(⊥:M)):
   IsWeightedHomogeneous w p (⊥:M):=by
 intro d hd
 have h:=weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d,hd⟩)
 simp only [weightedTotalDegree',hp] at h
 rw [eq_bot_iff, ←WithBot.coe_le_coe, ←h]
 apply Finset.le_sup (mem_support_iff.mpr hd)
theorem isWeightedHomogeneous_C (w:σ → M) (r:R):
   IsWeightedHomogeneous w (C r:MvPolynomial σ R) 0:=
 isWeightedHomogeneous_monomial _ _ _ (map_zero _)
variable (R)
theorem isWeightedHomogeneous_zero (w:σ → M) (m:M):
   IsWeightedHomogeneous w (0:MvPolynomial σ R) m:=
 (weightedHomogeneousSubmodule R w m).zero_mem
theorem isWeightedHomogeneous_one (w:σ → M):IsWeightedHomogeneous w (1:MvPolynomial σ R) 0:=
 isWeightedHomogeneous_C _ _
lemma isWeightedHomogeneous_of_isEmpty [IsEmpty σ] (w:σ → M) (f:MvPolynomial σ R):
   IsWeightedHomogeneous w f 0:=by
 rw [eq_C_of_isEmpty f]
 exact isWeightedHomogeneous_C _ _
theorem isWeightedHomogeneous_X (w:σ → M) (i:σ):
   IsWeightedHomogeneous w (_root_.MvPolynomial.X i:MvPolynomial σ R) (w i):=by
 apply isWeightedHomogeneous_monomial
 simp only [weight,LinearMap.toAddMonoidHom_coe,linearCombination_single,one_nsmul]
namespace IsWeightedHomogeneous
variable {R}
 {φ ψ:MvPolynomial σ R} {m n:M}
theorem coeff_eq_zero {w:σ → M} (hφ:IsWeightedHomogeneous w φ n) (d:σ →₀ ℕ)
   (hd:weight w d≠n):coeff d φ=0:=by
 have aux:=mt (@hφ d) hd
 rwa [Classical.not_not] at aux
theorem inj_right {w:σ → M} (hφ:φ≠0) (hm:IsWeightedHomogeneous w φ m)
   (hn:IsWeightedHomogeneous w φ n):m=n:=by
 obtain ⟨d,hd⟩:∃ d,coeff d φ≠0:=exists_coeff_ne_zero hφ
 rw [←hm hd, ←hn hd]
theorem add {w:σ → M} (hφ:IsWeightedHomogeneous w φ n) (hψ:IsWeightedHomogeneous w ψ n):
   IsWeightedHomogeneous w (φ+ψ) n:=
 (weightedHomogeneousSubmodule R w n).add_mem hφ hψ
theorem sum {ι:Type*} (s:Finset ι) (φ:ι → MvPolynomial σ R) (n:M) {w:σ → M}
   (h:∀ i∈s,IsWeightedHomogeneous w (φ i) n):IsWeightedHomogeneous w (∑ i∈s,φ i) n:=
 (weightedHomogeneousSubmodule R w n).sum_mem h
set_option backward.isDefEq.respectTransparency false in
theorem mul {w:σ → M} (hφ:IsWeightedHomogeneous w φ m) (hψ:IsWeightedHomogeneous w ψ n):
   IsWeightedHomogeneous w (φ*ψ) (m+n):=
 weightedHomogeneousSubmodule_mul w m n <| Submodule.mul_mem_mul hφ hψ
lemma C_mul {w:σ → M} (hφ:IsWeightedHomogeneous w φ m) (r:R):
   IsWeightedHomogeneous w (C r*φ) m:=by
 rw [←zero_add m]
 exact (isWeightedHomogeneous_C w r).mul hφ
theorem pow {w:σ → M} (hφ:IsWeightedHomogeneous w φ m) (n:ℕ):
   IsWeightedHomogeneous w (φ^n) (n • m):=by
 induction n with
 | zero => rw [pow_zero,zero_smul];exact isWeightedHomogeneous_one R w
 | succ n ih => rw [pow_succ,succ_nsmul];exact ih.mul hφ
theorem prod {ι:Type*} (s:Finset ι) (φ:ι → MvPolynomial σ R) (n:ι → M) {w:σ → M}:
   (∀ i∈s,IsWeightedHomogeneous w (φ i) (n i)) →
     IsWeightedHomogeneous w (∏ i∈s,φ i) (∑ i∈s,n i):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 refine Finset.induction_on s ?_ ?_
 · intro
   simp only [isWeightedHomogeneous_one,Finset.sum_empty,Finset.prod_empty]
 · intro i s his IH h
   simp only [his,Finset.prod_insert,Finset.sum_insert,not_false_iff]
   apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
   intro j hjs
   exact h j (Finset.mem_insert_of_mem hjs)
theorem weighted_total_degree [SemilatticeSup M] {w:σ → M} (hφ:IsWeightedHomogeneous w φ n)
   (h:φ≠0):weightedTotalDegree' w φ=n:=by
 simp only [weightedTotalDegree']
 apply le_antisymm
 · simp only [Finset.sup_le_iff,mem_support_iff,WithBot.coe_le_coe]
   exact fun d hd => le_of_eq (hφ hd)
 · obtain ⟨d,hd⟩:∃ d,coeff d φ≠0:=exists_coeff_ne_zero h
   simp only [←hφ hd]
   replace hd:=Finsupp.mem_support_iff.mpr hd
   apply Finset.le_sup hd
set_option backward.isDefEq.respectTransparency false in
lemma induction_on {w:σ → M} {m:M}
   {motive:(p:MvPolynomial σ R) → p.IsWeightedHomogeneous w m → Prop}
   (zero:motive 0 (isWeightedHomogeneous_zero R w m))
   (add:∀ p q hp hq,motive p hp → motive q hq → motive (p+q) (hp.add hq))
   (monomial:∀ (d:σ →₀ ℕ) (r:R) (hr:Finsupp.weight w d=m),
     motive ((monomial d) r) (isWeightedHomogeneous_monomial w d r hr))
   {p:MvPolynomial σ R} (hp:p.IsWeightedHomogeneous w m):
   motive p hp:=by
 suffices h:∀ a,motive (C a*p) (.C_mul hp _) by simpa using h 1
 let A:Submodule R (MvPolynomial σ R):=
   { carrier:={ p | ∃ hp,∀ a,motive (C a*p) (.C_mul hp _)}
     add_mem':=fun ⟨_,hx⟩ ⟨_,hy⟩↦
       ⟨.add ‹_› ‹_›,fun a↦by simp [mul_add,add _ _ _ _ (hx a) (hy a)]⟩
     zero_mem':=⟨isWeightedHomogeneous_zero R w m,by simp [zero]⟩
     smul_mem':=fun a x ⟨_,hx⟩↦⟨by simp [Algebra.smul_def,C_mul ‹_› a],fun a↦by
       simp_rw [Algebra.smul_def,algebraMap_eq, ←mul_assoc, ←map_mul]
       apply hx⟩}
 rw [←mem_weightedHomogeneousSubmodule,weightedHomogeneousSubmodule_eq_finsupp_supported,
   AddMonoidAlgebra.supported_eq_span_single] at hp
 refine (Submodule.span_le (p:=A) |>.mpr ?_ hp).2
 rw [Set.image_subset_iff]
 intro d hd
 simp only [MvPolynomial,Submodule.coe_set_mk,AddSubmonoid.coe_set_mk,
   AddSubsemigroup.coe_set_mk,preimage_setOf_eq,mem_setOf_eq,A]
 refine ⟨isWeightedHomogeneous_monomial w d 1 hd,fun a↦?_⟩
 simpa only [single_eq_monomial, ←MvPolynomial.C_mul_monomial] using monomial _ (a*1) hd
end IsWeightedHomogeneous
variable {R}
lemma WeightedHomogeneousSubmodule.gradedMonoid {w:σ → M}:
   SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) where
 one_mem:=isWeightedHomogeneous_one R w
 mul_mem _ _ _ _:=IsWeightedHomogeneous.mul
def weightedHomogeneousComponent (w:σ → M) (n:M):MvPolynomial σ R →ₗ[R] MvPolynomial σ R:=
 letI:=Classical.decEq M
 (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
   Finsupp.restrictDom _ _ {d | weight w d=n} ∘ₗ (coeffLinearEquiv _).toLinearMap
section WeightedHomogeneousComponent
variable {w:σ → M} (n:M) (φ ψ:MvPolynomial σ R)
set_option backward.isDefEq.respectTransparency false in
theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d:σ →₀ ℕ):
   coeff d (weightedHomogeneousComponent w n φ)=
     if weight w d=n then coeff d φ else 0:=by
 simp [weightedHomogeneousComponent,MvPolynomial,coeff,Finsupp.filter_apply]
set_option backward.isDefEq.respectTransparency false in
theorem weightedHomogeneousComponent_apply [DecidableEq M]:
   weightedHomogeneousComponent w n φ=
     ∑ d∈φ.support with weight w d=n,monomial d (coeff d φ):=by
 simp [weightedHomogeneousComponent,MvPolynomial,coeff,Finsupp.filter_eq_sum,support,monomial]
 congr
theorem weightedHomogeneousComponent_isWeightedHomogeneous:
   (weightedHomogeneousComponent w n φ).IsWeightedHomogeneous w n:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 intro d hd
 contrapose! hd
 rw [coeff_weightedHomogeneousComponent,if_neg hd]
theorem weightedHomogeneousComponent_mem (w:σ → M) (φ:MvPolynomial σ R) (m:M):
   weightedHomogeneousComponent w m φ∈weightedHomogeneousSubmodule R w m:=by
 rw [mem_weightedHomogeneousSubmodule]
 exact weightedHomogeneousComponent_isWeightedHomogeneous m φ
@[simp]
theorem weightedHomogeneousComponent_C_mul (n:M) (r:R):
   weightedHomogeneousComponent w n (C r*φ)=C r*weightedHomogeneousComponent w n φ:=by
 simp only [C_mul',map_smul]
theorem weightedHomogeneousComponent_eq_zero'
   (h:∀ d:σ →₀ ℕ,d∈φ.support → weight w d≠n):
   weightedHomogeneousComponent w n φ=0:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 rw [weightedHomogeneousComponent_apply,sum_eq_zero]
 intro d hd;rw [mem_filter] at hd
 exfalso;exact h _ hd.1 hd.2
theorem weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M]
   (h:weightedTotalDegree w φ < n):weightedHomogeneousComponent w n φ=0:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 rw [weightedHomogeneousComponent_apply,sum_eq_zero]
 intro d hd
 rw [Finset.mem_filter] at hd
 exfalso
 apply lt_irrefl n
 nth_rw 1 [←hd.2]
 exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h
theorem weightedHomogeneousComponent_finsupp:
   (fun m => weightedHomogeneousComponent w m φ).HasFiniteSupport:=by
 apply ((fun d:σ →₀ ℕ => (weight w) d) '' (φ.support:Set (σ →₀ ℕ))).toFinite.subset
 intro m hm
 by_contra hm'
 apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
 simpa only [Set.mem_image,not_exists,not_and] using! hm'
variable (w)
theorem sum_weightedHomogeneousComponent:
   (finsum fun m => weightedHomogeneousComponent w m φ)=φ:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
 ext1 d
 simp only [coeff_sum,coeff_weightedHomogeneousComponent]
 rw [Finset.sum_eq_single (weight w d)]
 · rw [if_pos rfl]
 · intro m _ hm'
   rw [if_neg hm'.symm]
 · intro hm
   rw [if_pos rfl]
   simp only [Finite.mem_toFinset,mem_support,Ne,Classical.not_not] at hm
   have:=coeff_weightedHomogeneousComponent (w:=w) (weight w d) φ d
   rw [hm,if_pos rfl,coeff_zero] at this
   exact this.symm
theorem finsum_weightedHomogeneousComponent:
   (finsum fun m => weightedHomogeneousComponent w m φ)=φ:=by
 rw [sum_weightedHomogeneousComponent]
variable {w}
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_same {m:M} {p:MvPolynomial σ R}
   (hp:IsWeightedHomogeneous w p m):
   weightedHomogeneousComponent w m p=p:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 letI:DecidableEq R:=Classical.decEq R
 ext x
 rw [coeff_weightedHomogeneousComponent]
 by_cases zero_coeff:coeff x p=0
 · split_ifs
   · rfl
   rw [zero_coeff]
 · rw [hp zero_coeff,if_pos rfl]
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_ne {m:M} (n:M)
   {p:MvPolynomial σ R} (hp:IsWeightedHomogeneous w p m):
   n≠m → weightedHomogeneousComponent w n p=0:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 letI:DecidableEq R:=Classical.decEq R
 intro hn
 ext x
 rw [coeff_weightedHomogeneousComponent]
 by_cases zero_coeff:coeff x p=0
 · simp [zero_coeff]
 · rw [if_neg]
   · rw [coeff_zero]
   · rw [hp zero_coeff];exact Ne.symm hn
theorem weightedHomogeneousComponent_of_mem [DecidableEq M] {m n:M}
   {p:MvPolynomial σ R} (h:p∈weightedHomogeneousSubmodule R w n):
   weightedHomogeneousComponent w m p=if m=n then p else 0:=by
 letI:DecidableEq R:=Classical.decEq R
 simp only [mem_weightedHomogeneousSubmodule] at h
 ext x
 rw [coeff_weightedHomogeneousComponent]
 by_cases zero_coeff:coeff x p=0
 · split_ifs <;>
   simp only [zero_coeff,coeff_zero]
 · rw [h zero_coeff]
   simp only [show n=m ↔ m=n from eq_comm]
   split_ifs with h1
   · rfl
   · simp only [coeff_zero]
lemma weightedHomogeneousComponent_eq_self {n:M} {p:MvPolynomial σ R}
   (hp:p.IsWeightedHomogeneous w n):weightedHomogeneousComponent w n p=p:=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 simp [weightedHomogeneousComponent_of_mem hp]
lemma support_weightedHomogeneousComponent [DecidableEq M] (n:M) (p:MvPolynomial σ R):
   (weightedHomogeneousComponent w n p).support={c∈p.support | (weight w) c=n}:=by
 ext c
 simp [coeff_weightedHomogeneousComponent,And.comm]
variable (R w)
open DirectSum
theorem DirectSum.coeLinearMap_eq_dfinsuppSum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
   (x:DirectSum M fun i:M => ↥(weightedHomogeneousSubmodule R w i)):
   (coeLinearMap fun i:M => weightedHomogeneousSubmodule R w i) x=
     DFinsupp.sum x (fun _ x => ↑x):=by
 rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]
theorem DirectSum.coeAddMonoidHom_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
   (x:DirectSum M fun i:M => ↥(weightedHomogeneousSubmodule R w i)):
   (DirectSum.coeAddMonoidHom fun i:M => weightedHomogeneousSubmodule R w i) x=
     DFinsupp.sum x (fun _ x => ↑x):=
 DirectSum.coeLinearMap_eq_dfinsuppSum R w x
theorem DirectSum.coeLinearMap_eq_finsum [DecidableEq M]
   (x:DirectSum M fun i:M => ↥(weightedHomogeneousSubmodule R w i)):
   (DirectSum.coeLinearMap fun i:M => weightedHomogeneousSubmodule R w i) x=
     finsum fun m => x m:=by
 classical
 rw [DirectSum.coeLinearMap_eq_dfinsuppSum,DFinsupp.sum,finsum_eq_sum_of_support_subset]
 apply DirectSum.support_subset
theorem weightedHomogeneousComponent_directSum [DecidableEq M]
   (x:DirectSum M fun i:M => ↥(weightedHomogeneousSubmodule R w i)) (m:M):
   (weightedHomogeneousComponent w m)
     ((DirectSum.coeLinearMap fun i:M => weightedHomogeneousSubmodule R w i) x)=x m:=by
 classical
 rw [DirectSum.coeLinearMap_eq_dfinsuppSum,DFinsupp.sum,map_sum]
 convert! @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
 · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (x m).prop]
 · intro n _ hmn
   exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne m (x n).prop hmn.symm
 · rw [DFinsupp.notMem_support_iff]
   intro hm;rw [hm,Submodule.coe_zero,map_zero]
end WeightedHomogeneousComponent
end AddCommMonoid
section OrderedAddCommMonoid
variable [AddCommMonoid M] [PartialOrder M]
 {w:σ → M} (φ:MvPolynomial σ R)
@[simp]
theorem weightedHomogeneousComponent_zero [CanonicallyOrderedAdd M] [IsAddTorsionFree M]
   (hw:∀ i:σ,w i≠0):
   weightedHomogeneousComponent w 0 φ=C (coeff 0 φ):=by
 classical
 letI:DecidableEq M:=Classical.decEq M
 letI:DecidableEq σ:=Classical.decEq σ
 ext1 d
 rcases Classical.em (d=0) with (rfl | hd)
 · simp only [coeff_weightedHomogeneousComponent,if_pos,map_zero,coeff_zero_C]
 · rw [coeff_weightedHomogeneousComponent,if_neg,coeff_C,if_neg (Ne.symm hd)]
   simp only [weight,LinearMap.toAddMonoidHom_coe,Finsupp.linearCombination_apply,Finsupp.sum,
     sum_eq_zero_iff,Finsupp.mem_support_iff,Ne,smul_eq_zero,not_forall,not_or,
     and_self_left,exists_prop]
   simp only [DFunLike.ext_iff,Finsupp.coe_zero,Pi.zero_apply,not_forall] at hd
   obtain ⟨i,hi⟩:=hd
   exact ⟨i,hi,hw i⟩
def NonTorsionWeight (w:σ → M):=
 ∀ n x,n • w x=(0:M) → n=0
omit [PartialOrder M] in
theorem nonTorsionWeight_of [IsAddTorsionFree M] (hw:∀ i:σ,w i≠0):
   NonTorsionWeight w:=
 fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx
theorem weightedDegree_eq_zero_iff [CanonicallyOrderedAdd M]
   (hw:NonTorsionWeight w) {m:σ →₀ ℕ}:
   weight w m=0 ↔ ∀ x:σ,m x=0:=by
 simp only [weight,Finsupp.linearCombination,LinearMap.toAddMonoidHom_coe,coe_lsum,
   LinearMap.coe_smulRight,LinearMap.id_coe,id_eq]
 rw [Finsupp.sum,Finset.sum_eq_zero_iff]
 apply forall_congr'
 intro x
 rw [Finsupp.mem_support_iff]
 constructor
 · intro hx
   by_contra hx'
   exact absurd (hw _ _ (hx hx')) hx'
 · order
end OrderedAddCommMonoid
section LinearOrderedAddCommMonoid
variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] [CanonicallyOrderedAdd M]
 {w:σ → M} (φ:MvPolynomial σ R)
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p:MvPolynomial σ R}:
   IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w=0:=by
 rw [weightedTotalDegree, ←bot_eq_zero,Finset.sup_eq_bot_iff,bot_eq_zero,IsWeightedHomogeneous]
 apply forall_congr'
 intro m
 rw [mem_support_iff]
theorem weightedTotalDegree_eq_zero_iff (hw:NonTorsionWeight w) (p:MvPolynomial σ R):
   p.weightedTotalDegree w=0 ↔ ∀ (m:σ →₀ ℕ) (_:m∈p.support) (x:σ),m x=0:=by
 rw [←isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero,IsWeightedHomogeneous]
 apply forall_congr'
 intro m
 rw [mem_support_iff]
 apply forall_congr'
 intro _
 exact weightedDegree_eq_zero_iff hw
end LinearOrderedAddCommMonoid
section GradedAlgebra
variable (w:σ → M) [AddCommMonoid M]
theorem weightedHomogeneousComponent_eq_zero_of_notMem [DecidableEq M]
   (φ:MvPolynomial σ R) (i:M) (hi:i∉Finset.image (weight w) φ.support):
   weightedHomogeneousComponent w i φ=0:=by
 apply weightedHomogeneousComponent_eq_zero'
 simp only [Finset.mem_image,mem_support_iff,ne_eq,not_exists,not_and] at hi
 exact fun m hm↦hi m (mem_support_iff.mp hm)
variable (R)
def decompose' [DecidableEq M]:=fun φ:MvPolynomial σ R =>
 DirectSum.mk (fun i:M => ↥(weightedHomogeneousSubmodule R w i))
   (Finset.image (weight w) φ.support) fun m =>
     ⟨weightedHomogeneousComponent w m φ,weightedHomogeneousComponent_mem w φ m⟩
theorem decompose'_apply [DecidableEq M] (φ:MvPolynomial σ R) (m:M):
   (decompose' R w φ m:MvPolynomial σ R)=weightedHomogeneousComponent w m φ:=by
 rw [decompose']
 by_cases hm:m∈Finset.image (weight w) φ.support
 · simp only [DirectSum.mk_apply_of_mem hm,Subtype.coe_mk]
 · rw [DirectSum.mk_apply_of_notMem hm,Submodule.coe_zero,
     weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]
@[implicit_reducible]
def weightedDecomposition [DecidableEq M]:
   DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
 decompose':=decompose' R w
 left_inv φ:=by
   classical
   conv_rhs => rw [←sum_weightedHomogeneousComponent w φ]
   rw [←DirectSum.sum_support_of (decompose' R w φ)]
   simp only [DirectSum.coeAddMonoidHom_of,map_sum,
     finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
   apply Finset.sum_congr _ (fun m _↦by rw [decompose'_apply])
   ext m
   simp only [DFinsupp.mem_support_toFun,ne_eq,Set.Finite.mem_toFinset,Function.mem_support,
     not_iff_not]
   conv_lhs => rw [←Subtype.coe_inj]
   rw [decompose'_apply,Submodule.coe_zero]
 right_inv x:=by
   classical
   apply DFinsupp.ext
   intro m
   rw [←Subtype.coe_inj,decompose'_apply]
   exact weightedHomogeneousComponent_directSum R w x m
set_option linter.style.whitespace false in
@[implicit_reducible]
def weightedGradedAlgebra [DecidableEq M]:
   GradedAlgebra (weightedHomogeneousSubmodule R w) where
 toDecomposition:=weightedDecomposition R w
 toGradedMonoid:=WeightedHomogeneousSubmodule.gradedMonoid
theorem weightedDecomposition.decompose'_eq [DecidableEq M]:
   (weightedDecomposition R w).decompose'=fun φ:MvPolynomial σ R =>
     DirectSum.mk (fun i:M => ↥(weightedHomogeneousSubmodule R w i))
       (Finset.image (weight w) φ.support) fun m =>
         ⟨weightedHomogeneousComponent w m φ,weightedHomogeneousComponent_mem w φ m⟩:=rfl
theorem weightedDecomposition.decompose'_apply [DecidableEq M]
   (φ:MvPolynomial σ R) (m:M):
   ((weightedDecomposition R w).decompose' φ m:MvPolynomial σ R)=
     weightedHomogeneousComponent w m φ:=
 MvPolynomial.decompose'_apply R w φ m
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma mem_iff_weightedHomogeneousComponent_mem [DecidableEq M] {I:Ideal (MvPolynomial σ R)}
   (h:I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (p:MvPolynomial σ R):
   p∈I ↔ ∀ m:M,(weightedHomogeneousComponent w m p)∈I:=by
 simp_rw [←weightedDecomposition.decompose'_apply]
 exact h.mem_iff
lemma weightedHomogeneousComponent_mem_of_mem [DecidableEq M] {I:Ideal (MvPolynomial σ R)}
   (h:I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {p:MvPolynomial σ R} (hp:p∈I)
   (m:M):(weightedHomogeneousComponent w m p)∈I:=
 (mem_iff_weightedHomogeneousComponent_mem R w h p).mp hp m
end GradedAlgebra
end MvPolynomial
end
end ProximityFlatProofPort
end PackedLegacy_IP

/-! Packed from ProximityPrize.SubmissionLower.F3. -/
section PackedLegacy_F3
section ProximityFlatProofPort
namespace MvPolynomial
variable {σ:Type*} {τ:Type*} {R:Type*} {S:Type*}
open Finsupp
def IsHomogeneous [CommSemiring R] (φ:MvPolynomial σ R) (n:ℕ):=
 IsWeightedHomogeneous 1 φ n
variable [CommSemiring R]
@[simp]
theorem weightedTotalDegree_singleton [DecidableEq σ] (p:MvPolynomial σ R):
   weightedTotalDegree (fun i => {i}) p=degrees p:=by
 rw [degrees_def];rfl
theorem weightedTotalDegree_one (φ:MvPolynomial σ R):
   weightedTotalDegree (1:σ → ℕ) φ=φ.totalDegree:=by
 simp only [totalDegree,weightedTotalDegree,weight,LinearMap.toAddMonoidHom_coe,
   linearCombination,Pi.one_apply,Finsupp.coe_lsum,LinearMap.coe_smulRight,LinearMap.id_coe,
   id,smul_eq_mul,mul_one]
@[simp]
theorem weightedTotalDegree_piSingle [DecidableEq σ] (i:σ) (p:MvPolynomial σ R):
   weightedTotalDegree (Pi.single i 1) p=degreeOf i p:=by
 simp only [weightedTotalDegree,weight,linearCombination,Pi.single_apply,degreeOf,degrees,
   Multiset.count_finset_sup]
 congr;ext d
 simp+contextual
theorem weightedTotalDegree_rename_of_injective {σ τ:Type*} {e:σ → τ}
   {w:τ → ℕ} {P:MvPolynomial σ R} (he:Function.Injective e):
   weightedTotalDegree w (rename e P)=weightedTotalDegree (w ∘ e) P:=by
 classical
 letI:DecidableEq τ:=Classical.decEq τ
 unfold weightedTotalDegree
 rw [support_rename_of_injective he,Finset.sup_image]
 congr;ext;unfold weight;simp
variable (σ R)
def homogeneousSubmodule (n:ℕ):Submodule R (MvPolynomial σ R) where
 carrier:={ x | x.IsHomogeneous n}
 __:=weightedHomogeneousSubmodule R 1 n
@[simp]
lemma weightedHomogeneousSubmodule_one (n:ℕ):
   weightedHomogeneousSubmodule R 1 n=homogeneousSubmodule σ R n:=rfl
variable {σ R}
@[simp]
theorem mem_homogeneousSubmodule (n:ℕ) (p:MvPolynomial σ R):
   p∈homogeneousSubmodule σ R n ↔ p.IsHomogeneous n:=Iff.rfl
variable (σ R)
theorem homogeneousSubmodule_eq_finsupp_supported (n:ℕ):
   homogeneousSubmodule σ R n=AddMonoidAlgebra.supported _ R {d | d.degree=n}:=by
 simp_rw [degree_eq_weight_one]
 exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n
lemma homogeneousSubmodule_fg [Finite σ] (n:ℕ):
   (homogeneousSubmodule σ R n).FG:=
 weightedHomogeneousSubmodule_fg R (1:σ → ℕ) (by simp) n
variable {σ R}
set_option backward.isDefEq.respectTransparency false in
theorem homogeneousSubmodule_mul (m n:ℕ):
   homogeneousSubmodule σ R m*homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m+n):=
 weightedHomogeneousSubmodule_mul 1 m n
set_option backward.isDefEq.respectTransparency false in
lemma homogeneousSubmodule_one_eq_span_X:
   MvPolynomial.homogeneousSubmodule σ R 1=.span R (.range _root_.MvPolynomial.X):=by
 simp [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
   AddMonoidAlgebra.supported_eq_span_single,MvPolynomial.single_eq_monomial,
   ←Finsupp.range_single_one, ←Set.range_comp,Function.comp_def, ←X_pow_eq_monomial]
section
theorem isHomogeneous_monomial {d:σ →₀ ℕ} (r:R) {n:ℕ} (hn:d.degree=n):
   IsHomogeneous (monomial d r) n:=by
 rw [degree_eq_weight_one] at hn
 exact isWeightedHomogeneous_monomial 1 d r hn
variable (σ)
theorem totalDegree_eq_zero_iff (p:MvPolynomial σ R):
   p.totalDegree=0 ↔ ∀ (m:σ →₀ ℕ) (_:m∈p.support) (x:σ),m x=0:=by
 rw [←weightedTotalDegree_one,weightedTotalDegree_eq_zero_iff _ p]
 exact nonTorsionWeight_of (Function.const σ one_ne_zero)
theorem totalDegree_zero_iff_isHomogeneous {p:MvPolynomial σ R}:
   p.totalDegree=0 ↔ IsHomogeneous p 0:=by
 rw [←weightedTotalDegree_one,
   ←isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero,IsHomogeneous]
alias ⟨isHomogeneous_of_totalDegree_zero,_⟩:=totalDegree_zero_iff_isHomogeneous
@[simp]
lemma homogeneousSubmodule_zero:
   MvPolynomial.homogeneousSubmodule σ R 0=1:=by
 ext
 rw [MvPolynomial.mem_homogeneousSubmodule,
   ←MvPolynomial.totalDegree_zero_iff_isHomogeneous,Submodule.mem_one,
   MvPolynomial.algebraMap_eq,MvPolynomial.totalDegree_eq_zero_iff_eq_C]
 grind [coeff_zero_C]
theorem isHomogeneous_C (r:R):IsHomogeneous (C r:MvPolynomial σ R) 0:=by
 apply isHomogeneous_monomial
 simp only [degree_apply,Finsupp.support_zero,Finsupp.zero_apply,Finset.sum_const_zero]
variable (R)
theorem isHomogeneous_zero (n:ℕ):IsHomogeneous (0:MvPolynomial σ R) n:=
 (homogeneousSubmodule σ R n).zero_mem
theorem isHomogeneous_one:IsHomogeneous (1:MvPolynomial σ R) 0:=
 isHomogeneous_C _ _
lemma isHomogeneous_of_isEmpty [IsEmpty σ] (f:MvPolynomial σ R):f.IsHomogeneous 0:=by
 rw [eq_C_of_isEmpty f]
 exact isHomogeneous_C _ _
variable {σ}
theorem isHomogeneous_X (i:σ):IsHomogeneous (_root_.MvPolynomial.X i:MvPolynomial σ R) 1:=by
 apply isHomogeneous_monomial
 simp only [degree_apply,Finsupp.support_single _ one_ne_zero,Finset.sum_singleton,
   single_eq_same]
variable {R} in
lemma monomial_mem_homogeneousSubmodule_pow_degree
   (r:R) (s:σ →₀ ℕ):
   monomial s r∈(homogeneousSubmodule σ R 1)^s.degree:=by
 induction s using Finsupp.induction with
 | zero => simp
 | single_add a b f _ _ h =>
   rw [map_add,Finsupp.degree_single,monomial_single_add,pow_add]
   exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (isHomogeneous_X R a) _) h
@[simp]
lemma homogeneousSubmodule_one_pow (n:ℕ):
   (homogeneousSubmodule σ R 1)^n=homogeneousSubmodule σ R n:=by
 refine le_antisymm ?_ fun x hx↦?_
 · induction n with
   | zero => simp [homogeneousSubmodule_zero]
   | succ n ih =>
     grw [pow_add,pow_one,ih]
     apply homogeneousSubmodule_mul
 · simp only [mem_homogeneousSubmodule] at hx
   induction hx using IsWeightedHomogeneous.induction_on with
   | zero => simp
   | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
   | monomial d r hr =>
     convert! monomial_mem_homogeneousSubmodule_pow_degree _ _
     rw [Finsupp.degree_eq_weight_one, ←Pi.one_def, ←hr]
end
namespace IsHomogeneous
variable [CommSemiring S] {φ ψ:MvPolynomial σ R} {m n:ℕ}
theorem coeff_eq_zero (hφ:IsHomogeneous φ n) {d:σ →₀ ℕ} (hd:d.degree≠n):
   coeff d φ=0:=by
 rw [degree_eq_weight_one] at hd
 exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd
theorem inj_right (hm:IsHomogeneous φ m) (hn:IsHomogeneous φ n) (hφ:φ≠0):m=n:=by
 obtain ⟨d,hd⟩:∃ d,coeff d φ≠0:=exists_coeff_ne_zero hφ
 rw [←hm hd, ←hn hd]
theorem add (hφ:IsHomogeneous φ n) (hψ:IsHomogeneous ψ n):IsHomogeneous (φ+ψ) n:=
 (homogeneousSubmodule σ R n).add_mem hφ hψ
theorem sum {ι:Type*} (s:Finset ι) (φ:ι → MvPolynomial σ R) (n:ℕ)
   (h:∀ i∈s,IsHomogeneous (φ i) n):IsHomogeneous (∑ i∈s,φ i) n:=
 (homogeneousSubmodule σ R n).sum_mem h
set_option backward.isDefEq.respectTransparency false in
theorem mul (hφ:IsHomogeneous φ m) (hψ:IsHomogeneous ψ n):IsHomogeneous (φ*ψ) (m+n):=
 homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ
theorem prod {ι:Type*} (s:Finset ι) (φ:ι → MvPolynomial σ R) (n:ι → ℕ)
   (h:∀ i∈s,IsHomogeneous (φ i) (n i)):IsHomogeneous (∏ i∈s,φ i) (∑ i∈s,n i):=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 revert h
 refine Finset.induction_on s ?_ ?_
 · intro
   simp only [isHomogeneous_one,Finset.sum_empty,Finset.prod_empty]
 · intro i s his IH h
   simp only [his,Finset.prod_insert,Finset.sum_insert,not_false_iff]
   apply (h i (by grind)).mul (IH _)
   grind
lemma C_mul (hφ:φ.IsHomogeneous m) (r:R):
   (C r*φ).IsHomogeneous m:=by
 simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X (r:R) (i:σ):
   (C r*_root_.MvPolynomial.X i).IsHomogeneous 1:=
 (isHomogeneous_X _ _).C_mul _
lemma pow (hφ:φ.IsHomogeneous m) (n:ℕ):(φ^n).IsHomogeneous (m*n):=by
 rw [show φ^n=∏ _i∈Finset.range n,φ by simp]
 rw [show m*n=∑ _i∈Finset.range n,m by simp [mul_comm]]
 apply IsHomogeneous.prod _ _ _ (fun _ _↦hφ)
lemma _root_.MvPolynomial.isHomogeneous_X_pow (i:σ) (n:ℕ):
   (_root_.MvPolynomial.X (R:=R) i^n).IsHomogeneous n:=by
 simpa only [one_mul] using (isHomogeneous_X _ _).pow n
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow (r:R) (i:σ) (n:ℕ):
   (C r*_root_.MvPolynomial.X i^n).IsHomogeneous n:=
 (isHomogeneous_X_pow _ _).C_mul _
lemma eval₂ (hφ:φ.IsHomogeneous m) (f:R →+*MvPolynomial τ S) (g:σ → MvPolynomial τ S)
   (hf:∀ r,(f r).IsHomogeneous 0) (hg:∀ i,(g i).IsHomogeneous n):
   (eval₂ f g φ).IsHomogeneous (n*m):=by
 apply IsHomogeneous.sum
 intro i hi
 rw [←zero_add (n*m)]
 apply IsHomogeneous.mul (hf _) _
 convert! IsHomogeneous.prod _ _ (fun k↦n*i k) _
 · rw [Finsupp.mem_support_iff] at hi
   rw [←Finset.mul_sum, ←hφ hi,weight_apply]
   simp_rw [smul_eq_mul,Finsupp.sum,Pi.one_apply,mul_one]
 · rintro k-
   apply (hg k).pow
protected lemma map (hφ:φ.IsHomogeneous n) (f:R →+*S):(map f φ).IsHomogeneous n:=by
 rw [map_eq_eval₂Hom_C_comp,MvPolynomial.coe_eval₂Hom]
 simpa only [one_mul] using hφ.eval₂ _ _ (fun r↦isHomogeneous_C _ (f r)) (isHomogeneous_X _)
lemma of_map {f:R →+*S} (hf:Function.Injective f)
   (h:(MvPolynomial.map f φ).IsHomogeneous n):φ.IsHomogeneous n:=
 fun u hu↦h (coeff_map f φ u ▸ map_zero f ▸ hf.ne hu)
lemma aeval [Algebra R S] (hφ:φ.IsHomogeneous m)
   (g:σ → MvPolynomial τ S) (hg:∀ i,(g i).IsHomogeneous n):
   (aeval g φ).IsHomogeneous (n*m):=
 hφ.eval₂ _ _ (fun _↦isHomogeneous_C _ _) hg
section CommRing
variable {R σ:Type*} [CommRing R] {φ ψ:MvPolynomial σ R} {n:ℕ}
theorem neg (hφ:IsHomogeneous φ n):IsHomogeneous (-φ) n:=
 (homogeneousSubmodule σ R n).neg_mem hφ
theorem sub (hφ:IsHomogeneous φ n) (hψ:IsHomogeneous ψ n):IsHomogeneous (φ-ψ) n:=
 (homogeneousSubmodule σ R n).sub_mem hφ hψ
end CommRing
lemma totalDegree_le (hφ:IsHomogeneous φ n):φ.totalDegree ≤ n:=by
 apply Finset.sup_le
 intro d hd
 rw [mem_support_iff] at hd
 simp_rw [Finsupp.sum, ←hφ hd,weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum,
   le_rfl]
theorem totalDegree (hφ:IsHomogeneous φ n) (h:φ≠0):totalDegree φ=n:=by
 apply le_antisymm hφ.totalDegree_le
 obtain ⟨d,hd⟩:∃ d,coeff d φ≠0:=exists_coeff_ne_zero h
 simp only [←hφ hd,MvPolynomial.totalDegree,Finsupp.sum]
 replace hd:=Finsupp.mem_support_iff.mpr hd
 simp only [weight_apply,Pi.one_apply,smul_eq_mul,mul_one]
 exact Finset.le_sup (f:=fun s↦∑ x∈s.support,s x) hd
lemma degree_eq_sum_deg_support (hφ:φ.IsHomogeneous n) {s:σ →₀ ℕ} (hs:s∈φ.support):
   n=∑ i∈s.support,s i:=by
 simp [←hφ <| mem_support_iff.mp hs, ←degree_apply,degree_eq_weight_one,Pi.one_def]
theorem rename_isHomogeneous {f:σ → τ} (h:φ.IsHomogeneous n):
   (rename f φ).IsHomogeneous n:=by
 rw [←φ.support_sum_monomial_coeff,map_sum];simp_rw [rename_monomial]
 apply IsHomogeneous.sum _ _ _ fun d hd↦isHomogeneous_monomial _ _
 intro d hd
 apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _↦.id ℕ).trans
 convert! h (mem_support_iff.mp hd)
 simp only [weight_apply,AddMonoidHom.id_apply,Pi.one_apply,smul_eq_mul,mul_one]
theorem rename_isHomogeneous_iff {f:σ → τ} (hf:f.Injective):
   (rename f φ).IsHomogeneous n ↔ φ.IsHomogeneous n:=by
 refine ⟨fun h d hd↦?_,rename_isHomogeneous⟩
 convert!←@h (d.mapDomain f) _
 · simp only [weight_apply,Pi.one_apply,smul_eq_mul,mul_one]
   exact Finsupp.sum_mapDomain_index_inj (h:=fun _↦id) hf
 · rwa [coeff_rename_mapDomain f hf]
lemma finSuccEquiv_coeff_isHomogeneous {N:ℕ} {φ:MvPolynomial (Fin (N+1)) R} {n:ℕ}
   (hφ:φ.IsHomogeneous n) (i j:ℕ) (h:i+j=n):
   ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j:=by
 intro d hd
 rw [finSuccEquiv_coeff_coeff] at hd
 have h':(weight 1) (Finsupp.cons i d)=i+j:=by
   simpa [Finset.sum_subset_zero_on_sdiff (g:=d.cons i)
    (d.cons_support (y:=i)) (by simp) (fun _ _↦rfl), ←h] using hφ hd
 simp only [weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum_cons,
   add_right_inj] at h' ⊢
 exact h'
set_option backward.defeqAttrib.useBackward true in
lemma coeff_isHomogeneous_of_optionEquivLeft_symm
   [hσ:Finite σ] {p:Polynomial (MvPolynomial σ R)}
   (hp:((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j:ℕ) (h:i+j=n):
   (p.coeff i).IsHomogeneous j:=by
 obtain ⟨k,⟨e⟩⟩:=Finite.exists_equiv_fin σ
 let e':=e.optionCongr.trans (_root_.finSuccEquiv _).symm
 let F:=renameEquiv R e
 let F':=renameEquiv R e'
 let φ:=F' ((optionEquivLeft R σ).symm p)
 have hφ:φ.IsHomogeneous n:=hp.rename_isHomogeneous
 suffices IsHomogeneous (F (p.coeff i)) j by
   rwa [←(IsHomogeneous.rename_isHomogeneous_iff e.injective)]
 convert! hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
 dsimp only [φ,F',F,renameEquiv_apply]
 rw [finSuccEquiv_rename_finSuccEquiv,AlgEquiv.apply_symm_apply]
 simp
open Polynomial in
private
lemma exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
   {N:ℕ} {F:MvPolynomial (Fin (Nat.succ N)) R} {n:ℕ} (hF:IsHomogeneous F n)
   (hFn:((finSuccEquiv R N) F).coeff n≠0):
   ∃ r,eval r F≠0:=by
 have hF₀:F≠0:=by contrapose hFn;simp [hFn]
 have hdeg:natDegree (finSuccEquiv R N F) < n+1:=by
   linarith [natDegree_finSuccEquiv F,degreeOf_le_totalDegree F 0,hF.totalDegree hF₀]
 use Fin.cons 1 0
 have aux:∀ i∈Finset.range n,constantCoeff ((finSuccEquiv R N F).coeff i)=0:=by
   intro i hi
   rw [Finset.mem_range] at hi
   apply (hF.finSuccEquiv_coeff_isHomogeneous i (n-i) (by lia)).coeff_eq_zero
   simp only [map_zero]
   rw [←Nat.sub_ne_zero_iff_lt] at hi
   exact hi.symm
 simp_rw [eval_eq_eval_mv_eval',eval_one_map,Polynomial.eval_eq_sum_range' hdeg,
   eval_zero,one_pow,mul_one,map_sum,Finset.sum_range_succ,Finset.sum_eq_zero aux,zero_add]
 contrapose hFn
 ext d
 rw [coeff_zero]
 obtain rfl | hd:=eq_or_ne d 0
 · apply hFn
 · contrapose! hd
   ext i
   rw [Finsupp.coe_zero,Pi.zero_apply]
   by_cases hi:i∈d.support
   · have:=hF.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero _) hd
     simp only [weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum] at this
     rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _↦zero_le)] at this
     exact this i hi
   · simpa using hi
section IsDomain
variable {R σ:Type*} [CommRing R] [IsDomain R] {F G:MvPolynomial σ R} {n:ℕ}
open Cardinal Polynomial
private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux {N:ℕ} {F:MvPolynomial (Fin N) R} {n:ℕ}
   (hF:F.IsHomogeneous n) (hF₀:F≠0) (hnR:n ≤ #R):
   ∃ r,eval r F≠0:=by
 induction N generalizing n with
 | zero =>
   use 0
   contrapose hF₀
   ext d
   simpa only [Subsingleton.elim d 0,eval_zero,coeff_zero] using! hF₀
 | succ N IH =>
   have hdeg:natDegree (finSuccEquiv R N F) < n+1:=by
     linarith [natDegree_finSuccEquiv F,degreeOf_le_totalDegree F 0,hF.totalDegree hF₀]
   obtain ⟨i,hi⟩:∃ i:ℕ,(finSuccEquiv R N F).coeff i≠0:=by
     contrapose! hF₀
     exact (finSuccEquiv _ _).injective <| Polynomial.ext <| by simpa using! hF₀
   have hin:i ≤ n:=by
     contrapose! hi
     exact coeff_eq_zero_of_natDegree_lt <| (Nat.le_of_lt_succ hdeg).trans_lt hi
   obtain hFn | hFn:=ne_or_eq ((finSuccEquiv R N F).coeff n) 0
   · exact hF.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux hFn
   have hin:i < n:=hin.lt_or_eq.elim id <| by aesop
   obtain ⟨j,hj⟩:∃ j,i+(j+1)=n:=(Nat.exists_eq_add_of_lt hin).imp <| by lia
   obtain ⟨r,hr⟩:∃ r,(eval r) (Polynomial.coeff ((finSuccEquiv R N) F) i)≠0:=
     IH (hF.finSuccEquiv_coeff_isHomogeneous _ _ hj) hi (.trans (by norm_cast;lia) hnR)
   set φ:R[X]:=Polynomial.map (eval r) (finSuccEquiv _ _ F) with hφ
   have hφ₀:φ≠0:=fun hφ₀↦hr <| by
     rw [←coeff_eval_eq_eval_coeff, ←hφ,hφ₀,Polynomial.coeff_zero]
   have hφR:φ.natDegree < #R:=by
     refine lt_of_lt_of_le ?_ hnR
     norm_cast
     refine lt_of_le_of_lt natDegree_map_le ?_
     suffices (finSuccEquiv _ _ F).natDegree≠n by lia
     rintro rfl
     refine leadingCoeff_ne_zero.mpr ?_ hFn
     simpa using! (finSuccEquiv R N).injective.ne hF₀
   obtain ⟨r₀,hr₀⟩:∃ r₀,Polynomial.eval r₀ φ≠0:=
     φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
   use Fin.cons r₀ r
   rwa [eval_eq_eval_mv_eval']
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
   (hF:F.IsHomogeneous n) (h:∀ r:σ → R,eval r F=0) (hnR:n ≤ #R):
   F=0:=by
 contrapose! h
 obtain ⟨k,f,hf,F,rfl⟩:=exists_fin_rename F
 have hF₀:F≠0:=by rintro rfl;simp at h
 have hF:F.IsHomogeneous n:=by rwa [rename_isHomogeneous_iff hf] at hF
 obtain ⟨r,hr⟩:=exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
 obtain ⟨r,rfl⟩:=(Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
 use r
 rwa [eval_rename]
lemma funext_of_le_card (hF:F.IsHomogeneous n) (hG:G.IsHomogeneous n)
   (h:∀ r:σ → R,eval r F=eval r G) (hnR:n ≤ #R):
   F=G:=by
 rw [←sub_eq_zero]
 apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
 simpa [sub_eq_zero] using h
lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F:MvPolynomial σ R} {n:ℕ}
   (hF:F.IsHomogeneous n) (h:∀ r:σ → R,eval r F=0):F=0:=by
 apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
 exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›
lemma funext [Infinite R] {F G:MvPolynomial σ R} {n:ℕ}
   (hF:F.IsHomogeneous n) (hG:G.IsHomogeneous n)
   (h:∀ r:σ → R,eval r F=eval r G):F=G:=by
 apply funext_of_le_card hF hG h
 exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›
end IsDomain
instance HomogeneousSubmodule.gcommSemiring:SetLike.GradedMonoid (homogeneousSubmodule σ R) where
 one_mem:=isHomogeneous_one σ R
 mul_mem _ _ _ _:=IsHomogeneous.mul
end IsHomogeneous
noncomputable section
open Finset
def homogeneousComponent (n:ℕ):MvPolynomial σ R →ₗ[R] MvPolynomial σ R:=
 weightedHomogeneousComponent 1 n
section HomogeneousComponent
open Finset Finsupp
variable (n:ℕ) (φ ψ:MvPolynomial σ R)
theorem homogeneousComponent_mem:
   homogeneousComponent n φ∈homogeneousSubmodule σ R n:=
 weightedHomogeneousComponent_mem _ φ n
theorem coeff_homogeneousComponent (d:σ →₀ ℕ):
   coeff d (homogeneousComponent n φ)=if d.degree=n then coeff d φ else 0:=by
 rw [degree_eq_weight_one]
 convert! coeff_weightedHomogeneousComponent n φ d
theorem homogeneousComponent_apply:
   homogeneousComponent n φ=∑ d∈φ.support with d.degree=n,monomial d (coeff d φ):=by
 simp_rw [degree_eq_weight_one]
 convert! weightedHomogeneousComponent_apply n φ
theorem homogeneousComponent_isHomogeneous:(homogeneousComponent n φ).IsHomogeneous n:=
 weightedHomogeneousComponent_isWeightedHomogeneous n φ
@[simp]
theorem homogeneousComponent_zero:homogeneousComponent 0 φ=C (coeff 0 φ):=
 weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)
@[simp]
theorem homogeneousComponent_C_mul (n:ℕ) (r:R):
   homogeneousComponent n (C r*φ)=C r*homogeneousComponent n φ:=
 weightedHomogeneousComponent_C_mul φ n r
theorem homogeneousComponent_eq_zero'
   (h:∀ d:σ →₀ ℕ,d∈φ.support → d.degree≠n):
   homogeneousComponent n φ=0:=by
 simp_rw [degree_eq_weight_one] at h
 exact weightedHomogeneousComponent_eq_zero' n φ h
theorem homogeneousComponent_eq_zero (h:φ.totalDegree < n):homogeneousComponent n φ=0:=by
 apply homogeneousComponent_eq_zero'
 rw [totalDegree,Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
 intro d hd;exact ne_of_lt (h d hd)
theorem sum_homogeneousComponent:
   (∑ i∈range (φ.totalDegree+1),homogeneousComponent i φ)=φ:=by
 ext1 d
 suffices φ.totalDegree < d.support.sum d → 0=coeff d φ by
   simpa [coeff_sum,coeff_homogeneousComponent]
 exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm
theorem homogeneousComponent_of_mem {m n:ℕ} {p:MvPolynomial σ R}
   (h:p∈homogeneousSubmodule σ R n):
   homogeneousComponent m p=if m=n then p else 0:=
 weightedHomogeneousComponent_of_mem h
lemma homogeneousComponent_eq_self {n:ℕ} {p:MvPolynomial σ R}
   (hp:p.IsHomogeneous n):homogeneousComponent n p=p:=by
 simp [homogeneousComponent_of_mem hp]
lemma support_homogeneousComponent (n:ℕ) (p:MvPolynomial σ R):
   (homogeneousComponent n p).support={c∈p.support | c.degree=n}:=by
 rw [degree_eq_weight_one]
 exact support_weightedHomogeneousComponent n p
lemma rename_homogeneousComponent {τ:Type*} {φ:σ → τ} (n:ℕ) (p:MvPolynomial σ R):
   rename φ (homogeneousComponent n p)=homogeneousComponent n (rename φ p):=by
 induction p using MvPolynomial.induction_on' with
 | monomial d c =>
   rw [rename_monomial,
     homogeneousComponent_of_mem (isHomogeneous_monomial c rfl),
     homogeneousComponent_of_mem (isHomogeneous_monomial c (Finsupp.degree_mapDomain φ d))]
   split_ifs <;> simp [rename_monomial]
 | add p q hp hq => simp [map_add,hp,hq]
end HomogeneousComponent
end
noncomputable section GradedAlgebra
lemma HomogeneousSubmodule.gradedMonoid:
   SetLike.GradedMonoid (homogeneousSubmodule σ R):=
 WeightedHomogeneousSubmodule.gradedMonoid
abbrev decomposition:
   DirectSum.Decomposition (homogeneousSubmodule σ R):=
 fast_instance% weightedDecomposition R (1:σ → ℕ)
abbrev gradedAlgebra:GradedAlgebra (homogeneousSubmodule σ R):=
 fast_instance% weightedGradedAlgebra R (1:σ → ℕ)
theorem decomposition.decompose'_apply (φ:MvPolynomial σ R) (i:ℕ):
   (decomposition.decompose' φ i:MvPolynomial σ R)=homogeneousComponent i φ:=
 weightedDecomposition.decompose'_apply R _ φ i
theorem decomposition.decompose'_eq:
   decomposition.decompose'=fun φ:MvPolynomial σ R =>
     DirectSum.mk (fun i:ℕ => ↥(homogeneousSubmodule σ R i)) (φ.support.image Finsupp.degree)
       fun m => ⟨homogeneousComponent m φ,homogeneousComponent_mem m φ⟩:=by
 rw [degree_eq_weight_one]
 rfl
attribute [local instance] MvPolynomial.gradedAlgebra
lemma mem_iff_homogeneousComponent_mem {I:Ideal (MvPolynomial σ R)}
   (h:I.IsHomogeneous (homogeneousSubmodule σ R)) (p:MvPolynomial σ R):
   p∈I ↔ ∀ n,(homogeneousComponent n p)∈I:=
 mem_iff_weightedHomogeneousComponent_mem R (1:σ → ℕ) h p
lemma homogeneousComponent_mem_of_mem {I:Ideal (MvPolynomial σ R)}
   (h:I.IsHomogeneous (homogeneousSubmodule σ R)) {p:MvPolynomial σ R} (hp:p∈I) (n:ℕ):
   (homogeneousComponent n p)∈I:=
 weightedHomogeneousComponent_mem_of_mem R (1:σ → ℕ) h hp n
end GradedAlgebra
end MvPolynomial
lemma Ideal.span_eq_map_homogeneousSubmodule {ι R:Type*} [CommSemiring R]
   (x:ι → R):
   Ideal.span (Set.range x)=
     Submodule.map (MvPolynomial.aeval x).toLinearMap
       (MvPolynomial.homogeneousSubmodule ι R 1):=by
 simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X,Submodule.map_span, ←Set.range_comp,
   Function.comp_def]
lemma Ideal.span_pow_eq_map_homogeneousSubmodule {ι R:Type*} [CommSemiring R]
   (x:ι → R) (n:ℕ):
   Ideal.span (Set.range x)^n=
     Submodule.map (MvPolynomial.aeval x).toLinearMap
       (MvPolynomial.homogeneousSubmodule ι R n):=by
 rw [←MvPolynomial.homogeneousSubmodule_one_pow,Submodule.map_pow,
   Ideal.span_eq_map_homogeneousSubmodule]
lemma Ideal.mem_span_pow_iff_exists_isHomogeneous {ι R:Type*} [CommSemiring R] {n:ℕ} (x:ι → R)
   (y:R):
   y∈(Ideal.span <| Set.range x)^n ↔
     ∃ (p:MvPolynomial ι R),p.IsHomogeneous n∧p.eval x=y:=by
 simp [Ideal.span_pow_eq_map_homogeneousSubmodule]
lemma Ideal.mem_span_iff_exists_isHomogeneous {ι R:Type*} [CommSemiring R] (x:ι → R) (y:R):
   y∈Ideal.span (.range x) ↔
     ∃ (p:MvPolynomial ι R),p.IsHomogeneous 1∧p.eval x=y:=by
 simp [Ideal.span_eq_map_homogeneousSubmodule]
end ProximityFlatProofPort
end PackedLegacy_F3

/-! Packed from ProximityPrize.SubmissionLower.IO. -/
section PackedLegacy_IO
section ProximityFlatProofPort
namespace MonomialOrder
open MvPolynomial
open scoped MonomialOrder
variable {sigma:Type*} {m:MonomialOrder sigma}
 {R:Type*} [CommSemiring R]
variable (m) in
noncomputable def degree (f:MvPolynomial sigma R):sigma →₀ ℕ:=
 m.toSyn.symm (f.support.sup m.toSyn)
variable (m) in
noncomputable def leadingCoeff (f:MvPolynomial sigma R):R:=
 f.coeff (m.degree f)
@[simp]
theorem degree_zero:m.degree (0:MvPolynomial sigma R)=0:=by
 simp [degree]
theorem degree_le_iff {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}:
   m.degree f ≼[m] d ↔ ∀ c∈f.support,c ≼[m] d:=by
 unfold degree
 simp only [AddEquiv.apply_symm_apply,Finset.sup_le_iff,
   MvPolynomial.mem_support_iff,ne_eq]
theorem le_degree {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}
   (hd:d∈f.support):d ≼[m] m.degree f:=by
 unfold degree
 simp only [AddEquiv.apply_symm_apply,Finset.le_sup hd]
theorem coeff_eq_zero_of_lt {f:MvPolynomial sigma R} {d:sigma →₀ ℕ}
   (hd:m.degree f ≺[m] d):f.coeff d=0:=by
 rw [←not_le] at hd
 by_contra hf
 apply hd (m.le_degree (MvPolynomial.mem_support_iff.mpr hf))
@[simp]
theorem leadingCoeff_zero:m.leadingCoeff (0:MvPolynomial sigma R)=0:=by
 simp [degree,leadingCoeff]
theorem leadingCoeff_ne_zero_iff {f:MvPolynomial sigma R}:
   m.leadingCoeff f≠0 ↔ f≠0:=by
 constructor
 · rw [not_imp_not]
   intro hf
   rw [hf,leadingCoeff_zero]
 · intro hf
   rw [←support_nonempty] at hf
   rw [leadingCoeff, ←MvPolynomial.mem_support_iff,degree]
   suffices f.support.sup m.toSyn∈m.toSyn '' f.support by
     obtain ⟨d,hd,hd'⟩:=this
     rw [←hd',AddEquiv.symm_apply_apply]
     exact hd
   exact Finset.sup_mem_of_nonempty hf
@[simp]
theorem leadingCoeff_eq_zero_iff {f:MvPolynomial sigma R}:
   leadingCoeff m f=0 ↔ f=0:=by
 simp only [←not_iff_not,leadingCoeff_ne_zero_iff]
lemma degree_mem_support {p:MvPolynomial sigma R} (hp:p≠0):
   m.degree p∈p.support:=by
 unfold degree
 suffices p.support.sup m.toSyn∈m.toSyn '' p.support by
   obtain ⟨d,hd,hd'⟩:=this
   rw [←hd',AddEquiv.symm_apply_apply]
   exact hd
 exact Finset.sup_mem_of_nonempty (support_nonempty.mpr hp)
theorem degree_mul_le {f g:MvPolynomial sigma R}:
   m.degree (f*g) ≼[m] m.degree f+m.degree g:=by
 classical
 letI:DecidableEq sigma:=Classical.decEq sigma
 rw [degree_le_iff]
 intro c
 rw [←not_lt,MvPolynomial.mem_support_iff,not_imp_not]
 intro hc
 rw [coeff_mul]
 apply Finset.sum_eq_zero
 rintro ⟨d,e⟩ hde
 simp only [Finset.mem_antidiagonal] at hde
 dsimp only
 by_cases hd:m.degree f ≺[m] d
 · rw [m.coeff_eq_zero_of_lt hd,zero_mul]
 · suffices m.degree g ≺[m] e by
     rw [m.coeff_eq_zero_of_lt this,mul_zero]
   simp only [not_lt] at hd
   apply lt_of_add_lt_add_left (a:=m.toSyn d)
   grw [←map_add _ _ e,hd, ←map_add,hde]
   exact hc
theorem coeff_mul_of_add_of_degree_le {f g:MvPolynomial sigma R}
   {a b:sigma →₀ ℕ} (ha:m.degree f ≼[m] a) (hb:m.degree g ≼[m] b):
   (f*g).coeff (a+b)=f.coeff a*g.coeff b:=by
 classical
 letI:DecidableEq sigma:=Classical.decEq sigma
 rw [coeff_mul,Finset.sum_eq_single (a,b)]
 · rintro ⟨c,d⟩ hcd h
   simp only [Finset.mem_antidiagonal] at hcd
   by_cases hf:m.degree f ≺[m] c
   · rw [m.coeff_eq_zero_of_lt hf,zero_mul]
   · suffices m.degree g ≺[m] d by
       rw [coeff_eq_zero_of_lt this,mul_zero]
     rw [not_lt] at hf
     rw [←not_le]
     intro hf'
     apply h
     suffices c=a by
       simpa [Prod.mk.injEq,this] using hcd
     apply m.toSyn.injective
     apply le_antisymm (le_trans hf ha)
     apply le_of_add_le_add_right (a:=m.toSyn b)
     rw [←map_add, ←hcd,map_add]
     simp only [add_le_add_iff_left]
     exact le_trans hf' hb
 · simp
theorem coeff_mul_of_degree_add {f g:MvPolynomial sigma R}:
   (f*g).coeff (m.degree f+m.degree g)=
     m.leadingCoeff f*m.leadingCoeff g:=
 coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)
theorem degree_mul_of_mul_leadingCoeff_ne_zero {f g:MvPolynomial sigma R}
   (hfg:m.leadingCoeff f*m.leadingCoeff g≠0):
   m.degree (f*g)=m.degree f+m.degree g:=by
 apply m.toSyn.injective
 apply le_antisymm degree_mul_le
 apply le_degree
 rw [MvPolynomial.mem_support_iff,coeff_mul_of_degree_add]
 exact hfg
theorem degree_mul [NoZeroDivisors R] {f g:MvPolynomial sigma R}
   (hf:f≠0) (hg:g≠0):
   m.degree (f*g)=m.degree f+m.degree g:=by
 apply degree_mul_of_mul_leadingCoeff_ne_zero
 simp only [ne_eq,mul_eq_zero,leadingCoeff_eq_zero_iff,not_or]
 tauto
end MonomialOrder
end ProximityFlatProofPort
end PackedLegacy_IO

/-! Packed from ProximityPrize.SubmissionLower.HL. -/
section PackedLegacy_HL
section ProximityFlatProofPort
def DegLex (α:Type*):=α
variable {α:Type*}
@[match_pattern] def toDegLex:α ≃ DegLex α:=Equiv.refl _
theorem toDegLex_injective:Function.Injective (toDegLex (α:=α)):=fun _ _↦_root_.id
theorem toDegLex_inj {a b:α}:toDegLex a=toDegLex b ↔ a=b:=Iff.rfl
@[match_pattern] def ofDegLex:DegLex α ≃ α:=Equiv.refl _
theorem ofDegLex_injective:Function.Injective (ofDegLex (α:=α)):=fun _ _↦_root_.id
theorem ofDegLex_inj {a b:DegLex α}:ofDegLex a=ofDegLex b ↔ a=b:=Iff.rfl
@[simp] theorem ofDegLex_symm_eq:(@ofDegLex α).symm=toDegLex:=rfl
@[simp] theorem toDegLex_symm_eq:(@toDegLex α).symm=ofDegLex:=rfl
@[simp] theorem ofDegLex_toDegLex (a:α):ofDegLex (toDegLex a)=a:=rfl
@[simp] theorem toDegLex_ofDegLex (a:DegLex α):toDegLex (ofDegLex a)=a:=rfl
@[elab_as_elim,induction_eliminator,cases_eliminator]
protected def DegLex.rec {β:DegLex α → Sort*} (h:∀ a,β (toDegLex a)):
   ∀ a,β a:=fun a => h (ofDegLex a)
@[simp] lemma DegLex.forall_iff {p:DegLex α → Prop}:(∀ a,p a) ↔ ∀ a,p (toDegLex a):=Iff.rfl
@[simp] lemma DegLex.exists_iff {p:DegLex α → Prop}:(∃ a,p a) ↔ ∃ a,p (toDegLex a):=Iff.rfl
noncomputable instance [AddCommMonoid α]:
   AddCommMonoid (DegLex α):=ofDegLex.addCommMonoid
theorem toDegLex_add [AddCommMonoid α] (a b:α):
   toDegLex (a+b)=toDegLex a+toDegLex b:=rfl
theorem ofDegLex_add [AddCommMonoid α] (a b:DegLex α):
   ofDegLex (a+b)=ofDegLex a+ofDegLex b:=rfl
namespace Finsupp
open scoped Function in
protected def DegLex (r:α → α → Prop) (s:ℕ → ℕ → Prop):
   (α →₀ ℕ) → (α →₀ ℕ) → Prop:=
 (Prod.Lex s (Finsupp.Lex r s)) on (fun x↦(x.degree,x))
theorem degLex_def {r:α → α → Prop} {s:ℕ → ℕ → Prop} {a b:α →₀ ℕ}:
   Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree,a) (b.degree,b):=
 Iff.rfl
namespace DegLex
theorem wellFounded
   {r:α → α → Prop} [Std.Trichotomous r] (hr:WellFounded (Function.swap r))
   {s:ℕ → ℕ → Prop} (hs:WellFounded s) (hs0:∀ ⦃n⦄,¬ s n 0):
   WellFounded (Finsupp.DegLex r s):=by
 have wft:=WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
 rw [←Set.wellFoundedOn_univ] at wft
 unfold Finsupp.DegLex
 rw [←Set.wellFoundedOn_range]
 exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _↦trivial)
instance [LT α]:LT (DegLex (α →₀ ℕ)):=
 ⟨fun f g↦Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩
theorem lt_def [LT α] {a b:DegLex (α →₀ ℕ)}:
   a < b ↔ (toLex ((ofDegLex a).degree,toLex (ofDegLex a))) <
       (toLex ((ofDegLex b).degree,toLex (ofDegLex b))):=
 Iff.rfl
theorem lt_iff [LT α] {a b:DegLex (α →₀ ℕ)}:
   a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree∨
   (((ofDegLex a).degree=(ofDegLex b).degree)∧toLex (ofDegLex a) < toLex (ofDegLex b)):=by
 simp [lt_def,Prod.Lex.toLex_lt_toLex]
variable [LinearOrder α]
instance isStrictOrder:IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) where
 irrefl:=fun a↦by simp [lt_def]
 «trans»:=by
   intro a b c hab hbc
   simp only [lt_iff] at hab hbc ⊢
   rcases hab with (hab | hab)
   · rcases hbc with (hbc | hbc)
     · left;exact lt_trans hab hbc
     · left;exact lt_of_lt_of_eq hab hbc.1
   · rcases hbc with (hbc | hbc)
     · left;exact lt_of_eq_of_lt hab.1 hbc
     · right;exact ⟨Eq.trans hab.1 hbc.1,lt_trans hab.2 hbc.2⟩
noncomputable instance:LinearOrder (DegLex (α →₀ ℕ)):=
 fast_instance% LinearOrder.lift'
   (fun (f:DegLex (α →₀ ℕ))↦toLex ((ofDegLex f).degree,toLex (ofDegLex f)))
   (fun f g↦by simp)
theorem le_iff {x y:DegLex (α →₀ ℕ)}:
   x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree∨
     (ofDegLex x).degree=(ofDegLex y).degree∧toLex (ofDegLex x) ≤ toLex (ofDegLex y):=by
 simp only [le_iff_eq_or_lt,lt_iff,EmbeddingLike.apply_eq_iff_eq]
 by_cases h:x=y
 · simp [h]
 · by_cases k:(ofDegLex x).degree < (ofDegLex y).degree
   · simp [k]
   · simp only [h,k,false_or]
instance:IsOrderedCancelAddMonoid (DegLex (α →₀ ℕ)) where
 le_of_add_le_add_left a b c h:=by
   rw [le_iff] at h ⊢
   simpa only [ofDegLex_add,map_add,add_lt_add_iff_left,add_right_inj,toLex_add,
     add_le_add_iff_left] using h
 add_le_add_left a b h c:=by
   rw [le_iff] at h ⊢
   simpa [ofDegLex_add,map_add] using h
theorem single_strictAnti:StrictAnti (fun (a:α)↦toDegLex (single a 1)):=by
 intro _ _ h
 simp only [lt_iff,ofDegLex_toDegLex,degree_single,lt_self_iff_false,Lex.single_lt_iff,h,
   and_self,or_true]
theorem single_antitone:Antitone (fun (a:α)↦toDegLex (single a 1)):=
 single_strictAnti.antitone
theorem single_lt_iff {a b:α}:
   toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b:=
 single_strictAnti.lt_iff_gt
theorem single_le_iff {a b:α}:
   toDegLex (Finsupp.single b 1) ≤ toDegLex (Finsupp.single a 1) ↔ a ≤ b:=
 single_strictAnti.le_iff_ge
theorem monotone_degree:
   Monotone (fun (x:DegLex (α →₀ ℕ))↦(ofDegLex x).degree):=by
 intro x y
 rw [le_iff]
 rintro (h | h)
 · apply le_of_lt h
 · apply le_of_eq h.1
noncomputable instance orderBot:OrderBot (DegLex (α →₀ ℕ)) where
 bot:=toDegLex (0:α →₀ ℕ)
 bot_le x:=by
   simp only [le_iff,ofDegLex_toDegLex,toLex_zero,map_zero]
   rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
   · simp only [h,lt_self_iff_false,true_and,false_or]
     exact bot_le
   · simp [h]
instance wellFoundedLT [WellFoundedGT α]:WellFoundedLT (DegLex (α →₀ ℕ)):=
 ⟨wellFounded wellFounded_gt wellFounded_lt fun _↦not_lt_zero⟩
end DegLex
end Finsupp
namespace MonomialOrder
open Finsupp
variable {σ:Type*} [LinearOrder σ] [WellFoundedGT σ]
noncomputable def degLex:
   MonomialOrder σ where
 syn:=DegLex (σ →₀ ℕ)
 toSyn:={ toEquiv:=toDegLex,map_add':=toDegLex_add}
 toSyn_monotone a b h:=by
   simp only [AddEquiv.coe_mk,DegLex.le_iff,ofDegLex_toDegLex]
   by_cases! ha:a.degree < b.degree
   · exact Or.inl ha
   · refine Or.inr ⟨le_antisymm ?_ ha,toLex_monotone h⟩
     rw [←add_tsub_cancel_of_le h,map_add]
     exact Nat.le_add_right a.degree (b-a).degree
theorem degLex_le_iff {a b:σ →₀ ℕ}:
   a ≼[degLex] b ↔ toDegLex a ≤ toDegLex b:=
 Iff.rfl
theorem degLex_lt_iff {a b:σ →₀ ℕ}:
   a ≺[degLex] b ↔ toDegLex a < toDegLex b:=
 Iff.rfl
theorem degLex_single_le_iff {a b:σ}:
   single a 1 ≼[degLex] single b 1 ↔ b ≤ a:=by
 rw [MonomialOrder.degLex_le_iff,DegLex.single_le_iff]
theorem degLex_single_lt_iff {a b:σ}:
   single a 1 ≺[degLex] single b 1 ↔ b < a:=by
 rw [MonomialOrder.degLex_lt_iff,DegLex.single_lt_iff]
end MonomialOrder
section Examples
open Finsupp MonomialOrder DegLex
example:single (1:Fin 2) 1 ≺[degLex] single 0 1:=by
 rw [degLex_lt_iff,single_lt_iff]
 exact Nat.one_pos
example:(single 0 1+single 1 1) ≺[degLex] single (0:Fin 2) 2:=by
 rw [degLex_lt_iff,lt_iff,ofDegLex_toDegLex]
 simp only [Fin.isValue,map_add,degree_single,Nat.reduceAdd,ofDegLex_toDegLex,
   lt_self_iff_false,toLex_add,true_and,false_or]
 use 0
 simp
example:single (0:Fin 2) 1 ≺[degLex] single 1 2:=by
 simp [degLex_lt_iff,lt_iff]
end Examples
end ProximityFlatProofPort
end PackedLegacy_HL

/-! Packed from ProximityPrize.SubmissionLower.IN. -/
section PackedLegacy_IN
section ProximityFlatProofPort
namespace MvPolynomial
open MonomialOrder Finsupp
open scoped MonomialOrder
variable {σ:Type*} {R:Type*}
section CommSemiring
variable [CommSemiring R] {f g:MvPolynomial σ R}
section LinearOrder
variable [LinearOrder σ] [WellFoundedGT σ]
theorem degree_degLexDegree:(degLex.degree f).degree=f.totalDegree:=by
 by_cases hf:f=0
 · simp [hf]
 apply le_antisymm
 · exact le_totalDegree (degLex.degree_mem_support hf)
 · unfold MvPolynomial.totalDegree
   apply Finset.sup_le
   intro b hb
   exact DegLex.monotone_degree (degLex.le_degree hb)
theorem degLex_totalDegree_monotone (h:degLex.degree f ≼[degLex] degLex.degree g):
   f.totalDegree ≤ g.totalDegree:=by
 simp only [←MvPolynomial.degree_degLexDegree]
 exact DegLex.monotone_degree h
end LinearOrder
end CommSemiring
end MvPolynomial
end ProximityFlatProofPort
end PackedLegacy_IN

/-! Packed from ProximityPrize.SubmissionLower.HH. -/
section PackedLegacy_HH
section ProximityFlatProofPort
variable {σ R:Type*} [CommSemiring R]
namespace MvPolynomial
section CopiedDeclarations
noncomputable def divMonomial (p:MvPolynomial σ R) (s:σ →₀ ℕ):MvPolynomial σ R:=
 AddMonoidAlgebra.divOf p s
local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial
@[simp]
theorem coeff_divMonomial (s:σ →₀ ℕ) (x:MvPolynomial σ R) (s':σ →₀ ℕ):
   coeff s' (x/ᵐᵒⁿᵒᵐⁱᵃˡ s)=coeff (s+s') x:=
 rfl
@[simp]
theorem support_divMonomial (s:σ →₀ ℕ) (x:MvPolynomial σ R):
   (x/ᵐᵒⁿᵒᵐⁱᵃˡ s).support=x.support.preimage _ (add_right_injective s).injOn:=
 rfl
@[simp]
theorem zero_divMonomial (s:σ →₀ ℕ):(0:MvPolynomial σ R)/ᵐᵒⁿᵒᵐⁱᵃˡ s=0:=
 AddMonoidAlgebra.zero_divOf _
theorem divMonomial_zero (x:MvPolynomial σ R):x/ᵐᵒⁿᵒᵐⁱᵃˡ 0=x:=
 x.divOf_zero
set_option backward.isDefEq.respectTransparency false in
theorem add_divMonomial (x y:MvPolynomial σ R) (s:σ →₀ ℕ):
   (x+y)/ᵐᵒⁿᵒᵐⁱᵃˡ s=x/ᵐᵒⁿᵒᵐⁱᵃˡ s+y/ᵐᵒⁿᵒᵐⁱᵃˡ s:=by
 simp [divMonomial,MvPolynomial,AddMonoidAlgebra.add_divOf]
theorem divMonomial_add (a b:σ →₀ ℕ) (x:MvPolynomial σ R):
   x/ᵐᵒⁿᵒᵐⁱᵃˡ (a+b)=x/ᵐᵒⁿᵒᵐⁱᵃˡ a/ᵐᵒⁿᵒᵐⁱᵃˡ b:=
 x.divOf_add _ _
@[simp]
theorem divMonomial_monomial_mul (a:σ →₀ ℕ) (x:MvPolynomial σ R):
   monomial a 1*x/ᵐᵒⁿᵒᵐⁱᵃˡ a=x:=
 x.of'_mul_divOf _
@[simp]
theorem divMonomial_mul_monomial (a:σ →₀ ℕ) (x:MvPolynomial σ R):
   x*monomial a 1/ᵐᵒⁿᵒᵐⁱᵃˡ a=x:=
 x.mul_of'_divOf _
@[simp]
theorem divMonomial_monomial (a:σ →₀ ℕ):monomial a 1/ᵐᵒⁿᵒᵐⁱᵃˡ a=(1:MvPolynomial σ R):=
 AddMonoidAlgebra.of'_divOf _
noncomputable def modMonomial (x:MvPolynomial σ R) (s:σ →₀ ℕ):MvPolynomial σ R:=
 x.modOf s
local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial
@[simp]
theorem coeff_modMonomial_of_not_le {s' s:σ →₀ ℕ} (x:MvPolynomial σ R) (h:¬s ≤ s'):
   coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s)=coeff s' x:=
 x.coeff_modOf_of_not_exists_add s s' <| by rintro ⟨d,rfl⟩;exact h le_self_add
@[simp]
theorem coeff_modMonomial_of_le {s' s:σ →₀ ℕ} (x:MvPolynomial σ R) (h:s ≤ s'):
   coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s)=0:=
 x.coeff_modOf_of_exists_add _ _ <| exists_add_of_le h
@[simp]
theorem monomial_mul_modMonomial (s:σ →₀ ℕ) (x:MvPolynomial σ R):
   monomial s 1*x %ᵐᵒⁿᵒᵐⁱᵃˡ s=0:=
 x.of'_mul_modOf _
@[simp]
theorem mul_monomial_modMonomial (s:σ →₀ ℕ) (x:MvPolynomial σ R):
   x*monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s=0:=
 x.mul_of'_modOf _
@[simp]
theorem monomial_modMonomial (s:σ →₀ ℕ):monomial s (1:R) %ᵐᵒⁿᵒᵐⁱᵃˡ s=0:=
 AddMonoidAlgebra.of'_modOf _
theorem divMonomial_add_modMonomial (x:MvPolynomial σ R) (s:σ →₀ ℕ):
   monomial s 1*(x/ᵐᵒⁿᵒᵐⁱᵃˡ s)+x %ᵐᵒⁿᵒᵐⁱᵃˡ s=x:=
 AddMonoidAlgebra.divOf_add_modOf x s
theorem modMonomial_add_divMonomial (x:MvPolynomial σ R) (s:σ →₀ ℕ):
   x %ᵐᵒⁿᵒᵐⁱᵃˡ s+monomial s 1*(x/ᵐᵒⁿᵒᵐⁱᵃˡ s)=x:=
 AddMonoidAlgebra.modOf_add_divOf x s
theorem monomial_one_dvd_iff_modMonomial_eq_zero {i:σ →₀ ℕ} {x:MvPolynomial σ R}:
   monomial i (1:R)∣x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i=0:=
 AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero
end CopiedDeclarations
section XLemmas
local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial
local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial
@[simp]
theorem X_mul_divMonomial (i:σ) (x:MvPolynomial σ R):
   MvPolynomial.X i*x/ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=x:=
 divMonomial_monomial_mul _ _
@[simp]
theorem X_divMonomial (i:σ):(MvPolynomial.X i:MvPolynomial σ R)/ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=1:=
 divMonomial_monomial (Finsupp.single i 1)
@[simp]
theorem mul_X_divMonomial (x:MvPolynomial σ R) (i:σ):
   x*MvPolynomial.X i/ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=x:=
 divMonomial_mul_monomial _ _
@[simp]
theorem X_mul_modMonomial (i:σ) (x:MvPolynomial σ R):
   MvPolynomial.X i*x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=0:=
 monomial_mul_modMonomial _ _
@[simp]
theorem mul_X_modMonomial (x:MvPolynomial σ R) (i:σ):
   x*MvPolynomial.X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=0:=
 mul_monomial_modMonomial _ _
@[simp]
theorem modMonomial_X (i:σ):(MvPolynomial.X i:MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=0:=
 monomial_modMonomial _
theorem divMonomial_add_modMonomial_single (x:MvPolynomial σ R) (i:σ):
   MvPolynomial.X i*(x/ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1)+x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=x:=
 divMonomial_add_modMonomial _ _
theorem modMonomial_add_divMonomial_single (x:MvPolynomial σ R) (i:σ):
   x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1+MvPolynomial.X i*(x/ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1)=x:=
 modMonomial_add_divMonomial _ _
theorem X_dvd_iff_modMonomial_eq_zero {i:σ} {x:MvPolynomial σ R}:
   MvPolynomial.X i∣x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1=0:=
 monomial_one_dvd_iff_modMonomial_eq_zero
end XLemmas
theorem monomial_dvd_monomial {r s:R} {i j:σ →₀ ℕ}:
   monomial i r∣monomial j s ↔ (s=0∨i ≤ j)∧r∣s:=by
 constructor
 · rintro ⟨x,hx⟩
   rw [MvPolynomial.ext_iff] at hx
   have hj:=hx j
   have hi:=hx i
   classical
   letI:DecidableEq σ:=Classical.decEq σ
   simp_rw [coeff_monomial,if_pos] at hj hi
   simp_rw [coeff_monomial_mul'] at hi hj
   split_ifs at hj with hi
   · exact ⟨Or.inr hi,_,hj⟩
   · exact ⟨Or.inl hj,hj.symm ▸ dvd_zero _⟩
 · rintro ⟨h | hij,d,rfl⟩
   · simp_rw [h,monomial_zero,dvd_zero]
   · refine ⟨monomial (j-i) d,?_⟩
     rw [monomial_mul,add_tsub_cancel_of_le hij]
@[simp]
theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j:σ →₀ ℕ}:
   monomial i (1:R)∣monomial j 1 ↔ i ≤ j:=by
 rw [monomial_dvd_monomial]
 simp_rw [one_ne_zero,false_or,dvd_rfl,and_true]
@[simp]
theorem X_dvd_X [Nontrivial R] {i j:σ}:
   (MvPolynomial.X i:MvPolynomial σ R)∣(MvPolynomial.X j:MvPolynomial σ R) ↔ i=j:=by
 refine monomial_one_dvd_monomial_one.trans ?_
 simp_rw [Finsupp.single_le_iff,Nat.one_le_iff_ne_zero,Finsupp.single_apply_ne_zero,
   ne_eq,reduceCtorEq,not_false_eq_true,and_true]
@[simp]
theorem X_dvd_monomial {i:σ} {j:σ →₀ ℕ} {r:R}:
   (MvPolynomial.X i:MvPolynomial σ R)∣monomial j r ↔ r=0∨j i≠0:=by
 refine monomial_dvd_monomial.trans ?_
 simp_rw [one_dvd,and_true,Finsupp.single_le_iff,Nat.one_le_iff_ne_zero]
theorem eq_divMonomial_single [IsLeftCancelAdd R]
   {i:σ} {p q r:MvPolynomial σ R} (h:p=MvPolynomial.X i*q+r)
   (hr:∀ n∈r.support,n i=0):
   q=p.divMonomial (Finsupp.single i 1):=by
 ext n
 rw [coeff_divMonomial,h,coeff_add,coeff_X_mul,left_eq_add, ←notMem_support_iff]
 intro hn
 simpa using hr _ hn
instance [IsLeftCancelAdd R]:
   IsCancelAdd (MvPolynomial σ R):=by
 suffices IsLeftCancelAdd (MvPolynomial σ R) from
   AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
 refine { add_left_cancel:=fun f g h H↦?_}
 ext d
 simpa using congr_arg (coeff d) H
theorem eq_modMonomial_single [IsLeftCancelAdd R]
   {σ:Type*} {i:σ} {p q r:MvPolynomial σ R}
   (h:p=MvPolynomial.X i*q+r) (hr:∀ n∈r.support,n i=0):
   r=p.modMonomial (Finsupp.single i 1):=by
 have h':=id h
 rwa [←p.divMonomial_add_modMonomial_single i,
   eq_divMonomial_single h hr,add_right_inj,eq_comm] at h'
section CommRing
variable {R:Type*} [CommRing R] {i:σ} {p q r:MvPolynomial σ R}
theorem eq_modMonomial_single_iff (h:MvPolynomial.X i∣p-r):
   r=p.modMonomial (Finsupp.single i 1) ↔
     ∀ n∈r.support,n i=0:=by
 refine ⟨fun h n↦?_,fun hr↦?_⟩
 · contrapose!
   intro hn
   rw [h,notMem_support_iff]
   apply coeff_modMonomial_of_le
   simpa [Nat.one_le_iff_ne_zero]
 · obtain ⟨q,hq⟩:=h
   apply eq_modMonomial_single (q:=q) _ hr
   rwa [←sub_eq_iff_eq_add]
theorem X_dvd_mul_iff [IsCancelMulZero R]:
   MvPolynomial.X i∣p*q ↔ MvPolynomial.X i∣p∨MvPolynomial.X i∣q:=by
 nontriviality R
 have _:NoZeroDivisors (MvPolynomial σ R):=
   IsLeftCancelMulZero.to_noZeroDivisors (MvPolynomial σ R)
 constructor
 · intro h
   suffices (p.modMonomial (Finsupp.single i 1))*(q.modMonomial (Finsupp.single i 1))=
         (p*q).modMonomial (Finsupp.single i 1) by
     simp only [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at h ⊢
     rwa [h,mul_eq_zero] at this
   have hp:=p.modMonomial_add_divMonomial_single i
   have hq:=q.modMonomial_add_divMonomial_single i
   rw [eq_modMonomial_single_iff]
   · intro n
     contrapose
     intro hn
     classical
     letI:DecidableEq σ:=Classical.decEq σ
     rw [notMem_support_iff,coeff_mul]
     apply Finset.sum_eq_zero
     intro x hx
     simp only [Finset.mem_antidiagonal] at hx
     simp only [←hx,Finsupp.coe_add,Pi.add_apply,Nat.add_eq_zero_iff,not_and_or] at hn
     rcases hn with hn | hn
     · rw [coeff_modMonomial_of_le,zero_mul]
       simpa [←Nat.one_le_iff_ne_zero] using hn
     · rw [mul_comm,coeff_modMonomial_of_le,zero_mul]
       simpa [←Nat.one_le_iff_ne_zero] using hn
   · nth_rewrite 1 [←hp]
     nth_rewrite 1 [←hq]
     simp only [add_mul,mul_add,add_assoc,add_sub_cancel_left]
     simp only [←mul_assoc,mul_comm _ (MvPolynomial.X i)]
     simp only [mul_assoc, ←mul_add (MvPolynomial.X i)]
     apply dvd_mul_right
 · rintro (h | h)
   · exact dvd_mul_of_dvd_left h q
   · exact dvd_mul_of_dvd_right h p
theorem X_prime [IsCancelMulZero R] [Nontrivial R]:Prime (MvPolynomial.X i:MvPolynomial σ R):=by
 refine ⟨X_ne_zero i,?_,fun p q↦X_dvd_mul_iff.mp⟩
 intro h
 rw [isUnit_iff_exists] at h
 rcases h with ⟨u,hu, -⟩
 apply_fun constantCoeff at hu
 simp at hu
theorem dvd_X_mul_iff [IsCancelMulZero R]:
   p∣MvPolynomial.X i*q ↔ p∣q∨(MvPolynomial.X i∣p∧p.divMonomial (Finsupp.single i 1)∣q):=by
 constructor
 · rintro ⟨r,hp⟩
   have:MvPolynomial.X i∣p∨MvPolynomial.X i∣r:=by simp [←X_dvd_mul_iff, ←hp]
   apply this.symm.imp
   · rintro ⟨r,rfl⟩
     obtain rfl:q=p*r:=by rw [←X_mul_cancel_left_iff (i:=i),hp,mul_left_comm]
     exact dvd_mul_right p r
   · intro hip
     refine ⟨hip,?_⟩
     rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at hip
     rw [←p.modMonomial_add_divMonomial_single i,hip,
       zero_add,mul_assoc,X_mul_cancel_left_iff] at hp
     use r
 · rintro (hp | ⟨hi,hq⟩)
   · exact dvd_mul_of_dvd_right hp (MvPolynomial.X i)
   · suffices p=MvPolynomial.X i*p.divMonomial (Finsupp.single i 1) by
       rw [this]
       exact mul_dvd_mul_left (MvPolynomial.X i) hq
     conv_lhs => rw [←p.modMonomial_add_divMonomial (Finsupp.single i 1)]
     simpa only [←C_mul_X_eq_monomial,C_1,one_mul,add_eq_right,
       ←X_dvd_iff_modMonomial_eq_zero]
theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n:σ →₀ ℕ}:
   p∣monomial n 1*q ↔ ∃ m r,m ≤ n∧r∣q∧p=monomial m 1*r:=by
 rcases subsingleton_or_nontrivial R with hR | hR
 · simp only [Subsingleton.elim _ p,dvd_refl,and_self,and_true,exists_const,true_iff]
   refine ⟨n,le_refl n⟩
 suffices ∀ (d) (n:σ →₀ ℕ) (hd:n.degree=d) (p q:MvPolynomial σ R),
   p∣monomial n 1*q ↔ ∃ m r,m ≤ n∧r∣q∧p=monomial m 1*r from this n.degree n rfl p q
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 intro d
 induction d with
 | zero =>
   intro n hn p
   rw [Finsupp.degree_eq_zero_iff] at hn
   simp only [hn,monomial_zero',C_1,one_mul,nonpos_iff_eq_zero,exists_and_left,
     exists_eq_left,exists_eq_right',implies_true]
 | succ d hd =>
   intro n hn p q
   refine ⟨fun hp↦?_,fun ⟨m,r,hmn,hrq,hp⟩↦?_⟩
   · obtain ⟨i,hi⟩:n.support.Nonempty:=by
       rw [Finsupp.support_nonempty_iff]
       intro hn'
       simp [hn'] at hn
     let n':=n-Finsupp.single i 1
     have hn':n'+Finsupp.single i 1=n:=by
       apply Finsupp.sub_add_single_one_cancel
       rwa [←Finsupp.mem_support_iff]
     have hnn':n' ≤ n:=by simp [←hn']
     have hd':n'.degree=d:=by
       rw [←add_left_inj, ←hn, ←hn']
       simp
     rw [←hn',monomial_add_single,pow_one,mul_comm _ (MvPolynomial.X i),mul_assoc,dvd_X_mul_iff] at hp
     rcases hp with hp | hp
     · obtain ⟨m,r,hm,hr,hp⟩:=(hd n' hd' p q).mp hp
       exact ⟨m,r,le_trans hm hnn',hr,hp⟩
     · obtain ⟨p',rfl⟩:=hp.1
       obtain ⟨m,r,hm,hr,hp⟩:=(hd n' hd' _ _).mp hp.2
       use m+Finsupp.single i 1,r,?_,hr
       · simp [monomial_add_single,pow_one,mul_comm _ (MvPolynomial.X i),mul_assoc, ←hp]
       · simpa [←hn'] using hm
   · rw [hp, ←add_tsub_cancel_of_le hmn, ←mul_one 1, ←monomial_mul,mul_one,mul_assoc]
     apply mul_dvd_mul dvd_rfl
     apply dvd_mul_of_dvd_right hrq
end CommRing
end MvPolynomial
end ProximityFlatProofPort
end PackedLegacy_HH

/-! Packed from ProximityPrize.SubmissionLower.AO. -/
section PackedLegacy_AO
section ProximityFlatProofPort
open Finset Equiv
variable {R:Type*}
namespace MvPolynomial
variable {σ:Type*} {a a' a₁ a₂:R} {e:ℕ} {n m:σ} {s:σ →₀ ℕ}
section CommSemiring
variable [CommSemiring R]
 {p q:MvPolynomial σ R}
section NoZeroDivisors
variable [NoZeroDivisors R]
section DegreeOf
lemma degreeOf_mul_eq (hp:p≠0) (hq:q≠0):
   degreeOf n (p*q)=degreeOf n p+degreeOf n q:=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 simp_rw [degreeOf_eq_natDegree,map_mul, ←renameEquiv_apply]
 rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply,EmbeddingLike.map_eq_zero_iff]
lemma degreeOf_prod_eq {ι:Type*} (s:Finset ι) (f:ι → MvPolynomial σ R)
   (h:∀ i∈s,f i≠0):
   degreeOf n (∏ i∈s,f i)=∑ i∈s,degreeOf n (f i):=by
 rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
 · simp [Subsingleton.eq_zero]
 · classical
   letI:DecidableEq ι:=Classical.decEq ι
   induction s using Finset.induction_on with
   | empty => simp
   | insert a s a_not_mem ih =>
     simp only [mem_insert,ne_eq,forall_eq_or_imp] at h
     obtain ⟨ha,hs⟩:=h
     simp [a_not_mem,not_false_eq_true,prod_insert,sum_insert,degreeOf_mul_eq ha
       (by rw [prod_ne_zero_iff];exact hs),ih hs]
theorem degreeOf_pow_eq (i:σ) (p:MvPolynomial σ R) (n:ℕ) (hp:p≠0):
   degreeOf i (p^n)=n*degreeOf i p:=by
 rw [pow_eq_prod_const,degreeOf_prod_eq (range n) (fun _↦p) (fun _ _↦hp)]
 simp
end DegreeOf
section Degrees
lemma degrees_mul_eq (hp:p≠0) (hq:q≠0):
   degrees (p*q)=degrees p+degrees q:=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 ext s
 simp_rw [Multiset.count_add, ←degreeOf_def,degreeOf_mul_eq hp hq]
end Degrees
theorem totalDegree_mul_of_isDomain {f g:MvPolynomial σ R}
   (hf:f≠0) (hg:g≠0):
   totalDegree (f*g)=totalDegree f+totalDegree g:=by
 cases exists_wellFoundedGT σ
 simp [←degree_degLexDegree,MonomialOrder.degree_mul hf hg]
theorem totalDegree_le_of_dvd_of_isDomain {f g:MvPolynomial σ R}
   (h:f∣g) (hg:g≠0):
   f.totalDegree ≤ g.totalDegree:=by
 obtain ⟨r,rfl⟩:=h
 rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
 lia
theorem dvd_C_iff_exists {f:MvPolynomial σ R} {a:R} (ha:a≠0):
   f∣C a ↔ ∃ b,b∣a∧f=C b:=by
 constructor
 · intro hf
   use coeff 0 f
   suffices f.totalDegree=0 by
     rw [totalDegree_eq_zero_iff_eq_C] at this
     refine ⟨?_,this⟩
     rw [this,C_dvd_iff_dvd_coeff] at hf
     simpa using hf 0
   apply Nat.eq_zero_of_le_zero
   simpa using totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
 · rintro ⟨b,hab,rfl⟩
   exact map_dvd C hab
end NoZeroDivisors
section nonZeroDivisors
open nonZeroDivisors
theorem degreeOf_C_mul (j:σ) (c:R) (hc:c∈R⁰):degreeOf j (C c*p)=degreeOf j p:=by
 by_cases hp:p=0
 · simp [hp]
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 simp_rw [degreeOf_eq_natDegree,map_mul, ←renameEquiv_apply]
 rw [Polynomial.natDegree_mul']
 · simp
 · have hp':(optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff≠0:=by
     intro h
     exact hp (rename_injective _ (Equiv.injective _) (by simpa using h))
   simp_rw [ne_eq,renameEquiv_apply,algHom_C,algebraMap_eq,optionEquivLeft_C,
     Polynomial.leadingCoeff_C]
   contrapose hp'
   ext m
   apply hc.1
   simpa using congr_arg (coeff m) hp'
end nonZeroDivisors
end CommSemiring
section CommRing
variable [CommRing R] [NoZeroDivisors R] {p q r:MvPolynomial σ R}
theorem dvd_monomial_iff_exists {n:σ →₀ ℕ} {a:R} (ha:a≠0):
   p∣monomial n a ↔ ∃ m b,m ≤ n∧b∣a∧p=monomial m b:=by
 rw [show monomial n a=monomial n 1*C a by rw [mul_comm,C_mul_monomial,mul_one],
   dvd_monomial_mul_iff_exists]
 apply exists_congr
 intro m
 constructor
 · rintro ⟨r,hmn,hr,h⟩
   rw [dvd_C_iff_exists ha] at hr
   obtain ⟨b,hb,hr⟩:=hr
   use b,hmn,hb
   rw [h,mul_comm,hr,C_mul_monomial,mul_one]
 · rintro ⟨b,hmn,hb,h⟩
   use C b,hmn,map_dvd C hb
   rwa [mul_comm,C_mul_monomial,mul_one]
theorem dvd_monomial_one_iff_exists {n:σ →₀ ℕ}:
   p∣monomial n 1 ↔ ∃ m u,m ≤ n∧IsUnit u∧p=monomial m u:=by
 rcases subsingleton_or_nontrivial R with hR | hR
 · suffices ∃ m,m ≤ n by simpa [Subsingleton.elim _ p]
   use n
 rw [dvd_monomial_iff_exists (one_ne_zero' R)]
 apply exists_congr
 intro m
 simp_rw [isUnit_iff_dvd_one]
theorem dvd_smul_X_iff_exists {i:σ} {r:R} (hr:r≠0):
   p∣r • MvPolynomial.X i ↔ ∃ s,s∣r∧(p=C s∨p=s • MvPolynomial.X i):=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 rw [MvPolynomial.X,smul_monomial,smul_eq_mul,mul_one,dvd_monomial_iff_exists hr,exists_comm]
 apply exists_congr
 intro b
 constructor
 · rintro ⟨m,hmn,hb,rfl⟩
   simp only [hb,true_and]
   suffices m=0∨m=Finsupp.single i 1 by
     apply this.imp <;> simp+contextual [smul_monomial,smul_eq_mul,mul_one]
   by_cases hm:m i=0
   · left
     ext j
     simp only [Finsupp.coe_zero,Pi.zero_apply, ←Nat.le_zero]
     by_cases hj:j=i
     · rw [←hm,hj]
     · exact (hmn j).trans (Finsupp.single_eq_of_ne hj).le
   · right
     ext j
     apply le_antisymm (hmn j)
     by_cases hj:j=i
     · simpa [hj,Nat.one_le_iff_ne_zero]
     · simp [Finsupp.single_eq_of_ne hj]
 · rintro ⟨hb,hp | hp⟩
   · use 0;simp [hb,hp]
   · use Finsupp.single i 1,le_rfl,hb
     simp [hp,smul_monomial]
theorem dvd_X_iff_exists {i:σ}:
   p∣MvPolynomial.X i ↔ ∃ r,IsUnit r∧(p=C r∨p=r • MvPolynomial.X i):=by
 classical
 letI:DecidableEq σ:=Classical.decEq σ
 nontriviality R
 rw [←one_smul R (MvPolynomial.X i),dvd_smul_X_iff_exists (one_ne_zero' R)]
 apply exists_congr
 intro r
 rw [isUnit_iff_dvd_one,one_smul]
end CommRing
end MvPolynomial
end ProximityFlatProofPort
end PackedLegacy_AO

/-! Packed from ProximityPrize.SubmissionLower.FI. -/
section PackedLegacy_FI
namespace ProximityPrize.SubmissionLower.RCN224
open RCN002
noncomputable section
variable (K:Type) [Field K]
def graphEquation (a b:K):MvPolynomial (Fin 3) K:=
 MvPolynomial.X 0-(MvPolynomial.C a+MvPolynomial.X 2*MvPolynomial.C b)
theorem graphEquation_ne_zero (a b:K):graphEquation K a b≠0:=by
 intro h
 have hd:=congrArg (MvPolynomial.pderiv (0:Fin 3)) h
 simp [graphEquation] at hd
theorem graphEquation_r_degree (a b:K):
   (graphEquation K a b).degreeOf (1:Fin 3)=0:=by
 have hm:(MvPolynomial.X 2*MvPolynomial.C b:MvPolynomial (Fin 3) K).degreeOf 1 ≤ 0:=by
   simpa [MvPolynomial.degreeOf_X] using MvPolynomial.degreeOf_mul_le (1:Fin 3)
     (MvPolynomial.X 2:MvPolynomial (Fin 3) K) (MvPolynomial.C b)
 have ha:(MvPolynomial.C a+MvPolynomial.X 2*MvPolynomial.C b:
     MvPolynomial (Fin 3) K).degreeOf 1 ≤ 0:=
   (MvPolynomial.degreeOf_add_le 1 _ _).trans (max_le (by simp) hm)
 apply Nat.eq_zero_of_le_zero
 exact (MvPolynomial.degreeOf_sub_le 1 _ _).trans
   (max_le (by simp [MvPolynomial.degreeOf_X]) ha)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem graphEquation_mem_of_affine_coordinate (a b:K)
   (hy:coordinate K P 0=algebraMap K (CoordinateField K P) a+
     coordinate K P 2*algebraMap K (CoordinateField K P) b):
   graphEquation K a b∈P:=by
 rw [←coordinateEvaluation_ker K P]
 change coordinateEvaluation K P (graphEquation K a b)=0
 simp only [graphEquation,map_sub,map_add,map_mul]
 change coordinate K P 0-(algebraMap K (CoordinateField K P) a+
   coordinate K P 2*algebraMap K (CoordinateField K P) b)=0
 exact sub_eq_zero.mpr hy
theorem not_y_affine_of_r_dependent_principal
   (g:MvPolynomial (Fin 3) K) (hP:P=Ideal.span {g})
   (hr:0 < g.degreeOf (1:Fin 3)) (a b:K):
   coordinate K P 0≠algebraMap K (CoordinateField K P) a+
     coordinate K P 2*algebraMap K (CoordinateField K P) b:=by
 intro hy
 have hmem:=graphEquation_mem_of_affine_coordinate K P a b hy
 rw [hP,Ideal.mem_span_singleton] at hmem
 obtain ⟨q,hq⟩:=hmem
 have hprod:g*q≠0:=by
   rw [←hq]
   exact graphEquation_ne_zero K a b
 obtain ⟨hg0,hq0⟩:=mul_ne_zero_iff.mp hprod
 have hle:g.degreeOf 1 ≤ (graphEquation K a b).degreeOf 1:=by
   rw [hq,MvPolynomial.degreeOf_mul_eq hg0 hq0]
   exact Nat.le_add_right _ _
 rw [graphEquation_r_degree] at hle
 omega
theorem coordinate_algebraic_of_scalar (i:Fin 3) (c:K)
   (hc:coordinate K P i=algebraMap K (CoordinateField K P) c):
   IsAlgebraic K (coordinate K P i):=by
 refine ⟨Polynomial.X-Polynomial.C c,Polynomial.X_sub_C_ne_zero c,?_⟩
 simp [hc]
theorem seed_transcendental_of_affine_coordinates [IsAlgClosed K]
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (a b c d:K)
   (hy:coordinate K P 0=algebraMap K (CoordinateField K P) a+
     coordinate K P 2*algebraMap K (CoordinateField K P) b)
   (hr:coordinate K P 1=algebraMap K (CoordinateField K P) c+
     coordinate K P 2*algebraMap K (CoordinateField K P) d):
   Transcendental K (coordinate K P 2):=by
 intro hz
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic K P 2 hz
 have hy':coordinate K P 0=algebraMap K (CoordinateField K P) (a+z*b):=by
   simpa only [map_add,map_mul,hz] using hy
 have hr':coordinate K P 1=algebraMap K (CoordinateField K P) (c+z*d):=by
   simpa only [map_add,map_mul,hz] using hr
 have hall:∀ i:Fin 3,IsAlgebraic K (coordinate K P i):=by
   intro i
   fin_cases i
   · exact coordinate_algebraic_of_scalar K P 0 _ hy'
   · exact coordinate_algebraic_of_scalar K P 1 _ hr'
   · exact coordinate_algebraic_of_scalar K P 2 _ hz.symm
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic K P hall
 exact hnonpoint v hv
theorem affine_coordinates_of_polynomial_pencil
   (ξ:K) (Q:Polynomial (CoordinateField K P)) (Q₀ Q₁:Polynomial K)
   (hQ:Q=Q₀.map (algebraMap K (CoordinateField K P))+
     Polynomial.C (coordinate K P 2)*Q₁.map (algebraMap K (CoordinateField K P)))
   (hy:Q.eval (algebraMap K (CoordinateField K P) ξ)=coordinate K P 0)
   (hr:Q.derivative.eval (algebraMap K (CoordinateField K P) ξ)=coordinate K P 1):
   coordinate K P 0=algebraMap K (CoordinateField K P) (Q₀.eval ξ)+
       coordinate K P 2*algebraMap K (CoordinateField K P) (Q₁.eval ξ)∧
     coordinate K P 1=algebraMap K (CoordinateField K P) (Q₀.derivative.eval ξ)+
       coordinate K P 2*algebraMap K (CoordinateField K P) (Q₁.derivative.eval ξ):=by
 constructor
 · rw [←hy,hQ]
   simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_map_apply]
 · rw [←hr,hQ,Polynomial.derivative_add,Polynomial.derivative_C_mul]
   simp only [Polynomial.derivative_map,Polynomial.eval_add,Polynomial.eval_mul,
     Polynomial.eval_C,Polynomial.eval_map_apply]
end
end ProximityPrize.SubmissionLower.RCN224
end PackedLegacy_FI

/-! Packed from ProximityPrize.SubmissionLower.BM. -/
section PackedLegacy_BM
namespace ProximityPrize.SubmissionLower.RCN147
noncomputable section
variable {K L:Type*} [Field K] [Field L]
theorem degree_lt_card_of_natDegree_le {ι:Type*}
   (I:Finset ι) (w:ℕ) (hw:w < I.card) (P:Polynomial L)
   (hP:P.natDegree ≤ w):P.degree < (I.card:WithBot ℕ):=
 lt_of_le_of_lt Polynomial.degree_le_natDegree
   (WithBot.coe_lt_coe.mpr (hP.trans_lt hw))
theorem mapped_affine_pencil_natDegree_le
   (coefficients:K →+*L) (P₀ P₁:Polynomial K) (w:ℕ)
   (h₀:P₀.natDegree ≤ w) (h₁:P₁.natDegree ≤ w) (γ:L):
   (P₀.map coefficients+Polynomial.C γ*P₁.map coefficients).natDegree ≤ w:=by
 apply (Polynomial.natDegree_add_le _ _).trans
 exact max_le (Polynomial.natDegree_map_le.trans h₀)
   ((Polynomial.natDegree_C_mul_le γ _).trans (Polynomial.natDegree_map_le.trans h₁))
theorem exists_basefield_affine_pencil_of_identity_nodes {ι τ:Type*}
   (coefficients:K →+*L) (I:Finset ι) (x u₀ u₁:ι → K)
   (w:ℕ) (hw:w < I.card) (hinj:Set.InjOn x I)
   (γ:τ → L) (P:τ → Polynomial L)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I →
     (P t).eval (coefficients (x i))=coefficients (u₀ i)+γ t*coefficients (u₁ i)):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀.map coefficients+Polynomial.C (γ t)*P₁.map coefficients:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 obtain ⟨S,hSI,hcard⟩:=Finset.exists_subset_card_eq (show w+1 ≤ I.card by omega)
 have hxS:Set.InjOn x S:=by
   intro i hi j hj hij
   exact hinj (hSI hi) (hSI hj) hij
 let P₀:Polynomial K:=Lagrange.interpolate S x u₀
 let P₁:Polynomial K:=Lagrange.interpolate S x u₁
 have h₀:P₀.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₀ hxS
 have h₁:P₁.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₁ hxS
 have heval₀:∀ i∈S,P₀.eval (x i)=u₀ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₀ hxS hi
 have heval₁:∀ i∈S,P₁.eval (x i)=u₁ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₁ hxS hi
 have hnodes:Set.InjOn (fun i => coefficients (x i)) S:=by
   intro i hi j hj hij
   exact hxS hi hj (coefficients.injective hij)
 have hws:w < S.card:=by omega
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hnodes
   (degree_lt_card_of_natDegree_le S w hws (P t) (hdegree t))
   (degree_lt_card_of_natDegree_le S w hws _
     (mapped_affine_pencil_natDegree_le coefficients P₀ P₁ w h₀ h₁ (γ t)))
 intro i hi
 simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply,heval₀ i hi,heval₁ i hi] using hvalues t i (hSI hi)
theorem exists_affine_pencil_of_identity_nodes {ι τ:Type*}
   (I:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:w < I.card)
   (hinj:Set.InjOn x I) (γ:τ → K) (P:τ → Polynomial K)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I → (P t).eval (x i)=u₀ i+γ t*u₁ i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀+Polynomial.C (γ t)*P₁:=by
 obtain ⟨P₀,P₁,h₀,h₁,hfamily⟩:=
   exists_basefield_affine_pencil_of_identity_nodes (RingHom.id K) I x u₀ u₁
     w hw hinj γ P hdegree hvalues
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 simpa only [Polynomial.map_id] using hfamily t
end
end ProximityPrize.SubmissionLower.RCN147
end PackedLegacy_BM

/-! Packed from ProximityPrize.SubmissionLower.E. -/
section PackedLegacy_E
namespace ProximityPrize.SubmissionLower.RCN136
noncomputable section
variable {K L:Type*} [Field K] [Field L]
def collectX (K:Type*) [Field K]:
   MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 3) (Polynomial K):=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 3)).trans
   (MvPolynomial.optionEquivRight K (Fin 3))
@[simp] theorem collectX_C (a:K):
   collectX K (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_zero:
   collectX K (MvPolynomial.X (0:Fin 4))=MvPolynomial.C Polynomial.X:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_succ (i:Fin 3):
   collectX K (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
def surfaceMap (φ:Polynomial K →+*L):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map φ).comp (collectX K).toRingHom
@[simp] theorem surfaceMap_C (φ:Polynomial K →+*L) (a:K):
   surfaceMap φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_zero (φ:Polynomial K →+*L):
   surfaceMap φ (MvPolynomial.X (0:Fin 4))=MvPolynomial.C (φ Polynomial.X):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_succ (φ:Polynomial K →+*L) (i:Fin 3):
   surfaceMap φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [surfaceMap]
theorem surfaceMap_injective (φ:Polynomial K →+*L) (hφ:Function.Injective φ):
   Function.Injective (surfaceMap φ):=
 (MvPolynomial.map_injective φ hφ).comp (collectX K).injective
theorem surfaceMap_ne_zero (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):surfaceMap φ Q≠0:=by
 intro h
 apply hQ
 apply surfaceMap_injective φ hφ
 simpa only [map_zero] using h
theorem surfaceMap_eq_eval₂Hom (φ:Polynomial K →+*L):
   surfaceMap φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem eval_surfaceMap (φ:Polynomial K →+*L)
   (v:Fin 3 → L) (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v) Q:=by
 have hhom:(MvPolynomial.eval v).comp (surfaceMap φ)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i <;> simp
 exact RingHom.congr_fun hhom Q
theorem surfaceMap_monomial (φ:Polynomial K →+*L)
   (d:Fin 4 →₀ ℕ) (a:K):
   surfaceMap φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [surfaceMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,
   map_mul,map_pow]
 ring
theorem support_surfaceMap_subset (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K):
   (surfaceMap φ Q).support ⊆ Q.support.image Finsupp.tail:=by
 classical
 have hsum:surfaceMap φ Q=
     ∑ d∈Q.support,surfaceMap φ (MvPolynomial.monomial d (MvPolynomial.coeff d Q)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [surfaceMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem surfaceMap_degreeOf_le (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (i:Fin 3):
   (surfaceMap φ Q).degreeOf i ≤ Q.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
theorem surfaceMap_separated_caps (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
   (hy:Q.degreeOf 1 ≤ ell) (hr:Q.degreeOf 2 ≤ s) (hz:Q.degreeOf 3 ≤ zcap):
   (surfaceMap φ Q).degreeOf 0 ≤ ell∧
     (surfaceMap φ Q).degreeOf 1 ≤ s∧
     (surfaceMap φ Q).degreeOf 2 ≤ zcap:=
 ⟨(surfaceMap_degreeOf_le φ Q 0).trans hy,
   (surfaceMap_degreeOf_le φ Q 1).trans hr,
   (surfaceMap_degreeOf_le φ Q 2).trans hz⟩
theorem surfaceMap_joint_seed_cap (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (cap:ℕ)
   (hcap:∀ d∈Q.support,d 1+d 3 ≤ cap):
   ∀ e∈(surfaceMap φ Q).support,e 0+e 2 ≤ cap:=by
 classical
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 exact hcap d hd
end
end ProximityPrize.SubmissionLower.RCN136
end PackedLegacy_E

/-! Packed from ProximityPrize.SubmissionLower.HF. -/
section PackedLegacy_HF
section ProximityFlatProofPort
universe u v w
variable (R:Type u) (L:Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
def CommutatorRing (L:Type v):Type v:=L
instance:NonUnitalNonAssocRing (CommutatorRing L):=
 have:=LieRing.toNonUnitalNonAssocRing L
 inferInstanceAs <| NonUnitalNonAssocRing L
namespace LieAlgebra
instance (L:Type v) [Nonempty L]:Nonempty (CommutatorRing L):=‹Nonempty L›
instance (L:Type v) [Inhabited L]:Inhabited (CommutatorRing L):=‹Inhabited L›
instance:LieRing (CommutatorRing L):=inferInstanceAs <| LieRing L
instance:LieAlgebra R (CommutatorRing L):=inferInstanceAs <| LieAlgebra R L
instance isScalarTower:IsScalarTower R (CommutatorRing L) (CommutatorRing L):=
 ⟨smul_lie (L:=L) (M:=L)⟩
instance smulCommClass:SMulCommClass R (CommutatorRing L) (CommutatorRing L):=
 ⟨fun t x y => (lie_smul t x y).symm⟩
end LieAlgebra
namespace LieHom
variable {R L}
 {L₂:Type w} [LieRing L₂] [LieAlgebra R L₂]
@[simps toFun]
def toNonUnitalAlgHom (f:L →ₗ⁅R⁆ L₂):CommutatorRing L →ₙₐ[R] CommutatorRing L₂:=
 { f with
   toFun:=f
   map_zero':=f.toLinearMap.map_zero
   map_mul':=f.map_lie}
theorem toNonUnitalAlgHom_injective:
   Function.Injective (toNonUnitalAlgHom:_ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂):=
 fun _ _ h => ext <| NonUnitalAlgHom.congr_fun h
end LieHom
end ProximityFlatProofPort
end PackedLegacy_HF

/-! Packed from ProximityPrize.SubmissionLower.IQ. -/
section PackedLegacy_IQ
section ProximityFlatProofPort
namespace IsNilpotent
variable {A:Type*} [Ring A] [Module ℚ A]
open Finset
open scoped Nat
noncomputable def exp (a:A):A:=
 ∑ i∈range (nilpotencyClass a),(i.factorial:ℚ)⁻¹ • (a^i)
theorem exp_eq_sum {a:A} {k:ℕ} (h:a^k=0):
   exp a=∑ i∈range k,(i.factorial:ℚ)⁻¹ • (a^i):=by
 have h₁:∑ i∈range k,(i.factorial:ℚ)⁻¹ • (a^i)=
     ∑ i∈range (nilpotencyClass a),(i.factorial:ℚ)⁻¹ • (a^i)+
       ∑ i∈Ico (nilpotencyClass a) k,(i.factorial:ℚ)⁻¹ • (a^i):=
   (sum_range_add_sum_Ico _ (csInf_le' h)).symm
 suffices ∑ i∈Ico (nilpotencyClass a) k,(i.factorial:ℚ)⁻¹ • (a^i)=0 by
   dsimp [exp]
   rw [h₁,this,add_zero]
 exact sum_eq_zero fun _ h₂ => by
   rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k,h⟩),smul_zero]
theorem exp_smul_eq_sum {M:Type*} [AddCommGroup M] [Module A M] [Module ℚ M] {a:A} {m:M}
   {k:ℕ} (h:(a^k) • m=0) (hn:IsNilpotent a):
   exp a • m=∑ i∈range k,(i.factorial:ℚ)⁻¹ • (a^i) • m:=by
 rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
 · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)),sum_smul,smul_assoc]
 rw [exp,sum_smul, ←sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
 suffices ∑ i∈Ico k (nilpotencyClass a),((i.factorial:ℚ)⁻¹ • (a^i)) • m=0 by
   simp_rw [this,add_zero,smul_assoc]
 refine sum_eq_zero fun r h₂↦?_
 rw [smul_assoc, ←pow_sub_mul_pow a (mem_Ico.1 h₂).1,mul_smul,h,smul_zero,smul_zero]
theorem exp_add_of_commute {a b:A} (h₁:Commute a b) (h₂:IsNilpotent a) (h₃:IsNilpotent b):
   exp (a+b)=exp a*exp b:=by
 obtain ⟨n₁,hn₁⟩:=h₂
 obtain ⟨n₂,hn₂⟩:=h₃
 let N:=n₁ ⊔ n₂
 have h₄:a^(N+1)=0:=pow_eq_zero_of_le (by omega) hn₁
 have h₅:b^(N+1)=0:=pow_eq_zero_of_le (by omega) hn₂
 rw [exp_eq_sum (k:=2*N+1)
   (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ (by lia)),
   exp_eq_sum h₄,exp_eq_sum h₅]
 set R2N:=range (2*N+1) with hR2N
 set RN:=range (N+1) with hRN
 have s₁:=by
   calc ∑ i∈R2N,(i !:ℚ)⁻¹ • (a+b)^i
       =∑ i∈R2N,(i !:ℚ)⁻¹ • ∑ j∈range (i+1),a^j*b^(i-j)*i.choose j:=?_
     _=∑ i∈R2N,(∑ j∈range (i+1),
           ((j !:ℚ)⁻¹*((i-j) !:ℚ)⁻¹) • (a^j*b^(i-j))):=?_
     _=∑ ij∈R2N ×ˢ R2N with ij.1+ij.2 ≤ 2*N,
           ((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2):=?_
   · refine sum_congr rfl fun i _↦?_
     rw [Commute.add_pow h₁ i]
   · simp_rw [smul_sum]
     refine sum_congr rfl fun i hi↦sum_congr rfl fun j hj↦?_
     simp only [mem_range] at hi hj
     replace hj:=Nat.le_of_lt_succ hj
     suffices (i !:ℚ)⁻¹*(i.choose j)=((j !:ℚ)⁻¹*((i-j)!:ℚ)⁻¹) by
       rw [←Nat.cast_commute (i.choose j), ←this, ←mul_smul_comm, ←nsmul_eq_mul,
         mul_smul, ←smul_assoc,smul_comm,smul_assoc]
       norm_cast
     rw [Nat.choose_eq_factorial_div_factorial hj,
       Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hj) (by positivity)]
     simp [field]
   · rw [hR2N,sum_sigma']
     apply sum_bij (fun ⟨i,j⟩ _↦(j,i-j))
     · simp only [mem_sigma,mem_range,mem_filter,mem_product,and_imp]
       lia
     · simp only [mem_sigma,mem_range,Prod.mk.injEq,and_imp]
       rintro ⟨x₁,y₁⟩-h₁ ⟨x₂,y₂⟩-h₂ h₃ h₄
       simp_all
       lia
     · simp only [mem_filter,mem_product,mem_range,mem_sigma,exists_prop,Sigma.exists,
         and_imp,Prod.forall,Prod.mk.injEq]
       exact fun x y _ _ _↦⟨x+y,x,by lia⟩
     · simp only [mem_sigma,mem_range,implies_true]
 have z₁:∑ ij∈R2N ×ˢ R2N with ¬ ij.1+ij.2 ≤ 2*N,
     ((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2)=0:=
   sum_eq_zero fun i hi↦by
     rw [mem_filter] at hi
     cases le_or_gt (N+1) i.1 with
       | inl h => rw [pow_eq_zero_of_le h h₄,zero_mul,smul_zero]
       | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅,mul_zero,smul_zero]
 have split₁:=sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
   (fun ij↦ij.1+ij.2 ≤ 2*N)
   (fun ij↦((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2))
 rw [z₁,add_zero] at split₁
 rw [split₁] at s₁
 have z₂:∑ ij∈R2N ×ˢ R2N with ¬ (ij.1 ≤ N∧ij.2 ≤ N),
     ((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2)=0:=
   sum_eq_zero fun i hi↦by
   simp only [not_and,not_le,mem_filter] at hi
   cases le_or_gt (N+1) i.1 with
     | inl h => rw [pow_eq_zero_of_le h h₄,zero_mul,smul_zero]
     | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅,mul_zero,smul_zero]
 have split₂:=sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
   (fun ij↦ij.1 ≤ N∧ij.2 ≤ N)
   (fun ij↦((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2))
 rw [z₂,add_zero] at split₂
 rw [←split₂] at s₁
 have restrict:∑ ij∈R2N ×ˢ R2N with ij.1 ≤ N∧ij.2 ≤ N,
     ((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2)=
       ∑ ij∈RN ×ˢ RN,((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2):=by
   apply sum_congr
   · ext x
     simp only [mem_filter,mem_product,mem_range,hR2N,hRN]
     lia
   · tauto
 rw [restrict] at s₁
 have s₂:=by
   calc (∑ i∈RN,(i !:ℚ)⁻¹ • a^i)*∑ i∈RN,(i !:ℚ)⁻¹ • b^i
       =∑ i∈RN,∑ j∈RN,((i !:ℚ)⁻¹*(j !:ℚ)⁻¹) • (a^i*b^j):=?_
     _=∑ ij∈RN ×ˢ RN,((ij.1 !:ℚ)⁻¹*(ij.2 !:ℚ)⁻¹) • (a^ij.1*b^ij.2):=?_
   · rw [sum_mul_sum]
     refine sum_congr rfl fun _ _↦sum_congr rfl fun _ _↦?_
     rw [smul_mul_assoc,mul_smul_comm,smul_smul]
   · rw [sum_sigma']
     apply sum_bijective (fun ⟨i,j⟩↦(i,j))
     · exact ⟨fun ⟨i,j⟩ ⟨i',j'⟩ h↦by cases h;rfl,fun ⟨i,j⟩↦⟨⟨i,j⟩,rfl⟩⟩
     · simp only [mem_sigma,mem_product,implies_true]
     · simp only [implies_true]
 rwa [s₂.symm] at s₁
@[simp]
theorem exp_zero:
   exp (0:A)=1:=by
 simp [exp_eq_sum (pow_one 0)]
theorem exp_mul_exp_neg_self {a:A} (h:IsNilpotent a):
   exp a*exp (-a)=1:=by
 simp [←exp_add_of_commute (Commute.neg_right rfl) h h.neg]
theorem exp_neg_mul_exp_self {a:A} (h:IsNilpotent a):
   exp (-a)*exp a=1:=by
 simp [←exp_add_of_commute (Commute.neg_left rfl) h.neg h]
theorem isUnit_exp {a:A} (h:IsNilpotent a):IsUnit (exp a):=by
 apply isUnit_iff_exists.2
 use exp (-a)
 exact ⟨exp_mul_exp_neg_self h,exp_neg_mul_exp_self h⟩
theorem map_exp {B F:Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module ℚ B]
   {a:A} (ha:IsNilpotent a) (f:F):
   f (exp a)=exp (f a):=by
 obtain ⟨k,hk⟩:=ha
 have hk':(f a)^k=0:=by simp [←map_pow,hk]
 simp [exp_eq_sum hk,exp_eq_sum hk',map_rat_smul]
theorem exp_smul {G:Type*} [Monoid G] [MulSemiringAction G A]
   (g:G) {a:A} (ha:IsNilpotent a):
   exp (g • a)=g • exp a:=
 (map_exp ha (MulSemiringAction.toRingHom G A g)).symm
set_option linter.flexible false in
theorem isNilpotent_exp_sub_one {a:A} (ha:IsNilpotent a):IsNilpotent (exp a-1):=by
 nontriviality A
 rw [exp, ←Nat.sub_add_cancel (pos_nilpotencyClass_iff.2 ha),Finset.sum_range_succ']
 simp
 apply Commute.isNilpotent_sum fun _ _↦smul (pow_of_pos ha <| by positivity) _
 simp [Nat.factorial_ne_zero]
end IsNilpotent
namespace Module.End
variable {R M N:Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
 [Module ℚ M] [Module ℚ N]
open _root_.IsNilpotent TensorProduct
theorem commute_exp_left_of_commute
   {fM:Module.End R M} {fN:Module.End R N} {g:M →ₗ[R] N}
   (hfM:IsNilpotent fM)
   (hfN:IsNilpotent fN)
   (h:fN ∘ₗ g=g ∘ₗ fM):
   _root_.IsNilpotent.exp fN ∘ₗ g=g ∘ₗ _root_.IsNilpotent.exp fM:=by
 ext m
 obtain ⟨k,hfM⟩:=hfM
 obtain ⟨l,hfN⟩:=hfN
 let kl:=max k l
 replace hfM:fM^kl=0:=pow_eq_zero_of_le (by omega) hfM
 replace hfN:fN^kl=0:=pow_eq_zero_of_le (by omega) hfN
 have (i:ℕ):(fN^i) (g m)=g ((fM^i) m):=by
   simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) m
 simp [_root_.IsNilpotent.exp_eq_sum hfM,_root_.IsNilpotent.exp_eq_sum hfN,
   this,map_rat_smul]
theorem exp_mul_of_derivation (R B:Type*) [CommRing R] [NonUnitalNonAssocRing B]
   [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [Module ℚ B]
   (D:B →ₗ[R] B) (h_der:∀ x y,D (x*y)=x*D y+(D x)*y)
   (h_nil:IsNilpotent D) (x y:B):
   _root_.IsNilpotent.exp D (x*y)=
     (_root_.IsNilpotent.exp D x)*(_root_.IsNilpotent.exp D y):=by
 let DL:Module.End R (B ⊗[R] B):=D.lTensor B
 let DR:Module.End R (B ⊗[R] B):=D.rTensor B
 have h_nilL:IsNilpotent DL:=h_nil.map <| lTensorAlgHom R B B
 have h_nilR:IsNilpotent DR:=h_nil.map <| rTensorAlgHom R B B
 have h_comm:Commute DL DR:=by ext;simp [DL,DR]
 set m:B ⊗[R] B →ₗ[R] B:=LinearMap.mul' R B with hm
 have h₁:_root_.IsNilpotent.exp D (x*y)=
     m (_root_.IsNilpotent.exp (DL+DR) (x ⊗ₜ[R] y)):=by
   suffices _root_.IsNilpotent.exp D ∘ₗ m=m ∘ₗ _root_.IsNilpotent.exp (DL+DR) by
     simpa using! LinearMap.congr_fun this (x ⊗ₜ[R] y)
   apply commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h_nil
   ext
   simp [DL,DR,hm,h_der]
 have h₂:_root_.IsNilpotent.exp DL=(_root_.IsNilpotent.exp D).lTensor B:=
   (h_nil.map_exp (lTensorAlgHom R B B)).symm
 have h₃:_root_.IsNilpotent.exp DR=(_root_.IsNilpotent.exp D).rTensor B:=
   (h_nil.map_exp (rTensorAlgHom R B B)).symm
 simp [h₁,_root_.IsNilpotent.exp_add_of_commute h_comm h_nilL h_nilR,h₂,h₃,hm]
end Module.End
end ProximityFlatProofPort
end PackedLegacy_IQ

/-! Packed from ProximityPrize.SubmissionLower.HE. -/
section PackedLegacy_HE
section ProximityFlatProofPort
structure LieDerivation (R L M:Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
   [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
   extends L →ₗ[R] M where
 protected leibniz' (a b:L):toLinearMap ⁅a,b⁆=⁅a,toLinearMap b⁆-⁅b,toLinearMap a⁆
/--.-/
add_decl_doc LieDerivation.toLinearMap
namespace LieDerivation
section
variable {R L M:Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
   [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (D:LieDerivation R L M) {D1 D2:LieDerivation R L M} (a b:L)
instance:FunLike (LieDerivation R L M) L M where
 coe D:=D.toFun
 coe_injective D1 D2 h:=by cases D1;cases D2;congr;exact DFunLike.coe_injective h
instance instLinearMapClass:LinearMapClass (LieDerivation R L M) R L M where
 map_add D:=D.toLinearMap.map_add'
 map_smulₛₗ D:=D.toLinearMap.map_smul
theorem toFun_eq_coe:D.toFun=⇑D:=rfl
def Simps.apply (D:LieDerivation R L M):L → M:=D
initialize_simps_projections LieDerivation (toFun → apply)
attribute [coe] toLinearMap
instance instCoeToLinearMap:Coe (LieDerivation R L M) (L →ₗ[R] M):=
 ⟨fun D => D.toLinearMap⟩
@[simp]
theorem mk_coe (f:L →ₗ[R] M) (h₁):((⟨f,h₁⟩:LieDerivation R L M):L → M)=f:=
 rfl
@[simp,norm_cast]
theorem coeFn_coe (f:LieDerivation R L M):⇑(f:L →ₗ[R] M)=f:=
 rfl
theorem coe_injective:@Function.Injective (LieDerivation R L M) (L → M) DFunLike.coe:=
 DFunLike.coe_injective
@[ext]
theorem ext (H:∀ a,D1 a=D2 a):D1=D2:=
 DFunLike.ext _ _ H
theorem congr_fun (h:D1=D2) (a:L):D1 a=D2 a:=
 DFunLike.congr_fun h a
@[simp]
lemma apply_lie_eq_sub (D:LieDerivation R L M) (a b:L):
   D ⁅a,b⁆=⁅a,D b⁆-⁅b,D a⁆:=
 D.leibniz' a b
lemma apply_lie_eq_add (D:LieDerivation R L L) (a b:L):
   D ⁅a,b⁆=⁅a,D b⁆+⁅D a,b⁆:=by
 rw [LieDerivation.apply_lie_eq_sub,sub_eq_add_neg,lie_skew]
theorem eqOn_lieSpan {s:Set L} (h:Set.EqOn D1 D2 s):
   Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s):=by
 intro _ hx
 induction hx using LieSubalgebra.lieSpan_induction with
 | mem x hx => exact h hx
 | zero => simp
 | add x y _ _ hx hy => simp [hx,hy]
 | smul t x _ hx => simp [hx]
 | lie x y _ _ hx hy => simp [hx,hy]
theorem ext_of_lieSpan_eq_top (s:Set L) (hs:LieSubalgebra.lieSpan R L s=⊤)
   (h:Set.EqOn D1 D2 s):D1=D2:=
 ext fun _ => eqOn_lieSpan h <| hs.symm ▸ trivial
section
open Finset Nat
theorem iterate_apply_lie (D:LieDerivation R L L) (n:ℕ) (a b:L):
   D^[n] ⁅a,b⁆=∑ ij∈antidiagonal n,choose n ij.1 • ⁅D^[ij.1] a,D^[ij.2] b⁆:=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [sum_antidiagonal_choose_succ_nsmul (M:=L) (fun i j => ⁅D^[i] a,D^[j] b⁆) n]
   simp only [Function.iterate_succ_apply',ih,map_sum,map_nsmul,apply_lie_eq_add,smul_add,
     sum_add_distrib,add_right_inj]
   refine sum_congr rfl fun ⟨i,j⟩ hij↦?_
   rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]
theorem iterate_apply_lie' (D:LieDerivation R L L) (n:ℕ) (a b:L):
   D^[n] ⁅a,b⁆=∑ i∈range (n+1),n.choose i • ⁅D^[i] a,D^[n-i] b⁆:=by
 rw [iterate_apply_lie D n a b]
 exact sum_antidiagonal_eq_sum_range_succ (fun i j↦n.choose i • ⁅D^[i] a,D^[j] b⁆) n
end
instance instZero:Zero (LieDerivation R L M) where
 zero:=
   { toLinearMap:=0
     leibniz':=fun a b => by simp only [LinearMap.zero_apply,lie_zero,sub_self]}
@[simp]
theorem coe_zero:⇑(0:LieDerivation R L M)=0:=
 rfl
@[simp]
theorem coe_zero_linearMap:↑(0:LieDerivation R L M)=(0:L →ₗ[R] M):=
 rfl
theorem zero_apply (a:L):(0:LieDerivation R L M) a=0:=
 rfl
instance:Inhabited (LieDerivation R L M):=
 ⟨0⟩
instance instAdd:Add (LieDerivation R L M) where
 add D1 D2:=
   { toLinearMap:=D1+D2
     leibniz':=fun a b↦by
       simp only [LinearMap.add_apply,coeFn_coe,apply_lie_eq_sub,lie_add,add_sub_add_comm]}
@[simp]
theorem coe_add (D1 D2:LieDerivation R L M):⇑(D1+D2)=D1+D2:=
 rfl
@[simp]
theorem coe_add_linearMap (D1 D2:LieDerivation R L M):↑(D1+D2)=(D1+D2:L →ₗ[R] M):=
 rfl
theorem add_apply:(D1+D2) a=D1 a+D2 a:=
 rfl
protected theorem map_neg:D (-a)= -D a:=
 map_neg D a
protected theorem map_sub:D (a-b)=D a-D b:=
 map_sub D a b
instance instNeg:Neg (LieDerivation R L M):=
 ⟨fun D =>
   mk (-D) fun a b => by
     simp only [LinearMap.neg_apply,coeFn_coe,apply_lie_eq_sub,
       neg_sub,lie_neg,sub_neg_eq_add,add_comm, ←sub_eq_add_neg] ⟩
@[simp]
theorem coe_neg (D:LieDerivation R L M):⇑(-D)= -D:=
 rfl
@[simp]
theorem coe_neg_linearMap (D:LieDerivation R L M):↑(-D)=(-D:L →ₗ[R] M):=
 rfl
theorem neg_apply:(-D) a= -D a:=
 rfl
instance instSub:Sub (LieDerivation R L M):=
 ⟨fun D1 D2 =>
   mk (D1-D2:L →ₗ[R] M) fun a b => by
     simp only [LinearMap.sub_apply,coeFn_coe,apply_lie_eq_sub,lie_sub,sub_sub_sub_comm]⟩
@[simp]
theorem coe_sub (D1 D2:LieDerivation R L M):⇑(D1-D2)=D1-D2:=
 rfl
@[simp]
theorem coe_sub_linearMap (D1 D2:LieDerivation R L M):↑(D1-D2)=(D1-D2:L →ₗ[R] M):=
 rfl
theorem sub_apply {D1 D2:LieDerivation R L M}:(D1-D2) a=D1 a-D2 a:=
 rfl
section Scalar
class SMulBracketCommClass (S L α:Type*) [SMul S α] [LieRing L] [AddCommGroup α]
   [LieRingModule L α]:Prop where
 smul_bracket_comm:∀ (s:S) (l:L) (a:α),s • ⁅l,a⁆=⁅l,s • a⁆
variable {S T:Type*}
 [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulBracketCommClass S L M]
 [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulBracketCommClass T L M]
instance instSMul:SMul S (LieDerivation R L M) where
 smul r D:=
   { toLinearMap:=r • D
     leibniz':=fun a b => by simp only [LinearMap.smul_apply,coeFn_coe,apply_lie_eq_sub,
       smul_sub,SMulBracketCommClass.smul_bracket_comm]}
@[simp]
theorem coe_smul (r:S) (D:LieDerivation R L M):⇑(r • D)=r • ⇑D:=
 rfl
@[simp]
theorem coe_smul_linearMap (r:S) (D:LieDerivation R L M):↑(r • D)=r • (D:L →ₗ[R] M):=
 rfl
theorem smul_apply (r:S) (D:LieDerivation R L M):(r • D) a=r • D a:=
 rfl
instance instSMulBase:SMulBracketCommClass R L M:=⟨fun s l a↦(lie_smul s l a).symm⟩
instance instSMulNat:SMulBracketCommClass ℕ L M:=⟨fun s l a => (lie_nsmul l a s).symm⟩
instance instSMulInt:SMulBracketCommClass ℤ L M:=⟨fun s l a => (lie_zsmul l a s).symm⟩
instance instAddCommGroup:AddCommGroup (LieDerivation R L M):=
 coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl
def coeFnAddMonoidHom:LieDerivation R L M →+L → M where
 toFun:=(↑)
 map_zero':=coe_zero
 map_add':=coe_add
@[simp]
lemma coeFnAddMonoidHom_apply (D:LieDerivation R L M):coeFnAddMonoidHom D=D:=rfl
instance:DistribMulAction S (LieDerivation R L M):=
 Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul
instance [SMul S T] [IsScalarTower S T M]:IsScalarTower S T (LieDerivation R L M):=
 ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
instance [SMulCommClass S T M]:SMulCommClass S T (LieDerivation R L M):=
 ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩
end Scalar
instance instModule {S:Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
   [SMulBracketCommClass S L M]:Module S (LieDerivation R L M):=
 Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul
end
section
variable {R L:Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
instance instBracket:Bracket (LieDerivation R L L) (LieDerivation R L L) where
 bracket D1 D2:=LieDerivation.mk ⁅(D1:Module.End R L),(D2:Module.End R L)⁆ (fun a b => by
   simp only [Ring.lie_def,apply_lie_eq_add,coeFn_coe,
     LinearMap.sub_apply,Module.End.mul_apply,map_add,sub_lie,lie_sub, ←lie_skew b]
   abel)
variable {D1 D2:LieDerivation R L L}
@[simp]
lemma commutator_coe_linear_map:↑⁅D1,D2⁆=⁅(D1:Module.End R L),(D2:Module.End R L)⁆:=
 rfl
lemma commutator_apply (a:L):⁅D1,D2⁆ a=D1 (D2 a)-D2 (D1 a):=
 rfl
instance:LieRing (LieDerivation R L L) where
 add_lie d e f:=by
   ext a;simp only [commutator_apply,add_apply,map_add];abel
 lie_add d e f:=by
   ext a;simp only [commutator_apply,add_apply,map_add];abel
 lie_self d:=by
   ext a;simp only [commutator_apply,zero_apply];abel
 leibniz_lie d e f:=by
   ext a;simp only [commutator_apply,add_apply,map_sub];abel
instance instLieAlgebra:LieAlgebra R (LieDerivation R L L) where
 lie_smul:=fun r d e => by ext a;simp only [commutator_apply,map_smul,smul_sub,smul_apply]
@[simp] lemma lie_apply (D₁ D₂:LieDerivation R L L) (x:L):
   ⁅D₁,D₂⁆ x=D₁ (D₂ x)-D₂ (D₁ x):=
 rfl
end
section
variable (R L:Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
attribute [local instance 100] LieRing.ofAssociativeRing
def toLinearMapLieHom:LieDerivation R L L →ₗ⁅R⁆ L →ₗ[R] L where
 toFun:=toLinearMap
 map_add':=by intro D1 D2;dsimp
 map_smul':=by intro D1 D2;dsimp
 map_lie':=by intro D1 D2;dsimp
lemma toLinearMapLieHom_injective:Function.Injective (toLinearMapLieHom R L):=
 fun _ _ h↦ext fun a↦congrFun (congrArg DFunLike.coe h) a
instance instNoetherian [IsNoetherian R L]:IsNoetherian R (LieDerivation R L L):=
 isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm
end
section Inner
variable (R L M:Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
   [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
@[simps!]
def inner:M →ₗ[R] LieDerivation R L M where
 toFun m:=
   { __:=(LieModule.toEnd R L M:L →ₗ[R] Module.End R M).flip m
     leibniz':=by simp}
 map_add' m n:=by ext;simp
 map_smul' t m:=by ext;simp
instance instLieRingModule:LieRingModule L (LieDerivation R L M) where
 bracket x D:=inner R L M (D x)
 add_lie x y D:=by simp
 lie_add x D₁ D₂:=by simp
 leibniz_lie x y D:=by simp
@[simp] lemma lie_lieDerivation_apply (x y:L) (D:LieDerivation R L M):
   ⁅x,D⁆ y=⁅y,D x⁆:=
 rfl
@[simp] lemma lie_coe_lieDerivation_apply (x:L) (D:LieDerivation R L M):
   ⁅x,(D:L →ₗ[R] M)⁆=⁅x,D⁆:=by
 ext;simp
instance instLieModule:LieModule R L (LieDerivation R L M) where
 smul_lie t x D:=by ext;simp
 lie_smul t x D:=by ext;simp
protected lemma leibniz_lie (x:L) (D₁ D₂:LieDerivation R L L):
   ⁅x,⁅D₁,D₂⁆⁆=⁅⁅x,D₁⁆,D₂⁆+⁅D₁,⁅x,D₂⁆⁆:=by
 ext y
 simp [-lie_skew, ←lie_skew (D₁ x) (D₂ y), ←lie_skew (D₂ x) (D₁ y),sub_eq_neg_add]
end Inner
section ExpNilpotent
variable {R L:Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
 (D:LieDerivation R L L)
noncomputable def exp (h:IsNilpotent D.toLinearMap):
   L ≃ₗ⁅R⁆ L:=
 { toLinearMap:=IsNilpotent.exp D.toLinearMap
   map_lie':=by
     let _i:=LieRing.toNonUnitalNonAssocRing L
     have:SMulCommClass R L L:=LieAlgebra.smulCommClass R L
     have:IsScalarTower R L L:=LieAlgebra.isScalarTower R L
     exact Module.End.exp_mul_of_derivation R L D.toLinearMap D.apply_lie_eq_add h
   invFun x:=IsNilpotent.exp (-D.toLinearMap) x
   left_inv x:=by
     simp only [AddHom.toFun_eq_coe,LinearMap.coe_toAddHom, ←LinearMap.comp_apply,
       ←Module.End.mul_eq_comp,h.exp_neg_mul_exp_self,Module.End.one_apply]
   right_inv x:=by
     simp only [AddHom.toFun_eq_coe,LinearMap.coe_toAddHom, ←LinearMap.comp_apply,
       ←Module.End.mul_eq_comp,h.exp_mul_exp_neg_self,Module.End.one_apply]}
lemma exp_apply (h:IsNilpotent D.toLinearMap):
   exp D h=IsNilpotent.exp D.toLinearMap:=
 rfl
lemma exp_map_apply (h:IsNilpotent D.toLinearMap) (l:L):
   exp D h l=IsNilpotent.exp D.toLinearMap l:=
 DFunLike.congr_fun (exp_apply D h) l
end ExpNilpotent
end LieDerivation
end ProximityFlatProofPort
end PackedLegacy_HE

/-! Packed from ProximityPrize.SubmissionLower.R3. -/
section PackedLegacy_R3
namespace ProximityPrize.SubmissionLower.RCN347
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Derivation
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem leibniz_product (D:Derivation K A A) (a b:A):
   D (a*b)=D a*b+a*D b:=by
 calc
   D (a*b)=a*D b+b*D a:=by
     simpa only [smul_eq_mul] using D.leibniz a b
   _=D a*b+a*D b:=by ac_rfl
theorem iterate_zero (D:Derivation K A A) (n:ℕ):D^[n] (0:A)=0:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih]
theorem iterate_add (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a+b)=D^[n] a+D^[n] b:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih,map_add]
theorem iterate_one_of_ne_zero (D:Derivation K A A) (n:ℕ) (hn:n≠0):
   D^[n] (1:A)=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,D.map_one_eq_zero]
   exact iterate_zero D n
theorem iterate_product (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a*b)=
     ∑ ij∈antidiagonal n,
       n.choose ij.1 • (D^[ij.1] a*D^[ij.2] b):=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [sum_antidiagonal_choose_succ_nsmul (M:=A)
     (fun i j => D^[i] a*D^[j] b) n]
   simp only [Function.iterate_succ_apply',ih,map_sum,map_nsmul,
     leibniz_product,smul_add,sum_add_distrib]
   rw [add_comm,add_right_inj]
   refine sum_congr rfl fun ⟨i,j⟩ hij => ?_
   rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
end Derivation
section NormalizedCoefficients
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem factorial_cast_ne_zero_below_characteristic
   (p:ℕ) [CharP L p]:∀ n:ℕ,n < p → (n.factorial:L)≠0:=by
 intro n
 induction n with
 | zero =>
   intro hn
   simp
 | succ n ih =>
   intro hn
   have hcast:((n+1:ℕ):L)≠0:=by
     intro hz
     have hdiv:p∣n+1:=(CharP.cast_eq_zero_iff L p (n+1)).mp hz
     exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) hdiv)
   rw [Nat.factorial_succ,Nat.cast_mul]
   exact mul_ne_zero hcast (ih (by omega))
noncomputable def jetCoefficient
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ):L:=
 value (D^[n] a)/(n.factorial:L)
theorem factorial_term_product
   (n i j:ℕ) (hij:i+j=n) (x y:L)
   (hn:(n.factorial:L)≠0)
   (hi:(i.factorial:L)≠0)
   (hj:(j.factorial:L)≠0):
   (n.choose i:L)*(x*y)/(n.factorial:L)=
     (x/(i.factorial:L))*(y/(j.factorial:L)):=by
 have hle:i ≤ n:=by omega
 have hsub:n-i=j:=by omega
 have hnat:=Nat.choose_mul_factorial_mul_factorial hle
 rw [hsub] at hnat
 have hcast:(n.choose i:L)*(i.factorial:L)*(j.factorial:L)=
     (n.factorial:L):=by
   simpa only [Nat.cast_mul] using congrArg (fun k:ℕ => (k:L)) hnat
 field_simp
 linear_combination (x*y)*hcast
theorem jetCoefficient_zero (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 0 n=0:=by
 simp [jetCoefficient,iterate_zero]
theorem jetCoefficient_one (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 1 n=if n=0 then 1 else 0:=by
 by_cases hn:n=0
 · subst n
   simp [jetCoefficient]
 · simp [jetCoefficient,iterate_one_of_ne_zero D n hn,hn]
theorem jetCoefficient_add
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ):
   jetCoefficient D value (a+b) n=
     jetCoefficient D value a n+jetCoefficient D value b n:=by
 simp only [jetCoefficient,iterate_add,map_add,add_div]
theorem jetCoefficient_product
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ)
   (hfactorial:∀ i ≤ n,(i.factorial:L)≠0):
   jetCoefficient D value (a*b) n=
     ∑ ij∈antidiagonal n,
       jetCoefficient D value a ij.1*jetCoefficient D value b ij.2:=by
 unfold jetCoefficient
 rw [iterate_product,map_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=n:=mem_antidiagonal.mp hij
 have hi:ij.1 ≤ n:=by omega
 have hj:ij.2 ≤ n:=by omega
 rw [map_nsmul,nsmul_eq_mul,map_mul]
 exact factorial_term_product n ij.1 ij.2 hsum
   (value (D^[ij.1] a)) (value (D^[ij.2] b))
   (hfactorial n le_rfl) (hfactorial ij.1 hi) (hfactorial ij.2 hj)
noncomputable def jetPolynomial
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A):Polynomial L:=
 ∑ j∈range bound,Polynomial.monomial j (jetCoefficient D value a j)
theorem jetPolynomial_coeff
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A) (j:ℕ):
   (jetPolynomial D value bound a).coeff j=
     if j < bound then jetCoefficient D value a j else 0:=by
 classical
 simp [jetPolynomial,Polynomial.coeff_monomial]
theorem jetPolynomial_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ):
   jetPolynomial D value bound 0=0:=by
 ext j
 simp [jetPolynomial_coeff,jetCoefficient_zero]
theorem jetPolynomial_one
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (hbound:0 < bound):
   jetPolynomial D value bound 1=1:=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient_one,hbound]
 · simp [jetPolynomial_coeff,jetCoefficient_one,hj,Polynomial.coeff_one]
theorem jetPolynomial_add
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A):
   jetPolynomial D value bound (a+b)=
     jetPolynomial D value bound a+jetPolynomial D value bound b:=by
 ext j
 by_cases hj:j < bound <;>
   simp [jetPolynomial_coeff,jetCoefficient_add,hj]
theorem X_pow_dvd_jetPolynomial_product_error
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 rw [Polynomial.X_pow_dvd_iff]
 intro j hj
 rw [Polynomial.coeff_sub]
 apply sub_eq_zero.mpr
 rw [jetPolynomial_coeff,if_pos hj,Polynomial.coeff_mul,
   jetCoefficient_product D value a b j (fun k hk =>
     hfactorial k (lt_of_le_of_lt hk hj))]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=j:=mem_antidiagonal.mp hij
 have hi:ij.1 < bound:=by omega
 have hk:ij.2 < bound:=by omega
 rw [jetPolynomial_coeff,if_pos hi,jetPolynomial_coeff,if_pos hk]
theorem X_pow_dvd_jetPolynomial_product_error_of_char
   (D:Derivation K A A) (value:A →+*L) (p bound:ℕ) [CharP L p]
   (hbound:bound ≤ p) (a b:A):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 apply X_pow_dvd_jetPolynomial_product_error
 intro j hj
 exact factorial_cast_ne_zero_below_characteristic p j (lt_of_lt_of_le hj hbound)
end NormalizedCoefficients
end ProximityPrize.SubmissionLower.RCN347
end PackedLegacy_R3

/-! Packed from ProximityPrize.SubmissionLower.R4. -/
section PackedLegacy_R4
namespace ProximityPrize.SubmissionLower.RCN348
open RCN347
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section TaylorMap
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
noncomputable def truncationIdeal (L:Type*) [Field L] (bound:ℕ):Ideal (Polynomial L):=
 Ideal.span ({(Polynomial.X:Polynomial L)^bound}:Set (Polynomial L))
abbrev TruncatedPolynomials (L:Type*) [Field L] (bound:ℕ):=
 Polynomial L ⧸ truncationIdeal L bound
noncomputable def taylorHom
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   A →+*TruncatedPolynomials L bound where
 toFun a:=Ideal.Quotient.mk (truncationIdeal L bound)
   (jetPolynomial D value bound a)
 map_zero':=by rw [jetPolynomial_zero,map_zero]
 map_one':=by rw [jetPolynomial_one D value bound hbound,map_one]
 map_add' a b:=by rw [jetPolynomial_add,map_add]
 map_mul' a b:=by
   rw [←map_mul]
   apply Ideal.Quotient.eq.mpr
   apply Ideal.mem_span_singleton.mpr
   exact X_pow_dvd_jetPolynomial_product_error D value bound a b hfactorial
theorem taylorHom_apply
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0) (a:A):
   taylorHom D value bound hbound hfactorial a=
     Ideal.Quotient.mk (truncationIdeal L bound) (jetPolynomial D value bound a):=
 rfl
theorem iterate_eq_zero_of_derivation_eq_zero
   (D:Derivation K A A) (a:A) (ha:D a=0) (n:ℕ) (hn:n≠0):
   D^[n] a=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,ha]
   exact iterate_zero D n
theorem jetPolynomial_of_derivation_eq_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound) (a:A) (ha:D a=0):
   jetPolynomial D value bound a=Polynomial.C (value a):=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient,hbound]
 · have hiter:=iterate_eq_zero_of_derivation_eq_zero D a ha j hj
   simp [jetPolynomial_coeff,jetCoefficient,hiter,Polynomial.coeff_C,hj]
theorem jetPolynomial_algebraMap
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound) (c:K):
   jetPolynomial D value bound (algebraMap K A c)=
     Polynomial.C (value (algebraMap K A c)):=
 jetPolynomial_of_derivation_eq_zero D value bound hbound _ (D.map_algebraMap c)
theorem jetCoefficient_derivation
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ)
   (hn:(n.factorial:L)≠0)
   (hsucc:((n+1).factorial:L)≠0):
   jetCoefficient D value (D a) n=
     jetCoefficient D value a (n+1)*(n+1:L):=by
 have hcast:(n+1:L)≠0:=by
   have hmul:(n+1:L)*(n.factorial:L)≠0:=by
     simpa only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hsucc
   exact (mul_ne_zero_iff.mp hmul).1
 simp only [jetCoefficient,Function.iterate_succ_apply,
   Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
 field_simp
theorem jetPolynomial_derivation_eq_derivative
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A)
   (hfactorial:∀ j ≤ bound,(j.factorial:L)≠0)
   (hlast:jetCoefficient D value a bound=0):
   jetPolynomial D value bound (D a)=
     (jetPolynomial D value bound a).derivative:=by
 ext j
 rw [Polynomial.coeff_derivative,jetPolynomial_coeff,jetPolynomial_coeff]
 by_cases hj:j < bound
 · rw [if_pos hj,jetCoefficient_derivation D value a j
     (hfactorial j hj.le) (hfactorial (j+1) (by omega))]
   by_cases hnext:j+1 < bound
   · rw [if_pos hnext]
   · have heq:j+1=bound:=by omega
     simp [heq,hlast]
 · have hnext:¬j+1 < bound:=by omega
   rw [if_neg hj,if_neg hnext,zero_mul]
theorem jetPolynomial_derivation_eq_derivative_of_char
   (D:Derivation K A A) (value:A →+*L) (p bound:ℕ) [CharP L p]
   (hbound:bound < p) (a:A)
   (hlast:jetCoefficient D value a bound=0):
   jetPolynomial D value bound (D a)=
     (jetPolynomial D value bound a).derivative:=by
 apply jetPolynomial_derivation_eq_derivative D value bound a
 · intro j hj
   exact factorial_cast_ne_zero_below_characteristic p j (lt_of_le_of_lt hj hbound)
 · exact hlast
theorem jetPolynomial_eq_shorter_of_tails_zero
   (D:Derivation K A A) (value:A →+*L) (small bound:ℕ) (a:A)
   (hsmall:small ≤ bound)
   (htails:∀ j,small ≤ j → j < bound → jetCoefficient D value a j=0):
   jetPolynomial D value bound a=jetPolynomial D value small a:=by
 ext j
 rw [jetPolynomial_coeff,jetPolynomial_coeff]
 by_cases hj:j < small
 · rw [if_pos hj,if_pos (lt_of_lt_of_le hj hsmall)]
 · rw [if_neg hj]
   by_cases hb:j < bound
   · rw [if_pos hb,htails j (by omega) hb]
   · rw [if_neg hb]
theorem eq_zero_of_quotient_eq_zero_of_natDegree_lt
   (bound:ℕ) (Q:Polynomial L) (hdegree:Q.natDegree < bound)
   (hzero:Ideal.Quotient.mk (truncationIdeal L bound) Q=0):Q=0:=by
 have hmem:=Ideal.Quotient.eq_zero_iff_mem.mp hzero
 have hdvd:(Polynomial.X:Polynomial L)^bound∣Q:=
   Ideal.mem_span_singleton.mp hmem
 have hcoeff:=Polynomial.X_pow_dvd_iff.mp hdvd
 ext j
 rw [Polynomial.coeff_zero]
 by_cases hj:j < bound
 · exact hcoeff j hj
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdegree (by omega))
end TaylorMap
section PolynomialRelation
variable {K A L σ:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem polynomial_relation_of_taylor_substitution
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0)
   (coordinates:σ → A) (polynomials:σ → Polynomial L)
   (hcoordinates:∀ i,
     jetPolynomial D value bound (coordinates i)=polynomials i)
   (F:MvPolynomial σ K)
   (hrelation:MvPolynomial.eval₂Hom (algebraMap K A) coordinates F=0)
   (hdegree:(MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F).natDegree < bound):
   MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F=0:=by
 let τ:=taylorHom D value bound hbound hfactorial
 let mk:=Ideal.Quotient.mk (truncationIdeal L bound)
 have hhom:τ.comp (MvPolynomial.eval₂Hom (algebraMap K A) coordinates)=
     mk.comp (MvPolynomial.eval₂Hom
       (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials):=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     change mk (jetPolynomial D value bound (algebraMap K A c))=
       mk (Polynomial.C (value (algebraMap K A c)))
     rw [jetPolynomial_algebraMap D value bound hbound]
   · intro i
     simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
     change mk (jetPolynomial D value bound (coordinates i))=mk (polynomials i)
     rw [hcoordinates]
 apply eq_zero_of_quotient_eq_zero_of_natDegree_lt bound _ hdegree
 have hF:=RingHom.congr_fun hhom F
 change τ (MvPolynomial.eval₂Hom (algebraMap K A) coordinates F)=
   mk (MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F) at hF
 rw [hrelation,map_zero] at hF
 exact hF.symm
end PolynomialRelation
end ProximityPrize.SubmissionLower.RCN348
end PackedLegacy_R4
