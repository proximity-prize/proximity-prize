import ProximityPrize.SubmissionLower.ContactTwoTailProviderAssembly6732Research
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Flat_TorsionFree
namespace ProximityPrize.SubmissionLower.ContactOriginalFactorLocalDVR6732Research
open scoped Classical TensorProduct
open ContactGenericInitialPoint ContactGenericSurface
open ContactCurveComponents ContactRegularComponentCover
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
abbrev Omega (K:Type) [Field K]:=GenericField K
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
abbrev Collected (K:Type) [Field K]:=
  MvPolynomial (Fin 3) (Polynomial K)
abbrev GenericPoly3 (K:Type) [Field K]:=
  MvPolynomial (Fin 3) (Omega K)
local instance:Algebra (Polynomial K) (Omega K):=
  (polynomialEmbedding K).toAlgebra
local instance:Module.IsTorsionFree (Polynomial K) (Omega K):=
  (Module.isTorsionFree_iff_algebraMap_injective).2
    (polynomialEmbedding_injective K)
local instance:Module.Flat (Polynomial K) (Omega K):=inferInstance
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra
local instance genericPolynomial_flat:
    Module.Flat (Collected K) (GenericPoly3 K):=by
  let E:=Algebra.IsPushout.equiv (Polynomial K) (Collected K)
    (Omega K) (GenericPoly3 K)
  letI:Module.Flat (Collected K)
      ((Collected K) ⊗[Polynomial K] Omega K):=inferInstance
  exact Module.Flat.of_linearEquiv E.symm.toLinearEquiv
def collectedPrime (P:Ideal (GenericPoly3 K)):Ideal (Collected K):=
  P.comap (algebraMap (Collected K) (GenericPoly3 K))
def originalPrime (P:Ideal (GenericPoly3 K)):Ideal (Poly4 K):=
  (collectedPrime P).comap (collectX K).toRingEquiv
theorem mem_originalPrime_iff
    (P:Ideal (GenericPoly3 K)) (A:Poly4 K):
    A∈originalPrime P ↔
      surfaceMap (polynomialEmbedding K) A∈P:=by
  rfl
instance collectedPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
    (collectedPrime P).IsPrime:=
  Ideal.IsPrime.comap (algebraMap (Collected K) (GenericPoly3 K))
instance originalPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
    (originalPrime P).IsPrime:=
  Ideal.IsPrime.comap (collectX K).toRingEquiv
theorem collectedPrime_height_le
    (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
    (collectedPrime P).height ≤ P.height:=by
  let p:=collectedPrime P
  letI:p.IsPrime:=inferInstance
  letI:P.LiesOver p:=⟨rfl⟩
  have h:=Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  rw [h]
  exact le_add_right (le_refl _)
theorem originalPrime_height_le
    (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
    (originalPrime P).height ≤ P.height:=by
  calc
    (originalPrime P).height=(collectedPrime P).height:=by
      simpa only [originalPrime] using
        RingEquiv.height_comap (collectX K).toRingEquiv (collectedPrime P)
    _ ≤ P.height:=collectedPrime_height_le P
theorem originalPrime_height_eq_two
    (P:Ideal (GenericPoly3 K)) [P.IsPrime]
    (hPheight:P.height ≤ 2)
    (F N:Poly4 K) (hF:Irreducible F)
    (hFmem:surfaceMap (polynomialEmbedding K) F∈P)
    (hNmem:surfaceMap (polynomialEmbedding K) N∈P)
    (hproper:¬ F∣N):
    (originalPrime P).height=2:=by
  let p:=originalPrime P
  let I:Ideal (Poly4 K):=Ideal.span {F}
  letI:p.IsPrime:=inferInstance
  letI:I.IsPrime:=Ideal.isPrime_span_singleton_of_prime hF.prime
  have hFmem':F∈p:=(mem_originalPrime_iff P F).2 hFmem
  have hNmem':N∈p:=(mem_originalPrime_iff P N).2 hNmem
  have hIp:I ≤ p:=by
    apply Ideal.span_le.2
    simpa using hFmem'
  have hNnot:N∉I:=by
    intro h
    exact hproper (Ideal.mem_span_singleton.mp h)
  have hIne:I≠p:=by
    intro h
    exact hNnot (h ▸ hNmem')
  have hIlt:I < p:=lt_of_le_of_ne hIp hIne
  have hIbot:I≠⊥:=by
    intro h
    have hzero:F=0:=by
      have:F∈(⊥:Ideal (Poly4 K)):=h ▸ Ideal.subset_span (by simp)
      simpa using this
    exact hF.ne_zero hzero
  have hbotlt:(⊥:Ideal (Poly4 K)) < I:=
    lt_of_le_of_ne bot_le hIbot.symm
  have hone:(1:ℕ∞) ≤ I.height:=by
    calc
      1=(0:ℕ∞)+1:=by simp
      _ ≤ (⊥:Ideal (Poly4 K)).height+1:=by gcongr;exact zero_le
      _ ≤ I.height:=Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
  have htwo:(2:ℕ∞) ≤ p.height:=by
    calc
      2=(1:ℕ∞)+1:=by norm_num
      _ ≤ I.height+1:=by gcongr
      _ ≤ p.height:=Ideal.height_add_one_le_of_lt_of_isPrime hIlt
  exact le_antisymm ((originalPrime_height_le P).trans hPheight) htwo
abbrev AmbientLocal (P:Ideal (Poly4 K)) [P.IsPrime]:=
  Localization.AtPrime P
abbrev OriginalFactorLocalRing
    (P:Ideal (Poly4 K)) [P.IsPrime] (F:Poly4 K):=
  AmbientLocal P ⧸ Ideal.span
    {algebraMap (Poly4 K) (AmbientLocal P) F}
private theorem derivation_sq_mem_maximal
    {A:Type} [CommRing A] [IsLocalRing A]
    {k:Type} [CommRing k] [Algebra k A]
    (D:Derivation k A A) {f:A}
    (hf:f∈IsLocalRing.maximalIdeal A^2):
    D f∈IsLocalRing.maximalIdeal A:=by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro x hx y hy
    rw [D.leibniz]
    exact (IsLocalRing.maximalIdeal A).add_mem
      ((IsLocalRing.maximalIdeal A).mul_mem_right (D y) hx)
      ((IsLocalRing.maximalIdeal A).mul_mem_right (D x) hy)
  · intro x y hx hy
    simpa only [map_add] using (IsLocalRing.maximalIdeal A).add_mem hx hy
end
end ProximityPrize.SubmissionLower.ContactOriginalFactorLocalDVR6732Research
