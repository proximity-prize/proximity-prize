-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, KoalaRootSurface.lean.
import ProximityPrize.SubmissionLower.Peer653KoalaBoxLift
import ProximityPrize.SubmissionLower.Peer653KoalaPointCount
import ProximityPrize.SubmissionLower.Peer653High53UpperGeometry

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace SplitCut.RootSurface
noncomputable section
open MvPolynomial SplitCut.BoxDegree
open K1_14 (FX Equation)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (flatten)
open Peer653High53Upper
open scoped BigOperators
abbrev x (J : Input) (γ : P1.K) := rootPoint (J.model.label γ) (J.family.scalar γ)
abbrev liftPoint (a b c : ℕ) (J : Input) (γ : P1.K) :=
  monomialPoint (exps a b c) (x J γ)
abbrev rootI {J : Input} {B : ResidueLift J} (D : Factors J B) (a b c : ℕ) :=
  (Ideal.span {flatten D.proper}).comap (proj FX a b c)

theorem injective {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (J : Input) :
    Function.Injective (liftPoint a b c J) := by
  intro γ η h
  have h' := monomialPoint_injective (axis ha hb hc) h
  have h₀ := congrFun h' (some (0:Fin 2))
  change K1_14.seedEmbedding (J.model.label γ) = K1_14.seedEmbedding (J.model.label η) at h₀
  exact sub_left_inj.mp (K1_14.seedEmbedding.injective h₀)

theorem mark_on_root {a b c : ℕ} {J : Input} {B : ResidueLift J} (D : Factors J B)
    {γ : P1.K} (hγ : rootOn J D.proper γ) : liftPoint a b c J γ ∈ zeroLocus FX (rootI D a b c) := by
  intro f hf
  rw [aeval_monomialPoint]
  change proj FX a b c f ∈ Ideal.span {flatten D.proper} at hf
  obtain ⟨k,hk⟩ := Ideal.mem_span_singleton.mp hf
  rw [hk,map_mul]
  have hz : aeval (x J γ) (flatten D.proper) = (0:FX) := by
    change K1_14_6_1.markEval _ _ _ = 0
    rw [K1_14_6_1.eval_flatten]
    exact hγ
  rw [hz,zero_mul]

theorem minimal_dimension {F : Type*} [Field F] {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    {g : MvPolynomial Idx F} (hg : g ≠ 0) {P : Ideal (MvPolynomial (exps a b c) F)}
    (hP : P ∈ ((Ideal.span {g}).comap (proj F a b c)).minimalPrimes) :
    (affineHilbertPolynomial P).natDegree = 2 := by
  let φ := proj F a b c
  have hφ : Function.Surjective φ := monomialMap_surjective (axis ha hb hc)
  obtain ⟨z,hz⟩ := hφ g
  change P ∈ ((Ideal.span {g}).comap φ).minimalPrimes at hP
  rw [← hz,Ideal.comap_span_singleton_of_surjective φ hφ] at hP
  have hK : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hnot : z ∉ RingHom.ker φ := fun h => hg (hz ▸ RingHom.mem_ker.mp h)
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hnot hP
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective φ hφ,
    show Nat.card Idx = 3 by simp [Idx,Nat.card_eq_fintype_card]] at hd
  omega

theorem cutoff_proper {a b c : ℕ} {J : Input} {B : ResidueLift J} (D : Factors J B)
    {p : MvPolynomial (exps a b c) FX} (hp : proj FX a b c p = quotientNumerator J B (J.ell+1))
    {P : Ideal (MvPolynomial (exps a b c) FX)} (hP : P ∈ (rootI D a b c).minimalPrimes) :
    p ∉ P := by
  intro h
  obtain ⟨z,hz,hpz⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP h
  let U := optionEquivLeft FX (Fin 2)
  have memI (f : MvPolynomial (exps a b c) FX) :
      f ∈ rootI D a b c ↔ D.proper ∣ U (proj FX a b c f) := by
    change proj FX a b c f ∈ Ideal.span {flatten D.proper} ↔ _
    rw [Ideal.mem_span_singleton,← map_dvd_iff U, show U (flatten D.proper) = D.proper from
      U.apply_symm_apply _]
  have hdiv := (memI _).mp hpz
  rw [map_mul,hp,map_mul] at hdiv
  change D.proper ∣ cutoff J B * U (proj FX a b c z) at hdiv
  have hfield := Polynomial.map_dvd (algebraMap K1_14.Seeds SeedField) hdiv
  rw [Polynomial.map_mul] at hfield
  have hq := D.proper_coprime.dvd_of_dvd_mul_left hfield
  have hprim := Polynomial.isPrimitive_of_dvd J.reduced.2.1 (show D.proper ∣ J.f from ⟨_,D.product⟩)
  exact hz ((memI _).mpr ((hprim.dvd_iff_fraction_map_dvd_fraction_map SeedField).mpr hq))

theorem divisor_fit {f g : Biform} {a b c : ℕ} (hf : f ≠ 0) (hd : g ∣ f)
    (hfit : f ∈ space FX a b c) : g ∈ space FX a b c := by
  obtain ⟨l,he⟩ := hd
  have hne := mul_ne_zero_iff.mp (he ▸ hf)
  have hle (i : Idx) : g.degreeOf i ≤ f.degreeOf i := by
    rw [he,degreeOf_mul_eq hne.1 hne.2]
    omega
  intro m hm
  refine ⟨(monomial_le_degreeOf none hm).trans ((hle _).trans ?_),
    (monomial_le_degreeOf (some 0) hm).trans ((hle _).trans ?_),
    (monomial_le_degreeOf (some 1) hm).trans ((hle _).trans ?_)⟩
  · exact degreeOf_le_iff.mpr (fun m hm => (hfit hm).1)
  · exact degreeOf_le_iff.mpr (fun m hm => (hfit hm).2.1)
  · exact degreeOf_le_iff.mpr (fun m hm => (hfit hm).2.2)

theorem proper_fit {J : Input} {B : ResidueLift J} (D : Factors J B) {v w : ℕ}
    (hfit : flatten J.f ∈ space FX J.e v w) : flatten D.proper ∈ space FX J.e v w := by
  have hne : J.f ≠ 0 := fun h => Nat.ne_of_gt J.reduced.1 (by simp [h])
  have hn : flatten J.f ≠ 0 := by simpa only [flatten,map_ne_zero_iff _ (optionEquivLeft FX (Fin 2)).symm.injective] using hne
  apply divisor_fit hn _ hfit
  exact map_dvd (optionEquivLeft FX (Fin 2)).symm (show D.proper ∣ J.f from ⟨_, D.product⟩)

end
end SplitCut.RootSurface
#print axioms SplitCut.RootSurface.cutoff_proper
#print axioms SplitCut.RootSurface.proper_fit
