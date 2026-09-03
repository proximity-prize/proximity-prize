import ProximityPrize.SubmissionLower.CommonShearDegreePrototype
import ProximityPrize.SubmissionLower.CommonShearFiberPrototype

namespace ProximityPrize.SubmissionLower.CommonShearFamilyPrototype

open scoped Classical BigOperators
open RCN001 RCN002 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN067 RCN093
  RCN231 RCN238 RCN319 RCN344 RCN370 RCN372
open CommonShearFiberPrototype RCN988

noncomputable section

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
local instance : DecidableEq K := Classical.decEq K

variable {I : Type} [Fintype I]
  (Q : I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i, (Q i).IsPrime]

private theorem elementEmbedding_congr_local
    {L : Type} [Field L] [Algebra Ω L] {s t : L}
    (hs : Transcendental Ω s) (ht : Transcendental Ω t) (h : s = t) :
    elementEmbedding Ω L s hs = elementEmbedding Ω L t ht := by
  subst t
  rfl

/-- Complete input package for `proper_cut_seed_bound_of_global_shear_sum`:
one common nonzero shear, one degree per component, the aggregate degree
budget, and a `GlobalShearFiberCertificate` for every component.  Components
with algebraic `Z` use the cardinality-one route; all transcendental sheared
coordinates (including algebraic-`Z`/transcendental-`R`) are charged together
by the family resultant. -/
theorem exists_common_global_shear_family
    (hinj : Function.Injective Q)
    (hfinite : ∀ i, ProjectionsFinite Ω (Q i))
    (hnonpoint : ∀ i (v : Fin 3 → Ω),
      Q i ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hsepY : ∀ i (hY : Transcendental Ω (coordinate Ω (Q i) 0)),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        rationalBaseAlgebra Ω (Q i) 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (Q i)))
    (hsepZ : ∀ i (hZ : Transcendental Ω (coordinate Ω (Q i) 2)),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        rationalBaseAlgebra Ω (Q i) 2 hZ
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (Q i)))
    (G T : MvPolynomial (Fin 3) Ω) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : I → Finset K) (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ i γ, γ ∈ Γ i → (selected γ).natDegree ≤ w)
    (hsolution : ∀ i γ, γ ∈ Γ i →
      specialization K (selected γ) γ F = 0)
    (hregular : ∀ i γ, γ ∈ Γ i → MvPolynomial.eval₂Hom
      (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ i γ, γ ∈ Γ i → Q i ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1) :
    ∃ a : Ω, a ≠ 0 ∧ ∃ dS : I → ℕ,
      (∑ i, dS i) ≤ coordinateMixedDegree Ω G T 1 +
          coordinateMixedDegree Ω G T 2 ∧
      ∀ i, GlobalShearFiberCertificate φ (Q i) F selected (Γ i) w
        (dS i) cap := by
  classical
  obtain ⟨a, ha0, hzdata, hall⟩ :=
    exists_common_shear_with_full_transcendental_sum_bound Q hinj
      (fun i hZ => hfinite i 2 hZ) hsepZ
      G T hG hGmem hTmem hproper
  let sS : Set I := {i | Transcendental Ω (affineV Ω (Q i) 0 a)}
  let hSsub : ∀ i : sS, Transcendental Ω (affineV Ω (Q i) 0 a) :=
    fun i => i.2
  let D : sS → ℕ := fun i =>
    letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
      (elementEmbedding Ω (CoordinateField Ω (Q i))
        (affineV Ω (Q i) 0 a) (hSsub i)).toRingHom.toAlgebra
    Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
  let dS : I → ℕ := fun i =>
    if hSi : Transcendental Ω (affineV Ω (Q i) 0 a) then
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) hSi).toRingHom.toAlgebra
      Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
    else 0
  have hall' :
      letI : ∀ i : sS,
          Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        fun i => (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) (hSsub i)).toRingHom.toAlgebra
      (∀ i : sS,
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i))) ∧
        (∑ i : sS,
          Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) ≤
            coordinateMixedDegree Ω G T 1 +
              coordinateMixedDegree Ω G T 2 := by
    simpa only [sS, hSsub] using hall
  have hsum : (∑ i, dS i) ≤ coordinateMixedDegree Ω G T 1 +
      coordinateMixedDegree Ω G T 2 := by
    calc
      (∑ i, dS i) = ∑ i : sS, D i := by
        apply Finset.sum_congr_set sS dS D
        · intro i hi
          change Transcendental Ω (affineV Ω (Q i) 0 a) at hi
          simp only [dS, dif_pos hi, D, hSsub]
        · intro i hi
          change ¬ Transcendental Ω (affineV Ω (Q i) 0 a) at hi
          simp only [dS, dif_neg hi]
      _ ≤ _ := by
        exact hall'.2
  refine ⟨a, ha0, dS, hsum, ?_⟩
  intro i
  by_cases hZi : Transcendental Ω (coordinate Ω (Q i) 2)
  · obtain ⟨hSi, hfiniteSi, hsepSi⟩ := hzdata i hZi
    have hSaffine : Transcendental Ω (affineV Ω (Q i) 0 a) := by
      simpa [affineV] using hSi
    have hfiber := globalShearFiberCertificate_of_common_shear
      (Q i) φ (hfinite i) (hnonpoint i) hZi (hsepY i) (hsepZ i)
      a hSi hfiniteSi hsepSi F selected (Γ i) p w hchar
      (fun γ hγ => hdegree i γ hγ)
      (fun γ hγ => hsolution i γ hγ)
      (fun γ hγ => hregular i γ hγ)
      (fun γ hγ => hpoint i γ hγ) cap
    have hemb :
        elementEmbedding Ω (CoordinateField Ω (Q i))
            (affineV Ω (Q i) 0 a) hSaffine =
          elementEmbedding Ω (CoordinateField Ω (Q i))
            (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2) hSi :=
      elementEmbedding_congr_local hSaffine hSi (by simp [affineV])
    have hdS : dS i =
        (letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
          (elementEmbedding Ω (CoordinateField Ω (Q i))
            (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2)
            hSi).toRingHom.toAlgebra;
          Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) := by
      rw [show dS i =
          (letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
            (elementEmbedding Ω (CoordinateField Ω (Q i))
              (affineV Ω (Q i) 0 a) hSaffine).toRingHom.toAlgebra;
            Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) by
        simp only [dS, dif_pos hSaffine]]
      rw [hemb]
    rw [hdS]
    exact hfiber
  · have hZalg : IsAlgebraic Ω (coordinate Ω (Q i) 2) := not_not.mp hZi
    have hSdegree : Transcendental Ω
        (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2) →
        1 ≤ dS i := by
      intro hSi
      have hSaffine : Transcendental Ω (affineV Ω (Q i) 0 a) := by
        simpa [affineV] using hSi
      let j : sS := ⟨i, hSaffine⟩
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) hSaffine).toRingHom.toAlgebra
      have hfd : FiniteDimensional (RatFunc Ω)
          (CoordinateField Ω (Q i)) := by
        simpa only [j, sS, hSsub] using hall'.1 j
      letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)) := hfd
      have hpos : 1 ≤ Module.finrank (RatFunc Ω)
          (CoordinateField Ω (Q i)) := Module.finrank_pos
      simpa only [dS, dif_pos hSaffine] using hpos
    exact globalShearFiberCertificate_of_algebraic_z
      (Q i) φ (hfinite i) (hnonpoint i) hZalg a (dS i) hSdegree
      F selected (Γ i) w (fun γ hγ => hpoint i γ hγ)
      cap hcapY hcapS

end

end ProximityPrize.SubmissionLower.CommonShearFamilyPrototype
