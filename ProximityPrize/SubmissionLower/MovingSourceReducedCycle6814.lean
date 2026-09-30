import ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814
import ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
namespace ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN249 RCN252
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN108 RCN109 RCN111 RCN112 RCN113
open RCN120 RCN125 RCN313 RCN333 RCN102
open MovingSourceFlowNumerator6814 MovingSourceReducedPrimary6814

theorem plane_not_dvd_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N) :
    ¬flagPlaneMap Ω lam mu nu order F∣flagPlaneMap Ω lam mu nu order N := by
  have hroot : flagEvaluation Ω C.1 lam mu nu (flagAlgHom lam mu nu F)=0 := by
    rw [flagEvaluation_flag]
    change F∈RingHom.ker (coordinateEvaluation Ω C.1).toRingHom
    rw [coordinateEvaluation_ker]
    exact RCN264.regularComponent_G_mem Ω F T R C
  intro hd
  have hh := (planeMap_dvd_iff_of_evaluation Ω (CoordinateField Ω C.1) order
    (flagEvaluation Ω C.1 lam mu nu) (flagAlgHom lam mu nu F) (flagAlgHom lam mu nu N)
    ((flag_irreducible_iff lam mu nu F).mpr hF) hroot ht).mp hd
  exact hN ((flag_dvd_iff lam mu nu F N).mp hh)

theorem resultant_ne_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N)
    (hpos : 0<(flagPlaneMap Ω lam mu nu order F).natDegree) :
    flagPlaneResultant lam mu nu order F N≠0 := by
  classical
  have hi := RCN103.transformedSurface_irreducible lam mu nu order hF C ht
  have hn := plane_not_dvd_replacement C lam mu nu order ht hF N hN
  exact RCN362.irreducible_resultant_ne_zero_of_not_dvd _ _ hi hpos hn

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

def reducedTailSurface (H G : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  surfaceMap (polynomialEmbedding K) (numerators H G (RCN326.w+1))

theorem reduced_resultant_ne
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (a : A)
    (H G : MvPolynomial (Fin 4) K) (hproper : ¬S.G∣reducedTailSurface H G) :
    flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G)≠0 := by
  exact resultant_ne_replacement (F.component a) F.lam F.mu F.nu F.order (F.ht a)
    S.irreducible_G (reducedTailSurface H G) hproper F.positive

theorem reduced_grouped_power_dvd
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (W : StageIndexedFactor S A F) :
    W.q^stageFamilyGroupedExponent S A hfirst F W.q∣
      flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G) := by
  let surface := stageSurfacePlane S F.lam F.mu F.nu F.order
  let oldTail := stageTailPlane S F.lam F.mu F.nu F.order
  let newTail := flagPlaneMap (GenericField K) F.lam F.mu F.nu F.order (reducedTailSurface H G)
  letI : (Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime :=
    indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G W.q W.irreducible W.witness
  have hsurface := indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu F.order F.ht
  have holdRoot : ∀ a : IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q,
      oldTail∈relationKernel (GenericField K) (CoordinateField (GenericField K) (F.component a.1).1)
        F.order (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu) (F.ht a.1) := by
    intro a
    exact flagPlaneMap_mem_relation (F.component a.1).1 F.lam F.mu F.nu F.order (F.ht a.1)
      (RCN264.regularComponent_T_mem (GenericField K) S.G _ _ (F.component a.1))
  have holdProper : indexedFiberTail W.q W.irreducible oldTail∉
      Ideal.span {indexedFiberSurface W.q W.irreducible surface} :=
    indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G hfirst W.q W.irreducible W.witness
  have hbar := indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order F.ht
    W.q W.irreducible surface oldTail holdRoot holdProper
  have htail := indexed_reduced_tail_mem_primary S hfirst H G hcross F.component
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible
  have hres : Polynomial.resultant surface newTail surface.natDegree newTail.natDegree≠0 :=
    reduced_resultant_ne S F W.witness.1 H G hproper
  have hmod : (indexedFiberSurface W.q W.irreducible surface).map
      (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0 :=
    stageFamily_surface_mod_ne S F W
  exact indexedFixedFactor_grouped_resultant_power_dvd_of_geometry F.component F.injective
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible W.monic
    surface newTail surface.natDegree newTail.natDegree
    (fun a => hsurface a.1) hbar
    (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a.1))
    htail Polynomial.natDegree_map_le Polynomial.natDegree_map_le hres hmod

theorem reduced_projection_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A)
    (hgate : ∀ a, ∀ hx : Transcendental (GenericField K)
        (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
          (MvPolynomial.X (F.order 0))),
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)) ∧
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)))
    (axis : MovingSourceProjectionFamily6814.Axis) (horder : F.order=axis.order)
    (surfaceFlag tailFlag : FlagDegree)
    (hSflag : RCN095.PolynomialInFlag surfaceFlag S.G)
    (hTflag : RCN095.PolynomialInFlag tailFlag (reducedTailSurface H G)) :
    (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a)*
      RCN344.coordinateDegree (GenericField K) (CoordinateField (GenericField K) (F.component a).1)
        (RCN042.coordinateOfGate
          (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
            (MvPolynomial.X (F.order 0))) (hgate a))) ≤
      RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
  classical
  by_cases hA : Nonempty A
  · let a0 : A := Classical.choice hA
    have hres := reduced_resultant_ne S F a0 H G hproper
    have hTne : reducedTailSurface H G≠0 := fun hz => hproper (hz ▸ dvd_zero _)
    have hdegree : (flagPlaneResultant F.lam F.mu F.nu F.order S.G
        (reducedTailSurface H G)).natDegree ≤ RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
      rw [horder]
      exact MovingSourceProjectionFamily6814.flag_resultant_degree_le axis F.lam F.mu F.nu
        S.G (reducedTailSurface H G) surfaceFlag tailFlag hSflag hTflag hTne
    let channel := RCN104.indexedWeightedFlagPlaneChannel_of_fixedFactors F.component F.lam F.mu F.nu
      F.order F.ht F.finite F.generates hgate
      (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a))
      (flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G))
      (RCN095.flagMixed surfaceFlag tailFlag axis.flag) hres hdegree
      (fun q hq hmonic a => reduced_grouped_power_dvd S hfirst H G hcross hproper F
        ⟨q,hq,hmonic,a⟩)
    exact channel.sum_mul_cost_le
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    simp

end
end ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
