import ProximityPrize.SubmissionLower.Q3
import ProximityPrize.SubmissionLower.B7
import ProximityPrize.SubmissionLower.N1
namespace ProximityPrize.SubmissionLower.RCN333
open scoped Classical BigOperators
open RCN135 RCN136
open RCN086
open RCN244
open RCN074
open RCN249
open RCN251
open RCN252
open RCN255
open RCN250
open RCN247
open RCN245
open RCN106
open RCN107
open RCN108
open RCN102
open RCN103
open RCN109
open RCN112
open RCN113
open RCN264
open RCN120
open RCN243
open RCN111
open RCN093 RCN095
open RCN125
open RCN066
open RCN336
open RCN226
open RCN002 RCN011
open RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
theorem finiteDimensional_coordinateField_congr
   {Omega : Type} [Field Omega]
   {P Q : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ : P = Q) (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
   (htP : Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ : Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hfinite : letI := flagBaseAlgebra Omega P lam mu nu order htP
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)) :
   letI := flagBaseAlgebra Omega Q lam mu nu order htQ
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega Q) := by
 subst Q
 exact hfinite
theorem flagGenerators_congr
   {Omega : Type} [Field Omega]
   {P Q : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ : P = Q) (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
   (htP : Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ : Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hgen : letI := flagBaseAlgebra Omega P lam mu nu order htP
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 1))} :
         Set (CoordinateField Omega P)) = ⊤) :
   letI := flagBaseAlgebra Omega Q lam mu nu order htQ
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 2)),
       flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 1))} :
       Set (CoordinateField Omega Q)) = ⊤ := by
 subst Q
 exact hgen
theorem indexedComponentFactor_congr
   {Omega : Type} [Field Omega]
   {P Q : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ : P = Q) (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
   (htP : Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ : Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   projectedFactor Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   projectedFactor Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ := by
 subst Q
 rfl
theorem relationKernel_congr
   {Omega : Type} [Field Omega]
   {P Q : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ : P = Q) (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
   (htP : Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ : Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   relationKernel Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   relationKernel Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ := by
 subst Q
 rfl
theorem flagPlaneMap_mem_relation
   {Omega : Type} [Field Omega]
   (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
   (ht : Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A : MvPolynomial (Fin 3) Omega} (hA : A ∈ P) :
   flagPlaneMap Omega lam mu nu order A ∈
     relationKernel Omega (CoordinateField Omega P) order
       (flagEvaluation Omega P lam mu nu) ht := by
 change planeEvaluation Omega (CoordinateField Omega P) order
   (flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom lam mu nu A)) = 0
 rw [← RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation Omega P lam mu nu (flagAlgHom lam mu nu A) = 0
 rw [flagEvaluation_flag]
 change A ∈ RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rw [coordinateEvaluation_ker]
 exact hA
theorem ideal_mem_right_of_sub_mem
   {R : Type} [CommRing R] (P : Ideal R) {A B : R}
   (hA : A ∈ P) (hAB : A - B ∈ P) : B ∈ P := by
 have h := P.sub_mem hA hAB
 simpa only [sub_sub_cancel] using h
@[simp] theorem flagPlaneMap_apply
   {Omega : Type} [Field Omega] (lam mu nu : Omega)
   (order : Fin 3 ≃ Fin 3) (A : MvPolynomial (Fin 3) Omega) :
   flagPlaneMap Omega lam mu nu order A =
     planeMap Omega order (flagAlgHom lam mu nu A) := rfl
theorem reducedStage_indexedFixedFactor_groupedPowerDvd
   (S : Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (Tred : MvPolynomial (Fin 3) (GenericField K))
   (hd : S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1) - Tred)
   {A : Type} [Fintype A]
   (component : A → RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F))
   (hcomponent : Function.Injective component)
   (lam mu nu : GenericField K) (order : Fin 3 ≃ Fin 3)
   (ht : ∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite : ∀ a,
     letI := flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen : ∀ a,
     letI := flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (component a).1)) = ⊤)
   (positive : 0 < (stageSurfacePlane S lam mu nu order).natDegree)
   (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q)
   (hqMonic : q.Monic)
   (a0 : IndexedFactorFiber component lam mu nu order ht q) :
   q^(∑ a : IndexedFactorFiber component lam mu nu order ht q,
     transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) *
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1) ∣
     flagPlaneResultant lam mu nu order S.G Tred := by
 let e := regularComponentEquiv
   (H := regularitySurface (polynomialEmbedding K) S.F) hd
 let oldComponent : A → StageComponent S := fun a => e.symm (component a)
 have oldComponent_val (a : A) : (oldComponent a).1 = (component a).1 :=
   regularComponentEquiv_symm_val hd (component a)
 have holdInjective : Function.Injective oldComponent :=
   e.symm.injective.comp hcomponent
 have htold : ∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
       (MvPolynomial.X (order 0))) := by
   intro a
   rw [oldComponent_val a]
   exact ht a
 have hfiniteold : ∀ a,
     letI := flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (oldComponent a).1) := by
   intro a
   exact finiteDimensional_coordinateField_congr
     (oldComponent_val a).symm lam mu nu order (ht a) (htold a) (hfinite a)
 have hgenold : ∀ a,
     letI := flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (oldComponent a).1)) = ⊤ := by
   intro a
   exact flagGenerators_congr (oldComponent_val a).symm lam mu nu order
     (ht a) (htold a) (hgen a)
 let surface := stageSurfacePlane S lam mu nu order
 let oldTail := stageTailPlane S lam mu nu order
 let redTail := flagPlaneMap (GenericField K) lam mu nu order Tred
 letI : (Ideal.span {indexedFiberSurface q hq surface}).IsPrime := by
   exact indexedFiberSurface_span_isPrime component lam mu nu order ht
     S.irreducible_G q hq a0
 have hsurface : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
     surface ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1) := by
   intro a
   change flagPlaneMap (GenericField K) lam mu nu order S.G ∈ _
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_G_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperRed : ¬ S.G ∣ Tred := by
   intro hr
   apply hfirstProper
   have hsum := hd.add hr
   simpa only [sub_add_cancel] using hsum
 have hredTailRoot : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
     redTail ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1) := by
   intro a
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_T_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperLocal : indexedFiberTail q hq redTail ∉
     Ideal.span {indexedFiberSurface q hq surface} := by
   exact indexedFiberTail_not_mem_surface component lam mu nu order ht
     S.irreducible_G hproperRed q hq a0
 have hbar : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥ := by
   intro a
   exact indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq
     surface redTail hredTailRoot hproperLocal a
 have hplaneDvd : surface ∣ oldTail-redTail := by
   simpa only [surface,oldTail,redTail,stageSurfacePlane,stageTailPlane,
     map_sub] using map_dvd (flagPlaneMap (GenericField K) lam mu nu order) hd
 have htail : ∀ a : IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberTail q hq redTail ∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a ^
           transportedMultiplicity hd
             (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
             (component a.1) := by
   intro a
   let Q := Ideal.span {indexedFiberSurface q hq surface} ⊔
     indexedFiberRelation component lam mu nu order ht q hq a ^
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1)
   have hfactorOld : q =
       indexedComponentFactor oldComponent lam mu nu order htold a.1 := by
     calc
       q = indexedComponentFactor component lam mu nu order ht a.1 := a.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a.1 := by
         exact indexedComponentFactor_congr (oldComponent_val a.1).symm
           lam mu nu order (ht a.1) (htold a.1)
   let aold : IndexedFactorFiber oldComponent lam mu nu order htold q :=
     ⟨a.1,hfactorOld⟩
   have hold := indexedFiberTail_mem_primary S hfirstProper oldComponent
     lam mu nu order htold hfiniteold hgenold q hq aold
   have aold_val : aold.1 = a.1 := rfl
   have hcomponentVal : (oldComponent aold.1).1 = (component a.1).1 := by
     rw [aold_val,oldComponent_val]
   have hrel : indexedFiberRelation oldComponent lam mu nu order htold q hq aold =
       indexedFiberRelation component lam mu nu order ht q hq a := by
     unfold indexedFiberRelation
     exact congrArg (Ideal.map (fiberLocalizePlane q hq))
       (relationKernel_congr hcomponentVal lam mu nu order
         (htold aold.1) (ht a.1))
   have hmult : localMultiplicity S
       (canonicalLocalDVRFamily S hfirstProper) (oldComponent aold.1) =
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) := by
     change localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component aold.1)) =
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component a.1))
     rw [aold_val]
   rw [hrel,hmult] at hold
   have holdQ : indexedFiberTail q hq oldTail ∈ Q := by
     simpa only [oldTail,surface,Q] using hold
   have hfiberDvd : indexedFiberSurface q hq surface ∣
       indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail := by
     simpa only [indexedFiberSurface,indexedFiberTail,map_sub] using
       map_dvd (fiberLocalizePlane q hq) hplaneDvd
   have hdiff : indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail ∈ Q :=
     (show Ideal.span {indexedFiberSurface q hq surface} ≤ Q from le_sup_left)
       (Ideal.mem_span_singleton.mpr hfiberDvd)
   exact ideal_mem_right_of_sub_mem Q
     (A := indexedFiberTail q hq oldTail)
     (B := indexedFiberTail q hq redTail) holdQ hdiff
 have hresultant0 := flagPlaneResultant_ne lam mu nu order
   S.irreducible_G hproperRed (component a0.1) (ht a0.1) positive
 have hresultant : Polynomial.resultant surface redTail surface.natDegree
     redTail.natDegree ≠ 0 := by
   simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
     flagPlaneMap_apply] using hresultant0
 have hPbar : (indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 := by
   have hfactorA0old : q =
       indexedComponentFactor oldComponent lam mu nu order htold a0.1 := by
     calc
       q = indexedComponentFactor component lam mu nu order ht a0.1 := a0.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a0.1 := by
         exact indexedComponentFactor_congr (oldComponent_val a0.1).symm
           lam mu nu order (ht a0.1) (htold a0.1)
   let F : StageIndexedFlagFamily S A := {
     component := oldComponent
     injective := holdInjective
     lam := lam
     mu := mu
     nu := nu
     order := order
     ht := htold
     finite := hfiniteold
     generates := hgenold
     positive := positive }
   let a0old : IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q :=
     ⟨a0.1,hfactorA0old⟩
   let W : StageIndexedFactor S A F :=
     { q := q, irreducible := hq, monic := hqMonic, witness := a0old }
   have hPbar0 := stageFamily_surface_mod_ne S F W
   change (indexedFiberSurface q hq
     (stageSurfacePlane S lam mu nu order)).map
       (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 at hPbar0
   simpa only [surface] using hPbar0
 have hpow := indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   component hcomponent lam mu nu order ht hfinite hgen q hq hqMonic
   surface redTail surface.natDegree redTail.natDegree hsurface hbar
   (fun a => transportedMultiplicity hd
     (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
     (component a.1)) htail Polynomial.natDegree_map_le
       Polynomial.natDegree_map_le hresultant hPbar
 simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
   flagPlaneMap_apply] using hpow
end
end ProximityPrize.SubmissionLower.RCN333
