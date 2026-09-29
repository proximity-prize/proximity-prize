import ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814

/-! The outer packet can share one ordinary flag frame across all its
geometric Stages. Both coefficients are chosen in the polynomial image;
the finitely many forbidden directional coefficients are excluded at once. -/
namespace ProximityPrize.SubmissionLower.MovingSourceOuterCommonFrame6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044
open RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370 RCN351 RCN037 RCN038
variable {Omega J : Type} [Field Omega] [IsAlgClosed Omega] [Fintype J]
local notation "Poly" => MvPolynomial (Fin 3) Omega

theorem exists_common_outer_frames
    (G T H : J → Poly)
    (base : ∀ i, ∀ C : RegularComponent Omega (G i) (T i) (H i), SeparableLiteralCoordinate C.1)
    (hactive : ∀ i, ∀ C : RegularComponent Omega (G i) (T i) (H i),
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0 ∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
    (hSderiv : ∀ i, MvPolynomial.pderiv (1 : Fin 3) (G i)≠0)
    (S : Set Omega) (hS : S.Infinite) :
    ∃ lam mu : Omega, lam∈S ∧ mu∈S ∧
      ∃ data : ∀ i, AdaptiveNestedProjectionDataActive (base i) (hactive i) (hSderiv i),
        ∀ i, (data i).lam=lam ∧ (data i).mu=mu := by
 let Family := (i : J) × RegularComponent Omega (G i) (T i) (H i)
 classical
 let E:Family → Type:=
   fun C => CoordinateField Omega C.2.1
 let rY:∀ C,E C:=fun C => coordinate Omega C.2.1 0
 let z:∀ C,E C:=fun C => coordinate Omega C.2.1 2
 let W:∀ C,Finset (Place Omega (E C)):=
   fun C => literalRelevantPlaces (base C.1 C.2)
 let baseC:∀ C,SeparableCoordinate Omega (E C):=
   fun C => literalToSeparableCoordinate (base C.1 C.2)
 obtain ⟨lam,hlamS,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive_in E rY z W
     S hS baseC (fun C => hactive C.1 C.2)
 let U:∀ C:Family,
     CoordinateField Omega C.2.1:=fun C => affineU Omega C.2.1 lam
 have hUgate:∀ C:Family,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.2.1):=
           (elementEmbedding Omega (CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.2.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.2.1):=
           (elementEmbedding Omega (CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.2.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀ C:Family,
     Coordinate Omega (CoordinateField Omega C.2.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:Family,
     coordinateValue Omega (CoordinateField Omega C.2.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:Family)
     (v:Place Omega (CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.2.1 2)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C.1 C.2)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 0
     have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 2
     have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.2.1 2)=
         v.val (coordinate Omega C.2.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C) ≤ 1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.2.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀ C:Family,
     D Omega (CoordinateField Omega C.2.1) (coordinate Omega C.2.1 1)≠0∨
       D Omega (CoordinateField Omega C.2.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀ C,E C:=fun C => coordinate Omega C.2.1 1
 let bad (i : J) : Set Omega := {mu | MvPolynomial.pderiv (0 : Fin 3) (G i)-
   MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) (G i)=0}
 have hbad : (⋃ i, bad i).Finite := by
   apply Set.finite_iUnion
   intro i
   have hs : (bad i).Subsingleton := by
     intro a ha b hb
     exact directional_bad_coefficient_subsingleton (G i) (hSderiv i) ha hb
   exact hs.finite
 obtain ⟨mu,hmuS,hmu0,hmu⟩ :=
   exists_common_exact_finite_separable_affine_adaptive_in
     E rS U W (S \ ⋃ i, bad i) (hS.sdiff hbad) baseC hactiveV
 have hmudir (i : J) : MvPolynomial.pderiv (0 : Fin 3) (G i)-
     MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) (G i)≠0 := by
   intro hh
   exact hmuS.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)
 let V:∀ C:Family,
     CoordinateField Omega C.2.1:=
   fun C => coordinate Omega C.2.1 1+mu • U C
 let hV:∀ C:Family,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:Family,
     Coordinate Omega (CoordinateField Omega C.2.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.2.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:Family,
     coordinateValue Omega (CoordinateField Omega C.2.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.2.1) (V C) (hV C)
 have hvPole:∀ (C:Family)
     (v:Place Omega (CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C.1 C.2)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C) ≤ 1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.2.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:Family,
     Transcendental Omega (affineV Omega C.2.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.2.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:Family):
     elementEmbedding Omega (CoordinateField Omega C.2.1)
         (affineV Omega C.2.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.2.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])

 let data (i : J) : AdaptiveNestedProjectionDataActive (base i) (hactive i) (hSderiv i) := {
   lam := lam
   lam_ne := hlam0
   mu := mu
   mu_ne := hmu0
   uProjection := fun C => uProjection ⟨i,C⟩
   allProjection := fun C => vProjection ⟨i,C⟩
   uGate := fun C => hUgate ⟨i,C⟩
   uTranscendental := fun C => (hlam ⟨i,C⟩).choose
   allAffineTranscendental := fun C => hVAff ⟨i,C⟩
   allFinite := by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.1
   allSeparable := by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.2.1
   uValue := fun C => huValue ⟨i,C⟩
   allValue := by
     intro C
     rw [hvValue ⟨i,C⟩]
     simp only [V,U,affineU,affineV,smul_add,smul_smul,add_assoc]
   allTranscendental := by
     intro C
     rw [hvValue ⟨i,C⟩]
     exact hV ⟨i,C⟩
   uPole := by
     intro C nu
     rw [huValue ⟨i,C⟩]
     exact huPole ⟨i,C⟩ nu
   allPole := by
     intro C nu
     rw [hvValue ⟨i,C⟩,hvPole ⟨i,C⟩ nu,huPole ⟨i,C⟩ nu]
   directional := hmudir i }
 exact ⟨lam,mu,hlamS,hmuS.1,data,fun _ => ⟨rfl,rfl⟩⟩

#print axioms exists_common_outer_frames
end
end ProximityPrize.SubmissionLower.MovingSourceOuterCommonFrame6814
