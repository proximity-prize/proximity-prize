import ProximityPrize.SubmissionLower.R6961MarkedHorizontalBasis
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix Algebra Finset
open scoped Polynomial Matrix BigOperators

variable {F E Ω : Type} [Field F] [Field E] [Algebra F E] [Field Ω]

private def atRoot (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) : E→+*Ω :=
  letI := h.toAlgebra
  (b.lift y hy).toRingHom

private theorem atRoot_base (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (c:F) :
    atRoot b h y hy (algebraMap F E c)=h c := by
  letI:=h.toAlgebra
  exact (b.lift y hy).commutes c

private theorem atRoot_value (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (v:E) :
    atRoot b h y hy v=∑ i:Fin b.dim,h (b.basis.repr v i)*y^i.val := by
  letI := h.toAlgebra
  conv_lhs => arg 2; rw [←b.basis.sum_repr v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul,atRoot_base,b.basis_eq_pow,map_pow]
  exact congrArg (h (b.basis.repr v i)*·) (congrArg (·^i.val) (b.lift_gen y hy))

variable {k K J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Algebra K E] [IsScalarTower K F E] [Fintype J] [DecidableEq J]

/-- One finite separable splitting polynomial provides an independent horizontal
evaluation matrix for the actual functions. Every row is a root-field embedding
extending an abscissa translation, which fixes the scalar parameter field. -/
theorem horizontal_frame_over {F' : Type} [Field F'] (exchange:F≃+*F')
    (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:F'[X],p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F' p.SplittingField (exchange (translateField F (algebraMap k K (offsets j)) a))) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 := by
  classical
  obtain ⟨N,sh,pick,full⟩:=section_coordinates (k:=k) b.basis v li
  let τ (i:Fin N):=(translateField F (algebraMap k K (sh i))).trans exchange
  let q (i:Fin N):=(minpoly F b.gen).map (τ i).toRingHom
  let polys:=Finset.univ.image q
  let p:=∏ f∈polys,f
  have mon (i) : (q i).Monic := (minpoly.monic b.isIntegral_gen).map _
  have irr (i) : Irreducible (q i) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (τ i))).mpr (minpoly.irreducible b.isIntegral_gen)
  have sep : p.Separable := by
    apply Polynomial.separable_prod'
    · rintro _ ha _ hb ne
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
      exact (irr i).coprime_iff_not_dvd.mpr
        (fun dv=>ne (eq_of_monic_of_associated (mon i) (mon j) ((irr i).associated_of_dvd (irr j) dv)))
    · rintro _ h
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h; exact simple.map
  let S:=p.SplittingField
  let incl:=algebraMap F' S
  have splits (i) : ((q i).map incl).Splits := by
    have dvd : q i∣p := Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem q (Finset.mem_univ i))
    exact Polynomial.Splits.of_dvd (SplittingField.splits p) ((Polynomial.map_ne_zero_iff incl.injective).mpr sep.ne_zero)
      (Polynomial.map_dvd incl dvd)
  have size (i) : Fintype.card ((q i).rootSet S)=b.dim := by
    rw [Polynomial.card_rootSet_eq_natDegree simple.map (splits i),show (q i).natDegree=(minpoly F b.gen).natDegree
      from natDegree_map_eq_of_injective (τ i).injective _,b.natDegree_minpoly]
  let idx (i) := Fintype.equivOfCardEq (show Fintype.card (Fin b.dim)=Fintype.card ((q i).rootSet S) by rw [size,Fintype.card_fin])
  let roots (i:Fin N) (j:Fin b.dim):S:=(idx i j).val
  have distinct (i) : Function.Injective (roots i) := Subtype.val_injective.comp (idx i).injective
  let emb (i:Fin N) := incl.comp (τ i).toRingHom
  have isRoot (i j) : (minpoly F b.gen).eval₂ (emb i) (roots i j)=0 := by
    have h := (Polynomial.mem_rootSet.mp (idx i j).property).2
    change (q i).eval₂ incl (roots i j)=0 at h
    rw [show q i=(minpoly F b.gen).map (τ i).toRingHom from rfl,eval₂_map] at h
    exact h
  let C:Matrix (Fin N×Fin b.dim) J F':=fun r j=>τ r.1 (b.basis.repr (v j) r.2)
  let before:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (pick i).1)) (b.basis.repr (v j) (pick i).2)
  have mapped : (C.submatrix pick _root_.id).det≠0 := by
    change (exchange.toRingHom.mapMatrix before).det≠0
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ exchange.injective).mpr full
  obtain ⟨r,det⟩:=sheet_minor C ⟨pick,mapped⟩ roots distinct
  let row (u:J):=atRoot b (emb (r u).1) (roots (r u).1 (r u).2) (isRoot (r u).1 (r u).2)
  refine ⟨p,sep,fun u=>sh (r u).1,row,fun j a=>atRoot_base ..,?_⟩
  let A:Matrix J J S:=fun i j=>∑ h:Fin b.dim, incl (C ((r i).1,h) j)*(roots (r i).1 (r i).2)^h.val
  have eqMat : (Matrix.of (fun i j:J=>row i (v j)))=A := by
    apply Matrix.ext
    intro i j
    exact atRoot_value b (emb (r i).1) (roots (r i).1 (r i).2) (isRoot (r i).1 (r i).2) (v j)
  rw [eqMat];exact det

theorem horizontal_frame (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:(Polynomial F),p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F p.SplittingField (translateField F (algebraMap k K (offsets j)) a)) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 :=
  horizontal_frame_over (RingEquiv.refl F) b simple v li

#print axioms horizontal_frame_over
#print axioms horizontal_frame
end Lower6961.MarkedEvaluation
