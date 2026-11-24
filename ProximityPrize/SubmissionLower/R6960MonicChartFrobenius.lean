import ProximityPrize.SubmissionLower.R6960MonicChartDerivationRings

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open RetainedCompression (Curve ordinate view view_y height heightCap wordDegree)
open scoped Polynomial Lower6960.MonicChart

variable {E : Type*} [Field E]
    [Algebra ChartField E] [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) ChartField E]

theorem root_finrank (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (b : PowerBasis ChartField E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0) :
    Module.finrank ChartField E=f.degreeOf ordinate := by
  let P := RetainedLinear.toSeed (view f)
  let j := algebraMap (Polynomial Scalar) ChartField
  have deg : P.natDegree=f.degreeOf ordinate := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have prim := pir.isPrimitive (by omega : P.natDegree≠0)
  have iq : Irreducible (P.map j) := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen (P.map j)=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd := minpoly.dvd ChartField b.gen rq
  have assoc := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : (P.map j).natDegree=(minpoly ChartField b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd assoc.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  rw [b.finrank,←b.natDegree_minpoly,←size,
    natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) ChartField),deg]

variable [DecidableEq ChartField] [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) ChartField E]

private theorem overlap_zero [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (d : Derivation ℤ ChartField ChartField) (D : Derivation ℤ E E)
    (share : ∀ a,D (algebraMap ChartField E a)=algebraMap ChartField E (d a))
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,d (RatFunc.C a)=RatFunc.C b)
    (on_X : d RatFunc.X=1 ∨ d RatFunc.X=0)
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis ChartField E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap ChartField E RatFunc.X)^K1.p*x+z^K1.p) : D x=0 := by
  obtain ⟨df,hf⟩ := finite_derivation d on_scalars on_X
  obtain ⟨di,hi'⟩ := infinity_derivation d on_scalars on_X
  let : Differential E := ⟨D⟩
  let : Differential (Polynomial Scalar) := ⟨df⟩
  let : Differential (Infinity Scalar) := ⟨di⟩
  let : DifferentialAlgebra (Polynomial Scalar) E := ⟨fun a=>by
    change D (algebraMap (Polynomial Scalar) E a)=algebraMap (Polynomial Scalar) E (df a)
    rw [IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField E,share,hf]
    exact (IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField E (df a)).symm⟩
  let : DifferentialAlgebra (Infinity Scalar) E := ⟨fun a=>by
    change D (algebraMap (Infinity Scalar) E a)=algebraMap (Infinity Scalar) E (di a)
    rw [IsScalarTower.algebraMap_apply (Infinity Scalar) ChartField E,share,hi']
    exact (IsScalarTower.algebraMap_apply (Infinity Scalar) ChartField E (di a)).symm⟩
  exact actual_coboundary_zero f ir lo hi bounded b root x y z fx iy overlap

/-- An integral Frobenius overlap for the actual bounded projected
factor has a p-th root in its own root field. Both underlying coordinate
partials restrict to the finite and infinity charts used in the pole proof. -/
theorem actual_coboundary_pth_root
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis ChartField E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap ChartField E RatFunc.X)^K1.p*x+z^K1.p) :
    ∃ w : E,w^K1.p=x := by
  let : IsFractionRing (Plane L) ChartField := plane_fractionRing
  let : FiniteDimensional ChartField E := b.finite
  let incl : L→+*ChartField := RatFunc.C.comp ((algebraMap (Polynomial L) Scalar).comp C)
  let : Fact K1.p.Prime := ⟨KoalaBear.is_prime⟩
  let : CharP E K1.p := charP_of_injective_ringHom ((algebraMap ChartField E).comp incl).injective K1.p
  have small : Module.finrank ChartField E<K1.p := by
    rw [root_finrank f ir lo b root]
    exact hi.trans (by decide +kernel)
  have : Algebra.IsSeparable ChartField E := by
    constructor
    intro a
    have integ : IsIntegral ChartField a := Algebra.IsIntegral.isIntegral a
    let : CharP ChartField K1.p := charP_of_injective_ringHom incl.injective K1.p
    exact (separable_iff_derivative_ne_zero (minpoly.irreducible integ)).mpr
      (CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char K1.p _ (minpoly.natDegree_pos integ)
        ((minpoly.natDegree_le a).trans_lt small))
  have : Algebra.FormallyEtale ChartField E := Algebra.FormallyEtale.of_isSeparable ChartField E
  obtain ⟨dx,dz,hx,hz,xx,zx,xs,zs⟩ := base_coordinates
  obtain ⟨Dx,ex⟩ := ChartDerivations.extend (B:=E) dx
  obtain ⟨Dz,ez⟩ := ChartDerivations.extend (B:=E) dz
  exact PlaneConstants.root_field_constant K1.p dx dz Dx Dz hx hz ex ez small x
    (overlap_zero dx Dx ex xs (Or.inl xx) f ir lo hi bounded b root x y z fx iy overlap)
    (overlap_zero dz Dz ez zs (Or.inr zx) f ir lo hi bounded b root x y z fx iy overlap)

/-- The integral roots of both chart sections have the original twist
rather than its p-th power. -/
theorem actual_coboundary_descent
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis ChartField E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap ChartField E RatFunc.X)^K1.p*x+z^K1.p) :
    ∃ w : E,w^K1.p=x ∧ IsIntegral (Polynomial Scalar) w ∧
      IsIntegral (Infinity Scalar) (algebraMap ChartField E RatFunc.X*w+z) ∧
      (algebraMap ChartField E RatFunc.X*w+z)^K1.p=y := by
  let incl : L→+*ChartField := RatFunc.C.comp ((algebraMap (Polynomial L) Scalar).comp C)
  let : Fact K1.p.Prime := ⟨KoalaBear.is_prime⟩
  let : CharP E K1.p := charP_of_injective_ringHom ((algebraMap ChartField E).comp incl).injective K1.p
  obtain ⟨w,hw⟩ := actual_coboundary_pth_root f ir lo hi bounded b root x y z fx iy overlap
  have ep : 0<K1.p := KoalaBear.is_prime.pos
  have iy' : (algebraMap ChartField E RatFunc.X*w+z)^K1.p=y := by
    rw [add_pow_char,mul_pow,hw,←overlap]
  exact ⟨w,hw,IsIntegral.of_pow ep (hw.symm ▸ fx),IsIntegral.of_pow ep (iy'.symm ▸ iy),iy'⟩

#print axioms actual_coboundary_pth_root
#print axioms actual_coboundary_descent
end
end Lower6960.MonicChart
