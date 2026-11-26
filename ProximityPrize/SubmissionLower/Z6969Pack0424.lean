import ProximityPrize.SubmissionLower.Z6969Pack0420
import ProximityPrize.SubmissionLower.Z6969Pack0422
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes

set_option Elab.async false

-- Source: Research6969.NearFactorPrice
section Z6969Source0429
set_option autoImplicit true
-- Adapted from the promoted lower-track proof at 2a99570fe043b6dabeac1e52f807826c8859d717.
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
namespace Research6969.Near6969FactorPrice
open Polynomial Finset
open K1 (K I p)
open K1_14 (L liftPoly)
open Lower6960
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter view view_y view_z
  MarkedFiber no_zero_degree constant_price specialize height evaluate_view evaluate
  aggregate box_iff abscissa_le_height pure_node_price_6969)
open Lower6960.Near6969Compression (escape heightCap proper_cut_price)
open RetainedLinear (GeometricallyLinear)
open CurvatureSquares (Ordinate zView xView ordEval)
open scoped Polynomial
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000

abbrev agreement : ℕ := 179740
abbrev wordDegree : ℕ := 133605
abbrev rate := MarkedEvaluation.rate

theorem rate_mono : Monotone rate := by
  intro e n le
  unfold rate MarkedEvaluation.rate
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 le) _) (Nat.sub_le_sub_right le 1))
    (Nat.mul_le_mul_left 2 le)) 1

private theorem vote_scale : CurvatureVotes.VoteScale agreement wordDegree 18 :=
  Or.inl (by decide +kernel)

private theorem word_roots {U : Finset K} (s : K → K[X]) (label : K → L) (Q : Ordinate)
    (H : ∀ γ∈U, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    ∀ γ∈U, ordEval (label γ) ((s γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (label γ))) (liftPoly (s γ))=0
  rw [← eval_map]
  exact (H γ hγ).root

theorem factor {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : n<64)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈T, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    T.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases T.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 24≤rate n := (by decide : 24≤rate 3).trans (rate_mono lo)
  have vRate : 18≤rate n := (by decide : 18≤24).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn label (T : Set K) := inject.injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (s x)) (T:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q T label (fun x=>liftPoly (s x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots s label Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) label inj
      (by decide) vote_scale Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e wordDegree < height wordDegree q
  · let param (j : T) := label j.val
    let root (j : T) := liftPoly (s j.val)
    have deg (j : T) : (root j).natDegree≤wordDegree := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : T) : evaluate (param j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape param root wordDegree (by decide) deg q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price T label (fun j=>liftPoly (s j))
      inj q G qp nondiv pos y z gy gz (fun j hj=>rootsF ⟨j,hj⟩)
      (fun j hj=>rootsG ⟨j,hj⟩)
    have ceiling : 14*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using ((by decide : 28≤rate 3).trans (rate_mono lo))
      have three : 3≤e := by omega
      have ratio : 14*e≤rate e :=
        (by decide +kernel : ∀ i : Fin 64, 3 ≤ i.val → 14*i.val ≤ rate i.val)
          ⟨_,degree.trans_lt hi⟩ three
      exact ratio.trans (rate_mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q wordDegree
        rw [RingEquiv.apply_symm_apply] at a
        exact (Nat.mul_le_mul_left 2 (a.trans wt)).trans_lt (by rw [two]; decide)
      have count := CurvatureSquares.degree_two_count words (algebraMap K L) label inj
        (by decide) vote_scale Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have mark' (j : K) (hj : j ∈ T) : MarkedFiber (view q) (label j) (liftPoly (s j)) := by
      simpa only [q,RingEquiv.apply_symm_apply] using mark j hj
    have charge : T.card≤rate (q.degreeOf ordinate)*(q.degreeOf parameter)+
        (q.degreeOf ordinate-1)*q.degreeOf ordinate := by
      by_cases pure : GeometricallyLinear (view q)
      · have irr : Irreducible (view q) := (MulEquiv.irreducible_iff view).mpr qp
        have pos' : 0<(view q).natDegree := by rw [view_y];omega
        have nodes := RetainedLinear.pure_of_geometrically_linear w (view q) irr pos' pure
        have bound := pure_node_price_6969 (w:=w) (s:=s) (T:=T)
          ⟨words.distinct, fun j hj=>(words.degree j hj).trans (by decide : wordDegree≤164806), words.hits⟩ label inj (view q) irr pos' nodes mark'
        rw [view_z] at bound
        exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_mono three)))
          (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
      · exact MarkedEvaluation.nonlinear_near6969 wordDegree T label inject (fun j=>liftPoly (s j)) q qp three
          (Or.inr ⟨y.symm ▸ degree.trans_lt hi, by decide⟩) (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt) pure mark'
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (rate_mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))

/-- The factored tariff for any integral retained ordinate, with no
dependency on how the marks or the integral equation were produced. -/
theorem price {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    (P : Ordinate) (pn : P≠0) (n B : ℕ) (lo : 3≤n) (hi : n<64)
    (degree : P.natDegree≤n) (bound : (zView P).natDegree≤B)
    (marks : ∀ γ∈T, MarkedFiber P (label γ) (liftPoly (s γ))) :
    T.card≤rate n*B+(n-1)*P.natDegree := by
  have chosen := aggregate P T label (fun j=>liftPoly (s j)) (rate n) (n-1) pn marks (by
    intro Q ir dvd U sub mark
    have W : Word agreement wordDegree w s U :=
      ⟨words.distinct.mono sub,fun j hj=>words.degree j (sub hj),fun j hj=>words.hits j (sub hj)⟩
    exact factor W label inject ir n lo hi ((natDegree_le_of_dvd dvd pn).trans degree) mark)
  exact chosen.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ bound) _)

end Research6969.Near6969FactorPrice
end Z6969Source0429

-- Source: Research6969.FarChart
section Z6969Source0430
set_option autoImplicit true
set_option Elab.async false
section Merged_R6960MonicChartActual

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap abscissa_coeff_height)
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)

private theorem width_at_cutoff (e d : ℕ) (pos : 0<e) :
    resultantWidth e (heightCap e d) d=(3*e-1)*(e-1)*d := by
  have mul : d*e≤heightCap e d := by
    unfold heightCap
    rw [mul_comm d e]
    exact Nat.mul_le_mul_right d (by omega)
  have eq := resultantWidth_eq (e:=e) (d:=d) pos mul
  have identity : (2*e-1)*heightCap e d=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
    unfold heightCap
    rw [h,show 2*(1+k)-1=2*k+1 by omega,show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  omega

/-- For the actual bounded projected factor, the overlap of the finite
and infinity chart coefficients has zero derivative. The only overlap
input is their Frobenius relation in the root field. -/
theorem actual_coboundary_zero_6969 {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra (Polynomial Scalar) E]
    [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra (Polynomial Scalar) E] [DifferentialAlgebra (Infinity Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap (RatFunc Scalar) E RatFunc.X)^K1.p*x+z^K1.p) :
    x′=0 := by
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  letI : CharP Scalar K1.p := charP_of_injective_ringHom seed.injective K1.p
  let inE : Scalar→+*E := (algebraMap (RatFunc Scalar) E).comp RatFunc.C
  letI : CharP E K1.p := charP_of_injective_ringHom inE.injective K1.p
  let P := RetainedLinear.toSeed (view f)
  let e := f.degreeOf ordinate
  let H := heightCap e 164806
  have deg : P.natDegree=e := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have e2 : 2≤P.natDegree := by omega
  have ep : 0<P.natDegree := by omega
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have tame : (P.natDegree:Scalar)≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff Scalar K1.p P.natDegree).mp zero
    exact ep.ne' (Nat.eq_zero_of_dvd_of_lt dvd (deg.symm ▸ hi.trans (by decide)))
  have coefficient (j : ℕ) : (P.coeff j).natDegree=((view f).coeff j).natDegree := by
    unfold P RetainedLinear.toSeed
    simp only [coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
  have weights (j : ℕ) (jle : j≤P.natDegree) :
      (P.coeff j).natDegree+164806*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm 164806]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f 164806 j zero).trans bounded
  have Hfit : 164806*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H 164806 := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H 164806 ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=164806) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H 164806<K1.p := by
    rw [deg,width_at_cutoff e 164806 (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right 164806
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 (by omega : e≤47)) 1)
       (Nat.sub_le_sub_right (by omega : e≤47) 1)))).trans_lt (by decide +kernel)
  have tameA : (P.natDegree:(Polynomial Scalar))≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (Polynomial.C : Scalar→+*(Polynomial Scalar)) Polynomial.C_injective).mpr tame
  have dp := derivative_degree P ep tameA
  have der : P.derivative≠0 := by intro zero; rw [zero,natDegree_zero] at dp; omega
  have resNZ : paddedRes P≠0 := Polynomial.resultant_derivative_ne_zero_of_irreducible P pir der
  have prim := pir.isPrimitive ep.ne'
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have iq : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rq
  have associated := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd associated.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  have dimension : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (size.trans b.natDegree_minpoly)
  exact common_coboundary_zero_generic b P H 164806 K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

end
end Lower6960.MonicChart

end Merged_R6960MonicChartActual

section Merged_R6960MonicChartFrobenius
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open RetainedCompression (Curve ordinate view view_y height heightCap)
open scoped Polynomial Lower6960.MonicChart
variable {E : Type*} [Field E]
    [Algebra ChartField E] [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) ChartField E]
variable [DecidableEq ChartField] [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) ChartField E]
private theorem overlap_zero [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (d : Derivation ℤ ChartField ChartField) (D : Derivation ℤ E E)
    (share : ∀ a,D (algebraMap ChartField E a)=algebraMap ChartField E (d a))
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,d (RatFunc.C a)=RatFunc.C b)
    (on_X : d RatFunc.X=1 ∨ d RatFunc.X=0)
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
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
  exact actual_coboundary_zero_6969 f ir lo hi bounded b root x y z fx iy overlap
theorem actual_coboundary_pth_root_6969
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
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
end
end Lower6960.MonicChart

end Merged_R6960MonicChartFrobenius

section Merged_R6960MonicFourChartDescent
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicFourChartDescent
noncomputable section
open Polynomial
open K1_14 (L)
open MonicChart (ChartField Scalar Infinity)
open ChartSections (Chart)
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]

theorem descend_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (u : Chart → E) (c : E)
    (h : Correction (a*K1.p) (b*K1.p) (fun s=>u s ^ K1.p) c) :
    ∃ d : E, d^K1.p=c ∧ Correction a b u d := by
  classical
  let : Algebra (Polynomial Scalar) E := ((algebraMap ChartField E).comp (algebraMap (Polynomial Scalar) ChartField)).toAlgebra
  let : IsScalarTower (Polynomial Scalar) ChartField E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial Scalar)) (S:=ChartField) (A:=E) fun _=>rfl
  let : Algebra (Infinity Scalar) E :=
    ((algebraMap ChartField E).comp (algebraMap (Infinity Scalar) ChartField)).toAlgebra
  let : IsScalarTower (Infinity Scalar) ChartField E :=
    IsScalarTower.of_algebraMap_eq (R:=Infinity Scalar) (S:=ChartField) (A:=E) fun _=>rfl
  let p := K1.p
  let : Fact p.Prime := ⟨KoalaBear.is_prime⟩
  let : CharP E p := charP_of_injective_ringHom ((algebraMap ChartField E).comp constants).injective p
  let Fr := frobenius E p
  have subpow (r s : E) : (r-s)^p=r^p-s^p := map_sub Fr r s
  let Xval := algebraMap ChartField E RatFunc.X
  have Xnz : Xval≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr RatFunc.X_ne_zero
  let x := u (false,false)^p-c
  let y := Xval^p*(u (true,false)^p-c)
  have finite : IsIntegral (Polynomial Scalar) x := by
    apply integral_of_inclusion (false,false) (IsFractionRing.injective _ _) finite_inclusion
    simpa only [frame,Bool.false_eq_true,ite_false,one_pow,one_mul,map_one] using h (false,false)
  have infinity_high : IsIntegral (Infinity Scalar) (Xval^(a*p)*(u (true,false)^p-c)) := by
    apply integral_of_inclusion (true,false)
      (ValuationSubring.algebraMap_injective _ ChartField) infinity_inclusion
    simpa only [frame,ite_true,Bool.false_eq_true,ite_false,one_pow,mul_one,map_pow] using h (true,false)
  have inv_coord : IsIntegral (Infinity Scalar) (Xval⁻¹) := by
    let t := MonicChart.inftyRingEval Scalar (Polynomial.X (R:=Scalar))
    have integral : IsIntegral (Infinity Scalar) (algebraMap (Infinity Scalar) E t) := isIntegral_algebraMap
    rw [IsScalarTower.algebraMap_apply (Infinity Scalar) ChartField E] at integral
    change IsIntegral (Infinity Scalar) (algebraMap ChartField E ((t:Infinity Scalar):ChartField)) at integral
    rwa [MonicChart.mapped_X_infty,map_inv₀] at integral
  have cancel : (Xval⁻¹)^((a-1)*p)*Xval^(a*p)=Xval^p := by
    have split : (a-1)*p+p=a*p := calc
      _ = (a-1)*p+1*p := by rw [Nat.one_mul]
      _ = a*p := by rw [←Nat.add_mul,Nat.sub_add_cancel ha]
    rw [←split,pow_add,←mul_assoc,←mul_pow,inv_mul_cancel₀ Xnz,one_pow,one_mul]
  have infinity : IsIntegral (Infinity Scalar) y := by
    have m := (inv_coord.pow ((a-1)*p)).mul infinity_high
    rwa [←mul_assoc,cancel] at m
  have overlap : y=Xval^p*x+(Xval*(u (true,false)-u (false,false)))^p := by
    rw [mul_pow,subpow]
    dsimp only [x,y]
    ring
  have root_in_tower : aeval basis.gen (RetainedLinear.toSeed (view f))=0 := by
    rw [aeval_map_algebraMap] at root
    exact root
  obtain ⟨w,hw⟩ := MonicChart.actual_coboundary_pth_root_6969 f ir lo hi bounded basis root_in_tower
    x y (Xval*(u (true,false)-u (false,false))) finite infinity overlap
  let d := u (false,false)-w
  have dp : d^p=c := by
    rw [show d=u (false,false)-w from rfl,subpow,hw]
    dsimp only [x]
    ring
  refine ⟨d,dp,?_⟩
  intro s
  apply IsIntegral.of_pow KoalaBear.is_prime.pos (n:=p)
  rw [mul_pow,subpow,dp,←map_pow,←frame_scale]
  exact h s
theorem descend_iterate_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (u : Chart → E) (n : ℕ) (c : E)
    (h : Correction (a*K1.p^n) (b*K1.p^n) (fun s=>u s ^ (K1.p^n)) c) :
    ∃ d : E, d^(K1.p^n)=c ∧ Correction a b u d := by
  induction n generalizing c with
  | zero => exact ⟨c,by simp,by simpa using h⟩
  | succ n ih =>
    have next : Correction ((a*K1.p^n)*K1.p) ((b*K1.p^n)*K1.p)
        (fun s=>(u s ^ (K1.p^n))^K1.p) c := by
      rw [pow_succ K1.p n,←Nat.mul_assoc,←Nat.mul_assoc] at h
      have powers : (fun s : Chart=>u s ^ (K1.p^n*K1.p)) =
          (fun s=> (u s ^ (K1.p^n))^K1.p) := funext fun s=>pow_mul (u s) _ _
      rwa [powers] at h
    obtain ⟨v,hv,hv'⟩ := descend_6969 f ir lo hi bounded basis root (a*K1.p^n) (b*K1.p^n)
      (Nat.mul_pos ha (pow_pos KoalaBear.is_prime.pos _)) (fun s=>u s ^ (K1.p^n)) c next
    obtain ⟨d,hd,hd'⟩ := ih v hv'
    exact ⟨d,by rw [pow_succ K1.p n,pow_mul,hd,hv],hd'⟩
end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent
end Z6969Source0430

-- Source: Research6969.FarSurface
section Z6969Source0431
set_option autoImplicit true
set_option Elab.async false
section Merged_R6960RetainedChartGluing
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedChartGluing
open ChartSections (Chart)
open MonicChart MonicFourChartDescent MonicScalarCorrection ChartGlobalTests
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
open Lower6960.MonicFourChartDescent (finite_inclusion infinity_inclusion)
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem common_correction_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo hi basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate_6969 f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩
theorem split_cocycle_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (g : Chart→Chart→E)
    (add : ∀ s t r, g s t+g t r=g s r)
    (regular : ∀ s t, IsIntegral (MonicChartLaurent.overlapRing s t)
      (algebraMap ChartField E (frame a b s)*g s t)) :
    ∃ w : Chart→E, (∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*w s)) ∧
      ∀ s t, g s t=w s-w t := by
  let u (s : Chart):=g s (false,false)
  have diff (s t) : u s-u t=g s t := sub_eq_of_eq_add (add s t (false,false)).symm
  obtain ⟨c,hc⟩:=common_correction_6969 f ir lo hi bounded basis root a b ha hb u
    (fun s t=> by rw [diff]; exact regular s t)
  exact ⟨fun s=>u s-c,hc,fun s t=>by rw [←diff]; ring⟩
end Lower6960.RetainedChartGluing

end
end Merged_R6960RetainedChartGluing

section Merged_R6960RetainedLineRestriction
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedLineRestriction
open MonicFourChartDescent ChartSections MonicChart RetainedChartGluing
open ChartGlobalTests (frame_ne)
open MonicChartLaurent (overlapRing)
open MonicChartProbes (planeMap planeMap_injective)
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
private theorem lines_ne (x z : L) : lines x z≠0 := by
  let m := planeMap (false,false)
  have a : (Polynomial.X (R:=(Polynomial L)))-C (C x)≠0 := X_sub_C_ne_zero _
  have b : (C (Polynomial.X (R:=L)) : (Polynomial (Polynomial L)))-C (C z)≠0 := by
    rw [←map_sub]; exact C_ne_zero.mpr (X_sub_C_ne_zero _)
  have good := (map_ne_zero_iff m (planeMap_injective _)).mpr (mul_ne_zero a b)
  simpa only [m,map_mul,map_sub,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_scalar,
    MonicChartProbes.planeMap_abscissa,chartCoordinate,Bool.false_eq_true,ite_false,lines] using good
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem split_of_split_on_lines_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (g : Chart→Chart→E) (add : ∀ s t r, g s t+g t r=g s r)
    (v : Chart→E) (localV : ∀ s, IsIntegral (baseChart s) (v s))
    (restricted : ∀ s t, ∃ r : E, IsIntegral (overlapRing s t) r ∧
      g s t-(v s-v t)=algebraMap ChartField E (lines x z / frame 1 1 s)*r) :
    ∃ w : Chart→E, (∀ s,IsIntegral (baseChart s) (w s)) ∧ ∀ s t,g s t=w s-w t := by
  let ι:=algebraMap ChartField E
  let P:=ι (lines x z)
  have pn : P≠0 := (map_ne_zero_iff ι ι.injective).mpr (lines_ne x z)
  let h (s t:Chart):=(g s t-(v s-v t))/P
  have coc (s t r) : h s t+h t r=h s r := by
    dsimp [h]
    rw [←add_div]
    congr 1
    linear_combination add s t r
  have twist (s t) : IsIntegral (overlapRing s t) (ι (frame 1 1 s)*h s t) := by
    obtain ⟨r,hr,eq⟩:=restricted s t
    have nz := (map_ne_zero_iff ι ι.injective).mpr (frame_ne 1 1 s)
    have recover : ι (frame 1 1 s)*h s t=r := by
      dsimp only [h]; rw [eq,map_div₀]
      change ι (frame 1 1 s)*(P/ι (frame 1 1 s)*r/P)=r
      field_simp
    rwa [recover]
  obtain ⟨w,localW,diff⟩:=split_cocycle_6969 f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
  refine ⟨fun s=>v s+P*w s,fun s=>(localV s).add ?_,fun s t=>?_⟩
  · have integral : IsIntegral (baseChart s) (ι (lines x z/frame 1 1 s)) :=
      isIntegral_algebraMap (x:=(⟨_, local_equation x z s⟩ : baseChart s))
    have eq : ι (lines x z / frame 1 1 s)*(ι (frame 1 1 s)*w s)=P*w s := by
      rw [map_div₀,←mul_assoc,div_mul_cancel₀ _ ((map_ne_zero_iff ι ι.injective).mpr (frame_ne _ _ _))]
    exact eq ▸ integral.mul (localW s)
  · have eq := (div_eq_iff pn).mp (diff s t)
    linear_combination eq
end Lower6960.RetainedLineRestriction

end
end Merged_R6960RetainedLineRestriction

section Merged_R6960RetainedPairedResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedRestrictionTorus
open MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

private theorem base_x (s : Chart) (x:L) : algebraMap (baseChart s) E (xcut s x) =
    ι (divisor false x)/ι (localFrame s false) := by
  change ι ((xcut s x):ChartField)=_
  rw [xcut_value,map_div₀]
private theorem base_z (s : Chart) (z:L) : algebraMap (baseChart s) E (zcut s z) =
    ι (divisor true z)/ι (localFrame s true) := by
  change ι ((zcut s z):ChartField)=_
  rw [zcut_value,map_div₀]

private theorem glue (s : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (u v:E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v) (h:Matched x z u v) :
    ∃ y:E,IsIntegral (baseChart s) y ∧ Congruent false x u y ∧ Congruent true z v y := by
  obtain ⟨a,b,ia,ib,eq⟩:=h
  have fn (j : Bool) : (ι (localFrame s j) : E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s j)
  have m:=lift_on_chart s x z nx nz u v hu hv ⟨ι (localFrame s false)*a,ι (localFrame s true)*b,
    (frame_integral s false).1.mul ia,(frame_integral s true).1.mul ib,by
      rw [base_x,base_z,eq]; field_simp [fn]⟩
  obtain ⟨y,a',b',hy,ia',ib',dx,dz⟩:=m
  refine ⟨y,hy,⟨ι ((localFrame s false)⁻¹)*a',
    (frame_integral s false).2.mul (order_mono (base_torus s) ia'),?_⟩,Congruent.symm
      ⟨ι ((localFrame s true)⁻¹)*b',(frame_integral s true).2.mul (order_mono (base_torus s) ib'),?_⟩⟩
  · rw [dx,base_x,map_inv₀,div_eq_mul_inv,mul_assoc]
  · rw [dz,base_z,map_inv₀,div_eq_mul_inv,mul_assoc]

private theorem product_residue [FiniteDimensional ChartField E]
    (s t : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (v:E)
    (reg : IsIntegral (overlapRing s t) v) (vx : Congruent false x v 0) (vz : Congruent true z v 0) :
    ∃ r:E, IsIntegral (overlapRing s t) r ∧
      v=ι (RetainedLineRestriction.lines x z / frame 1 1 s)*r := by
  obtain ⟨a,ia,ea⟩:=vx; obtain ⟨b,ib,eb⟩:=vz
  rw [sub_zero] at ea eb
  let Xv:=ι (divisor false x)
  let Zv:=ι (divisor true z)
  let P:=ι (localFrame s false)
  let Q:=ι (localFrame s true)
  have mne (p:ChartField) (pn:p≠0) : (ι p:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr pn
  have xn : Xv≠0:=mne _ (divisor_ne false x)
  have zn : Zv≠0:=mne _ (divisor_ne true z)
  have pn : P≠0:=mne _ (localFrame_ne s false)
  have qn : Q≠0:=mne _ (localFrame_ne s true)
  let r:=P*Q*v/(Xv*Zv)
  have xeq : algebraMap (baseChart s) E (xcut s x)*r=Q*b := by
    rw [base_x]; change Xv/P*(P*Q*v/(Xv*Zv))=Q*b
    change v=Zv*b at eb
    rw [eb]; field_simp
  have zeq : algebraMap (baseChart s) E (zcut s z)*r=P*a := by
    rw [base_z]; change Zv/Q*(P*Q*v/(Xv*Zv))=P*a
    change v=Xv*a at ea
    rw [ea]; field_simp
  have both : algebraMap (baseChart s) E (xcut s x*zcut s z)*r=v := by
    rw [map_mul,base_x,base_z]; change Xv/P*(Zv/Q)*(P*Q*v/(Xv*Zv))=v
    field_simp
  refine ⟨r,cancel_both s t x z nx nz r (both ▸ reg)
    (xeq ▸ (frame_integral s true).1.mul ib) (zeq ▸ (frame_integral s false).1.mul ia),?_⟩
  have e : frame 1 1 s=localFrame s false*localFrame s true := by simp [frame,localFrame,axisBit,coordinate]
  rw [e,map_div₀,map_mul]
  rw [RetainedLineRestriction.lines,map_mul]
  change v=(Xv*Zv)/(P*Q)*(P*Q*v/(Xv*Zv))
  field_simp

private theorem lift_axis (j : Bool) (c:L) (nc:c≠0) (u:Chart→E) (v:Bool→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (data : LineData j c u v) (s:Chart) :
    ∃ w:E,IsIntegral (baseChart s) w ∧ Congruent j c (u s-(u (false,false)-v false)) w := by
  let bit:=axisBit s (!j)
  let t:=reference j bit
  have parallel : axisBit s (!j)=axisBit t (!j) := by cases j <;> simp [bit,t,reference,axisBit]
  have r := (reg s t).add (order_mono (chart_cover s t) (data.1 bit))
  obtain ⟨w,hw,cw⟩:=line_representative j c nc s t parallel (u s-u t+v bit) r
  refine ⟨w,hw,Congruent.trans ?_ cw⟩
  have shared : Congruent j c (u (false,false)-u t) (v false-v bit) := by
    cases h:bit with
    | false => have t0:t=(false,false) := by cases j <;> simp [t,h,reference]
               rw [t0,sub_self,sub_self]; exact Congruent.refl j c 0
    | true => simpa only [t,h] using data.2
  obtain ⟨d,id,eq⟩:=shared.symm
  exact ⟨d,id,by rw [←eq]; abel⟩

/-- Only two transition differences and one crossing value are needed to detect an
untwisted obstruction on the original four normalized charts. -/
theorem split_of_paired_data_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) (u:Chart→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (v w:Bool→E)
    (dv : LineData false x u v) (dw : LineData true z u w) (joined : Matched x z (v false) (w false)) :
    ∃ c:E, Correction 0 0 u c := by
  let : FiniteDimensional ChartField E := basis.finite
  choose a ia ca using lift_axis false x nx u v reg dv
  choose b ib cb using lift_axis true z nz u w reg dw
  obtain ⟨h₁,h₂,ih₁,ih₂,joint⟩:=joined
  have m (s:Chart) : Matched x z (a s) (b s) := by
    obtain ⟨p,ip,ep⟩:=ca s
    obtain ⟨q,iq,eq⟩:=cb s
    refine ⟨h₁-p,h₂+q,ih₁.sub ip,ih₂.add iq,?_⟩
    rw [mul_sub,mul_add]
    linear_combination joint-ep+eq
  choose l il ax az using fun s=>glue s x z nx nz (a s) (b s) (ia s) (ib s) (m s)
  have residual (s t : Chart) (j:Bool) (d:L) (y:E) (lift:∀ i,Congruent j d (u i-y) (l i)) :
      Congruent j d ((u s-u t)-(l s-l t)) 0 := by
    obtain ⟨r,hr,eq⟩:=(lift s).sub (lift t)
    refine ⟨r,hr,?_⟩
    rw [sub_zero,←eq]; abel
  have restriction (s t : Chart) := product_residue s t x z nx nz ((u s-u t)-(l s-l t))
    ((reg s t).sub ((order_mono (into_cleared _ (edge s t)) (il s)).sub (order_mono (chart_cover s t) (il t))))
    (residual s t _ _ _ (fun i=>(ca i).trans (ax i))) (residual s t _ _ _ (fun i=>(cb i).trans (az i)))
  obtain ⟨p,ip,eq⟩:=RetainedLineRestriction.split_of_split_on_lines_6969 f ir lo hi bounded basis root x z
    (fun s t=>u s-u t) (fun _ _ _=>by abel) l il restriction
  refine ⟨u (false,false)-p (false,false),fun s=>?_⟩
  have id : u s-(u (false,false)-p (false,false))=p s := by linear_combination eq s (false,false)
  simpa [id,frame] using ip s

end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedPairedResidues

section Merged_R6960RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open ChartSections (Chart)
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
open scoped Lower6960.RetainedSurfaceClass

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel_6969 (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data_6969 f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedSurfaceClass
end Z6969Source0431

-- Source: Research6969.FarNonlinear
section Z6969Source0432
set_option autoImplicit true
set_option Elab.async false
section Merged_R6960RetainedTwistedBudget
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwistedRestriction
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (chartSpace congr_of_eq)
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

open RetainedCompression (Curve ordinate view height heightCap)

theorem initial_6969 (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164806 f≤heightCap (f.degreeOf ordinate) 164806) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [FiniteDimensional L (Paired E x z)] {b:ℕ}
    (size:finrank L (Paired E x z)≤b) : Budget E 0 b := by
  have spaces:charts E 0=potentials E := by
    ext u; change (∀s t,Over s t 0 _ )↔_
    simp only [Over,pow_zero,one_mul]; rfl
  let e:=LinearEquiv.ofEq _ _ spaces
  let f₀:=(rawMap E x z).comp e.toLinearMap
  apply RetainedCodimension.from_map f₀ _ _ size
  ext u
  change e u∈(rawMap E x z).ker ↔ ∃ c:E,∀s, Regular s 0 ((u.1 s:E)-c)
  rw [restriction_kernel_6969 E f ir lo hi bounded basis root x z nx nz]
  simp only [Regular,pow_zero,one_mul]; rfl


/-- Uniform surface bound for every positive abscissa twist of the same actual
factor. The degrees s,t are measured on its own two specialized chart orders. -/
theorem actual_all_twists_6969 (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164806 f≤heightCap (f.degreeOf ordinate) 164806) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
        (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)),
        (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
        (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
        Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧ IsReduced (Crossing E x z) ∧
        ∀ i:ℕ, Budget E i (s+(i+1)*t) := by
  have : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi basis root
  obtain ⟨x,z,nx,nz,⟨B⟩,red⟩:=actual_crossing E f ir lo hi basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,base⟩:=paired_bound E x z nx nz xf xi zf zi
  obtain ⟨fg,fo,d,ed,index⟩:=native_euler E false x nx xf xi
  have de : d= -(t:ℤ) := WithBot.coe_injective (ed.symm.trans dt)
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fg
  have inject:=global_eval_injective E false x z nx nz xf
  have eRank := LinearMap.finrank_le_finrank_of_injective inject
  change finrank L (LineGlobals E false x)≤finrank L (Crossing E x z) at eRank
  have mrank:=node_rank_le E false x z nx nz xf
  have line : finrank L (LineObstructions E false x)≤t := by omega
  refine ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B⟩,red,fun i=>?_⟩
  induction i with
  | zero => simpa only [zero_add,one_mul] using initial_6969 E f ir lo hi bounded basis root x z nx nz base
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,Nat.add_assoc] using grow E i x nx ih line

end Lower6960.RetainedTwistedRestriction

end
end Merged_R6960RetainedTwistedBudget

section Merged_R6960MarkedVerticalProfile
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 14000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open RetainedCompression (Curve ordinate view view_y height heightCap)
open RetainedRestrictionTorus RetainedSurfaceClass CollisionMarked Polynomial LineEuler Algebra Module Submodule Horner
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.Horner Lower6960.RetainedSurfaceClass

local instance profileFieldDecidable_6969 : DecidableEq ChartField := Classical.decEq _

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]



/-- The vertical deficit of this precise surface is positive on the nonlinear
branch, is tame at the profile prime, and supplies the physical function rank. -/
theorem vertical_profile_6969 (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164806 f≤heightCap (f.degreeOf ordinate) 164806) (nonlin:¬RetainedLinear.GeometricallyLinear (view f))
    (b:PowerBasis ChartField E) (dim:b.dim=(view f).natDegree)
    (root:aeval b.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (small:finrank L (Crossing E x z)<K1.p) {n:ℕ}
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true))
    (s:ℕ) (measure:(transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    0<s ∧ 2*s<K1.p ∧ ∀(U:Finset L)(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j)) →
      finrank Scalar (span Scalar (Set.range v))+s≤(view f).natDegree*s := by
  classical
  let Q:=RetainedLinear.toSeed (view f)
  have e0:Q.natDegree=(view f).natDegree:=RetainedLinear.toSeed_degree _
  have e1:(view f).natDegree=f.degreeOf ordinate:=view_y f
  have rank:finrank ChartField E=(view f).natDegree:=b.finrank.trans dim
  have gen:=generic_measure_eq_native (E:=E) true x z nx nz K1.p small zf zi s measure
  dsimp only at gen
  rw [generic_algebra_vertical] at gen
  obtain ⟨F,I,det⟩:=gen
  have positive:0<s := by
    by_contra! h
    have zd:s=0:=by omega
    rw [zd,Nat.cast_zero,neg_zero,WithBot.coe_zero] at det
    obtain ⟨w,ind,integ⟩:=constant_frame F I det
    have pos:0<finrank ChartField E:=Module.finrank_pos
    letI:Nonempty (Fin (finrank ChartField E)):=⟨⟨0,pos⟩⟩
    exact nonlin (actual_geometric_of_constants (view f) ((MulEquiv.irreducible_iff view).mpr ir)
      (by omega) b root w ind (Fintype.card_fin _) integ)
  have width (j:ℕ):(Q.coeff j).natDegree≤heightCap (f.degreeOf ordinate) 164806 := by
    have d:(Q.coeff j).natDegree=((view f).coeff j).natDegree:=by
      simp only [Q,RetainedLinear.toSeed,Polynomial.coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
    rw [d]
    by_cases z:(view f).coeff j=0
    · rw [z,natDegree_zero];omega
    · exact (Nat.le_add_right _ _).trans ((RetainedCompression.abscissa_coeff_height f 164806 j z).trans bounded)
  have hr (n':ℕ) (eq:n'=Q.natDegree)
      (F':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) false))
      (I':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) true))
      (dd:(normalizedTransition F' I').det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
      s≤(Q.natDegree-1)*heightCap (f.degreeOf ordinate) 164806 := by
    subst n'
    obtain ⟨d,dg,db⟩:=actual_horner_budget Q _ (by omega) width b.gen root
      (b.natDegree_minpoly.trans (dim.trans e0.symm)) F' I'
    have eq:d= -(s:ℤ):=WithBot.coe_injective (dg.symm.trans dd)
    rw [eq,neg_neg] at db
    exact_mod_cast db
  have cap:=hr _ (rank.trans e0.symm) F I det
  have tame:2*s<K1.p := by
    have h:2*((f.degreeOf ordinate-1)*heightCap (f.degreeOf ordinate) 164806)<K1.p := by
      exact (by decide +kernel : ∀j:Fin 48,2*((j.val-1)*heightCap j.val 164806)<K1.p) ⟨_,hi⟩
    rw [e0,e1] at cap;omega
  refine ⟨positive,tame,fun U m v regular=>?_⟩
  have bound:=actual_vertical_rank F I s positive det U m v regular
  rwa [Fintype.card_fin,rank] at bound

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedVerticalProfile

section Merged_R6960MarkedProtocol
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open MonicChart (Scalar ChartField)
open RetainedCompression (Curve ordinate parameter view view_y height heightCap MarkedFiber)
open RetainedTwistedRestriction RetainedSurfaceClass CollisionMarked Polynomial Module Algebra Finset
open scoped Polynomial Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass





theorem nonlinear_6969 (T : Finset K) (label : K → L) (inj : Function.Injective label)
    (word : K → Polynomial L) (f : Curve (Polynomial L)) (ir : Irreducible f)
    (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48) (seed : 0<f.degreeOf parameter)
    (bounded : height 164806 f≤heightCap (f.degreeOf ordinate) 164806)
    (nonlin : ¬RetainedLinear.GeometricallyLinear (view f))
    (marks : ∀ γ∈T, MarkedFiber (view f) (label γ) (word γ)) :
    T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate := by
  classical
  let P:=view f
  let Q:(Polynomial ChartField):=(RetainedLinear.toSeed P).map (algebraMap (Polynomial Scalar) ChartField)
  have pi:Irreducible P:=(MulEquiv.irreducible_iff view).mpr ir
  have degP:P.natDegree=f.degreeOf ordinate:=view_y f
  have seedI:=RetainedLinear.toSeed_irreducible pi (by omega : 0<P.natDegree)
  have degS: (RetainedLinear.toSeed P).natDegree=P.natDegree:=RetainedLinear.toSeed_degree P
  have qi:Irreducible Q := (seedI.isPrimitive (by omega)).irreducible_iff_irreducible_map_fraction_map.mp seedI
  letI : Fact (Irreducible Q):=⟨qi⟩
  let E:=AdjoinRoot Q
  let b:PowerBasis ChartField E:=AdjoinRoot.powerBasis qi.ne_zero
  have root:aeval b.gen Q=0 := (AdjoinRoot.aeval_eq Q).trans (AdjoinRoot.mk_self)
  have dim:b.dim=P.natDegree:=(natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) ChartField)
    (RetainedLinear.toSeed P)).trans degS
  have : FiniteDimensional ChartField E:=b.finite
  have : Algebra.IsSeparable ChartField E:=MonicChartProbes.actual_separable f ir lo hi b root
  letI : CharP Scalar K1.p:=charP_of_injective_ringHom inner.injective K1.p
  obtain ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B⟩,reduced,surface⟩:=
    actual_all_twists_6969 E f ir lo hi bounded b root
  have : FiniteDimensional L (Crossing E x z):=Module.Finite.of_basis B
  have small:finrank L (Crossing E x z)<K1.p := by
    rw [finrank_eq_card_basis B,Fintype.card_fin];exact hi.trans (by decide)
  obtain ⟨positive,tame,vrank⟩:=vertical_profile_6969 f ir lo hi bounded nonlin b dim root x z nx nz small zf zi s ds
  have tariff:=actual_horizontal_horner f ir lo hi b root x z nx nz K1.p small xf xi t dt
  obtain ⟨δf,δi,nf,ni,df,di,xc,zc,tail⟩:=
    actual_measured_discriminants x z nx nz K1.p small xf xi zf zi s t ds dt
  let S:=T.image label
  let wt (z:L):(Polynomial L):=word (Function.invFun label z)
  have mark (z:L) (mem:z∈S):MarkedFiber P z (wt z) := by
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp mem
    change MarkedFiber P _ (word (Function.invFun label (label a)))
    rw [Function.leftInverse_invFun inj];exact marks a ha
  have pn:projectedRaw P≠0:=by intro zero;have eq:=projectedRaw_degree P;rw [zero,natDegree_zero] at eq;omega
  have bound:=all_labels (E:=E) K1.p P pn (by omega) (degP ▸ hi.trans (by decide : 48<K1.p))
    (f.degreeOf parameter) seed b dim (projected_root_of_seed P b.gen root) s t positive tame
    (degP.symm ▸ tariff) (by simpa only [Nat.sub_add_cancel positive] using surface (s-1))
    δf δi nf ni df di xc zc tail S wt mark vrank
  rwa [show S.card=T.card from card_image_of_injective _ inj,degP] at bound

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedProtocol
end Z6969Source0432

-- Source: Research6969.FarFactorPrice
section Z6969Source0433
set_option autoImplicit true
set_option Elab.async false

namespace Research6969.Far6969FactorPrice
open Polynomial Finset
open K1 (K I p)
open K1_14 (L liftPoly)
open Lower6960
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter view view_y view_z
  MarkedFiber no_zero_degree constant_price specialize height heightCap evaluate_view evaluate
  escape proper_cut_price aggregate box_iff abscissa_le_height pure_node_price_6969)
open RetainedLinear (GeometricallyLinear)
open CurvatureSquares (Ordinate zView xView ordEval)
open scoped Polynomial
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000

abbrev agreement : ℕ := 179740
abbrev wordDegree : ℕ := 164806
abbrev rate := MarkedEvaluation.rate

theorem rate_mono : Monotone rate := by
  intro e n le
  unfold rate MarkedEvaluation.rate
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 le) _) (Nat.sub_le_sub_right le 1))
    (Nat.mul_le_mul_left 2 le)) 1

private theorem vote_scale : CurvatureVotes.VoteScale agreement wordDegree 18 :=
  Or.inl (by decide +kernel)

private theorem word_roots {U : Finset K} (s : K → K[X]) (label : K → L) (Q : Ordinate)
    (H : ∀ γ∈U, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    ∀ γ∈U, ordEval (label γ) ((s γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (label γ))) (liftPoly (s γ))=0
  rw [← eval_map]
  exact (H γ hγ).root

theorem factor {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : n<48)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈T, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    T.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases T.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 24≤rate n := (by decide : 24≤rate 3).trans (rate_mono lo)
  have vRate : 18≤rate n := (by decide : 18≤24).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn label (T : Set K) := inject.injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (s x)) (T:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q T label (fun x=>liftPoly (s x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots s label Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) label inj
      (by decide) vote_scale Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e wordDegree < height wordDegree q
  · let param (j : T) := label j.val
    let root (j : T) := liftPoly (s j.val)
    have deg (j : T) : (root j).natDegree≤wordDegree := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : T) : evaluate (param j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape param root wordDegree (by decide) deg q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price T label (fun j=>liftPoly (s j))
      inj q G qp nondiv pos y z gy gz (fun j hj=>rootsF ⟨j,hj⟩)
      (fun j hj=>rootsG ⟨j,hj⟩)
    have ceiling : 12*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using tRate
      have three : 3≤e := by omega
      have ratio : 12*e≤rate e :=
        (by decide +kernel : ∀ i : Fin 48, 3 ≤ i.val → 12*i.val ≤ rate i.val)
          ⟨_,degree.trans_lt hi⟩ three
      exact ratio.trans (rate_mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q wordDegree
        rw [RingEquiv.apply_symm_apply] at a
        exact (Nat.mul_le_mul_left 2 (a.trans wt)).trans_lt (by rw [two]; decide)
      have count := CurvatureSquares.degree_two_count words (algebraMap K L) label inj
        (by decide) vote_scale Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have mark' (j : K) (hj : j ∈ T) : MarkedFiber (view q) (label j) (liftPoly (s j)) := by
      simpa only [q,RingEquiv.apply_symm_apply] using mark j hj
    have charge : T.card≤rate (q.degreeOf ordinate)*(q.degreeOf parameter)+
        (q.degreeOf ordinate-1)*q.degreeOf ordinate := by
      by_cases pure : GeometricallyLinear (view q)
      · have irr : Irreducible (view q) := (MulEquiv.irreducible_iff view).mpr qp
        have pos' : 0<(view q).natDegree := by rw [view_y];omega
        have nodes := RetainedLinear.pure_of_geometrically_linear w (view q) irr pos' pure
        have bound := pure_node_price_6969 words label inj (view q) irr pos' nodes mark'
        rw [view_z] at bound
        exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_mono three)))
          (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
      · exact MarkedEvaluation.nonlinear_6969 T label inject (fun j=>liftPoly (s j)) q qp three
          (y.symm ▸ degree.trans_lt hi) (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt) pure mark'
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (rate_mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))

/-- The factored tariff for any integral retained ordinate, with no
dependency on how the marks or the integral equation were produced. -/
theorem price {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    (P : Ordinate) (pn : P≠0) (n B : ℕ) (lo : 3≤n) (hi : n<48)
    (degree : P.natDegree≤n) (bound : (zView P).natDegree≤B)
    (marks : ∀ γ∈T, MarkedFiber P (label γ) (liftPoly (s γ))) :
    T.card≤rate n*B+(n-1)*P.natDegree := by
  have chosen := aggregate P T label (fun j=>liftPoly (s j)) (rate n) (n-1) pn marks (by
    intro Q ir dvd U sub mark
    have W : Word agreement wordDegree w s U :=
      ⟨words.distinct.mono sub,fun j hj=>words.degree j (sub hj),fun j hj=>words.hits j (sub hj)⟩
    exact factor W label inject ir n lo hi ((natDegree_le_of_dvd dvd pn).trans degree) mark)
  exact chosen.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ bound) _)

end Research6969.Far6969FactorPrice
end Z6969Source0433
