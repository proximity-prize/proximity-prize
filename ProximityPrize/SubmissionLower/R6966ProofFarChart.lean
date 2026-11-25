import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Union
import ProximityPrize.SubmissionLower.R6960MonicChartFrobenius
import ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant

set_option Elab.async false

-- merged module R6960MonicFourChartDescent
section Merged_R6960MonicFourChartDescent

-- merged module R6960ChartSections
section Merged_R6960ChartSections
namespace Lower6960.ChartSections
abbrev Exponent := ℤ×ℤ
abbrev Chart := Bool×Bool
def fits (d : ℕ) (s : Bool) (i : ℤ) : Prop :=
  if s then i ≤ -(d:ℤ) else 0 ≤ i
def allowed (a b : ℕ) (s : Chart) (m : Exponent) : Prop :=
  fits a s.1 m.1 ∧ fits b s.2 m.2
def overlap (a b : ℕ) (s t : Chart) (m : Exponent) : Prop :=
  (s.1=t.1 → fits a s.1 m.1) ∧ (s.2=t.2 → fits b s.2 m.2)
private def opposite (i : ℤ) : Bool := decide (0 ≤ i)
private theorem excluded (d : ℕ) (hd : 0<d) (i : ℤ) : ¬fits d (opposite i) i := by
  by_cases hi : 0 ≤ i
  · simp [opposite,hi,fits]; omega
  · simp [opposite,hi,fits]
theorem negative_correction {k : Type*} [AddCommGroup k] (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (p : Chart→Exponent→₀k)
    (compatible : ∀ s t m,¬overlap a b s t m → (p s) m=(p t) m) :
    ∃ c : Exponent→₀k, ∀ s m,¬allowed a b s m → (p s-c) m=0 := by
  classical
  let coeff (m : Exponent) := p (opposite m.1,opposite m.2) m
  let support := Finset.univ.biUnion fun s : Chart=>(p s).support
  let c : Exponent→₀k := Finsupp.onFinset support coeff (fun m hm=>
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hm⟩)
  refine ⟨c,?_⟩
  rintro ⟨s,t⟩ ⟨i,j⟩ bad
  change ¬(fits a s i ∧ fits b t j) at bad
  change p (s,t) (i,j)-p (opposite i,opposite j) (i,j)=0
  apply sub_eq_zero.mpr
  by_cases bx : fits a s i
  · have bz : ¬fits b t j := fun z=>bad ⟨bx,z⟩
    calc p (s,t) (i,j) = p (opposite i,t) (i,j) := compatible (s,t) (opposite i,t) (i,j) (fun h=>bz (h.2 rfl))
         _ = _ := compatible (opposite i,t) (opposite i,opposite j) (i,j) (fun h=>excluded a ha i (h.1 rfl))
  · calc p (s,t) (i,j) = p (s,opposite j) (i,j) := compatible (s,t) (s,opposite j) (i,j) (fun h=>bx (h.1 rfl))
         _ = _ := compatible (s,opposite j) (opposite i,opposite j) (i,j) (fun h=>excluded b hb j (h.2 rfl))
theorem no_global {k : Type*} [Zero k] (a b : ℕ) (negative : 0<a ∨ 0<b)
    (f : Exponent→₀k) (regular : ∀ s m,¬allowed a b s m → f m=0) : f=0 := by
  ext m
  rcases negative with ha | hb
  · exact regular (opposite m.1,false) m (fun h=>excluded a ha m.1 h.1)
  · exact regular (false,opposite m.2) m (fun h=>excluded b hb m.2 h.2)
#print axioms negative_correction
#print axioms no_global
section
variable {k ι J : Type*} [CommRing k] [Fintype ι]
def relation (column : ι→J) (coefficient : ι→k) (offset : ι→Exponent)
    (u : J→Exponent→₀k) (m : Exponent) : k :=
  ∑ i,coefficient i*u (column i) (m.1-(offset i).1,m.2-(offset i).2)
theorem correction_with_relations {L : Type*} (a b B : ℕ) (wide : 2*B<a) (hb : 0<b)
    (col : L→ι→J) (coeff : L→ι→k) (off : L→ι→Exponent)
    (bound : ∀ l i,-(B:ℤ)≤(off l i).1 ∧ (off l i).1≤(B:ℤ))
    (u : Chart→J→Exponent→₀k)
    (compatible : ∀ j s t m,¬overlap a b s t m → u s j m=u t j m)
    (closed : ∀ l s m,relation (col l) (coeff l) (off l) (u s) m=0) :
    ∃ v : J→Exponent→₀k,
      (∀ s j m,¬allowed a b s m → (u s j-v j) m=0) ∧
      ∀ l m,relation (col l) (coeff l) (off l) v m=0 := by
  classical
  choose v hv using fun j=>negative_correction a b (by omega) hb (fun s=>u s j) (compatible j)
  refine ⟨v,fun s j=>hv j s,?_⟩
  intro l m
  let s : Chart := (decide (-(B:ℤ) ≤ m.1),false)
  have agree (i) : u s (col l i) (m.1-(off l i).1,m.2-(off l i).2)=
      v (col l i) (m.1-(off l i).1,m.2-(off l i).2) := by
    apply sub_eq_zero.mp
    apply hv (col l i) s
    intro h
    have x:=h.1
    obtain ⟨low,high⟩:=bound l i
    by_cases side : -(B:ℤ)≤m.1
    · simp [s,side,fits] at x; omega
    · simp [s,side,fits] at x; omega
  calc _ = relation (col l) (coeff l) (off l) (u s) m := by
             unfold relation
             exact Finset.sum_congr rfl (fun i _=>congrArg (coeff l i*·) (agree i).symm)
       _ = 0 := closed l s m
#print axioms correction_with_relations
end
end Lower6960.ChartSections

end Merged_R6960ChartSections

-- merged module R6960MonicFourChartDescent
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
open RetainedCompression (Curve ordinate view height heightCap wordDegree)
open scoped Polynomial
def constants : L →+* ChartField := RatFunc.C.comp ((algebraMap (Polynomial L) Scalar).comp C)
def scalarCoordinate : ChartField := RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))
def chartCoordinate (infinity : Bool) (x : ChartField) : ChartField :=
  if infinity then x⁻¹ else x
def baseChart (s : Chart) : Subring ChartField :=
  Subring.closure (Set.range constants ∪
    {chartCoordinate s.1 RatFunc.X, chartCoordinate s.2 scalarCoordinate})
def frame (a b : ℕ) (s : Chart) : ChartField :=
  (if s.1 then RatFunc.X else 1)^a * (if s.2 then scalarCoordinate else 1)^b
theorem frame_scale (a b n : ℕ) (s : Chart) :
    frame (a*n) (b*n) s=(frame a b s)^n := by
  simp only [frame,pow_mul,mul_pow]
variable {E : Type*} [Field E] [Algebra ChartField E]
def Correction (a b : ℕ) (u : Chart → E) (c : E) : Prop :=
  ∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*(u s-c))
theorem finite_inclusion :
    baseChart (false,false) ≤ (algebraMap (Polynomial Scalar) ChartField).range := by
  apply Subring.closure_le.mpr
  intro x hx
  simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with ⟨c,rfl⟩ | rfl | rfl
  · exact ⟨C (algebraMap (Polynomial L) Scalar (C c)),RatFunc.algebraMap_C _⟩
  · exact ⟨Polynomial.X,RatFunc.algebraMap_X⟩
  · exact ⟨C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L))),RatFunc.algebraMap_C _⟩
theorem infinity_inclusion [DecidableEq ChartField] :
    baseChart (true,false) ≤ (algebraMap (Infinity Scalar) ChartField).range := by
  apply Subring.closure_le.mpr
  intro x hx
  simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with ⟨c,rfl⟩ | rfl | rfl
  · exact ⟨MonicChart.inftyRingEval Scalar (C (algebraMap (Polynomial L) Scalar (C c))),aeval_C _ _⟩
  · exact ⟨MonicChart.inftyRingEval Scalar Polynomial.X,MonicChart.mapped_X_infty⟩
  · exact ⟨MonicChart.inftyRingEval Scalar (C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))),
      aeval_C _ _⟩
theorem integral_of_inclusion (s : Chart) {R : Type*} [CommRing R] [Algebra R ChartField]
    [Algebra R E] [IsScalarTower R ChartField E] (inj : Function.Injective (algebraMap R ChartField))
    (fit : baseChart s ≤ (algebraMap R ChartField).range) {q : E}
    (integral : IsIntegral (baseChart s) q) : IsIntegral R q := by
  let j := algebraMap R ChartField
  let equiv : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b eq=>inj (congrArg Subtype.val eq),j.rangeRestrict_surjective⟩
  let lift : baseChart s →+* R := equiv.symm.toRingHom.comp (Subring.inclusion fit)
  have commute (x : baseChart s) : j (lift x)=(x:ChartField) :=
    congrArg Subtype.val (equiv.apply_symm_apply (Subring.inclusion fit x))
  let : Algebra (baseChart s) R := lift.toAlgebra
  let : IsScalarTower (baseChart s) R E := IsScalarTower.of_algebraMap_eq fun x=>by
    change algebraMap ChartField E (x:ChartField) = algebraMap R E (lift x)
    rw [IsScalarTower.algebraMap_apply R ChartField E,commute]
  exact integral.tower_top
theorem descend (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
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
  obtain ⟨w,hw⟩ := MonicChart.actual_coboundary_pth_root f ir lo hi bounded basis root_in_tower
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
theorem descend_iterate (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
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
    obtain ⟨v,hv,hv'⟩ := descend f ir lo hi bounded basis root (a*K1.p^n) (b*K1.p^n)
      (Nat.mul_pos ha (pow_pos KoalaBear.is_prime.pos _)) (fun s=>u s ^ (K1.p^n)) c next
    obtain ⟨d,hd,hd'⟩ := ih v hv'
    exact ⟨d,by rw [pow_succ K1.p n,pow_mul,hd,hv],hd'⟩
#print axioms descend
#print axioms descend_iterate
end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

-- merged module R6966ProofFarChart
section Merged_R6966ProofFarChart

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
theorem actual_coboundary_zero_far {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra (Polynomial Scalar) E]
    [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra (Polynomial Scalar) E] [DifferentialAlgebra (Infinity Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
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
  let H := heightCap e 164748
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
      (P.coeff j).natDegree+164748*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm 164748]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f 164748 j zero).trans bounded
  have Hfit : 164748*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H 164748 := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H 164748 ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=164748) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H 164748<K1.p := by
    rw [deg,width_at_cutoff e 164748 (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right 164748
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
  exact common_coboundary_zero_generic b P H 164748 K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

#print axioms actual_coboundary_zero_far
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
    (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
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
  exact actual_coboundary_zero_far f ir lo hi bounded b root x y z fx iy overlap
theorem actual_coboundary_pth_root_far
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
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

theorem descend_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
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
  obtain ⟨w,hw⟩ := MonicChart.actual_coboundary_pth_root_far f ir lo hi bounded basis root_in_tower
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
theorem descend_iterate_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
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
    obtain ⟨v,hv,hv'⟩ := descend_far f ir lo hi bounded basis root (a*K1.p^n) (b*K1.p^n)
      (Nat.mul_pos ha (pow_pos KoalaBear.is_prime.pos _)) (fun s=>u s ^ (K1.p^n)) c next
    obtain ⟨d,hd,hd'⟩ := ih v hv'
    exact ⟨d,by rw [pow_succ K1.p n,pow_mul,hd,hv],hd'⟩
#print axioms descend_far
#print axioms descend_iterate_far
end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

end Merged_R6966ProofFarChart
