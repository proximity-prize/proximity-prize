import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Near6967LargeRank19g5
import ProximityPrize.SubmissionLower.Near6967RescueMoment0
import ProximityPrize.SubmissionLower.Near6967RescueMoment21
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing

section Merged6967_R6966ProofFarChart
set_option Elab.async false






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
    (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
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
  let H := heightCap e 164768
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
      (P.coeff j).natDegree+164768*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm 164768]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f 164768 j zero).trans bounded
  have Hfit : 164768*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H 164768 := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H 164768 ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=164768) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H 164768<K1.p := by
    rw [deg,width_at_cutoff e 164768 (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right 164768
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
  exact common_coboundary_zero_generic b P H 164768 K1.p prim e2 dimension tame weights
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
    (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
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
    (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
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
    (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
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
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
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

end Merged6967_R6966ProofFarChart

section Merged6967_R6966ProofFarHelperChecks
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem helper_twoSlopes_first : value (helper .twoSlopes) 2523 = 6545338531045200 := by decide +kernel
private theorem helper_twoSlopes_next : value (helper .twoSlopes) 2524 = 6679665452604930 := by decide +kernel
theorem helper_twoSlopes : Checked (helper .twoSlopes) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_twoSlopes_first]; decide
  · rw [helper_twoSlopes_first, helper_twoSlopes_next]; decide

private theorem helper_seedBoundary_first : value (helper .seedBoundary) 2523 = 7560830254794174 := by decide +kernel
private theorem helper_seedBoundary_next : value (helper .seedBoundary) 2524 = 7695555085052792 := by decide +kernel
theorem helper_seedBoundary : Checked (helper .seedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_seedBoundary_first]; decide
  · rw [helper_seedBoundary_first, helper_seedBoundary_next]; decide

private theorem helper_mixedBoundary_first : value (helper .mixedBoundary) 2523 = 7362928442070252 := by decide +kernel
private theorem helper_mixedBoundary_next : value (helper .mixedBoundary) 2524 = 7497579418291506 := by decide +kernel
theorem helper_mixedBoundary : Checked (helper .mixedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_mixedBoundary_first]; decide
  · rw [helper_mixedBoundary_first, helper_mixedBoundary_next]; decide

private theorem helper_jetBoundary_first : value (helper .jetBoundary) 2523 = 13870655135954406 := by decide +kernel
private theorem helper_jetBoundary_next : value (helper .jetBoundary) 2524 = 14007885472736058 := by decide +kernel
theorem helper_jetBoundary : Checked (helper .jetBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_jetBoundary_first]; decide
  · rw [helper_jetBoundary_first, helper_jetBoundary_next]; decide

#print axioms helper_jetBoundary
end Research6966.FarSourceData

end Merged6967_R6966ProofFarHelperChecks

section Merged6967_R6966ProofFarRescueChecks0
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_0_first : value (rescue 0 0) 2523 = 10993851832907096028 := by decide +kernel
private theorem rescue0_0_next : value (rescue 0 0) 2524 = 11281408671784861830 := by decide +kernel
theorem rescue0_0 : Checked (rescue 0 0) := by
  refine ⟨(Lower6960.RescueSource.checked 0 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_0_first]; decide
  · rw [rescue0_0_first, rescue0_0_next]; decide

private theorem rescue0_1_first : value (rescue 0 1) 2523 = 16277657288235768940 := by decide +kernel
private theorem rescue0_1_next : value (rescue 0 1) 2524 = 16707514658117575641 := by decide +kernel
theorem rescue0_1 : Checked (rescue 0 1) := by
  refine ⟨(Lower6960.RescueSource.checked 0 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_1_first]; decide
  · rw [rescue0_1_first, rescue0_1_next]; decide

private theorem rescue0_2_first : value (rescue 0 2) 2523 = 23179202614347604758 := by decide +kernel
private theorem rescue0_2_next : value (rescue 0 2) 2524 = 23787796224702143914 := by decide +kernel
theorem rescue0_2 : Checked (rescue 0 2) := by
  refine ⟨(Lower6960.RescueSource.checked 0 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_2_first]; decide
  · rw [rescue0_2_first, rescue0_2_next]; decide

private theorem rescue0_3_first : value (rescue 0 3) 2523 = 34747829043717608682 := by decide +kernel
private theorem rescue0_3_next : value (rescue 0 3) 2524 = 35665950998225780301 := by decide +kernel
theorem rescue0_3 : Checked (rescue 0 3) := by
  refine ⟨(Lower6960.RescueSource.checked 0 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_3_first]; decide
  · rw [rescue0_3_first, rescue0_3_next]; decide

private theorem rescue0_4_first : value (rescue 0 4) 2523 = 52615867542843322138 := by decide +kernel
private theorem rescue0_4_next : value (rescue 0 4) 2524 = 53988372690271896947 := by decide +kernel
theorem rescue0_4 : Checked (rescue 0 4) := by
  refine ⟨(Lower6960.RescueSource.checked 0 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_4_first]; decide
  · rw [rescue0_4_first, rescue0_4_next]; decide

private theorem rescue0_5_first : value (rescue 0 5) 2523 = 67359285271636795191 := by decide +kernel
private theorem rescue0_5_next : value (rescue 0 5) 2524 = 69179245508755399803 := by decide +kernel
theorem rescue0_5 : Checked (rescue 0 5) := by
  refine ⟨(Lower6960.RescueSource.checked 0 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_5_first]; decide
  · rw [rescue0_5_first, rescue0_5_next]; decide

private theorem rescue0_6_first : value (rescue 0 6) 2523 = 121656882695070774787 := by decide +kernel
private theorem rescue0_6_next : value (rescue 0 6) 2524 = 124944471805025408291 := by decide +kernel
theorem rescue0_6 : Checked (rescue 0 6) := by
  refine ⟨(Lower6960.RescueSource.checked 0 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_6_first]; decide
  · rw [rescue0_6_first, rescue0_6_next]; decide

private theorem rescue0_7_first : value (rescue 0 7) 2523 = 268770206213944602876 := by decide +kernel
private theorem rescue0_7_next : value (rescue 0 7) 2524 = 276286952477044288258 := by decide +kernel
theorem rescue0_7 : Checked (rescue 0 7) := by
  refine ⟨(Lower6960.RescueSource.checked 0 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_7_first]; decide
  · rw [rescue0_7_first, rescue0_7_next]; decide

#print axioms rescue0_7
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks0

section Merged6967_R6966ProofFarRescueChecks1
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_8_first : value (rescue 0 8) 2523 = 943789569290868389493 := by decide +kernel
private theorem rescue0_8_next : value (rescue 0 8) 2524 = 970614815246679257133 := by decide +kernel
theorem rescue0_8 : Checked (rescue 0 8) := by
  refine ⟨(Lower6960.RescueSource.checked 0 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_8_first]; decide
  · rw [rescue0_8_first, rescue0_8_next]; decide

private theorem rescue0_9_first : value (rescue 0 9) 2523 = 267244918515615466491 := by decide +kernel
private theorem rescue0_9_next : value (rescue 0 9) 2524 = 274576396254103191416 := by decide +kernel
theorem rescue0_9 : Checked (rescue 0 9) := by
  refine ⟨(Lower6960.RescueSource.checked 0 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_9_first]; decide
  · rw [rescue0_9_first, rescue0_9_next]; decide

private theorem rescue0_10_first : value (rescue 0 10) 2523 = 2406545104677087139848 := by decide +kernel
private theorem rescue0_10_next : value (rescue 0 10) 2524 = 2479953131085029892458 := by decide +kernel
theorem rescue0_10 : Checked (rescue 0 10) := by
  refine ⟨(Lower6960.RescueSource.checked 0 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_10_first]; decide
  · rw [rescue0_10_first, rescue0_10_next]; decide

private theorem rescue0_11_first : value (rescue 0 11) 2523 = 12287576678775534651765 := by decide +kernel
private theorem rescue0_11_next : value (rescue 0 11) 2524 = 12670859791761626119151 := by decide +kernel
theorem rescue0_11 : Checked (rescue 0 11) := by
  refine ⟨(Lower6960.RescueSource.checked 0 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_11_first]; decide
  · rw [rescue0_11_first, rescue0_11_next]; decide

private theorem rescue0_12_first : value (rescue 0 12) 2523 = 8685889781659315105339 := by decide +kernel
private theorem rescue0_12_next : value (rescue 0 12) 2524 = 8937903425812963607931 := by decide +kernel
theorem rescue0_12 : Checked (rescue 0 12) := by
  refine ⟨(Lower6960.RescueSource.checked 0 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_12_first]; decide
  · rw [rescue0_12_first, rescue0_12_next]; decide

private theorem rescue0_13_first : value (rescue 0 13) 2523 = 33436196178634889213719 := by decide +kernel
private theorem rescue0_13_next : value (rescue 0 13) 2524 = 34432943515138260125798 := by decide +kernel
theorem rescue0_13 : Checked (rescue 0 13) := by
  refine ⟨(Lower6960.RescueSource.checked 0 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_13_first]; decide
  · rw [rescue0_13_first, rescue0_13_next]; decide

private theorem rescue0_14_first : value (rescue 0 14) 2523 = 280417622456098156708042 := by decide +kernel
private theorem rescue0_14_next : value (rescue 0 14) 2524 = 288904471049547041737291 := by decide +kernel
theorem rescue0_14 : Checked (rescue 0 14) := by
  refine ⟨(Lower6960.RescueSource.checked 0 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_14_first]; decide
  · rw [rescue0_14_first, rescue0_14_next]; decide

private theorem rescue0_15_first : value (rescue 0 15) 2523 = 330548933888513495788671 := by decide +kernel
private theorem rescue0_15_next : value (rescue 0 15) 2524 = 340551606824331637490082 := by decide +kernel
theorem rescue0_15 : Checked (rescue 0 15) := by
  refine ⟨(Lower6960.RescueSource.checked 0 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_15_first]; decide
  · rw [rescue0_15_first, rescue0_15_next]; decide

#print axioms rescue0_15
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks1

section Merged6967_R6966ProofFarRescueChecks2
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_16_first : value (rescue 0 16) 2523 = 1300133281356352385144812 := by decide +kernel
private theorem rescue0_16_next : value (rescue 0 16) 2524 = 1339786344907610075920742 := by decide +kernel
theorem rescue0_16 : Checked (rescue 0 16) := by
  refine ⟨(Lower6960.RescueSource.checked 0 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_16_first]; decide
  · rw [rescue0_16_first, rescue0_16_next]; decide

private theorem rescue1_0_first : value (rescue 1 0) 2523 = 9885536861786535480 := by decide +kernel
private theorem rescue1_0_next : value (rescue 1 0) 2524 = 10144087367396544695 := by decide +kernel
theorem rescue1_0 : Checked (rescue 1 0) := by
  refine ⟨(Lower6960.RescueSource.checked 1 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_0_first]; decide
  · rw [rescue1_0_first, rescue1_0_next]; decide

private theorem rescue1_1_first : value (rescue 1 1) 2523 = 14634260873436752981 := by decide +kernel
private theorem rescue1_1_next : value (rescue 1 1) 2524 = 15020701517213981108 := by decide +kernel
theorem rescue1_1 : Checked (rescue 1 1) := by
  refine ⟨(Lower6960.RescueSource.checked 1 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_1_first]; decide
  · rw [rescue1_1_first, rescue1_1_next]; decide

private theorem rescue1_2_first : value (rescue 1 2) 2523 = 20859967959017294682 := by decide +kernel
private theorem rescue1_2_next : value (rescue 1 2) 2524 = 21407658903143839546 := by decide +kernel
theorem rescue1_2 : Checked (rescue 1 2) := by
  refine ⟨(Lower6960.RescueSource.checked 1 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_2_first]; decide
  · rw [rescue1_2_first, rescue1_2_next]; decide

private theorem rescue1_3_first : value (rescue 1 3) 2523 = 31227069148370693265 := by decide +kernel
private theorem rescue1_3_next : value (rescue 1 3) 2524 = 32052139154317577831 := by decide +kernel
theorem rescue1_3 : Checked (rescue 1 3) := by
  refine ⟨(Lower6960.RescueSource.checked 1 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_3_first]; decide
  · rw [rescue1_3_first, rescue1_3_next]; decide

private theorem rescue1_4_first : value (rescue 1 4) 2523 = 47429316720838890624 := by decide +kernel
private theorem rescue1_4_next : value (rescue 1 4) 2524 = 48666484982962399873 := by decide +kernel
theorem rescue1_4 : Checked (rescue 1 4) := by
  refine ⟨(Lower6960.RescueSource.checked 1 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_4_first]; decide
  · rw [rescue1_4_first, rescue1_4_next]; decide

private theorem rescue1_5_first : value (rescue 1 5) 2523 = 60653053592500348353 := by decide +kernel
private theorem rescue1_5_next : value (rescue 1 5) 2524 = 62291798132412526464 := by decide +kernel
theorem rescue1_5 : Checked (rescue 1 5) := by
  refine ⟨(Lower6960.RescueSource.checked 1 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_5_first]; decide
  · rw [rescue1_5_first, rescue1_5_next]; decide

private theorem rescue1_6_first : value (rescue 1 6) 2523 = 109682455853969740771 := by decide +kernel
private theorem rescue1_6_next : value (rescue 1 6) 2524 = 112646313090642365006 := by decide +kernel
theorem rescue1_6 : Checked (rescue 1 6) := by
  refine ⟨(Lower6960.RescueSource.checked 1 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_6_first]; decide
  · rw [rescue1_6_first, rescue1_6_next]; decide

#print axioms rescue1_6
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks2

section Merged6967_R6966ProofFarRescueChecks3
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue1_7_first : value (rescue 1 7) 2523 = 241993128456778330713 := by decide +kernel
private theorem rescue1_7_next : value (rescue 1 7) 2524 = 248760953173520095083 := by decide +kernel
theorem rescue1_7 : Checked (rescue 1 7) := by
  refine ⟨(Lower6960.RescueSource.checked 1 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_7_first]; decide
  · rw [rescue1_7_first, rescue1_7_next]; decide

private theorem rescue1_8_first : value (rescue 1 8) 2523 = 849598700267779463943 := by decide +kernel
private theorem rescue1_8_next : value (rescue 1 8) 2524 = 873746541974699264332 := by decide +kernel
theorem rescue1_8 : Checked (rescue 1 8) := by
  refine ⟨(Lower6960.RescueSource.checked 1 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_8_first]; decide
  · rw [rescue1_8_first, rescue1_8_next]; decide

private theorem rescue1_9_first : value (rescue 1 9) 2523 = 240965461280919782211 := by decide +kernel
private theorem rescue1_9_next : value (rescue 1 9) 2524 = 247575737610859589738 := by decide +kernel
theorem rescue1_9 : Checked (rescue 1 9) := by
  refine ⟨(Lower6960.RescueSource.checked 1 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_9_first]; decide
  · rw [rescue1_9_first, rescue1_9_next]; decide

private theorem rescue1_10_first : value (rescue 1 10) 2523 = 2147498827865418165342 := by decide +kernel
private theorem rescue1_10_next : value (rescue 1 10) 2524 = 2213004161819893527007 := by decide +kernel
theorem rescue1_10 : Checked (rescue 1 10) := by
  refine ⟨(Lower6960.RescueSource.checked 1 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_10_first]; decide
  · rw [rescue1_10_first, rescue1_10_next]; decide

private theorem rescue1_11_first : value (rescue 1 11) 2523 = 10967061526424031726132 := by decide +kernel
private theorem rescue1_11_next : value (rescue 1 11) 2524 = 11309149146092295171369 := by decide +kernel
theorem rescue1_11 : Checked (rescue 1 11) := by
  refine ⟨(Lower6960.RescueSource.checked 1 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_11_first]; decide
  · rw [rescue1_11_first, rescue1_11_next]; decide

private theorem rescue1_12_first : value (rescue 1 12) 2523 = 7832673625264521642378 := by decide +kernel
private theorem rescue1_12_next : value (rescue 1 12) 2524 = 8059921376295043965493 := by decide +kernel
theorem rescue1_12 : Checked (rescue 1 12) := by
  refine ⟨(Lower6960.RescueSource.checked 1 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_12_first]; decide
  · rw [rescue1_12_first, rescue1_12_next]; decide

private theorem rescue1_13_first : value (rescue 1 13) 2523 = 30108956018993983611811 := by decide +kernel
private theorem rescue1_13_next : value (rescue 1 13) 2524 = 31006505338825302427259 := by decide +kernel
theorem rescue1_13 : Checked (rescue 1 13) := by
  refine ⟨(Lower6960.RescueSource.checked 1 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_13_first]; decide
  · rw [rescue1_13_first, rescue1_13_next]; decide

private theorem rescue1_14_first : value (rescue 1 14) 2523 = 252515913441853806015831 := by decide +kernel
private theorem rescue1_14_next : value (rescue 1 14) 2524 = 260158232647111460052111 := by decide +kernel
theorem rescue1_14 : Checked (rescue 1 14) := by
  refine ⟨(Lower6960.RescueSource.checked 1 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_14_first]; decide
  · rw [rescue1_14_first, rescue1_14_next]; decide

#print axioms rescue1_14
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks3

section Merged6967_R6966ProofFarRescueChecks4
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue1_15_first : value (rescue 1 15) 2523 = 297658992181589161289221 := by decide +kernel
private theorem rescue1_15_next : value (rescue 1 15) 2524 = 306666303657716368664988 := by decide +kernel
theorem rescue1_15 : Checked (rescue 1 15) := by
  refine ⟨(Lower6960.RescueSource.checked 1 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_15_first]; decide
  · rw [rescue1_15_first, rescue1_15_next]; decide

private theorem rescue1_16_first : value (rescue 1 16) 2523 = 1170766636276246440297688 := by decide +kernel
private theorem rescue1_16_next : value (rescue 1 16) 2524 = 1206473760120388049038460 := by decide +kernel
theorem rescue1_16 : Checked (rescue 1 16) := by
  refine ⟨(Lower6960.RescueSource.checked 1 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_16_first]; decide
  · rw [rescue1_16_first, rescue1_16_next]; decide

private theorem rescue2_0_first : value (rescue 2 0) 2523 = 5265137427050598132 := by decide +kernel
private theorem rescue2_0_next : value (rescue 2 0) 2524 = 5402789110189155822 := by decide +kernel
theorem rescue2_0 : Checked (rescue 2 0) := by
  refine ⟨(Lower6960.RescueSource.checked 2 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_0_first]; decide
  · rw [rescue2_0_first, rescue2_0_next]; decide

private theorem rescue2_1_first : value (rescue 2 1) 2523 = 7783917520006364876 := by decide +kernel
private theorem rescue2_1_next : value (rescue 2 1) 2524 = 7989379062171522828 := by decide +kernel
theorem rescue2_1 : Checked (rescue 2 1) := by
  refine ⟨(Lower6960.RescueSource.checked 2 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_1_first]; decide
  · rw [rescue2_1_first, rescue2_1_next]; decide

private theorem rescue2_2_first : value (rescue 2 2) 2523 = 11161170332029664874 := by decide +kernel
private theorem rescue2_2_next : value (rescue 2 2) 2524 = 11454194197516565944 := by decide +kernel
theorem rescue2_2 : Checked (rescue 2 2) := by
  refine ⟨(Lower6960.RescueSource.checked 2 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_2_first]; decide
  · rw [rescue2_2_first, rescue2_2_next]; decide

private theorem rescue2_3_first : value (rescue 2 3) 2523 = 16524804253035896651 := by decide +kernel
private theorem rescue2_3_next : value (rescue 2 3) 2524 = 16961299548082013648 := by decide +kernel
theorem rescue2_3 : Checked (rescue 2 3) := by
  refine ⟨(Lower6960.RescueSource.checked 2 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_3_first]; decide
  · rw [rescue2_3_first, rescue2_3_next]; decide

private theorem rescue2_4_first : value (rescue 2 4) 2523 = 25634831999391782808 := by decide +kernel
private theorem rescue2_4_next : value (rescue 2 4) 2524 = 26303362486135430743 := by decide +kernel
theorem rescue2_4 : Checked (rescue 2 4) := by
  refine ⟨(Lower6960.RescueSource.checked 2 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_4_first]; decide
  · rw [rescue2_4_first, rescue2_4_next]; decide

private theorem rescue2_5_first : value (rescue 2 5) 2523 = 32589331636920032367 := by decide +kernel
private theorem rescue2_5_next : value (rescue 2 5) 2524 = 33469763559409700726 := by decide +kernel
theorem rescue2_5 : Checked (rescue 2 5) := by
  refine ⟨(Lower6960.RescueSource.checked 2 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_5_first]; decide
  · rw [rescue2_5_first, rescue2_5_next]; decide

#print axioms rescue2_5
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks4

section Merged6967_R6966ProofFarRescueChecks5
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue2_6_first : value (rescue 2 6) 2523 = 58829123473184628714 := by decide +kernel
private theorem rescue2_6_next : value (rescue 2 6) 2524 = 60434256384167111665 := by decide +kernel
theorem rescue2_6 : Checked (rescue 2 6) := by
  refine ⟨(Lower6960.RescueSource.checked 2 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_6_first]; decide
  · rw [rescue2_6_first, rescue2_6_next]; decide

private theorem rescue2_7_first : value (rescue 2 7) 2523 = 129994625254114366638 := by decide +kernel
private theorem rescue2_7_next : value (rescue 2 7) 2524 = 133629842144170696303 := by decide +kernel
theorem rescue2_7 : Checked (rescue 2 7) := by
  refine ⟨(Lower6960.RescueSource.checked 2 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_7_first]; decide
  · rw [rescue2_7_first, rescue2_7_next]; decide

private theorem rescue2_8_first : value (rescue 2 8) 2523 = 455116298288554647855 := by decide +kernel
private theorem rescue2_8_next : value (rescue 2 8) 2524 = 468051059384248142887 := by decide +kernel
theorem rescue2_8 : Checked (rescue 2 8) := by
  refine ⟨(Lower6960.RescueSource.checked 2 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_8_first]; decide
  · rw [rescue2_8_first, rescue2_8_next]; decide

private theorem rescue2_9_first : value (rescue 2 9) 2523 = 130606278063138771636 := by decide +kernel
private theorem rescue2_9_next : value (rescue 2 9) 2524 = 134188095177075693204 := by decide +kernel
theorem rescue2_9 : Checked (rescue 2 9) := by
  refine ⟨(Lower6960.RescueSource.checked 2 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_9_first]; decide
  · rw [rescue2_9_first, rescue2_9_next]; decide

private theorem rescue2_10_first : value (rescue 2 10) 2523 = 1080760326510561934242 := by decide +kernel
private theorem rescue2_10_next : value (rescue 2 10) 2524 = 1113723572480253753155 := by decide +kernel
theorem rescue2_10 : Checked (rescue 2 10) := by
  refine ⟨(Lower6960.RescueSource.checked 2 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_10_first]; decide
  · rw [rescue2_10_first, rescue2_10_next]; decide

private theorem rescue2_11_first : value (rescue 2 11) 2523 = 5528609606370022766377 := by decide +kernel
private theorem rescue2_11_next : value (rescue 2 11) 2524 = 5701042841912867470195 := by decide +kernel
theorem rescue2_11 : Checked (rescue 2 11) := by
  refine ⟨(Lower6960.RescueSource.checked 2 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_11_first]; decide
  · rw [rescue2_11_first, rescue2_11_next]; decide

private theorem rescue2_12_first : value (rescue 2 12) 2523 = 4199903438702869895266 := by decide +kernel
private theorem rescue2_12_next : value (rescue 2 12) 2524 = 4323114627941737736857 := by decide +kernel
theorem rescue2_12 : Checked (rescue 2 12) := by
  refine ⟨(Lower6960.RescueSource.checked 2 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_12_first]; decide
  · rw [rescue2_12_first, rescue2_12_next]; decide

private theorem rescue2_13_first : value (rescue 2 13) 2523 = 16181012354818290583443 := by decide +kernel
private theorem rescue2_13_next : value (rescue 2 13) 2524 = 16663330573718804396246 := by decide +kernel
theorem rescue2_13 : Checked (rescue 2 13) := by
  refine ⟨(Lower6960.RescueSource.checked 2 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_13_first]; decide
  · rw [rescue2_13_first, rescue2_13_next]; decide

#print axioms rescue2_13
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks5

section Merged6967_R6966ProofFarRescueChecks6
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue2_14_first : value (rescue 2 14) 2523 = 135733630105529859494217 := by decide +kernel
private theorem rescue2_14_next : value (rescue 2 14) 2524 = 139841249048881042723980 := by decide +kernel
theorem rescue2_14 : Checked (rescue 2 14) := by
  refine ⟨(Lower6960.RescueSource.checked 2 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_14_first]; decide
  · rw [rescue2_14_first, rescue2_14_next]; decide

private theorem rescue2_15_first : value (rescue 2 15) 2523 = 159924267586221333876924 := by decide +kernel
private theorem rescue2_15_next : value (rescue 2 15) 2524 = 164763330520007685067632 := by decide +kernel
theorem rescue2_15 : Checked (rescue 2 15) := by
  refine ⟨(Lower6960.RescueSource.checked 2 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_15_first]; decide
  · rw [rescue2_15_first, rescue2_15_next]; decide

private theorem rescue2_16_first : value (rescue 2 16) 2523 = 629364272743055187098533 := by decide +kernel
private theorem rescue2_16_next : value (rescue 2 16) 2524 = 648557774243552322035405 := by decide +kernel
theorem rescue2_16 : Checked (rescue 2 16) := by
  refine ⟨(Lower6960.RescueSource.checked 2 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_16_first]; decide
  · rw [rescue2_16_first, rescue2_16_next]; decide

private theorem rescue3_0_first : value (rescue 3 0) 2523 = 602970617221879744 := by decide +kernel
private theorem rescue3_0_next : value (rescue 3 0) 2524 = 617620775585054936 := by decide +kernel
theorem rescue3_0 : Checked (rescue 3 0) := by
  refine ⟨(Lower6960.RescueSource.checked 3 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_0_first]; decide
  · rw [rescue3_0_first, rescue3_0_next]; decide

private theorem rescue3_1_first : value (rescue 3 1) 2523 = 899272124321665292 := by decide +kernel
private theorem rescue3_1_next : value (rescue 3 1) 2524 = 921430983248684304 := by decide +kernel
theorem rescue3_1 : Checked (rescue 3 1) := by
  refine ⟨(Lower6960.RescueSource.checked 3 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_1_first]; decide
  · rw [rescue3_1_first, rescue3_1_next]; decide

private theorem rescue3_2_first : value (rescue 3 2) 2523 = 1303559770590432453 := by decide +kernel
private theorem rescue3_2_next : value (rescue 3 2) 2524 = 1336083292271820232 := by decide +kernel
theorem rescue3_2 : Checked (rescue 3 2) := by
  refine ⟨(Lower6960.RescueSource.checked 3 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_2_first]; decide
  · rw [rescue3_2_first, rescue3_2_next]; decide

private theorem rescue3_3_first : value (rescue 3 3) 2523 = 1843425133366306869 := by decide +kernel
private theorem rescue3_3_next : value (rescue 3 3) 2524 = 1889931912781883221 := by decide +kernel
theorem rescue3_3 : Checked (rescue 3 3) := by
  refine ⟨(Lower6960.RescueSource.checked 3 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_3_first]; decide
  · rw [rescue3_3_first, rescue3_3_next]; decide

private theorem rescue3_4_first : value (rescue 3 4) 2523 = 3507050577921309156 := by decide +kernel
private theorem rescue3_4_next : value (rescue 3 4) 2524 = 3603204289564826008 := by decide +kernel
theorem rescue3_4 : Checked (rescue 3 4) := by
  refine ⟨(Lower6960.RescueSource.checked 3 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_4_first]; decide
  · rw [rescue3_4_first, rescue3_4_next]; decide

#print axioms rescue3_4
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks6

section Merged6967_R6966ProofFarRescueChecks7
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue3_5_first : value (rescue 3 5) 2523 = 7489641033536709828 := by decide +kernel
private theorem rescue3_5_next : value (rescue 3 5) 2524 = 7701169469592824291 := by decide +kernel
theorem rescue3_5 : Checked (rescue 3 5) := by
  refine ⟨(Lower6960.RescueSource.checked 3 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_5_first]; decide
  · rw [rescue3_5_first, rescue3_5_next]; decide

private theorem rescue3_6_first : value (rescue 3 6) 2523 = 11139783284838223848 := by decide +kernel
private theorem rescue3_6_next : value (rescue 3 6) 2524 = 11458059119749764004 := by decide +kernel
theorem rescue3_6 : Checked (rescue 3 6) := by
  refine ⟨(Lower6960.RescueSource.checked 3 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_6_first]; decide
  · rw [rescue3_6_first, rescue3_6_next]; decide

private theorem rescue3_7_first : value (rescue 3 7) 2523 = 30818535306158378565 := by decide +kernel
private theorem rescue3_7_next : value (rescue 3 7) 2524 = 31720936624811994515 := by decide +kernel
theorem rescue3_7 : Checked (rescue 3 7) := by
  refine ⟨(Lower6960.RescueSource.checked 3 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_7_first]; decide
  · rw [rescue3_7_first, rescue3_7_next]; decide

private theorem rescue3_8_first : value (rescue 3 8) 2523 = 77812039346312810523 := by decide +kernel
private theorem rescue3_8_next : value (rescue 3 8) 2524 = 80129248853554716784 := by decide +kernel
theorem rescue3_8 : Checked (rescue 3 8) := by
  refine ⟨(Lower6960.RescueSource.checked 3 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_8_first]; decide
  · rw [rescue3_8_first, rescue3_8_next]; decide

private theorem rescue3_9_first : value (rescue 3 9) 2523 = 22879193048418890232 := by decide +kernel
private theorem rescue3_9_next : value (rescue 3 9) 2524 = 23544073108231618966 := by decide +kernel
theorem rescue3_9 : Checked (rescue 3 9) := by
  refine ⟨(Lower6960.RescueSource.checked 3 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_9_first]; decide
  · rw [rescue3_9_first, rescue3_9_next]; decide

private theorem rescue3_10_first : value (rescue 3 10) 2523 = 125333744100732112296 := by decide +kernel
private theorem rescue3_10_next : value (rescue 3 10) 2524 = 128791231602917188148 := by decide +kernel
theorem rescue3_10 : Checked (rescue 3 10) := by
  refine ⟨(Lower6960.RescueSource.checked 3 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_10_first]; decide
  · rw [rescue3_10_first, rescue3_10_next]; decide

private theorem rescue3_11_first : value (rescue 3 11) 2523 = 681552305100395858232 := by decide +kernel
private theorem rescue3_11_next : value (rescue 3 11) 2524 = 700780913432257764516 := by decide +kernel
theorem rescue3_11 : Checked (rescue 3 11) := by
  refine ⟨(Lower6960.RescueSource.checked 3 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_11_first]; decide
  · rw [rescue3_11_first, rescue3_11_next]; decide

private theorem rescue3_12_first : value (rescue 3 12) 2523 = 725494617530151166212 := by decide +kernel
private theorem rescue3_12_next : value (rescue 3 12) 2524 = 747906350533965510656 := by decide +kernel
theorem rescue3_12 : Checked (rescue 3 12) := by
  refine ⟨(Lower6960.RescueSource.checked 3 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_12_first]; decide
  · rw [rescue3_12_first, rescue3_12_next]; decide

#print axioms rescue3_12
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks7

section Merged6967_R6966ProofFarRescueChecks8
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue3_13_first : value (rescue 3 13) 2523 = 3491925422840167442078 := by decide +kernel
private theorem rescue3_13_next : value (rescue 3 13) 2524 = 3601630206041551229144 := by decide +kernel
theorem rescue3_13 : Checked (rescue 3 13) := by
  refine ⟨(Lower6960.RescueSource.checked 3 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_13_first]; decide
  · rw [rescue3_13_first, rescue3_13_next]; decide

private theorem rescue3_14_first : value (rescue 3 14) 2523 = 29925491567114913788052 := by decide +kernel
private theorem rescue3_14_next : value (rescue 3 14) 2524 = 30881579269098215905296 := by decide +kernel
theorem rescue3_14 : Checked (rescue 3 14) := by
  refine ⟨(Lower6960.RescueSource.checked 3 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_14_first]; decide
  · rw [rescue3_14_first, rescue3_14_next]; decide

private theorem rescue3_15_first : value (rescue 3 15) 2523 = 31531713406041263088888 := by decide +kernel
private theorem rescue3_15_next : value (rescue 3 15) 2524 = 32539250072611095453888 := by decide +kernel
theorem rescue3_15 : Checked (rescue 3 15) := by
  refine ⟨(Lower6960.RescueSource.checked 3 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_15_first]; decide
  · rw [rescue3_15_first, rescue3_15_next]; decide

private theorem rescue3_16_first : value (rescue 3 16) 2523 = 141229381504403034243615 := by decide +kernel
private theorem rescue3_16_next : value (rescue 3 16) 2524 = 145780220505190559257495 := by decide +kernel
theorem rescue3_16 : Checked (rescue 3 16) := by
  refine ⟨(Lower6960.RescueSource.checked 3 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_16_first]; decide
  · rw [rescue3_16_first, rescue3_16_next]; decide

#print axioms rescue3_16
end Research6966.FarSourceData

end Merged6967_R6966ProofFarRescueChecks8

section Merged6967_R6966ProofHelperRescueChecked0
set_option Elab.async false


















set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step0 : Request := ⟨⟨⟨913,1274,274,70667⟩,22869055897600,72278016338⟩,0,2,1,308303⟩
private theorem pos0_0 : Positive step0 2317 2317 := by decide +kernel
private theorem pos0_1 : Positive step0 2318 2319 := by decide +kernel
private theorem pos0_2 : Positive step0 2320 2325 := by decide +kernel
private theorem pos0_3 : Positive step0 2326 2342 := by decide +kernel
private theorem pos0_4 : Positive step0 2343 2390 := by decide +kernel
private theorem pos0_5 : Positive step0 2391 2522 := by decide +kernel
theorem step0_verified : Checked step0 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1274_274, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos0_0, by decide, by decide, pos0_1, by decide, by decide, pos0_2, by decide, by decide, pos0_3, by decide, by decide, pos0_4, by decide, by decide, pos0_5, rfl⟩⟩⟩
def step1 : Request := ⟨⟨⟨1007,1405,302,77045⟩,30653695393792,106799856912⟩,1,2,1,308303⟩
private theorem pos1_0 : Positive step1 2317 2317 := by decide +kernel
private theorem pos1_1 : Positive step1 2318 2319 := by decide +kernel
private theorem pos1_2 : Positive step1 2320 2325 := by decide +kernel
private theorem pos1_3 : Positive step1 2326 2342 := by decide +kernel
private theorem pos1_4 : Positive step1 2343 2390 := by decide +kernel
private theorem pos1_5 : Positive step1 2391 2522 := by decide +kernel
theorem step1_verified : Checked step1 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1405_302, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos1_0, by decide, by decide, pos1_1, by decide, by decide, pos1_2, by decide, by decide, pos1_3, by decide, by decide, pos1_4, by decide, by decide, pos1_5, rfl⟩⟩⟩
def step2 : Request := ⟨⟨⟨1156,1613,347,81404⟩,46376998666240,185502762679⟩,2,2,1,308303⟩
private theorem pos2_0 : Positive step2 2317 2317 := by decide +kernel
private theorem pos2_1 : Positive step2 2318 2319 := by decide +kernel
private theorem pos2_2 : Positive step2 2320 2325 := by decide +kernel
private theorem pos2_3 : Positive step2 2326 2342 := by decide +kernel
private theorem pos2_4 : Positive step2 2343 2389 := by decide +kernel
private theorem pos2_5 : Positive step2 2390 2519 := by decide +kernel
private theorem pos2_6 : Positive step2 2520 2522 := by decide +kernel
theorem step2_verified : Checked step2 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1613_347, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2389, 2519, 2522], ⟨by decide, by decide, pos2_0, by decide, by decide, pos2_1, by decide, by decide, pos2_2, by decide, by decide, pos2_3, by decide, by decide, pos2_4, by decide, by decide, pos2_5, by decide, by decide, pos2_6, rfl⟩⟩⟩
def step3 : Request := ⟨⟨⟨1482,2068,445,85215⟩,97653165391872,500730734846⟩,3,2,1,308303⟩
private theorem pos3_0 : Positive step3 2317 2317 := by decide +kernel
private theorem pos3_1 : Positive step3 2318 2319 := by decide +kernel
private theorem pos3_2 : Positive step3 2320 2325 := by decide +kernel
private theorem pos3_3 : Positive step3 2326 2341 := by decide +kernel
private theorem pos3_4 : Positive step3 2342 2385 := by decide +kernel
private theorem pos3_5 : Positive step3 2386 2506 := by decide +kernel
private theorem pos3_6 : Positive step3 2507 2522 := by decide +kernel
theorem step3_verified : Checked step3 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2068_445, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2506, 2522], ⟨by decide, by decide, pos3_0, by decide, by decide, pos3_1, by decide, by decide, pos3_2, by decide, by decide, pos3_3, by decide, by decide, pos3_4, by decide, by decide, pos3_5, by decide, by decide, pos3_6, rfl⟩⟩⟩
def step4 : Request := ⟨⟨⟨1704,2378,511,104484⟩,148231870742528,874078075528⟩,6,2,1,308303⟩
private theorem pos4_0 : Positive step4 2317 2317 := by decide +kernel
private theorem pos4_1 : Positive step4 2318 2319 := by decide +kernel
private theorem pos4_2 : Positive step4 2320 2325 := by decide +kernel
private theorem pos4_3 : Positive step4 2326 2341 := by decide +kernel
private theorem pos4_4 : Positive step4 2342 2385 := by decide +kernel
private theorem pos4_5 : Positive step4 2386 2504 := by decide +kernel
private theorem pos4_6 : Positive step4 2505 2522 := by decide +kernel
theorem step4_verified : Checked step4 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2378_511, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2504, 2522], ⟨by decide, by decide, pos4_0, by decide, by decide, pos4_1, by decide, by decide, pos4_2, by decide, by decide, pos4_3, by decide, by decide, pos4_4, by decide, by decide, pos4_5, by decide, by decide, pos4_6, rfl⟩⟩⟩
def step5 : Request := ⟨⟨⟨2093,2921,628,116994⟩,274660672143360,1989358623137⟩,8,2,1,308303⟩
private theorem pos5_0 : Positive step5 2317 2317 := by decide +kernel
private theorem pos5_1 : Positive step5 2318 2319 := by decide +kernel
private theorem pos5_2 : Positive step5 2320 2325 := by decide +kernel
private theorem pos5_3 : Positive step5 2326 2341 := by decide +kernel
private theorem pos5_4 : Positive step5 2342 2384 := by decide +kernel
private theorem pos5_5 : Positive step5 2385 2500 := by decide +kernel
private theorem pos5_6 : Positive step5 2501 2522 := by decide +kernel
theorem step5_verified : Checked step5 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2921_628, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos5_0, by decide, by decide, pos5_1, by decide, by decide, pos5_2, by decide, by decide, pos5_3, by decide, by decide, pos5_4, by decide, by decide, pos5_5, by decide, by decide, pos5_6, rfl⟩⟩⟩
def step6 : Request := ⟨⟨⟨2093,2921,628,146327⟩,274660672143360,1989358623137⟩,12,2,1,308303⟩
private theorem pos6_0 : Positive step6 2317 2317 := by decide +kernel
private theorem pos6_1 : Positive step6 2318 2319 := by decide +kernel
private theorem pos6_2 : Positive step6 2320 2325 := by decide +kernel
private theorem pos6_3 : Positive step6 2326 2341 := by decide +kernel
private theorem pos6_4 : Positive step6 2342 2384 := by decide +kernel
private theorem pos6_5 : Positive step6 2385 2500 := by decide +kernel
private theorem pos6_6 : Positive step6 2501 2522 := by decide +kernel
theorem step6_verified : Checked step6 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2921_628, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos6_0, by decide, by decide, pos6_1, by decide, by decide, pos6_2, by decide, by decide, pos6_3, by decide, by decide, pos6_4, by decide, by decide, pos6_5, by decide, by decide, pos6_6, rfl⟩⟩⟩
def step7 : Request := ⟨⟨⟨2538,3542,761,179489⟩,489286602588160,4296679719083⟩,17,2,1,308303⟩
private theorem pos7_0 : Positive step7 2317 2317 := by decide +kernel
private theorem pos7_1 : Positive step7 2318 2319 := by decide +kernel
private theorem pos7_2 : Positive step7 2320 2325 := by decide +kernel
private theorem pos7_3 : Positive step7 2326 2341 := by decide +kernel
private theorem pos7_4 : Positive step7 2342 2384 := by decide +kernel
private theorem pos7_5 : Positive step7 2385 2499 := by decide +kernel
private theorem pos7_6 : Positive step7 2500 2522 := by decide +kernel
theorem step7_verified : Checked step7 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3542_761, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2499, 2522], ⟨by decide, by decide, pos7_0, by decide, by decide, pos7_1, by decide, by decide, pos7_2, by decide, by decide, pos7_3, by decide, by decide, pos7_4, by decide, by decide, pos7_5, by decide, by decide, pos7_6, rfl⟩⟩⟩
def step8 : Request := ⟨⟨⟨1940,2707,582,219253⟩,218735576350720,1467723847114⟩,16,2,1,308303⟩
private theorem pos8_0 : Positive step8 2317 2317 := by decide +kernel
private theorem pos8_1 : Positive step8 2318 2319 := by decide +kernel
private theorem pos8_2 : Positive step8 2320 2325 := by decide +kernel
private theorem pos8_3 : Positive step8 2326 2341 := by decide +kernel
private theorem pos8_4 : Positive step8 2342 2384 := by decide +kernel
private theorem pos8_5 : Positive step8 2385 2501 := by decide +kernel
private theorem pos8_6 : Positive step8 2502 2522 := by decide +kernel
theorem step8_verified : Checked step8 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2707_582, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos8_0, by decide, by decide, pos8_1, by decide, by decide, pos8_2, by decide, by decide, pos8_3, by decide, by decide, pos8_4, by decide, by decide, pos8_5, by decide, by decide, pos8_6, rfl⟩⟩⟩
def step9 : Request := ⟨⟨⟨3028,4226,908,173742⟩,830714806272000,8703717248479⟩,17,2,1,308303⟩
private theorem pos9_0 : Positive step9 2317 2317 := by decide +kernel
private theorem pos9_1 : Positive step9 2318 2319 := by decide +kernel
private theorem pos9_2 : Positive step9 2320 2325 := by decide +kernel
private theorem pos9_3 : Positive step9 2326 2341 := by decide +kernel
private theorem pos9_4 : Positive step9 2342 2383 := by decide +kernel
private theorem pos9_5 : Positive step9 2384 2496 := by decide +kernel
private theorem pos9_6 : Positive step9 2497 2522 := by decide +kernel
theorem step9_verified : Checked step9 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment4226_908, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2383, 2496, 2522], ⟨by decide, by decide, pos9_0, by decide, by decide, pos9_1, by decide, by decide, pos9_2, by decide, by decide, pos9_3, by decide, by decide, pos9_4, by decide, by decide, pos9_5, by decide, by decide, pos9_6, rfl⟩⟩⟩
def step10 : Request := ⟨⟨⟨3877,5411,1163,224258⟩,1743568608690176,23389476977098⟩,25,2,1,308303⟩
private theorem pos10_0 : Positive step10 2317 2317 := by decide +kernel
private theorem pos10_1 : Positive step10 2318 2319 := by decide +kernel
private theorem pos10_2 : Positive step10 2320 2324 := by decide +kernel
private theorem pos10_3 : Positive step10 2325 2338 := by decide +kernel
private theorem pos10_4 : Positive step10 2339 2375 := by decide +kernel
private theorem pos10_5 : Positive step10 2376 2473 := by decide +kernel
private theorem pos10_6 : Positive step10 2474 2522 := by decide +kernel
theorem step10_verified : Checked step10 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5411_1163, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos10_0, by decide, by decide, pos10_1, by decide, by decide, pos10_2, by decide, by decide, pos10_3, by decide, by decide, pos10_4, by decide, by decide, pos10_5, by decide, by decide, pos10_6, rfl⟩⟩⟩
def step11 : Request := ⟨⟨⟨1948,2719,584,277594⟩,221335049994240,1492745996263⟩,18,2,1,308303⟩
private theorem pos11_0 : Positive step11 2317 2317 := by decide +kernel
private theorem pos11_1 : Positive step11 2318 2319 := by decide +kernel
private theorem pos11_2 : Positive step11 2320 2325 := by decide +kernel
private theorem pos11_3 : Positive step11 2326 2341 := by decide +kernel
private theorem pos11_4 : Positive step11 2342 2384 := by decide +kernel
private theorem pos11_5 : Positive step11 2385 2501 := by decide +kernel
private theorem pos11_6 : Positive step11 2502 2522 := by decide +kernel
theorem step11_verified : Checked step11 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2719_584, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos11_0, by decide, by decide, pos11_1, by decide, by decide, pos11_2, by decide, by decide, pos11_3, by decide, by decide, pos11_4, by decide, by decide, pos11_5, by decide, by decide, pos11_6, rfl⟩⟩⟩
def step12 : Request := ⟨⟨⟨2251,3141,675,343663⟩,341464862162944,2658401808400⟩,23,2,1,308303⟩
private theorem pos12_0 : Positive step12 2317 2317 := by decide +kernel
private theorem pos12_1 : Positive step12 2318 2319 := by decide +kernel
private theorem pos12_2 : Positive step12 2320 2325 := by decide +kernel
private theorem pos12_3 : Positive step12 2326 2341 := by decide +kernel
private theorem pos12_4 : Positive step12 2342 2384 := by decide +kernel
private theorem pos12_5 : Positive step12 2385 2500 := by decide +kernel
private theorem pos12_6 : Positive step12 2501 2522 := by decide +kernel
theorem step12_verified : Checked step12 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3141_675, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos12_0, by decide, by decide, pos12_1, by decide, by decide, pos12_2, by decide, by decide, pos12_3, by decide, by decide, pos12_4, by decide, by decide, pos12_5, by decide, by decide, pos12_6, rfl⟩⟩⟩
def step13 : Request := ⟨⟨⟨4135,5771,1240,280759⟩,2114656146554880,30253081279145⟩,33,2,1,308303⟩
private theorem pos13_0 : Positive step13 2317 2317 := by decide +kernel
private theorem pos13_1 : Positive step13 2318 2319 := by decide +kernel
private theorem pos13_2 : Positive step13 2320 2324 := by decide +kernel
private theorem pos13_3 : Positive step13 2325 2338 := by decide +kernel
private theorem pos13_4 : Positive step13 2339 2375 := by decide +kernel
private theorem pos13_5 : Positive step13 2376 2473 := by decide +kernel
private theorem pos13_6 : Positive step13 2474 2522 := by decide +kernel
theorem step13_verified : Checked step13 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5771_1240, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos13_0, by decide, by decide, pos13_1, by decide, by decide, pos13_2, by decide, by decide, pos13_3, by decide, by decide, pos13_4, by decide, by decide, pos13_5, by decide, by decide, pos13_6, rfl⟩⟩⟩
def step14 : Request := ⟨⟨⟨4774,6663,1432,274830⟩,3254472040251392,53757553058289⟩,33,2,1,308303⟩
private theorem pos14_0 : Positive step14 2317 2317 := by decide +kernel
private theorem pos14_1 : Positive step14 2318 2319 := by decide +kernel
private theorem pos14_2 : Positive step14 2320 2324 := by decide +kernel
private theorem pos14_3 : Positive step14 2325 2338 := by decide +kernel
private theorem pos14_4 : Positive step14 2339 2375 := by decide +kernel
private theorem pos14_5 : Positive step14 2376 2473 := by decide +kernel
private theorem pos14_6 : Positive step14 2474 2522 := by decide +kernel
theorem step14_verified : Checked step14 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment6663_1432, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos14_0, by decide, by decide, pos14_1, by decide, by decide, pos14_2, by decide, by decide, pos14_3, by decide, by decide, pos14_4, by decide, by decide, pos14_5, by decide, by decide, pos14_6, rfl⟩⟩⟩
def step15 : Request := ⟨⟨⟨2768,3863,803,307658⟩,618805432156160,5922866008688⟩,24,2,1,308303⟩
private theorem pos15_0 : Positive step15 2317 2317 := by decide +kernel
private theorem pos15_1 : Positive step15 2318 2319 := by decide +kernel
private theorem pos15_2 : Positive step15 2320 2325 := by decide +kernel
private theorem pos15_3 : Positive step15 2326 2341 := by decide +kernel
private theorem pos15_4 : Positive step15 2342 2385 := by decide +kernel
private theorem pos15_5 : Positive step15 2386 2507 := by decide +kernel
private theorem pos15_6 : Positive step15 2508 2522 := by decide +kernel
theorem step15_verified : Checked step15 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3863_803, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2507, 2522], ⟨by decide, by decide, pos15_0, by decide, by decide, pos15_1, by decide, by decide, pos15_2, by decide, by decide, pos15_3, by decide, by decide, pos15_4, by decide, by decide, pos15_5, by decide, by decide, pos15_6, rfl⟩⟩⟩
def step16 : Request := ⟨⟨⟨3578,4993,1073,448025⟩,1370321365237760,16957563831998⟩,40,2,1,308303⟩
private theorem pos16_0 : Positive step16 2317 2317 := by decide +kernel
private theorem pos16_1 : Positive step16 2318 2319 := by decide +kernel
private theorem pos16_2 : Positive step16 2320 2324 := by decide +kernel
private theorem pos16_3 : Positive step16 2325 2338 := by decide +kernel
private theorem pos16_4 : Positive step16 2339 2375 := by decide +kernel
private theorem pos16_5 : Positive step16 2376 2474 := by decide +kernel
private theorem pos16_6 : Positive step16 2475 2522 := by decide +kernel
theorem step16_verified : Checked step16 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment4993_1073, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2474, 2522], ⟨by decide, by decide, pos16_0, by decide, by decide, pos16_1, by decide, by decide, pos16_2, by decide, by decide, pos16_3, by decide, by decide, pos16_4, by decide, by decide, pos16_5, by decide, by decide, pos16_6, rfl⟩⟩⟩
def step17 : Request := ⟨⟨⟨898,1253,269,68441⟩,21731605217280,67542002002⟩,0,2,2,308232⟩
private theorem pos17_0 : Positive step17 2317 2317 := by decide +kernel
private theorem pos17_1 : Positive step17 2318 2319 := by decide +kernel
private theorem pos17_2 : Positive step17 2320 2325 := by decide +kernel
private theorem pos17_3 : Positive step17 2326 2342 := by decide +kernel
private theorem pos17_4 : Positive step17 2343 2390 := by decide +kernel
private theorem pos17_5 : Positive step17 2391 2522 := by decide +kernel
theorem step17_verified : Checked step17 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1253_269, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos17_0, by decide, by decide, pos17_1, by decide, by decide, pos17_2, by decide, by decide, pos17_3, by decide, by decide, pos17_4, by decide, by decide, pos17_5, rfl⟩⟩⟩
def step18 : Request := ⟨⟨⟨1007,1405,302,73764⟩,30653695393792,106799856912⟩,1,2,2,308232⟩
private theorem pos18_0 : Positive step18 2317 2317 := by decide +kernel
private theorem pos18_1 : Positive step18 2318 2319 := by decide +kernel
private theorem pos18_2 : Positive step18 2320 2325 := by decide +kernel
private theorem pos18_3 : Positive step18 2326 2342 := by decide +kernel
private theorem pos18_4 : Positive step18 2343 2390 := by decide +kernel
private theorem pos18_5 : Positive step18 2391 2522 := by decide +kernel
theorem step18_verified : Checked step18 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1405_302, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos18_0, by decide, by decide, pos18_1, by decide, by decide, pos18_2, by decide, by decide, pos18_3, by decide, by decide, pos18_4, by decide, by decide, pos18_5, rfl⟩⟩⟩
def step19 : Request := ⟨⟨⟨1217,1698,365,85182⟩,54066727616512,227606727472⟩,3,2,2,308232⟩
private theorem pos19_0 : Positive step19 2317 2317 := by decide +kernel
private theorem pos19_1 : Positive step19 2318 2319 := by decide +kernel
private theorem pos19_2 : Positive step19 2320 2325 := by decide +kernel
private theorem pos19_3 : Positive step19 2326 2341 := by decide +kernel
private theorem pos19_4 : Positive step19 2342 2386 := by decide +kernel
private theorem pos19_5 : Positive step19 2387 2511 := by decide +kernel
private theorem pos19_6 : Positive step19 2512 2522 := by decide +kernel
theorem step19_verified : Checked step19 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1698_365, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2386, 2511, 2522], ⟨by decide, by decide, pos19_0, by decide, by decide, pos19_1, by decide, by decide, pos19_2, by decide, by decide, pos19_3, by decide, by decide, pos19_4, by decide, by decide, pos19_5, by decide, by decide, pos19_6, rfl⟩⟩⟩
def step20 : Request := ⟨⟨⟨1663,2321,499,93728⟩,137859039232000,793615206921⟩,5,2,2,308232⟩
private theorem pos20_0 : Positive step20 2317 2317 := by decide +kernel
private theorem pos20_1 : Positive step20 2318 2319 := by decide +kernel
private theorem pos20_2 : Positive step20 2320 2325 := by decide +kernel
private theorem pos20_3 : Positive step20 2326 2341 := by decide +kernel
private theorem pos20_4 : Positive step20 2342 2385 := by decide +kernel
private theorem pos20_5 : Positive step20 2386 2505 := by decide +kernel
private theorem pos20_6 : Positive step20 2506 2522 := by decide +kernel
theorem step20_verified : Checked step20 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2321_499, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2505, 2522], ⟨by decide, by decide, pos20_0, by decide, by decide, pos20_1, by decide, by decide, pos20_2, by decide, by decide, pos20_3, by decide, by decide, pos20_4, by decide, by decide, pos20_5, by decide, by decide, pos20_6, rfl⟩⟩⟩
def step21 : Request := ⟨⟨⟨1838,2565,551,99806⟩,185938796871680,1182570018933⟩,6,2,2,308232⟩
private theorem pos21_0 : Positive step21 2317 2317 := by decide +kernel
private theorem pos21_1 : Positive step21 2318 2319 := by decide +kernel
private theorem pos21_2 : Positive step21 2320 2325 := by decide +kernel
private theorem pos21_3 : Positive step21 2326 2341 := by decide +kernel
private theorem pos21_4 : Positive step21 2342 2384 := by decide +kernel
private theorem pos21_5 : Positive step21 2385 2501 := by decide +kernel
private theorem pos21_6 : Positive step21 2502 2522 := by decide +kernel
theorem step21_verified : Checked step21 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2565_551, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos21_0, by decide, by decide, pos21_1, by decide, by decide, pos21_2, by decide, by decide, pos21_3, by decide, by decide, pos21_4, by decide, by decide, pos21_5, by decide, by decide, pos21_6, rfl⟩⟩⟩
def step22 : Request := ⟨⟨⟨2032,2836,610,111856⟩,251451338391552,1768487180381⟩,8,2,2,308232⟩
private theorem pos22_0 : Positive step22 2317 2317 := by decide +kernel
private theorem pos22_1 : Positive step22 2318 2319 := by decide +kernel
private theorem pos22_2 : Positive step22 2320 2325 := by decide +kernel
private theorem pos22_3 : Positive step22 2326 2341 := by decide +kernel
private theorem pos22_4 : Positive step22 2342 2384 := by decide +kernel
private theorem pos22_5 : Positive step22 2385 2500 := by decide +kernel
private theorem pos22_6 : Positive step22 2501 2522 := by decide +kernel
theorem step22_verified : Checked step22 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2836_610, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos22_0, by decide, by decide, pos22_1, by decide, by decide, pos22_2, by decide, by decide, pos22_3, by decide, by decide, pos22_4, by decide, by decide, pos22_5, by decide, by decide, pos22_6, rfl⟩⟩⟩
def step23 : Request := ⟨⟨⟨2093,2921,628,140098⟩,274660672143360,1989358623137⟩,12,2,2,308232⟩
private theorem pos23_0 : Positive step23 2317 2317 := by decide +kernel
private theorem pos23_1 : Positive step23 2318 2319 := by decide +kernel
private theorem pos23_2 : Positive step23 2320 2325 := by decide +kernel
private theorem pos23_3 : Positive step23 2326 2341 := by decide +kernel
private theorem pos23_4 : Positive step23 2342 2384 := by decide +kernel
private theorem pos23_5 : Positive step23 2385 2500 := by decide +kernel
private theorem pos23_6 : Positive step23 2501 2522 := by decide +kernel
theorem step23_verified : Checked step23 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2921_628, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos23_0, by decide, by decide, pos23_1, by decide, by decide, pos23_2, by decide, by decide, pos23_3, by decide, by decide, pos23_4, by decide, by decide, pos23_5, by decide, by decide, pos23_6, rfl⟩⟩⟩

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueChecked0

section Merged6967_R6966ProofHelperRescueChecked1
set_option Elab.async false
















set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step24 : Request := ⟨⟨⟨2558,3570,767,148437⟩,500939249156096,4434008324066⟩,14,2,2,308232⟩
private theorem pos24_0 : Positive step24 2317 2317 := by decide +kernel
private theorem pos24_1 : Positive step24 2318 2319 := by decide +kernel
private theorem pos24_2 : Positive step24 2320 2325 := by decide +kernel
private theorem pos24_3 : Positive step24 2326 2341 := by decide +kernel
private theorem pos24_4 : Positive step24 2342 2384 := by decide +kernel
private theorem pos24_5 : Positive step24 2385 2499 := by decide +kernel
private theorem pos24_6 : Positive step24 2500 2522 := by decide +kernel
theorem step24_verified : Checked step24 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3570_767, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2499, 2522], ⟨by decide, by decide, pos24_0, by decide, by decide, pos24_1, by decide, by decide, pos24_2, by decide, by decide, pos24_3, by decide, by decide, pos24_4, by decide, by decide, pos24_5, by decide, by decide, pos24_6, rfl⟩⟩⟩
def step25 : Request := ⟨⟨⟨2589,3613,777,179361⟩,519720973893632,4654956318519⟩,18,2,2,308232⟩
private theorem pos25_0 : Positive step25 2317 2317 := by decide +kernel
private theorem pos25_1 : Positive step25 2318 2319 := by decide +kernel
private theorem pos25_2 : Positive step25 2320 2325 := by decide +kernel
private theorem pos25_3 : Positive step25 2326 2341 := by decide +kernel
private theorem pos25_4 : Positive step25 2342 2384 := by decide +kernel
private theorem pos25_5 : Positive step25 2385 2499 := by decide +kernel
private theorem pos25_6 : Positive step25 2500 2522 := by decide +kernel
theorem step25_verified : Checked step25 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3613_777, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2499, 2522], ⟨by decide, by decide, pos25_0, by decide, by decide, pos25_1, by decide, by decide, pos25_2, by decide, by decide, pos25_3, by decide, by decide, pos25_4, by decide, by decide, pos25_5, by decide, by decide, pos25_6, rfl⟩⟩⟩
def step26 : Request := ⟨⟨⟨2013,2809,604,218012⟩,244377702891520,1701721319759⟩,17,2,2,308232⟩
private theorem pos26_0 : Positive step26 2317 2317 := by decide +kernel
private theorem pos26_1 : Positive step26 2318 2319 := by decide +kernel
private theorem pos26_2 : Positive step26 2320 2325 := by decide +kernel
private theorem pos26_3 : Positive step26 2326 2341 := by decide +kernel
private theorem pos26_4 : Positive step26 2342 2384 := by decide +kernel
private theorem pos26_5 : Positive step26 2385 2500 := by decide +kernel
private theorem pos26_6 : Positive step26 2501 2522 := by decide +kernel
theorem step26_verified : Checked step26 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2809_604, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos26_0, by decide, by decide, pos26_1, by decide, by decide, pos26_2, by decide, by decide, pos26_3, by decide, by decide, pos26_4, by decide, by decide, pos26_5, by decide, by decide, pos26_6, rfl⟩⟩⟩
def step27 : Request := ⟨⟨⟨3700,5164,1110,215130⟩,1515691726602240,19405049205455⟩,25,2,2,308232⟩
private theorem pos27_0 : Positive step27 2317 2317 := by decide +kernel
private theorem pos27_1 : Positive step27 2318 2319 := by decide +kernel
private theorem pos27_2 : Positive step27 2320 2324 := by decide +kernel
private theorem pos27_3 : Positive step27 2325 2338 := by decide +kernel
private theorem pos27_4 : Positive step27 2339 2375 := by decide +kernel
private theorem pos27_5 : Positive step27 2376 2474 := by decide +kernel
private theorem pos27_6 : Positive step27 2475 2522 := by decide +kernel
theorem step27_verified : Checked step27 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5164_1110, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2474, 2522], ⟨by decide, by decide, pos27_0, by decide, by decide, pos27_1, by decide, by decide, pos27_2, by decide, by decide, pos27_3, by decide, by decide, pos27_4, by decide, by decide, pos27_5, by decide, by decide, pos27_6, rfl⟩⟩⟩
def step28 : Request := ⟨⟨⟨4271,5961,1281,238935⟩,2330461376872448,34440377265092⟩,29,2,2,308232⟩
private theorem pos28_0 : Positive step28 2317 2317 := by decide +kernel
private theorem pos28_1 : Positive step28 2318 2319 := by decide +kernel
private theorem pos28_2 : Positive step28 2320 2324 := by decide +kernel
private theorem pos28_3 : Positive step28 2325 2338 := by decide +kernel
private theorem pos28_4 : Positive step28 2339 2375 := by decide +kernel
private theorem pos28_5 : Positive step28 2376 2473 := by decide +kernel
private theorem pos28_6 : Positive step28 2474 2522 := by decide +kernel
theorem step28_verified : Checked step28 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5961_1281, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos28_0, by decide, by decide, pos28_1, by decide, by decide, pos28_2, by decide, by decide, pos28_3, by decide, by decide, pos28_4, by decide, by decide, pos28_5, by decide, by decide, pos28_6, rfl⟩⟩⟩
def step29 : Request := ⟨⟨⟨2276,3176,683,318055⟩,353158876889088,2780324254692⟩,23,2,2,308232⟩
private theorem pos29_0 : Positive step29 2317 2317 := by decide +kernel
private theorem pos29_1 : Positive step29 2318 2319 := by decide +kernel
private theorem pos29_2 : Positive step29 2320 2325 := by decide +kernel
private theorem pos29_3 : Positive step29 2326 2341 := by decide +kernel
private theorem pos29_4 : Positive step29 2342 2384 := by decide +kernel
private theorem pos29_5 : Positive step29 2385 2500 := by decide +kernel
private theorem pos29_6 : Positive step29 2501 2522 := by decide +kernel
theorem step29_verified : Checked step29 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3176_683, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos29_0, by decide, by decide, pos29_1, by decide, by decide, pos29_2, by decide, by decide, pos29_3, by decide, by decide, pos29_4, by decide, by decide, pos29_5, by decide, by decide, pos29_6, rfl⟩⟩⟩
def step30 : Request := ⟨⟨⟨5426,7573,1628,332558⟩,4778673736777728,89712770855631⟩,44,2,2,308232⟩
private theorem pos30_0 : Positive step30 2317 2317 := by decide +kernel
private theorem pos30_1 : Positive step30 2318 2319 := by decide +kernel
private theorem pos30_2 : Positive step30 2320 2324 := by decide +kernel
private theorem pos30_3 : Positive step30 2325 2338 := by decide +kernel
private theorem pos30_4 : Positive step30 2339 2375 := by decide +kernel
private theorem pos30_5 : Positive step30 2376 2473 := by decide +kernel
private theorem pos30_6 : Positive step30 2474 2522 := by decide +kernel
theorem step30_verified : Checked step30 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment7573_1628, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos30_0, by decide, by decide, pos30_1, by decide, by decide, pos30_2, by decide, by decide, pos30_3, by decide, by decide, pos30_4, by decide, by decide, pos30_5, by decide, by decide, pos30_6, rfl⟩⟩⟩
def step31 : Request := ⟨⟨⟨2273,3172,682,363472⟩,351726004862976,2765910980015⟩,24,2,2,308232⟩
private theorem pos31_0 : Positive step31 2317 2317 := by decide +kernel
private theorem pos31_1 : Positive step31 2318 2319 := by decide +kernel
private theorem pos31_2 : Positive step31 2320 2325 := by decide +kernel
private theorem pos31_3 : Positive step31 2326 2341 := by decide +kernel
private theorem pos31_4 : Positive step31 2342 2384 := by decide +kernel
private theorem pos31_5 : Positive step31 2385 2500 := by decide +kernel
private theorem pos31_6 : Positive step31 2501 2522 := by decide +kernel
theorem step31_verified : Checked step31 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3172_682, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos31_0, by decide, by decide, pos31_1, by decide, by decide, pos31_2, by decide, by decide, pos31_3, by decide, by decide, pos31_4, by decide, by decide, pos31_5, by decide, by decide, pos31_6, rfl⟩⟩⟩
def step32 : Request := ⟨⟨⟨4270,5959,1281,466848⟩,2329241279791104,34403208852529⟩,48,2,2,308232⟩
private theorem pos32_0 : Positive step32 2317 2317 := by decide +kernel
private theorem pos32_1 : Positive step32 2318 2319 := by decide +kernel
private theorem pos32_2 : Positive step32 2320 2324 := by decide +kernel
private theorem pos32_3 : Positive step32 2325 2338 := by decide +kernel
private theorem pos32_4 : Positive step32 2339 2375 := by decide +kernel
private theorem pos32_5 : Positive step32 2376 2473 := by decide +kernel
private theorem pos32_6 : Positive step32 2474 2522 := by decide +kernel
theorem step32_verified : Checked step32 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5959_1281, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos32_0, by decide, by decide, pos32_1, by decide, by decide, pos32_2, by decide, by decide, pos32_3, by decide, by decide, pos32_4, by decide, by decide, pos32_5, by decide, by decide, pos32_6, rfl⟩⟩⟩
def step33 : Request := ⟨⟨⟨3393,4735,1018,497020⟩,1169070071480320,13720983207995⟩,40,2,2,308232⟩
private theorem pos33_0 : Positive step33 2317 2317 := by decide +kernel
private theorem pos33_1 : Positive step33 2318 2319 := by decide +kernel
private theorem pos33_2 : Positive step33 2320 2325 := by decide +kernel
private theorem pos33_3 : Positive step33 2326 2341 := by decide +kernel
private theorem pos33_4 : Positive step33 2342 2383 := by decide +kernel
private theorem pos33_5 : Positive step33 2384 2495 := by decide +kernel
private theorem pos33_6 : Positive step33 2496 2522 := by decide +kernel
theorem step33_verified : Checked step33 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment4735_1018, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2383, 2495, 2522], ⟨by decide, by decide, pos33_0, by decide, by decide, pos33_1, by decide, by decide, pos33_2, by decide, by decide, pos33_3, by decide, by decide, pos33_4, by decide, by decide, pos33_5, by decide, by decide, pos33_6, rfl⟩⟩⟩
def step34 : Request := ⟨⟨⟨913,1274,274,62076⟩,22869055897600,72278016338⟩,0,2,4,307568⟩
private theorem pos34_0 : Positive step34 2317 2317 := by decide +kernel
private theorem pos34_1 : Positive step34 2318 2319 := by decide +kernel
private theorem pos34_2 : Positive step34 2320 2325 := by decide +kernel
private theorem pos34_3 : Positive step34 2326 2342 := by decide +kernel
private theorem pos34_4 : Positive step34 2343 2390 := by decide +kernel
private theorem pos34_5 : Positive step34 2391 2522 := by decide +kernel
theorem step34_verified : Checked step34 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1274_274, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos34_0, by decide, by decide, pos34_1, by decide, by decide, pos34_2, by decide, by decide, pos34_3, by decide, by decide, pos34_4, by decide, by decide, pos34_5, rfl⟩⟩⟩
def step35 : Request := ⟨⟨⟨1007,1405,302,67675⟩,30653695393792,106799856912⟩,1,2,4,307568⟩
private theorem pos35_0 : Positive step35 2317 2317 := by decide +kernel
private theorem pos35_1 : Positive step35 2318 2319 := by decide +kernel
private theorem pos35_2 : Positive step35 2320 2325 := by decide +kernel
private theorem pos35_3 : Positive step35 2326 2342 := by decide +kernel
private theorem pos35_4 : Positive step35 2343 2390 := by decide +kernel
private theorem pos35_5 : Positive step35 2391 2522 := by decide +kernel
theorem step35_verified : Checked step35 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1405_302, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos35_0, by decide, by decide, pos35_1, by decide, by decide, pos35_2, by decide, by decide, pos35_3, by decide, by decide, pos35_4, by decide, by decide, pos35_5, rfl⟩⟩⟩
def step36 : Request := ⟨⟨⟨1214,1694,364,70229⟩,53657153044480,225404613013⟩,2,2,4,307568⟩
private theorem pos36_0 : Positive step36 2317 2317 := by decide +kernel
private theorem pos36_1 : Positive step36 2318 2319 := by decide +kernel
private theorem pos36_2 : Positive step36 2320 2325 := by decide +kernel
private theorem pos36_3 : Positive step36 2326 2341 := by decide +kernel
private theorem pos36_4 : Positive step36 2342 2386 := by decide +kernel
private theorem pos36_5 : Positive step36 2387 2511 := by decide +kernel
private theorem pos36_6 : Positive step36 2512 2522 := by decide +kernel
theorem step36_verified : Checked step36 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1694_364, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2386, 2511, 2522], ⟨by decide, by decide, pos36_0, by decide, by decide, pos36_1, by decide, by decide, pos36_2, by decide, by decide, pos36_3, by decide, by decide, pos36_4, by decide, by decide, pos36_5, by decide, by decide, pos36_6, rfl⟩⟩⟩
def step37 : Request := ⟨⟨⟨1396,1948,419,74914⟩,81610237542400,394206147308⟩,3,2,4,307568⟩
private theorem pos37_0 : Positive step37 2317 2317 := by decide +kernel
private theorem pos37_1 : Positive step37 2318 2319 := by decide +kernel
private theorem pos37_2 : Positive step37 2320 2325 := by decide +kernel
private theorem pos37_3 : Positive step37 2326 2341 := by decide +kernel
private theorem pos37_4 : Positive step37 2342 2385 := by decide +kernel
private theorem pos37_5 : Positive step37 2386 2506 := by decide +kernel
private theorem pos37_6 : Positive step37 2507 2522 := by decide +kernel
theorem step37_verified : Checked step37 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1948_419, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2506, 2522], ⟨by decide, by decide, pos37_0, by decide, by decide, pos37_1, by decide, by decide, pos37_2, by decide, by decide, pos37_3, by decide, by decide, pos37_4, by decide, by decide, pos37_5, by decide, by decide, pos37_6, rfl⟩⟩⟩
def step38 : Request := ⟨⟨⟨1704,2378,511,85815⟩,148231870742528,874078075528⟩,5,2,4,307568⟩
private theorem pos38_0 : Positive step38 2317 2317 := by decide +kernel
private theorem pos38_1 : Positive step38 2318 2319 := by decide +kernel
private theorem pos38_2 : Positive step38 2320 2325 := by decide +kernel
private theorem pos38_3 : Positive step38 2326 2341 := by decide +kernel
private theorem pos38_4 : Positive step38 2342 2385 := by decide +kernel
private theorem pos38_5 : Positive step38 2386 2504 := by decide +kernel
private theorem pos38_6 : Positive step38 2505 2522 := by decide +kernel
theorem step38_verified : Checked step38 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2378_511, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2504, 2522], ⟨by decide, by decide, pos38_0, by decide, by decide, pos38_1, by decide, by decide, pos38_2, by decide, by decide, pos38_3, by decide, by decide, pos38_4, by decide, by decide, pos38_5, by decide, by decide, pos38_6, rfl⟩⟩⟩
def step39 : Request := ⟨⟨⟨1883,2628,565,96916⟩,200058078756864,1303840388938⟩,7,2,4,307568⟩
private theorem pos39_0 : Positive step39 2317 2317 := by decide +kernel
private theorem pos39_1 : Positive step39 2318 2319 := by decide +kernel
private theorem pos39_2 : Positive step39 2320 2325 := by decide +kernel
private theorem pos39_3 : Positive step39 2326 2341 := by decide +kernel
private theorem pos39_4 : Positive step39 2342 2384 := by decide +kernel
private theorem pos39_5 : Positive step39 2385 2501 := by decide +kernel
private theorem pos39_6 : Positive step39 2502 2522 := by decide +kernel
theorem step39_verified : Checked step39 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2628_565, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos39_0, by decide, by decide, pos39_1, by decide, by decide, pos39_2, by decide, by decide, pos39_3, by decide, by decide, pos39_4, by decide, by decide, pos39_5, by decide, by decide, pos39_6, rfl⟩⟩⟩
def step40 : Request := ⟨⟨⟨2093,2921,628,128474⟩,274660672143360,1989358623137⟩,12,2,4,307568⟩
private theorem pos40_0 : Positive step40 2317 2317 := by decide +kernel
private theorem pos40_1 : Positive step40 2318 2319 := by decide +kernel
private theorem pos40_2 : Positive step40 2320 2325 := by decide +kernel
private theorem pos40_3 : Positive step40 2326 2341 := by decide +kernel
private theorem pos40_4 : Positive step40 2342 2384 := by decide +kernel
private theorem pos40_5 : Positive step40 2385 2500 := by decide +kernel
private theorem pos40_6 : Positive step40 2501 2522 := by decide +kernel
theorem step40_verified : Checked step40 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2921_628, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos40_0, by decide, by decide, pos40_1, by decide, by decide, pos40_2, by decide, by decide, pos40_3, by decide, by decide, pos40_4, by decide, by decide, pos40_5, by decide, by decide, pos40_6, rfl⟩⟩⟩
def step41 : Request := ⟨⟨⟨2535,3538,760,157760⟩,487505563484160,4276697639028⟩,17,2,4,307568⟩
private theorem pos41_0 : Positive step41 2317 2317 := by decide +kernel
private theorem pos41_1 : Positive step41 2318 2319 := by decide +kernel
private theorem pos41_2 : Positive step41 2320 2325 := by decide +kernel
private theorem pos41_3 : Positive step41 2326 2341 := by decide +kernel
private theorem pos41_4 : Positive step41 2342 2384 := by decide +kernel
private theorem pos41_5 : Positive step41 2385 2499 := by decide +kernel
private theorem pos41_6 : Positive step41 2500 2522 := by decide +kernel
theorem step41_verified : Checked step41 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3538_760, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2499, 2522], ⟨by decide, by decide, pos41_0, by decide, by decide, pos41_1, by decide, by decide, pos41_2, by decide, by decide, pos41_3, by decide, by decide, pos41_4, by decide, by decide, pos41_5, by decide, by decide, pos41_6, rfl⟩⟩⟩
def step42 : Request := ⟨⟨⟨2972,4148,892,152318⟩,786027838963712,8084380042177⟩,17,2,4,307568⟩
private theorem pos42_0 : Positive step42 2317 2317 := by decide +kernel
private theorem pos42_1 : Positive step42 2318 2319 := by decide +kernel
private theorem pos42_2 : Positive step42 2320 2325 := by decide +kernel
private theorem pos42_3 : Positive step42 2326 2341 := by decide +kernel
private theorem pos42_4 : Positive step42 2342 2383 := by decide +kernel
private theorem pos42_5 : Positive step42 2384 2496 := by decide +kernel
private theorem pos42_6 : Positive step42 2497 2522 := by decide +kernel
theorem step42_verified : Checked step42 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment4148_892, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2383, 2496, 2522], ⟨by decide, by decide, pos42_0, by decide, by decide, pos42_1, by decide, by decide, pos42_2, by decide, by decide, pos42_3, by decide, by decide, pos42_4, by decide, by decide, pos42_5, by decide, by decide, pos42_6, rfl⟩⟩⟩
def step43 : Request := ⟨⟨⟨1995,2784,598,204645⟩,237704260878336,1640652401644⟩,17,2,4,307568⟩
private theorem pos43_0 : Positive step43 2317 2317 := by decide +kernel
private theorem pos43_1 : Positive step43 2318 2319 := by decide +kernel
private theorem pos43_2 : Positive step43 2320 2325 := by decide +kernel
private theorem pos43_3 : Positive step43 2326 2341 := by decide +kernel
private theorem pos43_4 : Positive step43 2342 2384 := by decide +kernel
private theorem pos43_5 : Positive step43 2385 2501 := by decide +kernel
private theorem pos43_6 : Positive step43 2502 2522 := by decide +kernel
theorem step43_verified : Checked step43 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2784_598, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos43_0, by decide, by decide, pos43_1, by decide, by decide, pos43_2, by decide, by decide, pos43_3, by decide, by decide, pos43_4, by decide, by decide, pos43_5, by decide, by decide, pos43_6, rfl⟩⟩⟩
def step44 : Request := ⟨⟨⟨3702,5167,1111,224981⟩,1518566705725440,19455018383557⟩,29,2,4,307568⟩
private theorem pos44_0 : Positive step44 2317 2317 := by decide +kernel
private theorem pos44_1 : Positive step44 2318 2319 := by decide +kernel
private theorem pos44_2 : Positive step44 2320 2324 := by decide +kernel
private theorem pos44_3 : Positive step44 2325 2338 := by decide +kernel
private theorem pos44_4 : Positive step44 2339 2375 := by decide +kernel
private theorem pos44_5 : Positive step44 2376 2473 := by decide +kernel
private theorem pos44_6 : Positive step44 2474 2522 := by decide +kernel
theorem step44_verified : Checked step44 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment5167_1111, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos44_0, by decide, by decide, pos44_1, by decide, by decide, pos44_2, by decide, by decide, pos44_3, by decide, by decide, pos44_4, by decide, by decide, pos44_5, by decide, by decide, pos44_6, rfl⟩⟩⟩
def step45 : Request := ⟨⟨⟨4652,6493,1396,235446⟩,3012346810204160,48493835261734⟩,32,2,4,307568⟩
private theorem pos45_0 : Positive step45 2317 2317 := by decide +kernel
private theorem pos45_1 : Positive step45 2318 2319 := by decide +kernel
private theorem pos45_2 : Positive step45 2320 2324 := by decide +kernel
private theorem pos45_3 : Positive step45 2325 2338 := by decide +kernel
private theorem pos45_4 : Positive step45 2339 2375 := by decide +kernel
private theorem pos45_5 : Positive step45 2376 2473 := by decide +kernel
private theorem pos45_6 : Positive step45 2474 2522 := by decide +kernel
theorem step45_verified : Checked step45 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment6493_1396, by decide, by decide, by decide, ⟨[2317, 2319, 2324, 2338, 2375, 2473, 2522], ⟨by decide, by decide, pos45_0, by decide, by decide, pos45_1, by decide, by decide, pos45_2, by decide, by decide, pos45_3, by decide, by decide, pos45_4, by decide, by decide, pos45_5, by decide, by decide, pos45_6, rfl⟩⟩⟩
def step46 : Request := ⟨⟨⟨2276,3176,683,294186⟩,353158876889088,2780324254692⟩,23,2,4,307568⟩
private theorem pos46_0 : Positive step46 2317 2317 := by decide +kernel
private theorem pos46_1 : Positive step46 2318 2319 := by decide +kernel
private theorem pos46_2 : Positive step46 2320 2325 := by decide +kernel
private theorem pos46_3 : Positive step46 2326 2341 := by decide +kernel
private theorem pos46_4 : Positive step46 2342 2384 := by decide +kernel
private theorem pos46_5 : Positive step46 2385 2500 := by decide +kernel
private theorem pos46_6 : Positive step46 2501 2522 := by decide +kernel
theorem step46_verified : Checked step46 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3176_683, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos46_0, by decide, by decide, pos46_1, by decide, by decide, pos46_2, by decide, by decide, pos46_3, by decide, by decide, pos46_4, by decide, by decide, pos46_5, by decide, by decide, pos46_6, rfl⟩⟩⟩
def step47 : Request := ⟨⟨⟨2273,3172,682,337055⟩,351726004862976,2765910980015⟩,24,2,4,307568⟩
private theorem pos47_0 : Positive step47 2317 2317 := by decide +kernel
private theorem pos47_1 : Positive step47 2318 2319 := by decide +kernel
private theorem pos47_2 : Positive step47 2320 2325 := by decide +kernel
private theorem pos47_3 : Positive step47 2326 2341 := by decide +kernel
private theorem pos47_4 : Positive step47 2342 2384 := by decide +kernel
private theorem pos47_5 : Positive step47 2385 2500 := by decide +kernel
private theorem pos47_6 : Positive step47 2501 2522 := by decide +kernel
theorem step47_verified : Checked step47 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3172_682, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2500, 2522], ⟨by decide, by decide, pos47_0, by decide, by decide, pos47_1, by decide, by decide, pos47_2, by decide, by decide, pos47_3, by decide, by decide, pos47_4, by decide, by decide, pos47_5, by decide, by decide, pos47_6, rfl⟩⟩⟩

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueChecked1

section Merged6967_R6966ProofHelperRescueChecked10
set_option Elab.async false













set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step240 : Request := ⟨⟨⟨239,332,74,2477⟩,426141286400,349077659⟩,0,3,51,385646⟩
private theorem pos240_0 : Positive step240 2317 2317 := by decide +kernel
private theorem pos240_1 : Positive step240 2318 2320 := by decide +kernel
private theorem pos240_2 : Positive step240 2321 2332 := by decide +kernel
private theorem pos240_3 : Positive step240 2333 2377 := by decide +kernel
private theorem pos240_4 : Positive step240 2378 2522 := by decide +kernel
theorem step240_verified : Checked step240 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment332_74, by decide, by decide, by decide, ⟨[2317, 2320, 2332, 2377, 2522], ⟨by decide, by decide, pos240_0, by decide, by decide, pos240_1, by decide, by decide, pos240_2, by decide, by decide, pos240_3, by decide, by decide, pos240_4, rfl⟩⟩⟩
def step241 : Request := ⟨⟨⟨269,373,83,2619⟩,604708536320,553942033⟩,1,3,51,385646⟩
private theorem pos241_0 : Positive step241 2317 2317 := by decide +kernel
private theorem pos241_1 : Positive step241 2318 2320 := by decide +kernel
private theorem pos241_2 : Positive step241 2321 2331 := by decide +kernel
private theorem pos241_3 : Positive step241 2332 2370 := by decide +kernel
private theorem pos241_4 : Positive step241 2371 2509 := by decide +kernel
private theorem pos241_5 : Positive step241 2510 2522 := by decide +kernel
theorem step241_verified : Checked step241 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment373_83, by decide, by decide, by decide, ⟨[2317, 2320, 2331, 2370, 2509, 2522], ⟨by decide, by decide, pos241_0, by decide, by decide, pos241_1, by decide, by decide, pos241_2, by decide, by decide, pos241_3, by decide, by decide, pos241_4, by decide, by decide, pos241_5, rfl⟩⟩⟩
def step242 : Request := ⟨⟨⟨281,390,87,3036⟩,690560696320,662678389⟩,2,3,51,385646⟩
private theorem pos242_0 : Positive step242 2317 2317 := by decide +kernel
private theorem pos242_1 : Positive step242 2318 2320 := by decide +kernel
private theorem pos242_2 : Positive step242 2321 2331 := by decide +kernel
private theorem pos242_3 : Positive step242 2332 2369 := by decide +kernel
private theorem pos242_4 : Positive step242 2370 2503 := by decide +kernel
private theorem pos242_5 : Positive step242 2504 2522 := by decide +kernel
theorem step242_verified : Checked step242 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment390_87, by decide, by decide, by decide, ⟨[2317, 2320, 2331, 2369, 2503, 2522], ⟨by decide, by decide, pos242_0, by decide, by decide, pos242_1, by decide, by decide, pos242_2, by decide, by decide, pos242_3, by decide, by decide, pos242_4, by decide, by decide, pos242_5, rfl⟩⟩⟩
def step243 : Request := ⟨⟨⟨316,439,97,3128⟩,973976371200,1053621943⟩,3,3,51,385646⟩
private theorem pos243_0 : Positive step243 2317 2317 := by decide +kernel
private theorem pos243_1 : Positive step243 2318 2320 := by decide +kernel
private theorem pos243_2 : Positive step243 2321 2330 := by decide +kernel
private theorem pos243_3 : Positive step243 2331 2364 := by decide +kernel
private theorem pos243_4 : Positive step243 2365 2479 := by decide +kernel
private theorem pos243_5 : Positive step243 2480 2522 := by decide +kernel
theorem step243_verified : Checked step243 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment439_97, by decide, by decide, by decide, ⟨[2317, 2320, 2330, 2364, 2479, 2522], ⟨by decide, by decide, pos243_0, by decide, by decide, pos243_1, by decide, by decide, pos243_2, by decide, by decide, pos243_3, by decide, by decide, pos243_4, by decide, by decide, pos243_5, rfl⟩⟩⟩
def step244 : Request := ⟨⟨⟨334,464,103,3412⟩,1153155727360,1318278333⟩,4,3,51,385646⟩
private theorem pos244_0 : Positive step244 2317 2317 := by decide +kernel
private theorem pos244_1 : Positive step244 2318 2320 := by decide +kernel
private theorem pos244_2 : Positive step244 2321 2330 := by decide +kernel
private theorem pos244_3 : Positive step244 2331 2363 := by decide +kernel
private theorem pos244_4 : Positive step244 2364 2473 := by decide +kernel
private theorem pos244_5 : Positive step244 2474 2522 := by decide +kernel
theorem step244_verified : Checked step244 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment464_103, by decide, by decide, by decide, ⟨[2317, 2320, 2330, 2363, 2473, 2522], ⟨by decide, by decide, pos244_0, by decide, by decide, pos244_1, by decide, by decide, pos244_2, by decide, by decide, pos244_3, by decide, by decide, pos244_4, by decide, by decide, pos244_5, rfl⟩⟩⟩
def step245 : Request := ⟨⟨⟨350,486,108,3785⟩,1326705278976,1586684409⟩,5,3,51,385646⟩
private theorem pos245_0 : Positive step245 2317 2317 := by decide +kernel
private theorem pos245_1 : Positive step245 2318 2320 := by decide +kernel
private theorem pos245_2 : Positive step245 2321 2330 := by decide +kernel
private theorem pos245_3 : Positive step245 2331 2363 := by decide +kernel
private theorem pos245_4 : Positive step245 2364 2471 := by decide +kernel
private theorem pos245_5 : Positive step245 2472 2522 := by decide +kernel
theorem step245_verified : Checked step245 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment486_108, by decide, by decide, by decide, ⟨[2317, 2320, 2330, 2363, 2471, 2522], ⟨by decide, by decide, pos245_0, by decide, by decide, pos245_1, by decide, by decide, pos245_2, by decide, by decide, pos245_3, by decide, by decide, pos245_4, by decide, by decide, pos245_5, rfl⟩⟩⟩
def step246 : Request := ⟨⟨⟨401,557,123,4227⟩,1982954733568,2718384649⟩,7,3,51,385646⟩
private theorem pos246_0 : Positive step246 2317 2317 := by decide +kernel
private theorem pos246_1 : Positive step246 2318 2320 := by decide +kernel
private theorem pos246_2 : Positive step246 2321 2329 := by decide +kernel
private theorem pos246_3 : Positive step246 2330 2358 := by decide +kernel
private theorem pos246_4 : Positive step246 2359 2450 := by decide +kernel
private theorem pos246_5 : Positive step246 2451 2522 := by decide +kernel
theorem step246_verified : Checked step246 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment557_123, by decide, by decide, by decide, ⟨[2317, 2320, 2329, 2358, 2450, 2522], ⟨by decide, by decide, pos246_0, by decide, by decide, pos246_1, by decide, by decide, pos246_2, by decide, by decide, pos246_3, by decide, by decide, pos246_4, by decide, by decide, pos246_5, rfl⟩⟩⟩
def step247 : Request := ⟨⟨⟨469,652,143,5128⟩,3152837345280,5065784484⟩,10,3,51,385646⟩
private theorem pos247_0 : Positive step247 2317 2317 := by decide +kernel
private theorem pos247_1 : Positive step247 2318 2320 := by decide +kernel
private theorem pos247_2 : Positive step247 2321 2329 := by decide +kernel
private theorem pos247_3 : Positive step247 2330 2357 := by decide +kernel
private theorem pos247_4 : Positive step247 2358 2444 := by decide +kernel
private theorem pos247_5 : Positive step247 2445 2522 := by decide +kernel
theorem step247_verified : Checked step247 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment652_143, by decide, by decide, by decide, ⟨[2317, 2320, 2329, 2357, 2444, 2522], ⟨by decide, by decide, pos247_0, by decide, by decide, pos247_1, by decide, by decide, pos247_2, by decide, by decide, pos247_3, by decide, by decide, pos247_4, by decide, by decide, pos247_5, rfl⟩⟩⟩
def step248 : Request := ⟨⟨⟨600,835,185,6642⟩,6642856099840,13695877387⟩,16,3,51,385646⟩
private theorem pos248_0 : Positive step248 2317 2317 := by decide +kernel
private theorem pos248_1 : Positive step248 2318 2319 := by decide +kernel
private theorem pos248_2 : Positive step248 2320 2325 := by decide +kernel
private theorem pos248_3 : Positive step248 2326 2343 := by decide +kernel
private theorem pos248_4 : Positive step248 2344 2397 := by decide +kernel
private theorem pos248_5 : Positive step248 2398 2522 := by decide +kernel
theorem step248_verified : Checked step248 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment835_185, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2343, 2397, 2522], ⟨by decide, by decide, pos248_0, by decide, by decide, pos248_1, by decide, by decide, pos248_2, by decide, by decide, pos248_3, by decide, by decide, pos248_4, by decide, by decide, pos248_5, rfl⟩⟩⟩
def step249 : Request := ⟨⟨⟨675,939,211,8066⟩,9548426379264,22119378957⟩,20,3,51,385646⟩
private theorem pos249_0 : Positive step249 2317 2317 := by decide +kernel
private theorem pos249_1 : Positive step249 2318 2319 := by decide +kernel
private theorem pos249_2 : Positive step249 2320 2325 := by decide +kernel
private theorem pos249_3 : Positive step249 2326 2343 := by decide +kernel
private theorem pos249_4 : Positive step249 2344 2395 := by decide +kernel
private theorem pos249_5 : Positive step249 2396 2522 := by decide +kernel
theorem step249_verified : Checked step249 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment939_211, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2343, 2395, 2522], ⟨by decide, by decide, pos249_0, by decide, by decide, pos249_1, by decide, by decide, pos249_2, by decide, by decide, pos249_3, by decide, by decide, pos249_4, by decide, by decide, pos249_5, rfl⟩⟩⟩
def step250 : Request := ⟨⟨⟨964,1343,299,10649⟩,27592923545600,91653421946⟩,32,3,51,385646⟩
private theorem pos250_0 : Positive step250 2317 2317 := by decide +kernel
private theorem pos250_1 : Positive step250 2318 2319 := by decide +kernel
private theorem pos250_2 : Positive step250 2320 2325 := by decide +kernel
private theorem pos250_3 : Positive step250 2326 2342 := by decide +kernel
private theorem pos250_4 : Positive step250 2343 2390 := by decide +kernel
private theorem pos250_5 : Positive step250 2391 2522 := by decide +kernel
theorem step250_verified : Checked step250 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1343_299, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos250_0, by decide, by decide, pos250_1, by decide, by decide, pos250_2, by decide, by decide, pos250_3, by decide, by decide, pos250_4, by decide, by decide, pos250_5, rfl⟩⟩⟩
def step251 : Request := ⟨⟨⟨964,1343,297,10040⟩,27453212065792,91177576164⟩,31,3,51,385646⟩
private theorem pos251_0 : Positive step251 2317 2317 := by decide +kernel
private theorem pos251_1 : Positive step251 2318 2319 := by decide +kernel
private theorem pos251_2 : Positive step251 2320 2325 := by decide +kernel
private theorem pos251_3 : Positive step251 2326 2342 := by decide +kernel
private theorem pos251_4 : Positive step251 2343 2390 := by decide +kernel
private theorem pos251_5 : Positive step251 2391 2522 := by decide +kernel
theorem step251_verified : Checked step251 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1343_297, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2342, 2390, 2522], ⟨by decide, by decide, pos251_0, by decide, by decide, pos251_1, by decide, by decide, pos251_2, by decide, by decide, pos251_3, by decide, by decide, pos251_4, by decide, by decide, pos251_5, rfl⟩⟩⟩
def step252 : Request := ⟨⟨⟨1217,1695,378,13247⟩,55521299398656,232557160904⟩,43,3,51,385646⟩
private theorem pos252_0 : Positive step252 2317 2317 := by decide +kernel
private theorem pos252_1 : Positive step252 2318 2319 := by decide +kernel
private theorem pos252_2 : Positive step252 2320 2325 := by decide +kernel
private theorem pos252_3 : Positive step252 2326 2341 := by decide +kernel
private theorem pos252_4 : Positive step252 2342 2386 := by decide +kernel
private theorem pos252_5 : Positive step252 2387 2511 := by decide +kernel
private theorem pos252_6 : Positive step252 2512 2522 := by decide +kernel
theorem step252_verified : Checked step252 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment1695_378, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2386, 2511, 2522], ⟨by decide, by decide, pos252_0, by decide, by decide, pos252_1, by decide, by decide, pos252_2, by decide, by decide, pos252_3, by decide, by decide, pos252_4, by decide, by decide, pos252_5, by decide, by decide, pos252_6, rfl⟩⟩⟩
def step253 : Request := ⟨⟨⟨1901,2650,589,21021⟩,210923565875200,1383373535668⟩,73,3,51,385646⟩
private theorem pos253_0 : Positive step253 2317 2317 := by decide +kernel
private theorem pos253_1 : Positive step253 2318 2319 := by decide +kernel
private theorem pos253_2 : Positive step253 2320 2325 := by decide +kernel
private theorem pos253_3 : Positive step253 2326 2341 := by decide +kernel
private theorem pos253_4 : Positive step253 2342 2384 := by decide +kernel
private theorem pos253_5 : Positive step253 2385 2501 := by decide +kernel
private theorem pos253_6 : Positive step253 2502 2522 := by decide +kernel
theorem step253_verified : Checked step253 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2650_589, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2501, 2522], ⟨by decide, by decide, pos253_0, by decide, by decide, pos253_1, by decide, by decide, pos253_2, by decide, by decide, pos253_3, by decide, by decide, pos253_4, by decide, by decide, pos253_5, by decide, by decide, pos253_6, rfl⟩⟩⟩
def step254 : Request := ⟨⟨⟨2000,2787,606,23022⟩,241468805218304,1663490943357⟩,76,3,51,385646⟩
private theorem pos254_0 : Positive step254 2317 2317 := by decide +kernel
private theorem pos254_1 : Positive step254 2318 2319 := by decide +kernel
private theorem pos254_2 : Positive step254 2320 2325 := by decide +kernel
private theorem pos254_3 : Positive step254 2326 2341 := by decide +kernel
private theorem pos254_4 : Positive step254 2342 2385 := by decide +kernel
private theorem pos254_5 : Positive step254 2386 2505 := by decide +kernel
private theorem pos254_6 : Positive step254 2506 2522 := by decide +kernel
theorem step254_verified : Checked step254 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment2787_606, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2385, 2505, 2522], ⟨by decide, by decide, pos254_0, by decide, by decide, pos254_1, by decide, by decide, pos254_2, by decide, by decide, pos254_3, by decide, by decide, pos254_4, by decide, by decide, pos254_5, by decide, by decide, pos254_6, rfl⟩⟩⟩
def step255 : Request := ⟨⟨⟨2502,3487,777,29171⟩,481439418417152,4152321171330⟩,101,3,51,385646⟩
private theorem pos255_0 : Positive step255 2317 2317 := by decide +kernel
private theorem pos255_1 : Positive step255 2318 2319 := by decide +kernel
private theorem pos255_2 : Positive step255 2320 2325 := by decide +kernel
private theorem pos255_3 : Positive step255 2326 2341 := by decide +kernel
private theorem pos255_4 : Positive step255 2342 2384 := by decide +kernel
private theorem pos255_5 : Positive step255 2385 2499 := by decide +kernel
private theorem pos255_6 : Positive step255 2500 2522 := by decide +kernel
theorem step255_verified : Checked step255 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment3487_777, by decide, by decide, by decide, ⟨[2317, 2319, 2325, 2341, 2384, 2499, 2522], ⟨by decide, by decide, pos255_0, by decide, by decide, pos255_1, by decide, by decide, pos255_2, by decide, by decide, pos255_3, by decide, by decide, pos255_4, by decide, by decide, pos255_5, by decide, by decide, pos255_6, rfl⟩⟩⟩
def step256 : Request := ⟨⟨⟨183,254,57,2073⟩,193292926976,121131076⟩,0,3,71,385646⟩
private theorem pos256_0 : Positive step256 2317 2317 := by decide +kernel
private theorem pos256_1 : Positive step256 2318 2321 := by decide +kernel
private theorem pos256_2 : Positive step256 2322 2338 := by decide +kernel
private theorem pos256_3 : Positive step256 2339 2412 := by decide +kernel
private theorem pos256_4 : Positive step256 2413 2522 := by decide +kernel
theorem step256_verified : Checked step256 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment254_57, by decide, by decide, by decide, ⟨[2317, 2321, 2338, 2412, 2522], ⟨by decide, by decide, pos256_0, by decide, by decide, pos256_1, by decide, by decide, pos256_2, by decide, by decide, pos256_3, by decide, by decide, pos256_4, rfl⟩⟩⟩
def step257 : Request := ⟨⟨⟨200,278,61,2403⟩,247865278464,170383811⟩,1,3,71,385646⟩
private theorem pos257_0 : Positive step257 2317 2317 := by decide +kernel
private theorem pos257_1 : Positive step257 2318 2321 := by decide +kernel
private theorem pos257_2 : Positive step257 2322 2337 := by decide +kernel
private theorem pos257_3 : Positive step257 2338 2403 := by decide +kernel
private theorem pos257_4 : Positive step257 2404 2522 := by decide +kernel
theorem step257_verified : Checked step257 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment278_61, by decide, by decide, by decide, ⟨[2317, 2321, 2337, 2403, 2522], ⟨by decide, by decide, pos257_0, by decide, by decide, pos257_1, by decide, by decide, pos257_2, by decide, by decide, pos257_3, by decide, by decide, pos257_4, rfl⟩⟩⟩
def step258 : Request := ⟨⟨⟨226,314,68,2489⟩,353070481408,273591980⟩,2,3,71,385646⟩
private theorem pos258_0 : Positive step258 2317 2317 := by decide +kernel
private theorem pos258_1 : Positive step258 2318 2320 := by decide +kernel
private theorem pos258_2 : Positive step258 2321 2332 := by decide +kernel
private theorem pos258_3 : Positive step258 2333 2379 := by decide +kernel
private theorem pos258_4 : Positive step258 2380 2522 := by decide +kernel
theorem step258_verified : Checked step258 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment314_68, by decide, by decide, by decide, ⟨[2317, 2320, 2332, 2379, 2522], ⟨by decide, by decide, pos258_0, by decide, by decide, pos258_1, by decide, by decide, pos258_2, by decide, by decide, pos258_3, by decide, by decide, pos258_4, rfl⟩⟩⟩
def step259 : Request := ⟨⟨⟨239,331,74,2610⟩,426141286400,345715284⟩,3,3,71,385646⟩
private theorem pos259_0 : Positive step259 2317 2317 := by decide +kernel
private theorem pos259_1 : Positive step259 2318 2320 := by decide +kernel
private theorem pos259_2 : Positive step259 2321 2332 := by decide +kernel
private theorem pos259_3 : Positive step259 2333 2377 := by decide +kernel
private theorem pos259_4 : Positive step259 2378 2522 := by decide +kernel
theorem step259_verified : Checked step259 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment331_74, by decide, by decide, by decide, ⟨[2317, 2320, 2332, 2377, 2522], ⟨by decide, by decide, pos259_0, by decide, by decide, pos259_1, by decide, by decide, pos259_2, by decide, by decide, pos259_3, by decide, by decide, pos259_4, rfl⟩⟩⟩
def step260 : Request := ⟨⟨⟨251,348,78,2987⟩,494498480128,422716393⟩,4,3,71,385646⟩
private theorem pos260_0 : Positive step260 2317 2317 := by decide +kernel
private theorem pos260_1 : Positive step260 2318 2320 := by decide +kernel
private theorem pos260_2 : Positive step260 2321 2331 := by decide +kernel
private theorem pos260_3 : Positive step260 2332 2371 := by decide +kernel
private theorem pos260_4 : Positive step260 2372 2518 := by decide +kernel
private theorem pos260_5 : Positive step260 2519 2522 := by decide +kernel
theorem step260_verified : Checked step260 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment348_78, by decide, by decide, by decide, ⟨[2317, 2320, 2331, 2371, 2518, 2522], ⟨by decide, by decide, pos260_0, by decide, by decide, pos260_1, by decide, by decide, pos260_2, by decide, by decide, pos260_3, by decide, by decide, pos260_4, by decide, by decide, pos260_5, rfl⟩⟩⟩
def step261 : Request := ⟨⟨⟨268,372,83,3236⟩,599698964480,549189173⟩,5,3,71,385646⟩
private theorem pos261_0 : Positive step261 2317 2317 := by decide +kernel
private theorem pos261_1 : Positive step261 2318 2320 := by decide +kernel
private theorem pos261_2 : Positive step261 2321 2331 := by decide +kernel
private theorem pos261_3 : Positive step261 2332 2370 := by decide +kernel
private theorem pos261_4 : Positive step261 2371 2510 := by decide +kernel
private theorem pos261_5 : Positive step261 2511 2522 := by decide +kernel
theorem step261_verified : Checked step261 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment372_83, by decide, by decide, by decide, ⟨[2317, 2320, 2331, 2370, 2510, 2522], ⟨by decide, by decide, pos261_0, by decide, by decide, pos261_1, by decide, by decide, pos261_2, by decide, by decide, pos261_3, by decide, by decide, pos261_4, by decide, by decide, pos261_5, rfl⟩⟩⟩
def step262 : Request := ⟨⟨⟨316,439,97,3334⟩,973976371200,1053621943⟩,7,3,71,385646⟩
private theorem pos262_0 : Positive step262 2317 2317 := by decide +kernel
private theorem pos262_1 : Positive step262 2318 2320 := by decide +kernel
private theorem pos262_2 : Positive step262 2321 2330 := by decide +kernel
private theorem pos262_3 : Positive step262 2331 2364 := by decide +kernel
private theorem pos262_4 : Positive step262 2365 2479 := by decide +kernel
private theorem pos262_5 : Positive step262 2480 2522 := by decide +kernel
theorem step262_verified : Checked step262 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment439_97, by decide, by decide, by decide, ⟨[2317, 2320, 2330, 2364, 2479, 2522], ⟨by decide, by decide, pos262_0, by decide, by decide, pos262_1, by decide, by decide, pos262_2, by decide, by decide, pos262_3, by decide, by decide, pos262_4, by decide, by decide, pos262_5, rfl⟩⟩⟩
def step263 : Request := ⟨⟨⟨376,522,114,3949⟩,1621734195200,2081076603⟩,10,3,71,385646⟩
private theorem pos263_0 : Positive step263 2317 2317 := by decide +kernel
private theorem pos263_1 : Positive step263 2318 2320 := by decide +kernel
private theorem pos263_2 : Positive step263 2321 2330 := by decide +kernel
private theorem pos263_3 : Positive step263 2331 2362 := by decide +kernel
private theorem pos263_4 : Positive step263 2363 2466 := by decide +kernel
private theorem pos263_5 : Positive step263 2467 2522 := by decide +kernel
theorem step263_verified : Checked step263 :=
  ⟨node_check _ (by decide) (by decide) (by decide), moment522_114, by decide, by decide, by decide, ⟨[2317, 2320, 2330, 2362, 2466, 2522], ⟨by decide, by decide, pos263_0, by decide, by decide, pos263_1, by decide, by decide, pos263_2, by decide, by decide, pos263_3, by decide, by decide, pos263_4, by decide, by decide, pos263_5, rfl⟩⟩⟩

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueChecked10
