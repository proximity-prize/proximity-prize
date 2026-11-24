import ProximityPrize.SubmissionLower.R6960MonicChartFrobenius
import ProximityPrize.SubmissionLower.R6960ChartSections

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

/-- The constants and the two coordinates in the actual rational field. -/
def constants : L →+* ChartField := RatFunc.C.comp ((algebraMap (Polynomial L) Scalar).comp C)

def scalarCoordinate : ChartField := RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))

def chartCoordinate (infinity : Bool) (x : ChartField) : ChartField :=
  if infinity then x⁻¹ else x

/-- The first bit is the abscissa chart and the second is the scalar chart.
Each chart contains the constants and its two chosen affine coordinates. -/
def baseChart (s : Chart) : Subring ChartField :=
  Subring.closure (Set.range constants ∪
    {chartCoordinate s.1 RatFunc.X, chartCoordinate s.2 scalarCoordinate})

/-- The factor converting a rational section to its polynomial frame on
this chart. The twist is negative at infinity in each direction. -/
def frame (a b : ℕ) (s : Chart) : ChartField :=
  (if s.1 then RatFunc.X else 1)^a * (if s.2 then scalarCoordinate else 1)^b

theorem frame_scale (a b n : ℕ) (s : Chart) :
    frame (a*n) (b*n) s=(frame a b s)^n := by
  simp only [frame,pow_mul,mul_pow]

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- The same correction gives an integral element over each actual base chart. -/
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

/-- Integrality persists under passage from a base chart to a larger ring
in the same rational field. -/
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

/-- A correction on the four actual charts for the Frobenius powers of the
potentials descends to a single correction over all four charts. Its
p-th power is the original correction in the same root field. -/
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

/-- Descend an arbitrarily iterated Frobenius correction, preserving the
same correction across all four actual chart rings on each step. -/
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
