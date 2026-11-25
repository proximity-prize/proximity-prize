import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Union
import ProximityPrize.SubmissionLower.R6960MonicChartFrobenius

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
open RetainedCompression (Curve ordinate view height heightCap TameBand)
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
theorem descend (degD : ℕ) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : TameBand (f.degreeOf ordinate) degD)
    (bounded : height degD f≤heightCap (f.degreeOf ordinate) degD)
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
  obtain ⟨w,hw⟩ := MonicChart.actual_coboundary_pth_root degD f ir lo hi bounded basis root_in_tower
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
theorem descend_iterate (degD : ℕ) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : TameBand (f.degreeOf ordinate) degD) (bounded : height degD f≤heightCap (f.degreeOf ordinate) degD)
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
    obtain ⟨v,hv,hv'⟩ := descend degD f ir lo hi bounded basis root (a*K1.p^n) (b*K1.p^n)
      (Nat.mul_pos ha (pow_pos KoalaBear.is_prime.pos _)) (fun s=>u s ^ (K1.p^n)) c next
    obtain ⟨d,hd,hd'⟩ := ih v hv'
    exact ⟨d,by rw [pow_succ K1.p n,pow_mul,hd,hv],hd'⟩
#print axioms descend
#print axioms descend_iterate
end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent
