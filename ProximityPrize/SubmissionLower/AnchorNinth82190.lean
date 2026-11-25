import ProximityPrize.SubmissionLower.Fast054

set_option Elab.async false

-- merged module AnchorPivotRank82180
section Merged_AnchorPivotRank82180

-- merged module AnchorTopFactor
section Merged_AnchorTopFactor
set_option Elab.async false
namespace SoundnessAnchor
open K1_13 K1_13_1_1 MvPolynomial
open K1_13_1_1 (monomial_band capX)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
structure Powers where
  base : FactorPowers
  top : ℕ
end
end SoundnessAnchor

end Merged_AnchorTopFactor

-- merged module AnchorPivot82180
section Merged_AnchorPivot82180

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm bandSpace_mul)
open MvPolynomial
open K1_13_1_1 (monomial_band capX)

structure E where
  a : ℕ
  b : ℕ
  c : ℕ
  f : ℕ
  deriving DecidableEq

def E.deg (e : E) := e.a+e.b+e.c+e.f
def E.index (e : E) := e.b+2*e.c+3*e.f
def E.order (e : E) := 3*e.a+e.c+2*e.f
def E.key (e : E) := 30000*e.a+20000*e.b+10001*e.c+64*e.f
noncomputable def mon (e : E) : Form :=
  MvPolynomial.X 0^e.a * MvPolynomial.X 1^e.b * MvPolynomial.X 2^e.c * MvPolynomial.X 3^e.f

noncomputable def encode : Form →ₐ[Geom] Polynomial Geom :=
  aeval (fun i => (Polynomial.X : Polynomial Geom)^(![30000,20000,10001,64] i : ℕ))

theorem encode_mon (e : E) : encode (mon e) = Polynomial.X ^ e.key := by
  simp [mon, encode, E.key, ← pow_mul, ← pow_add]

private theorem mono_band {e : E} {d lo hi top : ℕ} (hd : e.deg = d)
    (hl : lo ≤ e.index) (hh : e.index ≤ hi) (ht : e.f ≤ top) :
    mon e ∈ bandSpace d lo hi top := by
  apply monomial_band e.a e.b e.c e.f hd <;> first | exact ht | exact_mod_cast hl | exact_mod_cast hh

private theorem mono_order (e : E) : mon e ∈ restrictWeightedOrder targetOrder e.order := by
  have h := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder (capX 0) e.a)
      (pow_mem_restrictWeightedOrder (capX 1) e.b)) (pow_mem_restrictWeightedOrder (capX 2) e.c))
    (pow_mem_restrictWeightedOrder (capX 3) e.f)
  simpa [mon,E.order,targetOrder, Nat.mul_comm, Nat.add_assoc] using h

abbrev Term := ℤ × E
noncomputable def poly : List Term → Form
  | [] => 0
  | (k,e)::xs => k • mon e + poly xs

theorem poly_band {d lo hi top : ℕ} (xs : List Term)
    (h : xs.all (fun t => decide (t.2.deg = d ∧ lo ≤ t.2.index ∧ t.2.index ≤ hi ∧ t.2.f ≤ top)) = true) :
    poly xs ∈ bandSpace d lo hi top := by
  induction xs with
  | nil => exact zero_mem _
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    obtain ⟨hd,hl,hh,ht⟩ := of_decide_eq_true hp
    exact add_mem (zsmul_mem (mono_band hd hl hh ht) _) (ih hr)

theorem poly_order {o : ℕ} (xs : List Term)
    (h : xs.all (fun t => decide (o ≤ t.2.order)) = true) :
    poly xs ∈ restrictWeightedOrder targetOrder o := by
  induction xs with
  | nil => exact zero_mem _
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    exact add_mem (zsmul_mem (restrictWeightedOrder_anti _ (of_decide_eq_true hp) (mono_order t.2)) _) (ih hr)

private theorem encoded_degree_le {b : ℕ} (xs : List Term)
    (h : xs.all (fun t => decide (t.2.key ≤ b)) = true) : (encode (poly xs)).degree ≤ (b : ℕ) := by
  induction xs with
  | nil => simp [poly]
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    rw [poly, map_add, map_zsmul, encode_mon]
    apply Polynomial.degree_add_le_of_degree_le _ (ih hr)
    rw [← Int.cast_smul_eq_zsmul (R := Geom)]
    exact (Polynomial.degree_smul_le _ _).trans ((Polynomial.degree_X_pow_le _).trans
      (WithBot.coe_le_coe.mpr (of_decide_eq_true hp)))

theorem encoded_degree {e : E} {b : ℕ} (xs : List Term) (h : b < e.key)
    (hu : xs.all (fun t => decide (t.2.key ≤ b)) = true) :
    (encode (poly ((1,e)::xs))).degree = (e.key : ℕ) := by
  rw [poly, one_zsmul, map_add, encode_mon, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (encoded_degree_le xs hu).trans_lt (WithBot.coe_lt_coe.mpr h)

structure Data where
  deg : ℕ
  lo : ℕ
  hi : ℕ
  top : ℕ
  ord : ℕ
  tag : ℕ
  deriving DecidableEq
def Data.plus (x y : Data) : Data := ⟨x.deg+y.deg,x.lo+y.lo,x.hi+y.hi,x.top+y.top,x.ord+y.ord,x.tag+y.tag⟩
def Data.times (n : ℕ) (x : Data) : Data := ⟨n*x.deg,n*x.lo,n*x.hi,n*x.top,n*x.ord,n*x.tag⟩
def Data.unit : Data := ⟨0,0,0,0,0,0⟩

structure Sound (v : Data) (q : Form) : Prop where
  band : q ∈ bandSpace v.deg v.lo v.hi v.top
  contact : backShift q ∈ restrictWeightedOrder targetOrder v.ord
  degree : (encode q).degree = (v.tag : ℕ)

theorem Sound.mul {u v : Data} {f g : Form} (h : Sound u f) (k : Sound v g) :
    Sound (u.plus v) (f*g) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Data.plus] using bandSpace_mul h.band k.band
  · rw [map_mul]; exact mul_mem_restrictWeightedOrder h.contact k.contact
  · rw [map_mul, Polynomial.degree_mul, h.degree, k.degree]; rfl

theorem sound_one : Sound Data.unit 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Data.unit,mon] using (mono_band (e := ⟨0,0,0,0⟩) (d := 0) (lo := 0) (hi := 0) (top := 0) rfl (by decide) (by decide) (by decide))
  · simp [Data.unit, restrictWeightedOrder_zero]
  · simp [Data.unit]

theorem Sound.pow {u : Data} {f : Form} (h : Sound u f) (n : ℕ) :
    Sound (u.times n) (f^n) := by
  induction n with
  | zero => simpa [Data.times,Data.unit] using sound_one
  | succ n ih => simpa [pow_succ,Data.times,Data.plus,Nat.succ_mul] using ih.mul h

def monoData (e : E) : Data := ⟨e.deg,e.index,e.index,e.f,e.c+2*e.f,e.key⟩
theorem sound_monomial (e : E) : Sound (monoData e) (mon e) := by
  refine ⟨mono_band rfl le_rfl le_rfl le_rfl, ?_, ?_⟩
  · have h0 : backShift (MvPolynomial.X 0) ∈ restrictWeightedOrder targetOrder 0 := by simp [restrictWeightedOrder_zero]
    have h := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder h0 e.a)
        (pow_mem_restrictWeightedOrder (capX 1) e.b)) (pow_mem_restrictWeightedOrder (capX 2) e.c))
        (pow_mem_restrictWeightedOrder (capX 3) e.f)
    simpa [monoData,mon,map_mul,map_pow,K1_13_1_1.backShift_X_of_ne 1 (by decide),
      K1_13_1_1.backShift_X_of_ne 2 (by decide), K1_13_1_1.backShift_X_of_ne 3 (by decide),targetOrder,Nat.mul_comm] using h
  · rw [encode_mon, Polynomial.degree_X_pow]; rfl

end AnchorPivot82180

end Merged_AnchorPivot82180

-- merged module AnchorPivotFactors82180
section Merged_AnchorPivotFactors82180

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open AnchorPivot82180 (poly_band poly_order encoded_degree)

def src0 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩)]
private def dst0 : List Term := [(-1,⟨0,0,1,0⟩), (1,⟨0,0,0,1⟩), (1,⟨1,0,0,0⟩)]
def data0 : Data := ⟨1,0,1,0,1,30000⟩
theorem spec0 : Sound data0 (poly src0) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src0) = poly dst0 := by
      simp [src0,dst0,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩)]) (by decide) (by decide)
def src1 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩)]
private def dst1 : List Term := [(1,⟨0,0,0,1⟩), (1,⟨1,0,0,0⟩)]
def data1 : Data := ⟨1,0,2,0,2,30000⟩
theorem spec1 : Sound data1 (poly src1) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src1) = poly dst1 := by
      simp [src1,dst1,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩)]) (by decide) (by decide)
def src2 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩), (-1,⟨0,0,0,1⟩)]
private def dst2 : List Term := [(1,⟨1,0,0,0⟩)]
def data2 : Data := ⟨1,0,3,1,3,30000⟩
theorem spec2 : Sound data2 (poly src2) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src2) = poly dst2 := by
      simp [src2,dst2,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩), (-1,⟨0,0,0,1⟩)]) (by decide) (by decide)
def src3 : List Term := [(1,⟨1,1,0,0⟩), (-1,⟨0,2,0,0⟩), (1,⟨1,0,1,0⟩)]
private def dst3 : List Term := [(1,⟨0,1,0,1⟩), (1,⟨1,1,0,0⟩), (-1,⟨0,0,2,0⟩), (1,⟨0,0,1,1⟩), (1,⟨1,0,1,0⟩)]
def data3 : Data := ⟨2,1,2,0,2,50000⟩
theorem spec3 : Sound data3 (poly src3) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src3) = poly dst3 := by
      simp [src3,dst3,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 40001) ([(-1,⟨0,2,0,0⟩), (1,⟨1,0,1,0⟩)]) (by decide) (by decide)
def src4 : List Term := [(1,⟨1,1,0,0⟩), (-1,⟨0,2,0,0⟩), (1,⟨0,1,1,0⟩), (-1,⟨1,0,0,1⟩)]
private def dst4 : List Term := [(1,⟨1,1,0,0⟩), (1,⟨0,0,1,1⟩), (-1,⟨0,0,0,2⟩), (-1,⟨1,0,0,1⟩)]
def data4 : Data := ⟨2,1,3,1,3,50000⟩
theorem spec4 : Sound data4 (poly src4) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src4) = poly dst4 := by
      simp [src4,dst4,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 40000) ([(-1,⟨0,2,0,0⟩), (1,⟨0,1,1,0⟩), (-1,⟨1,0,0,1⟩)]) (by decide) (by decide)
def src5 : List Term := [(1,⟨1,0,1,0⟩), (-1,⟨0,1,1,0⟩), (1,⟨0,0,2,0⟩), (1,⟨1,0,0,1⟩), (-1,⟨0,1,0,1⟩)]
private def dst5 : List Term := [(1,⟨1,0,1,0⟩), (1,⟨0,0,0,2⟩), (1,⟨1,0,0,1⟩)]
def data5 : Data := ⟨2,2,4,1,4,40001⟩
theorem spec5 : Sound data5 (poly src5) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src5) = poly dst5 := by
      simp [src5,dst5,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 30064) ([(-1,⟨0,1,1,0⟩), (1,⟨0,0,2,0⟩), (1,⟨1,0,0,1⟩), (-1,⟨0,1,0,1⟩)]) (by decide) (by decide)
def src6 : List Term := [(1,⟨2,0,1,0⟩), (-2,⟨1,1,1,0⟩), (-1,⟨1,2,0,0⟩), (1,⟨0,3,0,0⟩), (1,⟨2,0,0,1⟩)]
private def dst6 : List Term := [(1,⟨0,0,3,0⟩), (-1,⟨0,0,2,1⟩), (-1,⟨0,0,1,2⟩), (-2,⟨1,0,2,0⟩), (1,⟨2,0,1,0⟩), (-1,⟨1,2,0,0⟩), (-2,⟨0,1,1,1⟩), (2,⟨0,1,0,2⟩), (2,⟨1,1,0,1⟩), (1,⟨0,0,0,3⟩), (2,⟨1,0,0,2⟩), (1,⟨2,0,0,1⟩)]
def data6 : Data := ⟨3,2,3,1,3,70001⟩
theorem spec6 : Sound data6 (poly src6) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src6) = poly dst6 := by
      simp [src6,dst6,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 70000) ([(-2,⟨1,1,1,0⟩), (-1,⟨1,2,0,0⟩), (1,⟨0,3,0,0⟩), (1,⟨2,0,0,1⟩)]) (by decide) (by decide)
def src7 : List Term := [(1,⟨1,3,0,0⟩), (-1,⟨0,4,0,0⟩), (1,⟨1,2,1,0⟩), (1,⟨2,0,2,0⟩), (-1,⟨2,1,0,1⟩)]
private def dst7 : List Term := [(1,⟨1,3,0,0⟩), (3,⟨0,2,1,1⟩), (1,⟨1,2,1,0⟩), (-2,⟨0,1,3,0⟩), (1,⟨0,0,4,0⟩), (1,⟨0,1,2,1⟩), (-2,⟨0,0,3,1⟩), (2,⟨1,1,2,0⟩), (1,⟨0,0,2,2⟩), (-2,⟨1,0,3,0⟩), (2,⟨1,0,2,1⟩), (1,⟨2,0,2,0⟩), (-2,⟨0,2,0,2⟩), (2,⟨0,1,1,2⟩), (-2,⟨1,2,0,1⟩), (-1,⟨0,1,0,3⟩), (2,⟨1,1,1,1⟩), (-2,⟨1,1,0,2⟩), (-1,⟨2,1,0,1⟩)]
def data7 : Data := ⟨4,3,4,1,3,90000⟩
theorem spec7 : Sound data7 (poly src7) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src7) = poly dst7 := by
      simp [src7,dst7,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 80064) ([(-1,⟨0,4,0,0⟩), (1,⟨1,2,1,0⟩), (1,⟨2,0,2,0⟩), (-1,⟨2,1,0,1⟩)]) (by decide) (by decide)

end AnchorPivot82180

end Merged_AnchorPivotFactors82180

-- merged module AnchorPivotRank82180
section Merged_AnchorPivotRank82180

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 8 × ℕ

structure Row where
  tag : ℕ
  index : ℕ
  ord : ℕ
  e : E
  factors : List Factor
  deriving DecidableEq




theorem independent {V ι : Type} [AddCommGroup V] [Module Geom V] [Fintype ι]
    (f : V →ₗ[Geom] Polynomial Geom) (v : ι → V) (tag : ι → ℕ) (inj : Function.Injective tag)
    (hdeg : ∀ i, (f (v i)).degree = (tag i : ℕ)) : LinearIndependent Geom v := by
  classical
  refine (Fintype.linearIndependent_iff (v := v)).mpr ?_
  intro w hw j
  by_contra hj
  let a := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i,hi,hiMax⟩ := a.exists_max_image tag
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let t := (Polynomial.lcoeff Geom (tag i)).comp f
  have hz := congrArg t hw
  simp only [map_sum,map_smul,map_zero] at hz
  rw [Finset.sum_eq_single i] at hz
  · change w i * (f (v i)).coeff (tag i) = 0 at hz
    have hn : f (v i) ≠ 0 := fun h => by simpa [h] using hdeg i
    have hd := Polynomial.natDegree_eq_of_degree_eq_some (hdeg i)
    rw [← hd,Polynomial.coeff_natDegree] at hz
    exact (mul_ne_zero hwi (Polynomial.leadingCoeff_ne_zero.mpr hn)) hz
  · intro b _ hbi
    by_cases hb : w b = 0
    · simp [hb]
    · have lt : tag b < tag i := lt_of_le_of_ne
        (hiMax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)) (fun e => hbi (inj e))
      change w b * (f (v b)).coeff (tag i) = 0
      rw [Polynomial.coeff_eq_zero_of_degree_lt (by rw [hdeg]; exact WithBot.coe_lt_coe.mpr lt),mul_zero]
  · simp


end AnchorPivot82180

end Merged_AnchorPivotRank82180

end Merged_AnchorPivotRank82180

-- merged module AnchorNinth82190
section Merged_AnchorNinth82190

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82190
open AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open AnchorPivot82180 (poly_band poly_order encoded_degree)

def src8 : List Term := [(1,⟨2,3,0,0⟩), (1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]
private def dst8 : List Term := [(1,⟨2,3,0,0⟩), (-4,⟨0,1,1,3⟩), (-2,⟨1,1,1,2⟩), (1,⟨0,2,0,3⟩), (-1,⟨1,2,0,2⟩), (-2,⟨2,2,0,1⟩), (1,⟨2,2,1,0⟩), (1,⟨0,1,2,2⟩), (4,⟨1,2,1,1⟩), (-1,⟨0,0,4,1⟩), (3,⟨0,0,3,2⟩), (2,⟨1,0,3,1⟩), (-1,⟨0,0,1,4⟩), (-6,⟨1,0,2,2⟩), (-3,⟨2,0,2,1⟩), (2,⟨3,0,1,1⟩), (3,⟨0,1,0,4⟩), (6,⟨1,1,0,3⟩), (1,⟨0,0,0,5⟩), (3,⟨2,1,0,2⟩), (3,⟨1,0,0,4⟩), (3,⟨2,0,0,3⟩), (1,⟨3,0,0,2⟩), (-2,⟨1,1,3,0⟩), (-2,⟨0,0,2,3⟩), (2,⟨2,1,2,0⟩), (-2,⟨2,0,3,0⟩), (1,⟨3,0,2,0⟩), (2,⟨2,1,1,1⟩), (1,⟨1,0,4,0⟩), (3,⟨2,0,1,2⟩)]
def data8 : Data := ⟨5,3,6,2,6,120000⟩
theorem spec8 : Sound data8 (poly src8) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src8) = poly dst8 := by
      simp [src8,dst8,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul]
      ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 110002) ([(1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]) (by decide) (by decide)

def allData : Fin 9 → Data := ![data0, data1, data2, data3, data4, data5, data6, data7, data8]
noncomputable def allPoly : Fin 9 → Form := ![poly src0, poly src1, poly src2, poly src3, poly src4, poly src5, poly src6, poly src7, poly src8]
theorem all_ok (i : Fin 9) : Sound (allData i) (allPoly i) := by
  fin_cases i
  · exact spec0
  · exact spec1
  · exact spec2
  · exact spec3
  · exact spec4
  · exact spec5
  · exact spec6
  · exact spec7
  · exact spec8

#print axioms all_ok
end AnchorPivot82190

end Merged_AnchorNinth82190
