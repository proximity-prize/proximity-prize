import ProximityPrize.SubmissionLower.AnchorTopFactor

set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm bandSpace_mul)
open MvPolynomial
open private monomial_band capX from ProximityPrize.SubmissionLower.Fast054

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

private theorem poly_band {d lo hi top : ℕ} (xs : List Term)
    (h : xs.all (fun t => decide (t.2.deg = d ∧ lo ≤ t.2.index ∧ t.2.index ≤ hi ∧ t.2.f ≤ top)) = true) :
    poly xs ∈ bandSpace d lo hi top := by
  induction xs with
  | nil => exact zero_mem _
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    obtain ⟨hd,hl,hh,ht⟩ := of_decide_eq_true hp
    exact add_mem (zsmul_mem (mono_band hd hl hh ht) _) (ih hr)

private theorem poly_order {o : ℕ} (xs : List Term)
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

private theorem encoded_degree {e : E} {b : ℕ} (xs : List Term) (h : b < e.key)
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
