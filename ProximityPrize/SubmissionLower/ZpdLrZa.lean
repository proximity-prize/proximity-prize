import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.Zzjdkoa
import ProximityPrize.SubmissionLower.ZHTtOyb
import ProximityPrize.SubmissionLower.ZTNQi7d
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qAW6lac
noncomputable section
open Finset Polynomial
open scoped Classical WithZero
open cu (L)
open P5 (p)
open qNu3xvc (Equation)
open qZV9OWb (ValueSlice rate)

open E7 (CurvePlace axV)
open private factor_height from ProximityPrize.SubmissionLower.ZHTtOyb
open private gauss₂ coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
open private val_const val_outer val_X from ProximityPrize.SubmissionLower.ZTNQi7d
open private cTA from ProximityPrize.SubmissionLower.Y
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
def c1 :Prop :=
  ∀ d s W:ℕ,0<s→s<p→2≤d→d<p→d*s≤W →
    Nonempty (Eliminant d s W)
def c2 :Prop :=
  ∀ d s W:ℕ,0<s→s<p→2≤d→d<p→d*s≤W →
    ∀ (R:Eliminant d s W) (m:Index d s W →₀ ℕ),m∈R.poly.support →
      ∀ k :Fin 3,m.sum (fun i n=>if block i=k then n else 0)≤ng d s W k
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),0<A.s→2≤A.d →
    ∀ (B:ValueSlice A) (R:Eliminant A.d A.s (A.b+A.d*A.s)),
      ∃ (δ:Index A.d A.s (A.b+A.d*A.s)→L) (n:ℕ),
        let P:=extract (actualCoeffs A.f B.g A.f.derivative) δ R.poly n
        P≠0∧B.N∣P
private theorem allowance_sum {d s W:ℕ} (hd:2≤d) (hW:d*s≤W) :
  (∑ k :Fin 3,ng d s W k)=rate d s W:= by
 simp only [Fin.sum_univ_three,ng,pairDegree,rate]
 have h0: (0:Fin 3)≠2 := by decide
 have h1 : (1 :Fin 3)≠2 := by decide
 simp only [h0,h1,ite_false,ite_true]
 have hs :s≤W:=(Nat.le_mul_of_pos_left _ (by omega :0<d)).trans hW
 have hA:d*d*s≤d*W+d*W:= calc
  _=d*(d*s) := by ring
  _≤d*W:=Nat.mul_le_mul_left _ hW
  _≤_:=Nat.le_add_right _ _
 have hB:d*(d-1)*s≤d*(W-s)+(d-1)*W:= calc
  _=(d-1)*(d*s) := by ring
  _≤(d-1)*W:=Nat.mul_le_mul_left _ hW
  _≤_:=Nat.le_add_left _ _
 have hR:3*d^2*s≤(6*d-2)*W:= calc
  _=(3*d)*(d*s) := by ring
  _≤_:=Nat.mul_le_mul (by omega) hW
 zify [show 1≤d by omega,show 2≤6*d by omega,hs,hA,hB,hR]
 ring
private theorem ags {d s W:ℕ} (hd:2≤d) (hW:d*s≤W)
   (R:jo d s W)
   (h : ∀ m∈R.support,∀ k :Fin 3,
     m.sum (fun i n=>if block i=k then n else 0)≤ng d s W k) :
   R.totalDegree≤ rate d s W:= by
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro m hm
 have hs : (∑ k :Fin 3,m.sum (fun i n=>if block i=k then n else 0)) =
     m.sum (fun _ n=>n) := by
   simp only [Finsupp.sum]
   rw [Finset.sum_comm]
   simp
 rw [← hs,← allowance_sum hd hW]
 exact sum_le_sum fun k _=>h m hm k
variable {E :Type} [Field E] [Algebra L E]
private theorem deform_bound {d s W m B:ℕ} (v :CurvePlace L E) (α:Index d s W→E)
    (δ:Index d s W→L) (hα : ∀ i,v.value (α i)≤WithZero.exp (B:ℤ))
    (R:jo d s W) (hr :R.totalDegree≤ m) (n i:ℕ) :
    v.value ((extract α δ R n).coeff i)≤WithZero.exp ((m*B:ℕ) :ℤ) := by
  let w:=gauss₂ v.value
  let b:=WithZero.exp (B:ℤ)
  have hb:1≤b:=WithZero.exp_le_exp.mpr (Int.natCast_nonneg B)
  have hc (a :E) :w (C (C a))=v.value a :=(val_const v.value _).trans (cTA v.value a)
  have hL (a :L) :w (C (C (algebraMap L E a)))≤1 := by
    rw [hc]
    by_cases ha :a=0
    · simp [ha]
    · exact (v.on_constants a ha).le
  have hε:w (C (Polynomial.X:E[X]))=1 :=(val_const v.value _).trans (val_X v.value)
  have hvar (j:Index d s W) :w (ic α δ j)≤b:= by
    unfold ic
    rw [sub_eq_add_neg]
    apply w.map_add_le
    · rw [map_add,map_mul]
      apply w.map_add_le
      · rw [hc]
        exact hα j
      · rw [map_mul,hε,mul_one]
        exact (hL _).trans hb
    · rw [Valuation.map_neg]
      split
      · rw [val_outer v.value]
        exact hb
      · rw [map_zero]
        exact zero_le
  rw [extract_coeff]
  refine (coeff_le_gauss₂ v.value _ i n).trans ?_
  change w (deform α δ R)≤_
  rw [deform,MvPolynomial.eval₂_eq]
  apply w.map_sum_le
  intro u hu
  rw [map_mul,map_prod]
  calc
    _≤1 * ∏ j∈u.support,b^u j :=
      mul_le_mul' (hL _) (prod_le_prod fun j _=> by rw [map_pow]; exact pow_le_pow_left' (hvar j) _)
    _=WithZero.exp ((u.sum (fun _ e=>e)*B:ℕ) :ℤ) := by
      rw [one_mul,prod_pow_eq_pow_sum]
      dsimp [b]
      simp [Finsupp.sum]
    _≤_:=WithZero.exp_le_exp.mpr
      (Int.ofNat_le.mpr (Nat.mul_le_mul_right B ((MvPolynomial.le_totalDegree hu).trans hr)))
theorem of_children (ek :c1) (degree :c2) (specialize :c3) :qZV9OWb.c5:= by
 intro E _ _ A hcurve hs hsp hd hp B
 have hW:A.d*A.s≤A.b+A.d*A.s :=Nat.le_add_left _ _
 obtain ⟨R⟩:=ek _ _ _ hs hsp hd hp hW
 obtain ⟨δ,n,hn,hN⟩:=specialize A hs hd B R
 have hdiv :axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hcurve
 refine factor_height hdiv A.f _ B.monic hn hN fun v i => ?_
 refine deform_bound v _ δ (fun j => ?_) R.poly
   (ags hd hW R.poly (degree _ _ _ hs hsp hd hp hW R)) n i
 rcases j with j | (j | j)
 · exact qrezXJe.sheet_bound v.value A.f _ _
 · exact (qrezXJe.sheet_bound v.value B.g _ _).trans
     (WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (B.common v)))
 · change v.value ((A.f.derivative.coeff j.val.1).coeff j.val.2)≤_
   rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast,coeff_mul_C,map_mul]
   exact (mul_le_mul' (qrezXJe.sheet_bound v.value A.f _ _)
     (cast_le_one (v :=v.value) _)).trans_eq (mul_one _)
end
end qAW6lac
