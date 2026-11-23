import ProximityPrize.SubmissionLower.Z3aw2hc
import ProximityPrize.SubmissionLower.ZocsBpe
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace q8Z6NHc
noncomputable section
open Polynomial Finset
open cu (L)
open P5 (p)
open qZu9hjc (Slice HE valueCoeffs valueDegree)
open qb0hmCe (coeffHeight)
open qFD8jve (sheetPole)
open E7 (CurvePlace poleOrder KB Tq Gb axV)
open agN (b27)
open private efc adG cTA efd aMX from ProximityPrize.SubmissionLower.Y
open scoped Classical WithZero
def c1 :Prop :=
  ∀ (d s a :ℕ),2≤d→d<p→d*s≤a →
    ∀ (b c:L),c≠0→Nonempty (UniversalValue d s a b c)
def c2 :Prop :=
  ∀ (d s a :ℕ),2≤d→d<p→d*s≤a →
    ∀ (b c:L),c≠0 → ∀ (V:UniversalValue d s a b c) i,
      ((V.R.coeff i).totalDegree :ℤ)≤ rawDegree d a s - boundary d a s
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (f :E[X][X]) (s a :ℕ),
    2≤f.natDegree→f.natDegree<p→f.natDegree*s≤a→HE f s a →
    ∀ (T:Slice f s a) (V:UniversalValue f.natDegree s a T.b T.c),
      ∃ (δ:Index f.natDegree s a→L) (n:ℕ),
        let P:=extract (actualCoeffs f T.g) δ V.R n
        P≠0∧T.N∣P
variable {E :Type} [Field E] [Algebra L E]
private theorem extract_coeff {d s a :ℕ} (α:Index d s a→E) (δ:Index d s a→L)
   (R: (jo d s a)[X]) (n i:ℕ) :
   (extract α δ R n).coeff i=(perturb α δ (R.coeff i)).coeff n:= by
 classical
 by_cases hi:i∈R.support
 · simp [extract,Polynomial.sum_def,finsetSum_coeff,coeff_monomial,hi]
 · simp [extract,Polynomial.sum_def,finsetSum_coeff,coeff_monomial,hi,
     notMem_support_iff.mp hi,perturb]
private theorem perturb_bound {d s a m B:ℕ} (v :CurvePlace L E)
    (α:Index d s a→E) (δ:Index d s a→L)
    (hα : ∀ i,v.value (α i)≤WithZero.exp (B:ℤ))
    (r :jo d s a) (hr :r.totalDegree≤ m) (n:ℕ) :
    v.value ((perturb α δ r).coeff n)≤WithZero.exp ((m*B:ℕ) :ℤ) := by
  let w:=efc v.value
  have hc (z :L) :v.value (algebraMap L E z)≤1 := by
    by_cases hz :z=0
    · simp [hz]
    · exact (v.on_constants z hz).le
  have hX:w (Polynomial.X:E[X])≤1 := by
    change adG v.value Polynomial.X≤1
    apply Finset.sup_le
    intro i _
    rw [coeff_X]
    split <;> simp
  have hvar (i:Index d s a) :
      w (C (α i)+C (algebraMap L E (δ i))*(Polynomial.X:E[X]))≤WithZero.exp (B:ℤ) := by
    apply w.map_add_le
    · change adG v.value (C (α i))≤_
      rw [cTA]
      exact hα i
    · rw [map_mul]
      change adG v.value (C (algebraMap L E (δ i)))*w Polynomial.X≤_
      rw [cTA]
      exact ((mul_le_mul' (hc _) hX).trans_eq (one_mul _)).trans (by simp)
  apply (aMX v.value _ n).trans
  change w (perturb α δ r)≤_
  rw [perturb,MvPolynomial.eval₂_eq]
  apply w.map_sum_le
  intro u hu
  rw [map_mul,map_prod]
  calc
    _≤1 * ∏ i∈u.support,(WithZero.exp (B:ℤ))^u i :=
      mul_le_mul' (by
        change adG v.value (C (algebraMap L E (r.coeff u)))≤1
        rw [cTA]
        exact hc _) (prod_le_prod fun i _=> by rw [map_pow]; exact pow_le_pow_left' (hvar i) _)
    _=WithZero.exp ((u.sum (fun _ e=>e)*B:ℕ) :ℤ) := by
      rw [one_mul,prod_pow_eq_pow_sum,← WithZero.exp_nsmul]
      simp [Finsupp.sum]
    _≤_:=WithZero.exp_le_exp.mpr
      (Int.ofNat_le.mpr (Nat.mul_le_mul_right B ((MvPolynomial.le_totalDegree hu).trans hr)))
private theorem factor_height (hdiv :axV L E) (f :E[X][X])
   (m:ℕ) {N P:E[X]} (hN :N.Monic) (hP:P≠0) (hdvd:N∣P)
   (hB : ∀ (v :CurvePlace L E) i,v.value (P.coeff i) ≤
     WithZero.exp ((m*sheetPole v.value f :ℕ) :ℤ)) :
   Gb L E (valueCoeffs N)≤ m*coeffHeight f := by
 obtain ⟨Q,rfl⟩:=hdvd
 have hQ:Q≠0:= fun h=>hP (by simp [h])
 let a := Q.leadingCoeff
 have ha :a≠0:=leadingCoeff_ne_zero.mpr hQ
 let H (v :CurvePlace L E) :=sheetPole v.value f
 let T (v :CurvePlace L E) :=Tq v.value (valueCoeffs N)
 let po (v :CurvePlace L E) :=poleOrder v.value a
 let zo (v :CurvePlace L E) :=KB v.value a
 have hlocal (v :CurvePlace L E) :T v+po v≤ m*H v+zo v := by
   have hb:adG v.value (N*Q)≤WithZero.exp ((m*H v :ℕ) :ℤ) :=
     Finset.sup_le fun i _=>hB v i
   rw [efd] at hb
   have hval :adG v.value N*v.value a≤WithZero.exp ((m*H v :ℕ) :ℤ) :=
     (mul_le_mul' le_rfl (aMX v.value Q Q.natDegree)).trans hb
   have hN1 :1≤adG v.value N := by
     simpa only [hN.coeff_natDegree,map_one] using aMX v.value N N.natDegree
   have hne :=(zero_lt_one.trans_le hN1).ne'
   have hp:0≤WithZero.log (adG v.value N) :=WithZero.le_log_of_exp_le (by simpa using hN1)
   have hT:T v≤(WithZero.log (adG v.value N)).toNat := by
     apply Finset.sup_le
     intro i _
     have hi:=aMX v.value N i.val
     change (WithZero.log (v.value (N.coeff i))).toNat≤_
     by_cases hz :v.value (N.coeff i)=0
     · simp [hz]
     · exact Int.toNat_le_toNat ((WithZero.log_le_log hz hne).mpr hi)
   rw [← WithZero.exp_log hne,← WithZero.exp_log (v.value.ne_zero_iff.mpr ha),
     ← WithZero.exp_add,WithZero.exp_le_exp] at hval
   change T v+(WithZero.log (v.value a)).toNat≤ m*H v+(-WithZero.log (v.value a)).toNat
   omega
 obtain ⟨hpo,hzo,heq,_⟩:=hdiv a
 change po.HasFiniteSupport at hpo
 change zo.HasFiniteSupport at hzo
 change (∑ᶠ v,po v)=(∑ᶠ v,zo v) at heq
 have hT:T.HasFiniteSupport:=b27 hdiv _
 have hH :H.HasFiniteSupport:=b27 hdiv _
 have hM: (fun v=>m*H v).HasFiniteSupport:=Function.HasFiniteSupport.mul_right _ hH
 have hsum:=finsum_le_finsum (hT.add hpo) (hM.add hzo) hlocal
 change (∑ᶠ v,(T v+po v))≤(∑ᶠ v,(m*H v+zo v)) at hsum
 rw [finsum_add_distrib hT hpo,finsum_add_distrib hM hzo,← mul_finsum' H m hH,← heq] at hsum
 exact Nat.le_of_add_le_add_right hsum
theorem of_children (ek :c1) (degree :c2) (specialize :c3) :qZu9hjc.c3:= by
 intro E _ _ hcurve f s a hd hp ha hf T
 obtain ⟨V⟩:=ek _ s a hd hp ha T.b T.c T.c_ne
 obtain ⟨δ,n,hn,hN⟩:=specialize f s a hd hp ha hf T V
 have hdiv :axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hcurve
 refine factor_height hdiv f _ T.monic hn hN fun v i => ?_
 have hdegree :=degree _ s a hd hp ha T.b T.c T.c_ne V i
 have he :rawDegree f.natDegree a s - boundary f.natDegree a s=valueDegree f.natDegree a s := by
   unfold rawDegree boundary kK valueDegree
   ring
 rw [he] at hdegree
 have hm:=Int.toNat_le_toNat hdegree
 rw [Int.toNat_natCast] at hm
 change v.value ((extract (actualCoeffs f T.g) δ V.R n).coeff i)≤_
 rw [extract_coeff]
 refine perturb_bound v _ δ (fun j => ?_) _ hm n
 cases j with
 | inl j=>exact qrezXJe.sheet_bound v.value f _ _
 | inr j =>
   exact (qrezXJe.sheet_bound v.value T.g _ _).trans
     (WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (T.common v)))
end
end q8Z6NHc
