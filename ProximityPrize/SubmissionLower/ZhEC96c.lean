import ProximityPrize.SubmissionLower.ZkEPT8b
import ProximityPrize.SubmissionLower.ZocsBpe
set_option Elab.async false
namespace qGWTmVd
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe q1kuFjb
open qFD8jve (aFA sheetPole)
open cu (L FX)
open E7 (CurvePlace poleOrder KB Tq Gb)
open agN (b27)
open scoped Classical WithZero
open private efc adG cTA aMX b4s bHf from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E]
private theorem pole_le (v :Valuation E ℤᵐ⁰) {z :E} {b:ℕ}
   (h:v z≤WithZero.exp (b:ℤ)) :poleOrder v z≤b:= by
 by_cases hz :z=0
 · simp [hz,poleOrder]
 exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr hz)).mpr h)
private theorem restricted_bound {q:Curve} (B:CurveModel q) (F:Raw)
   (v :CurvePlace L B.E) :
   aFA v.value (restrict B F) (height F*Tq v.value B.seed) := by
 let b:=Tq v.value B.seed
 have hs (k :Fin 2) :v.value (B.seed k)≤WithZero.exp (b:ℤ) := by
   apply WithZero.le_exp_of_log_le
   exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr (Finset.le_sup
     (f := fun k=>poleOrder v.value (B.seed k)) (mem_univ k)))
 have hconst (a :L) :v.value (algebraMap L B.E a)≤1 := by
   by_cases ha :a=0
   · simp [ha]
   exact (v.on_constants a ha).le
 intro i j
 rw [restrict_coeff]
 apply v.value.map_sum_le
 intro a ha
 have hd' := (Qt.Qc (embed F) (height F)).mp le_rfl i
 have ha' : a∈((embed F).coeff i).support := by
   simpa only [embed,coe_mapRingHom,coeff_map,
     MvPolynomial.support_map_of_injective _ (IsFractionRing.injective L[X] FX)] using ha
 have hd:a.sum (fun _ n=>n)≤height F :=
   (Finset.le_sup (f := fun a=>a.sum fun _ n=>n) ha').trans hd'
 rw [map_mul,Finsupp.prod,map_prod]
 calc
   _≤1 * ∏ k∈a.support,(WithZero.exp (b:ℤ))^a k :=
     mul_le_mul' (hconst _) (prod_le_prod fun k _=> by rw [map_pow]; exact pow_le_pow_left' (hs k) _)
   _=WithZero.exp ((a.sum (fun _ n=>n)*b:ℕ) :ℤ) := by
     rw [one_mul,prod_pow_eq_pow_sum,← WithZero.exp_nsmul]
     simp [Finsupp.sum]
   _≤_:=WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (Nat.mul_le_mul_right _ hd))
private def gauss₂ (v :Valuation E ℤᵐ⁰) :Valuation E[X][X] ℤᵐ⁰ :=
 (efc (b4s v)).comap (mapRingHom (algebraMap E[X] (RatFunc E)))
private theorem coeff_le_gauss₂ (v :Valuation E ℤᵐ⁰) (f :E[X][X]) (i j:ℕ) :
  v ((f.coeff i).coeff j)≤gauss₂ v f := by
 apply (aMX v _ j).trans
 have h:=aMX (b4s v) (f.map (algebraMap E[X] (RatFunc E))) i
 rw [coeff_map,bHf] at h
 exact h
private theorem gauss₂_bound (v :Valuation E ℤᵐ⁰) (f :E[X][X]) {b:ℕ}
  (h:aFA v f b) :gauss₂ v f≤WithZero.exp (b:ℤ) := by
 change adG (b4s v) (f.map (algebraMap E[X] (RatFunc E)))≤_
 apply Finset.sup_le
 intro i _
 rw [coeff_map,bHf]
 exact Finset.sup_le fun j _=>h i j
private theorem gauss₂_C (v :Valuation E ℤᵐ⁰) (c:E) :
  gauss₂ v (C (C c))=v c:= by
 change adG (b4s v) ((C (C c) :E[X][X]).map _)= _
 rw [map_C,cTA,bHf,cTA]
private theorem gauss₂_normal (v :Valuation E ℤᵐ⁰) (f :E[X][X]) (h:headScalar f=1) :
  gauss₂ v f=WithZero.exp (sheetPole v f :ℤ) := by
 refine (gauss₂_bound v f (qrezXJe.sheet_bound v f)).antisymm ?_
 have hm:=coeff_le_gauss₂ v f f.natDegree (f.coeff f.natDegree).natDegree
 rw [coeff_natDegree,show (f.coeff f.natDegree).leadingCoeff=1 from h,map_one] at hm
 have hn:=(zero_lt_one.trans_le hm).ne'
 apply (WithZero.le_log_iff_exp_le hn).mp
 have hlog:0≤WithZero.log (gauss₂ v f) :=
  (WithZero.le_log_iff_exp_le hn).mpr (by simpa using hm)
 rw [← Int.toNat_of_nonneg hlog]
 apply Int.ofNat_le.mpr
 apply Finset.sup_le
 intro ij _
 apply pole_le v
 rw [Int.toNat_of_nonneg hlog,WithZero.exp_log hn]
 exact coeff_le_gauss₂ v f ij.1 ij.2
theorem factor_heights {q:Curve} (B:CurveModel q)
   (hB:Gb L B.E B.seed≤q.totalDegree) (F:Raw)
   (hF:restrict B F≠0) (S:Factorization (restrict B F)) :
   (∑ᶠ v :CurvePlace L B.E,poleOrder v.value (headScalar (restrict B F)))≤height F*q.totalDegree ∧
   coeffHeight (C S.amm) + ∑ j,coeffHeight (S.f j)≤height F*q.totalDegree := by
 let c:=headScalar (restrict B F)
 let V:=CurvePlace L B.E
 let P (v :V) :=poleOrder v.value c
 let Ju (v :V) :=KB v.value c
 let H (v :V) :=Tq v.value B.seed
 let A (v :V) :=sheetPole v.value (C S.amm)
 let T (j:Fin S.n) (v :V) :=sheetPole v.value (S.f j)
 have hn:c≠0:=b5S hF
 have hP (v :V) :P v≤height F*H v :=
   pole_le v.value (by
     change v.value ((restrict B F).coeff (restrict B F).natDegree).leadingCoeff≤_
     rw [← coeff_natDegree]
     exact restricted_bound B F v _ _)
 have hlocal (v :V) :P v+(A v + ∑ j,T j v)≤height F*H v+Ju v := by
   have hg:=gauss₂_bound v.value _ (restricted_bound B F v)
   rw [S.product,map_mul,map_prod] at hg
   rw [show C (C c*S.amm)=C (C c)*C S.amm from map_mul C _ _,
     map_mul,gauss₂_C,gauss₂_normal v.value _ (by rw [head_C]; exact S.monic)] at hg
   have he (j:Fin S.n) :gauss₂ v.value (S.f j)=WithZero.exp (T j v :ℤ) :=
     gauss₂_normal v.value _ (S.normalized j)
   simp_rw [he] at hg
   have hs : (∏ j,WithZero.exp (T j v :ℤ))=WithZero.exp ((∑ j,T j v :ℕ) :ℤ) := by
     rw [Nat.cast_sum]
     let φ:ℤ →+ Additive ℤᵐ⁰:=⟨⟨WithZero.exp,WithZero.exp_zero⟩,WithZero.exp_add⟩
     exact (map_sum φ _ _).symm
   change (v.value c*WithZero.exp (A v :ℤ))*(∏ j,WithZero.exp (T j v :ℤ)) ≤
     WithZero.exp ((height F*H v :ℕ) :ℤ) at hg
   rw [hs,mul_assoc,← WithZero.exp_add,← WithZero.exp_log (v.value.ne_zero_iff.mpr hn),
     ← WithZero.exp_add,WithZero.exp_le_exp] at hg
   change (WithZero.log (v.value c)).toNat+(A v + ∑ j,T j v) ≤
     height F*H v+(-WithZero.log (v.value c)).toNat
   omega
 obtain ⟨hp,hz,heq,_⟩:=principal B c
 have hh:H.HasFiniteSupport:=b27 (principal B) _
 have ha :A.HasFiniteSupport:=b27 (principal B) _
 have ht (j:Fin S.n) : (T j).HasFiniteSupport:=b27 (principal B) _
 have hts : (fun v => ∑ j,T j v).HasFiniteSupport :=
   Function.HasFiniteSupport.sum ht univ
 have hh' : (fun v=>height F*H v).HasFiniteSupport:=Function.HasFiniteSupport.mul_right _ hh
 have hmain: (∑ᶠ v,(P v+(A v + ∑ j,T j v))) ≤
     ∑ᶠ v,(height F*H v+Ju v) :=
   finsum_le_finsum (hp.add (ha.add hts)) (hh'.add hz) hlocal
 have hl: (∑ᶠ v,(P v+(A v + ∑ j,T j v))) =
     (∑ᶠ v,P v)+(∑ᶠ v,(A v + ∑ j,T j v)) :=finsum_add_distrib hp (ha.add hts)
 have hm: (∑ᶠ v,(A v + ∑ j,T j v)) =
     (∑ᶠ v,A v)+(∑ j,∑ᶠ v,T j v) := by
   calc
     _=(∑ᶠ v,A v)+(∑ᶠ v,∑ j,T j v) :=finsum_add_distrib ha hts
     _ = _:=congrArg ((∑ᶠ v,A v) + ·) (finsum_sum_comm univ (fun v j=>T j v) (fun j _=>ht j))
 have hr : (∑ᶠ v,(height F*H v+Ju v)) =
     height F*(∑ᶠ v,H v)+(∑ᶠ v,P v) := by
   calc
     _=(∑ᶠ v,(height F*H v))+(∑ᶠ v,Ju v) :=finsum_add_distrib hh' hz
     _ = _:=congrArg₂ (· + ·) (mul_finsum' H (height F) hh).symm heq.symm
 rw [hl,hm,hr] at hmain
 have hs : (∑ᶠ v,P v)≤(∑ᶠ v,(height F*H v)) :=finsum_le_finsum hp hh' hP
 rw [← mul_finsum' H (height F) hh] at hs
 have hbound:height F*(∑ᶠ v,H v)≤height F*q.totalDegree :=Nat.mul_le_mul_left _ hB
 exact ⟨hs.trans hbound,(Nat.le_of_add_le_add_left
   (hmain.trans_eq (Nat.add_comm _ _))).trans hbound⟩
end
end qGWTmVd
