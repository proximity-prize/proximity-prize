import ProximityPrize.SubmissionLower.Z2L10ra
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.ZcC9kBb
import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
open _root_ renaming Algebra.IsSeparable → zw7, Algebra.lmul → zXA, Function.Surjective → zpX, Int.natCast_nonneg → zbO, Int.toNat_eq_max → zDc, LinearMap.range → zWl, Module.finrank → zsE, Polynomial.X → z7y, Polynomial.coeff_X_zero → zfr
section
set_option autoImplicit true
namespace qzM5sEd
noncomputable section
open aR (ao)
open Rj (lK kJ acw m5)
open qlc9qed (Bank)
open qPQ4nYa
private theorem c4g (b : Bank) (q k : ℕ) (p : kJ) :
    zsE ao (zWl (aPi b q (offset b k))) ≤ xR b q (offset b k) p := by
  let f := aPi b q (offset b k)
  by_cases hcut : Ic b q (offset b k) ≤ 0
  · have hz : f = 0 := by
      ext L : 1
      change MvPolynomial.weightedTruncation (![2, 0, 1] : Fin 3 → ℕ)
        (Ic b q (offset b k)).toNat (MvPolynomial.bind₁ acw (L : lK)) = 0
      apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
      simp [Int.toNat_of_nonpos hcut]
    change zsE ao (zWl f) ≤ _
    simp [hz, xR, hcut]
  have hdim := f.finrank_range_add_finrank_ker
  have hcols := gte b q (offset b k)
  have hshift := plane_kernel_lower b q (offset b k) p
  have hbase := plane_kernel_lower b q (offset b k) (fun _ => 0)
  have hdeg : K6 b q (fun _ => 0) = iO b q := by simp [K6]
  have hflag : D8 b q (offset b k) (fun _ => 0) = pT b q (offset b k) := by
    funext i
    simp only [D8, Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [hdeg, hflag] at hbase
  change _ ≤ (zsE ao (LinearMap.ker f) : ℤ) at hshift hbase
  have hlower := max_le (zbO (zsE ao (LinearMap.ker f)))
    (max_le hbase hshift)
  change zsE ao (zWl f) ≤ _
  unfold xR
  simp only [hcut, ite_false]
  have hbound : (zsE ao (zWl f) : ℤ) ≤
      Bb b q (offset b k) -
        max 0 (max (m5 (iO b q) (pT b q (offset b k)))
          (m5 (K6 b q p) (D8 b q (offset b k) p))) := by
    omega
  simpa using Int.toNat_le_toNat hbound
end
end qzM5sEd
end
section
section
set_option maxRecDepth 8192
namespace qmb8rCe
open aR (Shape)
open qOPkAYa (base Filed)
def c1 :Prop :=
  ∀ q d h:ℕ,q≤15→d≤q→h≤27→ rankCut box q d h≤ cap box q d h
def c2 :Prop :=
  ∀ q d h:ℕ,15<q→q<27→d≤q→h≤27→ rankCut box q d h≤ cap box q d h
def c3:Prop :=
  ∀ d h:ℕ,d≤27→h≤27→ rankCut box 27 d h≤ cap box 27 d h
theorem gen (a :Shape) (U d n:ℕ) (hb:0<a.b) (hU:a.b≤U + 1)
    (hc : ∀ q d h:ℕ,q≤a.j→d≤q→h≤a.j→ rankCut a q d h≤ cap a q d h)
    (hF:Filed a d) (hn:sumN (base a) (a.b+1)=n) :
    qzLARrc.windowBudget a U≤(U + 1)*n+d:= by
  obtain ⟨h1,h2⟩:=hF
  rw [hn] at h1 h2
  refine (window_le_cost _ _ hc).trans ?_
  rw [qOPkAYa.cost_linear _ _ hb hU]
  refine (Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2).trans_eq ?_
  rw [← Nat.add_assoc,← Nat.add_mul,Nat.sub_add_cancel hU]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qzLARrc.c3:= by
  refine gen ⟨87,27,12⟩ 640 15643160 991536 (by decide) (by decide) ?_ qPzVOea.proof ?_
  · intro q d h hq hd hh
    change q≤27 at hq
    by_cases hl:q≤15
    · exact h1 q d h hl hd hh
    by_cases he :q=27
    · subst q; exact h3 d h hd hh
    exact h2 q d h (by omega) (by omega) hd hh
  · refine (qOPkAYa.b6N (⟨⟨64,87,27,640⟩,12,0,0⟩:P5_7_2.TopRow)).symm.trans ?_
    simp only [q7IA62d.ama,Finset.sum_const,Finset.card_range,smul_eq_mul]
    decide
end qmb8rCe
end
section
set_option autoImplicit true
section
namespace qv2t4Be
noncomputable section
abbrev CommonField (K F:Type) [Field K] [Field F] [Algebra K F] :=
 IntermediateField.normalClosure K F (AlgebraicClosure F)
end
end qv2t4Be
end
section
open Polynomial renaming coeff_sub→qz0,mul_coeff_zero→qz1
namespace qv2t4Be
noncomputable section
open Polynomial Finset
open scoped WithZero
open P5_7_1_7_4_3_4 (adG)
open E7 (KB)
open private b4s bHf aMX efd cTA from ProximityPrize.SubmissionLower.Y
open private eFr from ProximityPrize.SubmissionLower.Y
variable {K F:Type} [Field K] [Field F]
abbrev gaussExtension (u:Valuation K ℤᵐ⁰) :Valuation (RatFunc K) ℤᵐ⁰ :=
 b4s u
theorem gauss_polynomial (u:Valuation K ℤᵐ⁰) (g:K[X]) :
  gaussExtension u (algebraMap K[X] (RatFunc K) g)=adG u g :=
 bHf u g
theorem gauss_surjective (u:Valuation K ℤᵐ⁰) (hu:zpX u) :
  zpX (gaussExtension u) := by
 intro a
 obtain ⟨x,hx⟩:=hu a
 exact ⟨algebraMap K[X] (RatFunc K) (C x),
  (gauss_polynomial u (C x)).trans ((cTA u x).trans hx)⟩
theorem scaled_restriction (u:Valuation K ℤᵐ⁰) (v :Valuation F ℤᵐ⁰)
   (m:RatFunc K →+* F) (n:ℕ)
   (h : ∀ g:K[X],v (m (algebraMap K[X] (RatFunc K) g))=adG u g^n)
   (x :RatFunc K) :v (m x)=gaussExtension u x^n:= by
 induction x using RatFunc.induction_on with
 | _ g d hd =>
   rw [map_div₀,v.map_div,(gaussExtension u).map_div,div_pow,
     gauss_polynomial,gauss_polynomial,h,h]
theorem eq_of_scaled {v w:Valuation F ℤᵐ⁰}
  (hv :zpX v) (hw:zpX w) {a b:ℕ}
  (ha :0<a) (hb:0<b) (h : ∀ x,v x^a=w x^b) :v=w:= by
 apply eFr hv hw
 intro x y
 rw [← pow_le_pow_iff_left₀ zero_le zero_le ha.ne',h,h,
  pow_le_pow_iff_left₀ zero_le zero_le hb.ne']
private theorem charpoly_split_closed [Algebra K F] [Module.Finite K F]
   [zw7 K F] [Infinite K] (q:F) :
   (zXA K F q).charpoly.map (algebraMap K (AlgebraicClosure F)) =
     ∏ σ:F →ₐ[K] AlgebraicClosure F,(z7y - C (σ q)) := by
 classical
 apply Polynomial.eq_of_infinite_eval_eq
 refine (Set.infinite_range_of_injective (algebraMap K (AlgebraicClosure F)).injective).mono ?_
 rintro _ ⟨t,rfl⟩
 change Polynomial.eval (algebraMap K (AlgebraicClosure F) t) _ = _
 rw [Polynomial.eval_map_algebraMap,Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
   LinearMap.eval_charpoly]
 have hs :zXA K F (algebraMap K F t) =
     algebraMap K (Module.End K F) t:=(zXA K F).commutes t
 rw [← hs,← map_sub,← Algebra.norm_apply,
   Algebra.norm_eq_prod_embeddings K (AlgebraicClosure F)]
 simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
   map_sub,AlgHom.commutes]
theorem charpoly_split [Algebra K F] [Module.Finite K F] [zw7 K F]
   [Infinite K] (q:F) :
   (zXA K F q).charpoly.map (algebraMap K (CommonField K F)) =
     ∏ σ:F →ₐ[K] CommonField K F,(z7y - C (σ q)) := by
 classical
 let Ω:=CommonField K F
 let j:Ω →ₐ[K] AlgebraicClosure F:=(Ω:IntermediateField K (AlgebraicClosure F)).val
 apply Polynomial.map_injective j.toRingHom j.injective
 have hcomp:j.toRingHom.comp (algebraMap K (CommonField K F)) =
     algebraMap K (AlgebraicClosure F) :=RingHom.ext j.commutes
 rw [Polynomial.map_map,hcomp]
 rw [charpoly_split_closed,Polynomial.map_prod]
 refine Fintype.prod_equiv (normalClosure.algHomEquiv K F
   (AlgebraicClosure F)).symm _ _ ?_
 intro σ
 simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
 congr 2
def order (w:Valuation K ℤᵐ⁰) (x :K) :ℤ := -WithZero.log (w x)
def charge (w:Valuation K ℤᵐ⁰) (P:K[X]) :ℤ :=
 order w (P.coeff 0)+WithZero.log (adG w P)
theorem order_pow_scale (u:Valuation K ℤᵐ⁰) (v :Valuation F ℤᵐ⁰)
  (x :K) (y :F) (n:ℕ) (h:v y=u x^n) :
  order v y=(n:ℤ)*order u x := by
 simp [order,h,WithZero.log_pow,← mul_neg]
private theorem gauss_mul (u:Valuation K ℤᵐ⁰) (P Q:K[X]) :
 adG u (P*Q)=adG u P*adG u Q:=efd u P Q
private theorem dMr (u:Valuation K ℤᵐ⁰) (P:K[X]) (n:ℕ) :
 u (P.coeff n)≤adG u P:=aMX u P n
private theorem gauss_ne (u:Valuation K ℤᵐ⁰) {P:K[X]} (hp:P.coeff 0≠0) :
   adG u P≠0 :=
 ((zero_lt_iff.mpr (u.ne_zero_iff.mpr hp)).trans_le (dMr u P 0)).ne'
private theorem charge_nonneg (u:Valuation K ℤᵐ⁰) {P:K[X]} (hp:P.coeff 0≠0) :
  0≤ charge u P:= by
 have h:=(WithZero.log_le_log (u.ne_zero_iff.mpr hp) (gauss_ne u hp)).mpr
  (dMr u P 0)
 unfold charge order
 omega
private theorem charge_mul (u:Valuation K ℤᵐ⁰) {P Q:K[X]}
  (hp:P.coeff 0≠0) (hq:Q.coeff 0≠0) :
  charge u (P*Q)=charge u P+charge u Q:= by
 simp only [charge,order,qz1,map_mul,gauss_mul,
  WithZero.log_mul (u.ne_zero_iff.mpr hp) (u.ne_zero_iff.mpr hq),
  WithZero.log_mul (gauss_ne u hp) (gauss_ne u hq)]
 abel
theorem charge_dvd_le (u:Valuation K ℤᵐ⁰) {P Q:K[X]} (hp:P.coeff 0≠0)
   (hq:Q∣P) (h : ∀ j,u (P.coeff j)≤1) :charge u Q≤order u (P.coeff 0) := by
 obtain ⟨R,rfl⟩:=hq
 rw [qz1] at hp
 have hNR:=charge_nonneg u (right_ne_zero_of_mul hp)
 have hmul :=charge_mul u (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)
 have hlog:=(WithZero.log_le_log (gauss_ne u
   (show (Q*R).coeff 0≠0 by rwa [qz1])) one_ne_zero).mpr
     (Finset.sup_le fun j _=>h j)
 rw [WithZero.log_one] at hlog
 have hQR:charge u Q≤ charge u (Q*R) := by omega
 exact hQR.trans (by unfold charge; omega)
private theorem linear_gauss (u:Valuation K ℤᵐ⁰) (x :K) :
   adG u (z7y - C x)=max 1 (u x) := by
 refine le_antisymm (Finset.sup_le fun j _ => ?_) (max_le ?_ ?_)
 · by_cases h0:j=0
   · subst j
     simp
   by_cases h1 :j=1
   · subst j
     simp
   simp [qz0,Polynomial.coeff_X,Polynomial.coeff_C,h0,Ne.symm h1]
 · have h:=dMr u (z7y - C x) 1
   rwa [qz0,Polynomial.coeff_X_one,coeff_C_succ,sub_zero,map_one] at h
 · have h:=dMr u (z7y - C x) 0
   rwa [qz0,zfr,coeff_C_zero,zero_sub,
     Valuation.map_neg] at h
private theorem charge_linear (u:Valuation K ℤᵐ⁰) {x :K} (hx :x≠0) :
   charge u (z7y - C x)=(KB u x :ℤ) := by
 simp only [charge,order,qz0,zfr,coeff_C_zero,
   zero_sub,Valuation.map_neg,linear_gauss,KB,zDc]
 by_cases h:u x≤1
 · have h' := (WithZero.log_le_log (u.ne_zero_iff.mpr hx) one_ne_zero).mpr h
   simp only [WithZero.log_one] at h'
   simp [max_eq_left h,max_eq_left (neg_nonneg.mpr h')]
 · have hle :=le_of_lt (lt_of_not_ge h)
   have h' := (WithZero.log_le_log one_ne_zero (u.ne_zero_iff.mpr hx)).mpr hle
   simp only [WithZero.log_one] at h'
   simp [max_eq_right hle,max_eq_right (neg_nonpos.mpr h')]
theorem charge_product {ι:Type} (u:Valuation K ℤᵐ⁰) (S:Finset ι) (x :ι→K)
   (hx : ∀ i,x i≠0) :
   charge u (∏ i∈S,(z7y - C (x i))) = ∑ i∈S,(KB u (x i) :ℤ) := by
 classical
 induction S using Finset.induction_on with
 | empty=>simp [charge,order,show adG u 1=u 1 from cTA u 1]
 | @insert j S hj ih =>
   rw [Finset.prod_insert hj,Finset.sum_insert hj,charge_mul u,charge_linear u (hx j),ih]
   · simpa using hx j
   · rw [Polynomial.coeff_zero_prod]
     exact Finset.prod_ne_zero_iff.mpr (fun i _=> by simpa using hx i)
theorem zero_scale {u:Valuation K ℤᵐ⁰} {v :Valuation F ℤᵐ⁰}
  {x :K} {y :F} {n:ℕ} (h:v y=u x^n) :
  (KB v y :ℤ)=(n:ℤ)*(KB u x :ℤ) := by
 change ((order v y).toNat :ℤ)=(n:ℤ)*((order u x).toNat :ℤ)
 rw [order_pow_scale _ _ _ _ _ h,zDc,zDc,
  mul_max_of_nonneg _ _ (zbO n),mul_zero]
end
end qv2t4Be
end
end
end
