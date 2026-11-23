import ProximityPrize.SubmissionLower.ZWWU4Jd
import ProximityPrize.SubmissionLower.ZdnOpje
import ProximityPrize.SubmissionLower.ZoOOLsc
set_option Elab.async false
open _root_ renaming Algebra.adjoin_induction → z90, Function.Injective → zq4, IsFractionRing.injective → zxb, IsLocalization.lift → zvq, IsLocalization.lift_eq → zX4, Polynomial.X → z7y, Polynomial.X_ne_zero → z05, Polynomial.prime_X → zEx, PowerSeries.coeff → z2o, RingHom.comp_apply → zQb, RingHom.ext → zz4, RingHom.id → zz5, Subalgebra → zTg, Submonoid.powers → zSL
section
set_option backward.isDefEq.respectTransparency false
namespace qnCt0Qc
noncomputable section
open Polynomial
open scoped nonZeroDivisors
open P5 (K)
open cu (L FX jz)
open P5_7_7 (Dg phys)
open qrKC9pb
open qyUzJvd
private theorem map_inv_unit {R F:Type} [CommRing R] [Field F] (j:R →+* F) (u:Rˣ) :
  j (↑u⁻¹:R)=(j (↑u:R))⁻¹ :=
 eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
def markCoeff (z :K) :L[X][X] →+* FX :=
 (evalRingHom (jz z)).comp (mapRingHom phys)
def yq (z :K) (y :FX) :Dg →+* FX:=eval₂RingHom (markCoeff z) y
theorem atMark_pair (z :K) (P Q:L[X]) (G:Dg) :
  yq z (phys P/phys Q) G=qGnV2ac.atPair G z P Q:= by
 rw [yq,coe_eval₂RingHom,qGnV2ac.atPair,P5_7_7.embed,coe_mapRingHom,eval₂_map]
 rfl
theorem dIG (J:Input) (r :Bool) (z :K) (y :FX)
    (hroot :yq z y J.F=0) (hy :r=true→y≠0)
    (hs :yq z (if r then y⁻¹ else y) (chartEq J r).derivative≠0) :
    ∃ φ:Chart J r →ₐ[L] FX,
      (∀ G,φ (evalChart J r G)=yq z (if r then y⁻¹ else y) G) ∧
      (∀ i:Fin 4,φ (coord J r i) =
        ![phys z7y,jz z,if r then y⁻¹ else y,
          -(yq z (if r then y⁻¹ else y) (physicalDerivative (chartEq J r))) /
            yq z (if r then y⁻¹ else y) (chartEq J r).derivative] i) := by
  let A:=AdjoinRoot J.F
  let t:A →+* FX:=AdjoinRoot.lift (markCoeff z) y hroot
  let j:A →+* EC J:=algebraMap A _
  have ht (G:Dg) :t (AdjoinRoot.mk J.F G)=yq z y G :=
    AdjoinRoot.lift_mk hroot _
  let M:=(FX⁰).comap t
  have hm (a :A) :a∈M↔t a≠0:=mem_nonZeroDivisors_iff_ne_zero
  let B:=Localization M
  let i:A →+* B:=algebraMap A B
  let T:B →+* FX:=zvq (fun a :M=>((hm a).mp a.2).isUnit)
  let I:B →+* EC J:=zvq (fun a :M =>
    (show j a≠0 from fun e=>(hm a).mp a.2
      (by rw [(zxb A (EC J)) (e.trans (map_zero j).symm),map_zero])).isUnit)
  have hT (a :A) :T (i a)=t a :=zX4 _ _
  have hI (a :A) :I (i a)=j a :=zX4 _ _
  have hinj:zq4 I:= by
    apply (IsLocalization.injective_iff_map_algebraMap_eq M I).mpr
    intro a b
    change i a=i b↔I (i a)=I (i b)
    rw [hI,hI,(zxb A (EC J)).eq_iff]
    exact ⟨fun e=>(zxb A (EC J))
      ((hI a).symm.trans ((congrArg I e).trans (hI b))),congrArg i⟩
  have unit (a :B) (ha :T a≠0) :IsUnit a := by
    obtain ⟨⟨b,c⟩,h⟩:=IsLocalization.surj M a
    change a*i c=i b at h
    have hb:t b≠0:= by
      rw [← hT,← h,map_mul,hT]
      exact mul_ne_zero ha ((hm c).mp c.2)
    exact isUnit_of_mul_isUnit_left (h.symm ▸ IsLocalization.map_units B (⟨b,(hm b).mpr hb⟩:M))
  let R:=i.comp (AdjoinRoot.mk J.F)
  have hR (G:Dg) :I (R G)=a7W J G:=hI _
  have hS (G:Dg) :T (R G)=yq z y G:=(hT _).trans (ht _)
  let a :=R z7y
  have ha :T a=y :=(hS _).trans (eval₂_X _ _)
  have hu : ∃ b:B,I b=jU J r∧T b=(if r then y⁻¹ else y) := by
    cases r
    · exact ⟨a,hR _,ha⟩
    · let u:=unit a (ha ▸ hy rfl)
      refine ⟨↑u.unit⁻¹,?_,?_⟩
      · rw [map_inv_unit,IsUnit.unit_spec]
        exact congrArg Inv.inv (hR _)
      · rw [map_inv_unit,IsUnit.unit_spec,ha]
        rfl
  obtain ⟨b,hb,hbt⟩:=hu
  let g:=eval₂RingHom (R.comp C) b
  have hg (G:Dg) :I (g G)=KM J r G:= by
    have he :I.comp (R.comp C)=(a7W J).comp C:=zz4 (fun q=>hR (C q))
    dsimp only [g]
    rw [coe_eval₂RingHom,hom_eval₂,he,hb]
    rfl
  have hgt (G:Dg) :T (g G)=yq z (if r then y⁻¹ else y) G:= by
    have he :T.comp (R.comp C)=markCoeff z :=
      zz4 (fun q=>(hS (C q)).trans (eval₂_C _ _))
    dsimp only [g]
    rw [coe_eval₂RingHom,hom_eval₂,he,hbt]
    rfl
  let F:=chartEq J r
  let d:=g F.derivative
  let u:=unit d (by rwa [show T d= _ from hgt _])
  let v := -g (physicalDerivative F)*(↑u.unit⁻¹:B)
  have hv :I v=jet J r := by
    dsimp only [v]
    rw [map_mul,map_neg,map_inv_unit,IsUnit.unit_spec,hg,show I d= _ from hg _]
    rfl
  have hvt:T v = -(yq z (if r then y⁻¹ else y) (physicalDerivative F)) /
      yq z (if r then y⁻¹ else y) F.derivative := by
    dsimp only [v]
    rw [map_mul,map_neg,map_inv_unit,IsUnit.unit_spec,hgt,show T d= _ from hgt _,
      div_eq_mul_inv]
  let tup:Fin 4→B := ![R (C (C z7y)),R (C z7y),b,v]
  have hcoord (k :Fin 4) :I (tup k)=(coord J r k :EC J) := by
    fin_cases k
    · exact hR _
    · exact hR _
    · exact hb
    · exact hv
  have hconst (c:L) :I (R (C (C (C c))))=algebraMap L (EC J) c:=hR _
  have hrange : (Chart J r).toSubring≤I.range := by
    intro a ha
    change a∈Chart J r at ha
    induction ha using z90 with
    | mem a ha =>
      obtain ⟨k,rfl⟩:=ha
      exact ⟨tup k,hcoord k⟩
    | algebraMap c=>exact ⟨_,hconst c⟩
    | add a b _ _ ha hb=>exact I.range.add_mem ha hb
    | mul a b _ _ ha hb=>exact I.range.mul_mem ha hb
  let e :=RingEquiv.ofBijective I.rangeRestrict
    ⟨fun _ _ h=>hinj (congrArg Subtype.val h),RingHom.rangeRestrict_surjective _⟩
  let ψ:=e.symm.toRingHom.comp (Subring.inclusion hrange)
  have hψ (a :Chart J r) (q:B) (hq:I q=(a :EC J)) :ψ a=q:= by
    apply e.injective
    exact (e.apply_symm_apply (Subring.inclusion hrange a)).trans (Subtype.ext hq.symm)
  let φ:Chart J r →ₐ[L] FX :=
    { toRingHom:=T.comp ψ
      commutes' := fun c=> by
        change T (ψ (algebraMap L (Chart J r) c))= _
        rw [hψ _ _ (hconst c),hS]
        simp only [yq,coe_eval₂RingHom,eval₂_C,markCoeff,zQb,
          coe_mapRingHom,map_C,coe_evalRingHom,eval_C]
        rfl }
  refine ⟨φ,fun G => ?_,fun k => ?_⟩
  · change T (ψ (evalChart J r G))= _
    rw [hψ _ _ ((hg G).trans (coe_evalChart J r G).symm),hgt]
  · change T (ψ (coord J r k))= _
    rw [hψ _ _ (hcoord k)]
    fin_cases k
    · change T (R (C (C z7y)))= _
      rw [hS]
      simp [yq,markCoeff]
    · change T (R (C z7y))= _
      rw [hS]
      simp [yq,markCoeff]
    · exact hbt
    · exact hvt
end
end qnCt0Qc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qnCt0Qc
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX jz)
open P5_7_7 (Dg phys seedDerivative)
open qGnV2ac (Sections coeff_seedDerivative)
open qrKC9pb (Input physicalDerivative)
open private fiber_map from ProximityPrize.SubmissionLower.Z6Jqnnb
open private fiber regular_fiber from ProximityPrize.SubmissionLower.ZWvyx4b
open private derivative_reverse coeff_X_derivative from ProximityPrize.SubmissionLower.Z0zgXCc
open private extend_seed_deriv from ProximityPrize.SubmissionLower.ZdnOpje
open scoped WithZero
private theorem reverse_calc (f n:FX[X]) (y :FX) (hy :y≠0)
    (hd:0<f.natDegree) (hn:n.natDegree≤f.natDegree)
    (hr :f.eval y=0) (hs :f.derivative.eval y≠0) :
    f.reverse.eval y⁻¹=0∧f.reverse.derivative.eval y⁻¹≠0 ∧
      -(n.reflect f.natDegree).eval y⁻¹/f.reverse.derivative.eval y⁻¹ =
        -(y⁻¹)^2*(-n.eval y/f.derivative.eval y) := by
  let:=invertibleOfNonzero hy
  let d:=f.natDegree
  let G:=C (d:FX)*f-Polynomial.X*f.derivative
  have hG:G.natDegree≤d-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    change (C (d:FX)*f-Polynomial.X*f.derivative).coeff i=0
    rw [coeff_sub,coeff_C_mul,coeff_X_derivative]
    rcases lt_or_eq_of_le (show d≤ i by omega) with hi' | rfl
    · rw [coeff_eq_zero_of_natDegree_lt hi',mul_zero,zero_mul,sub_self]
    · rw [mul_comm,sub_self]
  have hrev :f.reverse.eval y⁻¹=0:= by
    simpa only [invOf_eq_inv,eval₂_id] using
      (eval₂_reverse_eq_zero_iff (zz5 FX) y f).mpr (by simpa only [eval₂_id] using hr)
  have hD:f.reverse.derivative.eval y⁻¹*y^(d-1) = -(y*f.derivative.eval y) := by
    rw [derivative_reverse f hd]
    have h:=eval₂_reflect_mul_pow (zz5 FX) y (d-1) G hG
    simpa only [invOf_eq_inv,eval₂_id,G,eval_sub,eval_mul,eval_C,eval_X,
      hr,mul_zero,zero_sub] using h
  have hN : (n.reflect d).eval y⁻¹*y^d=n.eval y := by
    simpa only [invOf_eq_inv,eval₂_id] using eval₂_reflect_mul_pow (zz5 FX) y d n hn
  have hdy :f.reverse.derivative.eval y⁻¹*y^d = -(y^2*f.derivative.eval y) := calc
    _=(f.reverse.derivative.eval y⁻¹*y^(d-1))*y := by
      rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hd]
    _ = _:= by rw [hD]; ring
  refine ⟨hrev,?_,?_⟩
  · intro h
    rw [h,zero_mul,eq_comm,neg_eq_zero] at hD
    exact mul_ne_zero hy hs hD
  · rw [← mul_div_mul_right _ _ (pow_ne_zero d hy),neg_mul,hN,hdy]
    field_simp
theorem atMark_reverse (J:Input) (S:Sections J.F) (γ:K) (hγ:γ∈S.CF)
    (y :FX) (hy :y≠0) (hr :yq (S.seed γ) y J.F=0)
    (hs :yq (S.seed γ) y J.F.derivative≠0) :
    let z :=S.seed γ
    yq z y⁻¹ J.F.reverse=0∧yq z y⁻¹ J.F.reverse.derivative≠0 ∧
      -(yq z y⁻¹ (seedDerivative J.F.reverse))/yq z y⁻¹ J.F.reverse.derivative =
        -(y⁻¹)^2*(-(yq z y (seedDerivative J.F))/yq z y J.F.derivative) := by
  let z :=S.seed γ
  let f :=fiber J.F z
  let n:=fiber (seedDerivative J.F) z
  have he (G:Dg) (a :FX) :yq z a G=(fiber G z).eval a := by
    rw [yq,coe_eval₂RingHom,fiber_map,← eval₂_eq_eval_map]
    rfl
  obtain ⟨hd,_⟩:=(regular_fiber J.Ca.jU J.Ca.two_le J.Ca.tame z).mp
    (S.regular_ordinate γ hγ)
  have hd' : f.natDegree=J.l:=hd
  have href :fiber J.F.reverse z=f.reverse := by
    change fiber J.F.reverse z=f.reflect f.natDegree
    rw [hd',fiber_map,reverse,J.Ca.jU,← reflect_map,← fiber_map]
  have hder (G:Dg) :fiber G.derivative z=(fiber G z).derivative := by
    rw [fiber_map,fiber_map,derivative_map]
  have hn:n.natDegree≤f.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [show n=fiber (seedDerivative J.F) z from rfl,fiber_map,coeff_map,
      coeff_seedDerivative,coeff_eq_zero_of_natDegree_lt (J.Ca.jU ▸ hd ▸ hi),
      derivative_zero,map_zero]
  have hnr :fiber (seedDerivative J.F.reverse) z=n.reflect f.natDegree := by
    ext i
    simp only [fiber_map,n,coeff_reflect,coeff_map,coeff_seedDerivative,coeff_reverse,
      hd',J.Ca.jU]
  change yq z y⁻¹ J.F.reverse=0∧yq z y⁻¹ J.F.reverse.derivative≠0 ∧
    -(yq z y⁻¹ (seedDerivative J.F.reverse))/yq z y⁻¹ J.F.reverse.derivative =
      -(y⁻¹)^2*(-(yq z y (seedDerivative J.F))/yq z y J.F.derivative)
  simp only [he,hder,href,hnr]
  change yq z y J.F=0 at hr
  change yq z y J.F.derivative≠0 at hs
  simp only [he,hder] at hr hs
  have hpos :0<f.natDegree := by rw [hd']; have :=J.Ca.two_le; omega
  exact reverse_calc f n y hy hpos hn hr hs
private theorem jet_chain {R A T:Type} [CommSemiring R] [CommSemiring A] [CommSemiring T]
  [Algebra R T] (D:Derivation R T T) (i:A →+* T) (x :T) (f :A[X]) :
  D (f.eval₂ i x)=(f.sum fun n a=>D (i a)*x^n)+f.derivative.eval₂ i x*D x := by
 rw [eval₂_eq_sum,derivative_apply,eval₂_sum]
 simp only [sum_def,map_sum,Finset.sum_mul]
 rw [← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro n _
 simp only [D.leibniz,D.leibniz_pow,smul_eq_mul,nsmul_eq_mul,eval₂_mul,
  eval₂_C,eval₂_pow,eval₂_X,eval₂_natCast,map_mul,map_natCast]
 ring
theorem ident_jet (z :K) (P Q:L[X]) (G:Dg)
    (hr :yq z (phys P/phys Q) G=0)
    (hs :yq z (phys P/phys Q) G.derivative≠0) :
    -(yq z (phys P/phys Q) (physicalDerivative G)) /
        yq z (phys P/phys Q) G.derivative =
      phys (P.derivative*Q-P*Q.derivative)/phys (Q^2) := by
  obtain ⟨D,h⟩:=extend_seed_deriv
  have hD (q:L[X]) :D (phys q)=phys q.derivative :=h q
  have hz :D (jz z)=0:= by
    change D (phys (C (algebraMap K L z)))=0
    rw [hD,derivative_C,map_zero]
  have hcoeff (q:L[X][X]) :markCoeff z q=q.eval₂ phys (jz z) := by
    rw [markCoeff,zQb,coe_evalRingHom,coe_mapRingHom,eval_map]
  have he (q:L[X][X]) :D (markCoeff z q) =
      markCoeff z (q.sum fun i b=>monomial i b.derivative) := by
    rw [hcoeff,hcoeff,jet_chain,hz,mul_zero,add_zero,eval₂_sum]
    simp only [sum_def,eval₂_monomial,hD]
  let y :=phys P/phys Q
  have h:=jet_chain D (markCoeff z) y G
  change D (yq z y G)=G.sum _+yq z y G.derivative*D y at h
  rw [hr,map_zero] at h
  have he' : yq z y (physicalDerivative G)=G.sum (fun i b=>D (markCoeff z b)*y^i) := by
    simp only [yq,coe_eval₂RingHom,physicalDerivative,eval₂_sum,eval₂_monomial,he]
  rw [← he'] at h
  apply (div_eq_iff hs).2
  rw [← neg_eq_of_add_eq_zero_left h.symm]
  have hp:D y=phys (P.derivative*Q-P*Q.derivative)/phys (Q^2) := by
    change D (phys P/phys Q)= _
    rw [D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,hD,hD,map_pow,map_sub,
      map_mul,map_mul,div_eq_mul_inv,inv_pow,mul_comm (phys Q)]
    ring
  rw [← hp,neg_neg,mul_comm]
end
end qnCt0Qc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qz2teNe
noncomputable section
open Polynomial
open cu (FX)
open P5_7_7 (phys)
open q2TwyLa (i5)
open qoGY3we
open scoped nonZeroDivisors
open private evalInv from ProximityPrize.SubmissionLower.ZSm5aLa
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
abbrev tu:=i5[X]
abbrev kB:=FractionRing tu
abbrev Target :=LaurentSeries FX
abbrev seriesIn:Series →+* Target :=algebraMap _ _
private theorem evalInv_injective :zq4 evalInv := by
 apply (injective_iff_map_eq_zero _).mpr
 intro q hq
 let u:FX:=(phys (z7y: (cu.L)[X]))⁻¹
 have hx :phys (z7y: (cu.L)[X])≠0 :=
   (map_ne_zero_iff _ (zxb _ _)).2 z05
 let:Invertible u:=invertibleOfNonzero (inv_ne_zero hx)
 have h:=(eval₂_reverse_eq_zero_iff (algebraMap cu.L FX) u q).mpr hq
 rw [invOf_eq_inv,show u⁻¹=phys (z7y: (cu.L)[X]) by simp [u]] at h
 have he :eval₂RingHom (algebraMap cu.L FX) (phys z7y)=phys := by
   apply Polynomial.ringHom_ext
   · intro a
     rw [coe_eval₂RingHom,eval₂_C]
     exact IsScalarTower.algebraMap_apply cu.L (cu.L)[X] FX a
   · exact eval₂_X _ _
 change eval₂RingHom (algebraMap cu.L FX) (phys z7y) q.reverse=0 at h
 rw [he] at h
 exact reverse_eq_zero.mp ((injective_iff_map_eq_zero _).mp (zxb _ _) _ h)
private theorem bcr (q:tu) (n:ℕ) :
   z2o n (bY true q) =
     evalInv (q.sum fun i a=>monomial i (z2o n a)) := by
 induction q using Polynomial.induction_on' with
 | add a b ha hb =>
   rw [map_add,map_add,ha,hb,sum_add_index,map_add]
   · simp
   · intro i a b
     rw [map_add,map_add]
 | monomial i a =>
   rw [sum_monomial_index _ _ (by simp)]
   simp only [bY,evalInv,↓reduceIte,coe_eval₂RingHom,eval₂_monomial,
     ← map_pow PowerSeries.C,PowerSeries.coeff_mul_C,PowerSeries.coeff_map]
theorem cFm:zq4 (bY true) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro q hq
 apply Polynomial.ext
 intro i
 rw [coeff_zero]
 apply PowerSeries.ext
 intro n
 have h:=bcr q n
 rw [hq,map_zero] at h
 have hz :=evalInv_injective (h.symm.trans (map_zero evalInv).symm)
 simpa only [sum_coeff _ (map_zero _),coeff_zero,map_zero] using
  congrArg (fun q: (cu.L)[X]=>q.coeff i) hz
def embedding:kB →+* Target :=
  IsFractionRing.lift (g:=seriesIn.comp (bY true))
    (HahnSeries.ofPowerSeries_injective.comp cFm)
theorem embedding_on (q:tu) :
  embedding (algebraMap tu kB q)=seriesIn (bY true q) :=
 IsFractionRing.lift_algebraMap _ _
def zeroIdeal:Ideal tu:=Ideal.span ({z7y} : Set tu)
instance :zeroIdeal.IsPrime :=
 (Ideal.span_singleton_prime z05).mpr zEx
abbrev inFrac (M:Submonoid tu) (h:M≤tu⁰) :zTg tu kB :=
 Localization.subalgebra.ofField kB M h
theorem rad_ne (A:Cover) :A.g.reverse≠0 :=
 fun h=>A.radical_unit.ne_zero (leadingCoeff_eq_zero.mpr (reverse_eq_zero.mp h))
abbrev offZero (A:Cover) :zTg tu kB :=
 inFrac (zSL (z7y*A.g.reverse))
  (powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero z05 (rad_ne A)))
abbrev afe :zTg tu kB :=
 inFrac zeroIdeal.primeCompl zeroIdeal.primeCompl_le_nonZeroDivisors
abbrev chartSubring (A:Cover) :zTg tu kB :=
 inFrac (zSL A.g.reverse) (powers_le_nonZeroDivisors_of_noZeroDivisors (rad_ne A))
end
end qz2teNe
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qz2teNe
noncomputable section
open Polynomial
open qoGY3we
open scoped nonZeroDivisors
private theorem bWc {s a b:tu} (hs :Prime s) (hb : ¬ s∣b)
   (n:ℕ) (h:s^n∣a*b) :s^n∣a := by
 induction n generalizing a with
 | zero=>simp
 | succ n ih =>
   have ha :=(hs.dvd_mul.mp ((dvd_pow_self s (Nat.succ_ne_zero _)).trans h)).resolve_right hb
   obtain ⟨c,rfl⟩:=ha
   rw [pow_succ'] at h ⊢
   obtain ⟨u,hu⟩:=h
   have hd:s^n∣c*b :=
     ⟨u,mul_left_cancel₀ hs.ne_zero (by simpa only [mul_assoc] using hu)⟩
   obtain ⟨w,hw⟩:=ih hd
   exact ⟨w,by rw [hw,mul_assoc]⟩
private theorem chart_inter (A:Cover) {z :kB} (ho:z∈offZero A)
  (ht:z∈afe) :z∈chartSubring A:= by
 let f :=algebraMap tu kB
 have hf :=zxb tu kB
 obtain ⟨a,_,⟨n,rfl⟩,ha⟩:=ho
 obtain ⟨c,b,hb,hc⟩:=ht
 have hb' : ¬ z7y∣b:= fun h=>hb (Ideal.mem_span_singleton.mpr h)
 have hbn:b≠0:=nonZeroDivisors.ne_zero (zeroIdeal.primeCompl_le_nonZeroDivisors hb)
 have hn: (z7y*A.g.reverse)^n≠0 :=
  pow_ne_zero _ (mul_ne_zero z05 (rad_ne A))
 have he :a*b=c*(z7y*A.g.reverse)^n:= by
  apply hf
  rw [map_mul,map_mul]
  apply (div_eq_div_iff ((map_ne_zero_iff f hf).mpr hn) ((map_ne_zero_iff f hf).mpr hbn)).mp
  rw [div_eq_mul_inv,div_eq_mul_inv]
  exact ha.symm.trans hc
 have hp:z7y^n∣a*b:= by
  refine ⟨A.g.reverse^n*c,?_⟩
  rw [he,mul_pow]
  ac_rfl
 obtain ⟨w,hw⟩:=bWc zEx hb' n hp
 refine ⟨w,A.g.reverse^n,⟨n,rfl⟩,?_⟩
 rw [ha,← div_eq_mul_inv,← div_eq_mul_inv,hw]
 change f (z7y^n*w)/f ((z7y*A.g.reverse)^n)=f w/f (A.g.reverse^n)
 rw [mul_pow,map_mul,map_mul]
 exact mul_div_mul_left _ _ ((map_ne_zero_iff f hf).mpr (pow_ne_zero n z05))
private theorem closed_loc (M:Submonoid tu) (h:M≤tu⁰) :
  IsIntegrallyClosed (inFrac M h) := by
 let:IsIntegrallyClosed tu:=UniqueFactorizationMonoid.instIsIntegrallyClosed
 exact isIntegrallyClosed_of_isLocalization (inFrac M h) M h
private theorem minpoly_coeff {R E :Type} [CommRing R] [IsDomain R] [Field E]
  [Algebra R kB] [IsFractionRing R kB] [IsIntegrallyClosed R] [Algebra kB E]
  {z :E} (h: ((algebraMap kB E).comp (algebraMap R kB)).IsIntegralElem z) (i:ℕ) :
  (minpoly kB z).coeff i∈Set.range (algebraMap R kB) := by
 have hz :IsIntegral kB z :=h.of_comp
 obtain ⟨q,hq,he⟩:=h
 have hd:minpoly kB z∣q.map (algebraMap R kB) := by
  apply minpoly.dvd
  change eval₂ (algebraMap kB E) z _=0
  rwa [eval₂_map]
 obtain ⟨f,hf⟩:=IsIntegrallyClosed.eq_map_mul_C_of_dvd kB hq hd
 rw [(minpoly.monic hz).leadingCoeff,C_1,mul_one] at hf
 exact ⟨f.coeff i,by rw [← coeff_map,hf]⟩
theorem glue (A:Cover) {z :Series}
   (ho: (embedding.comp (offZero A).val.toRingHom).IsIntegralElem (seriesIn z))
   (ht: (embedding.comp afe.val.toRingHom).IsIntegralElem (seriesIn z))
   (j:Away A →+* Series) (hj:j.comp (algebraMap tu (Away A))=bY true) :
   j.IsIntegralElem z := by
 let:Algebra kB Target :=embedding.toAlgebra
 let:IsIntegrallyClosed (offZero A) :=closed_loc _ _
 let:IsIntegrallyClosed afe :=closed_loc _ _
 let q:=minpoly kB (seriesIn z)
 have hq:q.Monic:=minpoly.monic (RingHom.IsIntegralElem.of_comp ho:IsIntegral kB (seriesIn z))
 have hcoeff : (↑q.coeffs :Set kB)⊆(chartSubring A).toSubring := by
   intro a ha
   obtain ⟨i,_,rfl⟩:=mem_coeffs_iff.mp ha
   obtain ⟨u,hu⟩:=minpoly_coeff (R:=offZero A) ho i
   obtain ⟨v,hv⟩:=minpoly_coeff (R:=afe) ht i
   exact chart_inter A (hu ▸ u.property) (hv ▸ v.property)
 let D:=chartSubring A
 have h: (embedding.comp D.val.toRingHom).IsIntegralElem (seriesIn z) := by
   refine ⟨q.toSubring D.toSubring hcoeff,(monic_toSubring _ _ _).mpr hq,?_⟩
   change eval₂ (embedding.comp D.toSubring.subtype) (seriesIn z) _=0
   rw [← eval₂_map,map_toSubring]
   exact minpoly.aeval kB (seriesIn z)
 let e :=IsLocalization.algEquiv (zSL A.g.reverse) (Away A) D
 have he : (embedding.comp D.val.toRingHom).comp e.toRingEquiv.toRingHom=seriesIn.comp j:= by
   apply IsLocalization.ringHom_ext (zSL A.g.reverse)
   apply zz4
   intro x
   change embedding (D.val (e (algebraMap tu (Away A) x))) =
     seriesIn (j (algebraMap tu (Away A) x))
   rw [e.commutes]
   exact (embedding_on x).trans (congrArg seriesIn (RingHom.congr_fun hj x).symm)
 have he' : (seriesIn.comp j).comp e.symm.toRingEquiv.toRingHom=embedding.comp D.val.toRingHom:= by
   rw [← he]
   apply zz4
   intro x
   change embedding (D.val (e (e.symm x)))=embedding (D.val x)
   rw [e.apply_symm_apply]
 apply RingHom.IsIntegralElem.of_map (g:=seriesIn) HahnSeries.ofPowerSeries_injective
 exact RingHom.IsIntegralElem.of_comp (he'.symm ▸ h)
end
end qz2teNe
end
section
namespace qz2teNe
noncomputable section
open Polynomial
open cu (L)
open qoGY3we
def c1 :Prop :=
  ∀ (A:Cover) (P:L[X]) (J:LocalRoot A.f A.r P),
    (embedding.comp (offZero A).val.toRingHom).IsIntegralElem (seriesIn J.logSeed)
def c2 :Prop :=
  TameLog → ∀ (A:Cover) (P:L[X]) (J:LocalRoot A.f A.r P),
    (embedding.comp afe.val.toRingHom).IsIntegralElem (seriesIn J.logSeed)
theorem of_children (h1 :c1) (h2 :c2) :qoGY3we.c3 :=
 fun tame A P J j hj=>glue A (h1 A P J) (h2 tame A P J) j hj
end
end qz2teNe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qnCt0Qc
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open P5_7_7 (phys seedDerivative)
open qGnV2ac (Sections zD)
open qrKC9pb (Input chartEq physicalDerivative)
open qyUzJvd
open qqi5QRb (pointPrime pointVal)
private theorem phys_ne {V:L[X]} (hV:V≠0) :phys V≠0 :=
 (map_ne_zero_iff phys (zxb L[X] FX)).mpr hV
private theorem unit_at (x :L) (V:L[X]) (hV:V.eval x≠0) :
  pointVal x (phys V)=1 := by
 change (pointPrime x).valuation FX (algebraMap L[X] FX V)=1
 rw [(pointPrime x).valuation_eq_one_iff_notMem,show (pointPrime x).asIdeal =
  Ideal.span {z7y - C x} from rfl,Ideal.mem_span_singleton,dvd_iff_isRoot,
  IsRoot.def]
 exact hV
private theorem make_chart (J:Input) (S:Sections J.F) (γ:K) (hγ:γ∈S.CF)
    (x :L) (r :Bool) (U V:L[X]) (hV:V.eval x≠0)
    (hy :r=true→phys (S.P γ)/phys (S.Q γ)≠0)
    (he : (if r then (phys (S.P γ)/phys (S.Q γ))⁻¹ else phys (S.P γ)/phys (S.Q γ)) =
      phys U/phys V)
    (hr :yq (S.seed γ) (phys U/phys V) (chartEq J r)=0)
    (hs :yq (S.seed γ) (phys U/phys V) (chartEq J r).derivative≠0)
    (hw : ∃ u:FX,pointVal x u=1 ∧
      -(yq (S.seed γ) (phys U/phys V) (seedDerivative (chartEq J r))) /
        yq (S.seed γ) (phys U/phys V) (chartEq J r).derivative =
          u*(phys (S.A γ)/phys (S.B γ))) :
    Nonempty (MarkChart J S γ x r) := by
  have hroot :yq (S.seed γ) (phys (S.P γ)/phys (S.Q γ)) J.F=0 :=
    (atMark_pair _ _ _ _).trans (S.root γ hγ)
  obtain ⟨φ,hφ,hc⟩:=dIG J r (S.seed γ) _ hroot hy (he.symm ▸ hs)
  simp only [he] at hφ hc
  have pol (q:L[X]) :pointVal x (phys q)≤1 :=
    (pointPrime x).valuation_le_one (K:=FX) q
  have quotient (n:ℕ) (q:L[X]) :pointVal x (phys q/phys (V^n))≤1 := by
    rw [phys.map_pow,map_div₀,map_pow,unit_at x V hV,one_pow,div_one]
    exact pol _
  have hj:=ident_jet (S.seed γ) U V (chartEq J r) hr hs
  have hreg (i:Fin 4) :pointVal x (φ (coord J r i))≤1 := by
    rw [hc]
    fin_cases i
    · exact pol _
    · exact pol (C (algebraMap K L (S.seed γ)))
    · change pointVal x (phys U/phys V)≤1
      simpa only [pow_one] using quotient 1 U
    · change pointVal x (-(yq (S.seed γ) (phys U/phys V)
        (physicalDerivative (chartEq J r)))/_)≤1
      rw [hj]
      exact quotient 2 _
  refine ⟨{ map :=φ,physical_eq :=hc 0,seed_eq :=hc 1,regular := ?_,
            simple := ?_,gK6 := ?_ }⟩
  · rintro ⟨a,ha⟩
    induction ha using z90 with
    | mem a ha =>
      obtain ⟨i,rfl⟩:=ha
      exact hreg i
    | algebraMap c =>
      change pointVal x (φ (algebraMap L (Chart J r) c))≤1
      rw [AlgHom.commutes]
      exact pol (C c)
    | add a b ha₀ hb₀ ha hb =>
      change pointVal x (φ ((⟨a,ha₀⟩:Chart J r) + ⟨b,hb₀⟩))≤1
      rw [map_add]
      exact ((pointVal x).map_add _ _).trans (max_le ha hb)
    | mul a b ha₀ hb₀ ha hb =>
      change pointVal x (φ ((⟨a,ha₀⟩:Chart J r)*⟨b,hb₀⟩))≤1
      rw [map_mul φ,map_mul]
      exact mul_le_one' ha hb
  · rw [sep,hφ]
    exact hs
  · simpa only [num,sep,map_neg,hφ] using hw
theorem proof :qyUzJvd.c1 := by
  intro J S γ hγ x
  let P:=S.P γ
  let Q:=S.Q γ
  let z :=S.seed γ
  let a :=phys P/phys Q
  let d:=yq z a J.F.derivative
  let n:=yq z a (seedDerivative J.F)
  have hQ:phys Q≠0:=phys_ne (S.denominator γ hγ)
  have hr :yq z a J.F=0:=(atMark_pair _ _ _ _).trans (S.root γ hγ)
  have hd:d≠0:= by simpa only [d,a,atMark_pair] using S.simple γ hγ
  have hform :phys (S.A γ)/phys (S.B γ)=(-n/d)*(phys Q)^2 := by
    simpa only [zD,a,d,n,atMark_pair,neg_div] using S.formula γ hγ
  by_cases hq:Q.eval x=0
  · have hp:P.eval x≠0:= by
      intro h
      obtain ⟨b,c,e⟩:=S.coprime γ hγ
      have ev :=congrArg (evalRingHom x) e
      change (evalRingHom x) (b*P+c*Q)=(evalRingHom x) 1 at ev
      simp only [map_add,map_mul,coe_evalRingHom,h,hq,mul_zero,add_zero,eval_one,
        zero_ne_one] at ev
    have hP:phys P≠0:=phys_ne (fun h=>hp (by rw [h,eval_zero]))
    have ha :a≠0:=div_ne_zero hP hQ
    obtain ⟨hr',hs',hv⟩:=atMark_reverse J S γ hγ a ha hr hd
    have he :a⁻¹=phys Q/phys P:=inv_div _ _
    refine ⟨true,make_chart J S γ hγ x true Q P hp (fun _=>ha) he
      (he ▸ hr') (he ▸ hs') ?_⟩
    refine ⟨-((phys P)⁻¹)^2,?_,?_⟩
    · rw [Valuation.map_neg,map_pow,map_inv₀,unit_at x P hp,inv_one,one_pow]
    · have hv' : -(yq z (phys Q/phys P) (seedDerivative J.F.reverse)) /
          yq z (phys Q/phys P) J.F.reverse.derivative =
            -(phys Q/phys P)^2*(-n/d) :=he ▸ hv
      change -(yq z (phys Q/phys P) (seedDerivative J.F.reverse)) /
        yq z (phys Q/phys P) J.F.reverse.derivative= _
      rw [hv',hform]
      field_simp [hP,hQ,hd]
  · refine ⟨false,make_chart J S γ hγ x false P Q hq
      (fun h=>Bool.noConfusion h) rfl hr hd ?_⟩
    refine ⟨((phys Q)⁻¹)^2,?_,?_⟩
    · rw [map_pow,map_inv₀,unit_at x Q hq,inv_one,one_pow]
    · change -n/d=((phys Q)⁻¹)^2*_
      rw [hform]
      field_simp [hQ,hd]
end
end qnCt0Qc
end
