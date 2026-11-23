import ProximityPrize.SubmissionLower.ZBcmVie
import ProximityPrize.SubmissionLower.ZuJZkxc
import ProximityPrize.SubmissionLower.ZvttkHa
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZFqQTue
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZvbAI4c
import ProximityPrize.SubmissionLower.ZX8w26c
set_option Elab.async false
open _root_ renaming Algebra.IsSeparable → zw7, CommRing → za6, Finset.sup_le → zf9, Function.Injective → zq4, Function.Surjective → zpX, Int.toNat_le_toNat → z0Z, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, MvPolynomial → z3y, MvPolynomial.X → z9v, Nat.eq_zero_of_le_zero → za7, Nat.mul_le_mul_right → ztf, Polynomial.C → z1z, Polynomial.map_injective → zTo
section
section
namespace qqI700a
def c1 :Prop :=qdpQ3Rb.c1
def c2 :Prop :=qdpQ3Rb.c2
def c3:Prop :=P5_7_1_7_4_3_4.c3
theorem of_children (qW:c1) (fibres :c2) (norm:c3) :qSHe4ub.c4 :=
  qdpQ3Rb.of_children qW fibres norm
end qqI700a
end
end
section
section
set_option autoImplicit true
namespace qoyAGrd
theorem proof :qLXroAb.c2 :=qU4m8Td.proof
end qoyAGrd
end
section
namespace q9uVqha
noncomputable section
open Polynomial qLXroAb
open cu (L FX)
open P5 (K)
open P5_7_7 (phys)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open q1kuFjb (IntSeries residue integralSeries fWQ)
open scoped WithZero
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
structure Generic (F:Sheet Cq z S) where
 M:Type
 [field :Field M]
 [aO8:Algebra Cq.E M]
 x :M
 y :M
 independent:Transcendental Cq.E x
 kernel : ∀ g:Cq.E[X][X],evalXY g x y=0↔F.f∣g
 generates :IntermediateField.adjoin Cq.E ({x,y} : Set M) = ⊤
 polar_ne :evalXY F.f.derivative x y≠0
 y_ne :y≠0
 finite :Module.Finite (IntermediateField.adjoin Cq.E ({x} : Set M)) M
 separable :zw7 (IntermediateField.adjoin Cq.E ({x} : Set M)) M
 deriv :Derivation Cq.E M M
 deriv_x :deriv x=1
attribute [instance] Generic.field Generic.aO8
variable {F:Sheet Cq z S}
abbrev Generic.point (G:Generic F) :Fin 4→G.M:=coords F.f G.x G.y
def Generic.sW (G:Generic F) (i:Fin 4) :G.M :=
 G.point i/evalXY F.f.derivative G.x G.y
abbrev Generic.constants (G:Generic F) :L →+* G.M :=
 (algebraMap Cq.E G.M).comp (algebraMap L Cq.E)
abbrev Generic.form (G:Generic F) (a :Fin 4→L) :G.M :=
 linear G.constants a G.point
structure MarkReduction (G:Generic F) (γ:K) (hγ:γ∈F.marks) where
 O:Subring G.M
 red:O →+* FX
 unit : ∀ a :O,red a≠0→ IsUnit a
 seed :seedRing F γ →+* O
 seed_val : ∀ c,(seed c:G.M)=algebraMap Cq.E G.M (c:Cq.E)
 seed_red : ∀ c,red (seed c)=phys (C ((F.atPlace γ hγ (c:Cq.E)).coeff 0))
 coord:Fin 4→O
 coord_val : ∀ i,(coord i:G.M)=G.sW i
 coord_red : ∀ i,red (coord i)=phys (markJet S γ i)
def seedResidue (F:Sheet Cq z S) (γ:K) (hγ:γ∈F.marks) :seedRing F γ →+* L :=
  residue.comp (((F.atPlace γ hγ).toRingHom.comp (seedRing F γ).subtype).codRestrict
    IntSeries fun c=>(integralSeries _ (by
     change (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (F.atPlace γ hγ (c:Cq.E))≤1
     rw [← F.value γ hγ]
     exact c.property)).property)
@[simp] theorem seedResidue_apply (γ:K) (hγ:γ∈F.marks) (c:seedRing F γ) :
   seedResidue F γ hγ c=(F.atPlace γ hγ (c:Cq.E)).coeff 0 :=
  fWQ _
def zp {R M:Type} [za6 R] [Field M]
    (j:R →+* M) (v :Fin 4→M) :z3y (Fin 4) R →+* M[X] :=
  MvPolynomial.eval₂Hom (C.comp j) (fun i=>C (v i)*Polynomial.X)
@[simp] theorem graphMap_X {R M:Type} [za6 R] [Field M]
   (j:R →+* M) (v :Fin 4→M) (i:Fin 4) :
   zp j v (z9v i)=C (v i)*Polynomial.X :=
  MvPolynomial.eval₂Hom_X' _ _ _
def TY {R M:Type} [za6 R] [Field M] (j:R →+* M)
    (r :R →+* L) (v :Fin 4→M) :Ideal (z3y (Fin 4) L) :=
  Ideal.map (MvPolynomial.map r) (RingHom.ker (zp j v))
abbrev Generic.RS (G:Generic F) (γ:K) (hγ:γ∈F.marks) :=
 TY ((algebraMap Cq.E G.M).comp (seedRing F γ).subtype)
  (seedResidue F γ hγ) G.point
def P5 (a :Fin 4→L) :z3y (Fin 4) L :=
 ∑ i,MvPolynomial.C (a i)*z9v i
def GraphCut (I:Ideal (z3y (Fin 4) L)) (a b:Fin 4→L) :Prop :=
 ∀ i:Fin 4,z9v i∈(I+Ideal.span {P5 a,P5 b}).radical
structure Projection (G:Generic F) (u:G.M) where
 [base :Algebra (tu Cq.E) G.M]
 [tower :IsScalarTower Cq.E (tu Cq.E) G.M]
 [finite :Module.Finite (tu Cq.E) G.M]
 separable :zw7 (tu Cq.E) G.M
 parameter :algebraMap (tu Cq.E) G.M
   (algebraMap Cq.E[X] (tu Cq.E) Polynomial.X)=u
end
end q9uVqha
end
section
namespace qXARP7c
noncomputable section
open Polynomial Finset WithZero
open scoped WithZero nonZeroDivisors
open P5 (K)
open cu (L)
open E7 (CurvePlace KB)
open qb0hmCe (CurveModel)
open qFD8jve (aFA)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb
open private adG cTA b4t efd efc aMX from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E]
abbrev gauss (v :Valuation E ℤᵐ⁰) (P:E[X]) :ℤᵐ⁰:=adG v P
theorem dMr (v :Valuation E ℤᵐ⁰) (P:E[X]) (i:ℕ) :
 v (P.coeff i)≤gauss v P:=aMX v P i
theorem gauss_ne (v :Valuation E ℤᵐ⁰) {P:E[X]} (h:P≠0) :
 gauss v P≠0:=b4t v h
def baseVal (v :Valuation E ℤᵐ⁰) :Valuation (tu E) ℤᵐ⁰ :=
  (efc v).extendToLocalization (S:=E[X]⁰)
    (fun _ h=>gauss_ne v (nonZeroDivisors.ne_zero h)) (tu E)
theorem base_poly (v :Valuation E ℤᵐ⁰) (P:E[X]) :
  baseVal v (algebraMap E[X] (tu E) P)=gauss v P :=
 Valuation.extendToLocalization_apply_map_apply _ _ _ _
theorem base_const (v :Valuation E ℤᵐ⁰) (a :E) :
  baseVal v (algebraMap E (tu E) a)=v a := by
 rw [zG3 E E[X] (tu E),base_poly]
 exact cTA v a
theorem base_surj (v :Valuation E ℤᵐ⁰) (hv :zpX v) :
  zpX (baseVal v) :=
 fun g=> let ⟨a,ha⟩:=hv g; ⟨algebraMap E (tu E) a,(base_const v a).trans ha⟩
def j3 (v :Valuation E ℤᵐ⁰) (P:E[X]) :ℕ :=
 (log (gauss v P)-log (v P.trailingCoeff)).toNat
private theorem debit_nonneg (v :Valuation E ℤᵐ⁰) {P:E[X]} (hP:P≠0) :
  0≤log (gauss v P)-log (v P.trailingCoeff) := by
 apply sub_nonneg.mpr
 exact (log_le_log (v.ne_zero_iff.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hP))
  (gauss_ne v hP)).2 (dMr v P P.natTrailingDegree)
private theorem debit_mul (v :Valuation E ℤᵐ⁰) {P Q:E[X]} (hP:P≠0) (hQ:Q≠0) :
   j3 v (P*Q)=j3 v P+j3 v Q:= by
 have ht {H :E[X]} (hH :H≠0) :v H.trailingCoeff≠0 :=
   v.ne_zero_iff.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hH)
 change (log (adG v (P*Q))-log (v (P*Q).trailingCoeff)).toNat= _
 rw [efd,trailingCoeff_mul,map_mul,
   log_mul (gauss_ne v hP) (gauss_ne v hQ),log_mul (ht hP) (ht hQ)]
 rw [show log (gauss v P)+log (gauss v Q) -
     (log (v P.trailingCoeff)+log (v Q.trailingCoeff)) =
     (log (gauss v P)-log (v P.trailingCoeff)) +
     (log (gauss v Q)-log (v Q.trailingCoeff)) by ring,
   Int.toNat_add (debit_nonneg v hP) (debit_nonneg v hQ)]
 rfl
theorem debit_le_trailing (v :Valuation E ℤᵐ⁰) {P Q:E[X]} {k :ℕ}
    (hP:P≠0) (hQ:Q≠0) (hQint : ∀ i,v (Q.coeff i)≤1) (hd:P^k∣Q) :
    k*j3 v P≤KB v Q.trailingCoeff := by
  have hpow (n:ℕ) :j3 v (P^n)=n*j3 v P:= by
    induction n with
    | zero =>
      simp only [pow_zero,Nat.zero_mul,j3,show (1 :E[X])=C 1 by simp,
        cTA,trailingCoeff_eq_coeff_zero (by simp : (C (1 :E)).coeff 0≠0),
        coeff_C_zero,sub_self,Int.toNat_zero]
    | succ n ih=>rw [pow_succ,debit_mul v (pow_ne_zero _ hP) hP,ih,Nat.succ_mul]
  have hQlog:log (gauss v Q)≤0:= by
    rw [← log_one]
    exact (log_le_log (gauss_ne v hQ) one_ne_zero).2 (zf9 fun i _=>hQint i)
  obtain ⟨H,rfl⟩:=hd
  have hH :H≠0:=right_ne_zero_of_mul hQ
  calc
    k*j3 v P≤k*j3 v P+j3 v H :=Nat.le_add_right _ _
    _=j3 v (P^k*H) := by rw [debit_mul v (pow_ne_zero _ hP) hH,hpow]
    _≤_:=z0Z (by omega)
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
theorem base_eval (A:Pencil F) (P:Cq.E[X]) :
   algebraMap (tu Cq.E) A.M (algebraMap Cq.E[X] (tu Cq.E) P) =
     P.eval₂ (algebraMap Cq.E A.M) A.u:= by
 refine RingHom.congr_fun (Polynomial.ringHom_ext (f :=(algebraMap (tu Cq.E) A.M).comp
   (algebraMap Cq.E[X] (tu Cq.E))) (g:=eval₂RingHom (algebraMap Cq.E A.M) A.u) ?_ ?_) P
 · intro a
   change algebraMap (tu Cq.E) A.M (algebraMap Cq.E[X] (tu Cq.E) (C a)) =
     (C a).eval₂ (algebraMap Cq.E A.M) A.u
   rw [eval₂_C,zG3 Cq.E (tu Cq.E) A.M,
     zG3 Cq.E Cq.E[X] (tu Cq.E)]
   rfl
 · simp [Pencil.u]
theorem vertical_base (A:Pencil F) (w:CurvePlace L Cq.E) (t:Vertical A w)
    (a :tu Cq.E) :
    t.value (algebraMap (tu Cq.E) A.M a)=baseVal w.value a^t.ramification := by
  have hp (P:Cq.E[X]) :t.value (algebraMap (tu Cq.E) A.M
      (algebraMap Cq.E[X] (tu Cq.E) P)) =
        baseVal w.value (algebraMap Cq.E[X] (tu Cq.E) P)^t.ramification := by
    rw [base_eval,t.overGauss,base_poly]
    rfl
  obtain ⟨N,D,_,rfl⟩:=IsFractionRing.div_surjective Cq.E[X] a
  rw [map_div₀,t.value.map_div,(baseVal w.value).map_div,div_pow,hp,hp]
theorem base_coeff (w:CurvePlace L Cq.E) {R:Cq.E[X][X]} (hR:R≠0)
   (hI:aFA w.value R 0) {P: (tu Cq.E)[X]} {k :ℕ} (hP:P≠0)
   (hD:P^k∣R.map (algebraMap Cq.E[X] (tu Cq.E))) :
   k*j3 (baseVal w.value) P≤KB w.value (chargeCoeff R) := by
 let j:=algebraMap Cq.E[X] (tu Cq.E)
 have hi:=zxb Cq.E[X] (tu Cq.E)
 have hQ:R.map j≠0:= fun h=>hR ((zTo j hi) (h.trans (Polynomial.map_zero j).symm))
 have hQint (i:ℕ) :baseVal w.value ((R.map j).coeff i)≤1 := by
   rw [coeff_map,base_poly]
   exact zf9 fun n _=> by simpa using hI i n
 have ht: (R.map j).natTrailingDegree=R.natTrailingDegree := by
   rw [natTrailingDegree,natTrailingDegree,trailingDegree,trailingDegree,
     support_map_of_injective R hi]
 have htc: (R.map j).trailingCoeff=j R.trailingCoeff := by
   rw [trailingCoeff,ht,coeff_map]
   rfl
 have hle :w.value (chargeCoeff R)≤baseVal w.value ((R.map j).trailingCoeff) := by
   rw [htc,base_poly]
   exact dMr w.value R.trailingCoeff R.trailingCoeff.natDegree
 have ht0:R.trailingCoeff≠0:=trailingCoeff_nonzero_iff_nonzero.mpr hR
 have hclog:log (w.value (chargeCoeff R))≤log (baseVal w.value ((R.map j).trailingCoeff)) :=
   (log_le_log (w.value.ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr ht0))
     ((baseVal w.value).ne_zero_iff.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hQ))).2 hle
 exact (debit_le_trailing _ hP hQ hQint hD).trans (z0Z (by omega))
end
end qXARP7c
end
section
namespace qb1WXKc
def c1 :Prop :=qymFiQe.c1
def c2 :Prop :=qymFiQe.c2
theorem of_children (span:c1) (coeffs :c2) :qLXroAb.c3 :=
 qCe4xzb.of_children infinity_discr
  (qymFiQe.of_children span coeffs 0)
end qb1WXKc
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace q0mTRkc
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L FX j9)
open P5_7_7 (phys)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (IntSeries residue Ua map_liftAt liftAt_reduce small_valuation
 power_residue fWQ)
open qFD8jve (sheetPole)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qxPDCsa (Bound UnitAt)
open qrezXJe (resultant_val_le sheet_bound)
open private guard_count from ProximityPrize.SubmissionLower.Zay1XCa
open private bOH from ProximityPrize.SubmissionLower.Znkyowe
open private efc adG cTA aMX from ProximityPrize.SubmissionLower.Y
private def row {R:Type} [za6 R] (j:ℕ) (f :R[X][X]) :R[X][X] :=
 ((Bivariate.swap f).coeff j).map z1z
private theorem c9b {R:Type} [za6 R] (j i:ℕ) (f :R[X][X]) :
  (row j f).coeff i=z1z ((f.coeff i).coeff j) := by
 rw [row,coeff_map,bOH]
private theorem row_map {R S:Type} [za6 R] [za6 S]
  (b:R →+* S) (j:ℕ) (f :R[X][X]) :
  (row j f).map (mapRingHom b)=row j (f.map (mapRingHom b)) := by
 ext i k
 simp only [coeff_map,coe_mapRingHom,c9b,map_C]
private theorem row_eval_zero {f :L[X][X]} {y :L} (h:f.eval (z1z y)=0)
  (j:ℕ) : (row j f).eval (z1z y)=0:= by
 have he :f.eval (z1z y)=(Bivariate.swap f).map (evalRingHom y) := by
  simpa [Polynomial.aeval_def,Polynomial.algebraMap_eq] using
    (Bivariate.aveal_eq_map_swap y f)
 have hz : ((Bivariate.swap f).coeff j).eval y=0:= by
  rw [he] at h
  simpa only [coeff_map,coe_evalRingHom,coeff_zero] using
    congrArg (fun g:L[X]=>g.coeff j) h
 simp only [row,eval_map_apply,hz,map_zero]
private theorem resultant_ne {E :Type} [Field E] {f :E[X][X]} {j:ℕ}
   (hf :Irreducible f) (hy :0<f.natDegree) (hx :0<(Bivariate.swap f).natDegree)
   (hr :row j f≠0) :f.resultant (row j f)≠0:= by
 let b:=algebraMap E[X] (FractionRing E[X])
 have hi:=zxb E[X] (FractionRing E[X])
 have hp:=hf.isPrimitive hy.ne'
 have hfg:Irreducible (f.map b) :=
   (hp.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing E[X])).mp hf
 have hc:IsCoprime (f.map b) ((row j f).map b) :=hfg.coprime_iff_not_dvd.mpr fun hd=> by
   have hd' := hp.dvd_of_fraction_map_dvd_fraction_map hd
   have hh:=natDegree_le_of_dvd (map_dvd (Bivariate.swap (R:=E)) hd')
     ((map_ne_zero_iff _ (Bivariate.swap (R:=E)).injective).mpr hr)
   rw [row,Bivariate.swap_map_C,natDegree_C] at hh
   exact (not_lt_of_ge hh) hx
 have h:=resultant_ne_zero _ _ hc
 rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,resultant_map_map] at h
 exact fun hz=>h (by rw [hz,map_zero])
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
private theorem residue_zero (F:Sheet Cq z S) {γ:K} (hγ:γ∈F.marks)
   (hs : (S γ).natDegree=0) (j k :ℕ) :
   (F.place γ).value ((F.f.resultant (row j F.f)).coeff k)<1 := by
 let a :=F.atPlace γ hγ
 let G:=Ua a F.f (fun i l=>(F.value γ hγ _).symm ▸ F.integral γ hγ i l)
 let m:=F.d
 let n:=(row j F.f).natDegree
 let R:=G.resultant (row j G) m n
 have hsub:G.map (mapRingHom IntSeries.subtype)=F.f.map (mapRingHom a.toRingHom) :=
   map_liftAt _ _ _
 have hred:G.map (mapRingHom residue)=cLN a 0 F.f :=liftAt_reduce _ _ _
 have hinj:zq4 (mapRingHom IntSeries.subtype) :=
   zTo _ IntSeries.subtype_injective
 have hd:G.natDegree=m:= by
   rw [← natDegree_map_eq_of_injective hinj,hsub,
     natDegree_map_eq_of_injective (zTo _ a.injective)]
 have hn: (row j G).natDegree=n:= by
   rw [← natDegree_map_eq_of_injective hinj,row_map,hsub,← row_map,
     natDegree_map_eq_of_injective (zTo _ a.injective)]
 have hRs :R.map IntSeries.subtype=(F.f.resultant (row j F.f)).map a.toRingHom:= by
   change mapRingHom IntSeries.subtype (G.resultant (row j G) m n)=mapRingHom a.toRingHom _
   rw [← resultant_map_map,row_map,hsub,← row_map,resultant_map_map]
 let y :=(j9 (S γ)).coeff 0
 have he :j9 (S γ)=z1z y :=
   eq_C_of_natDegree_le_zero (natDegree_map_le.trans hs.le)
 have hf :=F.root γ hγ
 have hp:=(eval₂_hom (p:=cLN a 0 F.f) phys (j9 (S γ))).symm.trans hf
 have h0: (cLN a 0 F.f).eval (z1z y)=0:= by
   rw [← he]
   exact (map_eq_zero_iff _ (zxb L[X] FX)).mp hp
 have hR0:R.map residue=0:= by
   exact map_resultant_eq_zero_of_common_root (mapRingHom residue) G (row j G)
     hd.le hn.le (Or.inl F.positive.ne') (z1z y) (hred.symm ▸ h0)
     (by rw [row_map,hred]; exact row_eval_zero h0 _)
 let u:=R.coeff k
 have hu: (u:LaurentSeries L)=a ((F.f.resultant (row j F.f)).coeff k) := by
   change (R.coeff k :LaurentSeries L)=a.toRingHom ((F.f.resultant (row j F.f)).coeff k)
   simpa only [coeff_map,Subring.subtype_apply] using
     congrArg (fun t: (LaurentSeries L)[X]=>t.coeff k) hRs
 have hv :residue u=0:= by
   simpa only [coeff_map,coeff_zero] using congrArg (fun t:L[X]=>t.coeff k) hR0
 obtain ⟨t,ht⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective u
 have ht' : (u:LaurentSeries L)=(t:LaurentSeries L) := by
   rw [← ht,LaurentSeries.powerSeriesEquivSubring_coe_apply]
 rw [F.value γ hγ,← hu,ht']
 exact ((small_valuation t).mpr ((power_residue _ t ht').symm.trans
   ((fWQ u).symm.trans hv))).trans_lt (WithZero.exp_lt_one_iff.mpr (by decide))
theorem dO2 (F:Sheet Cq z S) (T:Finset K) (hT:T⊆F.marks)
   (hs : ∀ γ∈T,(S γ).natDegree=0) (hX : ∃ i,0<(F.f.coeff i).natDegree) :
   T.card≤2*F.d*F.h:= by
 obtain ⟨i,hi⟩:=hX
 let j:=(F.f.coeff i).natDegree
 have hh: (F.f.coeff i).coeff j≠0 :=
   leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hi)
 have hx :0<(Bivariate.swap F.f).natDegree :=
   hi.trans_le (le_natDegree_of_ne_zero (fun hz=>hh (by rw [← bOH,hz,coeff_zero])))
 let G:=row j F.f
 have hG:G≠0:= fun hz=>hh (by
   have h:=congrArg (fun f :Cq.E[X][X]=>f.coeff i) hz
   change (row j F.f).coeff i= _ at h
   simpa only [c9b,coeff_zero,C_eq_zero] using h)
 let R:=F.f.resultant G
 have hR:R≠0:=resultant_ne F.irreducible F.positive hx hG
 have hdeg:G.natDegree≤F.d:=natDegree_le_iff_coeff_eq_zero.mpr fun l hl=> by
   change (row j F.f).coeff l=0
   rw [c9b,coeff_eq_zero_of_natDegree_lt hl,coeff_zero,map_zero]
 have hb:Bound F R (F.d+G.natDegree) := by
   intro w k
   let v :=efc w.value
   let b:=WithZero.exp (sheetPole w.value F.f :ℤ)
   have hf (l:ℕ) :v (F.f.coeff l)≤b:=zf9 fun x _=>sheet_bound w.value F.f l x
   have hg (l:ℕ) :v (G.coeff l)≤b:= by
     change adG w.value ((row j F.f).coeff l)≤_
     rw [c9b,cTA]
     exact sheet_bound w.value F.f l j
   exact (aMX w.value _ k).trans ((resultant_val_le v F.f G _ _ b hf hg).trans_eq (by
     simp [b,← WithZero.exp_nsmul]))
 let k :=R.natDegree
 have hbad:T⊆F.marks.filter (fun γ => ¬ UnitAt F γ (R.coeff k)) := fun γ hγ =>
   mem_filter.mpr ⟨hT hγ,(residue_zero F (hT hγ) (hs γ hγ) j k).ne⟩
 exact (card_le_card hbad).trans ((guard_count F (leadingCoeff_ne_zero.mpr hR) hb).trans
   (ztf _ (by omega)))
end
end q0mTRkc
end
section
namespace q0mTRkc
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open cu (L FX j9)
open P5_7_7 (phys)
open E7 (KB)
open qYdH9sc (polarDegree poleFee)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (expansion_coeff)
open qFD8jve (aFA)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation atPolynomial)
open qxPDCsa (discDegree Good)
open qLXroAb (chargeCoeff)
open private choose_variation restrict zJ height_zero from ProximityPrize.SubmissionLower.Zay1XCa
open private sum_charge from ProximityPrize.SubmissionLower.ZFqQTue
def c1 :Prop :=qLXroAb.c1
def c2 :Prop :=qLXroAb.c2
def c3:Prop :=qLXroAb.c3
def c4 :Prop :=qLXroAb.c4
def c5:Prop :=qLXroAb.c5
def c6:Prop :=qLXroAb.c6
def c7:Prop :=qLXroAb.c7
private theorem disc_le {D g W:ℕ} (hg:0<g) (hW:g*D ≤W) :
  discDegree D g W≤polarDegree D g W:= by
 have h₁: (2*g-1)*W=(2*g-2)*W+W:= by
  rw [← Nat.add_one_mul,show 2*g-2+1=2*g-1 by omega]
 have h₂:g*g*D =g*(g-1)*D + g*D:= calc
  _=g*(g-1+1)*D:= by rw [Nat.sub_add_cancel hg]
  _ = _:= by ring
 rw [discDegree,polarDegree,h₁,h₂]
 omega
private theorem degree_lt {D g W:ℕ} (hg:3≤g) (hW:g*D ≤W)
  (hp:polarDegree D g W<p) :D <p:= by
 have h₁: (g-1)*(g*D)+g*g*D =(2*g-1)*(g*D) := by
  rw [show g*g*D =g*(g*D) by ring,← Nat.add_mul,show g-1+g=2*g-1 by omega]
 have hm:=Nat.mul_le_mul_left (2*g-1) hW
 have hd:D ≤(g-1)*(g*D) := by
  calc
    D =1*(1*D) := by simp
    _≤_:=Nat.mul_le_mul (by omega) (ztf D (by omega))
 change (2*g-1)*W-g*g*D <p at hp
 omega
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
private theorem eval_const_degree (f :L[X][X]) (a :L) {M:ℕ}
  (h : ∀ i,(f.coeff i).natDegree≤M) : (f.eval (z1z a)).natDegree≤M:= by
 rw [eval_eq_sum_range]
 apply natDegree_sum_le_of_forall_le
 intro i _
 rw [← Polynomial.C_pow,mul_comm]
 exact (natDegree_C_mul_le _ _).trans (h i)
private theorem const_den_degree (V:Variation F) {γ:K} (hγ:γ∈V.marks) {M:ℕ}
    (hS: (S γ).natDegree=0) (hF : ∀ i,(F.f.coeff i).natDegree≤M) :
    (V.den γ).natDegree≤M:= by
  let a :=F.atPlace γ (V.Bp hγ)
  let f :=cLN a 0 F.f
  let d:=f.derivative.eval (j9 (S γ))
  have he (g:L[X][X]) :phys (g.eval (j9 (S γ)))=atPolynomial g (S γ) :=
    (eval₂_hom (p:=g) phys (j9 (S γ))).symm
  have hinj:zq4 phys :=zxb L[X] FX
  have hdp:phys d≠0:=(he _).trans_ne (V.simple γ hγ)
  have hd:d≠0:=(map_ne_zero_iff phys hinj).mp hdp
  have hfrac:=V.formula γ hγ
  change _ = -(atPolynomial (cLN a 1 F.f) (S γ) /
    atPolynomial f.derivative (S γ)) at hfrac
  rw [← he,← he,neg_div',← map_neg] at hfrac
  have hmul :V.num γ*d = -((cLN a 1 F.f).eval (j9 (S γ)))*V.den γ :=
    hinj (by simpa only [map_mul] using
      (div_eq_div_iff ((map_ne_zero_iff phys hinj).mpr (V.den_ne γ hγ)) hdp).mp hfrac)
  have hdiv :V.den γ∣d:=(V.reduced γ hγ).symm.dvd_of_dvd_mul_left (by
    rw [hmul]
    exact dvd_mul_left _ _)
  apply (natDegree_le_of_dvd hdiv hd).trans
  have hs : (j9 (S γ)).natDegree≤0:=natDegree_map_le.trans hS.le
  dsimp only [d]
  rw [eq_C_of_natDegree_le_zero hs]
  apply eval_const_degree
  intro i
  rw [coeff_derivative,← Nat.cast_succ,← Polynomial.C_eq_natCast,mul_comm]
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  change ((cLN a 0 F.f).coeff (i+1)).coeff j=0
  rw [expansion_coeff,coeff_eq_zero_of_natDegree_lt ((hF _).trans_lt hj),map_zero,
    HahnSeries.coeff_zero]
private theorem constant_budget (V:Variation F) {W:ℕ} (hw:F.weight 0 W)
    (hg:3≤F.d) (hs : ∀ γ∈V.marks,(S γ).natDegree≤0)
    (hi : ∀ γ∈V.marks,(V.num γ).natDegree≤0+(V.den γ).natDegree) :
    ∑ γ∈V.marks,V.DG 0 γ≤poleFee 0 F.d W*F.h:= by
  have he (γ:K) (hγ:γ∈V.marks) :V.DG 0 γ=(V.den γ).natDegree := by
    have hn: (V.num γ).natDegree≤(V.den γ).natDegree := by simpa using hi γ hγ
    simp only [Variation.DG,Nat.sub_zero,max_eq_left hn]
  by_cases hX : ∃ i,0<(F.f.coeff i).natDegree
  · have hw' (i:ℕ) : (F.f.coeff i).natDegree≤W:= by
      by_cases hn:F.f.coeff i=0
      · simp [hn]
      · simpa using hw i hn
    have hc:=dO2 F V.marks V.Bp (fun γ hγ=>za7 (hs γ hγ)) hX
    calc
      _ ≤ ∑ _γ∈V.marks,W:=sum_le_sum fun γ hγ=> by
        rw [he γ hγ]
        exact const_den_degree V hγ (za7 (hs γ hγ)) hw'
      _=V.marks.card*W:= by simp [Nat.mul_comm]
      _≤(2*F.d*F.h)*W:=ztf _ hc
      _=(2*F.d*W)*F.h:= by ring
      _≤_:= by
        simp only [poleFee,Nat.mul_zero,Nat.sub_zero]
        exact ztf _ (ztf _ (by omega))
  · have hz (i:ℕ) : (F.f.coeff i).natDegree≤0:=Nat.le_of_not_gt (fun hi=>hX ⟨i,hi⟩)
    have hs0 : ∑ γ∈V.marks,V.DG 0 γ ≤ ∑ _γ∈V.marks,0 :=
      sum_le_sum fun γ hγ=> by
        rw [he γ hγ]
        exact const_den_degree V hγ (za7 (hs γ hγ)) hz
    simpa using hs0.trans (by simp)
theorem of_children (disc:c1) (refs :c2) (infty :c3) (bY:c4) (elim:c5)
   (orders :c6) (norm:c7) :qYdH9sc.c4 := by
 intro q Cq z S F D g W hd hg hp hW hguard hw hS
 subst g
 obtain ⟨hδ,hδd,hδb,hsimple⟩:=disc F D W hp hw
 have hδp:=(hδd.trans (disc_le F.positive hW)).trans_lt hguard
 obtain ⟨V,hV⟩:=choose_variation F hsimple
 obtain ⟨A⟩:=refs V D W hw
 let T:=F.marks.filter (Good A)
 have hT:T⊆F.marks :=filter_subset _ _
 have ht:T⊆V.marks := by
   rw [hV]
   exact fun γ hγ=>mem_filter.mpr ⟨hT hγ,(mem_filter.mp hγ).2.1⟩
 let U:=restrict V ht
 have hi (γ:K) (hγ:γ∈T) : (U.num γ).natDegree≤D+(U.den γ).natDegree :=
   infty A hp hw γ (ht hγ) (mem_filter.mp hγ).2 (hS γ (hT hγ))
 refine ⟨U,(zJ A hδ hδb).trans (ztf _ (by omega)),?_⟩
 by_cases hD:D =0
 · subst D
   exact constant_budget U hw hg (fun γ hγ=>hS γ (hT hγ)) hi
 have hD' := Nat.pos_of_ne_zero hD
 obtain ⟨P,hchart⟩:=bY U hg hp
 obtain ⟨R,hR,hb,hdiv⟩:=elim P D W hg hD' (degree_lt hg hW hguard) hW hw
 have hc:chargeCoeff R≠0 :=
   leadingCoeff_ne_zero.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hR)
 have hbound:=sum_charge F hc hT (fun w=>hb w R.natTrailingDegree R.trailingCoeff.natDegree)
 have hlocal (γ:K) (hγ:γ∈T) :
     D*U.DG D γ≤KB (F.place γ).value (chargeCoeff R) := by
   have hv :=orders U P hp hδ hδp γ hγ (mem_filter.mp hγ).2.1 (hchart γ hγ).some
   have hbr :aFA (F.place γ).value R 0:= by
     simpa only [height_zero (hT hγ),Nat.mul_zero] using hb (F.place γ)
   rw [Variation.DG,max_eq_left (by have :=hi γ hγ; omega)]
   exact norm P (F.place γ) (U.den γ) R D (U.den_ne γ hγ) hR hbr hdiv hv
 apply Nat.le_of_mul_le_mul_left _ hD'
 change D*(∑ γ∈T,U.DG D γ)≤D*(poleFee D F.d W*F.h)
 rw [mul_sum]
 exact (sum_le_sum hlocal).trans (hbound.trans_eq (mul_assoc _ _ _))
end
end q0mTRkc
end
end
