import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZCqrzHc
import ProximityPrize.SubmissionLower.Zsty7Cb
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Fin.castSucc_injective → zX8, Fin.last → zym, Fin.lastCases_castSucc → zwu, Fin.lastCases_last → zTz, Fin.sum_univ_castSucc → zHE, Finset.sum_le_sum → zQk, Finsupp.weight → ztN, Finsupp.weight_apply → zDM, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Ideal.span → zye, Int.natCast_nonneg → zbO, Nat.mul_le_mul_left → zBI, Nat.mul_left_comm → zZ0, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.eval_C → zFf, Polynomial.eval_X → zB5, Polynomial.eval_add → zvF, Polynomial.eval_mul → zbr
set_option maxHeartbeats 3000000
section
set_option autoImplicit true
namespace qU25pbd
noncomputable section
open aR (Shape)
open dN (GeoField GeoJets)
open vS (g9)
open B8 (lS bF Exponent Qj Nl qK)
open agM (Vw agj)
open aA6 (RM b0z Kx)
open qZqYIua (geoShape)
open MvPolynomial
open scoped Pointwise
open private aHz from ProximityPrize.SubmissionLower.J
private def totalWt:Fin 5→ℕ:=Fin.lastCases 0 (fun _=>1)
private def indexWt:Fin 5→ℕ:=Fin.lastCases 0 Fin.val
private theorem weight_sum (w:Fin 5→ℕ) (m:Exponent) :
    ztN w m = ∑ i:Fin 5,w i*m i:= by
  rw [zDM,Finsupp.sum_fintype m (fun i c=>c•w i)
    (fun i=>zero_smul ℕ (w i))]
  simp only [smul_eq_mul,Nat.mul_comm]
private def hShape (g:g9) :Shape :=
  ⟨weightedTotalDegree totalWt g,weightedTotalDegree indexWt g,degreeOf 3 g⟩
private theorem fits (g:g9) (a :Shape×ℕ) :
    g∈restrictSupport GeoField (Nl a) ↔
      (hShape g).b≤2*a.1.b∧(hShape g).j≤2*a.1.j ∧
      (hShape g).t≤2*a.1.t∧degreeOf 4 g≤2*a.2 := by
  change (g.support :Set _)⊆Nl a↔_
  have h₁ (m:Exponent) :ztN totalWt m = ∑ i:Fin 4,m i.castSucc:= by
    rw [weight_sum,zHE]
    simp only [totalWt,zTz,zwu,zero_mul,add_zero,one_mul]
  have h₂ (m:Exponent) :
      ztN indexWt m = ∑ i:Fin 4,i.val*m i.castSucc:= by
    rw [weight_sum,zHE]
    simp only [indexWt,zTz,zwu,zero_mul,add_zero]
  simp only [hShape,Nl,Qj,Set.subset_def,Finset.mem_coe,
    Set.mem_ofPred_eq,Shape.scale]
  constructor
  · intro h
    exact ⟨Finset.sup_le fun m hm=>h₁ m ▸ (h m hm).1,
      Finset.sup_le fun m hm=>h₂ m ▸ (h m hm).2.1,
      degreeOf_le_iff.mpr (fun m hm=>(h m hm).2.2.1),
      degreeOf_le_iff.mpr (fun m hm=>(h m hm).2.2.2)⟩
  · rintro ⟨hb,hj,ht,hz⟩ m hm
    exact ⟨h₁ m ▸ (le_weightedTotalDegree totalWt hm).trans hb,
      h₂ m ▸ (le_weightedTotalDegree indexWt hm).trans hj,
      (monomial_le_degreeOf 3 hm).trans ht,(monomial_le_degreeOf 4 hm).trans hz⟩
theorem embed_ne {g:GeoJets} (hg:g≠0) :qK g≠0:= by
  exact (rename_injective _ (zX8 4)).ne (by simpa using hg)
private theorem embed_shape (g:GeoJets) :hShape (qK g)=geoShape g:= by
  unfold hShape geoShape qK
  change Shape.mk (weightedTotalDegree totalWt (rename z1o g))
    (weightedTotalDegree indexWt (rename z1o g))
    (degreeOf (z1o (3:Fin 4)) (rename z1o g))= _
  simp only [weightedTotalDegree_rename_of_injective (zX8 4),
    degreeOf_rename_of_injective (zX8 4)]
  have h₁:totalWt ∘ z1o=(1 :Fin 4→ℕ) := by
    funext i
    simp [totalWt]
  have h₂:indexWt ∘ z1o=(Fin.val :Fin 4→ℕ) := by
    funext i
    simp [indexWt]
  rw [h₁,h₂,weightedTotalDegree_one]
private theorem embed_last (g:GeoJets) :degreeOf 4 (qK g)=0:= by
  change degreeOf (zym 4) (rename z1o g)=0
  rw [← weightedTotalDegree_piSingle,weightedTotalDegree_rename_of_injective (zX8 4)]
  have h:Pi.single (zym 4) (1 :ℕ) ∘ z1o=(0:Fin 4→ℕ) := by
    funext i
    change (Pi.single (zym 4) (1 :ℕ) :Fin 5→ℕ) i.castSucc=0
    rw [Pi.single_apply,ite_eq_right (Fin.castSucc_ne_last i)]
  change weightedTotalDegree (Pi.single (zym 4) (1 :ℕ) ∘ z1o) g=0
  rw [h]
  simp [weightedTotalDegree,zDM]
private theorem mul_shape {g v :g9} (hg:g≠0) (hv :v≠0) :
    hShape (g*v)=(hShape g).plus (hShape v) := by
  simp only [hShape,Shape.plus,← weightedTotalDegree_piSingle,
    weightedTotalDegree_mul _ _ _ hg hv]
private theorem fits_mul {g:GeoJets} (hg:g≠0) (v :g9) (a :Shape×ℕ) :
    (qK g)^2*v∈restrictSupport GeoField
      (Nl (a.1.plus (geoShape g),a.2)) ↔
      v∈restrictSupport GeoField (Nl a) := by
  by_cases hv :v=0
  · simp [hv]
  have he :=embed_ne hg
  have hm {k l:g9} (hk :k≠0) (hl:l≠0) :
      degreeOf 4 (k*l)=degreeOf 4 k+degreeOf 4 l:= by
    simp only [← weightedTotalDegree_piSingle (4 :Fin 5),weightedTotalDegree_mul _ _ _ hk hl]
  rw [fits,fits,mul_shape (pow_ne_zero _ he) hv,pow_two,mul_shape he he,embed_shape]
  rw [hm (mul_ne_zero he he) hv,hm he he,embed_last]
  simp only [zero_add,Shape.plus]
  omega
private theorem rank_square (g:GeoJets) (hg:g≠0) (a :Shape×ℕ) :
    Module.finrank GeoField ((restrictSupport GeoField
      (Nl (a.1.plus (geoShape g),a.2))).map
      (zvR GeoField (zye {(qK g)^2})).toLinearMap) +
      (Nl a).ncard=(Nl (a.1.plus (geoShape g),a.2)).ncard:= by
  classical
  let d:=(qK g)^2
  let J:Ideal g9:=zye {d}
  let S:=Nl (a.1.plus (geoShape g),a.2)
  let T:=Nl a
  let U:=restrictSupport GeoField S
  let V:=restrictSupport GeoField T
  let π:=(zvR GeoField J).toLinearMap.domRestrict U
  let μ:=((LinearMap.mulLeft GeoField d).domRestrict V).codRestrict U
    (fun v=>(fits_mul hg v.val a).mpr v.property)
  let:Module.Finite GeoField U:=restrictSupport_finite (Set.toFinite S)
  have hμ:Function.Injective μ:= fun x y h =>
    Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ (embed_ne hg)) (congrArg Subtype.val h))
  have hr :LinearMap.range μ=LinearMap.ker π:= by
    ext x
    rw [LinearMap.mem_range,LinearMap.mem_ker]
    change (∃ v,μ v=x)↔zVv J x.val=0
    rw [z1Q]
    constructor
    · rintro ⟨v,rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hx
      obtain ⟨v,hv⟩:=Ideal.mem_span_singleton.mp hx
      have hvu:d*v∈U:=hv ▸ x.property
      exact ⟨⟨v,(fits_mul hg v a).mp hvu⟩,Subtype.ext hv.symm⟩
  have hn:=π.finrank_range_add_finrank_ker
  rw [← hr,LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj hμ] at hn
  have fin (W:Set Exponent) [Finite W] :
      Module.finrank GeoField (restrictSupport GeoField W)=W.ncard:= by
    rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),Nat.card_coe_set_eq]
  exact fin T ▸ fin S ▸ hn
theorem diagonal_rank (B:lS) (hB : ∀ i,bF (B i).1) (t:Fin 5→ℕ)
    (g:GeoJets) (hg:g≠0) (n:ℕ) (a :Shape×ℕ)
    (ha : (a.1.plus (geoShape g),a.2)=agj (Vw B t) n) :
    affineHilbertFunction (RM B (zye {(qK g)^2}) t) n +
      (Nl a).ncard=(Nl (agj (Vw B t) n)).ncard:= by
  rw [b0z,Kx,← aHz,cys.proof B hB t n,← ha]
  exact rank_square g hg a
end
end qU25pbd
end
section
set_option autoImplicit true
namespace qU25pbd
noncomputable section
open aR (Shape)
open dN (GeoJets)
open B8 (lS bF qK)
open agM (Vw agj euK)
open aA6 (RM)
open Dr (ChamberBox)
open qZqYIua (geoShape)
open MvPolynomial
open private count count_eq from ProximityPrize.SubmissionLower.ZCqrzHc
def volumeSlope (s a :Shape) :ℚ :=
  let b:ℚ:=a.b
  let j:ℚ:=a.j
  let t:ℚ:=a.t
  let u:ℚ:=s.b
  let v :ℚ:=s.j
  let w:ℚ:=s.t
  u*(8*j^2*t - 24*j*t^2+24*t^3) +
  v*(16*b*j*t - 24*b*t^2 - 12*j^2*t+28*j*t^2 - 20*t^3) +
  w*(8*b*j^2 - 48*b*j*t+72*b*t^2 - 4*j^3+28*j^2*t - 60*j*t^2 + 36*t^3)
private def shiftCount (b j t u v w n:ℚ) :ℚ :=
  count (n*b) (n*j) (n*t) - count (n*b-u) (n*j-v) (n*t-w)
private def BZ (s a :Shape) :Polynomial ℚ :=
  let F:=shiftCount a.b a.j a.t s.b s.j s.t
  let L:=volumeSlope s a/2
  z1z L*z7y ^3 +
    z1z ((F 1+F (-1))/2 - F 0)*z7y ^2 +
    z1z ((F 1-F (-1))/2 - L)*z7y+Polynomial.C (F 0)
private theorem eval_ray (s a :Shape) (n:ℚ) :
    (BZ s a).eval n=shiftCount a.b a.j a.t s.b s.j s.t n:= by
  simp only [BZ,zvF,zbr,Polynomial.eval_pow,zFf,
    zB5,volumeSlope,shiftCount,count]
  ring
private theorem bgD (s a :Shape) (h:ℕ) :
    (BZ s a*(z1z (2*(h:ℚ))*z7y+1)).coeff 4 =
      volumeSlope s a*h:= by
  simp only [mul_add,mul_one,← mul_assoc,Polynomial.coeff_add,Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C,BZ,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C]
  norm_num
theorem interior_sum (B:lS) (hB : ∀ i,bF (B i).1)
    (h0:B 0=(⟨5,4,1⟩,0)) (d:Fin 5→ℕ) (hd:0<d 0) :
    let a :=(Vw B d).1
    a.j<a.b∧3*a.t<a.j∧0<a.t:= by
  have hb : ∑ i:Fin 4,d i.succ*(B i.succ).1.j ≤ ∑ i:Fin 4,d i.succ*(B i.succ).1.b :=
    zQk fun i _=>zBI _ (hB i.succ).1
  have hj:3*(∑ i:Fin 4,d i.succ*(B i.succ).1.t) ≤ ∑ i:Fin 4,d i.succ*(B i.succ).1.j:= by
    rw [Finset.mul_sum]
    exact zQk fun i _=> by
      simpa only [zZ0] using zBI (d i.succ) (hB i.succ).2
  simp only [Vw,Fin.sum_univ_succ,h0] at hb hj ⊢
  omega
theorem bEc (B:lS) (hB : ∀ i,bF (B i).1)
    (d:Fin 5→ℕ) (g:GeoJets) (hg:g≠0)
    (hint : let a := (Vw B d).1; a.j < a.b ∧ 3 * a.t < a.j ∧ 0 < a.t) :
    (affineHilbertPolynomial (RM B (zye {(qK g)^2}) d)).coeff 4 =
      volumeSlope (geoShape g) (Vw B d).1*(Vw B d).2 := by
  let a :=(Vw B d).1
  let h:=(Vw B d).2
  let s :=geoShape g
  let F:=BZ s a*(z1z (2*(h:ℚ))*z7y+1)
  suffices he :F=affineHilbertPolynomial (RM B (zye {(qK g)^2}) d) by
    rw [← he]
    exact bgD s a h
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=s.b+s.j+s.t+1)
  intro n hn
  change a.j<a.b∧3*a.t<a.j∧0<a.t at hint
  obtain ⟨hb,hj,ht⟩:=hint
  have hb' := zBI n (Nat.succ_le_iff.mpr hb)
  have hj' := zBI n (Nat.succ_le_iff.mpr hj)
  have ht' : n≤n*a.t:= by simpa using zBI n ht
  simp only [Nat.mul_succ,zZ0 n 3] at hb' hj'
  let b:=a.scale n
  have hb'' : b.j+s.b≤b.b:= by change n*a.j+s.b≤n*a.b; omega
  have hj'' : 3*b.t+s.j≤b.j:= by change 3*(n*a.t)+s.j≤n*a.j; omega
  have ht'' : s.t<b.t:= by change s.t<n*a.t; omega
  let c:Shape :=⟨b.b-s.b,b.j-s.j,b.t-s.t⟩
  have hcb:c.plus s=b:= by
    simp [c,Shape.plus,Nat.sub_add_cancel (by omega :s.b≤b.b),
      Nat.sub_add_cancel (by omega :s.j≤b.j),Nat.sub_add_cancel ht''.le]
  have hB' : ChamberBox b:=⟨by omega,by omega,by omega⟩
  have hC:ChamberBox c:= by
    change b.j-s.j≤b.b-s.b∧3*(b.t-s.t)≤b.j-s.j∧0<b.t-s.t
    omega
  have hr :=diagonal_rank B hB d g hg n (c,n*h) (by
    change (c.plus s,n*h)=(b,n*h)
    rw [hcb])
  rw [show agj (Vw B d) n=(b,n*h) from rfl,euK,euK] at hr
  have hr' := congrArg (fun k :ℕ=>(k :ℚ)) hr
  push_cast at hr'
  rw [count_eq c hC,count_eq b hB'] at hr'
  simp only [F,zbr,zvF,zFf,zB5,
    Polynomial.eval_one,eval_ray,shiftCount]
  rw [eq_sub_of_add_eq hr']
  dsimp only [c]
  rw [Nat.cast_sub (by omega :s.b≤b.b),Nat.cast_sub (by omega :s.j≤b.j),
    Nat.cast_sub ht''.le]
  simp only [b,Shape.scale,Nat.cast_mul]
  ring
end
end qU25pbd
end
section
set_option autoImplicit true
namespace qU25pbd
noncomputable section
open aR (Shape aO qP)
open dN (GeoField GeoJets bC)
open vS (g9 tC)
open B8 (lS bF Admissible MH qK tW i9
  H7 aC0 bA1)
open agM (Vw diagonal)
open aA6 (RM)
open P6_6 (bf pair32)
open qsnQ6jb (boxes a4d aRQ)
open qZqYIua (geoShape)
open MvPolynomial
open private product_admissible from ProximityPrize.SubmissionLower.Zsty7Cb
open private axg.b9k from ProximityPrize.SubmissionLower.J
open private alt aCd bT8 DB aXN aAj ahP ayr bhc gpW bB8 bB9 dEB dEA from ProximityPrize.SubmissionLower.BI
open private Q9 bwo bwp from ProximityPrize.SubmissionLower.T
private abbrev dirs :Finset (Fin 5) := {1, 2,3,4}
private theorem square_degree (B:lS) (hB:Admissible B) (f :g9) (hf :f≠0) :
    tW B (zye {f^2}) dirs =
      tW B (zye {f}) dirs+tW B (zye {f}) dirs := by
  let J:Ideal g9:=zye {f^2}
  let Q:Ideal g9:=zye {f}
  have hJQ:J≤Q:=Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self f (by decide))
  have hreg:IsLeftRegular (zVv (⊥ : Ideal g9) (f^2)) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq,z1Q,Ideal.mem_bot]
    exact pow_ne_zero 2 hf
  have hdim:MH J dirs.card:= by
    simpa only [show dirs.card=4 by decide,i9,bot_sup_eq,J] using
      (aC0 (d:=4) hreg bA1)
  have hc (x :g9) :x*f∈J↔x∈Q:= by
    simp only [J,Q,Ideal.mem_span_singleton]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v,mul_right_cancel₀ hf (by linear_combination hv)⟩
    · rintro ⟨v,rfl⟩
      exact ⟨v,by ring⟩
  have he :i9 J f= Q:=sup_eq_right.mpr hJQ
  simpa only [he] using axg.b9k bzC.proof hB hdim hc
set_option maxRecDepth 4096 in
private theorem slope_differences (s q a b:Shape) :
    aAj b (aAj a (aAj q (volumeSlope s))) =
      fun _=>(aXN s q a b:ℚ) := by
  funext x
  simp only [aAj,volumeSlope,aXN,aR.gI,aR.Dn,Shape.plus]
  push_cast
  ring
private theorem j4 (s q g a b:Shape) (u v :ℕ) (x :Shape×ℕ) :
    DB (b,v) (DB (a,u) (DB (g,1)
      (DB (q,0) (ahP (volumeSlope s))))) x =
      (aXN s q a b:ℚ)+(u:ℚ)*(aXN s q g b:ℚ) +
        (v :ℚ)*(aXN s q g a :ℚ) := by
  simp only [dEB,bB8,bB9,dEA,
    Nat.cast_zero,zero_mul,add_zero,gpW,slope_differences]
  simp only [ahP,ayr,bhc,aAj,sub_self,zero_mul,
    zero_add,Nat.cast_one,one_mul]
  ring
private def prismPrice (s q p:Shape) :ℤ :=
  let u:=bf+1
  let v :=bf+2
  let a :=qP u p
  let b:=qP v p
  let c:=tC p
  aXN s q a b+(u:ℤ)*aXN s q c b+(v :ℤ)*aXN s q c a
private theorem square_bill (g:GeoJets) (hg:g≠0) (q p:Shape) (hq:bF q) :
    16*tW (boxes q p) (zye {(qK g)^2}) dirs =
      (prismPrice (geoShape g) q p:ℚ) := by
  let B:=boxes q p
  let J:Ideal g9:=zye {(qK g)^2}
  have hB:=(product_admissible q p hq).1
  have hc:dirs.card=4 := by decide
  have he (U:Finset (Fin 5)) :
      (affineHilbertPolynomial (J.comap (monomialMap GeoField
        (H7 B (diagonal U))))).coeff dirs.card =
          ahP (volumeSlope (geoShape g)) (Vw B (diagonal U)) := by
    change (affineHilbertPolynomial (RM B J (diagonal U))).coeff dirs.card= _
    rw [hc,bEc B hB _ g hg (interior_sum B hB rfl _ (by unfold diagonal; split <;> decide))]
    rfl
  change 16*tW B J dirs= _
  unfold tW
  rw [show (2 :ℚ)^dirs.card = 16 by rw [hc]; norm_num,← mul_div_assoc,
    mul_div_cancel_left₀ _ (by decide)]
  change (∑ U∈dirs.powerset,(-1 :ℚ)^(dirs.card-U.card) *
    (affineHilbertPolynomial (J.comap (monomialMap GeoField
      (H7 B (diagonal U))))).coeff dirs.card)= _
  simp only [he]
  change alt B dirs (ahP (volumeSlope (geoShape g)))= _
  rw [show dirs=insert 1 (insert 2 (insert 3 (insert 4 ∅))) by decide,
    aCd _ (by decide),aCd _ (by decide),aCd _ (by decide),
    aCd _ (by decide),bT8]
  let u:=bf+1
  let v :=bf+2
  let a :=qP u p
  let b:=qP v p
  change DB (b,v) (DB (a,u) (DB (tC p,1)
    (DB (q,0) (ahP (volumeSlope (geoShape g)))))) _ = _
  simpa only [prismPrice,Int.cast_add,Int.cast_mul,Int.cast_natCast] using
    j4 (geoShape g) q (tC p) a b u v _
private theorem bNU {s r q a b:Shape} (h:aO s r)
    (hq:bF q) (ha :bF a) (hb:bF b) :
    aXN s q a b≤aXN r q a b:= by
  let d:Shape :=⟨r.b-s.b,r.j-s.j,r.t-s.t⟩
  have he :s.plus d=r := by
    obtain ⟨h₁,h₂,h₃⟩:=h
    cases s
    cases r
    simp_all [d,Shape.plus]
  change Q9 s q a b≤Q9 r q a b
  rw [← he,bwo]
  exact le_add_of_nonneg_right (bwp d q a b hq ha hb)
theorem proof :qsnQ6jb.c3:= by
  intro R r q p hR hbox hq _ ht hguard
  let g:=bC R
  let s :=geoShape g
  have hB:=product_admissible q p hq
  have hg:g≠0:=P6_6_7_3.agr hR
  have hs :aO s r :=lB.abr hbox
  have hprice :pair32 true p r q=prismPrice r q p:= by
    have ht' : p.t≠1 := by omega
    have htest : (true && (p.t != 1))=true := by simp [ht']
    unfold aRQ at hguard
    simp only [pair32,htest,ite_true,ite_eq_right hguard]
    rfl
  have hmon :prismPrice s q p≤prismPrice r q p:= by
    unfold prismPrice
    exact add_le_add (add_le_add (bNU hs hq (hB.1 3) (hB.1 4))
      (mul_le_mul_of_nonneg_left (bNU hs hq (hB.1 2) (hB.1 4)) (zbO _)))
      (mul_le_mul_of_nonneg_left (bNU hs hq (hB.1 2) (hB.1 3)) (zbO _))
  have hm:=square_bill g hg q p hq
  rw [square_degree _ hB _ (embed_ne hg)] at hm
  simp only [a4d,i9,bot_sup_eq]
  rw [hprice]
  linarith only [hm,(Int.cast_le (R:=ℚ)).mpr hmon]
end
end qU25pbd
end
