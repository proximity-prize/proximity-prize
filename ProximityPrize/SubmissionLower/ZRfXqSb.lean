import ProximityPrize.SubmissionLower.ZusnbBc
import ProximityPrize.SubmissionLower.ZvqS6Fa
import ProximityPrize.SubmissionLower.ZInx8Od
set_option Elab.async false
open _root_ renaming Algebra.algebraMap_self → zCp, CommRing → za6, DFunLike.congr_fun → zmU, Field → zrb, Finset.sum_eq_single → zi6, Finset.sum_eq_zero → zYF, Function.Injective → zq4, Ideal.subset_span → zCn, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.algebraMap_eq → zYY, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_eq_eval₂Hom → zfM, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.ringHom_ext → zXT, Polynomial.X → z7y, Polynomial.derivative → zst, Polynomial.ext → zXJ, Polynomial.map_C → zrL, Polynomial.map_dvd → z36, Polynomial.map_mul → zNl, Polynomial.map_prod → zeg, Polynomial.map_sub → z3A, Polynomial.map_sum → zWe, Polynomial.map_zero → zgY, Polynomial.ringHom_ext → z86, Polynomial.sum_def → zBJ, PowerSeries → zpm, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb, RingHom.id → zz4, RingHom.id_comp → z70
set_option maxHeartbeats 1000000
section
section
set_option backward.isDefEq.respectTransparency false
namespace qZbPQGe
noncomputable section
open Polynomial
open cu (L)
open q8Z6NHc (jo Index extract perturb)
open private extract_coeff from ProximityPrize.SubmissionLower.ZHTtOyb
open scoped Classical
variable {E :Type} [zrb E] [Algebra L E] {d s a :ℕ}
local notation "A" => Directions E d s a
local notation "F" => LiftField E d s a
local notation "κ" => (algebraMap A F)
local notation "j" => (algebraMap E (AlgebraicClosure E))
local notation "ct" => (PowerSeries.constantCoeff :PowerSeries F →+* F)
theorem line_injective (α:Index d s a→E) :zq4 (line α) := by
 let back :A →+* A:=zOD znf
   (fun i=>z9v i-MvPolynomial.C (j (α i)))
 have h:back.comp ((evalRingHom 1).comp (line α)) =
     MvPolynomial.map ((j).comp (algebraMap L E)) := by
   apply zXT
   · intro z
     simp [back,line,zQb]
   · intro i
     simp [back,line]
 intro x y hxy
 apply MvPolynomial.map_injective ((j).comp (algebraMap L E)) ((j).comp (algebraMap L E)).injective
 rw [← h,zQb,zQb,hxy]
 rfl
theorem seriesLine_injective (α:Index d s a→E) :
   zq4 (seriesLine α) :=
 (Polynomial.coe_injective F).comp ((map_injective κ (zxb A F)).comp (line_injective α))
@[simp] theorem seriesLine_C (α:Index d s a→E) (z :L) :
    seriesLine α (znf z) =
      PowerSeries.C (extend (d:=d) (s :=s) (a :=a) (j (algebraMap L E z))) := by
  simp [seriesLine,line,zQb]
@[simp] theorem seriesLine_residue (α:Index d s a→E) (i:Index d s a) :
    ct (seriesLine α (z9v i)) =
      extend (d:=d) (s :=s) (a :=a) (j (α i)) := by
  simp [seriesLine,line,zQb,zrD]
private def chooseDirection (δ:Index d s a→L) :A →+* AlgebraicClosure E :=
 zY9 (fun i=>j (algebraMap L E (δ i)))
private theorem specialize_line (α:Index d s a→E) (δ:Index d s a→L) (r :jo d s a) :
   (line α r).map (chooseDirection δ)=(perturb α δ r).map j:= by
 let u:jo d s a →+* E[X] :=
   zOD (Polynomial.C.comp (algebraMap L E))
     (fun i=>Polynomial.C (α i)+Polynomial.C (algebraMap L E (δ i))*z7y)
 change ((mapRingHom (chooseDirection δ)).comp (line α)) r=((mapRingHom j).comp u) r
 congr 1
 apply zXT
 · intro z
   simp [chooseDirection,line,u,zQb]
 · intro i
   simp [chooseDirection,line,u,zrD]
private def directionCoeff (α:Index d s a→E) (R: (jo d s a)[X]) (n:ℕ) :A[X] :=
 R.sum fun i r=>monomial i ((line α r).coeff n)
private theorem directionCoeff_coeff (α:Index d s a→E) (R: (jo d s a)[X]) (n i:ℕ) :
   (directionCoeff α R n).coeff i=(line α (R.coeff i)).coeff n:= by
 by_cases hi:i∈R.support
 · simp [directionCoeff,zBJ,finsetSum_coeff,coeff_monomial,hi]
 · simp [directionCoeff,zBJ,finsetSum_coeff,coeff_monomial,hi,
     notMem_support_iff.mp hi]
private theorem cNx (r :A) (hr :r≠0) :
  ∃ δ:Index d s a→L,chooseDirection δ r≠0:= by
 by_contra! h
 apply hr
 let b:L →+* AlgebraicClosure E :=(j).comp (algebraMap L E)
 refine MvPolynomial.funext_set (fun _=>Set.range b)
  (fun _=>Set.infinite_range_of_injective b.injective) ?_
 intro x hx
 have hx' (i:Index d s a) : ∃ z,b z=x i:=hx i (Set.mem_univ i)
 choose δ hδ using hx'
 have he : (fun i=>b (δ i))=x :=funext hδ
 change zY9 x r=0
 rw [← he]
 exact h δ
private theorem reduce_dvd {B:Type} [zrb B] {P Q: (zpm B)[X]}
    (hQ:Q.Monic) (hd:Q∣P) (n:ℕ)
    (hn : ∀ i k,k<n→z2o k (P.coeff i)=0) :
    Q.map zbO ∣
      P.sum (fun i r=>monomial i (z2o n r)) := by
  let t:=(PowerSeries.X:zpm B)^n
  have ht:t≠0:=pow_ne_zero _ PowerSeries.X_ne_zero
  have hm (i:ℕ) :t∣P.coeff i:=PowerSeries.X_pow_dvd_iff.mpr (hn i)
  let V:=P.sum fun i _=>monomial i (Classical.choose (hm i))
  have hV:t•V=P:= by
    simp only [V,zBJ,Finset.smul_sum,smul_monomial,smul_eq_mul,
      ← Classical.choose_spec (hm _)]
    exact sum_monomial_eq P
  have hdiv :Q∣V:= by
    have hz :=(modByMonic_eq_zero_iff_dvd hQ).mpr hd
    rw [← hV,smul_modByMonic,smul_eq_C_mul,mul_eq_zero] at hz
    exact (modByMonic_eq_zero_iff_dvd hQ).mp (hz.resolve_left (C_ne_zero.mpr ht))
  convert z36 zbO hdiv using 1
  simp only [V,zBJ,zWe,map_monomial]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc
    _=z2o n (t*Classical.choose (hm i)) :=
      congrArg (z2o n) (Classical.choose_spec (hm i))
    _ = _:= by
      simpa only [zero_add,PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        PowerSeries.coeff_X_pow_mul (Classical.choose (hm i)) n 0
theorem line_extract (α:Index d s a→E) {R: (jo d s a)[X]}
    (hR:R≠0) {N :E[X]} (hN :N.Monic)
    {Q: (zpm F)[X]} (hQ:Q.Monic) (hdiv :Q∣R.map (seriesLine α))
    (hres :Q.map ct=N.map ((extend (d:=d) (s :=s) (a :=a)).comp j)) :
    ∃ (δ:Index d s a→L) (n:ℕ),extract α δ R n≠0∧N∣extract α δ R n:= by
  have hex : ∃ n,directionCoeff α R n≠0:= by
    by_contra! hz
    apply hR
    apply zXJ
    intro i
    rw [coeff_zero]
    apply line_injective α
    apply zXJ
    intro n
    rw [map_zero,coeff_zero,← directionCoeff_coeff,hz n,coeff_zero]
  let n:=Nat.find hex
  have hmin (k :ℕ) (hk :k<n) :directionCoeff α R k=0:= by
    by_contra h
    exact (Nat.not_le_of_lt hk) (Nat.find_min' hex h)
  have hc (k i:ℕ) :
      z2o k ((R.map (seriesLine α)).coeff i) =
        κ ((directionCoeff α R k).coeff i) := by
    simp [seriesLine,directionCoeff_coeff,zQb]
  have hb:N.map (extend.comp j)∣(directionCoeff α R n).map κ:= by
    have h:=reduce_dvd hQ hdiv n (fun i k hk=> by rw [hc,hmin k hk,coeff_zero,map_zero])
    rw [hres] at h
    convert h using 1
    ext i
    by_cases hi:i∈(R.map (seriesLine α)).support
    · calc
        _=z2o n ((R.map (seriesLine α)).coeff i) := by
          rw [hc,coeff_map]
        _ = _:= by simp [zBJ,finsetSum_coeff,coeff_monomial,hi]
    · have hz :=notMem_support_iff.mp hi
      simpa [zBJ,finsetSum_coeff,coeff_monomial,hi,hz] using (hc n i).symm
  have hb' : N.map (MvPolynomial.C.comp j)∣directionCoeff α R n:= by
    apply (map_dvd_map κ (zxb A F) (hN.map _)).mp
    simpa only [map_map,extend,RingHom.comp_assoc] using hb
  obtain ⟨i,hi⟩ : ∃ i,(directionCoeff α R n).coeff i≠0:= by
    by_contra! hz
    exact Nat.find_spec hex (zXJ fun i=>(hz i).trans (coeff_zero i).symm)
  obtain ⟨δ,hδ⟩:=cNx _ hi
  have hm: (directionCoeff α R n).map (chooseDirection δ)=(extract α δ R n).map j:= by
    ext k
    simpa only [coeff_map,extract_coeff,directionCoeff_coeff] using
      congrArg (fun p: (AlgebraicClosure E)[X]=>p.coeff n) (specialize_line α δ (R.coeff k))
  refine ⟨δ,n,?_,(map_dvd_map j (j).injective hN).mp ?_⟩
  · intro hz
    apply hδ
    rw [← coeff_map,hm,hz,zgY,coeff_zero]
  · have hh: (chooseDirection δ).comp (MvPolynomial.C.comp j)=j:= by
      ext x
      simp [chooseDirection]
    simpa only [hm,map_map,hh] using z36 (chooseDirection δ) hb'
end
end qZbPQGe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qZbPQGe
noncomputable section
open Polynomial
open cu (L)
open qZu9hjc (HE Slice atPair)
open q8Z6NHc (jo UniversalValue actualCoeffs Generic genericF genericG)
open scoped Classical
def c1 :Prop :=
  ∀ {E F:Type} [zrb E] [Algebra L E] [zrb F]
    (j:AlgebraicClosure E →+* F) (f :E[X][X]) (s a :ℕ),
    HE f s a → ∀ (T:Slice f s a)
    (u:jo f.natDegree s a →+* zpm F),
    (∀ i,zbO (u (z9v i)) =
      j (algebraMap E (AlgebraicClosure E) (actualCoeffs f T.g i))) →
    aWi zbO (avm u) =
      aWi (j.comp (algebraMap E (AlgebraicClosure E))) f ∧
    ∃ q:Fin T.size→zpm F×zpm F,
      (∀ i,(zbO (q i).1,zbO (q i).2) =
        (j (T.pt i).1,j (T.pt i).2)) ∧
      (∀ i,pairEval (zz4 _) (q i).1 (q i).2 (avm u)=0) ∧
      (∀ i,pairEval (zz4 _) (q i).1 (q i).2 (asa u)=0)
def c2 :Prop :=
  ∀ {d s a :ℕ} {b c:L} (V:UniversalValue d s a b c)
    {F:Type} [zrb F] (k :Generic d s a →+* F) (x y :F),
    atPair k x y (genericF d s a)=0 →
    atPair k x y (genericG d s a)=0 →
    ∃ i,(k (V.pt i).1,k (V.pt i).2)=(x,y)
private theorem map_seriesValue {F D:Type} [zrb F] [zrb D]
  (h:zpm F →+* D) (v w:zpm F) (n:ℕ)
  (hw:zbO w≠0) :
  h (v*w⁻¹^n)=h v/(h w)^n:= by
 have hi:h w⁻¹=(h w)⁻¹:= by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul,mul_comm _ w,PowerSeries.mul_inv_cancel _ hw,map_one]
 rw [map_mul,map_pow,hi,div_eq_mul_inv,inv_pow]
private theorem extend_generic {A D:Type} [za6 A] [IsDomain A] [zrb D] [IsAlgClosed D]
   (v :A →+* D) (hv :zq4 v) :
   ∃ k :AlgebraicClosure (FractionRing A) →+* D,
     k.comp (algebraMap A (AlgebraicClosure (FractionRing A)))=v := by
 let k₀:FractionRing A →+* D:=IsFractionRing.lift hv
 let:Algebra (FractionRing A) D:=k₀.toAlgebra
 let k :AlgebraicClosure (FractionRing A) →ₐ[FractionRing A] D:=IsAlgClosed.lift
 refine ⟨k.toRingHom,RingHom.ext fun z => ?_⟩
 change k (algebraMap A (AlgebraicClosure (FractionRing A)) z)=v z
 rw [zG3 A (FractionRing A) (AlgebraicClosure (FractionRing A)),k.commutes]
 exact IsFractionRing.lift_algebraMap hv z
private theorem subproduct_dvd {S D:Type} [za6 S] [zrb D]
  (ι:S →+* D) (hι:zq4 ι) {m n:ℕ} (l:Fin m ↪ Fin n)
  (w:Fin m→S) (v :Fin n→D) (hw : ∀ i,ι (w i)=v (l i)) (R:S[X]) (c:D)
  (hR:R.map ι=C c * ∏ i,(z7y - C (v i))) :
  (∏ i,(z7y - C (w i)))∣R:= by
 apply (map_dvd_map ι hι (monic_prod_of_monic _ _ fun i _=>monic_X_sub_C (w i))).mp
 rw [hR,zeg]
 simp only [z3A,map_X,map_C,hw]
 apply dvd_mul_of_dvd_right
 let q (i:Fin n) :D[X] :=z7y - C (v i)
 change (∏ i,q (l i)) ∣ ∏ i,q i
 rw [← Finset.prod_map Finset.univ l q]
 exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
private theorem transport_product {A S G D:Type} [za6 A] [za6 S]
  [za6 G] [za6 D] {m:ℕ}
  (u:A →+* S) (ι:S →+* D) (j:A →+* G) (k :G →+* D)
  (hk :k.comp j=ι.comp u) (R:A[X]) (c:G) (v :Fin m→G)
  (hR:R.map j=C c * ∏ i,(z7y - C (v i))) :
  (R.map u).map ι=C (k c) * ∏ i,(z7y - C (k (v i))) := by
 rw [map_map,← hk,← map_map,hR,zNl,zrL,zeg]
 simp only [z3A,Polynomial.map_X,zrL]
private theorem series_factor (bY5:c2)
    {E F:Type} [zrb E] [Algebra L E] [zrb F]
    (j:AlgebraicClosure E →+* F) (f :E[X][X]) (s a :ℕ) (T:Slice f s a)
    (V:UniversalValue f.natDegree s a T.b T.c)
    (u:jo f.natDegree s a →+* zpm F)
    (hu:zq4 u)
    (hc : ∀ z :L,u (znf z) =
      PowerSeries.C (j (algebraMap E (AlgebraicClosure E) (algebraMap L E z))))
    (hred:aWi zbO (avm u) =
      aWi (j.comp (algebraMap E (AlgebraicClosure E))) f)
    (q:Fin T.size→zpm F×zpm F)
    (hq : ∀ i,(zbO (q i).1,zbO (q i).2) =
      (j (T.pt i).1,j (T.pt i).2))
    (hfq : ∀ i,pairEval (zz4 _) (q i).1 (q i).2 (avm u)=0)
    (hgq : ∀ i,pairEval (zz4 _) (q i).1 (q i).2 (asa u)=0) :
    ∃ Q: (zpm F)[X],Q.Monic∧Q∣V.R.map u ∧
      Q.map zbO=T.N.map (j.comp (algebraMap E (AlgebraicClosure E))) := by
  let S:=zpm F
  let B:=FractionRing S
  let D:=AlgebraicClosure B
  let A:=jo f.natDegree s a
  let ι:S →+* D:=(algebraMap B D).comp (algebraMap S B)
  have hι:zq4 ι :=
    (algebraMap B D).injective.comp (zxb S B)
  let v :A →+* D:=ι.comp u
  have hv :zq4 v := fun _ _ h=>hu (hι h)
  obtain ⟨k,hk⟩:=extend_generic v hv
  change k.comp (algebraMap (jo f.natDegree s a) (Generic f.natDegree s a))=ι.comp u at hk
  have hF:aWi ι (avm u)=aWi k (genericF f.natDegree s a) := by
    change aWi ι (shape _)=aWi k (shape _)
    rw [pairMap_shape,pairMap_shape]
    exact congrArg (fun w:A →+* D =>avm w) hk.symm
  have hG:aWi ι (asa u)=aWi k (genericG f.natDegree s a) := by
    change aWi ι (shape _)=aWi k (shape _)
    rw [pairMap_shape,pairMap_shape]
    exact congrArg (fun w:A →+* D =>asa w) hk.symm
  let ct :S →+* F:=zbO
  have hqx i:ct (q i).1=j (T.pt i).1 :=congrArg Prod.fst (hq i)
  have hqy i:ct (q i).2=j (T.pt i).2 :=congrArg Prod.snd (hq i)
  let g i:=u (znf T.b)+u (znf T.c)*(q i).2
  let z i:=pairEval (zz4 _) (q i).1 (q i).2 (avm u).derivative
  let e :=f.natDegree - 2
  let w i:=z i*(g i)⁻¹^e
  have hg i:ct (g i)=j (qZu9hjc.gauge T.b T.c (T.pt i).2) := by
    dsimp only [g]
    rw [map_add,map_mul,hqy,hc,hc]
    dsimp only [ct]
    simp only [qZu9hjc.gauge,map_add,map_mul,
      ← zG3 L E (AlgebraicClosure E)]
    rfl
  have hgne i:ct (g i)≠0:= by
    rw [hg,map_ne_zero_iff _ j.injective]
    exact T.gauge_ne i
  let Q:S[X] := ∏ i,(z7y - C (w i))
  have hQ:Q.Monic:=monic_prod_of_monic _ _ fun i _=>monic_X_sub_C _
  have hpoints (i:Fin T.size) : ∃ l,(k (V.pt l).1,k (V.pt l).2) =
      (ι (q i).1,ι (q i).2) := by
    refine bY5 V k _ _ ?_ ?_
    · change pairEval k _ _ _=0
      have h:=congrArg ι (hfq i)
      rwa [map_pairEval_id,hF,pairEval_map,z70,map_zero] at h
    · change pairEval k _ _ _=0
      have h:=congrArg ι (hgq i)
      rwa [map_pairEval_id,hG,pairEval_map,z70,map_zero] at h
  choose l hl using hpoints
  have hli:zq4 l:= by
    intro i m h
    have hm:=(hl i).symm.trans (h ▸ hl m)
    apply T.distinct
    exact Prod.ext
      (j.injective ((hqx i).symm.trans ((congrArg ct (hι (congrArg Prod.fst hm))).trans (hqx m))))
      (j.injective ((hqy i).symm.trans ((congrArg ct (hι (congrArg Prod.snd hm))).trans (hqy m))))
  let val (i:Fin V.size) :=
    atPair (zz4 _) (V.pt i).1 (V.pt i).2 (genericF f.natDegree s a).derivative /
      qZu9hjc.gauge T.b T.c (V.pt i).2^e
  have hconst (b:L) :k (algebraMap L (Generic f.natDegree s a) b)=ι (u (znf b)) :=
    RingHom.congr_fun hk (znf b)
  refine ⟨Q,hQ,subproduct_dvd ι hι ⟨l,hli⟩ w (k ∘ val) ?_ _ (k V.scalar) ?_,?_⟩
  · intro i
    have hx :k (V.pt (l i)).1=ι (q i).1 :=congrArg Prod.fst (hl i)
    have hy :k (V.pt (l i)).2=ι (q i).2 :=congrArg Prod.snd (hl i)
    have hfD:aWi ι (avm u).derivative =
        aWi k (genericF f.natDegree s a).derivative := by
      simpa only [aWi,derivative_map] using congrArg zst hF
    have hz :ι (z i)=k (atPair (zz4 _) (V.pt (l i)).1 (V.pt (l i)).2
        (genericF f.natDegree s a).derivative) := by
      change ι (pairEval (zz4 _) _ _ _)=k (pairEval (zz4 _) _ _ _)
      simp only [map_pairEval_id,hfD,hx,hy]
    change ι (w i)=k (val (l i))
    dsimp only [w,val]
    rw [map_seriesValue ι _ _ _ (hgne i),map_div₀,map_pow,hz]
    simp only [qZu9hjc.gauge,map_add,map_mul,hconst,hy,g]
    rfl
  · exact transport_product u ι _ k hk V.R V.scalar val V.product
  · have h:=congrArg (Polynomial.map j) T.product
    rw [map_map,zeg] at h
    rw [h]
    simp only [Q,zeg,z3A,Polynomial.map_X,zrL]
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (fun x :F=>z7y - C x)
    change ct (w i)=j _
    dsimp only [w]
    rw [map_seriesValue ct _ _ _ (hgne i),hg,map_div₀,map_pow]
    have hfd:aWi ct (avm u).derivative =
        aWi (j.comp (algebraMap E (AlgebraicClosure E))) f.derivative := by
      simpa only [ct,aWi,derivative_map] using congrArg zst hred
    change ct (pairEval (zz4 _) _ _ _)/_=j (pairEval (algebraMap E _) _ _ _)/_
    rw [map_pairEval_id ct,hfd,pairEval_map,z70]
    rw [map_pairEval,hqx,hqy]
theorem of_children (lift:c1) (norm:c2) :q8Z6NHc.c3:= by
 intro E _ _ f s a _ _ _ hf T V
 let α:=actualCoeffs (d:=f.natDegree) (s :=s) (a :=a) f T.g
 let j:=extend (E :=E) (d:=f.natDegree) (s :=s) (a :=a)
 let u:=seriesLine α
 obtain ⟨hred,q,hq,hfq,hgq⟩:=lift j f s a hf T u (seriesLine_residue α)
 obtain ⟨Q,hQ,hd,hr⟩:=series_factor norm j f s a T V u (seriesLine_injective α)
   (seriesLine_C α) hred q hq hfq hgq
 have hR:V.R≠0:= by
   intro hz
   have h:=V.product
   rw [hz,zgY] at h
   exact (mul_ne_zero (C_ne_zero.mpr V.scalar_ne)
     (Finset.prod_ne_zero_iff.mpr fun _ _=>X_sub_C_ne_zero _)) h.symm
 exact line_extract α hR T.monic hQ hd hr
end
end qZbPQGe
end
section
namespace qFwMjQd
noncomputable section
open cu (L)
open P5 (p)
open qZu9hjc (gauge)
open q8Z6NHc (UniversalValue rawDegree boundary)
def c1 :Prop :=
  ∀ {E :Type} [zrb E] [IsAlgClosed E] (d s a :ℕ),2≤d→d*s≤a →
    ∀ (f :LineData E d s a) (g:LineData E d s (a+s+1))
      (h:LineData E (d-1) s (a-s)) (A B:Finset (aax E)),
      (∀ q∈A,simple (bY false f) (bY false g) (bY false h) q) →
      (∀ q∈B,q 1=0∧simple (bY true f) (bY true g) (bY true h) q) →
      (A.card:ℤ)+B.card≤ rawDegree d a s
def c2 :Prop :=
  ∀ (d s a :ℕ) (hd:2≤d),d<p → ∀ ha :d*s≤a,
    ∀ (b c:L),c≠0 →
      let h:=hLine d s a hd (weight_base hd ha) b c
      ∃ B:Finset (aax (Eline d s a)),
        (∀ q∈B,q 1=0 ∧
          simple (bY true (fLine d s a)) (bY true (gLine d s a)) (bY true h) q) ∧
        boundary d a s≤(B.card:ℤ)
def c3:Prop :=
  ∀ (d s a :ℕ) (hd:2≤d),d<p → ∀ ha :d*s≤a,
    ∀ (b c:L),c≠0 → ∀ V:UniversalValue d s a b c,
      let h:=hLine d s a hd (weight_base hd ha) b c
      ∃ A:Finset (aax (Eline d s a)),
        (∀ q∈A,simple (bY false (fLine d s a)) (bY false (gLine d s a))
          (bY false h) q∧gauge b c (q 1)≠0) ∧
        (aOw V.R).natDegree≤A.card
theorem of_children (bound:c1) (Zq:c2) (sW:c3) :q8Z6NHc.c2 := by
 intro d s a hd hp ha b c hc V i
 obtain ⟨B,hB,hb⟩:=Zq d s a hd hp ha b c hc
 obtain ⟨A,hA,hdeg⟩:=sW d s a hd hp ha b c hc V
 have hraw:=bound d s a hd ha (fLine d s a) (gLine d s a)
  (hLine d s a hd (weight_base hd ha) b c) A B (fun q hq=>(hA q hq).1) hB
 have hi:=(coefficient_le_line_degree V.R i).trans hdeg
 exact le_sub_iff_add_le.mpr ((add_le_add (Int.ofNat_le.mpr hi) hb).trans hraw)
end
end qFwMjQd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qs5yTLd
noncomputable section
open Polynomial
open qZu9hjc (HE atPair jacobian)
open q8Z6NHc (Slot)
open qZbPQGe
private theorem shape_actual {E :Type} [zrb E] {d s a :ℕ} (f :E[X][X])
    (hd:f.natDegree≤d) (hw:HE f s a) :
    shape (fun k :Slot d s a=>(f.coeff k.val.1.val).coeff k.val.2.val)=f := by
  classical
  apply zXJ fun i=>zXJ fun j => ?_
  rw [shape,finsetSum_coeff,finsetSum_coeff]
  have term (k :Slot d s a) :
      ((monomial k.val.1.val (monomial k.val.2.val
        ((f.coeff k.val.1.val).coeff k.val.2.val))).coeff i).coeff j =
        if k.val.1.val=i∧k.val.2.val=j then (f.coeff i).coeff j else 0:= by
    by_cases hi:k.val.1.val=i <;> by_cases hj:k.val.2.val=j <;>
      simp [coeff_monomial,hi,hj]
  simp only [term]
  by_cases hc: (f.coeff i).coeff j=0
  · simp [hc]
  have hfi:f.coeff i≠0:= fun h=>hc (by rw [h,coeff_zero])
  have hi:=(le_natDegree_of_ne_zero hfi).trans hd
  have hj:=le_natDegree_of_ne_zero hc
  have hw' := hw i hfi
  let k :Slot d s a :=⟨(⟨i,by omega⟩,⟨j,by omega⟩),by
    change j+i*s≤a
    omega⟩
  rw [zi6 k]
  · simp [k]
  · intro l _ hl
    apply ite_eq_right
    rintro ⟨h₁,h₂⟩
    exact hl (Subtype.ext (Prod.ext (Fin.ext h₁) (Fin.ext h₂)))
  · simp
private theorem residues {E F:Type} [zrb E] [zrb F] {d s a :ℕ}
  (k :E →+* F) (f :E[X][X]) (hd:f.natDegree≤d) (hw:HE f s a)
  (v :Slot d s a→zpm F)
  (hv : ∀ i,zbO (v i)=k ((f.coeff i.val.1.val).coeff i.val.2.val)) :
  aWi zbO (shape v)=aWi k f := by
 rw [pairMap_shape,← shape_actual f hd hw,pairMap_shape]
 exact congrArg shape (funext hv)
private theorem at_image {E G F:Type} [zrb E] [zrb G] [zrb F]
  (e :E →+* G) (j:G →+* F) (f :E[X][X]) (x y :G) :
  (aWi (j.comp e) f).evalEval (j x) (j y)=j (atPair e x y f) := by
 change _=j (pairEval e x y f)
 rw [map_pairEval]
 exact (eval₂_eval₂RingHom_apply _ _ _ _).symm
theorem proof :qZbPQGe.c1 := by
  intro E F _ _ _ j f s a hf T u hu
  let e :=algebraMap E (AlgebraicClosure E)
  let k :=j.comp e
  have hf' : aWi zbO (avm u)=aWi k f :=
    residues k f le_rfl hf _ (fun i=>hu (.inl i))
  have hg' : aWi zbO (asa u)=aWi k T.g :=
    residues k T.g T.degree T.weight _ (fun i=>hu (.inr i))
  refine ⟨hf',?_⟩
  change (avm u).map (mapRingHom zbO)=f.map (mapRingHom k) at hf'
  change (asa u).map (mapRingHom zbO)=T.g.map (mapRingHom k) at hg'
  have dR (i:Fin T.size) :
      ∃ z :zpm F×zpm F,
        (zbO z.1,zbO z.2) =
          (j (T.pt i).1,j (T.pt i).2) ∧
        pairEval (zz4 _) z.1 z.2 (avm u)=0 ∧
        pairEval (zz4 _) z.1 z.2 (asa u)=0:= by
    have hzF:=at_image e j f (T.pt i).1 (T.pt i).2
    have hzG:=at_image e j T.g (T.pt i).1 (T.pt i).2
    rw [T.f_zero i,map_zero] at hzF
    rw [T.g_zero i,map_zero] at hzG
    have heval (p:E[X][X]) :
        (p.map (mapRingHom k)).evalEval (j (T.pt i).1) (j (T.pt i).2) =
          j (atPair e (T.pt i).1 (T.pt i).2 p) :=
      at_image e j p (T.pt i).1 (T.pt i).2
    have hd:det (aWi k f) (aWi k T.g) (j (T.pt i).1) (j (T.pt i).2)≠0:= by
      have he :det (aWi k f) (aWi k T.g) (j (T.pt i).1) (j (T.pt i).2) =
          j (jacobian e (T.pt i).1 (T.pt i).2 f T.g) := by
        simp only [det,aWi,dx_map,derivative_map,heval,jacobian,map_sub,map_mul]
        rfl
      rw [he,map_ne_zero_iff _ j.injective]
      exact T.simple i
    obtain ⟨z,h₀,h₁,h₂⟩:=aOv (avm u) (asa u)
      (j (T.pt i).1) (j (T.pt i).2)
      (by rw [hf']; exact hzF) (by rw [hg']; exact hzG) (by rw [hf',hg']; exact hd)
    refine ⟨z,h₀,?_,?_⟩
    · change eval₂ (evalRingHom z.1) z.2 (avm u)=0
      rwa [eval₂_evalRingHom]
    · change eval₂ (evalRingHom z.1) z.2 (asa u)=0
      rwa [eval₂_evalRingHom]
  choose z hz using dR
  exact ⟨z,fun i=>(hz i).1,fun i=>(hz i).2.1,fun i=>(hz i).2.2⟩
end
end qs5yTLd
end
section
namespace qdRD8me
open Polynomial
open qZu9hjc (atPair)
open q8Z6NHc (Generic genericF genericG)
open qZbPQGe (pairEval map_pairEval)
open scoped BigOperators
private theorem finite_roots {E F σ:Type} [zrb E] [IsAlgClosed E] [zrb F] [Finite σ]
   {n:ℕ} (k :E →+* F) (pt:Fin n→σ→E) (f g:z3y σ E)
   (cover : ∀ u:σ→E,zIe u f=0→zIe u g=0 →
     ∃ i,pt i=u)
   (z :σ→F) (hf :zOD k z f=0)
   (hg:zOD k z g=0) :
   ∃ i,(fun a=>k (pt i a))=z := by
 classical
 let I:Ideal (z3y σ E) :=Ideal.span {f,g}
 let ev :=zOD k z
 have hI:I≤RingHom.ker ev := by
   change Ideal.span {f,g} ≤ _
   rw [Ideal.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
   exact ⟨hf,hg⟩
 have hcoord (a :σ) : ∃ c:E,k c=z a := by
   let q:z3y σ E := ∏ i,(z9v a-MvPolynomial.C (pt i a))
   have hrad:q∈I.radical:= by
     rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K:=E)]
     intro u hu
     have hfu:=hu f (zCn (by simp))
     have hgu:=hu g (zCn (by simp))
     obtain ⟨i,rfl⟩:=cover u hfu hgu
     change zIe (pt i) q=0
     simp only [q,map_prod]
     exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
   obtain ⟨m,hm⟩:=Ideal.mem_radical_iff.mp hrad
   have hpow:ev (q^m)=0:=hI hm
   rw [map_pow] at hpow
   have hq:zOD k z q=0:=eq_zero_of_pow_eq_zero hpow
   simp only [q,map_prod,map_sub,zrD,zTv] at hq
   obtain ⟨i,-,hi⟩:=Finset.prod_eq_zero_iff.mp hq
   exact ⟨pt i a,(sub_eq_zero.mp hi).symm⟩
 choose w hw using hcoord
 have hz : (fun a=>k (w a))=z :=funext hw
 have hzero {p:z3y σ E} (hp:ev p=0) :zIe w p=0:= by
   apply k.injective
   rwa [zfM,zCp,MvPolynomial.map_eval₂Hom,
     RingHom.comp_id,hz,map_zero]
 obtain ⟨i,hi⟩:=cover w (hzero hf) (hzero hg)
 exact ⟨i,by rw [hi]; exact hz⟩
private noncomputable def flatten {E :Type} [zrb E] (f :E[X][X]) :z3y Bool E :=
 pairEval znf (z9v false) (z9v true) f
private theorem alU {E F:Type} [zrb E] [zrb F] (k :E →+* F)
  (u:Bool→F) (f :E[X][X]) :
  zOD k u (flatten f)=atPair k (u false) (u true) f := by
 rw [flatten,map_pairEval]
 have hk : (zOD k u).comp znf=k := by
  apply RingHom.ext
  intro a
  exact zTv k u a
 rw [hk,zrD,zrD]
 rfl
private def coords {E :Type} (x y :E) (a :Bool) :E :=if a then y else x
theorem proof :qZbPQGe.c2 := by
 intro d s a b c V F _ k x y hf hg
 let pts (i:Fin V.size) :=coords (V.pt i).1 (V.pt i).2
 let f :=flatten (genericF d s a)
 let g:=flatten (genericG d s a)
 have cover (u:Bool→Generic d s a) (hfu:zIe u f=0)
     (hgu:zIe u g=0) : ∃ i,pts i=u:= by
   simp only [f,g,zfM,zCp,
     alU] at hfu hgu
   obtain ⟨i,hi⟩:=V.all_roots (u false) (u true) hfu hgu
   exact ⟨i,funext fun j=> by cases j <;> simp [pts,hi,coords]⟩
 obtain ⟨i,hi⟩:=finite_roots k pts f g cover (coords x y)
   (by simpa [f,alU,coords] using hf)
   (by simpa [g,alU,coords] using hg)
 exact ⟨i,Prod.ext (congrFun hi false) (congrFun hi true)⟩
end qdRD8me
end
end
section
section
namespace q9sUlTb
noncomputable section
open qFwMjQd (LineData Chart aax)
open MvPolynomial
variable {R S E :Type} [za6 R] [za6 S]
def fullChart {d s a :ℕ} (rx ry rz :Bool) (f :LineData R d s a) :Chart R :=
  ∑ i,(C (if rz then (f i).2 else (f i).1)+C (if rz then (f i).1 else (f i).2)*z9v 2) *
    z9v 0^(if rx then a - i.val.1.val*s - i.val.2.val else i.val.2.val) *
    z9v 1^(if ry then d - i.val.1.val else i.val.1.val)
def push {d s a :ℕ} (k :R →+* S) (f :LineData R d s a) :LineData S d s a :=
 fun i=>(k (f i).1,k (f i).2)
theorem b8A {d s a :ℕ} (k :R →+* S) (x y z :Bool) (f :LineData R d s a) :
  map k (fullChart x y z f)=fullChart x y z (push k f) := by
 cases z <;> simp only [fullChart,Bool.false_eq_true,ite_false,ite_true,
  map_sum,map_mul,map_add,map_pow,map_C,map_X,push]
def zeroAt (f g h:Chart R) (q:aax R) :Prop :=
 eval q f=0∧eval q g=0∧eval q h=0
theorem zeroAt_map (k :R →+* S) {f g h:Chart R} {q:aax R}
  (hz :zeroAt f g h q) :zeroAt (map k f) (map k g) (map k h) (k ∘ q) := by
 rcases hz with ⟨hf,hg,hh⟩
 simp only [zeroAt,← map_eval,hf,hg,hh,map_zero,and_self]
def noBoundary {d s a :ℕ} (f :LineData R d s a) (g:LineData R d s (a+s+1))
    (h:LineData R (d-1) s (a-s)) :Prop :=
  ∀ x y z (q:aax R),
    zeroAt (fullChart x y z f) (fullChart x y z g) (fullChart x y z h) q →
    (x=true→q 0≠0)∧(y=true→q 1≠0)∧(z=true→q 2≠0)
def samePoint (rev :Bool) (u v :aax R) :Prop :=
 u 0=v 0∧u 2=v 2∧if rev then u 1*v 1=1 else u 1=v 1
variable [zrb E]
def mix {d s a :ℕ} (k :E →+* R) (t:R) (f g:LineData E d s a) :LineData R d s a :=
  fun i=>(k (f i).1+t*(k (g i).1 - k (f i).1),
    k (f i).2+t*(k (g i).2 - k (f i).2))
theorem push_mix {d s a :ℕ} (m:R →+* S) (k :E →+* R) (t:R) (f g:LineData E d s a) :
  push m (mix k t f g)=mix (m.comp k) (m t) f g:= by
 ext i <;> simp [push,mix]
@[simp] theorem mix_zero {d s a :ℕ} (k :E →+* R) (f g:LineData E d s a) :
   mix k 0 f g=push k f := by
  ext i <;> simp [mix,push]
@[simp] theorem mix_one {d s a :ℕ} (k :E →+* R) (f g:LineData E d s a) :
   mix k 1 f g=push k g:= by
  ext i <;> simp [mix,push]
@[simp] theorem push_id {d s a :ℕ} (f :LineData E d s a) :push (zz4 E) f=f :=rfl
end
end q9sUlTb
end
section
namespace qRIxBbd
noncomputable section
open Polynomial
open q8Z6NHc (Slot)
variable {R S:Type} [za6 R] [za6 S] {d s a :ℕ}
def cV (k :ℕ) (f :Slot d s a→R) :R[X] :=
 ∑ i,if i.val.1.val=k then monomial i.val.2.val (f i) else 0
def bwE {k j:ℕ} (hk :k≤d) (hj:j+k*s≤a) :Slot d s a :=
 ⟨(⟨k,by omega⟩,⟨j,by omega⟩),hj⟩
theorem grade_coeff (k :ℕ) (f :Slot d s a→R) (hk :k≤d) (j:ℕ) :
    (cV k f).coeff j=if hj:j+k*s≤a then f (bwE hk hj) else 0:= by
  classical
  rw [cV,finsetSum_coeff]
  by_cases hj:j+k*s≤a
  · rw [dite_eq_left hj,zi6 (bwE hk hj)]
    · simp [bwE]
    · intro i _ hi
      split_ifs with h
      · rw [coeff_monomial]
        split_ifs with h'
        · exact (hi (by
            apply Subtype.ext
            exact Prod.ext (Fin.ext h) (Fin.ext h'))).elim
        · rfl
      · simp
    · simp
  · rw [dite_eq_right hj]
    apply zYF
    intro i _
    split_ifs with h
    · rw [coeff_monomial]
      split_ifs with h'
      · exact (hj (by simpa [h,h'] using i.property)).elim
      · rfl
    · simp
theorem grade_degree (k :ℕ) (f :Slot d s a→R) (hk :k≤d) :
  (cV k f).natDegree≤a-k*s := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [grade_coeff k f hk,dite_eq_right (by omega)]
theorem grade_map (φ:R →+* S) (k :ℕ) (f :Slot d s a→R) :
  (cV k f).map φ=cV k (φ ∘ f) := by
 classical
 rw [cV,zWe,cV]
 apply Finset.sum_congr rfl
 intro i _
 split_ifs <;> simp [Function.comp_apply]
theorem grade_fill {k l:ℕ} (hk :k≤d) (ha :k*s≤a) (P:R[X])
   (hP:P.natDegree≤a-k*s) :
   cV l (fun i:Slot d s a=>if i.val.1.val=k then P.coeff i.val.2.val else 0) =
     if l=k then P else 0:= by
 classical
 by_cases h:l=k
 · subst l
   rw [ite_eq_left rfl]
   ext j
   rw [grade_coeff k _ hk]
   by_cases hj:j+k*s≤a
   · simp [hj,bwE]
   · rw [dite_eq_right hj,coeff_eq_zero_of_natDegree_lt (show P.natDegree<j by omega)]
 · rw [ite_eq_right h,cV]
   apply zYF
   intro i _
   by_cases hi:i.val.1.val=l
   · simp [hi,h]
   · simp [hi]
end
end qRIxBbd
end
section
namespace q33Mraa
noncomputable section
open cu (L)
open Polynomial
open q8Z6NHc (jo Generic Index UniversalValue)
open qG7TGJa (value)
open qFwMjQd (aax Eline lineVar onLine)
variable {d s a :ℕ}
def Lw (i:Index d s a) :Generic d s a :=
 algebraMap (jo d s a) (Generic d s a) (z9v i)
def Yn (i:Index d s a) :Eline d s a :=lineVar (some (false,i))
def slope (i:Index d s a) :Eline d s a :=lineVar (some (true,i))
def target (d s a :ℕ) :Eline d s a :=lineVar (σ:=Index d s a) none
structure Frame (d s a :ℕ) (z :Eline d s a) where
 emb:Generic d s a →ₐ[L] Eline d s a
 coeff_eq : ∀ i,emb (Lw i)=Yn i+slope i*z
 independent:zq4 (zOD emb.toRingHom slope)
def scaleSlope (i:Index d s a) :Generic d s a :=
 match i with
 | .inl _=>Lw i
 | .inr _=>0
def scaleLine (r : (jo d s a)[X]) (t:Generic d s a) : (Generic d s a)[X] :=
 onLine (algebraMap L _) Lw scaleSlope t r
abbrev pointValue {b c:L} (V:UniversalValue d s a b c) (i:Fin V.size) :
 Generic d s a :=value b c (V.pt i)
def linePoint {b c:L} (V:UniversalValue d s a b c) {z :Eline d s a}
    (J:Frame d s a z) (i:Fin V.size) :aax (Eline d s a) :=
  ![J.emb (V.pt i).1,J.emb (V.pt i).2,z]
end
end q33Mraa
end
section
set_option backward.isDefEq.respectTransparency false
namespace q33Mraa
noncomputable section
open Polynomial
open cu (L)
open q8Z6NHc (jo Generic Index)
open qFwMjQd (Eline onLine aOw)
open private map_onLine from ProximityPrize.SubmissionLower.ZusnbBc
private theorem shift {R σ F:Type} [za6 R] [za6 F] (k :R →+* F)
    (u v :σ→F) (t z :F) (r : (z3y σ R)[X]) :
    (onLine k u v t r).comp (z7y+C z) =
      onLine k (fun i=>u i+v i*z) v t r := by
  change ((compRingHom (z7y+C z)).comp (onLine k u v t)) r= _
  apply zmU
  apply z86
  · intro f
    simp only [zQb,coe_compRingHom_apply,onLine,coe_eval₂RingHom,eval₂_C]
    change ((compRingHom (z7y+C z)).comp (zOD (C.comp k)
      (fun i=>C (u i)+C (v i)*z7y))) f= _
    apply zmU
    apply zXT
    · intro x
      simp
    · intro i
      simp only [zQb,zrD,coe_compRingHom_apply,
        C_comp,X_comp,map_add,map_mul]
      ring
  · simp [onLine]
theorem line_multiplicity_le {d s a :ℕ} (R: (jo d s a)[X]) {z :Eline d s a}
    (J:Frame d s a z) (t:Generic d s a) (ht:J.emb t=target d s a)
    (hn:scaleLine R t≠0) :
    rootMultiplicity z (aOw R)≤ rootMultiplicity 0 (scaleLine R t) := by
  let F:=Generic d s a
  let W:=z3y (Index d s a) F
  let k :L →+* W:=MvPolynomial.C.comp (algebraMap L F)
  let u (i:Index d s a) :W:=znf (Lw i)
  let P:=onLine k u z9v (znf t) R
  let φ:W →+* Eline d s a :=zOD J.emb.toRingHom slope
  let ψ:W →+* F:=zOD (zz4 F) scaleSlope
  have hφ: (P.map φ)=(aOw R).comp (z7y+C z) := by
    have hk :φ.comp k=algebraMap L (Eline d s a) := by
      ext x
      exact (zTv J.emb.toRingHom slope (algebraMap L F x)).trans
        (J.emb.commutes x)
    have hu:φ ∘ u=fun i=>Yn i+slope i*z := by
      funext i
      exact (zTv J.emb.toRingHom slope (Lw i)).trans (J.coeff_eq i)
    have hv :φ ∘ (z9v:Index d s a→W)=slope := by
      funext i
      exact zrD _ _ i
    have hT:φ (znf t)=target d s a :=
      (zTv _ _ _).trans ht
    rw [show P=onLine k u z9v (znf t) R from rfl,map_onLine,
      aOw,shift,hk,hu,hv,hT]
    rfl
  have hψ:P.map ψ=scaleLine R t:= by
    have hk :ψ.comp k=algebraMap L F:= by
      ext x
      exact zTv (zz4 F) scaleSlope (algebraMap L F x)
    have hu:ψ ∘ u=Lw:= by
      funext i
      exact zTv (zz4 F) scaleSlope (Lw i)
    have hv :ψ ∘ (z9v:Index d s a→W)=scaleSlope := by
      funext i
      exact zrD _ _ i
    have hT:ψ (znf t)=t:=zTv _ _ _
    rw [show P=onLine k u z9v (znf t) R from rfl,map_onLine,
      scaleLine,hk,hu,hv,hT]
  have h:=eq_rootMultiplicity_map (f :=φ) (p:=P) J.independent 0
  change rootMultiplicity 0 P=rootMultiplicity (φ 0) (P.map φ) at h
  rw [map_zero,hφ,← rootMultiplicity_eq_rootMultiplicity] at h
  have hh:=le_rootMultiplicity_map (f :=ψ) (p:=P) (hψ.trans_ne hn) 0
  rw [h,map_zero,hψ] at hh
  exact hh
end
end q33Mraa
end
section
set_option backward.isDefEq.respectTransparency false
namespace q33Mraa
noncomputable section
open Polynomial
open scoped Classical
open cu (L)
open P5 (p)
open qZu9hjc (gauge)
open q8Z6NHc (jo Generic UniversalValue)
open qFwMjQd
def c1 :Prop :=
  ∀ {d s a :ℕ} (R: (jo d s a)[X]),R.IsPrimitive →
    ∀ z∈(aOw R).roots,Nonempty (Frame d s a z)
def c2 :Prop :=
  ∀ {d s a :ℕ} {b c:L} (V:UniversalValue d s a b c) (t:Generic d s a),
    t≠0→scaleLine V.R t≠0 ∧
    rootMultiplicity 0 (scaleLine V.R t) =
      rootMultiplicity t (V.R.map (algebraMap (jo d s a) (Generic d s a)))
def c3:Prop :=
  ∀ {d s a :ℕ} (hd:2≤d),d<p → ∀ ha :d*s≤a,
    ∀ {b c:L},c≠0 → ∀ (V:UniversalValue d s a b c) {z :Eline d s a}
      (J:Frame d s a z) (i:Fin V.size),J.emb (pointValue V i)=target d s a →
      let q:=linePoint V J i
      simple (bY false (fLine d s a)) (bY false (gLine d s a))
        (bY false (hLine d s a hd (weight_base hd ha) b c)) q∧gauge b c (q 1)≠0
variable {d s a :ℕ} {b c:L}
private theorem target_ne :target d s a≠0:= by
 let B:=LineRing (q8Z6NHc.Index d s a)
 let E :=Eline d s a
 have h:zq4 (algebraMap B E) := by
  rw [zYY B (FractionRing B) E]
  exact (algebraMap (FractionRing B) E).injective.comp (zxb B _)
 exact (map_ne_zero_iff _ h).2 (MvPolynomial.X_ne_zero none)
private theorem bdm {z :Eline d s a} (J:Frame d s a z)
    (R: (jo d s a)[X]) :
    (aOw R).eval z =
      (R.map ((J.emb.toRingHom).comp (algebraMap (jo d s a) (Generic d s a)))).eval
        (target d s a) := by
  let k :=algebraMap (jo d s a) (Generic d s a)
  let E :=Eline d s a
  change ((evalRingHom z).comp (onLine (algebraMap L E) Yn slope (target d s a))) R =
    ((evalRingHom (target d s a)).comp (mapRingHom (J.emb.toRingHom.comp k))) R
  apply zmU
  apply z86
  · intro f
    simp only [zQb,coe_evalRingHom,onLine,coe_eval₂RingHom,
      eval₂_C,coe_mapRingHom,map_C,eval_C]
    change ((evalRingHom z).comp (zOD (C.comp (algebraMap L E))
      (fun j=>C (Yn j)+C (slope j)*z7y))) f=(J.emb.toRingHom.comp k) f
    apply zmU
    apply zXT
    · intro u
      simp only [zQb,zTv,coe_evalRingHom,eval_C]
      change algebraMap L E u=J.emb ((k.comp znf) u)
      rw [show k.comp znf=algebraMap L (Generic d s a) from
        (zYY L (jo d s a) (Generic d s a)).symm]
      exact (J.emb.commutes u).symm
    · intro i
      simpa only [zQb,zrD,coe_evalRingHom,eval_add,
        eval_mul,eval_C,eval_X,← J.coeff_eq i] using
        (show J.emb (Lw i)=J.emb.toRingHom (k (z9v i)) from rfl)
  · simp [onLine]
private theorem product_roots {F:Type} [zrb F] (n:ℕ) (v :Fin n→F) (r :F)
  (hr :r≠0) :
  (C r * ∏ i,(z7y - C (v i))).roots=(Finset.univ :Finset (Fin n)).val.map v := by
 rw [roots_C_mul _ hr,Finset.prod_eq_multiset_prod]
 rw [show (fun i=>z7y - C (v i))=(fun q=>z7y - C q) ∘ v from rfl,
  ← Multiset.map_map]
 exact roots_multiset_prod_X_sub_C (Finset.univ.val.map v)
private theorem root_count {F:Type} [zrb F] (n:ℕ) (v :Fin n→F) (t r :F)
   (hr :r≠0) :
   rootMultiplicity t (C r * ∏ i,(z7y - C (v i))) =
     (Finset.univ.filter (fun i=>v i=t)).card:= by
 classical
 rw [← count_roots,product_roots _ _ _ hr,Multiset.count_map]
 simp only [← Finset.filter_val,Finset.card,eq_comm (a :=t)]
private theorem specialized_product {z :Eline d s a} (J:Frame d s a z)
   (V:UniversalValue d s a b c) :
   V.R.map (J.emb.toRingHom.comp (algebraMap (jo d s a) (Generic d s a))) =
     C (J.emb V.scalar) * ∏ i,(z7y - C (J.emb (pointValue V i))) := by
 have h:=V.product
 change _=C V.scalar * ∏ i:Fin V.size,(z7y - C (pointValue V i)) at h
 rw [← map_map,h,zNl,zeg]
 simp only [z3A,map_X,map_C]
 rfl
theorem of_children (frames :c1) (scaling:c2) (points :c3) :
    qFwMjQd.c3:= by
  classical
  intro d s a hd hp ha b c hc V
  let P:=aOw V.R
  let S:=P.roots.toFinset
  let J (z :Eline d s a) (hz :z∈S) :Frame d s a z :=
    Classical.choice (frames V.R V.primitive z (Multiset.mem_toFinset.mp hz))
  let lg (z : {z // z∈S}) :Finset (Fin V.size) :=
    Finset.univ.filter fun i=>(J z.val z.prop).emb (pointValue V i)=target d s a
  let U:=S.attach.sigma lg
  let Q (j:Σ _ : {z // z∈S},Fin V.size) :aax (Eline d s a) :=
    linePoint V (J j.1.val j.1.prop) j.2
  have hQ:zq4 Q:= by
    intro j j' h
    have hz :j.1=j'.1 :=Subtype.ext (congrFun h 2)
    obtain ⟨⟨z,hzmem⟩,i⟩:=j
    obtain ⟨⟨z',hzmem'⟩,i'⟩:=j'
    have hs :z=z' := congrArg Subtype.val hz
    subst z'
    have hi:=V.distinct (Prod.ext ((J z hzmem).emb.injective (congrFun h 0))
      ((J z hzmem).emb.injective (congrFun h 1)))
    change i=i' at hi
    subst i'
    rfl
  refine ⟨U.image Q,?_,?_⟩
  · intro q hq
    obtain ⟨⟨z,i⟩,hzi,rfl⟩:=Finset.mem_image.mp hq
    exact points hd hp ha hc V (J z.val z.prop) i (Finset.mem_filter.mp (Finset.mem_sigma.mp hzi).2).2
  · rw [Finset.card_image_of_injective _ hQ,Finset.card_sigma,← IsAlgClosed.card_roots_eq_natDegree,
      ← Multiset.toFinset_sum_count_eq,← Finset.sum_attach S]
    apply Finset.sum_le_sum
    intro z _
    let B:=J z.val z.prop
    have hz :=isRoot_of_mem_roots (Multiset.mem_toFinset.mp z.prop)
    have he :=bdm B V.R
    rw [show (aOw V.R).eval z.val=0 from hz,specialized_product B V] at he
    have hpoly : (C (B.emb V.scalar) *
        ∏ i,(z7y - C (B.emb (pointValue V i)))).eval (target d s a)=0:=he.symm
    simp only [eval_mul,eval_C,eval_prod,eval_sub,eval_X] at hpoly
    have hscalar :B.emb V.scalar≠0:=(map_ne_zero_iff _ B.emb.injective).2 V.scalar_ne
    obtain ⟨i,_,hi⟩:=Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hpoly).resolve_left hscalar)
    have ht:B.emb (pointValue V i)=target d s a :=(sub_eq_zero.mp hi).symm
    have ht0:pointValue V i≠0:= fun h=>target_ne (ht.symm.trans (by rw [h,map_zero]))
    obtain ⟨hn,hs⟩:=scaling V (pointValue V i) ht0
    have hm:=line_multiplicity_le V.R B (pointValue V i) ht hn
    rw [hs,eq_rootMultiplicity_map B.emb.injective (pointValue V i),map_map,specialized_product B V] at hm
    change _≤ rootMultiplicity (B.emb (pointValue V i)) _ at hm
    rw [ht,root_count V.size (fun i=>B.emb (pointValue V i)) _ _ hscalar] at hm
    rw [count_roots]
    exact hm
end
end q33Mraa
end
end
