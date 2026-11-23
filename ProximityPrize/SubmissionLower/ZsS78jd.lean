import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.ZMyjDge
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace qvWbALd
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open Cu
open quN7Z4a (Sheet)
open qBajpRb (CurveRing yq)
open qRoCwuc (genericDisc ConstantOddPart goodMarks)
open E7 (CurveField CurvePlace axV poleOrder KB Tq Gb)
open agN (b27)
open private common_divisor from ProximityPrize.SubmissionLower.ZjpV9lc
open private good_subset from ProximityPrize.SubmissionLower.ZXGF8Ec
open scoped WithZero BigOperators
variable {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
private theorem residue_surj (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S) (γ:T) :
  Function.Surjective (M.residue γ) := by
 intro r
 refine ⟨M.lift γ (algebraMap L (CurveRing S.bY) r),?_⟩
 exact (RingHom.congr_fun (M.cqr γ) _).trans ((yq ..).commutes r)
private theorem local_rank_loss (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S)
   {Q G: (oO C₀)[X]} (hq:Q.Monic)
   (he :genericDisc S= Q^2*G) (hl:G.leadingCoeff=(genericDisc S).leadingCoeff)
   (hm:0<G.natDegree) (hR:G.resultant G.derivative≠0) {γ:K} (hγ:γ∈goodMarks S) :
   ∃ d:ℕ,2*d=G.natDegree ∧
     d≤KB (M.place ⟨γ,good_subset S hγ⟩).value (G.resultant G.derivative) := by
 classical
 let γ' : T:=⟨γ,good_subset S hγ⟩
 let v :=(M.place γ').value
 let A:=v.valuationSubring
 let ι:A →+* oO C₀:=A.toSubring.subtype
 let ρ:=M.residue γ'
 let D:=localDisc S M γ'
 have hι:Function.Injective ι:=Subtype.val_injective
 have hD:D.map ι=genericDisc S:=localDisc_generic S M γ'
 have hDdeg:D.natDegree=(genericDisc S).natDegree :=
   (natDegree_map_eq_of_injective hι D).symm.trans (congrArg natDegree hD)
 have hDunit :ρ D.leadingCoeff≠0:= by
   rw [leadingCoeff,hDdeg,← coeff_map,localDisc_fibre,coeff_map]
   exact (Finset.mem_filter.mp hγ).2
 have hsurj:=residue_surj S M γ'
 have hDv :v (ι D.leadingCoeff)=1 := by
   apply (show v (ι D.leadingCoeff)≤1 from D.leadingCoeff.property).antisymm
   apply le_of_not_gt
   intro h
   apply hDunit
   apply RingHom.mem_ker.mp
   rw [IsLocalRing.ker_eq_maximalIdeal ρ hsurj]
   exact (v.mem_maximalIdeal_iff).mpr h
 have hGunit :v G.leadingCoeff=1 := by
   rw [hl,← hD,leadingCoeff_map_of_injective hι]
   exact hDv
 have hDint (i:ℕ) :v ((genericDisc S).coeff i)≤1 := by
   rw [← hD,coeff_map]
   exact (D.coeff i).property
 have lift_poly (P: (oO C₀)[X]) (hp : ∀ i,v (P.coeff i)≤1) :
     ∃ l:A[X],l.map ι=P:= by
   apply (mem_lifts (f :=ι) P).mp
   exact (lifts_iff_coeff_lifts (f :=ι) P).mpr fun i=>⟨⟨_,hp i⟩,rfl⟩
 obtain ⟨q,hq'⟩:=lift_poly Q (square_factor_integral v he hGunit hDint)
 obtain ⟨g,hg'⟩:=lift_poly G (aNI v hq he hDint)
 have hf :D =q^2*g:= by
   apply Polynomial.map_injective _ hι
   rw [hD,Polynomial.map_mul,Polynomial.map_pow,hq',hg',he]
 have hgl:g.leadingCoeff=D.leadingCoeff :=hι (by
   rw [← leadingCoeff_map_of_injective hι,hg',hl,← hD,
     leadingCoeff_map_of_injective hι])
 have hqm: (q.map ι).Monic:= by rwa [hq']
 have hq0: (q.map ρ).Monic:=(hι.monic_map_iff.mpr hqm).map ρ
 have hgdeg:g.natDegree=G.natDegree :=
   (natDegree_map_eq_of_injective hι g).symm.trans (congrArg natDegree hg')
 have hgddeg:g.derivative.natDegree=G.derivative.natDegree := by
   rw [← natDegree_map_eq_of_injective hι g.derivative,← derivative_map,hg']
 have hgf : (g.map ρ).natDegree=G.natDegree :=
   (natDegree_map_eq_iff.mpr (Or.inl (hgl.symm ▸ hDunit))).trans hgdeg
 have hg0:g.map ρ≠0:=ne_zero_of_natDegree_gt (hgf ▸ hm)
 obtain ⟨w,hw⟩:=qRoCwuc.disc_square S (good_subset S hγ)
 have hs :w^2=C (1 :L)*(q.map ρ)^2*g.map ρ:= by
   have h:=(localDisc_fibre S M γ').trans hw
   change D.map ρ=w*w at h
   simpa only [hf,Polynomial.map_mul,Polynomial.map_pow,map_one,one_mul,pow_two] using h.symm
 obtain ⟨B,hB,hd,hbg,hbg'⟩:=common_divisor hg0 one_ne_zero hq0.ne_zero hs
 rw [hgf] at hd
 refine ⟨B.natDegree,hd,?_⟩
 have hres :=cfp ρ (M.uniformizer γ') hsurj (M.kernel γ') g g.derivative
   hgdeg.le hgddeg.le hB (by omega) hbg (by simpa only [derivative_map] using hbg')
 obtain ⟨b,hb⟩:=hres
 have hb' := congrArg ι hb
 rw [← resultant_map_map,← derivative_map,hg',map_mul,map_pow] at hb'
 have hle :v (G.resultant G.derivative)≤WithZero.exp (-(B.natDegree :ℤ)) := by
   have hπ:v (ι (M.uniformizer γ'))=WithZero.exp (-1) :=M.uniformizer_value γ'
   rw [hb',map_mul,map_pow,hπ]
   exact (mul_le_mul' le_rfl b.property).trans_eq (by
     rw [mul_one,← WithZero.exp_nsmul,nsmul_eq_mul,mul_neg,mul_one])
 have hb:=(WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr hR)).2 hle
 unfold KB
 change B.natDegree≤(-WithZero.log (v (G.resultant G.derivative))).toNat
 omega
private theorem weighted_count (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S)
    (hcurve :CurveField L (oO C₀)) (hheight:Gb L (oO C₀)
      S.bY.coordinate≤H) {Q G: (oO C₀)[X]} (hq:Q.Monic)
    (he :genericDisc S= Q^2*G) (hl:G.leadingCoeff=(genericDisc S).leadingCoeff)
    (hm:0<G.natDegree) (hsep:G.Separable) :
    (goodMarks S).card≤8*H := by
  classical
  let U:=goodMarks S
  let m:=G.natDegree
  let n:=G.derivative.natDegree
  let R:=G.resultant G.derivative
  have hR:R≠0:=resultant_ne_zero _ _ hsep
  by_cases hU:U.Nonempty
  swap
  · simp [show goodMarks S = ∅ from not_nonempty_iff_eq_empty.mp hU]
  obtain ⟨a,ha⟩:=hU
  obtain ⟨d,hd,_⟩:=local_rank_loss S M hq he hl hm hR ha
  have hdpos :0<d:= by omega
  let place (γ:U) :CurvePlace L (oO C₀) :=
    M.place ⟨γ,good_subset S γ.property⟩
  let V:=univ.image place
  have hinj:Function.Injective place := fun _ _ h =>
    Subtype.ext (congrArg (fun x :T=>(x :K)) (M.distinct h))
  have hcard:V.card=U.card:= by
    change (univ.image place).card= _
    rw [Finset.card_image_of_injective _ hinj,card_univ,Fintype.card_coe]
  have hdiv :axV L (oO C₀) :=
    aFU.of_children bRt.proof bRu.proof _ _ hcurve
  have hV : ∀ w∈V,d≤KB w.value R:= by
    intro w hw
    obtain ⟨γ,_,rfl⟩:=mem_image.mp hw
    obtain ⟨k,hk,hord⟩:=local_rank_loss S M hq he hl hm hR γ.property
    simpa only [show d=k by omega] using hord
  have htotal:d*U.card ≤ ∑ᶠ w:CurvePlace L (oO C₀),poleOrder w.value R:= by
    rw [(hdiv R).2.2.1,← hcard]
    let W:=(hdiv R).2.1.toFinset
    have hincl:V⊆W:= fun w hw=>(hdiv R).2.1.mem_toFinset.mpr
      (Nat.ne_of_gt (hdpos.trans_le (hV w hw)))
    rw [finsum_eq_finsetSum_of_support_subset _ (s :=W) fun w hw=>(hdiv R).2.1.mem_toFinset.mpr hw]
    calc
      _ = ∑ _w∈V,d:= by simp [Nat.mul_comm]
      _ ≤ ∑ w∈V,KB w.value R:=sum_le_sum hV
      _≤_:=sum_le_sum_of_subset hincl
  have hpole (w:CurvePlace L (oO C₀)) :
      poleOrder w.value R≤((m+n)*2)*Tq w.value S.bY.coordinate := by
    have hf :=cfo w.value G _ (aNI w.value hq he (disc_bound S w)) m n
    rw [← WithZero.exp_nsmul] at hf
    have hlog:=(WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr hR)).2 hf
    unfold poleOrder
    have heq : (m+n)•(2*(Tq w.value S.bY.coordinate :ℤ)) =
        (((m+n)*2*Tq w.value S.bY.coordinate :ℕ) :ℤ) := by push_cast; ring
    rw [heq] at hlog
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hlog
  have ht: (∑ᶠ w:CurvePlace L (oO C₀),poleOrder w.value R)≤((m+n)*2)*H := by
    let W:=(hdiv R).1.toFinset
    rw [finsum_eq_finsetSum_of_support_subset _ (s :=W) fun w hw=>(hdiv R).1.mem_toFinset.mpr hw]
    calc
      _ ≤ ∑ w∈W,((m+n)*2)*Tq w.value S.bY.coordinate :=sum_le_sum fun w _=>hpole w
      _=((m+n)*2) * ∑ w∈W,Tq w.value S.bY.coordinate := by rw [mul_sum]
      _≤_:=Nat.mul_le_mul_left _ (by
        let hW:=b27 hdiv S.bY.coordinate
        let V' := W∪hW.toFinset
        apply le_trans (sum_le_sum_of_subset (show W⊆V' from subset_union_left))
        rw [← finsum_eq_finsetSum_of_support_subset _ (s :=V') fun w hw =>
          mem_union_right _ (hW.mem_toFinset.mpr hw)]
        exact hheight)
  have hmn:m+n≤2*m:= by
    have h:=(natDegree_derivative_le G).trans (Nat.sub_le _ _)
    omega
  apply Nat.le_of_mul_le_mul_left _ hdpos
  calc
    d*U.card≤((m+n)*2)*H :=htotal.trans ht
    _≤((2*m)*2)*H :=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmn)
    _=d*(8*H) := by rw [show m=2*d from hd.symm]; ring
theorem count (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S)
  (hcurve :CurveField L (oO C₀))
  (hheight:Gb L (oO C₀) S.bY.coordinate≤H)
  (ht: (genericDisc S).natDegree<p) (hn : ¬ ConstantOddPart (genericDisc S)) :
  (goodMarks S).card≤8*H := by
 let:CharP (oO C₀) p :=
  charP_of_injective_ringHom ((zT C₀).comp (algebraMap K L)).injective p
 obtain ⟨Q,G,hq,he,hl,hm,hs⟩:=odd_factor ht hn
 exact weighted_count S M hcurve hheight hq he hl hm hs
end
end qvWbALd
