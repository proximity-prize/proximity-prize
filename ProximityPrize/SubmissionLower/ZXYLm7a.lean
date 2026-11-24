import ProximityPrize.SubmissionLower.ZsazLcd
import ProximityPrize.SubmissionLower.ZOAcvWb
import ProximityPrize.SubmissionLower.Z5rjxle
import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.ZzzlQ7b
import ProximityPrize.SubmissionLower.ZCEtgbe
import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.ZVMYHza
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZalmDpd
import ProximityPrize.SubmissionLower.Z0aQQAb
import ProximityPrize.SubmissionLower.ZlH1Cxb
import ProximityPrize.SubmissionLower.ZMNCpvb
set_option Elab.async false
section
section
set_option autoImplicit true
namespace qkjH8aa
theorem proof :qa9Ovbd.c6:= by
 intro T C S D q M b f G H R A B hfpos hS hSd hA hB hf hG hH hR hz hw heq i
 exact ⟨qZcMfNa.resultant_bounded hf hG i,
  qgcZtNc.markedResultant C S D q M b f G H R A B
   hfpos hS hSd hA hB hf hG hH hR hz hw heq i⟩
end qkjH8aa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qUDmSXc
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open Cu
open E7 (CurvePlace axV poleOrder KB Tq Gb)
open agN (b27)
open quN7Z4a (Sheet)
open qRoCwuc (disc genericDisc goodMarks)
open qvWbALd (MarkedPlaces localDisc localDisc_generic localDisc_fibre
 odd_factor aNI square_factor_integral disc_bound cfo)
open private good_subset from ProximityPrize.SubmissionLower.ZXGF8Ec
open private residue_surj from ProximityPrize.SubmissionLower.ZsS78jd
open scoped BigOperators WithZero qvWbALd
def c1 :Prop :=qvWbALd.c1
def c2 :Prop :=qvWbALd.c2
private theorem square_of_fibre {a :L} {q r :L[X]} (ha :a≠0) (hq:q≠0)
  (hs :IsSquare (C a*q^2*r)) :IsSquare r := by
 obtain ⟨w,hw⟩:=hs.exists_sq
 have hdiv :q^2∣w^2 :=⟨C a*r,by rw [← hw]; ring⟩
 obtain ⟨u,hu⟩:=(UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide :2≠0)).mp hdiv
 have he :C a*r=u^2 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hq)
  rw [← mul_pow,← hu,← hw]
  ring
 obtain ⟨b,hb⟩:=IsAlgClosed.exists_pow_nat_eq a⁻¹ zero_lt_two
 refine ⟨C b*u,?_⟩
 rw [← pow_two,mul_pow,← map_pow,hb,← he,← mul_assoc,← map_mul,
  inv_mul_cancel₀ ha,map_one,one_mul]
variable {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
 (S:Sheet C₀ J 2 H T z s)
private abbrev Ia (γ:goodMarks S) :T:=⟨γ,good_subset S γ.property⟩
private theorem at_mark (M:MarkedPlaces S) {Q G R: (oO C₀)[X]}
   (hq:Q.Monic) (he :genericDisc S= Q^2*G)
   (hl:G.leadingCoeff=(genericDisc S).leadingCoeff)
   (hG:G=C G.leadingCoeff*R) (hR:R.Monic) (γ:goodMarks S)
   (hs :IsSquare ((disc S).map (MvPolynomial.eval (S.parameter γ)))) :
   let v :=(M.place (Ia S γ)).value
   ∃ f :v.valuationSubring[X],
     f.map v.valuationSubring.toSubring.subtype=R∧f.Monic ∧
     IsSquare (f.map (M.residue (Ia S γ)))∧v G.leadingCoeff=1 := by
 classical
 let γ' := Ia S γ
 let v :=(M.place γ').value
 let A:=v.valuationSubring
 let i:A →+* oO C₀:=A.toSubring.subtype
 let ρ:=M.residue γ'
 let D:=localDisc S M γ'
 have hi:Function.Injective i:=Subtype.val_injective
 have hD:D.map i=genericDisc S:=localDisc_generic S M γ'
 have hdeg:D.natDegree=(genericDisc S).natDegree :=
   (natDegree_map_eq_of_injective hi D).symm.trans (congrArg natDegree hD)
 have hunit :ρ D.leadingCoeff≠0:= by
   rw [leadingCoeff,hdeg,← coeff_map,localDisc_fibre,coeff_map]
   exact (Finset.mem_filter.mp γ.property).2
 have hval :v G.leadingCoeff=1 := by
   rw [hl,← hD,leadingCoeff_map_of_injective hi]
   apply (show v (i D.leadingCoeff)≤1 from D.leadingCoeff.property).antisymm
   apply le_of_not_gt
   intro h
   apply hunit
   apply RingHom.mem_ker.mp
   rw [IsLocalRing.ker_eq_maximalIdeal ρ (residue_surj S M γ')]
   exact (v.mem_maximalIdeal_iff).mpr h
 have hDint (j:ℕ) :v ((genericDisc S).coeff j)≤1 := by
   rw [← hD,coeff_map]
   exact (D.coeff j).property
 have lift_poly (P: (oO C₀)[X]) (hp : ∀ j,v (P.coeff j)≤1) :
     ∃ f :A[X],f.map i=P:= by
   apply (mem_lifts (f :=i) P).mp
   exact (lifts_iff_coeff_lifts (f :=i) P).mpr fun j=>⟨⟨_,hp j⟩,rfl⟩
 obtain ⟨q,hqi⟩:=lift_poly Q (square_factor_integral v he hval hDint)
 obtain ⟨r,hri⟩:=lift_poly R (fun j=> by
   have hj:=aNI v hq he hDint j
   have hj' := congrArg (fun P: (oO C₀)[X]=>P.coeff j) hG
   change G.coeff j=(C G.leadingCoeff*R).coeff j at hj'
   rwa [hj',coeff_C_mul,map_mul,hval,one_mul] at hj)
 have hq' : q.Monic:=hi.monic_map_iff.mpr (hqi.symm ▸ hq)
 have hr' : r.Monic:=hi.monic_map_iff.mpr (hri.symm ▸ hR)
 have hmul :D =C D.leadingCoeff*q^2*r := by
   apply Polynomial.map_injective _ hi
   rw [hD,Polynomial.map_mul,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,
     hqi,hri,← leadingCoeff_map_of_injective hi,hD,← hl]
   conv_lhs=>rw [he,hG]
   ring
 refine ⟨r,hri,hr',square_of_fibre hunit (hq'.map ρ).ne_zero ?_,hval⟩
 have hh:IsSquare (D.map ρ) := by rwa [localDisc_fibre]
 have hm:=congrArg (fun P:A[X]=>P.map ρ) hmul
 change D.map ρ=(C D.leadingCoeff*q^2*r).map ρ at hm
 rw [hm] at hh
 simpa only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow] using hh
private theorem exL {F:Type} [Field F] (v :Valuation F ℤᵐ⁰)
    {G R:F[X]} (hG:G=C G.leadingCoeff*R) (ha :v G.leadingCoeff=1)
    (hres :G.resultant G.derivative≠0)
    (hder :G.derivative.natDegree=R.natDegree - 1)
    (hdeg:G.natDegree=R.natDegree) (f :v.valuationSubring[X])
    (hf :f.map v.valuationSubring.toSubring.subtype=R)
    (π:v.valuationSubring) (hπ:v (π:F)=WithZero.exp (-1)) {e :ℕ}
    (he :π^e∣f.resultant f.derivative R.natDegree (R.natDegree - 1)) :
    e≤KB v (G.resultant G.derivative) := by
  let i:=v.valuationSubring.toSubring.subtype
  change f.map i=R at hf
  obtain ⟨b,hb⟩:=he
  have hb' := congrArg i hb
  rw [← resultant_map_map,← derivative_map f i,hf,map_mul,map_pow] at hb'
  have hscale :v (G.resultant G.derivative) =
      v (R.resultant R.derivative R.natDegree (R.natDegree - 1)) := by
    have hs (m n:ℕ) :G.resultant G.derivative m n =
        (C G.leadingCoeff*R).resultant (C G.leadingCoeff*R.derivative)
          m n:=congrArg₂ (fun P Q:F[X]=>P.resultant Q m n) hG
            ((congrArg derivative hG).trans (derivative_C_mul _ _))
    rw [hdeg,hder,hs,resultant_C_mul_left,resultant_C_mul_right,
      map_mul,map_mul,map_pow,map_pow,ha]
    simp only [one_pow,one_mul]
  have hle :v (G.resultant G.derivative)≤WithZero.exp (-(e :ℤ)) := by
    rw [hscale,hb',map_mul,map_pow,show v (i π)=WithZero.exp (-1) from hπ]
    exact (mul_le_mul' le_rfl b.property).trans_eq (by
      rw [mul_one,← WithZero.exp_nsmul,nsmul_eq_mul,mul_neg,mul_one])
  have hlog:=(WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr hres)).2 hle
  unfold KB
  omega
private theorem sum_over_places {α β:Type} (U:Finset α) (u:U→β)
  (hu:Function.Injective u) (e :α→ℕ) (g:β→ℕ)
  (hg:g.HasFiniteSupport) (he : ∀ j:U,e j≤g (u j)) :
  ∑ j∈U,e j ≤ ∑ᶠ b,g b:= by
 classical
 let V:=univ.image u
 let W:=V∪hg.toFinset
 rw [finsum_eq_finsetSum_of_support_subset _ (s :=W) fun b hb =>
  mem_union_right _ (hg.mem_toFinset.mpr hb)]
 calc
  _ = ∑ j:U,e j:=(sum_attach U e).symm
  _ ≤ ∑ j:U,g (u j) :=sum_le_sum fun j _=>he j
  _ = ∑ b∈V,g b:=(sum_image fun _ _ _ _ h=>hu h).symm
  _≤_:=sum_le_sum_of_subset subset_union_left
private theorem pole_budget (hdiv :axV L (oO C₀))
    (hh:Gb L (oO C₀) S.bY.coordinate≤H)
    {Q G: (oO C₀)[X]} (hq:Q.Monic)
    (he :genericDisc S= Q^2*G) (hres :G.resultant G.derivative≠0) :
    ∑ᶠ v :CurvePlace L (oO C₀),KB v.value (G.resultant G.derivative) ≤
      (G.natDegree+G.derivative.natDegree)*(2*H) := by
  let R:=G.resultant G.derivative
  let b:=G.natDegree+G.derivative.natDegree
  have hpole (v :CurvePlace L (oO C₀)) :
      poleOrder v.value R≤(b*2)*Tq v.value S.bY.coordinate := by
    have hb:=cfo v.value G _ (aNI v.value hq he (disc_bound S v))
      G.natDegree G.derivative.natDegree
    rw [← WithZero.exp_nsmul] at hb
    have hlog:=(WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hres)).2 hb
    have heq :b•(2*(Tq v.value S.bY.coordinate :ℤ)) =
        (((b*2)*Tq v.value S.bY.coordinate :ℕ) :ℤ) := by
      rw [nsmul_eq_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,mul_assoc]
    change WithZero.log (v.value R)≤b•_ at hlog
    rw [heq] at hlog
    simpa only [poleOrder,Int.toNat_natCast] using Int.toNat_le_toNat hlog
  classical
  let W:=(hdiv R).1.toFinset
  rw [← (hdiv R).2.2.1,finsum_eq_finsetSum_of_support_subset _ (s :=W)
    fun v hv=>(hdiv R).1.mem_toFinset.mpr hv]
  change _≤b*(2*H)
  rw [← mul_assoc]
  calc
    _ ≤ ∑ v∈W,(b*2)*Tq v.value S.bY.coordinate :=sum_le_sum fun v _=>hpole v
    _=(b*2) * ∑ v∈W,Tq v.value S.bY.coordinate := by rw [mul_sum]
    _≤_:=Nat.mul_le_mul_left _ (by
      let hW:=b27 hdiv S.bY.coordinate
      let V:=W∪hW.toFinset
      apply le_trans (sum_le_sum_of_subset (show W⊆V from subset_union_left))
      rw [← finsum_eq_finsetSum_of_support_subset _ (s :=V)
        fun v hv=>mem_union_right _ (hW.mem_toFinset.mpr hv)]
      exact hh)
private theorem bD9 {F:Type} [Field F] [CharP F p] {G:F[X]}
  (hm:0<G.natDegree) (ht:G.natDegree<p) :
  G.derivative.natDegree=G.natDegree - 1 := by
 have hn: (G.natDegree :F)≠0:= by
  rw [Ne,CharP.cast_eq_zero_iff F p]
  exact fun h=>(not_le_of_gt ht) (Nat.le_of_dvd hm h)
 have hpred:G.natDegree - 1+1=G.natDegree := by omega
 have hc: ((G.natDegree - 1 :ℕ) :F)+1=(G.natDegree :F) :=
  (Nat.cast_add_one _).symm.trans (congrArg (fun n:ℕ=>(n:F)) hpred)
 apply le_antisymm (natDegree_derivative_le G) (le_natDegree_of_ne_zero ?_)
 rw [coeff_derivative,hpred,hc,coeff_natDegree]
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hm)) hn
theorem of_children (h1 :c1) (h2 :c2) :qRoCwuc.c1 := by
  classical
  intro C₀ _ J H T z s S hz _ hs ht hn
  obtain ⟨hc,hh⟩:=h1 S
  obtain ⟨M⟩:=h2 S hc hz
  let F:=oO C₀
  let:CharP F p:=charP_of_injective_ringHom ((zT C₀).comp (algebraMap K L)).injective p
  obtain ⟨Q,G,hq,he,hl,hm,hsep⟩:=odd_factor ht hn
  have hg:=ne_zero_of_natDegree_gt hm
  let a :=G.leadingCoeff
  have ha :a≠0:=leadingCoeff_ne_zero.mpr hg
  let R:=C a⁻¹*G
  have hR:R.Monic:= by
    rw [show R=G*C a⁻¹ from mul_comm _ _]
    exact monic_mul_leadingCoeff_inv hg
  have hG:G=C G.leadingCoeff*R:= by rw [show R= _ from rfl,← mul_assoc,← map_mul,
    mul_inv_cancel₀ ha,map_one,one_mul]
  have hd:G.natDegree=R.natDegree :=(natDegree_C_mul (p:=G) (inv_ne_zero ha)).symm
  have htG:G.natDegree<p:=(natDegree_le_of_dvd
    ⟨Q^2,he.trans (mul_comm _ _)⟩ (fun hz' => hn ⟨0,1,by simp [hz']⟩)).trans_lt ht
  have hder :=bD9 (F:=F) hm htG
  have hsepR:R.Separable :=hsep.of_dvd ⟨C a,hG.trans (mul_comm _ _)⟩
  have hres :G.resultant G.derivative≠0:=resultant_ne_zero _ _ hsep
  choose f hf hfm hfs hval using fun γ:goodMarks S =>
    at_mark S M hq he hl hG hR γ (hs γ γ.property)
  refine ⟨⟨R,hR,hd ▸ hm,hd ▸ htG,hsepR,⟨Q,hq,?_⟩,
    fun γ=>(M.place (Ia S γ)).value.valuationSubring.toSubring,
    fun γ=>M.residue (Ia S γ),fun γ=>residue_surj S M _,fun γ=>M.uniformizer _,
    fun γ=>M.kernel _,f,hf,hfm,hfs,?_⟩⟩
  · calc
      _= Q^2*G:=he
      _=C (genericDisc S).leadingCoeff*Q^2*R:= by rw [hG,← hl,mul_left_comm,mul_assoc]
  · intro e h
    let u (γ:goodMarks S) :=M.place (Ia S γ)
    have hu:Function.Injective u:= fun _ _ h' => Subtype.ext
      (congrArg (fun γ:T=>(γ:K)) (M.distinct h'))
    have hdiv :axV L F :=
      aFU.of_children bRt.proof bRu.proof _ _ hc
    have hb:=sum_over_places (goodMarks S) u hu e
      (fun v=>KB v.value (G.resultant G.derivative)) (hdiv _).2.1
      (fun γ=>exL (u γ).value hG (hval γ) hres (hder.trans (congrArg (· - 1) hd)) hd
        (f γ) (hf γ) (M.uniformizer _) (M.uniformizer_value _) (h γ))
    refine hb.trans ((pole_budget S hdiv hh hq he hres).trans_eq ?_)
    rw [hder,hd,show R.natDegree+(R.natDegree - 1)=2*R.natDegree - 1 by omega]
end
end qUDmSXc
end
end
section
section
set_option autoImplicit true
namespace q7JZjze
theorem proof :qa9Ovbd.c2 :=qtVXGJd.proof
end q7JZjze
end
section
set_option autoImplicit true
theorem qcgsXkd.proof :qa9Ovbd.c3 :=
  qyOEyfe.proof
end
section
set_option autoImplicit true
namespace qUBKcMe
theorem proof :qa9Ovbd.c4 :=qvwhqDa.proof
end qUBKcMe
end
section
set_option autoImplicit true
namespace q3pDxPb
theorem proof :qa9Ovbd.c5:=q5yqMPc.proof
end q3pDxPb
end
end
section
set_option autoImplicit true
namespace qNgJy2c
noncomputable section
open Polynomial Finset
open P6 (K p)
open qWdRihc (UJ d)
open qrsE1ie (discriminant geomSquare)
open quN7Z4a (sheet compressionWidth physicalWeight)
open cu (L)
open private bd0 from ProximityPrize.SubmissionLower.ZqKag5d
open private OF.distinct OF.degree OF.lg from ProximityPrize.SubmissionLower.ZogIzOe
open private band_degrees from ProximityPrize.SubmissionLower.ZRqikKa
open private disc_degree from ProximityPrize.SubmissionLower.ZcErkXc
open private rate_ge dQt from ProximityPrize.SubmissionLower.Z3swOYa
theorem proof :q4V2ihd.c1 := by
  classical
  intro b u del M Γ F _ x T J Q H hm
  have hw:=bd0 F x.vo hm.subset
  have hz :Set.InjOn M.label (T:Set K) := fun _ _ _ _ e=>sub_left_inj.mp e
  let W:UJ:=⟨T,algebraMap K L ∘ M.label,F.scalar,M.word,
    fun _ hγ _ hη e=>hz hγ hη ((algebraMap K L).injective e),
    OF.distinct hw,fun γ hγ=>(OF.degree hw γ hγ).trans
      (Nat.add_le_add_left (band_degrees b).2 131071),OF.lg hw⟩
  have hcount:T.card≤29*H+2 := by
    obtain ⟨_,C₀,_,_,_,hδ,_,_⟩:=hm.curve
    obtain ⟨C,hC,_,⟨S⟩⟩:=sheet (by decide :0<2) hm.curve hδ hm.marks
    let:Fact (Irreducible C) :=⟨hC⟩
    by_cases hM:compressionWidth d 2≤physicalWeight d S.root.equation
    · have hc:=q6CrDDe.of_children
        q978Lma.proof P5_7_1_5_4_2_1_2.proof
        C J T M.label F.scalar d H S (by decide) hM hz W.degree
      omega
    by_cases hs :geomSquare S.root.equation
    · obtain ⟨cover⟩:=qPTDwMb.proof C J T M.label F.scalar M.word H S hs hz
      exact dQt W cover
    have hdisc: (discriminant S.root.equation).natDegree<p :=
      (disc_degree d S.root.equation).trans_lt
        ((Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hM) (by decide)).trans
          (by decide :2*compressionWidth d 2<p))
    have hc:=qvWbALd.of_children
      q9aDOab.proof qmpFDTd.proof
      C J T M.label F.scalar H S hdisc hs hz
    omega
  have hc: (T.card:ℚ)≤29*H+2 := by exact_mod_cast hcount
  have hr :=mul_le_mul_of_nonneg_right (rate_ge b) (Nat.cast_nonneg (α:=ℚ) H)
  have hm' : (0:ℚ)≤16*(2*(Q.totalDegree :ℚ)) := by positivity
  linarith only [hc,hr,hm']
end
end qNgJy2c
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_3_1_1
theorem proof :qUDmSXc.c1 :=q9aDOab.proof
end P5_7_3_3_4_3_1_1
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_3_1_2
theorem proof :qUDmSXc.c2 :=qmpFDTd.proof
end P5_7_3_3_4_3_1_2
end
section
set_option autoImplicit true
namespace qzr6Ywe
theorem proof :qWEQiwd.c3 :=
  qRoCwuc.of_children
    (qUDmSXc.of_children P5_7_3_3_4_3_1_1.proof P5_7_3_3_4_3_1_2.proof)
    q6s3Ofd.proof
end qzr6Ywe
end
section
set_option autoImplicit true
namespace qnW7ygd
theorem proof :qNUt03b.c1 :=
  qa9Ovbd.of_children qtxrZka.proof q7JZjze.proof
    qcgsXkd.proof qUBKcMe.proof q3pDxPb.proof
    qkjH8aa.proof
end qnW7ygd
end
section
set_option autoImplicit true
namespace qEnmsja
theorem proof :qNUt03b.c2 :=
  qxblDlc.of_children qw8MfCe.proof qDall2c.proof q6senCe.proof
end qEnmsja
end
