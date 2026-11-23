import ProximityPrize.SubmissionLower.B9
import ProximityPrize.SubmissionLower.ZYEj7Fd
import ProximityPrize.SubmissionLower.ZNBvygc
import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
open _root_ renaming Fin.ext → zmq, Fin.sum_univ_eq_sum_range → zdx, Finsupp.single → zhf, Finsupp.weight_apply → zDM, Function.Injective → zq4, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.monomial_le_degreeOf → zKk, Nat.mul_add → zws, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Submodule.mem_iInf → zxR
section
set_option autoImplicit true
namespace qK9VCOd
open Polynomial Finset
open cu (L)
open jA (jK mA)
open P5_7_2 (TopRow)
open q7F2qKe (weakAgreement)
open q7IA62d (Aw capColumns clearance coord cutoff ama kO width)
open private exponent exponent_none exponent_zero bpQ d5n from ProximityPrize.SubmissionLower.B9
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
private abbrev iL (t:TopRow) (q:ℕ) :=t.shape.B+t.shape.J - q
private abbrev aHb (t:TopRow) (h q c j:ℕ) :=width t q c j+h*iL t q
private abbrev Lh (t:TopRow) (h:ℕ) :=
 Σ q:Fin (t.shape.B+1),Σ c:Fin (min q.val (min t.YM (t.shape.J/2))+1),
   Σ j:Fin (min (q.val-c.val) (t.shape.J-2*c.val)+1),
     Fin (aHb t h q.val c.val j.val)×Fin (t.shape.U+1)
private def expOf {t h} (z :Lh t h) :mA →₀ ℕ :=
 exponent z.2.2.2.2.val (z.1.val-z.2.1.val-z.2.2.1.val) z.2.2.1.val z.2.1.val
private abbrev xOf {t h} (z :Lh t h) :ℕ:=z.2.2.2.1.val
private theorem exponent_eta (a :mA →₀ ℕ) :
   exponent (a none) (a (some 0)) (a (some 1)) (a (some 2))=a := by
 ext j
 cases j with
 | none=>exact exponent_none ..
 | some j=>fin_cases j <;> rfl
private theorem sum_exp (u i j c:ℕ) (f :mA→ℕ→ℕ) (hz : ∀ x,f x 0=0) :
  (exponent u i j c).sum f=f none u+(f (some 0) i+f (some 1) j+f (some 2) c) := by
 rw [Finsupp.sum_fintype _ _ hz,Fintype.sum_option,Fin.sum_univ_three]
 simp only [exponent_none,exponent_zero,bpQ,d5n]
private theorem admissible {t:TopRow} {h n u i j c:ℕ}
    (ht:131071*t.shape.B<t.shape.m*weakAgreement) :
    (capColumns t (exponent u i j c) ∧
      n+kO h (exponent u i j c)≤ cutoff t+clearance h t) ↔
    i+j+c≤t.shape.B∧j+2*c≤t.shape.J∧c≤t.YM∧u≤t.shape.U ∧
      n<aHb t h (i+j+c) c j:= by
  have hs (w:mA→ℕ) :
      (exponent u i j c).weight w=u*w none+(i*w (some 0)+j*w (some 1)+c*w (some 2)) := by
    rw [zDM]
    exact sum_exp _ _ _ _ (fun x n=>n*w x) (fun x=>Nat.zero_mul _)
  have hjet:=sum_exp u i j c (fun x n=>x.elim 0 fun k=>(131071+h-k.val)*n)
    (fun x=> by cases x <;> simp)
  simp only [capColumns,kO,hs,hjet,Option.elim_none,Option.elim_some,
    exponent_none,d5n,mul_zero,zero_add,mul_one,Fin.val_zero,Fin.val_one,
    Fin.val_two]
  have h₁:131071+h-1+1=131071+h:= by omega
  have h₂:131071+h-2+2=131071+h:= by omega
  have hw: (131071+h-0)*i+(131071+h-1)*j+(131071+h-2)*c+(j+2*c) =
      131071*(i+j+c)+h*(i+j+c) := by
    calc
      _=(131071+h)*i+(131071+h-1+1)*j+(131071+h-2+2)*c:= by
        simp only [Nat.sub_zero]
        ring
      _ = _:= by rw [h₁,h₂]; ring
  have hn (hq:i+j+c≤t.shape.B) :
      n+((131071+h-0)*i+(131071+h-1)*j+(131071+h-2)*c) ≤
          cutoff t+clearance h t↔n<aHb t h (i+j+c) c j:= by
    have hraw:=(zBI 131071 hq).trans_lt ht
    have hc:h*iL t (i+j+c)+h*(i+j+c)=(t.shape.B+t.shape.J)*h:= by
      rw [← zws,Nat.sub_add_cancel (hq.trans (Nat.le_add_right _ _)),z5A]
    unfold cutoff clearance aHb width
    omega
  constructor
  · rintro ⟨⟨q,hj,hc,hu⟩,hx⟩
    exact ⟨q,by omega,hc,hu,(hn q).mp hx⟩
  · rintro ⟨q,hj,hc,hu,hx⟩
    exact ⟨⟨q,by omega,hc,hu⟩,(hn q).mpr hx⟩
private theorem col_admissible {t h} (ht:131071*t.shape.B<t.shape.m*weakAgreement)
  (z :Lh t h) :
  capColumns t (expOf z)∧xOf z+kO h (expOf z)≤ cutoff t+clearance h t:= by
 rcases z with ⟨q,c,j,x,u⟩
 have hq:=q.isLt
 have hc:=c.isLt
 have hj:=j.isLt
 simp only [Nat.lt_succ_iff,le_min_iff] at hq hc hj
 have hs :q.val-c.val-j.val+j.val+c.val=q.val := by omega
 apply admissible ht |>.mpr
 rw [hs]
 exact ⟨hq,by omega,hc.2.1,Nat.le_of_lt_succ u.isLt,x.isLt⟩
private theorem col_exists {t h a n}
  (ht:131071*t.shape.B<t.shape.m*weakAgreement)
  (ha :capColumns t a∧n+kO h a≤ cutoff t+clearance h t) :
  ∃ z :Lh t h,expOf z=a∧xOf z=n:= by
 let i:=a (some 0)
 let j:=a (some 1)
 let c:=a (some 2)
 let u:=a none
 have he :exponent u i j c=a :=exponent_eta a
 obtain ⟨hq,hj,hc,hu,hx⟩:=(admissible ht).mp (he ▸ ha :capColumns t
  (exponent u i j c)∧n+kO h (exponent u i j c)≤ cutoff t+clearance h t)
 refine ⟨⟨⟨i+j+c,by omega⟩,⟨c,by simp only [Nat.lt_succ_iff,le_min_iff]; omega⟩,
  ⟨j,by simp only [Nat.lt_succ_iff,le_min_iff]; omega⟩,⟨n,hx⟩,⟨u,by omega⟩⟩,?_,rfl⟩
 simpa only [expOf,show i+j+c-c-j=i by omega] using he
private theorem col_injective (t:TopRow) (h:ℕ) :
  zq4 (fun z :Lh t h=>(expOf z,xOf z)) := by
 rintro ⟨q,c,j,x,u⟩ ⟨q',c',j',x',u'⟩ he
 have h₀:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 0)) he
 have h₁:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 1)) he
 have h₂:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 2)) he
 have h₃:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 none) he
 have h₄:=congrArg Prod.snd he
 simp only [expOf,xOf,exponent_zero,bpQ,d5n,exponent_none] at *
 have hc:=c.isLt
 have hj:=j.isLt
 have hc' := c'.isLt
 have hj' := j'.isLt
 simp only [Nat.lt_succ_iff,le_min_iff] at hc hj hc' hj'
 have :q=q' := zmq (by omega)
 subst q'
 have :c=c' := zmq h₂
 subst c'
 have :j=j' := zmq h₁
 subst j'
 have :x=x' := zmq h₄
 have :u=u' := zmq h₃
 subst x'
 subst u'
 rfl
private def mon (a :mA →₀ ℕ) (n:ℕ) :jK :=
 MvPolynomial.monomial a (Polynomial.monomial n 1)
private theorem coeff_mon (a b:mA →₀ ℕ) (m n:ℕ) :
  ((mon a m).coeff b).coeff n=if a=b∧m=n then 1 else 0:= by
 classical
 by_cases he :a=b <;> simp [mon,he,Polynomial.coeff_monomial]
theorem ds9 (t:TopRow) (h:ℕ)
    (ht:131071*t.shape.B<t.shape.m*weakAgreement) :
    Module.Finite L (Aw h t (cutoff t)) ∧
      (t.shape.U+1)*ama t (fun q c j=>width t q c j+h*(t.shape.B+t.shape.J-q)) ≤
        Module.finrank L (Aw h t (cutoff t)) := by
  classical
  let V:=Aw h t (cutoff t)
  let proj:V →ₗ[L] (Lh t h→L) :=
    LinearMap.pi fun z=>(coord (expOf z) (xOf z)).comp V.subtype
  have hmem (P:jK) :
      P∈V ↔ ∀ a n,¬ (capColumns t a∧n+kO h a≤ cutoff t+clearance h t) →
        (P.coeff a).coeff n=0:= by
    simp only [V,Aw,zxR,LinearMap.mem_ker]
    rfl
  have hinj:zq4 proj:= by
    intro P Q hp
    apply Subtype.ext
    ext a n
    by_cases ha :capColumns t a∧n+kO h a≤ cutoff t+clearance h t
    · obtain ⟨z,hz,hn⟩:=col_exists ht ha
      have he :=congrFun hp z
      change (P.val.coeff (expOf z)).coeff (xOf z)=(Q.val.coeff (expOf z)).coeff (xOf z) at he
      simpa only [hz,hn] using he
    · exact ((hmem _).mp P.property a n ha).trans (((hmem _).mp Q.property a n ha).symm)
  let:Module.Finite L V:=Module.Finite.of_injective proj hinj
  let col (z :Lh t h) :V :=
    ⟨mon (expOf z) (xOf z),(hmem _).mpr (by
      intro a n ha
      rw [coeff_mon,ite_eq_right]
      rintro ⟨rfl,rfl⟩
      exact (ha (col_admissible ht z)).elim)⟩
  have heq :proj ∘ col=(Pi.basisFun L (Lh t h) :Lh t h→Lh t h→L) := by
    funext z w
    rw [Function.comp_apply,Pi.basisFun_apply,Pi.single_apply]
    change ((mon (expOf z) (xOf z)).coeff (expOf w)).coeff (xOf w)= _
    simp only [coeff_mon,← Prod.mk.injEq,(col_injective t h).eq_iff,eq_comm]
  have hli:LinearIndependent L col:= by
    apply LinearIndependent.of_comp proj
    rw [heq]
    exact (Pi.basisFun L (Lh t h)).linearIndependent
  refine ⟨inferInstance,?_⟩
  have hcard:Fintype.card (Lh t h) =
      (t.shape.U+1)*ama t (fun q c j=>aHb t h q c j) := by
    simp only [Lh,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,z5A _ (t.shape.U+1)]
    unfold ama
    simp only [Finset.mul_sum]
    rw [← zdx]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← zdx]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← zdx]
  rw [← hcard]
  exact hli.fintype_card_le_finrank
end
end qK9VCOd
end
section
set_option autoImplicit true
namespace qK9VCOd
open Finset
open P5_7_2 (fO TopRow row topDonors)
open q7F2qKe (weakAgreement)
open q7IA62d (profile ama width required contactDebit eMG layerCeiling)
open scoped BigOperators
private theorem jet_add (t:TopRow) (f g:ℕ→ℕ→ℕ→ℕ) :
  ama t (fun q c j=>f q c j+g q c j)=ama t f+ama t g:= by
 simp only [ama,sum_add_distrib]
private theorem beP (t:TopRow) (h:ℕ) (f :ℕ→ℕ→ℕ→ℕ) :
  ama t (fun q c j=>h*f q c j)=h*ama t f := by
 simp only [ama,mul_sum]
private theorem residual_anti (t:TopRow) {d D:ℕ} (hle :d≤D) :
  residual t D ≤ residual t d:= by
 unfold residual ama
 refine sum_le_sum fun q _=>sum_le_sum fun c _=>sum_le_sum fun j _ => ?_
 exact Nat.sub_le_sub_left (ztf c (zBI 3 hle)) _
private theorem volume (t:TopRow) (h d:ℕ) :
   (t.shape.U+1)*ama t (fun q c j=>width t q c j+h*(t.shape.B+t.shape.J-q)) =
     (t.shape.U+1)*residual t d+layerCeiling d t +
     h*((t.shape.U+1)*ama t (fun q _ _=>t.shape.B+t.shape.J-q)) := by
 have hw:ama t (width t) =
     residual t d+ama t (fun q c j=>min (width t q c j) (3*d*c)) := by
   rw [residual,← jet_add]
   unfold ama
   refine sum_congr rfl fun q _=>sum_congr rfl fun c _=>sum_congr rfl fun j _ => ?_
   change width t q c j=width t q c j-3*d*c+min (width t q c j) (3*d*c)
   omega
 rw [jet_add,beP,hw,zws,zws,layerCeiling,Nat.mul_left_comm _ h]
private def Ly (b:fO) :ℕ:=if b.val<7 then 2541 else 2703
private theorem band_end (b:fO) : (row b).declaredHi≤Ly b:= by
 fin_cases b <;> decide
private theorem raw_positive (b:fO) (e :Bool) :
  131071*(profile b e).shape.B<(profile b e).shape.m*weakAgreement:= by
 cases e <;> by_cases hb:b.val<7 <;>
  simp only [profile,topDonors,hb,ite_true,ite_false,Bool.false_eq_true] <;> decide
private theorem endpoint_floor (b:fO) (e :Bool) :
   1+contactDebit (profile b e)+Ly b*(profile b e).poleRank ≤
     ((profile b e).shape.U+1)*residual (profile b e) (if e then Ly b else 0) := by
 cases e <;> by_cases hb:b.val<7 <;>
   simp only [profile,topDonors,Ly,hb,ite_true,ite_false,Bool.false_eq_true,contactDebit]
 · rw [value1 rfl rfl rfl rfl]
   decide
 · rw [value1 rfl rfl rfl rfl]
   decide
 · rw [value2 rfl rfl rfl rfl]
   decide
 · rw [value3 rfl rfl rfl rfl]
   decide
theorem proof :q7IA62d.c1 := by
 intro b e h hh
 let t:=profile b e
 let d:=if e then (row b).declaredHi else 0
 have hreq :required b e=layerCeiling d t+1 := by
  cases e
  · simp [required,d,layerCeiling,ama]
  · rfl
 have hd:=band_end b
 have hd' : d≤(if e then Ly b else 0) := by
  cases e
  · exact le_rfl
  · exact hd
 have hr :=ds9 t h (raw_positive b e)
 have hp:=ztf t.poleRank (hh.trans hd)
 have hm:=zBI (t.shape.U+1) (residual_anti t hd')
 have he :1+contactDebit t+Ly b*t.poleRank≤(t.shape.U+1)*residual t d :=
  (endpoint_floor b e).trans hm
 refine ⟨hr.1,le_trans ?_ hr.2⟩
 change required b e+contactDebit t+eMG h t≤_
 rw [volume t h d,hreq,eMG,zws]
 omega
end qK9VCOd
end
section
set_option autoImplicit true
namespace q3hrY0a
noncomputable section
open Polynomial
open DP (jF ad0)
open jA (jK mA)
open Rk (aIY)
open q7IA62d
open private bno a8W byG dxN from ProximityPrize.SubmissionLower.S
private theorem cEb {h t W} (D:jF h) (a :ℕ) (P:jK)
    (hP:CapsCut h t W P) :CapsCut h t (W+(3*h)*a) (Yd D a P) := by
  obtain ⟨hB,hJ,hC,hU,hW⟩:=hP
  let Q:=Yd D a P
  have hs (s :mA →₀ ℕ) (hs :s∈Q.support) :zhf none a+s∈P.support :=
    a8W (H :=D.block 0) (i:=a) hs
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro s h
    rw [← byG _ rfl a s]
    exact (z6P _ (hs s h)).trans hB
  · apply Finset.sup_le
    intro s h
    rw [← byG _ rfl a s]
    exact (z6P _ (hs s h)).trans hJ
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro s h
    simpa using (zKk (some 2) (hs s h)).trans hC
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro s h
    exact (Nat.le_add_left ..).trans
      ((zKk none (hs s h)).trans hU)
  · intro s hQ
    let w:mA→ℕ:= fun j=>j.elim 0 (fun k=>131071+h - k.val)
    have hw (u:mA →₀ ℕ) :kO h u=Finsupp.weight w u:= by
      rw [kO,zDM]
      congr 1
      funext j e
      cases j <;> simp [w,z5A]
    have hbefore :=hW _ (hs s hQ)
    change (P.coeff _).natDegree+kO h (zhf none a+s)≤_ at hbefore
    rw [hw,byG w rfl] at hbefore
    change (Q.coeff s).natDegree+kO h s≤_
    rw [hw]
    obtain ⟨u,hu⟩:=bno P a s
    have hc: (Q.coeff s).natDegree ≤
        ((D.block 0)^(3*a)).natDegree+(P.coeff (zhf none a+s)).natDegree := by
      simp only [Q,Yd,seedDerivative,← aIY,
        MvPolynomial.coeff_C_mul,hu]
      exact natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_mul_C_le _ _) _)
    have hd: ((D.block 0)^(3*a)).natDegree≤(3*h)*a := by
      calc
        _≤(3*a)*(D.block 0).natDegree :=natDegree_pow_le
        _=(3*h)*a := by rw [D.degree]; ring
    omega
theorem proof :q7IA62d.c5:= by
 intro b e h _ _ D _ Crt word
 dsimp only
 intro W a _ P hP
 obtain ⟨hA,hC,hD⟩:=Submodule.mem_inf.mp hP
 refine Submodule.mem_inf.mpr ⟨mem_ambient.mpr (cEb D a P (mem_ambient.mp hA)),?_,?_⟩
 · apply (zxR _).mpr
   intro i
   have hi:=bsz.mp ((zxR _).mp hC i)
   exact bsz.mpr (dxN (D.block 0) a _ (ad0 i) (word i) P hi)
 · exact mem_poleSpace.mpr (c4E Crt _ a P (mem_poleSpace.mp hD))
end
end q3hrY0a
end
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def d0_0:=s! 5135 1082 1082 41 8 0x8efe1f45803eda86a2c01a0c3ed16009cebc2d9fd330768b2a00de490895002b4665ca800341a3a540
private def d0_1 :=s! 5135 1082 3130 41 8 0x80fb4d1d5b48c4cea2c0277762d16014becf28b00a9d467458054bbaaa2c02937d0d16013818628b00
private def d0_2 :=s! 5135 1082 5178 40 8 0x372c0dda00f8a512da023fc397da03fd83d446d61af12fac087bfcb977cb0823482a4da18c920fe
private def d0_3:=s! 5135 1082 7226 28 1 0xa796b22
private def r0:=j! 5135 1082 0x10fd401b0600 [d0_0,d0_1,d0_2,d0_3]
private def d1_0:=s! 5170 1082 1082 41 8 0x908d1013403f7cfac9a01a4af6c4d009e4d82d214337390a3200e005bc19002b98798c8003478a8640
private def d1_1 :=s! 5170 1082 3130 41 8 0x84d9e539a54a8f64c9a0284a2bc4d0151ef292680ac8b7a134055f22fc9a029c09144d013bca552680
private def d1_2 :=s! 5170 1082 5178 40 8 0x49b3f614011fe4fc14027ac68214044b297e506677f8c9e7d8e6810cca6b7d529cddfe1e31e91a5
private def d1_3:=s! 5170 1082 7226 30 1 0x21628d67
private def r1 :=j! 5170 1082 0x115d49eae032 [d1_0,d1_1,d1_2,d1_3]
private def d2_0:=s! 5744 1209 1209 41 8 0xb54c7351c04de39468e01f61f794700b64326f0123a6152d8200fc82d5c10030da8a608003a854f040
private def d2_1 :=s! 5744 1209 3257 41 8 0xd74ec751c071ccbe68e03aca8c94701dc01cfa380ec1d9d51c072c02968e0368a4214701942f7ba380
private def d2_2 :=s! 5744 1209 5305 41 8 0x22041a9a301a9f34e32d12d85d7feeac75a6c7ecb7d4f99901acbab89f1636c23ae132d78c9423a380
private def d2_3:=s! 5744 1209 7353 38 4 0x8b95a942e25584603d0320518254812a460
private def r2 :=j! 5744 1209 0x1a9265e92d58 [d2_0,d2_1,d2_2,d2_3]
def dataI:Array aqm := #[
 r0,r1,r2
]
end qpECY2d
end
