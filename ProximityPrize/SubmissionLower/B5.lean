import ProximityPrize.SubmissionLower.M
import ProximityPrize.SubmissionLower.AB
set_option Elab.async false
open _root_ renaming B8.cylinder→lV,Ideal→lJ,Ideal.Quotient.mk→ oz,Ideal.span→ oY,Irreducible→ oq,IsLeftCancelMulZero.mul_left_cancel_of_ne_zero→pC,IsLeftRegular→ oD,MvPolynomial.C→n5,MvPolynomial.eval→pG,MvPolynomial.eval_C→ oZ,MvPolynomial.map→nX,MvPolynomial.weightedTotalDegree_one→ ox,MvPolynomial.weightedTotalDegree_piSingle→ oj,Nat.add_le_add→ ov,Nat.add_le_add_right→ oK,Nat.mul_le_mul_left→pz,Polynomial→ oy,Polynomial.C→nq,Polynomial.eval_map_apply→pL,Polynomial.hasseDeriv→mD,aR.Shape→lI,aR.embed→c9,aR.extend→aU,dN.GeoJets→lz,dN.separant→cy,map_mul→nI
set_option autoImplicit true
section
namespace dnK
noncomputable section
open aR (af Shape bY)
open dN (bC)

open GJ (vE)
open lB (bF aFf A9)


open scoped BigOperators
private theorem c5M:GJ.c1 :=
 axe.of_children bzy.proof bao.proof
private theorem cAI:GJ.c2 := by
  apply E6.of_children
  · apply YU.of_children
    · exact akN.of_children
        cya.proof bap.proof
    · exact ap6.of_children cyb.proof
        (anb.of_children
          cyd.proof cye.proof)
  · exact axf.of_children
      cyf.proof cyg.proof
private theorem bPY:GJ.c3:= by
  refine ap7.of_children cyh.proof aY2.proof ?_
  apply UH.of_children
  · exact aA4.of_children
      cyi.proof cyj.proof
  · exact aKo.of_children
      cyk.proof cyl.proof
  · exact akO.of_children cym.proof
      (aFS.of_children
        cyn.proof baq.proof)
private theorem cTh (L:ℕ) (hL:0<L) (p:lI) :vE (bY L p) := by
 refine ⟨A9 _ _,?_⟩
 change 0< min (2*L*(p.t-1)+L+1) ((2*L*(p.j-3)+L+3)/3)
 omega
private theorem b4b {a b:lI} (ha :vE a) (hb:bF b) :
  vE (a.plus b) := by
 obtain ⟨⟨ha₁,ha₂⟩,ha₃⟩:=ha
 obtain ⟨hb₁,hb₂⟩:=hb
 change (a.j+b.j≤a.b+b.b∧3*(a.t+b.t)≤a.j+b.j)∧0<a.t+b.t
 exact ⟨⟨by omega,by omega⟩,by omega⟩
private theorem BP {a :lI} (ha :bF a) (k :ℕ) :
  bF (a.scale k) := by
 refine ⟨pz k ha.1,?_⟩
 simpa [Shape.scale,Nat.mul_left_comm 3 k] using pz k ha.2
private theorem b4c {a :lI} (ha :vE a) {k :ℕ} (hk :0<k) :
   vE (a.scale k) :=
 ⟨BP ha.1 k,Nat.mul_pos hk ha.2⟩
private theorem agr {F:af 4} (hF:F≠0) :bC F≠0:= by
 intro h
 apply hF
 apply aFf
 simpa only [bC,map_zero] using h
end
end dnK
end
section
namespace atq
noncomputable section
open Polynomial MvPolynomial
open K1 (K)
open aR (af ao aO embed bY cK)
open dN (GeoJets GeoField j8 An bC su arh)
open aY3 (a86 aXG avh)
open wH (qg)
open lB (bF yy abx Po ahA
 afz SZ)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private structure TaylorChart (L:ℕ) where
 denom:lz
 numerator :Fin L→lz
private def TaylorChart.dM {L:ℕ} (T:TaylorChart L) (h:lI) :Prop :=
 yy T.denom h ∧ ∀ i,yy (T.numerator i) h
private def TaylorChart.aay {L:ℕ} (T:TaylorChart L) (S:ao[X]) :Prop :=
 An S T.denom≠0 ∧
  ∀ i,An S (T.numerator i) =
    An S T.denom*j8 (mD i.val S)
private abbrev agy (L:ℕ) :=GeoField×(Fin L→GeoField)
private def TaylorChart.pullback {L:ℕ} (T:TaylorChart L) (a :agy L) :GeoJets :=
 n5 a.1*T.denom + ∑ i,n5 (a.2 i)*T.numerator i
private theorem TaylorChart.aWC {L:ℕ} (T:TaylorChart L) {h:lI}
    (hT:T.dM h) (a :agy L) :yy (T.pullback a) h:= by
  classical
  have hw (w:Fin 4→ℕ) (d:ℕ) (hD:T.denom.weightedTotalDegree w≤d)
      (hN : ∀ i,(T.numerator i).weightedTotalDegree w≤d) :
      (T.pullback a).weightedTotalDegree w≤d:= by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((Po _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((Po _ _ _).trans (hN i))
  refine ⟨?_,hw Fin.val h.j hT.1.2.1 (fun i=>(hT.2 i).2.1),?_⟩
  · simpa only [ox] using hw 1 h.b
      (by simpa only [ox] using hT.1.1)
      (fun i=> by simpa only [ox] using (hT.2 i).1)
  · simpa only [oj] using hw (Pi.single (3:Fin 4) 1) h.t
      (by simpa only [oj] using hT.1.2.2)
      (fun i=> by simpa only [oj] using (hT.2 i).2.2)
private def denominator (L:ℕ) (g:af 4) :af 4 :=
 cy g^(2*L)
private def numerator (L:ℕ) (g:af 4) (i:Fin L) :af 4 :=
 if hi:i.val<4 then MvPolynomial.X ⟨i.val,hi⟩*denominator L g
 else
   n5 (nq (↑i.val.factorial:ao)⁻¹) *
     (cy g^(2*(L - i.val))*su g i.val)
private def ceP (L:ℕ) (g:af 4) :TaylorChart L where
 denom:=bC (denominator L g)
 numerator i:=bC (numerator L g i)
private theorem Vi {L:ℕ} (w:Fin 4→ℕ) (Δ d₀:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) (hw : ∀ i,w i≤d₀)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) (i:Fin L) :
    W w (numerator L g i)≤d₀+2*L*(B - w 3)+L*Δ:= by
  have hi:i.val≤L:=i.isLt.le
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((ov ((abx w _).trans (hw _)) (aXG w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤2*(L - i.val)*(B - w 3)+(w 0+i.val*(2*(B - w 3)+Δ)) :=
        ov (aXG w hg _) (avh w Δ hshift hB hg i.val)
      _=w 0+2*(i.val+(L - i.val))*(B - w 3)+i.val*Δ:= by ring
      _≤_:= by
        rw [Nat.add_sub_of_le hi]
        exact ov (oK (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem bW2 {L:ℕ} {g:af 4} {p:lI}
   (hg:aO (aR.shape g) p) (hp:bF p) (ht:0<p.t) :
   (ceP L g).dM (bY L p) := by
 constructor
 · apply a86 hg hp ht
   intro w Δ d₀ B _ _ _ hB
   exact (aXG w hB (2*L)).trans (by omega)
 · intro i
   exact a86 hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
     Vi w Δ d₀ hs hw hwB hB i)
private theorem ajW (S:ao[X]) (n:ℕ) :
  derivative^[n] S=nq (n.factorial:ao)*mD n S:= by
 ext m
 rw [coeff_iterate_derivative,Polynomial.coeff_C_mul,hasseDeriv_coeff,
  Nat.descFactorial_eq_factorial_mul_choose]
 simp only [nsmul_eq_mul,Nat.cast_mul,mul_assoc]
private theorem a2o {L:ℕ} (hL:L≤K1.p) {g:af 4} {S:ao[X]}
    (hg:cK g S=0) (hr :qg g S) : (ceP L g).aay S:= by
  have hden:cK (denominator L g) S=cK (cy g) S^(2*L) :=
    map_pow (pG (aR.jet S:Fin 4→ao[X])) _ _
  constructor
  · change An S (bC (denominator L g))≠0
    rw [afz,map_ne_zero_iff _ SZ,hden]
    exact pow_ne_zero _ hr
  · intro i
    change An S (bC (numerator L g i)) =
      An S (bC (denominator L g))*j8 (mD i.val S)
    rw [afz,afz,← nI]
    apply congrArg j8
    unfold numerator
    split_ifs with hinit
    · unfold cK
      rw [nI,MvPolynomial.eval_X,mul_comm]
      rfl
    · let E :=pG (aR.jet S:Fin 4→ao[X])
      change E (_ *(_^_ *_))= _
      rw [nI,nI,map_pow,oZ]
      change _ *(cK (cy g) S^(2*(L - i.val)) *
        cK (su g i.val) S)= _
      rw [arh _ _ hg,ajW]
      have hinv :nq (↑i.val.factorial:ao)⁻¹ *
          nq (↑i.val.factorial:ao)=1 := by
        rw [← nI,inv_mul_cancel₀ (ahA (i.isLt.trans_le hL)),map_one]
      have hpow:2*(L - i.val)+2*i.val = 2*L:= by
        rw [← Nat.mul_add,Nat.sub_add_cancel i.isLt.le]
      calc
        _=(nq (↑i.val.factorial:ao)⁻¹*nq (↑i.val.factorial:ao)) *
            ((cK (cy g) S^(2*(L - i.val))*cK (cy g) S^(2*i.val)) *
              mD i.val S) := by ring
        _ = _:= by rw [hinv,one_mul,← pow_add,hpow,hden]
private abbrev constants :ao →+* GeoField:=j8.comp nq
private abbrev center :GeoField:=j8 Polynomial.X
private def L4 (L:ℕ) (x a :K) :agy L :=
 (-constants (c9 a),fun i=>(constants (c9 x) - center)^i.val)
private theorem auQ (S:ao[X]) : (S.map constants).eval center=j8 S:= by
 rw [Polynomial.eval_map]
 change Polynomial.eval₂RingHom constants center S=j8 S
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [constants]
 · simp [center]
private theorem gAR {L:ℕ} (S:ao[X]) (hS:S.natDegree<L) (x :ao) :
   (∑ i:Fin L,j8 (mD i.val S)*(constants x - center)^i.val) =
     constants (S.eval x) := by
 let P:=S.map constants
 have hdeg: (taylor center P).natDegree<L:= by
   rw [natDegree_taylor]
   exact natDegree_map_le.trans_lt hS
 have hcoeff (i:ℕ) :
     (taylor center P).coeff i=j8 (mD i S) := by
   rw [taylor_coeff]
   change (mD i (S.map constants)).eval center= _
   rw [hasseDeriv_map,auQ]
 have heval :=(taylor center P).eval_eq_sum_range' hdeg (constants x - center)
 rw [← Fin.sum_univ_eq_sum_range] at heval
 simp only [hcoeff] at heval
 rw [taylor_eval_sub,show P.eval (constants x)=constants (S.eval x) from
   pL constants x] at heval
 exact heval.symm
private theorem gKY {L:ℕ} (T:TaylorChart L) {S:K[X]}
    (hS:S.natDegree<L) (hT:T.aay (aU S)) (x a :K) :
    An (aU S) (T.pullback (L4 L x a))=0↔S.eval x=a := by
  have hdeg: (aU S).natDegree<L:=natDegree_map_le.trans_lt hS
  have hval :=gAR (aU S) hdeg (c9 x)
  rw [pL] at hval
  have hsum :
      (∑ i:Fin L,(constants (c9 x) - center)^i.val *
        (An (aU S) T.denom*j8 (mD i.val (aU S)))) =
        An (aU S) T.denom*constants (c9 (S.eval x)) := by
    rw [← hval,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _=> by ring
  unfold TaylorChart.pullback L4
  simp only [map_add,map_sum,nI,An,oZ]
  change (-constants (c9 a))*An (aU S) T.denom +
      (∑ i:Fin L,(constants (c9 x) - center)^i.val *
        An (aU S) (T.numerator i))=0↔_
  simp only [hT.2,hsum]
  rw [show -constants (c9 a)*An (aU S) T.denom +
      An (aU S) T.denom*constants (c9 (S.eval x)) =
      An (aU S) T.denom*(constants (c9 (S.eval x)) - constants (c9 a)) by ring,
    mul_eq_zero,or_iff_right hT.1,sub_eq_zero]
  exact (SZ.comp Polynomial.C_injective).eq_iff.trans embed.injective.eq_iff
theorem d40 {L:ℕ} (hL:L≤K1.p) {g:af 4} {p:lI}
    (hg:aO (aR.shape g) p) (hp:bF p) (ht:0<p.t) (x a :K) :
    ∃ D:lz ,yy D (bY L p) ∧
      ∀ S:K[X],S.natDegree<L→cK g (aU S)=0→qg g (aU S) →
        (An (aU S) D =0↔S.eval x=a) := by
  let T:=ceP L g
  exact ⟨T.pullback (L4 L x a),T.aWC (bW2 hg hp ht) _,
    fun S hS hvan hreg=>gKY T hS (a2o hL hvan hreg) x a⟩
end
end atq
end
section
namespace atq
noncomputable section
open Polynomial
open P0 (K)

open aR (aO bY embed)
open dN (An Ch)
open BO (aYz pN)
open aKp (rV cZO)

open lB (yy)
private theorem bYY:aKp.c2 :=
 as4.of_children bRo.proof bjz.proof
private theorem bYX {f C s p D} {Γ:Finset K}
   (hc:aYz f C) (hp:aO ⟨1,3,1⟩ p)
   (hD:yy D p) (hproper :D∉C) (hinj:Set.InjOn s (Γ:Set K))
   {L:Finset K} (hL:L⊆Γ)
   (hmarks : ∀ γ∈L,C≤Ch (aU (s γ))∧An (aU (s γ)) D =0) :
   6*L.card≤pN C (p.scale 6) := by
 classical
 let point := fun γ=>rV (aU (s γ))
 have hinjL:Set.InjOn point (L:Set K) := by
   intro γ hγ η hη he
   exact hinj (hL hγ) (hL hη)
     (Polynomial.map_injective c9 embed.injective (cZO he))
 have hcount:=bYY C p hc.prime hc.dim hp D hD hproper (L.image point) (by
   intro x hx
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
   exact hmarks γ hγ)
 rwa [Finset.card_image_of_injOn hinjL] at hcount
private theorem cFk (L:ℕ) (p:lI) :
  aO ⟨1,3,1⟩ (bY L p) := by
 unfold bY
 simp only [aO]
 exact ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),
  Nat.le_add_left _ _,le_min (by omega) (by omega)⟩
end
end atq
end
section
namespace bjX
noncomputable section





open B8 (aYC cKY)

open MvPolynomial
open scoped BigOperators
theorem ccZ:B8.bTp :=
 Jq.of_children as5.proof cyq.proof
theorem bZB:B8.bQI :=
 axg.of_children bzC.proof
  (aA6.of_children bzD.proof cyr.proof)
theorem cKZ:aYC :=
 cKY ccZ bZB
end
end bjX
end
section
namespace bjX
noncomputable section
open aR (af)
open dN (GeoJets bC kC oA lN GeoField)
open vS (g9)
open B8 (i9 qK TB Ro)
open RingTheory.Sequence
open private cwM cTT from ProximityPrize.SubmissionLower.V
open private cJk cJh c70 cJj cJi
 from ProximityPrize.SubmissionLower.C
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem egg {f Q:af 4} (hf :oq f) (hQ : ¬ f∣Q) :
    oD (oz (oY {bC f}) (bC Q)) := by
  let I:lJ (af 4) :=oY {f}
  let:I.IsPrime :=(Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  have hphysical:IsWeaklyRegular (af 4) [f,Q] := by
    rw [cwM]
    exact ⟨pC hf.ne_zero,
      pC
        (mt Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_span_singleton.not.mpr hQ))⟩
  let B:=MvPolynomial (Fin 4) lN
  let T:=(nonZeroDivisors (oy aR.ao)).map (n5 (σ:=Fin 4))
  have h₁:=hphysical.of_isLocalization B T
  have :=cTT
  have h₂:=h₁.of_flat (S:=lz)
  simp only [List.map_cons,List.map_nil] at h₂
  change IsWeaklyRegular lz
    [nX (algebraMap lN GeoField)
      (nX (algebraMap (oy aR.ao) lN) f),
     nX (algebraMap lN GeoField)
      (nX (algebraMap (oy aR.ao) lN) Q)] at h₂
  have h₃:IsWeaklyRegular lz [bC f,bC Q] := by
    simpa only [bC,dN.j8,MvPolynomial.map_map] using h₂
  exact ((cwM ..).mp h₃).2
theorem bZC (f Q:af 4) (hf :oq f) (hQ : ¬ f∣Q) :
    let A:=i9 ⊥ (qK (bC f))
    let J:=i9 A (qK (bC Q))
    oD (oz A (qK (bC Q))) ∧
    ∀ P:lJ lz ,∀ h: (kC f Q).IsMinimalPrime P,
      TB (lV P) 3 ∧
        ∃ hc:J.IsMinimalPrime (lV P),
          oA (kC f Q) P h.isPrime≤Ro J (lV P) hc.isPrime := by
  let F:lJ GeoJets :=oY {bC f}
  have hA:i9 ⊥ (qK (bC f))=lV F:= by
    simp [i9,lV,F,Ideal.map_span]
  have hJ:i9 (i9 ⊥ (qK (bC f))) (qK (bC Q)) =
      lV (kC f Q) := by
    rw [hA,kC,Ideal.span_insert]
    simp [i9,lV,F,Ideal.map_sup,Ideal.map_span]
  have hreg:=egg hf hQ
  have hF:=WI.agr hf.ne_zero
  dsimp only
  constructor
  · exact (congrArg (fun I:lJ g9 =>
      oD (oz I (qK (bC Q)))) hA).mpr
      (cJk hreg)
  · intro P hP
    refine ⟨cJh (GJ.bf6 hF (c70 hF hreg) hP),
      ?_⟩
    apply (congrArg (fun I:lJ g9 => ∃ hc:I.IsMinimalPrime (lV P),
      oA (kC f Q) P hP.isPrime≤Ro I (lV P) hc.isPrime) hJ).mpr
    exact ⟨cJj hP,(cJi (kC f Q) P hP.isPrime).le⟩
end
end bjX
end
