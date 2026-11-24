import ProximityPrize.SubmissionLower.CU
import ProximityPrize.SubmissionLower.Z6sVZdb
import ProximityPrize.SubmissionLower.ZG8ydqc
set_option Elab.async false
set_option autoImplicit true
namespace aKK
noncomputable section
open Polynomial MvPolynomial K1 aR Ex dN wH lB Tx
open scoped BigOperators
open private azv cM3 Ur cYg denominator ajW from ProximityPrize.SubmissionLower.ZG8ydqc
open private cr1 ayL from ProximityPrize.SubmissionLower.Z6sVZdb
open private crZ from ProximityPrize.SubmissionLower.J
local notation "W" => MvPolynomial.weightedTotalDegree
private def numerator (L:ℕ) (f :af 4) (n:ℕ) :af 4 :=
  if hn:n<4 then MvPolynomial.X ⟨n,hn⟩*denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial:ao)⁻¹) *
      (separant f^(L - n)*azv f n)
private theorem ZB (L:ℕ) (w:Fin 4→ℕ) {f :af 4} {B:ℕ}
    (hf :W w f≤B) :W w (denominator L f)≤L*(B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (Ur w hf))
private theorem Vi {L n:ℕ} (hn:n≤L) (w:Fin 4→ℕ) (Δ d₀:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) (hw : ∀ i,w i≤d₀)
    {f :af 4} {B:ℕ} (hB:w 3≤B) (hf :W w f≤B) :
    W w (numerator L f n)≤d₀+L*(B - w 3+Δ) := by
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((abx w _).trans (hw _)) (ZB L w hf)).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _))
  · have hp:=(weightedTotalDegree_pow_le w (separant f) (L - n)).trans
      (Nat.mul_le_mul_left _ (Ur w hf))
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤(L - n)*(B - w 3)+(w 0+n*(B - w 3+Δ)) :=
        Nat.add_le_add hp (cYg w Δ hshift hB hf n)
      _=w 0+((L - n)+n)*(B - w 3)+n*Δ:= by ring
      _≤_:= by
        rw [Nat.sub_add_cancel hn,Nat.mul_add]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
private theorem bnw {L:ℕ} (hL:L<K1.p) {f :af 4}
    (hf : (shape f).t=1) (S:ao[X]) (hon :cK f S=0) (hr :qg f S) :
    An S (bC (denominator L f))≠0 ∧
      ∀ i:Fin L,An S (bC (numerator L f i.val)) =
        An S (bC (denominator L f))*j8 (hasseDeriv i.val S) := by
  have hp:cK (separant f) S≠0:=hr
  have hden:cK (denominator L f) S=cK (separant f) S^L :=
    map_pow (MvPolynomial.eval (jet S:Fin 4→ao[X])) _ _
  constructor
  · rw [afz,hden]
    exact (map_ne_zero_iff _ SZ).mpr (pow_ne_zero _ hp)
  · intro i
    rw [afz,afz,← map_mul]
    apply congrArg j8
    unfold numerator
    split_ifs with hinit
    · unfold cK
      rw [map_mul,MvPolynomial.eval_X,mul_comm]
      rfl
    · let E :=MvPolynomial.eval (jet S:Fin 4→ao[X])
      change E (_ *(_^_ *_))= _
      rw [map_mul,map_mul,map_pow,MvPolynomial.eval_C]
      change _ *(cK (separant f) S^(L - i.val) *
        cK (azv f i.val) S)= _
      rw [cM3 hf S hon hr,ajW]
      have hinv :Polynomial.C (↑i.val.factorial:ao)⁻¹ *
          Polynomial.C (↑i.val.factorial:ao)=1 := by
        rw [← map_mul,inv_mul_cancel₀ (ahA (i.isLt.trans hL)),map_one]
      have hpow:L - i.val+i.val=L:=Nat.sub_add_cancel i.isLt.le
      calc
        _=(Polynomial.C (↑i.val.factorial:ao)⁻¹*Polynomial.C (↑i.val.factorial:ao)) *
            ((cK (separant f) S^(L - i.val)*cK (separant f) S^i.val) *
              hasseDeriv i.val S) := by ring
        _ = _:= by rw [hinv,one_mul,← pow_add,hpow,hden]
private abbrev constants :ao →+* cH :=qY.comp Polynomial.C
private abbrev center :cH :=qY Polynomial.X
private theorem bds {L:ℕ} (S:K[X]) (hS:S.natDegree<L) (x :K) :
    (∑ j:Fin L,(constantCoeff x - center)^j.val *
      qY (hasseDeriv j.val (extend S)))=constantCoeff (S.eval x) := by
  let P:=(extend S).map constants
  let u:=constantCoeff x - center
  have hcoeff (n:ℕ) : (Polynomial.taylor center P).coeff n =
      qY (hasseDeriv n (extend S)) := by
    rw [Polynomial.taylor_coeff,Polynomial.hasseDeriv_map,ayL]
  have hd: (Polynomial.taylor center P).natDegree<L:= by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le).trans_lt hS
  have hev :P.eval (constantCoeff x)=constantCoeff (S.eval x) := by
    change ((S.map embed).map constants).eval (constantCoeff x)= _
    rw [Polynomial.map_map]
    exact Polynomial.eval_map_apply Tx.constantCoeff x
  calc
    _=(Polynomial.taylor center P).eval u:= by
      rw [Polynomial.eval_eq_sum_range' hd,← Fin.sum_univ_eq_sum_range]
      simp only [hcoeff,u]
      exact Finset.sum_congr rfl fun j _=>mul_comm _ _
    _=P.eval (constantCoeff x) :=Polynomial.taylor_eval_sub _ _ _
    _ = _:=hev
theorem djr {L:ℕ} {H :Shape} (D:GeoJets) (N :Fin L→GeoJets)
    (hD:yy D H) (hN : ∀ j,yy (N j) H) :
    ∃ C:a1h H,∀ S:K[X],S.natDegree<L →
      (An (extend S) D ≠0 ∧ ∀ j,An (extend S) (N j) =
        An (extend S) D *j8 (hasseDeriv j.val (extend S))) →
      C.ar5 S:= by
  let value (i:I) :gQ :=
    ∑ j:Fin L,MvPolynomial.C ((constantCoeff (node i) - center)^j.val)*N j
  have hvalue (i:I) :Supported H (value i) := by
    classical
    intro m hm
    unfold value at hm
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact crZ (cr1 (hN j)) _ m hj
  refine ⟨⟨D,value,cr1 hD,hvalue⟩,?_⟩
  intro S hS h
  refine ⟨h.1,fun i => ?_⟩
  let ev :=An (extend S)
  change ev (value i)=constantCoeff (S.eval (node i))*ev D
  have hc (a :cH) :ev (MvPolynomial.C a)=a :=MvPolynomial.eval_C a
  have he (j:Fin L) :ev (N j) =
      ev D *qY (hasseDeriv j.val (extend S)) :=h.2 j
  simp only [value,map_sum,map_mul,hc,he]
  calc
    _=ev D *(∑ j:Fin L,(constantCoeff (node i) - center)^j.val *
        qY (hasseDeriv j.val (extend S))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _=>mul_left_comm _ _ _)
    _ = _:= by rw [bds S hS,mul_comm]
end
end aKK
