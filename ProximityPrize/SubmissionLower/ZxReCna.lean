import ProximityPrize.SubmissionLower.CU
import ProximityPrize.SubmissionLower.Z6sVZdb
set_option Elab.async false
set_option autoImplicit true
namespace bR8
noncomputable section
open Polynomial MvPolynomial K1 aR dN wH lB Tx
open Ex (C6)
open scoped BigOperators
open private denominator ZB aAA avh ajW from ProximityPrize.SubmissionLower.ZceTCvc




local notation "W" => MvPolynomial.weightedTotalDegree
private def VT (L:ℕ) (g:af 4) (n:ℕ) :af 4 :=
  if hn:n<4 then MvPolynomial.X ⟨n,hn⟩*denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial:ao)⁻¹) *
      (separant g^(2*(L - n))*su g n)
private theorem Vi {L n:ℕ} (hn:n≤L) (w:Fin 4→ℕ) (Δ d₀:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) (hw : ∀ i,w i≤d₀)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) :
    W w (VT L g n)≤d₀+2*L*(B - w 3)+L*Δ:= by
  unfold VT
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((abx w _).trans (hw _)) (ZB L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp:=(weightedTotalDegree_pow_le w (separant g) (2*(L - n))).trans
      (Nat.mul_le_mul_left _ ((aAA w g).trans (Nat.sub_le_sub_right hg _)))
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤2*(L - n)*(B - w 3)+(w 0+n*(2*(B - w 3)+Δ)) :=
        Nat.add_le_add hp (avh w Δ hshift hB hg n)
      _=w 0+2*(n+(L - n))*(B - w 3)+n*Δ:= by ring
      _≤_:= by
        rw [Nat.add_sub_of_le hn]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
private theorem cGH (L:ℕ) (g:af 4) (p:Shape) (hB:aO (shape g) p)
    (hp:bF p) (ht:0<p.t) :
    yy (bC (denominator L g)) (bY L p) ∧
      ∀ n≤L,yy (bC (VT L g n)) (bY L p) := by
  have hb:1≤p.b:= by have :=hp.1; have :=hp.2; omega
  have hj:3≤p.j:= by have :=hp.2; omega
  have h₁:W 1 g≤p.b:= by simpa only [shape,weightedTotalDegree_one] using hB.1
  have h₂:W Fin.val g≤p.j:= by simpa only [shape,C6] using hB.2.1
  let w:Fin 4→ℕ:=Pi.single 3 1
  have h₃:W w g≤p.t:= by simpa only [w,shape,weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i,w i≤1 := by
    intro i
    fin_cases i <;> decide
  have hw3:w 3=1 := by decide
  have fits (P:af 4) (hb' : W 1 P≤1+2*L*(p.b - 1))
      (hj' : W Fin.val P≤2*L*(p.j-3)+L+3)
      (ht' : W w P≤2*L*(p.t - 1)+L+1) :
      yy (bC P) (bY L p) := by
    apply abr
    refine ⟨?_,?_,?_⟩
    · change P.totalDegree≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree≤1+2*L*(p.b - 1)).trans (le_max_left _ _)
    · change qE P≤_
      rwa [C6]
    · change P.degreeOf 3≤ min _ _
      apply le_min
      · simpa only [w,weightedTotalDegree_piSingle] using ht'
      · have h:=(a9d P).trans hj'
        omega
  constructor
  · apply fits
    · exact (ZB L _ h₁).trans (Nat.le_add_left _ _)
    · exact (ZB L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h:=ZB L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro n hn
    apply fits
    · have h:=Vi hn 1 0 1 (fun _=> by simp) (fun _=>le_rfl) hb h₁
      change W 1 (VT L g n)≤1+2*L*(p.b - 1)+L*0 at h
      simpa only [mul_zero,add_zero] using h
    · have h:=Vi hn Fin.val 1 3 (fun _=> by rfl)
        (fun j:Fin 4=>Nat.le_of_lt_succ j.isLt) hj h₂
      change W Fin.val (VT L g n)≤3+2*L*(p.j-3)+L*1 at h
      simpa only [mul_one,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using h
    · have hwle :w 3≤p.t:=hw3.symm ▸ ht
      have h:=Vi hn w 1 1 hshift hw hwle h₃
      simpa only [hw3,mul_one,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using h
private theorem bnw (L:ℕ) (g:af 4) (S:ao[X])
    (hg:cK g S=0) (hr :qg g S) :
    An S (bC (denominator L g))≠0 ∧
      ∀ n≤L,n<K1.p →
        An S (bC (VT L g n)) =
          An S (bC (denominator L g))*j8 (hasseDeriv n S) := by
  have hp:cK (separant g) S≠0:=hr
  have hden:cK (denominator L g) S=cK (separant g) S^(2*L) :=
    map_pow (MvPolynomial.eval (jet S:Fin 4→ao[X])) _ _
  constructor
  · rw [afz]
    apply (map_ne_zero_iff _ SZ).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro n hn hc
    rw [afz,afz,← map_mul]
    apply congrArg j8
    unfold VT
    split_ifs
    · unfold cK
      rw [map_mul,MvPolynomial.eval_X,mul_comm]
      rfl
    · let E :=MvPolynomial.eval (jet S:Fin 4→ao[X])
      change E (_ *(_^_ *_))= _
      rw [map_mul,map_mul,map_pow,MvPolynomial.eval_C]
      change _ *(cK (separant g) S^(2*(L - n))*cK (su g n) S)= _
      rw [arh _ _ hg,ajW]
      have hinv :Polynomial.C (↑n.factorial:ao)⁻¹*Polynomial.C (↑n.factorial:ao)=1 := by
        rw [← map_mul,inv_mul_cancel₀ (ahA hc),map_one]
      have hpow:2*(L - n)+2*n=2*L:= by
        rw [← Nat.mul_add,Nat.sub_add_cancel hn]
      calc
        _=(Polynomial.C (↑n.factorial:ao)⁻¹*Polynomial.C (↑n.factorial:ao)) *
            ((cK (separant g) S^(2*(L - n))*cK (separant g) S^(2*n)) *
              hasseDeriv n S) := by ring
        _ = _:= by rw [hinv,one_mul,← pow_add,hpow,hden]
end
end bR8
