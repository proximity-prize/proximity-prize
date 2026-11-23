import ProximityPrize.SubmissionLower.B5
import ProximityPrize.SubmissionLower.Z9GIThc
import ProximityPrize.SubmissionLower.ZFZJbJc
set_option Elab.async false
set_option autoImplicit true
namespace qbRvrcc
noncomputable section
open Polynomial MvPolynomial aR dN
open wH (qg)
open lB (bF yy abr abx Po
  ahA a9d afz SZ)
open bat (step Fy WB exb)
open Ex (C6)
open private step_bound cpc from ProximityPrize.SubmissionLower.Z9GIThc
open private bdn bpy anS from ProximityPrize.SubmissionLower.L
open private TaylorChart TaylorChart.mk TaylorChart.pullback TaylorChart.aWC L4 gKY ajW from ProximityPrize.SubmissionLower.B5
local notation "W" => MvPolynomial.weightedTotalDegree
private def thinRaw (g:af 4) :ℕ→af 4
  | 0=>MvPolynomial.C (Polynomial.C ((3:ℕ).factorial:ao))*MvPolynomial.X 3
  | k+1=>step true g k (thinRaw g k)
private def thinNumerator (g:af 4) (m:ℕ) (i:ℕ) :af 4 :=
  if hi:i<3 then MvPolynomial.X ⟨i,by omega⟩*separant g^m
  else
    MvPolynomial.C (Polynomial.C (↑i.factorial:ao)⁻¹) *
      (separant g^(m-(i-3))*thinRaw g (i-3))
private theorem raw_weight (w:Fin 4→ℕ) (δ:ℕ)
    (hs : ∀ i:Fin 3,w i.succ≤w i.castSucc+δ)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) (k :ℕ) :
    W w (thinRaw g k)≤w 3+k*(B - w 3+δ) := by
  induction k with
  | zero =>
    simpa only [thinRaw,zero_mul,add_zero] using
      (Po w _ (MvPolynomial.X 3)).trans (abx w 3)
  | succ k ih =>
    simpa only [thinRaw,Fy,ite_true,one_mul,Nat.add_mul,Nat.add_assoc] using
      step_bound true w δ hs hB hg ih k
private theorem numerator_weight (w:Fin 4→ℕ) (δ:ℕ)
    (hs : ∀ i:Fin 3,w i.succ≤w i.castSucc+δ) (hw : ∀ i,w i≤w 3)
    {g:af 4} {B m i:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hi:i≤ m+3) :
    W w (thinNumerator g m i)≤w 3+m*(B - w 3+δ) := by
  unfold thinNumerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      (Nat.add_le_add ((abx w _).trans (hw _))
        ((cpc g w m hg).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))))
  · let k :=i-3
    have hk :k≤ m:= by dsimp [k]; omega
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤(m - k)*(B - w 3)+(w 3+k*(B - w 3+δ)) :=
        Nat.add_le_add (cpc g w _ hg) (raw_weight w δ hs hB hg k)
      _=w 3+((m - k)+k)*(B - w 3)+k*δ:= by ring
      _≤_:= by
        rw [Nat.sub_add_cancel hk,Nat.mul_add,← Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right δ hk) _
private theorem thin_fits {g Q:af 4} {p:Shape} {L:ℕ}
    (h4 :4≤L) (hg:aO (shape g) p) (hp:bF p) (ht:p.t=1)
    (h : ∀ (w:Fin 4→ℕ) (δ B:ℕ),(∀ i:Fin 3,w i.succ≤w i.castSucc+δ) →
      (∀ i,w i≤w 3)→w 3≤B→W w g≤B →
      W w Q≤w 3+(L-4)*(B - w 3+δ)) :
    yy (bC Q) (P6_6.weightedChart L p) := by
  have hj:3≤p.j:= by simpa only [ht,mul_one] using hp.2
  have hb:1≤p.b:=(show 1≤3 by decide).trans (hj.trans hp.1)
  have hbQ:=h 1 0 p.b (fun _=> by simp) (fun _=>le_rfl) hb
    (by rw [weightedTotalDegree_one]; exact hg.1)
  have hjQ:=h Fin.val 1 p.j (fun _=>le_rfl) (fun i=>Nat.le_of_lt_succ i.isLt) hj
    (by rw [← C6]; exact hg.2.1)
  let w:Fin 4→ℕ:=Pi.single 3 1
  have htQ:=h w 1 p.t (fun i=> by fin_cases i <;> decide) (fun i=> by fin_cases i <;> decide)
    (by rw [ht]; decide) (by
      change W (Pi.single (3:Fin 4) 1) g≤p.t
      rw [weightedTotalDegree_piSingle]
      exact hg.2.2)
  simp only [weightedTotalDegree_one,Pi.one_apply,add_zero] at hbQ
  change W Fin.val Q≤3+(L-4)*(p.j-3+1) at hjQ
  rw [show p.j-3+1=p.j - 2 by omega] at hjQ
  have htop:Q.degreeOf 3≤1+(L-4) := by
    simpa only [w,weightedTotalDegree_piSingle,show w 3=1 by decide,ht,
      Nat.sub_self,zero_add,mul_one] using htQ
  have hindex :=(a9d Q).trans hjQ
  rw [P6_6.weightedChart,ite_eq_left ht]
  apply abr
  refine ⟨hbQ.trans (le_max_left _ _),?_,?_⟩
  · change qE Q≤_
    rwa [C6]
  · change Q.degreeOf 3≤ min (L-3) ((3+(L-4)*(p.j - 2))/3)
    exact le_min (htop.trans (by omega)) (by omega)
private theorem eval_raw_thin {g:af 4} {S:ao[X]}
    (hg:cK g S=0) (hl:separant (separant g)=0) (k :ℕ) :
    cK (thinRaw g k) S=cK (separant g) S^k*(derivative^[k+3]) S:= by
  let E :=MvPolynomial.eval (jet S:Fin 4→ao[X])
  have hE (P:af 4) :WB S P=E P:= by
    rw [show WB S P=Rl.Ve P S from rfl,
      Rl.bFl]
    rfl
  have hflow (P:af 4) :E (u6 g P)=E (separant g)*derivative (E P) := by
    simpa only [hE] using bpy S g P (by rw [hE]; exact hg)
  have hsep:E (pK (separant g))=derivative (E (separant g)) := by
    simpa only [hE,hl,map_zero,mul_zero,add_zero] using (bdn S (separant g)).symm
  change E (thinRaw g k)=E (separant g)^k*(derivative^[k+3]) S
  induction k with
  | zero =>
    simp only [thinRaw,E,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,pow_zero,
      one_mul,jet,ajW,zero_add]
    rfl
  | succ k ih =>
    rw [show k.succ+3=(k+3).succ by omega,Function.iterate_succ_apply']
    simp only [thinRaw,step,ite_true,map_sub,map_mul,map_natCast,hflow,hsep,ih]
    exact anS k (E (separant g)) _
private theorem thin_eval {g:af 4} {S:ao[X]} {m i:ℕ}
    (hg:cK g S=0) (hl:separant (separant g)=0) (hi:i≤ m+3) (hc:i<K1.p) :
    cK (thinNumerator g m i) S=cK (separant g^m) S*hasseDeriv i S:= by
  let E :=MvPolynomial.eval (jet S:Fin 4→ao[X])
  change E (thinNumerator g m i)=E (separant g^m)*hasseDeriv i S
  unfold thinNumerator
  split_ifs with hlo
  · rw [map_mul,MvPolynomial.eval_X,mul_comm]
    rfl
  · have hraw:=eval_raw_thin hg hl (i-3)
    change E (thinRaw g (i-3))=E (separant g)^(i-3)*(derivative^[i-3+3]) S at hraw
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt hlo),ajW] at hraw
    have hk :m-(i-3)+(i-3)=m:= by omega
    have hf :Polynomial.C (↑i.factorial:ao)⁻¹ *
        Polynomial.C (↑i.factorial:ao)=1 := by
      rw [← map_mul,inv_mul_cancel₀ (ahA hc),map_one]
    rw [map_mul,map_mul,MvPolynomial.eval_C,map_pow,map_pow,hraw]
    calc
      _=(Polynomial.C (↑i.factorial:ao)⁻¹*Polynomial.C (↑i.factorial:ao)) *
          ((E (separant g)^(m-(i-3))*E (separant g)^(i-3))*hasseDeriv i S) := by ring
      _ = _:= by rw [hf,one_mul,← pow_add,hk]
theorem d40 {L:ℕ} (h4 :4≤L) (hL:L≤K1.p)
    {g:af 4} {p:Shape} (hg:aO (shape g) p) (hp:bF p) (ht:0<p.t)
    (x a :P6.K) :
    ∃ D:GeoJets,yy D (P6_6.weightedChart L p) ∧
      ∀ S:P6.K[X],S.natDegree<L→cK g (extend S)=0→qg g (extend S) →
        (An (extend S) D =0↔S.eval x=a) := by
  by_cases hlin:p.t=1
  · let m:=L-4
    let T:TaylorChart L:=TaylorChart.mk (bC (separant g^m))
      (fun i=>bC (thinNumerator g m i))
    have hi (i:Fin L) :i.val≤ m+3:= by have :=i.isLt; dsimp [m]; omega
    refine ⟨TaylorChart.pullback T (L4 L x a),TaylorChart.aWC T ⟨?_,?_⟩ _,?_⟩
    · apply thin_fits h4 hg hp hlin
      intro w δ B _ _ _ hB
      exact (cpc g w m hB).trans
        ((Nat.mul_le_mul_left m (Nat.le_add_right _ _)).trans (Nat.le_add_left _ _))
    · intro i
      apply thin_fits h4 hg hp hlin
      intro w δ B hs hw h3 hB
      exact numerator_weight w δ hs hw h3 hB (hi i)
    · intro S hS hz hr
      have hgt: (shape g).t=1 := by
        have hle :=hg.2.2.trans_eq hlin
        have hpos : (shape g).t≠0:= by
          intro hzero
          apply hr
          change cK (separant g) (extend S)=0
          rw [show separant g=0 from pderiv_eq_zero_of_notMem_vars (by
            intro hm
            exact (mem_vars_iff_degreeOf_ne_zero.mp hm) hzero)]
          exact map_zero (MvPolynomial.eval (jet (extend S)))
        omega
      apply gKY T hS _ x a
      constructor
      · change An (extend S) (bC (separant g^m))≠0
        rw [afz,map_ne_zero_iff _ SZ]
        change MvPolynomial.eval (jet (extend S)) (separant g^m)≠0
        rw [map_pow]
        exact pow_ne_zero m hr
      · intro i
        change An (extend S) (bC (thinNumerator g m i))= _
        rw [afz,thin_eval hz (exb hgt) (hi i) (i.isLt.trans_le hL)]
        simp only [T,afz,map_mul]
  · simpa only [P6_6.weightedChart,ite_eq_right hlin] using atq.d40 hL hg hp ht x a
end
end qbRvrcc
