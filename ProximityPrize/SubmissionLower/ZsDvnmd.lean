import ProximityPrize.SubmissionLower.Z5cYAOe
import ProximityPrize.SubmissionLower.ZxReCna
import ProximityPrize.SubmissionLower.E
set_option Elab.async false
set_option autoImplicit true
namespace P1_6_7_3
noncomputable section
open Polynomial MvPolynomial K1 aR Ex dN wH lB Tx
open scoped BigOperators
open private atb.denominator from ProximityPrize.SubmissionLower.ZG8ydqc
open private numerator ZB aKK.Vi from ProximityPrize.SubmissionLower.Z5cYAOe
open private lB.denominator from ProximityPrize.SubmissionLower.ZceTCvc


local notation "W" => MvPolynomial.weightedTotalDegree
private def bIy (L:ℕ) (p:Shape) :Shape :=
  let j:=3+L*(p.j - 2)
  ⟨max (1+L*(p.b - 1)) j,j,min (L+1) (j/3)⟩
private theorem dMZ (L:ℕ) (f :af 4) (ht: (shape f).t=1) :
    let H :=bIy L (shape f).iU
    yy (bC (atb.denominator L f)) H ∧
      ∀ i:Fin L,yy (bC (numerator L f i.val)) H := by
  let p:=(shape f).iU
  have hpt:p.t=1 :=ht
  have hj:3≤p.j:= by
    have h:=(Tn f).2
    change 3*p.t≤p.j at h
    omega
  have hb:1≤p.b:=(by omega :1≤p.j).trans (Tn f).1
  have hbF:W 1 f≤p.b:= by
    rw [weightedTotalDegree_one]
    exact le_max_left _ _
  have hjF:W Fin.val f≤p.j:= by
    rw [← C6]
    exact le_rfl
  let w:Fin 4→ℕ:=Pi.single 3 1
  have hwF:W w f≤1 := by simpa only [w,weightedTotalDegree_piSingle,shape] using ht.le
  have hw3:w 3=1 := by decide
  have hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i,w i≤1 := by
    intro i
    fin_cases i <;> decide
  have pack (P:af 4) (hb' : W 1 P≤1+L*(p.b - 1))
      (hj' : W Fin.val P≤3+L*(p.j - 2))
      (ht' : W w P≤L+1) :yy (bC P) (bIy L p) := by
    apply abr
    refine ⟨?_,?_,?_⟩
    · change P.totalDegree≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree≤1+L*(p.b - 1)).trans (le_max_left _ _)
    · change qE P≤_
      rwa [C6]
    · change P.degreeOf 3≤ min _ ((3+L*(p.j - 2))/3)
      apply le_min
      · simpa only [w,weightedTotalDegree_piSingle] using ht'
      · have h:=(a9d P).trans hj'
        omega
  change yy (bC (atb.denominator L f)) (bIy L p) ∧
    ∀ i:Fin L,yy (bC (numerator L f i.val)) (bIy L p)
  constructor
  · apply pack
    · exact (ZB L 1 hbF).trans (Nat.le_add_left _ _)
    · have h:=ZB L Fin.val hjF
      change W Fin.val (atb.denominator L f)≤L*(p.j-3) at h
      exact h.trans ((Nat.mul_le_mul_left _ (by omega :p.j-3≤p.j - 2)).trans
        (Nat.le_add_left _ _))
    · have h:=ZB L w hwF
      rw [hw3,Nat.sub_self,Nat.mul_zero] at h
      exact h.trans (Nat.zero_le _)
  · intro i
    apply pack
    · simpa only [Pi.one_apply,add_zero] using
        aKK.Vi i.isLt.le 1 0 1 (fun _=> by simp) (fun _=>le_rfl) hb hbF
    · have h:=aKK.Vi i.isLt.le Fin.val 1 3 (fun _=> by rfl)
        (fun j:Fin 4=>Nat.le_of_lt_succ j.isLt) hj hjF
      change W Fin.val (numerator L f i.val)≤3+L*(p.j-3+1) at h
      rwa [show p.j-3+1=p.j - 2 by omega] at h
    · have h:=aKK.Vi i.isLt.le w 1 1 hshift hw (show w 3≤1 from hw3.le) hwF
      simpa only [hw3,Nat.sub_self,zero_add,Nat.mul_one,Nat.add_comm] using h
end
end P1_6_7_3
