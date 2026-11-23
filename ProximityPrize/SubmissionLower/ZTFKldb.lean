import ProximityPrize.SubmissionLower.ZK7Ye0a
import ProximityPrize.SubmissionLower.Zy3W3oe
set_option Elab.async false
open _root_ renaming Finset.range→cy,Finsupp.weight_apply→nX,MvPolynomial.X→lI,MvPolynomial.degreeOf_eq_sup→ oq,Polynomial.X→mD,Submodule→lV,True.intro→c9,qMHqmcc.appendGrades→lJ
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qlc9qed
noncomputable section
open Polynomial

open aR (ao)
open jA Rk
open acZ (bI3 cfL)



open private bno a8W byG from ProximityPrize.SubmissionLower.S
open scoped BigOperators
private theorem egb (F:jK) : (bC F).support=F.support :=
 MvPolynomial.support_map_of_injective F (IsFractionRing.injective ao[X] iP)
theorem mem_ambient {b h t F} : F∈Aw b h t ↔
  Jn b.box F∧gY F≤b.U∧ahb h (t+(b.box.b+b.box.j)*h) F:= by
 classical
 simp only [Aw,Submodule.mem_inf,Submodule.mem_comap,Submodule.restrictScalars_mem,
  cfL,bI3,MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
  MvPolynomial.weightedTotalDegree_piSingle]
 change (Jn b.box (bC F)∧gY (bC F)≤b.U)∧ahb h _ F↔_
 simp only [Jn,vC,lP,gY,MvPolynomial.weightedTotalDegree,
  oq,egb,and_assoc]
theorem b4I {F:jK} : gY (bC F)=gY F:= by
 classical
 simp only [gY,oq,egb]
private theorem trueCut_shift (H :ao[X]) (i t:ℕ) (F:jK)
    (hF:ahb H.natDegree t F) :
    ahb H.natDegree (t+(3*H.natDegree)*i) (Yd H i F) := by
  intro a ha
  obtain ⟨u,hu⟩:=bno F i a
  have hbefore :=hF _ (a8W ha)
  let w:mA→ℕ:= fun j=>j.elim 0 (fun k=>131071+H.natDegree - k.val)
  have hw (a :mA →₀ ℕ) :
      a.sum (fun j e=>j.elim 0 (fun k=>(131071+H.natDegree - k.val)*e)) =
        Finsupp.weight w a := by
    rw [nX]
    congr 1
    funext j e
    cases j <;> simp [w,Nat.mul_comm]
  rw [hw,byG w rfl] at hbefore
  rw [hw]
  have hc: ((Yd H i F).coeff a).natDegree ≤
      (H^(3*i)).natDegree+(F.coeff (Finsupp.single none i+a)).natDegree := by
    simp only [Yd,← aIY,MvPolynomial.coeff_C_mul,hu]
    exact natDegree_mul_le.trans
      (Nat.add_le_add_left (natDegree_mul_C_le _ _) _)
  have hp: (H^(3*i)).natDegree≤(3*H.natDegree)*i:= by
    exact natDegree_pow_le.trans_eq (by ring)
  omega
private theorem sum_coeffs (a :mA →₀ ℕ) (w:Fin 3→ℕ) :
   a.sum (fun i e=>i.elim 0 (fun j=>w j*e)) =
     w 0*a (some 0)+w 1*a (some 1)+w 2*a (some 2) := by
 rw [Finsupp.sum_fintype _ _ (by intro i; cases i <;> simp),Fintype.sum_option,
   Fin.sum_univ_three]
 simp
end
end qlc9qed
end
section
set_option autoImplicit true
namespace qPQ4nYa
noncomputable section
open aR (ao)
open Rj
open qlc9qed (Bank)
open MvPolynomial
def FF (b:Bank) (e :Exp) :Prop :=
 e.weight BU≤b.box.b∧e.weight indexWeight≤b.box.j∧e (some 2)≤b.box.t
def apR (b:Bank) :lV ao Flat :=restrictSupport ao {e | FF b e}
def origin (b:Bank) :Flat →ₗ[ao] Flat :=
 (weightedTruncation oH b.m).comp J6.toLinearMap
def originRange (b:Bank) :lV ao Flat :=
 LinearMap.range ((origin b).domRestrict (apR b))
def offset (b:Bank) (k :ℕ) :ℤ:=(k :ℤ) - b.box.j
def TO (b:Bank) (q k :ℕ) :Set Exp :=
  {e | FF b e∧e.weight BU=q ∧
    (e none :ℤ)-(e.weight indexWeight:ℤ)=offset b k}
def Block (b:Bank) (q k :ℕ) :lV ao Flat :=
 restrictSupport ao (TO b q k)
def af3 (b:Bank) (q k :ℕ) :Block b q k →ₗ[ao] Flat :=
 (origin b).domRestrict (Block b q k)
def iO (b:Bank) (q:ℕ) :ℕ:=min q b.box.j
def Ic (b:Bank) (q:ℕ) (g:ℤ) :ℤ:=(b.m:ℤ) - q - g
def pT (b:Bank) (q:ℕ) (g:ℤ) (i:Fin 3) :Flag :=
 let d:ℤ:=iO b q
 ![⟨0,-g⟩,⟨d - b.box.t,2*d - b.box.j⟩,⟨0,Ic b q g⟩] i
def K6 (b:Bank) (q:ℕ) (p:kJ) :ℤ :=
 iO b q - ∑ j,(p j:ℤ)*yE j
def D8 (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) (i:Fin 3) :Flag :=
  ⟨(pT b q g i).iy - ∑ j,(p j:ℤ)*(Jd j i).iy,
    (pT b q g i).HE - ∑ j,(p j:ℤ)*(Jd j i).HE⟩
def cappedCumulative (d C:ℕ) (w:ℤ) :ℤ :=
  gd d w -
    (if C<d then gd (d-(C+1) :ℕ) (w - 2*((C:ℤ)+1)) else 0)
def Bb (b:Bank) (q:ℕ) (g:ℤ) :ℤ :=
 let d:=iO b q
 cappedCumulative d b.box.t b.box.j - cappedCumulative d b.box.t (min b.box.j (-g - 1))
def xR (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) :ℕ :=
  if Ic b q g≤0 then 0 else
    (Bb b q g - max 0 (max
      (m5 (iO b q) (pT b q g))
      (m5 (K6 b q p) (D8 b q g p)))).toNat
def rankBudget (b:Bank) (p:ℕ→ℕ→kJ) :ℕ :=
  ∑ q∈cy (b.box.b+1),∑ k∈cy (b.m+b.box.j),
    xR b q (offset b k) (p q k)
end
end qPQ4nYa
end
section
set_option autoImplicit true
namespace qzLARrc
noncomputable section
open aR (ao Shape)
open jA (kS mA)
open aFN (Slot)
open qlc9qed (Bank)
open scoped Polynomial BigOperators
def projectivity (k d e :ao) :kS :=
  let z :=algebraMap ao[X] kS mD
  algebraMap ao kS k*z /
    (algebraMap ao kS d+algebraMap ao kS e*z)
abbrev LocalCoeff (l:ℕ) :=ao[X] ⧸ Ideal.span {((mD:ao[X])^l)}
abbrev bjM (l:ℕ) :=MvPolynomial mA (LocalCoeff l)
def localParameter (l:ℕ) :LocalCoeff l:=Ideal.Quotient.mk _ mD
abbrev LocalSlot (a :Shape) (U:ℕ) :=
 Fin (a.b+a.j)×Fin (U + 1)×(Σ q:Fin (a.b+1),Slot a q.val)
def localColumn (a :Shape) (U:ℕ) (i:LocalSlot a U) :bjM (a.b+a.j) :=
  let t:=MvPolynomial.C (localParameter (a.b+a.j))
  let z :=lI (none :mA)
  let A:=lI (some 0:mA)
  let B:=lI (some 1 :mA)
  let C:=lI (some 2 :mA)
  let q:=i.2.2.1.val
  let c:=i.2.2.2.1.val
  let b:=i.2.2.2.2.val
  t^i.1.val*z^i.2.1.val*(z+t*A)^(q - c - b) *
    (A+t*B)^b*(B+t*C)^c
def localImage (a :Shape) (U:ℕ) :lV ao (bjM (a.b+a.j)) :=
 Submodule.span ao (Set.range (localColumn a U))
def derivativeIndex {a :Shape} {q:ℕ} (i:Slot a q) :ℕ :=
 i.2.val+2*i.1.val
def flagMatrix (a :Shape) (q:ℕ) (ν:ℤ) (w:ℕ) :
    Matrix (Slot a q) (Slot a q) ao :=
  fun r s =>
    if q - s.1.val - s.2.val≤w∧0≤ν+(derivativeIndex s :ℤ) ∧
        ν+(q:ℤ)+(derivativeIndex r :ℤ)<((a.b+a.j:ℕ) :ℤ) ∧
        r.1.val≤ s.1.val∧s.1.val - r.1.val≤ r.2.val then
      (Nat.choose s.1.val r.1.val :ao) *
        (Nat.choose s.2.val (r.2.val-(s.1.val - r.1.val)) :ao)
    else 0
def flagRank (a :Shape) (q:ℕ) (ν:ℤ) (w:ℕ) :ℕ:=(flagMatrix a q ν w).rank
def windowBudget (a :Shape) (U:ℕ) :ℕ :=
  ∑ q∈cy (a.b+1),∑ i∈cy (a.b+2*a.j),
    let ν:=(i:ℤ)-(a.j:ℤ)
    (U + a.b+1 - 2*q)*flagRank a q ν q +
      ∑ w∈cy q,flagRank a q ν w
def oneDebit (b:Bank) :ℕ:=(b.U + 1)*b.basePole+b.poleExcess
end
end qzLARrc
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open qMHqmcc (GG receipt)
local notation "az" => (receipt 2575 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl))
private theorem r1 :GG b11 20 4 :=⟨az,az,az,az,c9⟩
private theorem r2 :GG b11 24 4 :=⟨az,az,az,az,c9⟩
private theorem r3:GG b11 28 4 :=⟨az,az,az,az,c9⟩
private theorem r4 :GG b11 32 4 :=⟨az,az,az,az,c9⟩
private theorem r5:GG b11 36 4 :=⟨az,az,az,az,c9⟩
theorem f :GG b11 20 20 :=
 lJ (lJ (lJ (lJ r1 r2) r3) r4) r5
end qJrKOKe
end
