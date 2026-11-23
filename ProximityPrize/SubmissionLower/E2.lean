import ProximityPrize.SubmissionLower.B9
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.B7
set_option Elab.async false
set_option autoImplicit true
section
namespace ak1
noncomputable section

open aR (Shape)

open scoped Polynomial BigOperators
abbrev ahD:Shape :=⟨6789,2300,1150⟩
abbrev Ga :Shape :=⟨6820,2300,1150⟩
end
end ak1
end
section
namespace ak1
noncomputable section
open K1 aR jA aFP
open scoped Polynomial BigOperators
private theorem bJx (f :ko)
    (hf :Irreducible f) (hb:0<vC f) (ht:vC f≤17)
    (hu:0<gY f) (htop:f.degreeOf (some 2)=0) :
    ∃ q:Lower,q≠0∧q.totalDegree≤2*gY f*vC f ∧
      H9 q≤(2*lP f+1)*gY f ∧
      ∀ (z :ao) (S:ao[X]),
        MvPolynomial.eval (ED (DI z) (jW S)) f=0 →
        MvPolynomial.eval (jW S) q=0:= by
  obtain ⟨g,hrel,hgu,hgb,hgj,htraj⟩:=bSd.b9v f hf hb (ht.trans (by decide)) htop
  obtain ⟨htot,hind⟩:=bRf.proof f g
  refine ⟨aGx f g,cAF hf hu hrel,?_,?_,fun z S hz =>
    cAG hu hz (htraj z S hz)⟩
  · calc
      _≤gY f*vC f+gY f*vC f :=
        htot.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgb))
      _ = _:= by ring
  · calc
      _≤gY f*lP f+gY f*(lP f+1) :=
        hind.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgj))
      _ = _:= by ring
end
end ak1
end
section
namespace att
open aR jA NR Rj
open MvPolynomial
open scoped Polynomial


open private aaH c4g from ProximityPrize.SubmissionLower.S
private theorem eGH (b:Bank) :
  Module.finrank ao (aTt b.box.b)≤b.avF:= by
 obtain ⟨p,hp⟩:=aaH cxP.proof HM.proof
  aw9.proof bzs.proof b
 apply (dFi b.box.b (fun q k=>xR q (offset k) (p q k)) ?_).trans hp
 intro q hq k hk
 have hB:b.box.b+1≤6821 := by cases b <;> decide
 exact (fTp q k).trans
  (c4g cxO.proof baj.proof (hq.trans_le hB) hk (p q k))
end att
end
section
namespace att
noncomputable section
open K1 aR jA

open scoped Polynomial BigOperators


private theorem bDY:NR.c4 :=
 aFO.of_children cxQ.proof cxR.proof
end
end att
end
