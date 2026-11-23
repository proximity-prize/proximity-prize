import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.DB
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.Zqd3kta
import ProximityPrize.SubmissionLower.ZhZv6fd
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.univ → zdB, MvPolynomial.C → znf, Nat.add_assoc → zVg, Nat.add_comm → zg2, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu, Nat.sub_self → zLF, Nat.zero_add → zbc, Polynomial → zM1, Polynomial.C → z1z
section
set_option autoImplicit true
section
namespace Ry
open aR (Shape)

open cS (ye order j3)

def bw (s e :Shape) :ℕ:=ye (order .ag s) e
def ahK (gH :ℕ) (p x y :Shape) :ℕ :=
 let s :=(p.plus x).plus y
 gH+bw (p.plus x) x+bw s y+j3 s.t
end Ry
end
end
section
set_option autoImplicit true
section
namespace Ke
noncomputable section
open Polynomial
open P2 (I K e9 jG mJ dw node p)
open I3 (YQ Reduced apb wX Er gap)
open cu (L FX Equation vm j9)
open MN (Ai)
open vq (Dx flatten separant)
open uk (pe zU wZ Tk adW af2)
open yW (cO)
open scoped BigOperators
abbrev ak9:=zM1 (MvPolynomial (Fin 2) (zM1 L))
structure Input where
 words :e9
 deleted:zJe I
 model :jG words deleted
 CF:zJe K
 family :mJ model CF
 block :L[X]
 bY:YQ model family block
 marks :zJe K
 marks_sub:marks⊆CF
 f :Equation
 regular : ∀ γ∈marks,apb f (model.label γ) (family.scalar γ)
 reduced:Reduced f
 lo:ℕ
 hi:ℕ
 lower :lo≤ model.iF.toNat
 upper :model.iF.toNat≤hi
 positive :0< model.iF.toNat
 quotient_pos :0<Er model.iF.toNat
 agreement_gap:wX hi<dw
 factorial_guard :Er lo+2<p
 beta_guard :P2.t<2*gap hi
 e :ℕ
 declared_sheets :3≤e
 sheet_bound:f.natDegree≤e
 v :ℕ
 agm:vm f v
 ddk :v<p
 representative :ak9
 aEA:representative.map (MvPolynomial.map (algebraMap (zM1 L) FX))=f
 HE : ∀ j m,(representative.coeff j).coeff m≠0 →
   ((representative.coeff j).coeff m).natDegree+j*wX hi<p
abbrev Input.w (J:Input) :ℕ:=J.model.iF.toNat
abbrev Input.d (J:Input) :ℕ:=wX J.hi
def Input.awm (J:Input) :L[X] :=J.block.map (frobenius L p)
def Input.HV (J:Input) :L[X] :=J.block*J.awm
def adn (J:Input) (i:Fin 2) :L[X] :=
 if i=0 then J.block else J.awm
def ar8 (_J:Input) (i:Fin 2) (g:K[X]) :pe[X] :=
 ((j9 g).map (if i=0 then RingHom.id L else frobenius L p)).map znf
def aPT (J:Input) (i:Fin 2) :pe[X] :=
  ar8 J i (J.model.factor*J.model.A₀) +
    C (MvPolynomial.X i)*ar8 J i (J.model.factor*J.model.A₁)
structure j7 (J:Input) where
 denominator :pe
 numerator :pe[X]
 ayD:denominator≠0
 bc6:denominator.totalDegree≤2*J.w
 af0 : ∀ j,(numerator.coeff j).totalDegree≤2*J.w
 numerator_width :numerator.natDegree<2*J.w
 congruences : ∀ i:Fin 2,(adn J i).map znf ∣
  aPT J i*numerator +
   C (MvPolynomial.X i*denominator)*ar8 J i J.model.Q
 unit_at_marks : ∀ γ∈J.CF,zU (J.model.label γ) denominator≠0
def a4K (J:Input) (i:ℕ) :FX :=
 (i.factorial:FX)⁻¹*(Dx^[i]) ((algebraMap L[X] FX J.HV)⁻¹)
def aj5 (J:Input) (B:j7 J) (r :ℕ) :Ai :=
  ∑ i∈Finset.range (r+1),znf (a4K J (r-i)) *
    (Tk B.denominator*af2 J.f r i -
      separant (flatten J.f)^(2*r-1)*adW B.numerator i)
def Uk {J:Input} (B:j7 J) :cO :=
 z1z (z1z (wZ B.denominator))
def uf (J:Input) (B:j7 J) :cO :=
 Uk B*z1z J.f.derivative
def test (J:Input) (B:j7 J) (r :ℕ) :cO :=
 z1z (MvPolynomial.optionEquivLeft FX (Fin 2) (aj5 J B r))
def lg (J:Input) (U:zJe K) (i:I) :zJe K:= by
 classical
 exact U.filter fun γ=>(J.family.scalar γ).eval (node i)=J.model.word i
end
end Ke
end
end
section
set_option autoImplicit true
namespace P6_6_8
open aR (Shape aO bY ceilDiv)
open yi (bF tD)
open nZ (j0 On Jg DC A9 ZT)
open P6_6
private abbrev resultBox :Shape :=⟨aPr,aWz,0⟩
private abbrev commonBox :Shape :=⟨aHc+aPr/tau,aM1+aWz/tau,0⟩
private def rH (x :Shape) :Shape :=
  if x.t=1 then ajN x.iU else bY (bf+4) x.iU
private def V0 (h:Shape) :Shape :=
  ⟨max (max h.b commonBox.b) (max h.j (commonBox.j+1)),max h.j (commonBox.j+1),max 1 h.t⟩
private theorem ceil_mono {a b:ℕ} (h:a≤b) (d:ℕ) :ceilDiv a d≤ ceilDiv b d :=
  Nat.div_le_div_right (zIu (zlr h d) 1)
private theorem fat_chart_mono {x y :Shape} (h:aO x y) (ht:x.t=y.t) :
    aO (rH x) (rH y) := by
  have hp:=On h
  by_cases h1 :y.t=1
  · rw [rH,rH,ite_eq_left (ht.trans h1),ite_eq_left h1]
    obtain ⟨hb,hj,_⟩:=hp
    refine ⟨?_,?_,?_⟩ <;> dsimp [ajN] <;> gcongr
  · rw [rH,rH,ite_eq_right (show x.t≠1 from ht.symm ▸ h1),ite_eq_right h1]
    exact DC _ hp
private theorem fat_chart_chamber (x :Shape) :bF (rH x) := by
  unfold rH
  split
  · exact ⟨le_max_right _ _,ZT _ _⟩
  · exact A9 _ _
private theorem fat_cut_mono {a b:Shape} (h:aO a b) :aO (V0 a) (V0 b) := by
  obtain ⟨hb,hj,ht⟩:=h
  refine ⟨?_,?_,?_⟩ <;> dsimp [V0] <;> gcongr
private theorem fat_cut_chamber {h:Shape} (hh:bF h) :bF (V0 h) := by
  refine ⟨le_max_right _ _,?_⟩
  change 3*max 1 h.t≤ max h.j (commonBox.j+1)
  rcases le_total 1 h.t with ht | ht
  · rw [max_eq_right ht]
    exact hh.2.trans (le_max_left _ _)
  · rw [max_eq_left ht]
    exact (show 3*1≤ commonBox.j+1 from by decide).trans (le_max_right _ _)
private theorem RQ {x y :Shape} (h:aO x y) (ht:x.t=y.t)
    (hx :3*x.t≤x.j) (hy :3*y.t≤y.j) :lY x≤lY y := by
  have hp:=On h
  have hh:=fat_chart_mono h ht
  have hc:=fat_cut_mono hh
  have xp:=Jg x hx
  have yp:=Jg y hy
  have xh:=fat_chart_chamber x
  have yh:=fat_chart_chamber y
  have xc:=fat_cut_chamber xh
  have yc:=fat_cut_chamber yh
  have hbig:bF commonBox :=⟨by decide,by decide⟩
  have hq:bF resultBox :=⟨by decide,by decide⟩
  have hd:=tD hp (j0 commonBox) hc hh yp hbig yc hbig xc xh
  have hdp:=tD hp (j0 commonBox) hc hp yp hbig yc hbig xc xp
  have hsing:=tD hp hp hh hh yp yp yh xp xh xh
  have hcurve :=tD hp (j0 resultBox) (j0 resultBox) hh yp hq hq hq hq xh
  have hpoint :=tD hp (j0 resultBox) (j0 resultBox) hp yp hq hq hq hq xp
  have hchartSq: (rH x).b^2≤(rH y).b^2 := by
    simpa only [pow_two] using zcp hh.1 hh.1
  have hbSq:x.b^2≤y.b^2 := by
    simpa only [pow_two] using zcp h.1 h.1
  dsimp only [lY]
  refine z9f (z9f (z9f ?_ ?_) ?_) le_rfl
  · refine z9f (z9f (z9f (z9f ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (zBI _ hd) _
    · exact ceil_mono hdp _
    · exact zcp (zBI _ hp.1) hchartSq
    · exact zcp (zBI _ hp.1) hh.1
  · by_cases hs :1<x.t
    · have hs' : 1<y.t:=ht ▸ hs
      simp only [ite_eq_left hs,ite_eq_left hs']
      exact z9f (z9f
        (ceil_mono (zcp (zBI 4 h.2.2) hsing) _)
        (zcp h.2.2 hbSq)) le_rfl
    · have hs' : ¬ 1<y.t:=ht ▸ hs
      simp only [ite_eq_right hs,ite_eq_right hs']
      exact le_rfl
  · exact ceil_mono (z9f (zBI P6.t hcurve)
      (zBI mV hpoint)) _
private theorem fat_at {x y :Shape} {n cap:ℕ} (hv :Valid x) (h:aO x y) (ht:x.t=y.t)
    (hy :3*y.t≤y.j) (hn:lY y=n) (hc:n≤ cap) :lY x≤ cap :=
  (RQ h ht hv.2.1 hy).trans (hn.le.trans hc)
theorem fat_bounds :
    (∀ x,Valid x→aO x ⟨24,7,1⟩→lY x≤earlyCap 1) ∧
    (∀ x,Valid x→aO x ⟨16,7,1⟩→lY x≤earlyCap 2/2) ∧
    (∀ x,Valid x→x.t=2→(aO x ⟨16,6,2⟩∨aO x ⟨10,7,2⟩) →
      lY x≤earlyCap 2) := by
  refine ⟨?_,?_,?_⟩
  · intro x hv h
    exact fat_at hv h (le_antisymm h.2.2 hv.1) (by decide) (n:=0x13408728ede0c7f) rfl (by decide)
  · intro x hv h
    exact fat_at hv h (le_antisymm h.2.2 hv.1) (by decide) (n:=0xcf66370fc4d089) rfl (by decide)
  · intro x hv ht h
    rcases h with h | h
    · exact fat_at hv h ht (by decide) (n:=0x234c69a6f148c96) rfl (by decide)
    · exact fat_at hv h ht (by decide) (n:=0x232fb3924a0c49f) rfl (by decide)
end P6_6_8
end
section
set_option autoImplicit true
namespace P6_6_8
open aR (Shape aO)
open P6_6
open scoped BigOperators
open private in_spend spend_partition from ProximityPrize.SubmissionLower.ZXrG2Fd
def c1 :Prop :=
  (¬ AdmissibleEarly ⟨3,8,1⟩) ∧
  ∀ j,3≤j→j≤7 → ¬ AdmissibleEarly ⟨edge j+1,j,1⟩
def c2 :Prop :=
  ∀ v,W0 v→FirstTest v (Cj v) ∧
    0<sharedOrder v∧sharedOrder v≤Cj v ∧
    dot (Lw v) (firstCaps v (Cj v))≤Cj v*laterCap v.t
def c3:Prop :=
  ∀ v,W0 v → ∀ r,JetShape r→aO r (firstCaps v (Cj v)) →
    ¬ CompanionTest v r (sharedOrder v)→smallFee (remainingChart v) r≤dot (Lw v) r
def c4 :Prop :=
  ∀ v,W0 v → ∀ r,JetShape r→aO r (firstCaps v (Cj v)) →
    ¬ CompanionTest v r (sharedOrder v)→0< r.t→aO r (remainingLiteral v) →
    ∃ k dR,0<k∧aO (v.scale k) Wk∧(CompanionTest v r k∨k=1) ∧
      selfFee v r k dR≤dot (Lw v) r
private theorem bez {x y z :Shape} (a :aO x y) (b:aO y z) :aO x z :=
  ⟨a.1.trans b.1,a.2.1.trans b.2.1,a.2.2.trans b.2.2⟩
private theorem bwU {n:ℕ} (a :Fin n→Shape) (S:zJe (Fin n))
    (ha : ∀ i,Valid (a i)) :wD a S=oL∨Valid (wD a S) := by
  classical
  induction S using Finset.induction_on with
  | empty=>exact .inl (by simp [Ds.wD,FI.oL])
  | insert i S hi ih =>
    right
    have he :wD a (insert i S)=(wD a S).plus (a i) := by
      simp only [Ds.wD,Shape.plus,Finset.sum_insert hi,zg2 (a i).b,
        zg2 (a i).j,zg2 (a i).t]
    rw [he]
    exact AJ.akw ih (ha i)
private theorem Z1 (h:c1) {v :Shape} (hv :v=oL∨Valid v)
    (ha :AdmissibleEarly v) :W0 v := by
  rcases hv with hz | hv
  · exact .inl hz
  obtain ⟨ht,hmin,hmax⟩:=hv
  have hj:v.j≤7:= by
    by_contra! hj
    exact h.1 (admissible_down (x :=⟨3,8,1⟩) ⟨by change 3≤v.b; omega,hj,ht⟩ ha)
  refine .inr ⟨⟨ht,hmin,hmax⟩,Nat.le_of_not_gt fun hb => ?_⟩
  exact h.2 v.j (by omega) hj (admissible_down (x :=⟨edge v.j+1,v.j,1⟩)
    ⟨hb,le_rfl,ht⟩ ha)
theorem c8J {v :Shape} (h:W0 v) :
    v.b≤24∧v.j≤7∧v.t≤2 ∧
      (v.t=2→aO v ⟨16,6,2⟩∨aO v ⟨10,7,2⟩) := by
  rcases h with rfl | ⟨hv,hb⟩
  · refine ⟨by decide,by decide,by decide,?_⟩
    intro h
    change 0=2 at h
    omega
  obtain ⟨b,j,t⟩:=v
  obtain ⟨ht,hmin,hmax⟩:=hv
  change b≤edge j at hb
  change 1≤t at ht
  change 3*t≤j at hmin
  change j≤3*b at hmax
  have h3:3≤j:= by omega
  have h7:j≤7:= by
    by_contra! h
    have he :edge j=0:= by
      simp only [edge,ite_eq_right (show j≠3 by omega),ite_eq_right (show j≠4 by omega),
        ite_eq_right (show j≠5 by omega),ite_eq_right (show j≠6 by omega),
        ite_eq_right (show j≠7 by omega)]
    omega
  change b≤24∧j≤7∧t≤2∧(t=2 →
    (b≤16∧j≤6∧t≤2)∨(b≤10∧j≤7∧t≤2))
  interval_cases j <;> simp [edge] at hb <;> omega
private theorem early_charge {n:ℕ} (a :Fin n→Shape) (S:zJe (Fin n))
    (ha : ∀ i,Valid (a i)) (hv :W0 (wD a S)) :
    (∑ i∈S,lY (a i))≤earlyCap (wD a S).t:= by
  let v :=wD a S
  have h:=fat_bounds
  change _≤earlyCap v.t
  obtain ⟨hb,hj,ht,hboxes⟩:=c8J hv
  change v.t≤2 at ht
  have sub (i) (hi:i∈S) :aO (a i) v :=in_spend a hi
  have charge (u:ℕ) (hu : ∀ i∈S,lY (a i)≤(a i).t*u) :
      (∑ i∈S,lY (a i))≤v.t*u:= by
    calc
      _ ≤ ∑ i∈S,(a i).t*u:=Finset.sum_le_sum hu
      _ = _:= by rw [← Finset.sum_mul]; rfl
  by_cases h0:v.t=0
  · have he :S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi =>
      Nat.not_succ_le_zero 0 ((ha i).1.trans ((sub i hi).2.2.trans_eq h0)))
    simp [he,h0,earlyCap]
  by_cases h1 :v.t=1
  · calc
      _≤v.t*earlyCap 1 :=charge _ fun i hi=> by
        obtain ⟨hbi,hji,hti⟩:=sub i hi
        have he : (a i).t=1 :=le_antisymm (hti.trans_eq h1) (ha i).1
        simpa only [he,one_mul] using h.1 (a i) (ha i) ⟨hbi.trans hb,hji.trans hj,he.le⟩
      _=earlyCap v.t:= by rw [h1,one_mul]
  · have h2 :v.t=2 := by omega
    have hb16:v.b≤16:=(hboxes h2).elim (·.1) (fun q=>q.1.trans (by decide))
    calc
      _≤v.t*(earlyCap 2/2) :=charge _ fun i hi=> by
        have hs :=sub i hi
        by_cases he : (a i).t=2
        · rw [he,show 2*(earlyCap 2/2)=earlyCap 2 by decide]
          exact h.2.2 (a i) (ha i) he ((hboxes h2).imp (bez hs) (bez hs))
        · have he' : (a i).t=1 := by
            have htop:=(ha i).1
            have htop' := hs.2.2
            omega
          simpa only [he',one_mul] using h.2.1 (a i) (ha i)
            ⟨hs.1.trans hb16,hs.2.1.trans hj,he'.le⟩
      _=earlyCap v.t:= by rw [h2]; rfl
private def debitCap (t:ℕ) :ℕ :=
  if t=0 then 0x60fab94f550300 else if t=1 then 0x5778f0f14cd2cc else
  if t=2 then 0x4e698046fc4436 else 0x45cde40f48d296
private theorem debit_row {t d:ℕ} (he :aIx t+aPd=d)
    (hc:d≤debitCap t) :aIx t+aPd≤debitCap t:=he.le.trans hc
local notation "debit!" tt "," dd=>debit_row (t:=tt) (d:=dd) rfl (by decide)
private theorem adx (t:ℕ) (ht:t≤16) :aIx t+aPd≤debitCap t:= by
  interval_cases t
  · exact debit! 0,0x60fab94f550300
  · exact debit! 1,0x5778f0f14cd2cc
  · exact debit! 2,0x4e698046fc4436
  · exact debit! 3,0x45cde40f48d296
  · exact debit! 4,0x3da87e7eb01215
  · exact debit! 5,0x35fae6360e1561
  · exact debit! 6,0x2ec764d516714e
  · exact debit! 7,0x280fa7f5079e73
  · exact debit! 8,0x21d5e3968fda70
  · exact debit! 9,0x1c1bd9495ae4f0
  · exact debit! 10,0x16e3aa7d3739e9
  · exact debit! 11,0x122f299de7d3e0
  · exact debit! 12,0xe0068b0e1f008
  · exact debit! 13,0xa5947cb48ca28
  · exact debit! 14,0x73bccc71fd0fc
  · exact debit! 15,0x4a9e217d29a8d
  · exact debit! 16,0x2a584c33b24d3
private theorem dUW {lo hi:ℕ} (h:lo≤hi) :debitCap hi≤debitCap lo:= by
  unfold debitCap
  split_ifs <;> omega
private theorem within_cap {u t bw:ℕ} (hu:u≤2) (ht:t≤16) (hle :u≤t)
    (hfee :bw=0∨u+1≤t∧bw=laterCap u) :
    earlyCap u+aIx t+aPd+bw≤gV:= by
  rw [zVg (earlyCap u)]
  rcases hfee with rfl | ⟨hpos,rfl⟩
  · exact (zlr (z3b ((adx t ht).trans (dUW hle)) _) _).trans
      (by interval_cases u <;> decide)
  · exact (zlr (z3b ((adx t ht).trans (dUW hpos)) _) _).trans
      (by interval_cases u <;> decide)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_6.c8:= by
  intro n a S ha hbox
  let v :=wD a S
  let w:=wD a (zdB \ S)
  change AdmissibleEarly v→_
  intro hadm
  have hv :W0 v :=Z1 h1 (bwU a S ha) hadm
  have he :=early_charge a S ha hv
  have htop: (wD a zdB).t=v.t+w.t:=congrArg Shape.t (spend_partition a S).symm
  have hu:=(c8J hv).2.2.1
  have ht: (wD a zdB).t≤16:=hbox.2.2
  have hle :v.t≤(wD a zdB).t:= by omega
  have Az (jX:ℕ) (hp:jX=0∨v.t+1≤(wD a zdB).t∧jX=laterCap v.t) :
      (∑ i∈S,lY (a i))+aIx (wD a zdB).t+aPd+jX≤gV :=
    (zlr (zlr (zlr he _) _) _).trans
      (within_cap hu ht hle hp)
  by_cases hw:w.t=0
  · exact ⟨0,.inl ⟨hw,rfl⟩,Az 0 (.inl rfl)⟩
  obtain ⟨hfirst,hell,horder,hcap⟩:=h2 v hv
  have hscale :aO (v.scale (sharedOrder v)) (v.scale (Cj v)) :=
    ⟨ztf _ horder,ztf _ horder,ztf _ horder⟩
  refine ⟨laterCap v.t,.inr ⟨Cj v,sharedOrder v,liftChoice v,Lw v,
    hfirst,hell,horder,bez hscale hfirst.2.2.1,hcap,?_⟩,
    Az _ (.inr ⟨by omega,rfl⟩)⟩
  intro r hjet hr
  exact ⟨fun _=>large_majorized v r hell,fun hn=>⟨h3 v hv r hjet hr hn,h4 v hv r hjet hr hn⟩⟩
end P6_6_8
end
section
set_option autoImplicit true
namespace qxJEhle
open Finset (Ico range sum_congr mem_range mem_Ico)
open aR (Shape)
open P6_6 (AdmissibleEarly Gq V7 ack gG)
open P6_6_8 (dNb pS aUJ)
open AJ (CL bOw)
open wV (aWp HY)
open private bgn eO4 ow integrate from ProximityPrize.SubmissionLower.Zqd3kta
open private clip eL3 bSj.aTY eNO bSj.ay9 total from ProximityPrize.SubmissionLower.E6
open private boa cUr from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
private def full (u j t:ℕ) (kA:ℕ×ℕ×ℕ) :ℕ :=
  HY (clip u 4026 kA.2.1) j t - HY (clip u 4026 kA.1) j t
private def loss (u j t:ℕ) (kA:ℕ×ℕ×ℕ) :ℕ :=
  if j≤kA.2.2∨clip u 4026 kA.2.1≤kA.2.2+1 then 0
  else
    let a :=max (clip u 4026 kA.1) (kA.2.2+1)
    let b:=clip u 4026 kA.2.1
    HY b j t - HY a j t -
      (b-a)*(HY (kA.2.2+1) j t - HY kA.2.2 j t)
private theorem clip_mono (u:ℕ) :Monotone (clip u 4026) := fun _ _ h =>
  zIu (min_le_min_left _ h) _
private theorem full_eq (u j t lo hi c:ℕ) (h:lo≤hi) :
    full u j t (lo,hi,c) = ∑ r∈Ico (clip u 4026 lo) (clip u 4026 hi),V7 r j t:= by
  change HY (clip u 4026 hi) j t - HY (clip u 4026 lo) j t= _
  simp only [bSj.aTY]
  exact eNO _ (clip_mono u h)
private theorem inert {r j t c:ℕ} (h:j≤ c) :
    V7 (min r c) j t=V7 r j t:= by
  simp only [bSj.ay9,total]
  refine sum_congr rfl fun z hz=>sum_congr rfl fun y hy=>sum_congr rfl fun x hx => ?_
  simp only [mem_range] at hz hy hx
  have hc:z+y + x≤ c:= by omega
  simp only [le_min_iff,hc,and_true]
private theorem add_loss_formula (a b c j t:ℕ) (hab:a≤b) (hcb:c+1≤b) :
    let C:= fun d=>HY d j t
    let q:=max a (c+1)
    let tail:=(b - q)*(C (c+1) - C c)
    C (c+1) - C (min a (c+1))+tail+(C b - C q - tail)=C b - C a := by
  intro C q tail
  have hqb:q≤b:=max_le hab hcb
  have ht:tail≤C b - C q:= by
    have ht:=cUr (cap:=c) (start:=q) ((Nat.le_succ c).trans (le_max_right a _)) (b - q) j t
    rw [Nat.add_sub_of_le hqb] at ht
    exact ht
  rw [zVg,zg2 tail,Nat.sub_add_cancel ht]
  rcases le_total a (c+1) with ha | ha
  · simp only [q,min_eq_left ha,max_eq_right ha]
    have h₁:C a≤C (c+1) :=boa j t ha
    have h₂:C (c+1)≤C b:=boa j t hcb
    omega
  · simp only [q,min_eq_right ha,max_eq_left ha,zLF,zbc]
private theorem add_loss (u j t lo hi c:ℕ) (h:lo≤hi) (hhi:hi≤4026) :
    aWp u 4026 j t (lo,hi,c)+loss u j t (lo,hi,c)=full u j t (lo,hi,c) := by
  have hp:=eL3 u 4026 j t lo hi c h
  have hf :=full_eq u j t lo hi c h
  by_cases hs :j≤ c∨clip u 4026 hi≤ c+1
  · rw [loss,ite_eq_left hs,Nat.add_zero,hp,hf]
    refine sum_congr rfl fun r hr => ?_
    rcases hs with hj | hh
    · exact inert hj
    · have hr' := (mem_Ico.mp hr).2
      rw [min_eq_left (show r≤ c by omega)]
  · have hc:c+1≤ clip u 4026 hi:=(lt_of_not_ge fun h' => hs (.inr h')).le
    have hlo:lo - u=clip u 4026 lo:= by simp only [clip,min_eq_right (h.trans hhi)]
    rw [loss,ite_eq_right hs,aWp]
    dsimp only
    rw [show min 4026 hi - u=clip u 4026 hi from rfl,hlo,min_eq_right hc]
    exact add_loss_formula _ _ _ _ _ (clip_mono u h) hc
private theorem balance (u j t start:ℕ) (bs :List (ℕ×ℕ×ℕ)) (h:ow start 4026 bs) :
    (bs.map (aWp u 4026 j t)).sum+(bs.map (loss u j t)).sum =
      full u j t (start,4026,0) := by
  induction bs generalizing start with
  | nil =>
    change start=4026 at h
    subst start
    simp [full]
  | cons kA rest ih =>
    rcases kA with ⟨lo,hi,c⟩
    obtain ⟨hstart,hle,_,htail⟩:=h
    subst start
    have hstop:=(integrate u j t 4026 hi rest htail).1
    have h₁:=add_loss u j t lo hi c hle hstop
    have h₂:=ih hi htail
    have h₃:full u j t (lo,hi,c)+full u j t (hi,4026,0)=full u j t (lo,4026,0) := by
      have ha :HY (clip u 4026 lo) j t≤HY (clip u 4026 hi) j t :=
        boa j t (clip_mono u hle)
      have hb:HY (clip u 4026 hi) j t≤HY (clip u 4026 4026) j t :=
        boa j t (clip_mono u hstop)
      simp only [full]
      omega
    simp only [List.map_cons,List.sum_cons]
    omega
private def quickCofactor (x :Shape) :ℕ :=
  if x.b≤4025∧x.j≤1710∧x.t≤570 then
    let j:=1710 - x.j
    let t:=570 - x.t
    full x.b j t (0,4026,0)-(bgn.map (loss x.b j t)).sum
  else 0
private theorem quickCofactor_eq (x :Shape) :quickCofactor x=Gq x := by
  rw [← aUJ]
  by_cases h:x.b≤4025∧x.j≤1710∧x.t≤570
  · simp only [quickCofactor,pS,ite_eq_left h]
    rw [← balance x.b (1710 - x.j) (570 - x.t) 0 bgn eO4,
      Nat.add_sub_cancel]
  · simp only [quickCofactor,pS,ite_eq_right h]
def mass (v :Shape) (start len:ℕ) :ℕ :=
  CL (fun i=>quickCofactor (v.scale (start+i+1))) len
private theorem mass_add (v :Shape) (start m n:ℕ) :
    mass v start (m+n)=mass v start m+mass v (start+m) n:= by
  simp only [mass,bOw,Finset.sum_range_add,zVg]
theorem appendMass {v :Shape} {n d m c len total:ℕ}
    (h:mass v 0 n=m) (hd:mass v n d=c)
    (hlen:n+d=len) (htotal:m+c=total) :mass v 0 len=total:= by
  rw [← hlen,mass_add,zbc,h,hd,htotal]
theorem exclude {v :Shape} {n m:ℕ} (hm:mass v 0 n=m)
    (hz :pS (v.scale (n+1))=0) (hn:n≤ack)
    (hlt:m<gG) : ¬ AdmissibleEarly v := by
  have hzero (i:ℕ) (hi:n≤ i) :Gq (v.scale (i+1))=0:= by
    have h:=zlr hi 1
    apply Nat.eq_zero_of_le_zero
    exact (dNb (x :=v.scale (n+1)) (y :=v.scale (i+1))
      ⟨ztf v.b h,ztf v.j h,
        ztf v.t h⟩).trans_eq ((aUJ _).symm.trans hz)
  have hs : (∑ i∈range n,Gq (v.scale (i+1)))=m:= by
    simpa only [mass,bOw,quickCofactor_eq,zbc] using hm
  intro h
  unfold AdmissibleEarly at h
  rw [FI.gw7 hzero hn,hs] at h
  exact Nat.not_le_of_lt hlt h
end qxJEhle
end
section
set_option autoImplicit true
namespace q33KzTa
open aR (Shape)
open wV (HY aWp)
open P6_6_8 (pS aUJ)
open private bgn from ProximityPrize.SubmissionLower.Zqd3kta
private def integral (a b c:ℕ) (C:ℕ→ℕ) :ℕ :=
  if b≤a then 0
  else if b≤ c+1 then C b - C a
  else if c+1≤a then (b-a)*(C (c+1) - C c)
  else C (c+1) - C a+(b-(c+1))*(C (c+1) - C c)
private theorem integral_eq (a b c:ℕ) (C:ℕ→ℕ) :
    integral a b c C =
      C (min b (c+1)) - C (min a (min b (c+1))) +
        (b - max a (c+1))*(C (c+1) - C c) := by
  by_cases hba :b≤a
  · simp only [integral,ite_eq_left hba,min_eq_right ((min_le_left b (c+1)).trans hba),
      zLF,Nat.sub_eq_zero_of_le (hba.trans (le_max_left a (c+1))),zero_mul,add_zero]
  simp only [integral,ite_eq_right hba]
  by_cases hbc:b≤ c+1
  · simp only [ite_eq_left hbc,min_eq_left hbc,min_eq_left (by omega :a≤b),
      Nat.sub_eq_zero_of_le (hbc.trans (le_max_right a (c+1))),zero_mul,add_zero]
  simp only [ite_eq_right hbc,min_eq_right (by omega :c+1≤b)]
  by_cases hca :c+1≤a
  · simp only [ite_eq_left hca,min_eq_right hca,max_eq_left hca,zLF,zero_add]
  simp only [ite_eq_right hca,min_eq_left (by omega :a≤ c+1),max_eq_right (by omega :a≤ c+1)]
private def bandMass (u j t:ℕ) :ℕ×ℕ×ℕ→ℕ
  | (lo,hi,c)=>integral (lo - u) (min 4026 hi - u) c (fun x=>HY x j t)
private theorem band_eq (u j t:ℕ) (kA:ℕ×ℕ×ℕ) :
    bandMass u j t kA=aWp u 4026 j t kA:= by
  obtain ⟨lo,hi,c⟩:=kA
  exact integral_eq (lo - u) (min 4026 hi - u) c (fun x=>HY x j t)
def stock (v :Shape) :ℕ :=
  if v.b≤4025∧v.j≤1710∧v.t≤570 then
    (bgn.map (bandMass v.b (1710 - v.j) (570 - v.t))).sum
  else 0
theorem stock_eq (v :Shape) :stock v=P6_6.Gq v := by
  have h:bandMass v.b (1710 - v.j) (570 - v.t) =
      aWp v.b 4026 (1710 - v.j) (570 - v.t) :=funext (band_eq _ _ _)
  rw [← aUJ]
  simp only [stock,pS,h]
end q33KzTa
end
