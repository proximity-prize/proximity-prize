import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.Zsty7Cb
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZWwTFfb
import ProximityPrize.SubmissionLower.Zsr715c
import ProximityPrize.SubmissionLower.Zh014Yc
import ProximityPrize.SubmissionLower.ZPThfKc
import ProximityPrize.SubmissionLower.ZNqW9Ld
import ProximityPrize.SubmissionLower.Ztd61Ce
import ProximityPrize.SubmissionLower.Z3sbwSc
import ProximityPrize.SubmissionLower.ZkT0QFc
import ProximityPrize.SubmissionLower.ZJObpKc
import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZArb4kb
import ProximityPrize.SubmissionLower.ZbvbtFa
set_option Elab.async false
open _root_ renaming Finset.sum_le_sum → zQk, Ideal.mem_span_singleton → zxV, Ideal.span → zye, IsFractionRing.injective → zxb, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.mul_left_comm → zZ0, Nat.pos_of_ne_zero → zOl, Nat.sub_add_cancel → zxt, Nat.zero_le → zD0, Polynomial.C → z1z, Polynomial.coeff_map → z0b, Polynomial.hasseDeriv → z75, Polynomial.map_zero → zgY, RingHom.ker → zdq
section
set_option autoImplicit true
namespace qqJLTVc
noncomputable section
open aR (Shape af aO shape qP)
open dN (GeoJets bC j8)
open vS (g9 tC)
open B8 (lS MH qK i9 bA1 aC0)
open Jq (jJ aoL)
open agM (a1Z Vw agj diagonal)
open NU (Admissible agJ LJ RW azm cru)
open aKL (RM)
open P6_6 (pair32 bf)
open qZqYIua (geoShape)
open qsnQ6jb (boxes aRQ a4d)
open MvPolynomial Finset
open private joint_admissible from ProximityPrize.SubmissionLower.Zsty7Cb
open private eqz from ProximityPrize.SubmissionLower.CE
open private alt aCd bT8 DB from ProximityPrize.SubmissionLower.BI
def c1 :Prop :=
  ∀ (g:GeoJets) (B:lS) (t:jJ),g≠0→(∀ i,agJ (B i)) →
    ∀ (n:ℕ) (a :Shape×ℕ),agJ a →
      a1Z a (geoShape g,0)=agj (Vw B t) n →
      (affineHilbertFunction (RM B (zye {qK g^2}) t) n:ℚ) =
        ((LJ (agj (Vw B t) n)).ncard:ℚ)-(LJ a).ncard
def c2 :Prop :=
  ∀ (a :Shape×ℕ) (d:Shape),agJ a →
    ∃ H :Polynomial ℚ,H.coeff 4=volumeDerivative d a ∧
      ∀ n:ℕ,aO d (agj a n).1→agJ (subtractHorizontal (agj a n) d) →
        H.eval (n:ℚ)=((LJ (agj a n)).ncard:ℚ) -
          (LJ (subtractHorizontal (agj a n) d)).ncard
private theorem cp6:slots.card=4 := by decide
private theorem dWF (J:Finset (Fin 5)) : ⇑(aoL J)=diagonal J:=rfl
private theorem strict_diagonal (B:lS) (hB : ∀ i,agJ (B i))
    (h0:B 0=(⟨5,4,1⟩,0)) (J:Finset (Fin 5)) :
    let a :=Vw B (diagonal J)
    a.1.j<a.1.b∧3*a.1.t<a.1.j∧2*a.2<a.1.t:= by
  let t:=diagonal J
  have ht:0<t 0:= by
    by_cases h: (0:Fin 5)∈J <;> simp [t,diagonal,h]
  change (∑ i,t i*(B i).1.j)<(∑ i,t i*(B i).1.b) ∧
    3*(∑ i,t i*(B i).1.t)<(∑ i,t i*(B i).1.j) ∧
    2*(∑ i,t i*(B i).2)<(∑ i,t i*(B i).1.t)
  rw [mul_sum,mul_sum]
  refine ⟨sum_lt_sum (fun i _=>zBI _ (hB i).1.1) ⟨0,mem_univ _,?_⟩,
    sum_lt_sum (fun i _ => ?_) ⟨0,mem_univ _,?_⟩,
    sum_lt_sum (fun i _ => ?_) ⟨0,mem_univ _,?_⟩⟩
  · rw [h0]
    exact Nat.mul_lt_mul_of_pos_left (by decide) ht
  · rw [zZ0]
    exact zBI _ (hB i).1.2
  · rw [h0,zZ0]
    exact Nat.mul_lt_mul_of_pos_left (by decide) ht
  · rw [zZ0]
    exact zBI _ (hB i).2
  · rw [h0,zZ0]
    exact Nat.mul_lt_mul_of_pos_left (by decide) ht
private theorem fitting_shift (a :Shape×ℕ) (d:Shape) (n:ℕ)
    (ha :a.1.j<a.1.b∧3*a.1.t<a.1.j∧2*a.2<a.1.t)
    (hn:d.b+d.j+d.t≤n) :
    aO d (agj a n).1∧agJ (subtractHorizontal (agj a n) d) ∧
      a1Z (subtractHorizontal (agj a n) d) (d,0)=agj a n:= by
  have hb:n*(a.1.j+1)≤n*a.1.b:=zBI n ha.1
  have hj:n*(3*a.1.t+1)≤n*a.1.j:=zBI n ha.2.1
  have ht:n*(2*a.2+1)≤n*a.1.t:=zBI n ha.2.2
  simp only [Nat.mul_add,Nat.mul_one] at hb hj ht
  rw [zZ0 n 3] at hj
  rw [zZ0 n 2] at ht
  have hb' : d.b≤n*a.1.b:= by omega
  have hj' : d.j≤n*a.1.j:= by omega
  have ht' : d.t≤n*a.1.t:= by omega
  refine ⟨⟨hb',hj',ht'⟩,⟨⟨?_,?_⟩,?_⟩,?_⟩
  · change n*a.1.j - d.j≤n*a.1.b - d.b
    omega
  · change 3*(n*a.1.t - d.t)≤n*a.1.j - d.j
    omega
  · change 2*(n*a.2)≤n*a.1.t - d.t
    omega
  · simp only [a1Z,subtractHorizontal,agj,Shape.plus,Shape.scale,Nat.add_zero,
      zxt hb',zxt hj',zxt ht']
private theorem square_degree (B:lS) (hB:Admissible B) (G:g9) (hG:G≠0) :
    RW B (zye {G^2}) slots =
      RW B (zye {G}) slots+RW B (zye {G}) slots := by
  have hr :IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal g9) (G^2)) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_bot]
    exact pow_ne_zero 2 hG
  have hd:MH (zye {G^2}) slots.card:= by
    rw [cp6]
    simpa only [i9,bot_sup_eq] using aC0 hr bA1
  have ha (x :g9) :x*G∈zye {G^2} ↔ x∈zye {G} := by
    rw [zxV,zxV]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨y,mul_right_cancel₀ hG (by linear_combination hy)⟩
    · rintro ⟨y,rfl⟩
      exact ⟨y,by ring⟩
  have he :i9 (zye {G^2}) G=zye {G} := by
    exact sup_eq_right.mpr
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self G (by decide)))
  simpa only [he] using eqz hB hd ha
private theorem bEc (h1 :c1) (h2 :c2) (B:lS) (hB : ∀ i,agJ (B i))
    (h0:B 0=(⟨5,4,1⟩,0)) (g:GeoJets) (hg:g≠0) (J:Finset (Fin 5)) :
    (affineHilbertPolynomial (RM B (zye {qK g^2}) (aoL J))).coeff 4 =
      volumeDerivative (geoShape g) (Vw B (diagonal J)) := by
  let a :=Vw B (diagonal J)
  let d:=geoShape g
  obtain ⟨H,hcoeff,hH⟩:=h2 a d (cru B hB _)
  have hEq:H=affineHilbertPolynomial (RM B (zye {qK g^2}) (aoL J)) := by
    apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=d.b+d.j+d.t)
    intro n hn
    obtain ⟨hle,hch,hcap⟩:=fitting_shift a d n (strict_diagonal B hB h0 J) hn
    exact (hH n hle hch).trans (h1 g B (aoL J) hg hB n _ hch (by rwa [dWF])).symm
  exact hEq ▸ hcoeff
private theorem polarized (B:lS) (d q g a b:Shape) (u v :ℕ)
    (h1 :B 1=(q,0)) (h2 :B 2=(g,1)) (h3:B 3=(a,u)) (h4 :B 4=(b,v)) :
    (∑ J∈slots.powerset,(-1 :ℚ)^(slots.card-J.card) *
      volumeDifference d (Vw B (diagonal J)))=signedVolume d q g a b u v := by
  change alt B slots (DB (d,0) azm)= _
  unfold slots
  rw [aCd _ (by decide),aCd _ (by decide),aCd _ (by decide)]
  have he : ({4} : Finset (Fin 5))=insert 4 ∅ := rfl
  rw [he,aCd _ (by decide),bT8,h1,h2,h3,h4,signed_volume_differences]
private theorem bHn (R:af 4) {r :Shape} (h:aO (shape R) r) :
    aO (geoShape (bC R)) r := by
  have hs :=MvPolynomial.support_map_subset j8 R
  refine ⟨(Finset.sup_mono hs).trans h.1,?_,?_⟩
  · have hj:=h.2.1
    change aR.qE R≤ r.j at hj
    rw [Ex.C6] at hj
    exact (Finset.sup_mono hs).trans hj
  · exact MvPolynomial.degreeOf_le_iff.mpr
      fun m hm=>((Dr.bHn h) m hm).2.2
private theorem uq (p r q:Shape) (ht:1<p.t) (h:aRQ p) :
    (pair32 true p r q:ℚ) =
      signedVolume r q (tC p) (qP (bf+1) p)
        (qP (bf+2) p) (bf+1) (bf+2) := by
  have hn:p.t≠1 := by omega
  unfold aRQ at h
  unfold pair32
  simp only [Bool.true_and,bne_iff_ne,ite_eq_left hn,ite_eq_left h,Int.cast_add,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  rfl
theorem of_children (h1 :c1) (h2 :c2) :qsnQ6jb.c4 := by
  intro R r q p hR hr hq _ ht hj
  let g:=bC R
  let B:=boxes q p
  have hB:Admissible B:=joint_admissible q p hq hj
  have h0:B 0=(⟨5,4,1⟩,0) :=rfl
  have hg:g≠0:=WI.agr hR
  have hG:qK g≠0 :=
    (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne hg
  have hs :=square_degree B hB (qK g) hG
  have hd:32*RW B (a4d R) slots =
      ∑ J∈slots.powerset,(-1 :ℚ)^(slots.card-J.card) *
        volumeDerivative (geoShape g) (Vw B (diagonal J)) := by
    have he :32*RW B (a4d R) slots =
        16*RW B (zye {qK g^2}) slots := by
      rw [hs]
      simp only [a4d,i9,bot_sup_eq,g]
      ring
    rw [he,RW]
    simp only [cp6]
    rw [show (2 :ℚ)^4=16 by norm_num,← mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num)]
    exact sum_congr rfl fun J _ =>
      congrArg (fun x :ℚ=>(-1 :ℚ)^(4-J.card)*x) (bEc h1 h2 B hB.1 h0 g hg J)
  rw [hd,derivative_differences B (geoShape g),
    polarized B (geoShape g) q (tC p) (qP (bf+1) p)
      (qP (bf+2) p) (bf+1) (bf+2) rfl rfl rfl rfl,
    uq p r q ht hj]
  exact signed_volume_mono (bHn R hr) hq (hB.1 2) (hB.1 3) (hB.1 4)
end
end qqJLTVc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape aO)
open yi (bF)

open P6_6
open private positiveRates from ProximityPrize.SubmissionLower.ZZZM2Ya
open private pos_bound from ProximityPrize.SubmissionLower.ZWwTFfb
private def Ig (i:Box) (thin:Bool) :Shape :=
  let Q:=caps i
  ⟨Q.b,Q.j,if thin then 1 else Q.t⟩
private theorem rate_at {i:Box} {thin:Bool} {b j B J:ℕ}
    (he :positiveRates (Ig i thin)=⟨b,j,0⟩)
    (hr :bgt i=⟨B,J,0⟩) (hb:b≤B) (hj:j≤J) :
    aO (positiveRates (Ig i thin)) (bgt i) :=
  he.symm ▸ hr.symm ▸ ⟨hb,hj,le_rfl⟩
local notation "rG" x "," y "," u "," v =>
  rate_at (b:=x) (j:=y) (B:=u) (J:=v) rfl rfl (by decide) (by decide)
private theorem selected_rates (i:Box) (thin:Bool) :
    aO (positiveRates (Ig i thin)) (bgt i) := by
  cases i <;> cases thin
  · exact rG 0x196e42814ba4a,0x122549d0c62372,0x196e61a06ac00,0x12254a276c2c00
  · exact rG 0x687e04f807f0,0x49b5a99ddbc34,0x196e61a06ac00,0x12254a276c2c00
  · exact rG 0x287b44fe4a2ca,0x11820ec595458d,0x287b4abd2c000,0x11821009d32000
  · exact rG 0x9a529b6fe02d,0x4687a5b419ed3,0x287b4abd2c000,0x11821009d32000
  · exact rG 0xbc53a3764a38,0x84e453f49b2ff,0xbc543dcb2c00,0x84e4572d5a800
  · exact rG 0x2f5e1a817413,0x2219551ad9358,0xbc543dcb2c00,0x84e4572d5a800
  · exact rG 0x5f7d83ed2207,0x449d0205136e8,0x5f7f37b39000,0x449d08e85c800
  · exact rG 0x1867cd612b26,0x11d7d275fa1d6,0x5f7f37b39000,0x449d08e85c800
  · exact rG 0x77857aa63c7,0x8e9cbb6e065e,0x779de2e1800,0x8e9e2c58e400
  · exact rG 0x2757192369d,0x29330654bf5a,0x779de2e1800,0x8e9e2c58e400
private theorem selected_chamber (i:Box) (thin:Bool) :bF (Ig i thin) := by
  cases i <;> cases thin <;> exact ⟨by decide,by decide⟩
theorem positive_fee (i:Box) {p r :Shape} (hs :JetShape r) (ht:0< r.t)
    (hp:aO p m6) (hpc:bF p) (hr :aO r (caps i)) :
    smallFee p r≤dot (bgt i) r := by
  let thin:=decide (r.t=1)
  let A:=Ig i thin
  have htA:r.t≤A.t∧(r.t=1↔A.t=1) := by
    by_cases he :r.t=1
    · simp [A,thin,Ig,he]
    · have hc:2≤(caps i).t:= by cases i <;> decide
      simp only [A,thin,Ig,decide_eq_false he,Bool.false_eq_true,ite_false]
      exact ⟨hr.2.2,by omega⟩
  have hch:=caps_chamber i
  have hA:bF A:=selected_chamber i thin
  have hbox :aO r.iU A:=⟨max_le hr.1 (hr.2.1.trans hch.1),hr.2.1,htA.1⟩
  have h:=selected_rates i thin
  exact (pos_bound hs ht hp hpc hA hbox htA.2).trans
    (z9f (z9f (ztf _ h.1)
      (ztf _ h.2.1)) (ztf _ h.2.2))
end P6_6_8_3
end
section
set_option autoImplicit true
namespace P6_6_8_3
open aR (Shape)
open P6_6
open P6_6_8 (sharedOrder)
private def z (b j:ℕ) :Shape :=⟨b,j,0⟩
theorem empty_b:CompanionTest oL (z 133 0) (sharedOrder oL) :=
  reject (chunks :=[([42,1,1,2],0x129c455607ad),([2,2,2,2],0x22e613db7e8),
    ([2,2,2,2],0x11a6921f9b4),([2,2,2,4],0x324aa05c36)])
    (len:=72) (value :=0x16175a56157f) ⟨rfl,rfl,rfl,rfl,trivial⟩ rfl rfl rfl (by decide)
theorem empty_j:CompanionTest oL (z 1 36) (sharedOrder oL) :=
  reject (chunks :=[([42,1,1,1],0x12388da73f17),([1,1,1,1],0x12af82a64ac),
    ([1,1,1,1],0xe262596e6f),([1,1,1,1],0xa58c55dd73),
    ([1,1,1,1],0x7406ddeaba),([1,1,2,2],0x6bb5b4f660),
    ([2,2,2,2],0x3b9be3f698),([3,4,7],0x1068e1ac65)])
    (len:=89) (value :=0x161735d973bc)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trivial⟩ rfl rfl rfl (by decide)
theorem empty_corner :CompanionTest oL (z 91 29) (sharedOrder oL) :=
  reject (chunks :=[([44,3,4,4],0x14a7da2429fd),([5,6,7,13],0x15ec9694c4f)])
    (len:=86) (value :=0x1606a38d764c) ⟨rfl,rfl,trivial⟩ rfl rfl rfl (by decide)
end P6_6_8_3
end
section
set_option autoImplicit true
namespace P6_6_8_3
open aR (Shape aO)
open P6_6
open P6_6_8 (W0 sharedOrder Lw not_companion_down)
def c1 :Prop :=
  ∀ v,W0 v→v≠oL →
    CompanionTest v ⟨(caps (retainedBox v)).b+1,0,0⟩ (sharedOrder v)
def c2 :Prop :=
  ∀ v,W0 v→v≠oL →
    CompanionTest v ⟨1,(caps (retainedBox v)).j+1,0⟩ (sharedOrder v)
def c3:Prop :=
  ∀ v,W0 v→v≠oL→aO (bgt (retainedBox v)) (Lw v)
def c4 :Prop :=
  ∀ i r,JetShape r→ r.t=0→0< r.j→aO r (caps i) →
    smallFee m6 r≤dot (bgt i) r
private theorem fit_caps (i:Box) {r :Shape} (hs :JetShape r)
    (hb:r.b≤(caps i).b) (hj:r.j≤(caps i).j) :aO r (caps i) := by
  refine ⟨hb,hj,?_⟩
  rw [caps_top]
  have h:=hs.2.1
  omega
private theorem empty_covered {r :Shape} (hs :JetShape r)
    (hn : ¬ CompanionTest oL r (sharedOrder oL)) :
    aO r (caps .emptyWide)∨aO r (caps .emptyTall) := by
  have hb:r.b≤132 := by
    by_contra! h
    exact (not_companion_down (x :=⟨133,0,0⟩) ⟨h,zD0 _,zD0 _⟩ hn) empty_b
  have hj:r.j≤35:= by
    by_contra! h
    exact (not_companion_down (x :=⟨1,36,0⟩) ⟨hs.1,h,zD0 _⟩ hn) empty_j
  by_cases hj28:r.j≤28
  · exact Or.inl (fit_caps .emptyWide hs hb hj28)
  · have hb90:r.b≤90:= by
      by_contra! h
      exact (not_companion_down (x :=⟨91,29,0⟩)
        ⟨h,Nat.lt_of_not_ge hj28,zD0 _⟩ hn) empty_corner
    exact Or.inr (fit_caps .emptyTall hs hb90 hj)
private theorem nonempty_covered (h1 :c1) (h2 :c2) {v r :Shape} (hv :W0 v)
    (hne :v≠oL) (hs :JetShape r) (hn : ¬ CompanionTest v r (sharedOrder v)) :
    aO r (caps (retainedBox v)) := by
  apply fit_caps _ hs
  · by_contra! h
    exact (not_companion_down (x :=⟨(caps (retainedBox v)).b+1,0,0⟩)
      ⟨h,zD0 _,zD0 _⟩ hn) (h1 v hv hne)
  · by_contra! h
    exact (not_companion_down (x :=⟨1,(caps (retainedBox v)).j+1,0⟩)
      ⟨hs.1,h,zD0 _⟩ hn) (h2 v hv hne)
private theorem bGy (h4 :c4) (i:Box) (v :Shape) {r :Shape} (hs :JetShape r)
    (hr :aO r (caps i)) :smallFee (remainingChart v) r≤dot (bgt i) r := by
  by_cases ht:r.t=0
  · by_cases hj:r.j=0
    · simp only [smallFee,dot,hj,ht,Nat.mul_zero,Nat.add_zero]
      exact Nat.le_mul_of_pos_left r.b (by cases i <;> decide)
    · simpa only [smallFee,ite_eq_left ht] using h4 i r hs ht (zOl hj) hr
  · obtain ⟨hp,hpc⟩:=remaining_fits v
    exact positive_fee i hs (zOl ht) hp hpc hr
private theorem dot_le {a b:Shape} (h:aO a b) (r :Shape) :
    dot a r≤dot b r :=
  z9f (z9f (ztf _ h.1)
    (ztf _ h.2.1)) (ztf _ h.2.2)
private theorem empty_rates :
    aO (bgt .emptyWide) (Lw oL) ∧
    aO (bgt .emptyTall) (Lw oL) := by
  rw [show Lw oL=⟨0x39df27bb617ba,0x13bc369d92a21e,0x615f93175cf5⟩ from rfl]
  exact ⟨⟨by decide,by decide,by decide⟩,⟨by decide,by decide,by decide⟩⟩
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_6_8.c3:= by
  intro v hv r hs _ hn
  by_cases hz :v=oL
  · subst v
    rcases empty_covered hs hn with h | h
    · exact (bGy h4 .emptyWide oL hs h).trans (dot_le empty_rates.1 r)
    · exact (bGy h4 .emptyTall oL hs h).trans (dot_le empty_rates.2 r)
  · exact (bGy h4 (retainedBox v) v hs (nonempty_covered h1 h2 hv hz hs hn)).trans
      (dot_le (h3 v hv hz) r)
end P6_6_8_3
end
section
set_option autoImplicit true
namespace q7F4Ild

theorem proof :q2w4Sxc.c4 := by
  intro v hv hj
  obtain ⟨hb,hB,ht⟩:=grade_five hv hj
  cases v with
  | mk b j t =>
    change j=5 at hj
    change t=1 at ht
    subst j
    subst t
    change 2≤b at hb
    change b≤19 at hB
    interval_cases b
    · exact QE
    · exact at3
    · exact at4
    · exact at5
    · exact at6
    · exact at7
    · exact at8
    · exact at9
    · exact at10
    · exact at11
    · exact at12
    · exact at13
    · exact at14
    · exact at15
    · exact at16
    · exact at17
    · exact at18
    · exact at19
end q7F4Ild
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
set_option quotPrecheck false
namespace qYiv0Ea
theorem band6:qHde8fc.c6:=kc fun w f a h1 h2 h3=> by
  obtain ⟨h107_0_0,h107_0_1,h107_0_2,h107_0_3,h107_0_4,h107_0_5,h107_0_6,h107_0_7,h107_0_8,h107_0_9,h107_0_10,h107_0_11,h107_0_12,h107_0_13,h107_0_14,h107_0_15,h107_1_0,h107_1_1,h107_1_2,h107_1_3,h107_1_4,h107_1_5,h107_1_6,h107_1_7,h107_1_8,h107_1_9,h107_1_10,h107_1_11,h107_1_12,h107_1_13,h107_1_14,h107_1_16,h107_2_0,h107_2_1,h107_2_2,h107_2_3,h107_2_4,h107_2_5,h107_2_6,h107_2_7,h107_2_8,h107_2_9,h107_2_10,h107_2_11,h107_2_12,h107_2_13,h107_2_14,h107_2_15,h107_3_0,h107_3_1,h107_3_2,h107_3_3,h107_3_4,h107_3_5,h107_3_6,h107_3_7,h107_3_8,h107_3_9,h107_3_10,h107_3_11,h107_3_12,h107_3_13,h107_3_14,h107_3_15,h107_4_0,h107_4_1,h107_4_2,h107_4_3,h107_4_4,h107_4_5,h107_4_6,h107_4_7,h107_4_8,h107_4_9,h107_4_10,h107_4_11,h107_4_12,h107_4_13,h107_4_14,h107_5_12,h107_5_13,h107_6_12,h107_6_13,h107_7_12,h108_0_0,h108_0_1,h108_0_2,h108_0_3,h108_0_4,h108_0_5,h108_0_6,h108_0_7,h108_0_8,h108_0_9,h108_0_10,h108_0_11,h108_0_12,h108_0_13,h108_0_14,h108_0_15,h108_1_0,h108_1_1,h108_1_2,h108_1_3,h108_1_4,h108_1_5,h108_1_6,h108_1_7,h108_1_8,h108_1_9,h108_1_10,h108_1_11,h108_1_12,h108_1_13,h108_1_14,h108_1_15,h108_1_16,h108_2_0,h108_2_1,h108_2_2,h108_2_3,h108_2_4,h108_2_5,h108_2_6,h108_2_7,h108_2_8,h108_2_9,h108_2_10,h108_2_11,h108_2_12,h108_2_13,h108_2_14,h108_2_15,h108_2_16,h108_3_0,h108_3_1,h108_3_2,h108_3_3,h108_3_4,h108_3_5,h108_3_6,h108_3_7⟩:=d6_1
  obtain ⟨h108_3_8,h108_3_9,h108_3_10,h108_3_11,h108_3_12,h108_3_13,h108_3_14,h108_3_15,h108_4_13,h108_4_14,h108_5_13,h108_5_14,h108_6_13,h109_0_0,h109_0_1,h109_0_2,h109_0_3,h109_0_4,h109_0_5,h109_0_6,h109_0_7,h109_0_8,h109_0_9,h109_0_10,h109_0_11,h109_0_12,h109_0_13,h109_0_14,h109_0_15,h109_0_16,h109_1_0,h109_1_1,h109_1_2,h109_1_3,h109_1_4,h109_1_5,h109_1_6,h109_1_7,h109_1_8,h109_1_9,h109_1_10,h109_1_11,h109_1_12,h109_1_13,h109_1_14,h109_1_15,h109_1_16,h109_2_0,h109_2_1,h109_2_2,h109_2_3,h109_2_4,h109_2_5,h109_2_6,h109_2_7,h109_2_8,h109_2_9,h109_2_10,h109_2_11,h109_2_12,h109_2_13,h109_2_14,h109_2_15,h109_2_16,h109_3_14,h109_3_15,h109_4_14,h109_4_15,h109_5_14⟩:=d6_2
  have hf :f<(w - 56)/2+1 := by omega
  have ha :a<(w - 56 - 2*f)/3+1 := by omega
  interval_cases w <;> (conv at hf=>rhs; norm_num) <;> interval_cases f <;> (conv at ha=>rhs; norm_num) <;>
    interval_cases a <;> first | assumption | exact okE (by decide +kernel) | exact okL (by norm_num)
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qqzGq1b
theorem a_P6_6_1_1_5_6:qHde8fc.c6:=qYiv0Ea.band6
theorem kc:qHde8fc.c6:=a_P6_6_1_1_5_6
end qqzGq1b
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
set_option quotPrecheck false
namespace qYiv0Ea
theorem band7:qHde8fc.c7:=kc fun w f a h1 h2 h3=> by
  obtain ⟨h110_0_0,h110_0_1,h110_0_2,h110_0_3,h110_0_4,h110_0_5,h110_0_6,h110_0_7,h110_0_8,h110_0_9,h110_0_10,h110_0_11,h110_0_12,h110_0_13,h110_0_14,h110_0_15,h110_0_16,h110_1_0,h110_1_1,h110_1_2,h110_1_3,h110_1_4,h110_1_5,h110_1_6,h110_1_7,h110_1_8,h110_1_9,h110_1_10,h110_1_11,h110_1_12,h110_1_13,h110_1_14,h110_1_15,h110_1_16,h110_2_15,h110_2_16,h110_3_15,h110_3_16,h110_4_15,h111_0_0,h111_0_1,h111_0_2,h111_0_3,h111_0_4,h111_0_5,h111_0_6,h111_0_7,h111_0_8,h111_0_9,h111_0_10,h111_0_11,h111_0_12,h111_0_13,h111_0_14,h111_0_15,h111_0_16,h111_1_16,h111_2_16,h111_3_16⟩:=d7_1
  have hf :f<(w - 56)/2+1 := by omega
  have ha :a<(w - 56 - 2*f)/3+1 := by omega
  interval_cases w <;> (conv at hf=>rhs; norm_num) <;> interval_cases f <;> (conv at ha=>rhs; norm_num) <;>
    interval_cases a <;> first | assumption | exact okE (by decide +kernel) | exact okL (by norm_num)
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qLAc3id
theorem a_P6_6_1_1_5_7:qHde8fc.c7:=qYiv0Ea.band7
theorem kc:qHde8fc.c7:=a_P6_6_1_1_5_7
end qLAc3id
end
section
set_option autoImplicit true
namespace qeu0RUc
noncomputable section
open aR (af)
open we (eT fW vY graph)
open yz (oe S3 F3 ay3 oF Ny alT
  bsa)
open P6_6 (m6)
open P6_6_5 (Zl R4)
open qSCPCwb (Gf aap Ji Lx)
open MvPolynomial
open scoped BigOperators
open private cXL from ProximityPrize.SubmissionLower.BG
def c1 :Prop :=
  ∀ v,v≤ m6.t → ∀ (f :af 3),(∀ P∈yD f,aFK v f P) →
    Nonempty (am9 v f)
def c2 :Prop :=
  ∀ v (f :af 3),Irreducible f → ∀ (T:Gf v f) (L:eT 4),
    (∀ P∈yD f,L∉F3 f P) →
    ∀ P∈yD f,∀ y :oe,y∈S3 f P→eval y L=0 →
      let J:=ay3 (vY (fW f)) (graph f) T.cut L
      oF y∈J.minimalPrimes∧Lx f P≤Ny J y
def c3:Prop :=
  ∀ v,v≤ m6.t → ∀ n (f :Fin n→af 3),Zl v f →
    (∑ i,T7 v (alT (vY (fW (f i)))))≤(R4 v :ℝ)
private theorem gnH (hlocal:c2) {v :ℕ} {f :af 3}
    (hf :Irreducible f) (T:Gf v f) (S:am9 v f) :
    (↑(∑ P∈yD f,(Lx f P).toNat*(S.points P).card) :ℝ) ≤
      T7 v (alT (vY (fW f))) := by
  classical
  let J:=ay3 (vY (fW f)) (graph f) T.cut S.polynomial
  let points :=(yD f).biUnion S.points
  have hlocal' (P) (hP:P∈yD f) (y) (hy :y∈S.points P) :
      oF y∈J.minimalPrimes∧Lx f P≤Ny J y :=
    hlocal v f hf T S.polynomial S.proper P hP y (S.roots P hP y hy).1
      (S.roots P hP y hy).2
  have hmin : ∀ y∈points,oF y∈J.minimalPrimes := by
    intro y hy
    obtain ⟨P,hP,hyP⟩:=Finset.mem_biUnion.mp hy
    exact (hlocal' P hP y hyP).1
  have hd:Set.PairwiseDisjoint (↑(yD f)) S.points := by
    intro P hP P' hP' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    exact S.off_other_curves P hP P' hP' hne y hy (S.roots P' hP' y hy').1
  have hcost: (∑ P∈yD f,(Lx f P).toNat*(S.points P).card) ≤
      ∑ y∈points,(Ny J y).toNat := by
    change _ ≤ ∑ y∈(yD f).biUnion S.points,(Ny J y).toNat
    rw [Finset.sum_biUnion hd]
    apply zQk
    intro P hP
    calc
      _ = ∑ _∈S.points P,(Lx f P).toNat := by simp [z5A]
      _≤_:= by
        apply zQk
        intro y hy
        exact ENat.toNat_le_toNat (hlocal' P hP y hy).2 (bsa (hmin y
          (Finset.mem_biUnion.mpr ⟨P,hP,hy⟩))).ne
  exact (Nat.cast_le.mpr hcost).trans
    (bOc _ _ _ _ (cXL hf.ne_zero) T.graph_box T.cut_box S.support points hmin)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qSCPCwb.c1 := by
  classical
  intro v hv n f hf T
  have hcurve (i:Fin n) (P) (hP:P∈yD (f i)) :aFK v (f i) P :=
    gnI (hf.irreducible i) hP
  let S (i:Fin n) :=Classical.choice (h1 v hv (f i) (hcurve i))
  let e :aap n→ℕ:= fun a=>(Lx (f a.1) a.2).toNat
  let d:aap n→ℕ:= fun a=>((S a.1).points a.2).card
  have hdeg (a :aap n) (ha :a∈Ji f) :
      (d a :ℚ)=pN v (f a.1) a.2 :=
    (S a.1).card_eq a.2 (azC.mp ha)
  refine ⟨⟨e,d,?_,?_,?_,?_,?_⟩⟩
  · exact fun _ ha=>cHt (azC.mp ha)
  · exact fun _ ha=>dOv (azC.mp ha)
  · apply (Nat.cast_le (α:=ℝ)).mp
    rw [gw3,Nat.cast_sum]
    exact (zQk fun i _ =>
      gnH h2 (hf.irreducible i) (T i) (S i)).trans (h3 v hv n f hf)
  · intro a ha hn
    have hp:=azC.mp ha
    obtain ⟨hfin,hcard⟩:=eMx hp (hcurve _ _ hp) (T a.1) hn
    exact ⟨hfin,Nat.cast_le.mp (hcard.trans_eq (hdeg a ha).symm)⟩
  · intro a ha _
    have hp:=azC.mp ha
    have hC:=hcurve _ _ hp
    have hpos :0<d a := by
      have h: (0:ℚ)<(d a :ℚ) := by
        rw [hdeg a ha]
        exact affineDegree_pos hC.1.ne_top
      exact_mod_cast h
    have hone :1≤pN v (f a.1) a.2 := by
      rw [← hdeg a ha]
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    obtain ⟨Q,hprime,hdim,hb,hrec⟩:=dM0 hf a.1 a.2 (T a.1) hC hone
    exact ⟨Q,hprime,hdim,hpos,hb.trans_eq (hdeg a ha).symm,hrec⟩
end
end qeu0RUc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qML2oMa
noncomputable section
open aR (ao af cK)
open oR (qg separant)
open B7 ac1
open P6_6 (bf gZ tB)
open P6_6_5 (Fb)
open qXTnXJe (bjP)
open scoped Polynomial
open private cFt from ProximityPrize.SubmissionLower.CT
open private ddz from ProximityPrize.SubmissionLower.E3
private theorem cJ9 {F:Type} [Field F] (k :ao →+* F) {U:F[X]}
    (hU:U.natDegree<bf) (f :af 3) {D:ℕ} (hf :tB f D) :
    (jW k U f).natDegree≤D:= by
  classical
  unfold jW
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod: (∏ i∈m.support,z75 i.val U^m i).natDegree ≤
      m.sum (fun i e=>(gZ - i.val)*e) := by
    unfold Finsupp.sum
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply zQk
    intro i _
    change ((z75 i.val U)^m i).natDegree≤(gZ - i.val)*m i
    rw [z5A]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)
theorem dIK (f :af 3) (hf :Irreducible f)
    (hd:0<f.degreeOf 2) (hmax :f.degreeOf 2<K1.p)
    {D:ℕ} (hw:tB f D) (hchar :D <K1.p) (hwhole :Fb f) :
    ∃ P:Ideal jo,XP P (GZ f) (GZ (separant f)) ∧
      bjP P ∧ ∀ S:ao[X],S.natDegree≤gZ→qg 2 f S →
        Gp S∈MvPolynomial.zeroLocus ao P:= by
  let hp: (Jy f).IsPrime :=dIP f hf hd
  have hs :=ddz f hf hd hmax
  have hweight (U: (WE f)[X]) (hU:U.natDegree<bf) :
      (jW (Jb f) U f).natDegree<K1.p :=
    (cJ9 _ hU f hw).trans_lt hchar
  obtain ⟨U,hsmall,hsol,hinit⟩ :=
    cFt f bf (by decide) (by decide) hs hweight hwhole
  have length_le :bf≤aR.bf := by decide
  have hU:=hsmall.trans_le length_le
  obtain ⟨m,v,hv⟩:=bam.proof f
  let k :=Jb f
  let point :rS→WE f := fun a=>U.coeff a.val
  let P:=zdq (ajk k point)
  have hbase :=cS8 k point
  have himage :=ed4 f hf hd U hU hsol hinit
  have hD:y3 f (GZ (separant f))≠0 :=
    fun h=>hs ((aO5 f _).mp h)
  have hUreg:jW k U (separant f)≠0:= by
    intro hz
    have h:=bdt k U (CW f) (separant f)
    rw [hz,Polynomial.eval_zero,hinit,bvd] at h
    exact hD h.symm
  refine ⟨P,⟨RingHom.ker_isPrime _,?_,?_,hs,?_⟩,?_,?_⟩
  · exact fun h=>hf.ne_zero (fZd (h.trans (map_zero _).symm))
  · change (oV P).comap tO.toRingHom=Jy f
    rw [hbase,RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨GZ (v a),m,?_⟩
    have hU' : (U.map (newConstants :WE f →+* aar (WE f))).natDegree <
        aR.bf :=Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : jW (newConstants.comp k) (U.map newConstants) f=0:= by
      rw [← aVM,hsol,zgY]
    have hs' : ee (newConstants.comp k) amg
        (rD amg (U.map newConstants)) (separant f)≠0:= by
      rw [bJF]
      exact fun h=>hUreg ((zxb _ _) (h.trans (map_zero _).symm))
    have h:=hv (aar (WE f)) (newConstants.comp k) (U.map newConstants) amg
      hU' hsol' hs' a
    rw [bJF,bJF,z0b,
      ← bGY k U hU,← bGY k U hU] at h
    exact eee k U a m _ _ h
  · intro a ha
    change ajk k point (MvPolynomial.X a)=0
    rw [ajk,MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e :nW →+* WE f :=y3 f
    let g:nW →+* dF :=
      zY9 (rD PV (S.map QM))
    let b:ao →+* nW:=MvPolynomial.C.comp QM
    have hg (q:af 3) :g (GZ q)=algebraMap ao[X] dF (cK q S) := by
      rw [← drX,bTU]
      rfl
    have hreg' : g (GZ (separant f))≠0:= by
      rw [hg]
      exact fun h=>hreg.2 ((zxb _ _) (h.trans (map_zero _).symm))
    have hker :zdq e≤zdq g:= by
      rw [show zdq e=Jy f by
        ext q
        exact aO5 f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker,hg,hreg.1,map_zero]
    have hS' : (S.map QM).natDegree<aR.bf :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS:jW QM (S.map QM) f=0:= by
      simpa only [dhO,hreg.1,zgY,RingHom.comp_id] using
        (aVM (RingHom.id ao) QM S f).symm
    have hrecU (a :rS) :
        e (GZ (separant f))^m*point a=e (GZ (v a)) := by
      have hc:=hv (WE f) k U (CW f) hU hsol
        (by rwa [hinit,bvd]) a
      rwa [hinit,bvd] at hc
    have hrecS (a :rS) :
        g (GZ (separant f))^m*QM (S.coeff a.val)=g (GZ (v a)) := by
      have hc:=hv dF QM (S.map QM) PV hS' hsolS
        (by rwa [bTU]) a
      rwa [bTU,z0b] at hc
    have hle :=d2y b e g hker (GZ (separant f)) m
      (fun a=>GZ (v a)) hD hreg' point (QM ∘ Gp S) hrecU hrecS
    intro q hq
    have hz :=hle hq
    change zOD (g.comp b) (QM ∘ Gp S) q=0 at hz
    have hqmap :zOD (g.comp b) (QM ∘ Gp S) =
        QM.comp (MvPolynomial.aeval (Gp S)).toRingHom:= by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b,g]
      · intro a
        simp
    rw [hqmap] at hz
    exact QM.injective (hz.trans (map_zero _).symm)
end
end qML2oMa
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
namespace qML2oMa
noncomputable section
open P6_6 P6_6_7 q6t08kb
open aR (af shape cK extend)
open Ex (X7 YN aQU bUq)
open oR (qg separant ang)
open B7 (GZ)
open BO (bfW)
open MvPolynomial
open scoped Polynomial
open private cBi from ProximityPrize.SubmissionLower.BF
open private b7n from ProximityPrize.SubmissionLower.B7
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
open private bqq from ProximityPrize.SubmissionLower.I
open private gxH from ProximityPrize.SubmissionLower.ZArb4kb
private theorem lower_irreducible {R:af 4} (hR:Irreducible R) (ht: (shape R).t=0) :
    Irreducible (X7 R) := by
  have hA:YN R=z1z (X7 R) := by
    have hd:=(aQU R).trans ht
    simpa only [ X7,Polynomial.leadingCoeff,hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
  have hC:=hA ▸ hR.map YN
  refine ⟨fun hu=>hC.not_isUnit (Polynomial.isUnit_C.mpr hu),?_⟩
  intro a b hab
  exact (hC.isUnit_or_isUnit (show z1z (X7 R)=z1z a*z1z b by
    rw [← Polynomial.C_mul,← hab])).imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp
private theorem lower_degree (R:af 4) : (X7 R).totalDegree≤(shape R).b:= by
  have h:=(Nat.le_add_right _ _).trans (b7n R (1 :Fin 4→ℕ))
  change (X7 R).weightedTotalDegree (1 :Fin 3→ℕ)≤R.weightedTotalDegree 1 at h
  change (X7 R).totalDegree≤R.totalDegree
  simpa only [weightedTotalDegree_one] using h
private theorem cY9 {R:af 4} {D:ℕ} (hR:tB R D) :
    tB (X7 R) D:= by
  intro m hm
  obtain ⟨u,hu,hc,hw⟩:=cBi R m hm
  have hle :=hw (fun i=>gZ - i.val)
  rw [← hc]
  apply (z3b _ _).trans (hR u hu)
  simpa only [Finsupp.weight_apply,smul_eq_mul,z5A,Fin.val_castSucc] using hle
private theorem regular_at (C:Context) (R:af 4) (ht: (shape R).t=0)
    {γ:P6.K} (hγ:γ∈regular C R) :
    γ∈C.Δ∧qg 2 (X7 R) (extend (C.s γ)) := by
  classical
  have hs :=Finset.mem_filter.mp hγ
  have hz :=Finset.mem_filter.mp hs.1
  refine ⟨hz.1,?_,hs.2⟩
  rw [← bUq R _ ht]
  exact bfW hz.2 (orderAt_ord C R γ)
theorem proof :q6t08kb.c3:= by
  classical
  intro C R l ell h hw
  dsimp only
  rcases h with ⟨⟨hR,hshape,hweight⟩,hguard,ht,_⟩
  let f :=X7 R
  let Γ:=regular C R
  by_cases hΓ:Γ.Nonempty
  · have hreg {γ} (hγ:γ∈Γ) :=regular_at C R ht hγ
    obtain ⟨γ,hγ⟩:=hΓ
    have htop:0<f.degreeOf 2 := by
      by_contra! hz
      have hn: (2 :Fin 3)∉f.vars := by
        rw [mem_vars_iff_degreeOf_ne_zero,not_ne_iff]
        exact Nat.eq_zero_of_le_zero hz
      have hsep:separant f=0:=pderiv_eq_zero_of_notMem_vars hn
      have hz' : cK (separant f) (extend (C.s γ))=0:= by
        rw [hsep]
        exact map_zero (zY9 (aR.jet (extend (C.s γ))))
      exact (hreg hγ).2.2 hz'
    have htotal:f.totalDegree≤(shape R).b:=lower_degree R
    have hmax :f.degreeOf 2<K1.p :=
      ((degreeOf_le_totalDegree _ _).trans (htotal.trans
        (hguard.2.2.1.1.trans (Nat.sub_le 4025 _)))).trans_lt (by decide)
    obtain ⟨P,hp,hsupport,hall⟩:=dIK f (lower_irreducible hR ht) htop hmax
      (cY9 hweight) (by decide :aWx<K1.p) hw
    obtain ⟨hdim,hdeg⟩:=qXTnXJe.adr _ _ _ hp hsupport
    let b:=(lowerBody (shape R)).b
    have hb: ((GZ f).totalDegree :ℚ)≤b :=
      Nat.cast_le.mpr ((bqq f).trans (htotal.trans (le_max_left _ _)))
    have hm:=C.messages.mono (show Γ⊆C.Δ from fun _ hγ' => (hreg hγ').1)
    have hcap:ang C.w Γ C.s (gZ*b) := by
      apply gxH hm hp.prime hdim
      · intro η hη
        exact hall _ (Polynomial.natDegree_map_le.trans (hm.degree η hη)) (hreg hη).2
      · simpa only [Nat.cast_mul] using
          hdeg.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg gZ))
    rw [d1C,ee8]
    exact (P6_6_5.bfL hm hcap).trans
      (z3b (Nat.le_mul_of_pos_right _ (hshape.1.trans_le (le_max_left _ _))) _)
  · rw [show regular C R = ∅ from Finset.not_nonempty_iff_eq_empty.mp hΓ,Finset.card_empty,Nat.mul_zero]
    exact zD0 _
end
end qML2oMa
end
