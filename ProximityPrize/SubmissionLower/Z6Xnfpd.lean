import ProximityPrize.SubmissionLower.ZNc08Oa
import ProximityPrize.SubmissionLower.ZZZuA2c
set_option Elab.async false
open _root_ renaming And.intro→ oq,Finset.range→aU,Finset.sum_congr→lJ,Finset.sum_le_sum→ oj,Finset.sum_sub_distrib→ oz,Int.natCast_nonneg→pG,IsCoprime→ ox,Module.finrank→ oY,Nat.le_div_iff_mul_le→ oZ,Nat.le_of_lt_succ→pL,Nat.mul_le_mul_left→ oy,Nonempty→nX,P5_7_1.Input→c9,P5_7_1.contactPowerAt→n5,Polynomial.C→lV,Polynomial.coeff_natDegree→ ov,Polynomial.map_mul→pz,True.intro→mD,cu.Equation→nI,cu.Shape→cy,cu.slots→lz,min_le_left→ oD,mul_le_mul_of_nonneg_left→pC,qMHqmcc.appendGrades→ oK
section
set_option autoImplicit true
namespace P5_7_1
noncomputable section
open Finset Polynomial MvPolynomial
open P5 (K p dw)
open cu (L ku FX Jet triangle vm j9 rD)
open DP (jF ad0)

open qQ (oU)
open Qt (aH3 gY bg4)
open baY (Bp)
open private bKE from ProximityPrize.SubmissionLower.D8
open private cer cTX from ProximityPrize.SubmissionLower.D8
open private ddI from ProximityPrize.SubmissionLower.A1
open private bGH Wb from ProximityPrize.SubmissionLower.A0
def aT2 (A h:ℕ) (s :cy) (E v W:ℕ) :ℕ :=
  ku s fun q j =>
    if q*(131071-h)≤W+j then
      Bp s.U v ((q-j)/E) (n5 A h s W - j)
    else 0
private def b4O (A h:ℕ) (s :cy) (E v W j:ℕ) :ℕ :=
 let r :=n5 A h s W - j
 (aH3 (131071-h) s.B W j - r*E)*lz s.U (r*v)
private theorem cJb (A h:ℕ) (s :cy) (E v W:ℕ)
  (hk :0<131071-h) (he :0<E) :
  (∑ j∈aU (s.J+1),b4O A h s E v W j)=aT2 A h s E v W:= by
 rw [aT2,← ddI]
 apply lJ rfl
 intro j _
 exact cTX _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem boi (A h:ℕ) (s :cy) (E v W:ℕ) (V:Submodule FX Jet)
    {f :nI} (hf :f≠0) (hE :E≤f.natDegree) (hv :v≤gY f)
    (hk :0<131071-h) (he :0<E)
    (hcaps : ∀ P∈V,oU P s)
    (hlead : ∀ P∈V,P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈V,P≠0→f^(n5 A h s W-P.natDegree)∣P.leadingCoeff) :
    oY FX V≤aT2 A h s E v W:= by
  have hrow {P:Jet} (hP:P∈V) (hn:P≠0) :
      P.leadingCoeff.natDegree+P.natDegree≤ s.B∧P.natDegree≤ s.J ∧
      vm P.leadingCoeff s.U:= by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree≠0:= by
      rw [ov,ov]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB,hJ,_⟩:=hcaps P hP _ _ ha
    refine ⟨hB,hJ,fun i => ?_⟩
    by_cases hi:P.leadingCoeff.coeff i=0
    · simp [hi]
    · rw [← ov] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cJb A h s E v W hk he]
  refine bGH (F:=FX) (A:=nI) V (b4O A h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r :=n5 A h s W - j
    apply cer _ (g:=f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact oy _ hE
    · rw [bg4 hf]
      exact oy _ hv
    · rintro c ⟨⟨P,hP⟩,rfl⟩ hc
      change P.coeff j≠0 at hc
      obtain ⟨hpV,hd⟩:=Wb.mp hP
      have hn:P≠0:= by
        intro hz
        exact hc (by simp [hz])
      have hj:P.natDegree=j :=
        le_antisymm (pL ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB,_,hseed⟩:=hrow hpV hn
      have hwidth :=hlead P hpV hn
      have hdiv :=hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree<_∧vm (P.coeff j) _∧_∣P.coeff j
      rw [← hj,ov,hj]
      refine ⟨?_,hseed,hdiv⟩
      have hd:=(oZ hk).2 hwidth
      unfold aH3
      omega
  · intro P hp
    by_cases hn:P=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
theorem bDM (A h:ℕ) (s :cy) (E v :ℕ) (hh:0<2*h) (hk :1≤131071-h) :
    (∑ W∈aU (s.m*A),aT2 A h s E v W)+jointGainAt A h s E v =
      triangle s.U*ku s (fun q j=>s.m*A+j-q*(131071-h)) := by
  have hswap (F:ℕ→ℕ→ℕ→ℕ) :
      (∑ W∈aU (s.m*A),ku s (F W)) =
        ku s (fun q j => ∑ W∈aU (s.m*A),F W q j) := by
    unfold ku
    rw [sum_comm]
    apply lJ rfl
    intro q _
    rw [sum_comm]
  simp only [aT2,jointGainAt]
  rw [hswap]
  simp only [ku,← sum_add_distrib,mul_sum]
  apply lJ rfl
  intro q _
  apply lJ rfl
  intro j hj
  have hjq:j≤q:=(pL (mem_range.mp hj)).trans (oD _ _)
  have hq:q≤q*(131071-h) := by simpa using oy q hk
  exact bKE (s.m*A) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
theorem emz (x :c9) :lo≤x.h∧x.h≤hi:= by
 obtain ⟨hl,hh⟩:=x.kA
 change (lo:ℤ)≤x.M.iF at hl
 change x.M.iF≤(hi:ℤ) at hh
 change lo≤x.M.iF.toNat∧x.M.iF.toNat≤hi
 omega
theorem poles (x :c9) :nX (Poles x) := by
  let M:=x.M
  let H :=x.H
  let σ:=frobenius L p
  rcases x.bY with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let A:=j9 (M.factor*M.A₀)
  let B:=j9 (M.factor*M.A₁)
  let Q:=j9 M.Q
  have hdet0:ox (Q*A) H := by
    simpa [Q,A,H,M,j9,mul_assoc] using hdet
  have hdet1 :ox (Q.map σ*A.map σ) (H.map σ) := by
    simpa [Q,A,H,M,j9,mul_assoc,σ,pz] using hdet'
  let D:jF x.h :=
    ⟨![H,H.map σ],![Q,Q.map σ],![A,A.map σ],![B,B.map σ],
      fun i=> by fin_cases i <;> first | exact hm | exact hm',
      fun i=> by fin_cases i <;> first | exact hd | exact hd',
      hcop,fun i=> by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  obtain ⟨crt⟩:=atp.dRH D
  refine ⟨⟨D,crt,rfl,rfl,rfl,rfl,rfl,?_,?_⟩⟩
  · intro i j
    fin_cases i
    · exact (hnode j).1
    · exact (hnode j).2
  · intro γ hγ i
    let z :=algebraMap K L (M.label γ)
    have hz :j9 (M.factor*M.wK γ)=A+(@lV L _) z*B:= by
      simp [A,B,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    obtain ⟨h₀,h₁,hr₀,hr₁⟩:=hmarks γ hγ
    fin_cases i
    · change ox (A+(@lV L _) z*B) H ∧
        H∣(A+(@lV L _) z*B)*j9 (x.F.scalar γ)+(@lV L _) z*Q
      rw [← hz]
      exact ⟨h₀,hr₀⟩
    · have hσ: (j9 (M.factor*M.wK γ)).map σ =
          A.map σ+(@lV L _) (z^p)*B.map σ:= by
        rw [hz,Polynomial.map_add,pz ,Polynomial.map_C]
        rfl
      change ox (A.map σ+(@lV L _) (z^p)*B.map σ) (H.map σ) ∧
        H.map σ∣(A.map σ+(@lV L _) (z^p)*B.map σ)*j9 (x.F.scalar γ) +
          (@lV L _) (z^p)*Q.map σ
      rw [← hσ]
      exact ⟨h₁,hr₁⟩
theorem aic {x :c9} {γ:K} (hγ:γ∈x.Γ) :
   (x.F.scalar γ).natDegree≤131071+x.h:= by
 rcases (x.F.mark γ hγ).aic with hz | hd
 · simp [hz]
 · change ((x.F.scalar γ).natDegree :ℤ)≤131071+x.M.iF at hd
   change (x.F.scalar γ).natDegree≤131071+x.M.iF.toNat
   omega
theorem necessary {x :c9} (P:Poles x) {s :cy} {W:ℕ} (hW:W<s.m*dw)
  {G:Jet} (hG:G∈P.rows s W) {γ:K} (hγ:γ∈x.Γ) :
  rD G (x.M.label γ) (x.F.scalar γ)=0:= by
 let B:=x.F.mark γ hγ
 have hd: (j9 (x.F.scalar γ)).natDegree≤131071+x.h:= by
  rw [j9,Polynomial.natDegree_map]
  exact aic hγ
 refine atp.dPr P.crt x.word P.nodes _ _ (P.marks γ hγ) hd B.bad.support
  B.bad.dw ?_ s W hW G hG
 intro i hit
 rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,B.scalar_hits i hit]
end
end P5_7_1
end
section
set_option autoImplicit true
namespace qPTjEYd
open Finset
open cu (ku)
open P5 (dw)
open P5_7_1 (jointGainAt ZN)
open Y2 (bg5)
open private deJ crN from ProximityPrize.SubmissionLower.D9
open private bfq from ProximityPrize.SubmissionLower.D9
def width (s :cy) (h:ℤ) (q j a :ℕ) :ℤ :=
 (s.m*dw:ℕ)+(j:ℤ)-(131071-h)*q - 2*h*(j+a :ℕ)
private theorem dma (s :cy) (h q j a :ℕ) (hh:h≤131071) :
  width s h q j a≤(↑(s.m*dw+j-q*(131071-h)-2*h*(j+a) :ℕ) :ℤ) := by
 rw [Nat.sub_sub]
 have cast_sub_le (x y :ℕ) : (x :ℤ)-y≤((x-y :ℕ) :ℤ) := by omega
 have hs :=cast_sub_le (s.m*dw+j) (q*(131071-h)+2*h*(j+a))
 unfold width
 push_cast [Nat.cast_sub hh] at hs ⊢
 linarith only [hs]
def powerCount (s :cy) (E v d:ℕ) :ℕ :=
 bg5 s v d (s.B/E+1-d)
theorem lt_powerCount (s :cy) (E v d a :ℕ) :
  a<powerCount s E v d↔a+d≤ s.B/E∧(a+d)*v≤ s.U:= by
 rw [powerCount,bfq]
 omega
private def bty (s :cy) (h:ℤ) (E v d:ℕ) :ℤ :=
 ∑ q∈aU (s.B+1),∑ j∈aU (s.J+1),∑ a∈aU (powerCount s E v d),
   if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*width s h q j a else 0
def phase (s :cy) (h:ℤ) (E v d:ℕ) :ℤ :=
  ∑ a∈aU (powerCount s E v d),(lz s.U ((a+d)*v) :ℤ) *
    ∑ j∈aU (min (s.J+1) (s.B+1-E*(a+d))),
      ∑ q∈Ico (j+E*(a+d)) (s.B+1),width s h q j a
private theorem position (s :cy) (h E v q j:ℕ) (hh:h≤131071)
    (he :0<E) (hq:q≤ s.B) (hj:j≤q) :
    let c:= fun a=>lz s.U (a*v)
    let x :=s.m*dw+j-q*(131071-h)
    let g:=(q-j)/E
    let f := fun d a=>(c (a+d) :ℤ)*width s h q j a
    (∑ a∈aU (powerCount s E v 0),if j+E*(a+0)≤q then f 0 a else 0) -
      (∑ a∈aU (powerCount s E v 1),if j+E*(a+1)≤q then f 1 a else 0) ≤
    (↑((∑ a∈aU g,(c a-c (a+1))*(x-2*h*(j+a)))+c g*(x-2*h*(j+g)) :ℕ) :ℤ) := by
  dsimp only
  let g:=(q-j)/E
  let c:= fun a=>lz s.U (a*v)
  let f := fun d a=>(c (a+d) :ℤ)*width s h q j a
  have step (a :ℕ) :c (a+1)≤ c a :=
    deJ _ (Nat.mul_le_mul_right v (by omega))
  have hz (d a :ℕ) (ha :powerCount s E v d≤a) (hg:a+d≤g) :f d a=0:= by
    have hcap:g≤ s.B/E :=Nat.div_le_div_right (by omega)
    have hout : ¬ (a+d)*v≤ s.U:= fun hs =>
      (Nat.not_lt_of_ge ha) ((lt_powerCount s E v d a).2 ⟨hg.trans hcap,hs⟩)
    simp [f,c,lz ,hout]
  have hdiv (a d:ℕ) :j+E*(a+d)≤q↔a+d≤g:= by
    rw [oZ he,Nat.mul_comm (a+d) E]
    omega
  have reform (d L:ℕ) (hd : ∀ a,a<L↔a+d≤g) :
      (∑ a∈aU (powerCount s E v d),if j+E*(a+d)≤q then f d a else 0) =
        ∑ a∈aU L,f d a := by
    simp only [hdiv,← hd]
    exact (crN L _ (fun a ha hb=>hz d a ha ((hd a).1 hb))).symm
  change (∑ a∈aU (powerCount s E v 0),if j+E*(a+0)≤q then f 0 a else 0) -
    (∑ a∈aU (powerCount s E v 1),if j+E*(a+1)≤q then f 1 a else 0)≤_
  rw [reform 0 (g+1) (fun a=> by omega),reform 1 g (fun a=> by omega),
    sum_range_succ,add_sub_right_comm,← oz ,Nat.cast_add,Nat.cast_sum]
  apply add_le_add
  · apply oj
    intro a _
    simp only [f,Nat.add_zero,← sub_mul,← Int.ofNat_sub (step a),Nat.cast_mul]
    exact pC (dma s h q j a hh) (pG _)
  · simp only [f,Nat.add_zero,Nat.cast_mul]
    exact pC (dma s h q j g hh) (pG _)
private theorem extend (s :cy) (h:ℤ) (E v d q:ℕ) :
   (∑ j∈aU (min q s.J+1),∑ a∈aU (powerCount s E v d),
     if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*width s h q j a else 0) =
   ∑ j∈aU (s.J+1),∑ a∈aU (powerCount s E v d),
     if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*width s h q j a else 0:= by
 apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
 intro j hj hnot
 simp only [mem_range,Nat.lt_succ_iff,le_min_iff] at hj hnot
 apply sum_eq_zero
 intro a _
 rw [ite_eq_right (by omega)]
private theorem c3Z (s :cy) (h:ℤ) (E v d:ℕ) :
    bty s h E v d=phase s h E v d:= by
  let f := fun q j a=>if j+E*(a+d)≤q then
    (lz s.U ((a+d)*v) :ℤ)*width s h q j a else 0
  calc
    bty s h E v d = ∑ q∈aU (s.B+1),∑ a∈aU (powerCount s E v d),
        ∑ j∈aU (s.J+1),f q j a :=
      lJ rfl fun q _=>sum_comm
    _=phase s h E v d:= by
      rw [sum_comm]
      apply lJ rfl
      intro a _
      rw [sum_comm]
      have column (j:ℕ) : (∑ q∈aU (s.B+1),f q j a) =
          (lz s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (j+E*(a+d)) (s.B+1),width s h q j a := by
        simp only [f,mul_sum,← sum_filter]
        congr 1
        ext q
        simp only [mem_filter,mem_range,mem_Ico,and_comm]
      simp_rw [column]
      rw [← mul_sum]
      apply congrArg ((lz s.U ((a+d)*v) :ℤ) * ·)
      symm
      apply sum_subset (range_mono (oD _ _))
      intro j hj hnot
      simp only [mem_range,lt_min_iff] at hj hnot
      rw [Ico_eq_empty_of_le (by omega),sum_empty]
theorem phase_bound (s :cy) (h E v :ℕ) (hh:h≤131071) (he :0<E) :
  phase s h E v 0 - phase s h E v 1≤(ZN h s E v :ℤ) := by
 rw [← c3Z,← c3Z]
 simp only [bty,jointGainAt,ku,Nat.cast_sum]
 rw [← oz]
 apply oj
 intro q hq
 rw [← extend s h E v 0 q,← extend s h E v 1 q,← oz]
 apply oj
 intro j hj
 rw [mem_range,Nat.lt_succ_iff] at hq hj
 exact position s h E v q j hh he hq (hj.trans (oD _ _))
theorem phase_affine (s :cy) (h:ℤ) (E v d:ℕ) :
  phase s h E v d=phase s 0 E v d+h*(phase s 1 E v d - phase s 0 E v d) := by
 simp only [phase,← oz ,mul_sum,← sum_add_distrib,← mul_sub]
 apply lJ rfl
 intro a _
 apply lJ rfl
 intro j _
 apply lJ rfl
 intro q _
 unfold width
 ring
end qPTjEYd
end
section
set_option autoImplicit true
namespace qd4jtSc
open P5_7_2 (fO)
abbrev b2 :fO:=⟨2,by decide⟩
abbrev b3:fO:=⟨3,by decide⟩
end qd4jtSc
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt)
private abbrev b:fO:=⟨6,by decide⟩
private theorem a0:GG b 0 3:= by
 repeat' apply oq
 all_goals first | exact mD | apply receipt 2539 rfl <;> with_unfolding_all rfl
private theorem a3:GG b 3 3:= by
 repeat' apply oq
 all_goals first | exact mD | apply receipt 2539 rfl <;> with_unfolding_all rfl
private theorem a6:GG b 6 3:= by
 repeat' apply oq
 all_goals first | exact mD | apply receipt 2539 rfl <;> with_unfolding_all rfl
private theorem a9:GG b 9 3:= by
 repeat' apply oq
 all_goals first | exact mD | apply receipt 2539 rfl <;> with_unfolding_all rfl
theorem a :GG (⟨6,by decide⟩:fO) 0 12 :=
 oK  (oK  (oK  a0 a3) a6) a9
end qyV6B3d
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt)
private abbrev kA:fO:=⟨6,by decide⟩
local notation "kU" => receipt 2539 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
private theorem nJ:GG kA 24 3:=⟨kU,kU,kU,mD⟩
private theorem tj:GG kA 27 3:=⟨kU,kU,kU,mD⟩
private theorem xM:GG kA 30 3:=⟨kU,kU,kU,mD⟩
private theorem A4 :GG kA 33 3:=⟨kU,kU,kU,mD⟩
theorem c:GG kA 24 12 :=
 oK (oK (oK nJ tj) xM) A4
end qyV6B3d
end
