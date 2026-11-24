import ProximityPrize.SubmissionLower.ZVLxwUa
import ProximityPrize.SubmissionLower.ZxlLGHd
import ProximityPrize.SubmissionLower.ZgLUh9d
import ProximityPrize.SubmissionLower.Z3wMysc
import ProximityPrize.SubmissionLower.Z3vxfLe
import ProximityPrize.SubmissionLower.ZfOr3oe
import ProximityPrize.SubmissionLower.ZGSvmVd
set_option Elab.async false
open _root_ renaming Finsupp.add_apply → zSs, Finsupp.degree_single → zlu, Finsupp.single → zhf, List.range → zCP, Nat.choose_eq_zero_of_lt → zsx, Set.range → zxp, Submodule.smul_mem → zc2, Submodule.span → zLD, Submodule.subset_span → zBO, Submodule.sum_mem → zo3, Submodule.zero_mem → z4M
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
namespace q1racBe
open qwzqCne
open fP (cF m9)
open axE (raw basis a1y aTx blP)

open private project ad7 rawForm amf from ProximityPrize.SubmissionLower.ZVLxwUa
open MvPolynomial
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
theorem large_value_span (e :aY) (ha :17≤e.val 0) (cut:ℕ) :jZ e cut:= by
  classical
  let S:=zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val))
  have hz :project 54 cut (bind₁ basis (monomial e.val 1))=0:= by
    funext m
    change (bind₁ basis (monomial e.val 1)).coeff m.val=0
    apply notMem_support_iff.mp
    intro hm
    have htop:=m.property.2.2.2
    exact (by omega : ¬ e.val 0≤ m.val 3) (blP _ _ hm).2
  obtain ⟨z,hzne,F,hF,hEq⟩:=aTx e.val
  rw [a1y,hEq,map_add,map_add,amf,map_smul,map_smul] at hz
  change z•project 54 cut (rawForm e.val)+project 54 cut (bind₁ raw F)=0 at hz
  have hFmem:project 54 cut (bind₁ raw F)∈S:= by
    rw [F.as_sum,map_sum,map_sum]
    apply S.sum_mem
    intro m hm
    obtain ⟨hd,hw⟩:=hF m hm
    let v :aY:=⟨m,hd.trans e.property⟩
    have hlt:dZ v<dZ e := by
      have hv :=v.property
      rw [cF] at hv
      change v.val.weight m9<e.val.weight m9 at hw
      rw [dZ,dZ,Sj,Sj]
      omega
    rw [amf,map_smul,map_smul]
    change _•project 54 cut (rawForm v.val)∈S
    rw [ad7]
    exact S.smul_mem _ (zBO ⟨⟨v,hlt⟩,rfl⟩)
  have ht:=S.neg_mem hFmem
  rw [← eq_neg_of_add_eq_zero_left hz] at ht
  have h:=S.smul_mem z⁻¹ ht
  rwa [smul_smul,inv_mul_cancel₀ hzne,one_smul,ad7] at h
end
end q1racBe
end
section
set_option autoImplicit true
namespace qzVXMPd
open qwzqCne MvPolynomial
open GN (Interpolant ord weights b9)
open fP (cF)
noncomputable section
private def pad (e :aY) :qHde8fc.aY :=
  ⟨e.val+Finsupp.single 1 2,by rw [map_add,zlu,e.property]⟩
@[simp] private theorem pad_zero (e :aY) : (pad e).val 0=e.val 0:= by
  simp [pad]
@[simp] private theorem pad_one (e :aY) : (pad e).val 1=e.val 1+2 := by
  simp [pad]
@[simp] private theorem pad_two (e :aY) : (pad e).val 2=e.val 2 := by
  simp [pad]
@[simp] private theorem pad_three (e :aY) : (pad e).val 3=e.val 3:= by
  simp [pad]
@[simp] private theorem pad_ord (e :aY) :ord (pad e).val=ord e.val := by
  simp only [ord,pad_zero,pad_two,pad_three]
private theorem pad_key {e v :aY} (h:dZ e<dZ v) :
    qHde8fc.dZ (pad e)<qHde8fc.dZ (pad v) := by
  have he :=cF e.val
  have hv :=cF v.val
  rw [e.property] at he
  rw [v.property] at hv
  unfold dZ at h
  rw [show cP (aD e.val)=54+ord e.val from nG e,
    show cP (aD v.val)=54+ord v.val from nG v] at h
  simp only [qHde8fc.dZ,qhonTAe.nG,pad_ord,pad_one,pad_two,pad_three]
  by_cases hOrd:ord e.val<ord v.val
  · omega
  have hOrd' : ord e.val=ord v.val := by omega
  by_cases hf :e.val 3<v.val 3
  · omega
  have hf' : e.val 3=v.val 3:= by omega
  by_cases hc:e.val 2<v.val 2
  · omega
  have hc' : e.val 2=v.val 2 := by omega
  omega
private def translate (j:Fin 3) :Interpolant:=MvPolynomial.X j+C (if j=0 then 2 else 0)
private theorem translate_eval (e :aY) (P:Interpolant) :
    b9 e.val (bind₁ translate P)=b9 (pad e).val P:= by
  have h :
      (fun i:Fin 3=>aeval (fun j:Fin 3=>(e.val j.succ:Ground)) (translate i)) =
      (fun j:Fin 3=>((pad e).val j.succ:Ground)) := by
    funext j
    fin_cases j <;> simp [translate]
  simp only [b9,aeval_bind₁,h]
theorem interpolate (e :aY) (ht:ord e.val≤56) :
    ∃ P:Interpolant,P∈Bounded (cutBudget e)∧Ak e P:= by
  obtain ⟨P,hP,hsep⟩:=qhonTAe.interpolate (pad e) (by simpa using ht)
  have hBudget:qhonTAe.cutBudget (pad e)=cutBudget e := by
    simp only [cutBudget,qhonTAe.cutBudget,pad_ord,pad_zero,pad_two]
  rw [hBudget] at hP
  have hTranslate (j:Fin 3) :translate j∈Bounded (weights j) :=
    (Bounded (weights j)).add_mem (X_mem_restrictWeightedDegree weights _ j le_rfl)
      (C_mem_restrictWeightedDegree weights _ _)
  refine ⟨bind₁ translate P,bind₁_mem_restrictWeightedDegree hTranslate hP,?_,?_⟩
  · rw [translate_eval]
    exact hsep.1
  · intro v hv hk
    rw [translate_eval]
    exact hsep.2 (pad v) ((qhonTAe.abJ _).mpr (by
      simpa only [pad_ord,pad_zero] using (abJ _).mp hv)) (pad_key hk)
end
end qzVXMPd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qT7fytc
open qHde8fc (Ground Exponent aD yv)
open fP (Ew cF xH m9 oG)
open axE (Form raw ao9)
open MvPolynomial
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
namespace Tr
abbrev af (d:ℕ) := {m:Exponent // m.degree=d}
abbrev qB (d cut:ℕ) :=qK9H6va.Lh d cut
def key (B:ℕ) (m:Exponent) :ℕ :=
  ((m.weight m9*B+m 3)*B+m 2)*B+m 1
theorem key_compare52 (u v :af 52) :key 53 u.val<key 53 v.val↔key 57 u.val<key 57 v.val := by
  have hu:=u.property
  have hv :=v.property
  rw [cF] at hu hv
  unfold key
  rcases lt_trichotomy (u.val.weight m9) (v.val.weight m9) with h | h | h
  · omega
  · rw [h]
    rcases lt_trichotomy (u.val 3) (v.val 3) with h | h | h
    · omega
    · rw [h]
      rcases lt_trichotomy (u.val 2) (v.val 2) with h | h | h <;> omega
    · omega
  · omega
def addOne (i:Fin 4) (m:Exponent) :Exponent:=m+Finsupp.single i 1
theorem addOne_degree (i:Fin 4) (m:Exponent) :
    (addOne i m).degree=m.degree+1 := by
  rw [addOne,map_add,zlu]
def raise (i:Fin 4) {d:ℕ} (u:af d) :af (d+1) :=
  ⟨addOne i u.val,by rw [addOne_degree,u.property]⟩
theorem raise_key (i:Fin 4) (m:Exponent) :
    key 57 (addOne i m)=key 57 m+key 57 (zhf i 1) := by
  fin_cases i <;> simp [key,oG,addOne,zSs] <;> omega
theorem key_unit (i:Fin 4) :1≤key 57 (zhf i 1) := by
  fin_cases i <;> simp [key,oG]
theorem key_unit_lt (i:Fin 4) (hi:i≠1) :1<key 57 (zhf i 1) := by
  fin_cases i <;> simp [key,oG] at *
def lower (i:Fin 4) {d:ℕ} (u:af (d+1)) (h:u.val i≠0) :af d:= by
  have hh:zhf i 1≤u.val :=Finsupp.single_le_iff.mpr (by omega)
  have hd:=congrArg Finsupp.degree (tsub_add_cancel_of_le hh)
  rw [map_add,zlu,u.property] at hd
  exact ⟨u.val-Finsupp.single i 1,Nat.add_right_cancel hd⟩
theorem lower_earlier {d:ℕ} (e :af d) (v :af (d+1)) (i:Fin 4) (hi:v.val i≠0)
    (h:key 57 v.val≤key 57 (raise 1 e).val)
    (hstrict :key 57 v.val<key 57 (raise 1 e).val∨i≠1) :
    key 57 (lower i v hi).val<key 57 e.val := by
  have hsub:addOne i (lower i v hi).val=v.val :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))
  have hk :=raise_key i (lower i v hi).val
  rw [hsub] at hk
  have he :key 57 (raise 1 e).val=key 57 e.val+1 := by
    change key 57 (addOne 1 e.val)= _
    rw [raise_key]
    simp [key,oG]
  rcases hstrict with hs | hs
  · have hp:=key_unit i
    omega
  · have hp:=key_unit_lt i hs
    omega
def raisedCol {d cut:ℕ} (m:qB d cut) :qB (d+1) cut:= by
  have h:=m.property
  rw [Ew,xH] at h
  refine ⟨addOne 0 m.val,?_⟩
  rw [Ew,addOne_degree,xH,h.1]
  simpa [addOne,zSs,Finsupp.single_apply] using h.2
def project (d cut:ℕ) :Form →ₗ[Ground] (qB d cut→Ground) :=
  LinearMap.pi fun m=>lcoeff Ground m.val
def rawForm (u:Exponent) :Form:=bind₁ raw (monomial u 1)
theorem ad7 {d cut:ℕ} (u:af d) :
    project d cut (rawForm u.val)=yv Subtype.val (aD u.val) := by
  funext m
  exact ao9 u.val m.val (u.property.trans m.property.1.symm)
def nextSpan {d:ℕ} (e :af d) (cut:ℕ) :Submodule Ground (qB d cut→Ground) :=
  zLD Ground (zxp fun v : {v :af d // key 57 v.val<key 57 e.val} =>
    yv Subtype.val (aD v.val.val))
def down (d cut:ℕ) : (qB (d+1) cut→Ground) →ₗ[Ground] (qB d cut→Ground) :=
  LinearMap.pi fun m=>((m.val 0:Ground)+1)•LinearMap.proj (raisedCol m)
theorem down_eq {d cut:ℕ} (F:Form) :
    down d cut (project (d+1) cut F)=project d cut (pderiv 0 F) := by
  funext m
  change ((m.val 0:Ground)+1)*F.coeff (addOne 0 m.val)=(pderiv 0 F).coeff m.val
  rw [coeff_pderiv,mul_comm]
  rfl
def direction :Derivation Ground Form Form:=pderiv 0+pderiv 1+pderiv 2+pderiv 3
theorem deriv_raw_X (j:Fin 4) :
    pderiv 0 (raw j)=bind₁ raw (direction (MvPolynomial.X j)) := by
  fin_cases j <;> simp [raw,direction,pderiv_X]
theorem deriv_raw (F:Form) :pderiv 0 (bind₁ raw F)=bind₁ raw (direction F) := by
  induction F using MvPolynomial.induction_on with
  | C a=>simp [derivation_C]
  | add F G hF hG=>simp only [map_add,hF,hG]
  | mul_X F j hF =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,bind₁_X_right,← hF,← deriv_raw_X]
theorem amf (m:Exponent) (z :Ground) : (monomial m z :Form)=z•monomial m 1 := by
  rw [smul_monomial,smul_eq_mul,mul_one]
theorem deriv_row {d cut:ℕ} (v :af (d+1)) :
    down d cut (project (d+1) cut (rawForm v.val)) =
      ∑ i:Fin 4,(v.val i:Ground)•project d cut (rawForm (v.val-Finsupp.single i 1)) := by
  rw [down_eq,rawForm,deriv_raw]
  simp only [direction,Derivation.add_apply,Fin.sum_univ_four,pderiv_monomial,one_mul,map_add,rawForm]
  congr 3 <;> rw [amf,map_smul,map_smul]
theorem deriv_term_mem {d cut:ℕ} (e :af d) (v :af (d+1)) (i:Fin 4)
    (h:key 57 v.val≤key 57 (raise 1 e).val)
    (hs :key 57 v.val<key 57 (raise 1 e).val∨i≠1) :
    (v.val i:Ground)•project d cut (rawForm (v.val-Finsupp.single i 1))∈nextSpan e cut:= by
  by_cases hi:v.val i=0
  · simp [hi]
  · let u:=lower i v hi
    change (v.val i:Ground)•project d cut (rawForm u.val)∈nextSpan e cut
    rw [ad7]
    exact zc2 _ _ (zBO ⟨⟨u,lower_earlier e v i hi h hs⟩,rfl⟩)
theorem descend {d cut:ℕ} (e :af d) (hd:d<56)
    (h:project (d+1) cut (rawForm (raise 1 e).val)∈nextSpan (raise 1 e) cut) :
    project d cut (rawForm e.val)∈nextSpan e cut:= by
  classical
  have hm: (nextSpan (raise 1 e) cut).map (down d cut)≤nextSpan e cut:= by
    apply (Submodule.map_span_le _ _ _).mpr
    rintro _ ⟨v,rfl⟩
    change down d cut (yv _ (aD v.val.val))∈nextSpan e cut
    rw [← ad7 v.val,deriv_row]
    exact zo3 _ fun i _=>deriv_term_mem e v.val i v.property.le (Or.inl v.property)
  have hh:=hm (Submodule.mem_map_of_mem (f :=down d cut) h)
  rw [deriv_row,← Finset.sum_erase_add _ _ (Finset.mem_univ (1 :Fin 4))] at hh
  have hsum: (∑ i∈(Finset.univ :Finset (Fin 4)).erase 1,
      ((raise 1 e).val i:Ground)•project d cut (rawForm ((raise 1 e).val-Finsupp.single i 1)))
      ∈ nextSpan e cut :=
    zo3 _ fun i hi=>deriv_term_mem e (raise 1 e) i le_rfl
      (Or.inr (Finset.ne_of_mem_erase hi))
  have htarget :=Submodule.sub_mem _ hh hsum
  rw [add_sub_cancel_left] at htarget
  change (((addOne 1 e.val) 1 :ℕ) :Ground) •
    project d cut (rawForm (addOne 1 e.val-Finsupp.single 1 1))∈nextSpan e cut at htarget
  have hcancel:addOne 1 e.val-Finsupp.single 1 1=e.val := by
    simp [addOne]
  rw [hcancel] at htarget
  have hpos : (addOne 1 e.val) 1≠0:= by simp [addOne,zSs]
  have he :=e.property
  rw [cF] at he
  have hb: (addOne 1 e.val) 1≤56:= by simp [addOne,zSs]; omega
  have hz : (((addOne 1 e.val) 1 :ℕ) :Ground)≠0:= by
    simpa only [Nat.cast_zero] using qhonTAe.cEo hb (by decide :0≤56) hpos
  have ht:=zc2 (nextSpan e cut) (((addOne 1 e.val) 1 :ℕ) :Ground)⁻¹ htarget
  rwa [smul_smul,inv_mul_cancel₀ hz,one_smul] at ht
end Tr
open Tr
def up (e :qoWrama.aY) :qHde8fc.aY:=raise 1 (raise 1 (raise 1 (raise 1 e)))
theorem up_apply_of_ne (e :qoWrama.aY) (i:Fin 4) (hi:i≠1) :
    (up e).val i=e.val i:= by
  simp [up,raise,addOne,zSs,Finsupp.single_eq_of_ne hi]
theorem up_one (e :qoWrama.aY) : (up e).val 1=e.val 1+4 := by
  simp only [up,raise,addOne,zSs,Finsupp.single_eq_same]
theorem up_coordinates (e :qoWrama.aY) :
    aD (up e).val=(e.val 1+4,e.val 2,e.val 3) := by
  simp only [aD,up_one,up_apply_of_ne e 2 (by decide),up_apply_of_ne e 3 (by decide)]
theorem up_cost (e :qoWrama.aY) :
    qHde8fc.cP (aD (up e).val)=qoWrama.cP (aD e.val)+4 := by
  rw [qHde8fc.Sj,qoWrama.Sj,oG,oG,
    up_apply_of_ne e 0 (by decide),up_apply_of_ne e 2 (by decide),up_apply_of_ne e 3 (by decide)]
  omega
theorem transfer52 (e :qoWrama.aY) (cut:ℕ)
    (h:qHde8fc.cE cut (aD (up e).val) ∈
      zLD Ground (zxp fun v :qHde8fc.iw (up e) =>
        qHde8fc.cE cut (aD v.val.val))) :
    qoWrama.cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :qoWrama.iw e =>
        qoWrama.cE cut (aD v.val.val)) := by
  have key56 (u v :qHde8fc.aY) :
      qHde8fc.dZ u<qHde8fc.dZ v↔key 57 u.val<key 57 v.val := by
    rw [qHde8fc.dZ,qHde8fc.dZ,qHde8fc.Sj,qHde8fc.Sj]
    unfold key
    omega
  have key52 (u v :qoWrama.aY) :
      qoWrama.dZ u<qoWrama.dZ v↔key 57 u.val<key 57 v.val := by
    rw [← key_compare52 u v,qoWrama.dZ,qoWrama.dZ,
      qoWrama.Sj,qoWrama.Sj]
    unfold key
    omega
  have hsource :zLD Ground (zxp fun v :qHde8fc.iw (up e) =>
      qHde8fc.cE cut (aD v.val.val))≤nextSpan (up e) cut:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact zBO ⟨⟨v.val,(key56 _ _).mp v.property⟩,rfl⟩
  have ht:yv (κ:=qB 56 cut) Subtype.val (aD (up e).val) ∈
      nextSpan (up e) cut:=hsource h
  rw [← ad7 (up e)] at ht
  have h52 :=descend e (by decide) (descend (raise 1 e) (by decide)
    (descend (raise 1 (raise 1 e)) (by decide) (descend (raise 1 (raise 1 (raise 1 e))) (by decide) ht)))
  rw [ad7] at h52
  apply (show nextSpan e cut≤_ from Submodule.span_le.mpr ?_) h52
  rintro _ ⟨v,rfl⟩
  exact zBO ⟨⟨v.val,(key52 _ _).mpr v.property⟩,rfl⟩
end
end qT7fytc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qT7fytc
open fP (cF xH oG)
open GN (ord weights)
open MvPolynomial
def hintAt (H :ℕ→ℕ) (w f a :ℕ) :ℕ:=(H w >>> (6*(17*f+a))) % 64
def bnd (w h:ℕ) :ℕ:=if h=0 then w-98 else max (w-98) h
def cOf (D w f a :ℕ) :ℕ:=w-(D + 3*a+2*f)
def bOf (D w f a :ℕ) :ℕ:=D - (a+cOf D w f a+f)
def zeroB (D w f a B:ℕ) :Bool:=decide (bOf D w f a+2*cOf D w f a+3*min f 16<B)
def anaB (D w f a B:ℕ) :Bool:=decide (3*(56-(w - D))+2*a+cOf D w f a/2<B)
def recB (recs :List Rec) (w f a B:ℕ) :Bool :=
  recs.any fun q=>q.w == w && q.f == f && q.a == a && decide (0<q.cut) && decide (q.cut≤B)
def altB (D:ℕ) (recs :List Rec) (w f a B:ℕ) :Bool :=
  zeroB D w f a B || anaB D w f a B || recB recs w f a B
theorem recB_spec {recs :List Rec} {w f a B:ℕ} (h:recB recs w f a B=true) :
    ∃ q∈recs,q.w=w∧q.f=f∧q.a=a∧0<q.cut∧q.cut≤B:= by
  unfold recB at h
  obtain ⟨q,hq,h⟩:=List.any_eq_true.mp h
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩:=h
  exact ⟨q,hq,h1,h2,h3,h4,h5⟩
section D52
open qHde8fc (Ground aD)
open qoWrama
theorem h52_length:qxuyiwe.h52.length=99:= by decide
def findK52 (g i:ℕ) (r :ℕ×ℕ×ℕ) :ℕ :=
  ((zCP (groupCount g i)).find? fun k=>ZX g i k == r).getD 0
def pivOK52 (w h:ℕ) (r :ℕ×ℕ×ℕ) :Bool :=
  h == 0 || (decide (h - 1<57) && decide (h - 1≤w) && decide (w-(h - 1)<99) &&
    decide (findK52 (w-(h - 1)) (h - 1) r<groupCount (w-(h - 1)) (h - 1)) &&
    ZX (w-(h - 1)) (h - 1) (findK52 (w-(h - 1)) (h - 1) r) == r)
def rowOK52 (H :ℕ→ℕ) (recs :List Rec) (w f a :ℕ) :Bool :=
  if 52 + 3*a+2*f≤w∧a+cOf 52 w f a+f≤52 then
    pivOK52 w (hintAt H w f a) (bOf 52 w f a,cOf 52 w f a,f) &&
      (decide (w+4-98≤bnd w (hintAt H w f a)) || altB 52 recs w f a (bnd w (hintAt H w f a)))
  else true
def srcPiv52 (H :ℕ→ℕ) (recs :List Rec) (lo hi g i k :ℕ) :Bool :=
  let r :=qHde8fc.ZX g i k
  let w:=g+i-4
  let a :=56-(r.1+r.2.1+r.2.2)
  if lo≤w∧w≤hi∧4≤ r.1∧a≤16∧4≤g+i then
    decide (i+1≤bnd w (hintAt H w r.2.2 a)) || altB 52 recs w r.2.2 a (bnd w (hintAt H w r.2.2 a))
  else true
def srcOK52 (H :ℕ→ℕ) (recs :List Rec) (lo hi g:ℕ) :Bool :=
  (zCP 57).all fun i=>(zCP (qHde8fc.groupCount g i)).all fun k=>srcPiv52 H recs lo hi g i k
theorem pivot52 {w h:ℕ} {r :ℕ×ℕ×ℕ} (hp:pivOK52 w h r=true) (h0:h≠0) :
    ∃ j:GroupedPivot,Ug j=r∧c37 j=w∧Nx j=((h - 1 :ℕ) :ℤ) := by
  simp only [pivOK52,Bool.or_eq_true,beq_iff_eq,h0,false_or,Bool.and_eq_true,
    decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨h57,hw⟩,hg⟩,hk⟩,hr⟩:=hp
  refine ⟨⟨⟨w-(h - 1),by rw [h52_length]; exact hg⟩,⟨⟨h - 1,h57⟩,⟨_,hk⟩⟩⟩,hr,?_,rfl⟩
  simp only [c37]
  omega
theorem bound52 {e :aY} {h cut:ℕ}
    (hp:pivOK52 (cP (aD e.val)) h (aD e.val)=true)
    (hc:cut≤bnd (cP (aD e.val)) h) :
    cut≤ cP (aD e.val)-98 ∨ ∃ j:GroupedPivot,Ug j=aD e.val ∧
      c37 j=cP (aD e.val)∧(cut:ℤ)≤Nx j+1 := by
  unfold bnd at hc
  split_ifs at hc with h0
  · exact Or.inl hc
  · rcases le_max_iff.mp hc with hc | hc
    · exact Or.inl hc
    · obtain ⟨j,hr,hcost,hidx⟩:=pivot52 hp h0
      exact Or.inr ⟨j,hr,hcost,by rw [hidx]; omega⟩
theorem zero52 (e :aY) (cut:ℕ) (h:e.val 1+2*e.val 2 + 3*min (e.val 3) 16<cut) :
    cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val)) := by
  have hz :cE cut (aD e.val)=0:= by
    funext m
    obtain ⟨_,hl,_,htop⟩:=m.property
    rw [xH] at hl
    have hl' : cut≤ m.val 1+2*m.val 2 + 3*m.val 3:= by exact_mod_cast hl
    simp only [cE,qHde8fc.yv,aD,Pi.zero_apply]
    by_cases h1 :e.val 1< m.val 1
    · simp [zsx h1]
    by_cases h2 :e.val 2< m.val 2
    · simp [zsx h2]
    by_cases h3:e.val 3< m.val 3
    · simp [zsx h3]
    exfalso
    omega
  rw [hz]
  exact z4M _
theorem wit52 (H :ℕ→ℕ) (recs :List Rec)
    (hrows : ∀ w,80≤w→w≤108 → ∀ a<17,∀ f<57,rowOK52 H recs w f a=true)
    (hsrc : ∀ g<99,srcOK52 H recs 80 108 g=true)
    (hrec : ∀ q∈recs,recOK52 q=true)
    {lo hi:ℕ} (hlo0:80≤lo) (hhi0:hi≤108) (h56:qHde8fc.aGq (lo+4) (hi+4))
    (e :aY) (hlo:lo≤ cP (aD e.val)) (hhi:cP (aD e.val)≤hi) :
    bk1 e := by
  by_cases ha :17≤e.val 0
  · exact ⟨0,Or.inl (Nat.zero_le _),
      qrcA6ce.span_of_inactive e 0 (fun h=> by have :=h.2; omega)⟩
  have hd:=e.property
  rw [cF] at hd
  have hw:cP (aD e.val)=52 + 3*e.val 0+e.val 2+2*e.val 3:= by
    rw [Sj,oG]
    omega
  have hco:aD e.val=(e.val 1,e.val 2,e.val 3) :=rfl
  generalize hW:cP (aD e.val)=w at hlo hhi hw
  have hc:cOf 52 w (e.val 3) (e.val 0)=e.val 2 := by unfold cOf; omega
  have hb:bOf 52 w (e.val 3) (e.val 0)=e.val 1 := by unfold bOf; rw [hc]; omega
  have hex :52 + 3*e.val 0+2*e.val 3≤w∧e.val 0+cOf 52 w (e.val 3) (e.val 0)+e.val 3≤52 := by
    rw [hc]; omega
  have hr :=hrows w (by omega) (by omega) (e.val 0) (by omega) (e.val 3) (by omega)
  rw [rowOK52,if_pos hex,hb,hc,← hco,Bool.and_eq_true] at hr
  obtain ⟨hp,hr⟩:=hr
  generalize hB:bnd w (hintAt H w (e.val 3) (e.val 0))=B at hr
  have fin : ∀ cut,cut≤B→cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val)) →
      bk1 e := by
    intro cut hcB hm
    refine ⟨cut,?_,hm⟩
    exact bound52 (e :=e) (h:=hintAt H w (e.val 3) (e.val 0)) (by rw [hW]; exact hp)
      (by rw [hW,hB]; exact hcB)
  have hord:ord e.val=w - 52 := by unfold ord; omega
  by_cases halt:altB 52 recs w (e.val 3) (e.val 0) B=true
  · simp only [altB,Bool.or_eq_true] at halt
    rcases halt with (hz | han) | hq
    ·
      simp only [zeroB,decide_eq_true_eq,hb,hc] at hz
      exact fin B le_rfl (zero52 e B hz)
    ·
      simp only [anaB,decide_eq_true_eq,hc] at han
      have hbud:qrcA6ce.cutBudget e<B:= by
        unfold qrcA6ce.cutBudget
        rw [hord]
        omega
      obtain ⟨P,hP,hsep⟩:=qrcA6ce.interpolate e (by omega)
      exact fin B le_rfl (qrcA6ce.Ae e B (by omega) P
        (restrictWeightedDegree_mono weights (by omega) hP) hsep)
    ·
      obtain ⟨q,hqm,hqw,hqf,hqa,hq0,hqB⟩:=recB_spec hq
      exact fin q.cut hqB (rec_sound52 (hrec q hqm) hq0 (by omega) e (hW.trans hqw.symm) hqa.symm hqf.symm)
  ·
    have hT:w+4-98≤B:= by
      rcases Bool.or_eq_true_iff.mp hr with h1 | h1
      · exact of_decide_eq_true h1
      · exact absurd h1 halt
    have hup:=up_cost e
    rw [hW] at hup
    obtain ⟨cut,hcut,hm⟩:=h56 (up e) (by omega) (by omega)
    refine fin cut ?_ (transfer52 e cut hm)
    rcases hcut with hc56 | ⟨j,hj,hjc,hji⟩
    · omega
    · obtain ⟨⟨g,hg⟩,⟨i,hi⟩,⟨k,hk⟩⟩:=j
      have hrow:qHde8fc.ZX g i k=(e.val 1+4,e.val 2,e.val 3) := by
        rw [← up_coordinates]
        exact hj
      have hgi:g+i=w+4 := by
        have :=hjc
        simp only [qHde8fc.c37] at this
        omega
      have hs :=List.all_eq_true.mp (List.all_eq_true.mp (hsrc g hg) i (List.mem_range.mpr hi)) k
        (List.mem_range.mpr hk)
      have hw' : g+i-4=w:= by omega
      have ha' : 56-(e.val 1+4+e.val 2+e.val 3)=e.val 0:= by omega
      simp only [srcPiv52,hrow,hw',ha'] at hs
      split_ifs at hs with hcond
      swap
      · exact (hcond ⟨by omega,by omega,by omega,by omega,by omega⟩).elim
      rw [hB] at hs
      rcases Bool.or_eq_true_iff.mp hs with h1 | h1
      · have h2 :=of_decide_eq_true h1
        simp only [qHde8fc.Nx] at hji
        omega
      · exact absurd h1 halt
theorem slab52_of (lo hi:ℕ) (hlo:80≤lo) (hhi:hi≤108) (h56:qHde8fc.aGq (lo+4) (hi+4))
    (H :ℕ→ℕ) (recs :List Rec)
    (hrows : ∀ w,80≤w→w≤108 → ∀ a<17,∀ f<57,rowOK52 H recs w f a=true)
    (hsrc : ∀ g<99,srcOK52 H recs 80 108 g=true)
    (hrec : ∀ q∈recs,recOK52 q=true) :aGq lo hi :=
  fun e h1 h2=>wit52 H recs hrows hsrc hrec hlo hhi h56 e h1 h2
end D52
section D54
open qwzqCne
def findK54 (g i:ℕ) (r :ℕ×ℕ×ℕ) :ℕ :=
  ((zCP (groupCount g i)).find? fun k=>ZX g i k == r).getD 0
def pivOK54 (w h:ℕ) (r :ℕ×ℕ×ℕ) :Bool :=
  h == 0 || (decide (h - 1<57) && decide (h - 1≤w) && decide (w-(h - 1)<99) &&
    decide (findK54 (w-(h - 1)) (h - 1) r<groupCount (w-(h - 1)) (h - 1)) &&
    ZX (w-(h - 1)) (h - 1) (findK54 (w-(h - 1)) (h - 1) r) == r)
def rowOK54 (H :ℕ→ℕ) (recs :List Rec) (w f a :ℕ) :Bool :=
  if 54+3*a+2*f≤w∧a+cOf 54 w f a+f≤54 then
    pivOK54 w (hintAt H w f a) (bOf 54 w f a,cOf 54 w f a,f) &&
      (decide (w+2 - 98≤bnd w (hintAt H w f a)) || altB 54 recs w f a (bnd w (hintAt H w f a)))
  else true
def srcPiv54 (H :ℕ→ℕ) (recs :List Rec) (lo hi g i k :ℕ) :Bool :=
  let r :=qHde8fc.ZX g i k
  let w:=g+i - 2
  let a :=56-(r.1+r.2.1+r.2.2)
  if lo≤w∧w≤hi∧2≤ r.1∧a≤16∧2≤g+i then
    decide (i+1≤bnd w (hintAt H w r.2.2 a)) || altB 54 recs w r.2.2 a (bnd w (hintAt H w r.2.2 a))
  else true
def srcOK54 (H :ℕ→ℕ) (recs :List Rec) (lo hi g:ℕ) :Bool :=
  (zCP 57).all fun i=>(zCP (qHde8fc.groupCount g i)).all fun k=>srcPiv54 H recs lo hi g i k
theorem pivot54 {w h:ℕ} {r :ℕ×ℕ×ℕ} (hp:pivOK54 w h r=true) (h0:h≠0) :
    ∃ j:Pivot,Ug j=r∧c37 j=w∧Nx j=h - 1 := by
  simp only [pivOK54,Bool.or_eq_true,beq_iff_eq,h0,false_or,Bool.and_eq_true,
    decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨h57,hw⟩,hg⟩,hk⟩,hr⟩:=hp
  refine ⟨⟨⟨w-(h - 1),hg⟩,⟨⟨h - 1,h57⟩,⟨_,hk⟩⟩⟩,hr,?_,rfl⟩
  simp only [c37,Nx]
  omega
theorem bound54 {e :aY} {h cut:ℕ}
    (hp:pivOK54 (cP (aD e.val)) h (aD e.val)=true)
    (hc:cut≤bnd (cP (aD e.val)) h) :
    cut≤ cP (aD e.val)-98 ∨ ∃ j:Pivot,Ug j=aD e.val ∧
      c37 j=cP (aD e.val)∧cut≤Nx j+1 := by
  unfold bnd at hc
  split_ifs at hc with h0
  · exact Or.inl hc
  · rcases le_max_iff.mp hc with hc | hc
    · exact Or.inl hc
    · obtain ⟨j,hr,hcost,hidx⟩:=pivot54 hp h0
      exact Or.inr ⟨j,hr,hcost,by rw [hidx]; omega⟩
theorem zero54 (e :aY) (cut:ℕ) (h:e.val 1+2*e.val 2 + 3*min (e.val 3) 16<cut) :
    cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val)) := by
  have hz :cE cut (aD e.val)=0:= by
    funext m
    obtain ⟨_,hl,_,htop⟩:=m.property
    rw [xH] at hl
    have hl' : cut≤ m.val 1+2*m.val 2 + 3*m.val 3:= by exact_mod_cast hl
    simp only [cE,yv,aD,Pi.zero_apply]
    by_cases h1 :e.val 1< m.val 1
    · simp [zsx h1]
    by_cases h2 :e.val 2< m.val 2
    · simp [zsx h2]
    by_cases h3:e.val 3< m.val 3
    · simp [zsx h3]
    exfalso
    omega
  rw [hz]
  exact z4M _
theorem to56_one (e :aY) : (q1racBe.to56 e).val 1=e.val 1+2 := by
  have h56:=(q1racBe.to56 e).property
  have h54 :=e.property
  rw [cF] at h56 h54
  rw [q1racBe.to56_apply_of_ne e 0 (by decide),q1racBe.to56_apply_of_ne e 2 (by decide),
    q1racBe.to56_apply_of_ne e 3 (by decide)] at h56
  omega
theorem wit54 (H :ℕ→ℕ) (recs :List Rec)
    (hrows : ∀ w,83≤w→w≤110 → ∀ a<17,∀ f<57,rowOK54 H recs w f a=true)
    (hsrc : ∀ g<99,srcOK54 H recs 83 110 g=true)
    (hrec : ∀ q∈recs,recOK54 q=true)
    {lo hi:ℕ} (hlo0:83≤lo) (hhi0:hi≤110) (h56:qHde8fc.aGq (lo+2) (hi+2))
    (e :aY) (hlo:lo≤ cP (aD e.val)) (hhi:cP (aD e.val)≤hi) :
    bk1 e := by
  by_cases ha :17≤e.val 0
  · exact ⟨0,Or.inl (Nat.zero_le _),q1racBe.large_value_span e ha 0⟩
  have hd:=e.property
  rw [cF] at hd
  have hw:cP (aD e.val)=54+3*e.val 0+e.val 2+2*e.val 3:= by
    rw [Sj,oG]
    omega
  have hco:aD e.val=(e.val 1,e.val 2,e.val 3) :=rfl
  generalize hW:cP (aD e.val)=w at hlo hhi hw
  have hc:cOf 54 w (e.val 3) (e.val 0)=e.val 2 := by unfold cOf; omega
  have hb:bOf 54 w (e.val 3) (e.val 0)=e.val 1 := by unfold bOf; rw [hc]; omega
  have hex :54+3*e.val 0+2*e.val 3≤w∧e.val 0+cOf 54 w (e.val 3) (e.val 0)+e.val 3≤54 := by
    rw [hc]; omega
  have hr :=hrows w (by omega) (by omega) (e.val 0) (by omega) (e.val 3) (by omega)
  rw [rowOK54,if_pos hex,hb,hc,← hco,Bool.and_eq_true] at hr
  obtain ⟨hp,hr⟩:=hr
  generalize hB:bnd w (hintAt H w (e.val 3) (e.val 0))=B at hr
  have fin : ∀ cut,cut≤B→cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val)) →
      bk1 e := by
    intro cut hcB hm
    refine ⟨cut,?_,hm⟩
    exact bound54 (e :=e) (h:=hintAt H w (e.val 3) (e.val 0)) (by rw [hW]; exact hp)
      (by rw [hW,hB]; exact hcB)
  have hord:ord e.val=w - 54 := by unfold ord; omega
  by_cases halt:altB 54 recs w (e.val 3) (e.val 0) B=true
  · simp only [altB,Bool.or_eq_true] at halt
    rcases halt with (hz | han) | hq
    · simp only [zeroB,decide_eq_true_eq,hb,hc] at hz
      exact fin B le_rfl (zero54 e B hz)
    · simp only [anaB,decide_eq_true_eq,hc] at han
      have hbud:qzVXMPd.cutBudget e<B:= by
        unfold qzVXMPd.cutBudget
        rw [hord]
        omega
      obtain ⟨P,hP,hsep⟩:=qzVXMPd.interpolate e (by omega)
      exact fin B le_rfl (qzVXMPd.Ae e B (by omega) P
        (restrictWeightedDegree_mono weights (by omega) hP) hsep)
    · obtain ⟨q,hqm,hqw,hqf,hqa,hq0,hqB⟩:=recB_spec hq
      exact fin q.cut hqB (rec_sound54 (hrec q hqm) hq0 (by omega) e (hW.trans hqw.symm) hqa.symm hqf.symm)
  · have hT:w+2 - 98≤B:= by
      rcases Bool.or_eq_true_iff.mp hr with h1 | h1
      · exact of_decide_eq_true h1
      · exact absurd h1 halt
    have hup:qHde8fc.cP (qHde8fc.aD (q1racBe.to56 e).val)=w+2 := by
      rw [qHde8fc.Sj,oG,q1racBe.to56_apply_of_ne e 0 (by decide),
        q1racBe.to56_apply_of_ne e 2 (by decide),q1racBe.to56_apply_of_ne e 3 (by decide)]
      omega
    obtain ⟨cut,hcut,hm⟩:=h56 (q1racBe.to56 e) (by omega) (by omega)
    refine fin cut ?_ (q1racBe.transfer e cut hm)
    rcases hcut with hc56 | ⟨j,hj,hjc,hji⟩
    · omega
    · obtain ⟨⟨g,hg⟩,⟨i,hi⟩,⟨k,hk⟩⟩:=j
      have hrow:qHde8fc.ZX g i k=(e.val 1+2,e.val 2,e.val 3) := by
        have :=hj
        simp only [qHde8fc.Ug,qHde8fc.aD,to56_one,
          q1racBe.to56_apply_of_ne e 2 (by decide),
          q1racBe.to56_apply_of_ne e 3 (by decide)] at this
        exact this
      have hgi:g+i=w+2 := by
        have :=hjc
        simp only [qHde8fc.c37] at this
        omega
      have hs :=List.all_eq_true.mp (List.all_eq_true.mp (hsrc g hg) i (List.mem_range.mpr hi)) k
        (List.mem_range.mpr hk)
      have hw' : g+i - 2=w:= by omega
      have ha' : 56-(e.val 1+2+e.val 2+e.val 3)=e.val 0:= by omega
      simp only [srcPiv54,hrow,hw',ha'] at hs
      split_ifs at hs with hcond
      swap
      · exact (hcond ⟨by omega,by omega,by omega,by omega,by omega⟩).elim
      rw [hB] at hs
      rcases Bool.or_eq_true_iff.mp hs with h1 | h1
      · have h2 :=of_decide_eq_true h1
        simp only [qHde8fc.Nx] at hji
        omega
      · exact absurd h1 halt
theorem slab54_of (lo hi:ℕ) (hlo:83≤lo) (hhi:hi≤110) (h56:qHde8fc.aGq (lo+2) (hi+2))
    (H :ℕ→ℕ) (recs :List Rec)
    (hrows : ∀ w,83≤w→w≤110 → ∀ a<17,∀ f<57,rowOK54 H recs w f a=true)
    (hsrc : ∀ g<99,srcOK54 H recs 83 110 g=true)
    (hrec : ∀ q∈recs,recOK54 q=true) :aGq lo hi :=
  fun e h1 h2=>wit54 H recs hrows hsrc hrec hlo hhi h56 e h1 h2
end D54
end qT7fytc
end
