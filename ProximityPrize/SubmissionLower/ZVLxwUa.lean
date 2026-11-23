import ProximityPrize.SubmissionLower.ZkYlUGe
import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
set_option autoImplicit true
namespace q1racBe
open qwzqCne (Ground Exponent aD yv)
open fP (Ew cF xH m9 oG)
open axE (Form raw ao9)
open MvPolynomial
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private abbrev af (d:ℕ) := {m:Exponent // m.degree=d}
private abbrev qB (d cut:ℕ) :=qK9H6va.Lh d cut
private def key (B:ℕ) (m:Exponent) :ℕ :=
  ((m.weight m9*B+m 3)*B+m 2)*B+m 1
private theorem key_compare (u v :af 54) :key 55 u.val<key 55 v.val↔key 57 u.val<key 57 v.val := by
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
private def addOne (i:Fin 4) (m:Exponent) :Exponent:=m+Finsupp.single i 1
private theorem addOne_degree (i:Fin 4) (m:Exponent) :
    (addOne i m).degree=m.degree+1 := by
  rw [addOne,map_add,Finsupp.degree_single]
private def raise (i:Fin 4) {d:ℕ} (u:af d) :af (d+1) :=
  ⟨addOne i u.val,by rw [addOne_degree,u.property]⟩
private theorem raise_key (i:Fin 4) (m:Exponent) :
    key 57 (addOne i m)=key 57 m+key 57 (Finsupp.single i 1) := by
  fin_cases i <;> simp [key,oG,addOne,Finsupp.add_apply] <;> omega
private theorem key_unit (i:Fin 4) :1≤key 57 (Finsupp.single i 1) := by
  fin_cases i <;> simp [key,oG]
private theorem key_unit_lt (i:Fin 4) (hi:i≠1) :1<key 57 (Finsupp.single i 1) := by
  fin_cases i <;> simp [key,oG] at *
private def lower (i:Fin 4) {d:ℕ} (u:af (d+1)) (h:u.val i≠0) :af d:= by
  have hh:Finsupp.single i 1≤u.val :=Finsupp.single_le_iff.mpr (by omega)
  have hd:=congrArg Finsupp.degree (tsub_add_cancel_of_le hh)
  rw [map_add,Finsupp.degree_single,u.property] at hd
  exact ⟨u.val-Finsupp.single i 1,Nat.add_right_cancel hd⟩
private theorem lower_earlier {d:ℕ} (e :af d) (v :af (d+1)) (i:Fin 4) (hi:v.val i≠0)
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
private def raisedCol {d cut:ℕ} (m:qB d cut) :qB (d+1) cut:= by
  have h:=m.property
  rw [Ew,xH] at h
  refine ⟨addOne 0 m.val,?_⟩
  rw [Ew,addOne_degree,xH,h.1]
  simpa [addOne,Finsupp.add_apply,Finsupp.single_apply] using h.2
private def project (d cut:ℕ) :Form →ₗ[Ground] (qB d cut→Ground) :=
  LinearMap.pi fun m=>lcoeff Ground m.val
private def rawForm (u:Exponent) :Form:=bind₁ raw (monomial u 1)
private theorem ad7 {d cut:ℕ} (u:af d) :
    project d cut (rawForm u.val)=yv Subtype.val (aD u.val) := by
  funext m
  exact ao9 u.val m.val (u.property.trans m.property.1.symm)
private def nextSpan {d:ℕ} (e :af d) (cut:ℕ) :Submodule Ground (qB d cut→Ground) :=
  Submodule.span Ground (Set.range fun v : {v :af d // key 57 v.val<key 57 e.val} =>
    yv Subtype.val (aD v.val.val))
private def down (d cut:ℕ) : (qB (d+1) cut→Ground) →ₗ[Ground] (qB d cut→Ground) :=
  LinearMap.pi fun m=>((m.val 0:Ground)+1)•LinearMap.proj (raisedCol m)
private theorem down_eq {d cut:ℕ} (F:Form) :
    down d cut (project (d+1) cut F)=project d cut (pderiv 0 F) := by
  funext m
  change ((m.val 0:Ground)+1)*F.coeff (addOne 0 m.val)=(pderiv 0 F).coeff m.val
  rw [coeff_pderiv,mul_comm]
  rfl
private def direction :Derivation Ground Form Form:=pderiv 0+pderiv 1+pderiv 2+pderiv 3
private theorem deriv_raw_X (j:Fin 4) :
    pderiv 0 (raw j)=bind₁ raw (direction (MvPolynomial.X j)) := by
  fin_cases j <;> simp [raw,direction,pderiv_X]
private theorem deriv_raw (F:Form) :pderiv 0 (bind₁ raw F)=bind₁ raw (direction F) := by
  induction F using MvPolynomial.induction_on with
  | C a=>simp [derivation_C]
  | add F G hF hG=>simp only [map_add,hF,hG]
  | mul_X F j hF =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,bind₁_X_right,← hF,← deriv_raw_X]
private theorem amf (m:Exponent) (z :Ground) : (monomial m z :Form)=z•monomial m 1 := by
  rw [smul_monomial,smul_eq_mul,mul_one]
private theorem deriv_row {d cut:ℕ} (v :af (d+1)) :
    down d cut (project (d+1) cut (rawForm v.val)) =
      ∑ i:Fin 4,(v.val i:Ground)•project d cut (rawForm (v.val-Finsupp.single i 1)) := by
  rw [down_eq,rawForm,deriv_raw]
  simp only [direction,Derivation.add_apply,Fin.sum_univ_four,pderiv_monomial,one_mul,map_add,rawForm]
  congr 3 <;> rw [amf,map_smul,map_smul]
private theorem deriv_term_mem {d cut:ℕ} (e :af d) (v :af (d+1)) (i:Fin 4)
    (h:key 57 v.val≤key 57 (raise 1 e).val)
    (hs :key 57 v.val<key 57 (raise 1 e).val∨i≠1) :
    (v.val i:Ground)•project d cut (rawForm (v.val-Finsupp.single i 1))∈nextSpan e cut:= by
  by_cases hi:v.val i=0
  · simp [hi]
  · let u:=lower i v hi
    change (v.val i:Ground)•project d cut (rawForm u.val)∈nextSpan e cut
    rw [ad7]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u,lower_earlier e v i hi h hs⟩,rfl⟩)
private theorem descend {d cut:ℕ} (e :af d) (hd:d<56)
    (h:project (d+1) cut (rawForm (raise 1 e).val)∈nextSpan (raise 1 e) cut) :
    project d cut (rawForm e.val)∈nextSpan e cut:= by
  classical
  have hm: (nextSpan (raise 1 e) cut).map (down d cut)≤nextSpan e cut:= by
    apply (Submodule.map_span_le _ _ _).mpr
    rintro _ ⟨v,rfl⟩
    change down d cut (yv _ (aD v.val.val))∈nextSpan e cut
    rw [← ad7 v.val,deriv_row]
    exact Submodule.sum_mem _ fun i _=>deriv_term_mem e v.val i v.property.le (Or.inl v.property)
  have hh:=hm (Submodule.mem_map_of_mem (f :=down d cut) h)
  rw [deriv_row,← Finset.sum_erase_add _ _ (Finset.mem_univ (1 :Fin 4))] at hh
  have hsum: (∑ i∈(Finset.univ :Finset (Fin 4)).erase 1,
      ((raise 1 e).val i:Ground)•project d cut (rawForm ((raise 1 e).val-Finsupp.single i 1)))
      ∈ nextSpan e cut :=
    Submodule.sum_mem _ fun i hi=>deriv_term_mem e (raise 1 e) i le_rfl
      (Or.inr (Finset.ne_of_mem_erase hi))
  have htarget :=Submodule.sub_mem _ hh hsum
  rw [add_sub_cancel_left] at htarget
  change (((addOne 1 e.val) 1 :ℕ) :Ground) •
    project d cut (rawForm (addOne 1 e.val-Finsupp.single 1 1))∈nextSpan e cut at htarget
  have hcancel:addOne 1 e.val-Finsupp.single 1 1=e.val := by
    simp [addOne]
  rw [hcancel] at htarget
  have hpos : (addOne 1 e.val) 1≠0:= by simp [addOne,Finsupp.add_apply]
  have he :=e.property
  rw [cF] at he
  have hb: (addOne 1 e.val) 1≤56:= by simp [addOne,Finsupp.add_apply]; omega
  have hz : (((addOne 1 e.val) 1 :ℕ) :Ground)≠0:= by
    simpa only [Nat.cast_zero] using qhonTAe.cEo hb (by decide :0≤56) hpos
  have ht:=Submodule.smul_mem (nextSpan e cut) (((addOne 1 e.val) 1 :ℕ) :Ground)⁻¹ htarget
  rwa [smul_smul,inv_mul_cancel₀ hz,one_smul] at ht
open qwzqCne (aY)

def to56 (e :aY) :qHde8fc.aY:=raise 1 (raise 1 e)
theorem to56_apply_of_ne (e :aY) (i:Fin 4) (hi:i≠1) :
    (to56 e).val i=e.val i:= by
  simp [to56,raise,addOne,Finsupp.add_apply,Finsupp.single_eq_of_ne hi]
theorem transfer (e :aY) (cut:ℕ)
    (h:qHde8fc.cE cut (qHde8fc.aD (to56 e).val) ∈
      qhonTAe.jZ (to56 e) cut) :jZ e cut:= by
  have key56 (u v :qHde8fc.aY) :
      qHde8fc.dZ u<qHde8fc.dZ v↔key 57 u.val<key 57 v.val := by
    rw [qHde8fc.dZ,qHde8fc.dZ,qHde8fc.Sj,qHde8fc.Sj]
    unfold key
    omega
  have key54 (u v :aY) :
      qwzqCne.dZ u<qwzqCne.dZ v↔key 57 u.val<key 57 v.val := by
    rw [← key_compare u v,qwzqCne.dZ,qwzqCne.dZ,
      qwzqCne.Sj,qwzqCne.Sj]
    unfold key
    omega
  have hsource :qhonTAe.jZ (to56 e) cut≤nextSpan (to56 e) cut:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨⟨v.val,(key56 _ _).mp v.property⟩,rfl⟩
  have ht:yv (κ:=qB 56 cut) Subtype.val (aD (to56 e).val) ∈
      nextSpan (to56 e) cut:=hsource h
  rw [← ad7 (to56 e)] at ht
  have h54 :=descend e (by decide) (descend (raise 1 e) (by decide) ht)
  rw [ad7] at h54
  apply (show nextSpan e cut≤_ from Submodule.span_le.mpr ?_) h54
  rintro _ ⟨v,rfl⟩
  exact Submodule.subset_span ⟨⟨v.val,(key54 _ _).mpr v.property⟩,rfl⟩
end
end q1racBe
