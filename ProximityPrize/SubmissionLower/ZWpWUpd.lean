import ProximityPrize.SubmissionLower.Zyuvo1c
import ProximityPrize.SubmissionLower.ZVbskte
import ProximityPrize.SubmissionLower.ZwYh3la
import ProximityPrize.SubmissionLower.ZwuC0Sd
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qqwac6b
noncomputable section
open Polynomial Finset
open P6 (K p dw blockLength)
open P6_7_1 (Input degree heights)
open q3rjQGe (quadraticRate)
open P5_7 (farAgreement)
open qrsE1ie (CoverIncidence NodeAllowance discriminant geomSquare)
open quN7Z4a (sheet physicalWeight compressionWidth)
open P5_7_7 (UJ mem_sites linear_count)
open gT (aQ abX)
open private disc_degree from ProximityPrize.SubmissionLower.ZcErkXc
open private hitmiss_pair from ProximityPrize.SubmissionLower.Zz5zkKe
open scoped Classical
def c1 :Prop :=qrsE1ie.c1
def c2 :Prop :=qrsE1ie.c2
private theorem inputMarks {x :Input} {T:Finset K} (hT:T⊆x.Γ) :
    UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
    fun γ hγ=>(P6_7.aic x.F (hT hγ)).trans (Nat.add_le_add_left (heights x).2 _),?_⟩
  intro γ hγ
  let m:=x.F.mark γ (hT hγ)
  exact (by decide :farAgreement≤dw).trans
    (m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi)))
private theorem count_nodes {w T U z s B} (M:UJ degree w T z s) (hU:U⊆T)
    (hnodes :NodeAllowance U s w B) :U.card≤6*B+1 := by
  have MU:UJ degree w U z s :=⟨M.Kw.mono hU,M.sections.mono hU,
    fun γ hγ=>M.degree γ (hU hγ),fun γ hγ=>M.dw γ (hU hγ)⟩
  have hgap:0<P5_7.gap degree := by decide
  by_cases hB:B=0
  · subst B
    simp only [mul_zero,zero_add]
    by_contra! h
    obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp h
    obtain ⟨i,hi⟩:=card_pos.mp (hgap.trans_le (hitmiss_pair MU ha hb hab))
    obtain ⟨hia,hib⟩:=mem_sdiff.mp hi
    rcases hnodes i with hh | hm
    · exact (not_lt_of_ge hh) (card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,mem_sites.mp hia⟩⟩)
    · exact (not_lt_of_ge hm) (card_pos.mpr ⟨b,mem_filter.mpr ⟨hb,mt mem_sites.mpr hib⟩⟩)
  have hc:=linear_count MU (Nat.pos_of_ne_zero hB)
    (show P5_7.gap degree≤blockLength by decide) hnodes
  have hn:=Nat.mul_le_mul_right B (show blockLength≤P5_7.gap degree*6 by decide)
  exact (Nat.le_of_mul_le_mul_left (hc.trans (by simpa only [Nat.mul_assoc] using hn)) hgap).trans
    (Nat.le_add_right _ _)
private theorem dQt {w T z s H} (M:UJ degree w T z s)
    (C:CoverIncidence T s w H) :T.card≤29*H+2 := by
  have hc:T.card≤5*H+(C.left.card+C.right.card) := by
    rw [← card_sdiff_add_card_eq_card (union_subset C.left_sub C.right_sub)]
    exact Nat.add_le_add C.zJ (card_union_le _ _)
  calc
    _≤5*H+((6*(2*C.leftDegree*H)+1)+(6*(2*C.rightDegree*H)+1)) :=
      hc.trans (Nat.add_le_add_left (Nat.add_le_add (count_nodes M C.left_sub C.left_nodes)
        (count_nodes M C.right_sub C.right_nodes)) _)
    _=5*H+12*H*(C.leftDegree+C.rightDegree)+2 := by ring
    _≤5*H+12*H*2+2 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ C.boS) _) _
    _ = _:= by ring
theorem of_children (h1 :c1) (h2 :c2) :qHuUuEa.c1 := by
  intro x _ T J Q H A
  have hrank : ∃ d:ℕ,Module.finrank aQ (abX J)=d*2 := by
    obtain ⟨_,C₀,_,_,_,h,_,_⟩:=A.curve
    exact ⟨C₀.totalDegree,h⟩
  obtain ⟨d,hd⟩:=hrank
  obtain ⟨C₀,hC₀,_,⟨S⟩⟩:=sheet (by decide :0<2) A.curve hd A.marks
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  have M:=inputMarks (x :=x) A.subset
  have hcount:T.card≤29*H+2 := by
    by_cases hw:compressionWidth degree 2≤physicalWeight degree S.root.equation
    · have hc:=h1 C₀ J T x.M.label x.F.scalar degree H S (by decide) hw M.Kw M.degree
      omega
    by_cases hs :geomSquare S.root.equation
    · obtain ⟨C⟩:=qWcuPdb.proof C₀ J T x.M.label x.F.scalar x.M.word H S hs M.Kw
      exact dQt M C
    have hdeg: (discriminant S.root.equation).natDegree<p :=
      (disc_degree degree S.root.equation).trans_lt
        ((Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hw) (by decide)).trans
          (by decide :2*compressionWidth degree 2<p))
    have hc:=h2 C₀ J T x.M.label x.F.scalar H S hdeg hs M.Kw
    omega
  have hc: (T.card:ℚ)≤29*H+2 := by exact_mod_cast hcount
  have hr : (29:ℚ)≤quadraticRate := by
    change (29:ℚ)≤13+8*262144/46300
    norm_num
  have hh:=mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (α:=ℚ) H)
  have hm: (0:ℚ)≤16*(2*(Q.totalDegree :ℚ)) := by positivity
  linarith only [hc,hh,hm]
end
end qqwac6b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 12
namespace qNRjwze
noncomputable section
open Polynomial Finset
open P6 (K p dw)
open P6_7 (RectTail)
open P6_7_2
open P6_7_2_3 (Origin last introCap)
open cu (L FX Jet Shape j9 A5)
open DP (U4 d3r d3q ad0)
open pI (oU)
open TD (auN)
open akZ (aRJ ajz cN5 bLw)
open private avoid multiples multiples_iff from ProximityPrize.SubmissionLower.ZwYh3la
open scoped Classical
theorem emE {b:RectTail} (x :Input b) :x.h≤(Bs b).hi:= by
  have hu:=x.kA.2
  have hp:b.kA.hi≤(Bs b).hi:= by cases b <;> decide
  change x.M.iF≤(b.kA.hi:ℤ) at hu
  change x.M.iF.toNat≤(Bs b).hi
  omega
theorem necessary {b:RectTail} {x :Input b} (P:Poles x) {s :Shape} {W:ℕ}
    (hw:W<s.m*dw) {g:Jet} (hg:g∈P.rows s W) {γ:K} (hγ:γ∈x.Γ) :
    Mark x g γ:= by
  let M:=x.F.mark γ hγ
  have hd: (j9 (x.F.scalar γ)).natDegree≤131071+x.h:= by
    rw [j9,Polynomial.natDegree_map]
    exact P6_7.aic x.F hγ
  refine atp.dPr P.crt x.word P.nodes _ _ (P.marks γ hγ) hd M.bad.support
    M.bad.dw ?_ s _ hw g hg
  intro j hj
  rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,M.scalar_hits j hj]
private theorem cutoff_lt {s :Shape} (hm:0<s.m) (h r :ℕ) :
    cutoff h r s<s.m*dw :=
  (Nat.sub_le ..).trans_lt (Nat.sub_lt (Nat.mul_pos hm (by decide)) (by decide))
theorem anchor_caps {b:RectTail} {x :Input b} {P:Poles x} (pick :Picks (b:=b) x.h P.rows) :
    oU (anchorRow pick) (free b 0) :=
  d3r P.crt x.word (pick.free_mem 0)
theorem anchor_zero {b:RectTail} {x :Input b} {P:Poles x} (pick :Picks (b:=b) x.h P.rows)
    {γ:K} (hγ:γ∈x.Γ) :Mark x (anchorRow pick) γ :=
  necessary P (cutoff_lt (by cases b <;> decide) _ _) (pick.free_mem 0) hγ
private theorem intro_room (b:RectTail) (i:Aux) :
    2*(Bs b).hi*auxReserve i<(auxiliary b i).m*dw:= by
  cases b <;> fin_cases i <;> decide
private theorem intro_small (b:RectTail) (i:Aux) : (auxiliary b i).U<p:= by
  cases b <;> fin_cases i <;> decide
theorem aux_positive (b:RectTail) (i:Aux) :0<(auxiliary b i).m:= by
  cases b <;> fin_cases i <;> decide
private theorem hasse_mem {b:RectTail} {x :Input b} {P:Poles x}
    (pick :Picks (b:=b) x.h P.rows) (i:Aux) (v :Fin 2) (r :ℕ) (hr :r≤auxReserve i) :
    A5 v r (pick.auxRow i)∈aV P i:= by
  have ht:=(Nat.mul_le_mul_right (auxReserve i)
    (Nat.mul_le_mul_left 2 (emE x))).trans_lt (intro_room b i)
  have hw:2*x.h*auxReserve i≤(auxiliary b i).m*dw-1 :=Nat.le_sub_one_of_lt ht
  have hW:cutoff x.h (auxReserve i) (auxiliary b i)+2*x.h*r ≤
      cutoff x.h 0 (auxiliary b i) := by
    simp only [cutoff,Nat.mul_zero,Nat.sub_zero]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left (2*x.h) hr) _).trans_eq (Nat.sub_add_cancel hw)
  exact d3q P.crt x.word rfl rfl rfl le_rfl hW
    (atp.d3s P.crt x.word (pick.aux_mem i) v r)
private theorem reference {b:RectTail} {x :Input b} {P:Poles x}
    (pick :Picks (b:=b) x.h P.rows) :Nonempty (Reference P) := by
  by_contra h
  have hspan:aV P 9 ≤ ⊥ := Submodule.span_le.mpr (by
    rintro _ ⟨A,hA,rfl⟩
    refine (Submodule.mem_bot FX).mpr ?_
    by_contra hz
    exact h ⟨⟨A,hA,hz⟩⟩)
  exact pick.aux_ne 9 ((Submodule.mem_bot FX).mp (hspan
    (d3q P.crt x.word rfl rfl rfl le_rfl (by
      simp only [cutoff,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _) (pick.aux_mem 9))))
private def fails {b:RectTail} {x :Input b} (P:Poles x) (f :Jet) (n:ℕ) :Prop :=
  n = 13 ∨ ∃ i:Aux,i.val=n ∧ ∃ g∈aV P i,¬ f∣g
private theorem fail_exists {b:RectTail} {x :Input b} (P:Poles x) (f :Jet) :
    ∃ n,fails P f n:=⟨13,Or.inl rfl⟩
private def first {b:RectTail} {x :Input b} (P:Poles x) (f :Jet) :Origin :=
  ⟨Nat.find (fail_exists P f),Nat.lt_succ_of_le (Nat.find_min' (fail_exists P f) (Or.inl rfl))⟩
private theorem before_first {b:RectTail} {x :Input b} {P:Poles x} {f :Jet} {i:Aux}
    (h:i.val<(first P f).val) : ∀ g∈aV P i,f∣g:= fun g hg=> by
  by_contra hd
  exact Nat.find_min (fail_exists P f) h (Or.inr ⟨i,rfl,g,hg,hd⟩)
private theorem first_missing {b:RectTail} {x :Input b} {P:Poles x} {f :Jet} {i:Aux}
    (h:i.val=(first P f).val) : ∃ g∈aV P i,¬ f∣g:= by
  rcases Nat.find_spec (H :=fail_exists P f) with he | ⟨j,hj,hn⟩
  · exact ((h.trans he).not_lt i.isLt).elim
  · exact (Fin.ext (hj.trans h.symm) :j=i) ▸ hn
theorem intro_succ (b:RectTail) (i:Aux) (j:Fin 3) :
    introCap b i.succ j=min (introCap b i.castSucc j) (auN (auxiliary b i) j/(auxReserve i+1)) := by
  unfold introCap
  have hi:i.val<(List.ofFn fun l:Aux=>(auxReserve l,auxiliary b l)).length:= by
    simpa only [List.length_ofFn] using i.isLt
  rw [show i.succ.val=i.val+1 from rfl,List.take_succ_eq_append_getElem hi,List.foldl_append]
  simp only [List.getElem_ofFn,List.foldl_cons,List.foldl_nil]
  rfl
structure Schedule {b:RectTail} {x :Input b} (P:Poles x) (R:Reference P) (D:Finset Jet) where
  origin :Jet→Origin
  cut:Aux→Jet
  nested : ∀ o j,ajz (D.filter (fun f=>o≤origin f)) j≤ introCap b o j
  last_dvd : ∀ f∈D,origin f=last→f∣U4 R.raw
  proper : ∀ f∈D,∀ i,i.val=(origin f).val → ¬ f∣cut i
  mem : ∀ i,cut i∈aV P i
theorem schedule {b:RectTail} {x :Input b} {P:Poles x} (pick :Picks (b:=b) x.h P.rows)
    {D:Finset Jet} (hD:aRJ (anchorRow pick) D)
    (hcap : ∀ j,ajz D j≤auN (free b 0) j) :
    ∃ R:Reference P,Nonempty (Schedule P R D) := by
  obtain ⟨R⟩:=reference pick
  have exists_cut (i:Aux) :
      ∃ g∈aV P i,∀ f∈D.filter (fun f=>i.val=(first P f).val),¬ f∣g:= by
    let:Infinite FX:=Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
    simpa only [multiples_iff] using
      avoid (aV P i) (D.filter (fun f=>i.val=(first P f).val)) multiples
        (fun f hf=> by simpa only [multiples_iff] using first_missing (mem_filter.mp hf).2)
  choose cut hmem hproper using exists_cut
  refine ⟨R,⟨⟨first P,cut,?_,?_,?_,hmem⟩⟩⟩
  · suffices h : ∀ o:Origin,∀ T⊆D,(∀ f∈T,o≤first P f) →
        ∀ j,ajz T j≤ introCap b o j by
      exact fun o j=>h o _ (filter_subset _ _) (fun f hf=>(mem_filter.mp hf).2) j
    intro o
    refine Fin.induction ?_ ?_ o
    · exact fun _ hT _ j=>(cN5 hT j).trans (hcap j)
    · intro i ih T hT hall j
      have hc:=ih T hT (fun f hf=>(show i.castSucc≤ i.succ from Nat.le_succ _).trans (hall f hf)) j
      have hr :=bLw (hD.mono hT) (pick.aux_ne i)
        (d3r P.crt x.word (pick.aux_mem i)) (intro_small b i) (auxReserve i)
        (fun f hf v a ha=>before_first (show i.val<(first P f).val from hall f hf)
          _ (hasse_mem pick i v a ha)) j
      rw [intro_succ]
      exact le_min hc hr
  · intro f _ he
    exact before_first (i:=9) (by rw [he]; decide) _ (Submodule.subset_span ⟨R.raw,R.mem,rfl⟩)
  · intro f hf i hi
    exact hproper i f (mem_filter.mpr ⟨hf,hi⟩)
theorem aux_zero {b:RectTail} {x :Input b} {P:Poles x} {i:Aux} {g:Jet}
    (hg:g∈aV P i) {γ:K} (hγ:γ∈x.Γ) :Mark x g γ :=
  necessary P (cutoff_lt (aux_positive b i) _ _) hg hγ
end
end qNRjwze
end
