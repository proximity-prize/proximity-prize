import ProximityPrize.SubmissionLower.ZbnhR9d
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 12
namespace qBPZs8a
noncomputable section
open Polynomial Finset
open P6 (K p dw)
open P6_7_1
open cu (L FX Jet qD A5)
open DP (d3r d3q)
open pI (oU)
open akZ (aRJ ajz cN5 bLw)
open scoped Classical
abbrev aV {x :Input} (P:Poles x) (i:Intro) :=
  P.rows (shape i) (cutoff (shape i))
theorem anchor_caps {x :Input} {P:Poles x} (R:EarlyPicks x P) :
    oU R.anchorRow anchor :=
  d3r P.crt x.word (R.free ⟨0,by decide⟩).mem
theorem cutoff_lt (s :cu.Shape) (hm:0<s.m) :cutoff s<s.m*dw :=
  Nat.sub_lt (Nat.mul_pos hm (by decide)) (by decide)
theorem anchor_zero {x :Input} {P:Poles x} (R:EarlyPicks x P) :
    ∀ γ∈x.Γ,Mark x R.anchorRow γ:= by
  have hm:=(R.free ⟨0,by decide⟩).mem
  change R.anchorRow∈P.rows anchor (buffer x.h 0 anchor) at hm
  rw [buffer,Nat.mul_zero,Nat.sub_zero] at hm
  exact fun _ hγ=>necessary P (cutoff_lt anchor (by decide)) hm hγ
theorem reference {x :Input} {P:Poles x} (R:EarlyPicks x P) :
    Nonempty (Reference x P) := by
  by_contra h
  have hspan:aV P referenceIndex ≤ ⊥ := Submodule.span_le.mpr (by
    rintro _ ⟨A,hA,rfl⟩
    exact (Submodule.mem_bot FX).mpr (by
      by_contra hz
      exact h ⟨⟨A,hA,hz⟩⟩))
  exact (R.intro referenceIndex).ne_zero ((Submodule.mem_bot FX).mp
    (hspan (d3q P.crt x.word rfl rfl rfl le_rfl (Nat.sub_le _ _)
      (R.intro referenceIndex).mem)))
private theorem intro_room (i:Intro) :2*packetHi*dI i<(shape i).m*dw:= by
  fin_cases i <;> decide
private theorem intro_small (i:Intro) : (shape i).U<p:= by
  fin_cases i <;> decide
theorem intro_positive (i:Intro) :0<(shape i).m:= by
  fin_cases i <;> decide
private theorem hasse_mem {x :Input} {P:Poles x} (R:EarlyPicks x P)
    (i:Intro) (v :Fin 2) (r :ℕ) (hr :r≤dI i) :
    A5 v r (R.intro i).row∈aV P i:= by
  have hm:=Nat.mul_le_mul_left (2*x.h) hr
  have ht:=(Nat.mul_le_mul_right (dI i)
    (Nat.mul_le_mul_left 2 (heights x).2)).trans_lt (intro_room i)
  have hle :2*x.h*dI i≤ cutoff (shape i) :=Nat.le_sub_one_of_lt ht
  have hW:buffer x.h (dI i) (shape i)+2*x.h*r≤ cutoff (shape i) := by
    unfold buffer
    exact (Nat.add_le_add_left hm _).trans_eq (Nat.sub_add_cancel hle)
  exact d3q P.crt x.word rfl rfl rfl le_rfl hW
    (atp.d3s P.crt x.word (R.intro i).mem v r)
private theorem avoid {F E α:Type*} [Field F] [Infinite F] [AddCommGroup E] [Module F E]
    (V:Submodule F E) (D:Finset α) (I:α→Submodule F E)
    (missing : ∀ f∈D,∃ g∈V,g∉I f) :
    ∃ g∈V,∀ f∈D,g∉I f := by
  induction D using Finset.induction_on with
  | empty=>exact ⟨0,V.zero_mem,by simp⟩
  | @insert f D hf ih =>
    obtain ⟨a,ha,hgood⟩:=ih (fun d hd=>missing d (mem_insert_of_mem hd))
    obtain ⟨b,hb,hbad⟩:=missing f (mem_insert_self _ _)
    let bad (d:α) := {c:F | a+c•b∈I d}
    have finite (d:α) (hd:d∈insert f D) : (bad d).Finite := by
      apply Set.Subsingleton.finite
      intro v hv w hw
      by_contra hn
      have he : (v-w)•b∈I d:= by
        rw [sub_smul,← show (a+v•b)-(a+w•b)=v•b - w•b by abel]
        exact (I d).sub_mem hv hw
      have hdb:b∈I d:= by
        simpa only [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hn),one_smul] using
          (I d).smul_mem (v-w)⁻¹ he
      rcases mem_insert.mp hd with rfl | hd
      · exact hbad hdb
      · exact hgood d hd (by simpa only [add_sub_cancel_right] using (I d).sub_mem hv ((I d).smul_mem v hdb))
    obtain ⟨c,hc⟩:=(Set.finite_iUnion (fun d : {d // d∈insert f D} => finite d d.2)).exists_notMem
    exact ⟨a+c•b,V.add_mem ha (V.smul_mem c hb),fun d hd hz =>
      hc (Set.mem_iUnion.mpr ⟨⟨d,hd⟩,hz⟩)⟩
private def specialize (z :K) :Jet →+* qQ.IW :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (qD z))
private def zeroAt (z :K) :Submodule FX Jet where
  carrier :=RingHom.ker (specialize z)
  zero_mem' := map_zero _
  add_mem' := fun ha hb=> by
    change specialize z _=0 at ha hb ⊢
    rw [map_add,ha,hb,add_zero]
  smul_mem' := fun a g hg=> by
    change specialize z g=0 at hg
    change specialize z (a•g)=0
    rw [Algebra.smul_def,map_mul,hg,mul_zero]
private def multiples (f :Jet) :Submodule FX Jet :=
  (Ideal.span ({f} : Set Jet)).restrictScalars FX
private theorem multiples_iff (f g:Jet) :g∈multiples f↔f∣g :=
  Ideal.mem_span_singleton (x :=g) (y :=f)
private theorem avoid_both (x :Input) (V:Submodule FX Jet) (D:Finset Jet)
    (missing : ∀ f∈D,∃ g∈V,¬ f∣g) :
    ∃ g∈V,BaseAvoid x V g ∧ ∀ f∈D,¬ f∣g:= by
  let:Infinite FX:=Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
  let good:=x.Γ.filter fun γ => ∃ g∈V,seedSpecialize g (x.M.label γ)≠0
  let bad:Jet ⊕ K→Submodule FX Jet :=
    Sum.elim multiples (fun γ=>zeroAt (x.M.label γ))
  have hm : ∀ a∈D.disjSum good,∃ g∈V,g∉bad a := by
    intro a ha
    cases a with
    | inl f =>
      obtain ⟨g,hg,hn⟩:=missing f (inl_mem_disjSum.mp ha)
      exact ⟨g,hg,fun h=>hn ((multiples_iff f g).mp h)⟩
    | inr γ=>exact (mem_filter.mp (inr_mem_disjSum.mp ha)).2
  obtain ⟨g,hg,hgood⟩:=avoid (F:=FX) (E :=Jet) V (D.disjSum good) bad hm
  refine ⟨g,hg,?_,fun f hf hd =>
    hgood (Sum.inl f) (inl_mem_disjSum.mpr hf) ((multiples_iff f g).mpr hd)⟩
  intro γ hγ hz Q hQ
  by_contra hn
  exact hgood (Sum.inr γ) (inr_mem_disjSum.mpr (mem_filter.mpr ⟨hγ,Q,hQ,hn⟩)) hz
private def fails {x :Input} (P:Poles x) (f :Jet) (n:ℕ) :Prop :=
  n=last ∨ ∃ i:Intro,i.val=n ∧ ∃ g∈aV P i,¬ f∣g
private theorem fail_exists {x :Input} (P:Poles x) (f :Jet) :
    ∃ n,fails P f n:=⟨last,Or.inl rfl⟩
private def first {x :Input} (P:Poles x) (f :Jet) :Origin :=
  ⟨Nat.find (fail_exists P f),Nat.lt_succ_of_le (Nat.find_min' (fail_exists P f) (Or.inl rfl))⟩
private theorem before_first {x :Input} {P:Poles x} {f :Jet} {i:Intro}
    (h:i.val<(first P f).val) : ∀ g∈aV P i,f∣g :=
  fun g hg=> by
    by_contra hd
    exact Nat.find_min (fail_exists P f) h (Or.inr ⟨i,rfl,g,hg,hd⟩)
private theorem first_missing {x :Input} {P:Poles x} {f :Jet} {i:Intro}
    (h:i.val=(first P f).val) : ∃ g∈aV P i,¬ f∣g:= by
  rcases Nat.find_spec (H :=fail_exists P f) with he | ⟨j,hj,hn⟩
  · exact ((h.trans he).not_lt i.isLt).elim
  · have hj' : j=i:=Fin.ext (hj.trans h.symm)
    exact hj' ▸ hn
theorem introCap_succ (i:Intro) (j:Fin 3) :
    introCap (i.val+1) j=min (introCap i.val j) (bgK (shape i) j/(dI i+1)) := by
  unfold introCap
  rw [List.take_succ_eq_append_getElem i.isLt,List.foldl_append]
  rfl
structure Schedule {x :Input} (P:Poles x) (D:Finset Jet) where
  origin :Jet→Origin
  cut:Intro→Jet
  nested : ∀ i≤last,∀ j,ajz (D.filter (fun f=>i≤(origin f).val)) j≤ introCap i j
  survives : ∀ f i,i.val<(origin f).val → ∀ g∈aV P i,f∣g
  proper : ∀ f∈D,∀ i,i.val=(origin f).val → ¬ f∣cut i
  mem : ∀ i,cut i∈aV P i
  avoids : ∀ i,BaseAvoid x (aV P i) (cut i)
theorem schedule {x :Input} {P:Poles x} (R:EarlyPicks x P) {D:Finset Jet}
    (hD:aRJ R.anchorRow D)
    (hcap : ∀ j,ajz D j≤bgK anchor j) :Nonempty (Schedule P D) := by
  have exists_cut (i:Intro) :=
    avoid_both x (aV P i) (D.filter (fun f=>i.val=(first P f).val))
      (fun f hf=>first_missing (mem_filter.mp hf).2)
  choose cut hmem ha hproper using exists_cut
  refine ⟨⟨first P,cut,?_,fun _ _=>before_first,?_,hmem,ha⟩⟩
  · suffices h : ∀ n≤last,∀ T⊆D,
        (∀ f∈T,n≤(first P f).val) → ∀ j,ajz T j≤ introCap n j by
      exact fun n hn j=>h n hn _ (filter_subset _ _) (fun f hf=>(mem_filter.mp hf).2) j
    intro n
    induction n with
    | zero=>exact fun _ _ ht _ j=>(cN5 ht j).trans (hcap j)
    | succ n ih =>
      intro hn T hT hall j
      let i:Intro:=⟨n,Nat.lt_of_succ_le hn⟩
      have hc:=ih (Nat.le_of_succ_le hn) T hT (fun f hf=>(Nat.le_succ n).trans (hall f hf)) j
      have hr :=bLw (hD.mono hT) (R.intro i).ne_zero
        (d3r P.crt x.word (R.intro i).mem) (intro_small i) (dI i)
        (fun f hf v a ha=>before_first (show i.val<(first P f).val from hall f hf)
          _ (hasse_mem R i v a ha)) j
      rw [introCap_succ i j]
      exact le_min hc hr
  · intro f hf i hi
    exact hproper i f (mem_filter.mpr ⟨hf,hi⟩)
end
end qBPZs8a
end
section
set_option autoImplicit true
namespace q9scLLa
noncomputable section
open Polynomial
open P6 (K p dw blockLength)
open P6_7_1 (Input degree)
open cu (L Equation yq)
open qHEUR1a (Raw embed height threshold)
abbrev modulus :ℕ:=threshold+1+degree
abbrev slope :ℕ:=13740
abbrev rate :ℕ:=0x14d56c7200
def weight (F:Raw) :ℕ :=
  F.support.sup fun i=>(F.coeff i).support.sup fun a =>
    ((F.coeff i).coeff a).natDegree+i*degree
def Zk (x :Input) (f :Equation) (γ:K) :Prop :=
  yq f (x.M.label γ) (x.F.scalar γ)=0
def site (x :Input) (γ:K) :Fin 2→L :=
  let z :=algebraMap K L (x.M.label γ)
  ![z,z^p]
def Sheet (F:Raw) :Prop :=
  Irreducible F∧Irreducible (embed F)∧0<F.natDegree∧F.natDegree≤12 ∧
    0<height F∧height F≤142
theorem multiplier_surplus (v :ℕ) :
    (1001*v+1)*(2*v+1)*(106*degree)<3*(1000*v+1)*(v+1)*modulus := by
  have h:3*(1000*v+1)*(v+1)*modulus =
      (1001*v+1)*(2*v+1)*(106*degree) +
      (0x10da7ab8*v^2+0x35ccd223b*v+0xdc9383) := by
    change 3*(1000*v+1)*(v+1)*9533441=(1001*v+1)*(2*v+1)*14144640+_
    ring
  rw [h]
  exact Nat.lt_add_of_pos_right (by positivity)
def polar (e :ℕ) :ℕ:=(6*e-2)*threshold-3*e^2*degree
def lowNumerator (e :ℕ) :ℕ :=
  (7+6*e)*(dw-degree)+2*e*blockLength+polar e
theorem variation_room {e :ℕ} (he :1≤e) (hE :e≤12) :
    e*degree≤threshold∧e<p∧(2*e-1)*threshold-e^2*degree<p ∧
    3*e^2*degree≤(6*e-2)*threshold∧2*threshold-degree≤polar e ∧
    lowNumerator e+(4*e^2+1)*(dw-degree)≤ slope*(dw-degree) := by
  interval_cases e <;> decide
end
end q9scLLa
end
