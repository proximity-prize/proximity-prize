import ProximityPrize.SubmissionLower.ZJb37yc
import ProximityPrize.SubmissionLower.ZrHwqOb
import ProximityPrize.SubmissionLower.Z67mtTa
import ProximityPrize.SubmissionLower.Zy3W3oe
import ProximityPrize.SubmissionLower.ZGCzLxb
import ProximityPrize.SubmissionLower.Za7Od9d
import ProximityPrize.SubmissionLower.ZagvXJe
set_option Elab.async false
open _root_ renaming Fin.addCases_left → zgb, Fin.addCases_right → z5m, Finset → zJe, IsFractionRing.injective → zxb, MvPolynomial.constantCoeff → zuE, Nat.add_le_add → z9f, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
namespace qhXrNmc
theorem proof :q0Nj7Rb.c2 :=P5_7_2_3Q1322.proof
end qhXrNmc
end
section
set_option autoImplicit true
namespace q9NOUMe
theorem proof :q0Nj7Rb.c4 :=qxRGmlc.proof
end q9NOUMe
end
section
set_option autoImplicit true
namespace qlxPgNe
theorem proof :q0Nj7Rb.c5 :=
  qA0rFHd.of_children qYur1ad.proof qnKm5Ba.proof qWpt85c.proof
end qlxPgNe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qFOgTpd
noncomputable section
open Finset
open P6 (K p blockLength dw)
open P5_7 (farAgreement)
open P6_7_3 (Input degree anchor emz)
open cu (Jet qD)
open gT (tK FW)
open pI (NO abM)
open qQ (VN aJr)
open aF0 (BJ YM)
open akZ (aSK)
open baX (mix)
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open scoped Classical
private theorem fixed_marks (x :Input) (G:tK) (hG:abM G 115 25) :
    (x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0).card ≤
      3*((115-25)*YM degree 115 25+25*BJ degree 115)+115^2 := by
  let T:=x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0
  let a :=BJ degree 115
  let v :=YM degree 115 25
  let β:ℚ:=((blockLength-farAgreement:ℕ) :ℚ)/((farAgreement-degree :ℕ) :ℚ)
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hv : (v :ℚ)≤a := by exact_mod_cast (min_le_left a (aF0.power degree*(25-1)+degree))
  have hT:T⊆x.Γ:=filter_subset _ _
  have h:=cSy (x.F.distinct.mono hT) ⟨by decide,by decide,by decide,by decide⟩
    G hG (fun γ hγ=>(mem_filter.mp hγ).2) (β*a) (β*v) (by positivity)
    (mul_le_mul_of_nonneg_left hv hβ) (fun U hU f hf hp hb hj hr=> by
      have hc:=qUJtx6c.ePE (x.F.distinct.mono (hU.trans hT))
        (fun γ hγ=>(P6_7.aic x.F (hT (hU hγ))).trans
          (Nat.add_le_add_left (emz x).2 _))
        (w:=x.M.word) (fun γ hγ =>
          let m:=x.F.mark γ (hT (hU hγ))
          ⟨m.bad.support,(by decide :farAgreement≤dw).trans m.bad.dw,m.scalar_hits⟩)
        (d:=degree) (by decide) (by decide) (by decide) f hf hp hb hj hr
      refine hc.trans_eq ?_
      change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
      unfold mix
      ring)
  have hβ₃:β≤3:= by
    change (82365:ℚ)/46174≤3
    apply (div_le_iff₀ (by decide : (0:ℚ)<46174)).mpr
    exact_mod_cast (show 82365≤3*46174 from by decide)
  have h' : (T.card:ℚ)≤((3*((115-25)*v+25*a)+115^2 :ℕ) :ℚ) := calc
    _≤ mix 115 25 (β*a) (β*v)+(115^2 :ℕ) :=h
    _≤ mix 115 25 (3*a) (3*v)+(115^2 :ℕ) := by unfold mix; gcongr
    _ = _:= by unfold mix; push_cast; ring
  exact_mod_cast h'
theorem anchor_book (x :Input) {f :Jet} {A:NO f anchor.free} (a :aSK A) :
    ∃ gH :zJe K,gH.card≤fixedContentFee ∧
      ∀ γ∈x.Γ,qD (x.M.label γ) a.content=0 ∨
        FW A.equation (x.F.scalar γ)=0→γ∈gH := by
  let T:=x.Γ.filter fun γ=>FW A.equation (x.F.scalar γ)=0
  let S:=x.Γ.filter fun γ=>qD (x.M.label γ) a.content=0
  let C:VN :=⟨a.content,a.content_ne,∅⟩
  have hs :=aJr (T:=S) (label :=x.M.label) (fun _ _ _ _ h=>sub_left_inj.mp h)
    C (a.content_le.trans_lt (by decide)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  have hS:S.card≤(p+1)*1025:= by
    exact (by simpa only [C,card_empty,Nat.add_zero] using hs :_≤(p+1)*a.content.totalDegree).trans
      (Nat.mul_le_mul_left _ a.content_le)
  refine ⟨T∪S,(card_union_le _ _).trans ((z9f (fixed_marks x _ A.equation_caps) hS).trans ?_),?_⟩
  · change 0x1fd7087d0f6≤fixedContentFee
    decide
  · intro γ hγ h
    exact mem_union.mpr (h.symm.imp (fun hz=>mem_filter.mpr ⟨hγ,hz⟩) (fun hz=>mem_filter.mpr ⟨hγ,hz⟩))
end
end qFOgTpd
end
section
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace qFOgTpd
noncomputable section
open Polynomial Finset
open P6 (p dw)
open P6_7_3
open cu (FX Jet A5)
open DP (U4 d3r Tl)
open pI (oU)
open XY (vf)
open akZ (aRJ ajz bLw)
open scoped Classical
open private a2f from ProximityPrize.SubmissionLower.Z
open private avoid_divisors from ProximityPrize.SubmissionLower.Zr07w3a
theorem anchor_caps {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :
    oU (anchorRow pick) anchor.free :=
  d3r P.crt x.word (pick.main ⟨0,by decide⟩).free_mem
private theorem anchor_mem {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :
    anchorRow pick∈P.rows anchor.free (cutoff anchor.free) := by
  have hm:=(pick.main ⟨0,by decide⟩).free_mem
  change anchorRow pick∈P.rows anchor.free (buffer x.h 0 anchor.free) at hm
  simpa only [buffer,Nat.mul_zero,Nat.sub_zero] using hm
theorem anchor_zero {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :
    ∀ γ∈x.Γ,Mark x (anchorRow pick) γ :=
  fun _ hγ=>necessary P (s :=anchor.free) (W:=cutoff anchor.free) (by decide) (anchor_mem pick) hγ
private theorem reference {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :
    Nonempty (Reference x P) := by
  by_contra h
  have hspan:P.rows anchor.free (cutoff anchor.free) ≤ ⊥ := Submodule.span_le.mpr (by
    rintro _ ⟨A,hA,rfl⟩
    exact (Submodule.mem_bot FX).mpr (by
      by_contra hz
      exact h ⟨⟨A,hA,hz⟩⟩))
  exact (pick.main ⟨0,by decide⟩).free_ne
    ((Submodule.mem_bot FX).mp (hspan (anchor_mem pick)))
private theorem intro_room (i:Intro) :2*hi*dI i<(shape i).m*dw:= by
  fin_cases i <;> decide
private theorem intro_small (i:Intro) : (shape i).U<p:= by
  fin_cases i <;> decide
private theorem intro_caps {x :Input} {P:Poles x} (pick :Picks x.h P.rows) (i:Intro) :
    oU (pick.intro i) (shape i) :=
  d3r P.crt x.word (pick.intro_mem i)
private theorem hasse_zero {x :Input} {P:Poles x} (pick :Picks x.h P.rows)
    (i:Intro) (v :Fin 2) (r :ℕ) (hr :r≤dI i) :
    ∀ γ∈x.Γ,Mark x (A5 v r (pick.intro i)) γ:= by
  have hm:=zBI (2*x.h) hr
  have ht:=(Nat.mul_le_mul_right (dI i)
    (zBI 2 (emz x).2)).trans_lt (intro_room i)
  have hW:buffer x.h (dI i) (shape i)+2*x.h*r<(shape i).m*dw:= by
    have hle :2*x.h*dI i≤ cutoff (shape i) := by unfold cutoff; omega
    calc
      _≤ cutoff (shape i) - 2*x.h*dI i+2*x.h*dI i:=Nat.add_le_add_left hm _
      _=cutoff (shape i) :=Nat.sub_add_cancel hle
      _<_:= by unfold cutoff; omega
  exact fun _ hγ=>necessary P hW
    (atp.d3s P.crt x.word (pick.intro_mem i) v r) hγ
private def admissible (x :Input) (s :cu.Shape) :Submodule FX Jet where
  carrier := {g | (∀ j i e,¬ (i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U) →
    a2f j i e g=0) ∧ ∀ γ∈x.Γ,vf (x.M.label γ) (x.F.scalar γ) g=0}
  zero_mem' := ⟨fun _ _ _ _=>map_zero _,fun _ _=>map_zero _⟩
  add_mem' := fun ha hb=>⟨fun j i e he=> by rw [map_add,ha.1 j i e he,hb.1 j i e he,add_zero],
    fun γ hγ=> by rw [map_add,ha.2 γ hγ,hb.2 γ hγ,add_zero]⟩
  smul_mem' := fun c g hg=>⟨fun j i e he=> by rw [map_smul,hg.1 j i e he,smul_zero],
    fun γ hγ=> by
      rw [Algebra.smul_def,map_mul,hg.2 γ hγ,mul_zero]⟩
private theorem admissible_iff {x :Input} {s :cu.Shape} {g:Jet} :
    g∈admissible x s↔oU g s ∧ ∀ γ∈x.Γ,Mark x g γ:= by
  change (_∧_)↔(_∧_)
  refine and_congr_left' ⟨?_,?_⟩
  · intro h j i hn
    have he (e) (hm:e∈((g.coeff j).coeff i).support) :
        i+j≤ s.B∧j≤ s.J∧Tl e≤ s.U :=
      not_not.mp fun hb=>(MvPolynomial.mem_support_iff.mp hm) (h j i e hb)
    obtain ⟨e,hm⟩:=MvPolynomial.support_nonempty.mpr hn
    refine ⟨(he e hm).1,(he e hm).2.1,?_⟩
    exact Finset.sup_le fun e hm=>(he e hm).2.2
  · intro h j i e he
    by_contra hn
    have hne : (g.coeff j).coeff i≠0:= by
      intro hz
      exact hn (by simp [a2f,hz])
    obtain ⟨hb,hj,hu⟩:=h j i hne
    exact he ⟨hb,hj,(MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hn)).trans hu⟩
private def passes {x :Input} {P:Poles x} (pick :Picks x.h P.rows)
    (R:Reference x P) (f :Jet) (i:Intro) :Prop :=
  (∀ v a,a≤dI i→f∣A5 v a (pick.intro i)) ∧
    (i.val=0→f∣U4 R.raw)
private def first {x :Input} {P:Poles x} (pick :Picks x.h P.rows)
    (R:Reference x P) (f :Jet) :IntroIndex :=
  let h : ∃ n,n=introductions.length ∨ ∃ i:Intro,i.val=n ∧ ¬ passes pick R f i :=
    ⟨introductions.length,Or.inl rfl⟩
  ⟨Nat.find h,Nat.lt_succ_of_le (Nat.find_min' h (Or.inl rfl))⟩
private theorem before_first {x :Input} {P:Poles x} {pick :Picks x.h P.rows}
    {R:Reference x P} {f :Jet} {i:Intro} (h:i.val<(first pick R f).val) :
    passes pick R f i:= by
  by_contra hn
  exact Nat.find_min _ h (Or.inr ⟨i,rfl,hn⟩)
private theorem first_missing {x :Input} {P:Poles x} {pick :Picks x.h P.rows}
    {R:Reference x P} {f :Jet} {i:Intro} (h:i.val=(first pick R f).val) :
    ¬ passes pick R f i:= by
  rcases Nat.find_spec (H :=(show ∃ n,n=introductions.length ∨
        ∃ j:Intro,j.val=n ∧ ¬ passes pick R f j from ⟨introductions.length,Or.inl rfl⟩)) with he | ⟨j,hj,hn⟩
  · exact ((h.trans he).not_lt i.isLt).elim
  · have hj' : j=i:=Fin.ext (hj.trans h.symm)
    exact hj' ▸ hn
structure Schedule (x :Input) {P:Poles x} (R:Reference x P) (D:zJe Jet) where
  origin :Jet→ IntroIndex
  cut:Intro→Jet
  nested : ∀ i≤ introductions.length,∀ j,
    (∑ f∈D.filter (fun f=>i≤(origin f).val),wD f j)≤ introCap i j
  last_dvd : ∀ f∈D,(origin f).val=introductions.length→f∣U4 R.raw
  proper : ∀ f∈D,∀ i,(origin f).val=i.val → ¬ f∣cut i
  caps : ∀ i,oU (cut i) (shape i)
  zero : ∀ i γ,γ∈x.Γ→Mark x (cut i) γ
theorem schedule {x :Input} {P:Poles x} (pick :Picks x.h P.rows) {D:zJe Jet}
    (hD:aRJ (anchorRow pick) D)
    (hcap : ∀ j,ajz D j≤bgK anchor.free j) :
    ∃ R:Reference x P,Nonempty (Schedule x R D) := by
  obtain ⟨R⟩:=reference pick
  let origin :=first pick R
  have refmem:U4 R.raw∈P.rows anchor.free (cutoff anchor.free) :=
    Submodule.subset_span ⟨R.raw,R.mem,rfl⟩
  have exists_cut (i:Intro) :
      ∃ g∈admissible x (shape i),∀ f∈D.filter (fun f=>(origin f).val=i.val),¬ f∣g:= by
    apply avoid_divisors
    intro f hf
    have hm:=first_missing (pick :=pick) (R:=R) (Finset.mem_filter.mp hf).2.symm
    by_cases hh : ∀ v a,a≤dI i→f∣A5 v a (pick.intro i)
    · have h:=not_imp.mp (fun h=>hm ⟨hh,h⟩)
      refine ⟨U4 R.raw,admissible_iff.mpr ⟨?_,fun _ hγ=>necessary P (s :=anchor.free) (W:=cutoff anchor.free) (by decide) refmem hγ⟩,h.2⟩
      have he :i=⟨0,by decide⟩:=Fin.ext h.1
      subst i
      intro j k hn
      obtain ⟨hb,hj,hu⟩:=d3r P.crt x.word refmem j k hn
      exact ⟨hb.trans (by decide),hj.trans (by decide),hu.trans (by decide)⟩
    · push Not at hh
      obtain ⟨v,a,ha,hn⟩:=hh
      exact ⟨_,admissible_iff.mpr ⟨czY.proof _ _ (intro_caps pick i) v a,
        hasse_zero pick i v a ha⟩,hn⟩
  choose cut hmem hproper using exists_cut
  refine ⟨R,⟨⟨origin,cut,?_,?_,?_,fun i=>(admissible_iff.mp (hmem i)).1,
    fun i=>(admissible_iff.mp (hmem i)).2⟩⟩⟩
  · suffices h : ∀ n≤ introductions.length,∀ T⊆D,
        (∀ f∈T,n≤(origin f).val) → ∀ j,ajz T j≤ introCap n j by
      exact fun n hn j=>h n hn _ (Finset.filter_subset _ _) (fun f hf=>(Finset.mem_filter.mp hf).2) j
    intro n
    induction n with
    | zero=>exact fun _ _ ht _ j=>(akZ.cN5 ht j).trans (hcap j)
    | succ n ih =>
      intro hn T hT hall j
      let i:Intro:=⟨n,Nat.lt_of_succ_le hn⟩
      have hc:=ih (Nat.le_of_succ_le hn) T hT (fun f hf=>(Nat.le_succ n).trans (hall f hf)) j
      have hr :=bLw (hD.mono hT) (pick.intro_ne i) (intro_caps pick i)
        (intro_small i) (dI i)
        (fun f hf=>(before_first (i:=i) (show n<_ from hall f hf)).1) j
      unfold introCap
      rw [List.take_succ_eq_append_getElem i.isLt,List.foldl_append]
      exact le_min hc hr
  · intro f _ hf
    have h:=before_first (pick :=pick) (R:=R) (f :=f) (i:=⟨0,by decide⟩)
      (by rw [show (first pick R f).val=introductions.length from hf]; decide)
    exact h.2 rfl
  · intro f hf i hi
    exact hproper i f (Finset.mem_filter.mpr ⟨hf,hi⟩)
end
end qFOgTpd
end
section
set_option autoImplicit true
namespace qY7abfd
noncomputable section
open P6 (K p blockLength)
open P6_7_3 (Input)
open qUrGXob (gap)
open cu (L)
open gT (kM bbt aSf)
open YY (U7)
structure DescendedMarks (x :Input) (T:zJe K) (J:Ideal kM)
    (Q:MvPolynomial (Fin 2) L) (e H :ℕ) :Prop where
  subset :T⊆x.Γ
  curve :bbt J e H
  irreducible :Irreducible Q
  projection :J.comap gT.pZ=Ideal.span {MvPolynomial.map U7 Q}
  plane_pos :0<Q.totalDegree
  seed_lt:Q.totalDegree*e<p
  marks : ∀ γ∈T,aSf J (x.M.label γ) (x.F.scalar γ)
abbrev linearRate :ℚ:=1+3*(blockLength:ℚ)/gap
abbrev quadraticRate :ℚ:=13+8*(blockLength:ℚ)/gap
abbrev nativeSlope (d:ℚ) (e :ℕ) :ℚ:=d/(3*(e :ℚ))+4*e+8
end
end qY7abfd
end
section
set_option autoImplicit true
namespace qvdiC8c
noncomputable section
open Polynomial Finset q3u9Tnc
open qe6nVeb (Raw phys)
open P5_7_7 (mL)
open P5 (K)
open P5_7_2 (A)
open cu (FX Equation vm kr yq qD)
open Qt (gY Qc acG)
open Y3 (embed)
open qVXVW4b (constant_height)
open scoped Classical
open private changeOrd changed_primitive change_caps change_eval from ProximityPrize.SubmissionLower.Za7Od9d
abbrev height (f :Raw) :=gY (embed f)
def value {J U} (B:DualWord J U) (γ:K) :FX:=phys (B.P γ)/phys (B.Q γ)
def rootHom {J U} (B:DualWord J U) (γ:K) :Raw →+* FX :=
  (eval₂RingHom (qD (J.model.label γ)) (value B γ)).comp embed
private theorem chart_det {J U} (B:DualWord J U) :
    phys B.a₀*phys B.b₁ - phys B.a₁*phys B.b₀≠0:= by
  obtain ⟨c,hc,h⟩:=B.determinant
  have hn:mL (univ :zJe P5.I)≠0 :=
    prod_ne_zero_iff.mpr fun i _=>X_sub_C_ne_zero _
  rw [← map_mul,← map_mul,← map_sub,h]
  exact (map_ne_zero_iff _ (zxb _ _)).mpr (mul_ne_zero (C_ne_zero.mpr hc) hn)
private theorem chart_identity {J U} (B:DualWord J U) {γ:K} (hγ:γ∈U) :
    phys B.b₀*value B γ - phys B.b₁ =
      (phys B.a₁ - phys B.a₀*value B γ)*kr (J.family.scalar γ) := by
  let P:=phys (B.P γ)
  let Q:=phys (B.Q γ)
  let loc:=phys (mL (sites J γ))
  have hp:loc*P=phys B.a₁*kr (J.family.scalar γ)+phys B.b₁:= by
    simpa only [P,loc,kr,map_mul,map_add] using congrArg phys (B.numerator_id γ hγ)
  have hq:loc*Q=phys B.a₀*kr (J.family.scalar γ)+phys B.b₀:= by
    simpa only [Q,loc,kr,map_mul,map_add] using congrArg phys (B.denominator_id γ hγ)
  have hn:Q≠0:=(map_ne_zero_iff _ (zxb _ _)).mpr (B.denominator γ hγ)
  have h: (phys B.a₀*kr (J.family.scalar γ)+phys B.b₀) *
      value B γ=phys B.a₁*kr (J.family.scalar γ)+phys B.b₁:= by
    change _ *(P/Q)= _
    rw [← hq,← hp,mul_assoc,← mul_div_assoc,mul_div_cancel_left₀ _ hn]
  linear_combination h
private theorem chart_inj {J U} (B:DualWord J U) (hU:U⊆J.CF) :
    Set.InjOn (value B) (U:Set K) := by
  intro γ hγ δ hδ he
  have h₁:=chart_identity B hγ
  have h₂:=chart_identity B hδ
  rw [← he] at h₂
  have hn:phys B.a₁ - phys B.a₀*value B γ≠0:= by
    intro hz
    apply chart_det B
    have hA:=sub_eq_zero.mp hz
    rw [hz,zero_mul] at h₁
    rw [hA,← sub_eq_zero.mp h₁]
    ring
  exact J.family.distinct (hU hγ) (hU hδ)
    (P5_7_7.atX_injective (mul_left_cancel₀ hn (h₁.symm.trans h₂)))
theorem transported {J U} (B:DualWord J U) {f :Equation} {e u:ℕ}
    (hp:f.IsPrimitive) (he :f.natDegree≤e) (hs :vm f u)
    (hr : ∀ γ∈U,yq f (J.model.label γ) (J.family.scalar γ)=0) :
    ∃ r :Raw,(embed r).IsPrimitive∧r.natDegree≤e∧height r≤u ∧
      ∀ γ∈U,atDual B r γ=0:= by
  let a :=phys B.b₀
  let b := -phys B.b₁
  let c := -phys B.a₀
  let d:=phys B.a₁
  have hm:a*d-b*c≠0:= by
    have h:=chart_det B
    rwa [show a*d-b*c = -(phys B.a₀*phys B.b₁ -
        phys B.a₁*phys B.b₀) by dsimp [a,b,c,d]; ring,neg_ne_zero]
  let g:=changeOrd a b c d f e
  have hg:g.IsPrimitive :=changed_primitive hm hp he
  obtain ⟨hd,hcap⟩:=change_caps a b c d (n:=e) hs
  obtain ⟨r,a',ha,hrepr,hdeg,_,_⟩:=Y3.normalize g e u hg.ne_zero hd hcap
  have hu:=ha.isUnit.map Y3.constant
  refine ⟨r,?_,hdeg,?_,?_⟩
  · intro b' hb
    rw [hrepr] at hb
    exact hg b' (hu.dvd_mul_left.mp hb)
  · change gY (embed r)≤u
    rw [hrepr,acG hu.ne_zero hg.ne_zero,constant_height,zero_add]
    exact (Qc g u).mpr hcap
  · intro γ hγ
    change (embed r).eval₂ _ (value B γ)=0
    rw [hrepr,eval₂_mul]
    apply mul_eq_zero.mpr
    right
    change (changeOrd a b c d f e).eval₂ _ _=0
    rw [change_eval a b c d he _ _ (kr (J.family.scalar γ)) ?_]
    · change yq f (J.model.label γ) (J.family.scalar γ)*_=0
      rw [hr γ hγ,zero_mul]
    · have h:=chart_identity B hγ
      dsimp [a,b,c,d]
      linear_combination h
theorem section_caps {J U} (B:DualWord J U) (hU:U⊆J.CF)
    {γ:K} (hγ:γ∈U) :
    (B.P γ).natDegree≤B.u₁∧(B.Q γ).natDegree≤B.u₀:= by
  let m:=J.family.mark γ (hU hγ)
  have hA:A≤(sites J γ).card :=
    m.bad.dw.trans (card_le_card fun i hi=>mem_filter.mpr ⟨mem_univ i,m.scalar_hits i hi⟩)
  obtain ⟨_,hq,hp⟩:=B.degrees γ hγ
  exact ⟨by omega,by omega⟩
theorem ecU {J U} (B:DualWord J U) (hU:U⊆J.CF)
    {T:zJe K} (hT:T⊆U)
    {F:Raw} (hF:F≠0) (hh:height F=0) (hr : ∀ γ∈T,atDual B F γ=0) :
    T.card≤F.natDegree := by
  let f :=embed F
  let q:=f.map zuE
  have hc (j:ℕ) :f.coeff j=MvPolynomial.C (zuE (f.coeff j)) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero ((Qc f 0).mp hh.le j))
  have he (z :K) :f.map (qD z)=q:= by
    ext j
    simp only [q,coeff_map]
    exact (congrArg (qD z) (hc j)).trans (MvPolynomial.eval_C _)
  have hq:q≠0:= fun hz=> by
    apply hF
    apply Y3.embed_injective
    change f=embed 0
    rw [map_zero]
    apply Polynomial.ext
    intro j
    have h:=congrArg (fun p:FX[X]=>p.coeff j) hz
    simp only [q,coeff_map,coeff_zero] at h
    rw [hc j,h,map_zero,coeff_zero]
  refine (P5_7_7.countRoots T _ ((chart_inj B hU).mono hT) q hq ?_).trans
    (natDegree_map_le.trans natDegree_map_le)
  intro γ hγ
  rw [← he (J.model.label γ),eval_map]
  exact hr γ hγ
end
end qvdiC8c
end
section
set_option autoImplicit true
namespace qvdiC8c
noncomputable section
open Polynomial Finset q3u9Tnc
open qe6nVeb (Raw Witness width filterOK switch highRate zWidth quotient modulus rank columns rows firstDigit)
open P5 (K p)
open cu (L)
open Qt (Qc)
open Y3 (embed)
open q4Pefpa (UR sk stock j3 inputSize load dhP)
open scoped Classical
open private rescale coeffMap_inj embed_degree embed_rect height_rect from ProximityPrize.SubmissionLower.ZagvXJe
private theorem rank_eq (D e j:ℕ) (x :Witness) :
    rank D e j x=j3 (width D) (e+x.g)+j3 (width D) j:= by
  unfold rank j3
  rw [Nat.mul_add,Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right (Nat.two_dvd_mul_add_one j) _)]
  simp only [Nat.mul_assoc]
private theorem proper_resultant {F G:Raw} (hi:Irreducible F) (hp:0<F.natDegree)
    (h : ¬ F∣G) : (embed F).resultant (embed G)≠0:= by
  let _:StrongNormalizationMonoid UR:=UniqueFactorizationMonoid.strongNormalizationMonoid
  let _:NormalizedGCDMonoid UR:=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let ψ:UR →+* FractionRing UR:=algebraMap _ _
  have hprim:=hi.isPrimitive hp.ne'
  have hi' := (hprim.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing UR)).mp hi
  have hc:IsCoprime (F.map ψ) (G.map ψ) :=
    hi'.coprime_iff_not_dvd.mpr fun hd=>h (hprim.dvd_of_fraction_map_dvd_fraction_map hd)
  have hn:=resultant_ne_zero _ _ hc
  rw [natDegree_map_eq_of_injective (zxb UR (FractionRing UR)),
    natDegree_map_eq_of_injective (zxb UR (FractionRing UR)),
    resultant_map_map] at hn
  change (F.map _).resultant (G.map _)≠0
  rw [natDegree_map_eq_of_injective coeffMap_inj,natDegree_map_eq_of_injective coeffMap_inj,
    resultant_map_map]
  intro hz
  exact hn (by rw [coeffMap_inj (hz.trans (map_zero _).symm),map_zero])
set_option maxRecDepth 1600 in
theorem high_count (h1 :q4Pefpa.c1) (h2 :q4Pefpa.c2)
    {J U} (B:DualWord J U) (hU:U⊆J.CF) {T:zJe K} (hT:T⊆U)
    {e u:ℕ} {x :Witness} (hx :filterOK J.D e u x)
    {F:Raw} (hi:Irreducible F) (hpos :0<F.natDegree) (hd:F.natDegree≤e)
    (hv :height F≤u) (hhigh : ¬ below B F (switch J.D e u x))
    (hroot : ∀ γ∈T,atDual B F γ=0) :
    T.card≤height F*highRate e u x := by
  let z :=zWidth e u x
  let v :=height F
  let W:=switch J.D e u x
  let j:=quotient e u x
  let M:=modulus J.D e u x
  let E :=e+x.g
  obtain ⟨_,_,_,hj,hM,hs,hp⟩:=hx
  have hl:=B.gMz
  have hsz (c n:ℕ) :c*n+n=(c+1)*n:= by ring
  have hsurplus :stock ((z+1)*v) ((x.c+1)*v)*(j3 (width J.D) E+j3 (width J.D) j) <
      inputSize x.g M (z*v) (x.c*v) := by
    apply rescale hv
    rw [← rank_eq]
    have hcols :columns e u x=stock ((z+1)*u) ((x.c+1)*u) := by
      change (z*u+u+1)*(x.c*u+u+1)= _
      rw [hsz,hsz]
      rfl
    have hrows :rows e u x*M=inputSize x.g M (z*u) (x.c*u) := by
      simp only [rows,inputSize,stock,z,mul_assoc]
    exact (hcols ▸ hs).trans_eq hrows
  obtain ⟨d,hdM,V,hV,hrow⟩:=h1 B.u₀ B.u₁ e x.g M (z*v) (x.c*v) v B.order
    (hl.symm ▸ hM) F hi.ne_zero hd (height_rect F)
  have hlarge :stock (z*v+v) (x.c*v+v)*j3 (B.u₀+B.u₁) j<Module.finrank L V:= by
    rw [hsz,hsz,hl] at hV ⊢
    dsimp only [E] at hsurplus
    rw [Nat.mul_add] at hsurplus
    omega
  have hload :W<load B.u₀ B.u₁ F:= by
    apply Nat.lt_of_not_ge
    intro h
    apply hhigh
    intro i m hm
    have hi' : i∈F.support :=mem_support_iff.mpr fun he=> by
      exact hm (by simp [he])
    exact ((Finset.le_sup (f := fun m =>
      ((F.coeff i).coeff m).natDegree+F.natDegree*B.u₀+i*(B.u₁-B.u₀))
      (MvPolynomial.mem_support_iff.mpr hm)).trans
      (Finset.le_sup (f := fun i=>(F.coeff i).support.sup fun m =>
        ((F.coeff i).coeff m).natDegree+F.natDegree*B.u₀+i*(B.u₁-B.u₀)) hi')).trans h
  have hm:M=W+1+j*(B.u₀+B.u₁) := by rw [hl]; rfl
  obtain ⟨G,hGV,hescape⟩ : ∃ G∈V,¬ F∣G:= by
    by_contra! ha
    exact hlarge.not_ge (h2 B.u₀ B.u₁ e x.g j W (z*v+v) (x.c*v+v)
      B.order hj F hi.ne_zero hd hload V (fun G hG=> by
        rw [← hm]
        exact ⟨(hrow G hG).1,(hrow G hG).2.1⟩) ha)
  obtain ⟨hpad,hrect,H,Q,hQ,hcong⟩:=hrow G hGV
  have hroots (γ:K) (hγ:γ∈T) :atDual B G γ=0:= by
    have hmU:=hT hγ
    obtain ⟨hn,hd'⟩:=section_caps B hU hmU
    apply dhP B.order hdM (B.denominator γ hmU) hn hd' hpad hQ hcong
    rw [map_mul,eval₂_mul]
    exact mul_eq_zero.mpr (Or.inl (hroot γ hγ))
  have hg (i:ℕ) (k :Fin 2) : ((embed G).coeff i).degreeOf k ≤
      (if k=0 then z+1 else x.c+1)*v := by
    change ((qQ9yWTb.embed G).coeff i).degreeOf k≤_
    rw [embed_rect]
    by_cases hk :k=0 <;> simpa only [sk,hk,ite_true,ite_false,hsz] using hrect k i
  have hp' : (e*(z+1)+E)*v<p:= calc
    _≤(e*(z+1)+E)*u:=zBI _ hv
    _=u*firstDigit e x (zWidth e u x) := by dsimp only [firstDigit,E,z]; ring
    _<p:=hp
  have hc:=qQ9yWTb.count_resultant ((embed_degree F).symm ▸ hpos)
    ((embed_degree F).symm ▸ hd) ((embed_degree G).symm ▸ hpad.1)
    ((Qc (embed F) v).mp le_rfl) hg (proper_resultant hi hpos hescape) hp'
    (z :=J.model.label) (y :=value B)
    (fun _ _ _ _ h=>sub_left_inj.mp h) hroot hroots
  exact hc.trans_eq (by dsimp only [highRate,firstDigit,E,v,z]; ring)
end
end qvdiC8c
end
section
set_option autoImplicit true
namespace qvdiC8c
noncomputable section
open Polynomial Finset q3u9Tnc
open qe6nVeb (Raw Witness filterOK switch highRate)
open P5 (K)
open Y3 (embed)
open scoped Classical
open private degree_pos height_mul from ProximityPrize.SubmissionLower.ZGCzLxb
private structure Allocation {J U} (B:DualWord J U) (T:zJe K) (d h W r :ℕ) where
  Bp:zJe K
  sub:Bp⊆T
  wD:ℕ
  budget:wD ≤h
  card:T.card≤Bp.card+wD*r+d
  sheets :LowSheets B Bp d (h-wD) W
private def emptySheets {J U} (B:DualWord J U) (d h W:ℕ) :LowSheets B ∅ d h W :=
  ⟨0,Fin.elim0,fun i=>i.elim0,fun i=>i.elim0,fun i=>i.elim0,fun i=>i.elim0,
    by simp,by simp,by simp⟩
private theorem cases_prop {α:Type*} {n m:ℕ} (f :Fin n→α) (g:Fin m→α)
    {P:α→Prop} (hf : ∀ i,P (f i)) (hg : ∀ i,P (g i)) (i:Fin (n+m)) :
    P (i.addCases f g) :=
  (Fin.forall_fin_add (fun j=>P (j.addCases f g))).mpr
    ⟨fun j=> by simpa only [Fin.addCases_left] using hf j,
      fun j=> by simpa only [Fin.addCases_right] using hg j⟩ i
private theorem cases_sum {α:Type*} {n m:ℕ} (f :Fin n→α) (g:Fin m→α) (w:α→ℕ) :
    (∑ i:Fin (n+m),w (i.addCases f g))=(∑ i,w (f i)) + ∑ i,w (g i) := by
  rw [Fin.sum_univ_add]
  simp only [zgb,z5m]
set_option maxHeartbeats 600000 in
private def appendSheets {J U} {B:DualWord J U} {T₁ T₂:zJe K}
    {d₁ d₂ h₁ h₂ W:ℕ} (a :LowSheets B T₁ d₁ h₁ W) (b:LowSheets B T₂ d₂ h₂ W) :
    LowSheets B (T₁∪T₂) (d₁+d₂) (h₁+h₂) W:= by
  refine ⟨a.size+b.size,Fin.addCases a.sheet b.sheet,?_,?_,?_,?_,?_,?_,?_⟩
  · exact cases_prop a.sheet b.sheet (P:=Irreducible) a.irreducible b.irreducible
  · exact cases_prop a.sheet b.sheet (P:= fun F=>0<F.natDegree) a.positive b.positive
  · exact cases_prop a.sheet b.sheet (P:= fun F=>0<height F) a.moving b.moving
  · exact cases_prop a.sheet b.sheet (P:= fun F=>below B F W) a.weight b.weight
  · exact (cases_sum a.sheet b.sheet (fun F:Raw=>F.natDegree)).le.trans
      (z9f a.ordinate_sum b.ordinate_sum)
  · exact (cases_sum a.sheet b.sheet (fun F:Raw=>height F)).le.trans
      (z9f a.seed_sum b.seed_sum)
  · intro γ hγ
    rcases mem_union.mp hγ with h | h
    · obtain ⟨i,hi⟩:=a.roots γ h
      exact ⟨i.castAdd _,by simpa only [zgb] using hi⟩
    · obtain ⟨i,hi⟩:=b.roots γ h
      exact ⟨i.natAdd _,by simpa only [z5m] using hi⟩
private def Allocation.merge {J U} {B:DualWord J U} {T₁ T₂:zJe K}
    {d₁ d₂ h₁ h₂ W r :ℕ} (a :Allocation B T₁ d₁ h₁ W r)
    (b:Allocation B T₂ d₂ h₂ W r) (hd:Disjoint T₁ T₂) :
    Allocation B (T₁∪T₂) (d₁+d₂) (h₁+h₂) W r := by
  refine ⟨a.Bp∪b.Bp,union_subset_union a.sub b.sub,a.wD+b.wD,
    z9f a.budget b.budget,?_,?_⟩
  · rw [card_union_of_disjoint hd,card_union_of_disjoint (hd.mono a.sub b.sub),Nat.add_mul]
    have ha :=a.card
    have hb:=b.card
    omega
  · have ha :=a.budget
    have hb:=b.budget
    have he :h₁-a.wD+(h₂-b.wD)=h₁+h₂-(a.wD+b.wD) := by omega
    exact he ▸ appendSheets a.sheets b.sheets
private theorem single
    {J U} (B:DualWord J U) (hU:U⊆J.CF) {e u:ℕ} {x :Witness}
    (hx :filterOK J.D e u x)
    {F:Raw} (hi:Irreducible F) (hp: (embed F).IsPrimitive)
    (hd:F.natDegree≤e) (hv :height F≤u)
    {T:zJe K} (hT:T⊆U) (hr : ∀ γ∈T,atDual B F γ=0) :
    Nonempty (Allocation B T F.natDegree (height F) (switch J.D e u x) (highRate e u x)) := by
  by_cases hz :height F=0
  · refine ⟨⟨∅,empty_subset _,0,Nat.zero_le _,?_,emptySheets B _ _ _⟩⟩
    simpa using ecU B hU hT hi.ne_zero hz hr
  have hm:=Nat.pos_of_ne_zero hz
  have hpos :0<F.natDegree :=degree_pos hp (dvd_refl _) hm
  by_cases hw:below B F (switch J.D e u x)
  · refine ⟨⟨T,Subset.rfl,0,Nat.zero_le _,by simp,?_⟩⟩
    exact ⟨1,fun _=>F,fun _=>hi,fun _=>hpos,fun _=>hm,fun _=>hw,
      by simp,by simp,fun γ hγ=>⟨0,hr γ hγ⟩⟩
  exact ⟨⟨∅,empty_subset _,height F,le_rfl,
    (high_count qHDgEWd.proof qwDXpPd.proof B hU hT hx hi hpos hd hv hw hr).trans (by simp),
    emptySheets B _ _ _⟩⟩
private theorem allocate
    {J U} (B:DualWord J U) (hU:U⊆J.CF) {e u:ℕ} {x :Witness}
    (hx :filterOK J.D e u x)
    (F:Raw) (hp: (embed F).IsPrimitive) (hd:F.natDegree≤e) (hv :height F≤u)
    (T:zJe K) (hT:T⊆U) (hr : ∀ γ∈T,atDual B F γ=0) :
    Nonempty (Allocation B T F.natDegree (height F) (switch J.D e u x) (highRate e u x)) := by
  revert hp hd hv T hT hr
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro hp
    exact (hp.ne_zero (map_zero _)).elim
  | unit F hF =>
    intro _ _ _ T _ hr
    have he :T = ∅ := eq_empty_iff_forall_notMem.mpr
      fun γ hγ=>(hF.map (rootHom B γ)).ne_zero (hr γ hγ)
    subst T
    exact ⟨⟨∅,Subset.rfl,0,Nat.zero_le _,by simp,emptySheets B _ _ _⟩⟩
  | mul a i ha hi ih =>
    intro hp hd hv T hT hr
    have hp₁:=isPrimitive_of_dvd hp (map_dvd embed (dvd_mul_right i a))
    have hp₂:=isPrimitive_of_dvd hp (map_dvd embed (dvd_mul_left a i))
    have hdeg:=natDegree_mul hi.ne_zero ha
    rw [hdeg] at hd ⊢
    have hheight:height (i*a)=height i+height a :=height_mul hi.ne_zero ha
    rw [hheight] at hv ⊢
    let T₁:=T.filter fun γ=>atDual B i γ=0
    let T₂:=T \ T₁
    have h₁:T₁⊆T:=filter_subset _ _
    have h₂:T₂⊆T:=sdiff_subset
    obtain ⟨s⟩:=single B hU hx hi hp₁ (by omega) (by omega) (h₁.trans hT)
      (fun γ hγ=>(mem_filter.mp hγ).2)
    have hr₂ (γ:K) (hγ:γ∈T₂) :atDual B a γ=0:= by
      have h:rootHom B γ (i*a)=0:=hr γ (h₂ hγ)
      rw [map_mul] at h
      exact (mul_eq_zero.mp h).resolve_left fun he =>
        (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨h₂ hγ,he⟩)
    obtain ⟨t⟩:=ih hp₂ (by omega) (by omega) T₂ (h₂.trans hT) hr₂
    have hu:T₁∪T₂=T:=union_sdiff_of_subset h₁
    exact ⟨hu ▸ s.merge t disjoint_sdiff_self_right⟩
theorem proof :q3u9Tnc.c1 := by
  intro J U hU B e u x _ hx f hf he hs hr
  obtain ⟨F,hprim,hdeg,hh,hF⟩:=transported B hf.2.1 he.le hs hr
  obtain ⟨a⟩:=allocate B hU hx F hprim hdeg hh U Subset.rfl hF
  refine ⟨a.Bp,a.sub,a.wD,a.budget.trans hh,?_,⟨?_⟩⟩
  · have h:=card_sdiff_add_card_eq_card a.sub
    have hc:=a.card
    omega
  · exact { a.sheets with
      ordinate_sum:=a.sheets.ordinate_sum.trans hdeg
      seed_sum:=a.sheets.seed_sum.trans (Nat.sub_le_sub_right hh _) }
end
end qvdiC8c
end
