import ProximityPrize.SubmissionLower.Zyuvo1c
import ProximityPrize.SubmissionLower.ZEGTqPa
import ProximityPrize.SubmissionLower.ZPkJuGd
import ProximityPrize.SubmissionLower.ZZhU1ja
set_option Elab.async false
open _root_ renaming Finset → zJe, Ideal.isCoprime_iff_sup_eq → zDt, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, IsDomain → ztn, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, Nat.add_le_add → z9f, Nat.mul_le_mul_left → zBI, RingHom.ker → zdq
section
set_option autoImplicit true
namespace qTplN5b
open P6_7_1 (degree)
abbrev polarDegree (e W:ℕ) :ℕ:=(2*e-1)*W-e*e*degree
abbrev poleFee (e W:ℕ) :ℕ:=(6*e-2)*W-3*e*e*degree
end qTplN5b
end
section
set_option autoImplicit true
namespace qRNngId
noncomputable section
open q3rjQGe (AxisSection)
open gT (Ambient aQ)
abbrev axisLength (q:Ideal Ambient) (i:Fin 2) :=
  zsE aQ (AxisSection q i)
end
end qRNngId
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qgscZIa
noncomputable section
open Finset
open P6 (p dw)
open P6_7_1
open q3rjQGe
open cu (FX Jet jz)
open gT (Ambient gk aQ aci iJ aNB)
open pI (xN oU dual pN weight dot)
open ac3
open OH (Q6 N8 PrincipalCut aHf bfe)
open TD (FP)
open private cpa from ProximityPrize.SubmissionLower.U
open private ea0 from ProximityPrize.SubmissionLower.U
open private gwL from ProximityPrize.SubmissionLower.U
open scoped Classical BigOperators Function
def c1 :Prop :=
  ∀ (q:Ideal Ambient) (a :Fin 2),xN q →
    (axisIdeal q a).IsPrime ∧
    ringKrullDim (AxisSection q a)=1 ∧
    (∀ [ztn (AxisSection q a)],
      aHf aQ (AxisSection q a) (axisCoord q a (freeAxis a)) =
        pN q 0)
def c2 :Prop :=
  ∀ (q:Ideal Ambient) (a :Fin 2) [ztn (AxisSection q a)],
    xN q→q.height=2→dual q →
    aHf aQ (AxisSection q a) (axisCoord q a 2)≤pN q 1 ∧
    bfe aQ (AxisSection q a) (axisCoord q a 2) (axisCoord q a 3)≤pN q 2
private theorem axis_length (h1 :c1) (h2 :c2)
    {x :Input} {P:Poles x} {q:Ideal Ambient} {g:Jet}
    (ha :xN q) (hh:q.height=2) (hd:dual q)
    (hg:g∈rectBank P terminal (rectCut terminal)) (hp:iJ g∉q) (a :Fin 2) :
    (∑ Q∈aOS q g,zsE aQ (AxisSection Q a)) ≤
      terminal.z*pN q 0+(terminal.B-terminal.J)*pN q 1 +
        terminal.J*pN q 2 := by
  obtain ⟨hprime,hdim,hfree⟩:=h1 q a ha
  have hdomain:ztn (gk (axisIdeal q a)) :=
    @Ideal.Quotient.isDomain _ _ (axisIdeal q a) inferInstance hprime
  have :ztn (AxisSection q a) :=hdomain
  have hf :axisRestrict q a (iJ g)≠0:= by
    intro hz
    apply hp
    have :q.IsPrime :=ha.prime
    rcases axis_localization q a with ht | ⟨_,hcomap⟩
    · exact (hprime.ne_top ht).elim
    · rw [← hcomap]
      change Q6 (iJ g)∈axisIdeal q a
      exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  let A:=AxisSection q a
  let f :=axisRestrict q a (iJ g)
  let D:=axisIdeal q a ⊔ zye {Q6 (iJ g)}
  let e : (A ⧸ zye {f}) ≃ₐ[aQ] (N8 ⧸ D) := by
    have he : (zye {Q6 (iJ g)}).map
        (Ideal.Quotient.mkₐ aQ (axisIdeal q a))=zye {f} := by
      rw [Ideal.map_span,Set.image_singleton]
      rfl
    rw [← he]
    exact DoubleQuot.quotQuotEquivQuotSupₐ aQ (axisIdeal q a) _
  have :zAa aQ (PrincipalCut f) :=
    ea0 aQ A hdim hf
  have :zAa aQ (N8 ⧸ D) :=
    zIU e.toLinearEquiv.toLinearMap e.surjective
  let S:=aOS q g
  let J (Q:S) :=axisIdeal Q.val a
  have hmin (Q:S) :Q.val∈(q ⊔ zye {iJ g}).minimalPrimes :=
    Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp Q.property).1
  have hle (Q:S) :D ≤J Q:= by
    have h:=(hmin Q).le
    refine sup_le (sup_le_sup (Ideal.map_mono (le_sup_left.trans h)) le_rfl) ?_
    apply (zvl _).mpr
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  have hmax (Q:S) :J Q = ⊤ ∨ ((J Q).IsMaximal∧(J Q).comap Q6= Q.val) := by
    have :Q.val.IsPrime :=(hmin Q).isPrime
    rcases axis_localization Q.val a with ht | ⟨hP,hc⟩
    · exact Or.inl ht
    · have : (J Q).IsPrime :=hP
      have :zAa aQ (N8 ⧸ J Q) :=
        zIU (Ideal.Quotient.factorₐ aQ (hle Q)).toLinearMap
          (Ideal.Quotient.factor_surjective (hle Q))
      exact Or.inr ⟨Ideal.Quotient.maximal_of_isField (J Q)
        (IsField.of_isDomain_of_finite aQ (N8 ⧸ J Q)),hc⟩
  have hpair :Pairwise (IsCoprime on J) := by
    intro Q R hQR
    rcases hmax Q with htop | ⟨hQ,hQc⟩
    · simp [zDt,htop]
    rcases hmax R with htop | ⟨hR,hRc⟩
    · simp [zDt,htop]
    have :=hQ
    have :=hR
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hQR
    apply Subtype.ext
    rw [← hQc,← hRc,he]
  have hsum:=gwL (k :=aQ) D J hle hpair
  have hlen:zsE aQ (N8 ⧸ D)≤aHf aQ A f :=
    e.toLinearEquiv.finrank_eq.symm.le.trans (cy9.proof aQ A hdim f hf)
  have hfree' : aHf aQ A (axisCoord q a (freeAxis a))=pN q 0 :=
    hfree
  obtain ⟨hy,hj⟩:=h2 q a ha hh hd
  have :CharP aQ p:=charP_of_injective_ringHom
    ((algebraMap FX aQ).comp jz).injective p
  obtain ⟨V⟩:=bzU.proof p aQ A hdim
    (axisCoord q a (freeAxis a)) (axisCoord q a 2) (axisCoord q a 3)
    (by rw [hfree']; exact ha.seed_size.1) (by rw [hfree']; exact ha.seed_size.2)
  have hwidth : (if a=0 then terminal.z else terminal.t)=terminal.z := by
    split <;> rfl
  have hdeg:aHf aQ A f ≤
      terminal.z*aHf aQ A (axisCoord q a (freeAxis a)) +
      (terminal.B-terminal.J)*aHf aQ A (axisCoord q a 2) +
      terminal.J*bfe aQ A (axisCoord q a 2) (axisCoord q a 3) := by
    rw [V.degree_eq f,V.degree_eq (axisCoord q a (freeAxis a)),V.degree_eq (axisCoord q a 2),
      V.line_eq]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hrow:=row_axis_poles hg (by decide :terminal.J≤terminal.B)
      (DP.d3r P.crt x.word (rectBank_le P _ _ hg)) q a (V.place i)
    rw [hwidth] at hrow
    simpa only [Nat.add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (V.QZ i) hrow
  rw [← sum_attach S]
  exact hsum.trans (hlen.trans (hdeg.trans (by
    rw [hfree']
    exact z9f (z9f le_rfl (zBI _ hy))
      (zBI _ hj))))
theorem of_children (h1 :c1) (h2 :c2) :q3rjQGe.c5:= by
  intro x P q ha hh hd g hg hp
  have hs :terminal.J≤terminal.B:= by decide
  have hg' := rectBank_le P terminal (rectCut terminal) hg
  have hc:oU g terminal.box :=DP.d3r P.crt x.word hg'
  let direct :=(a2T q g).biUnion (marks x)
  have hgeom (Q) (hQ:Q∈aOS q g) :=
    bZk ha hp (mem_filter.mp hQ).1
  let C:RectCover := {
    direct :=direct
    qv :=aOS q g
    geometric:= fun Q hQ=>⟨(hgeom Q hQ).1,(hgeom Q hQ).2,
      cy6.proof Q (hgeom Q hQ).1 (hgeom Q hQ).2 (mem_filter.mp hQ).2⟩
    finite_axis := fun Q hQ a=> by
      have :Q.IsPrime :=(hgeom Q hQ).1
      exact axis_finite Q (hgeom Q hQ).2 a }
  have hcard:direct.card≤(a2T q g).card:= by
    have hs (Q) (hQ:Q∈a2T q g) : (marks x Q).card≤1 := by
      obtain ⟨hQ,hconst⟩:=mem_filter.mp hQ
      have :Q.IsPrime :=(bZk ha hp hQ).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply jz.injective
      apply (algebraMap FX (gk Q)).injective
      exact (cpa hconst (mem_filter.mp hγ).2).trans
        (cpa hconst (mem_filter.mp hδ).2).symm
    exact card_biUnion_le.trans ((sum_le_sum hs).trans_eq (by simp))
  refine ⟨C,fun a => ?_,fun j => ?_,?_⟩
  · have h:=axis_length h1 h2 ha hh hd hg hp a
    have ha1 : (0:Fin 3).succ=(1 :Fin 4) :=rfl
    have ha2 : (0:Fin 2).succ.succ=(2 :Fin 4) :=rfl
    simpa only [C,RectCover.kd,FP,axisWeight,Fin.sum_univ_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.sum_univ_zero,zero_mul,add_zero,ha1,ha2,
      Nat.cast_add,Nat.cast_mul,Nat.cast_zero,add_assoc] using
        (Nat.cast_le (α:=ℚ)).mpr h
  · have h:C.toacW.cost j≤dot (weight terminal.box j) (pN q) := by
      fin_cases j
      · exact ac6.Bridge.dS4 terminal.box q g hs ha hc hp
      · exact ac6.Bridge.dSZ terminal.box q g hs ha hc hp
      · exact hcard.trans (ac6.Bridge.dSJ terminal.box q g hs ha hc hp)
    simpa only [SS,terminal_shape,FP,dot,Nat.cast_sum,Nat.cast_mul] using
      (Nat.cast_le (α:=ℚ)).mpr h
  · intro γ hγ
    obtain ⟨hγ,hmark⟩:=mem_filter.mp hγ
    have hw:rectCut terminal<terminal.box.m*dw:= by decide
    let e :=aci (x.M.label γ) (x.F.scalar γ)
    change q≤zdq e at hmark
    have hz :iJ g∈zdq e :=RingHom.mem_ker.mpr
      ((aNB _ _ _).trans (necessary P hw hg' hγ))
    have hle :q ⊔ zye {iJ g} ≤ zdq e :=
      sup_le hmark ((zvl _).mpr hz)
    have : (zdq e).IsPrime :=RingHom.ker_isPrime e
    obtain ⟨Q,hmin,hQmark⟩:=Ideal.exists_minimalPrimes_le hle
    have hQ:Q∈aT1 q g:=Ideal.mem_minimalPrimesFinset.mpr hmin
    by_cases ht:aYy Q
    · exact mem_union_left _ (mem_biUnion.mpr
        ⟨Q,mem_filter.mpr ⟨hQ,ht⟩,mem_filter.mpr ⟨hγ,hQmark⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,Q,mem_filter.mpr ⟨hQ,ht⟩,hQmark⟩)
end
end qgscZIa
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
namespace qWiDZjb
open qigFtUb
private theorem r0:Prefix .pruned 67 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r1 :Prefix .pruned 71 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r2 :Prefix .pruned 75 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r3:Prefix .pruned 79 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
theorem Wp:Prefix .pruned 67 16 :=
  prefix_add (prefix_add (prefix_add r0 r1) r2) r3
end qWiDZjb
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
namespace qAOSsCb
open qigFtUb
theorem batchE :Prefix .tailThree 60 15:= by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
end qAOSsCb
end
section
set_option autoImplicit true
namespace qH2fULd
noncomputable section
open Polynomial Finset
open qQ9yWTb (Raw Curve Moving Usable height)
open qy95ATd (WordChart left root weight site G width lowRate B marks)
open qb0hmCe (CurveModel SiteTarget)
open P6 (K I blockLength p)
open P6_7_3 (Input)
open P5_7_7 (hit)
open scoped Classical
def c1 :Prop :=
  ∀ (x :Input) (U:zJe K),U⊆x.Γ → ∀ (J:WordChart x U) (T:zJe K),T⊆U →
    ∀ (e W:ℕ),e<p →
    ∀ F:Raw,Moving F→F.natDegree≤e →
      (∀ f :Raw,Irreducible f→f∣F→weight J f≤W) →
      (∀ γ∈T,root J F γ) →
      ∀ q:Curve,Irreducible q →
        Nonempty (Prepared J q (T.filter fun γ=>Usable q (site x γ)) e W (height F))
def c2 :Prop :=
  ∀ {x :Input} {U:zJe K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C),S.d<p → ∀ R:SiteTarget,
      (S.marks.filter (exception R S)).card≤2*S.d*(S.h+S.d*R.height q)
def c3:Prop :=
  ∀ {x :Input} {U:zJe K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) (e W:ℕ),S.d≤e→e<p →
    2*left J+(J.u₁-J.u₀)=width→e*width≤W →
    (2*e-2)*W-e*(e-1)*width<p →
    (∀ i,(S.f.coeff i).natDegree+S.d*left J+i*(J.u₁-J.u₀)≤W∨S.f.coeff i=0) →
    ∑ γ∈S.marks,poleOrderAt S γ≤poleRate e W*S.h
private theorem word_budget (local_test :c2)
    {x :Input} {U:zJe K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) (hp:S.d<p) (i:I) :
    (S.marks.filter fun γ => ¬ hit x.M.word x.F.scalar γ i ∧
      (S.num γ).eval (P5_7_7.base i)≠0).card≤2*S.d*S.h:= by
  let y :=P5_7_7.base i
  let R:SiteTarget :=⟨y,0,J.a₁.eval y,0,J.a₀.eval y,0⟩
  have h:=local_test S hp R
  have h0:R.height q=0:= by simp [SiteTarget.height,R]
  rw [h0,Nat.mul_zero,Nat.add_zero] at h
  refine (card_le_card ?_).trans h
  intro γ hγ
  obtain ⟨hS,hm,hn⟩:=mem_filter.mp hγ
  refine mem_filter.mpr ⟨hS,?_⟩
  have hmatch :targetMatch R J γ:= by
    simpa only [targetMatch,R,y,zero_mul,add_zero] using
      ⟨(J.target i).symm,(J.dual_hits γ (S.Bp hS) i).mpr hm⟩
  exact ⟨hmatch,fun he=>hn (he.mpr (Or.inl (by simp [SiteTarget.det,R])))⟩
private theorem primary_budget (local_test :c2)
    {x :Input} {U:zJe K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) (hp:S.d<p) (R:Starts J) :
    (S.marks.filter fun γ=>S.num γ=0).card≤4*S.d*(S.h+S.d*q.totalDegree) := by
  let Q (i:Fin 2) :SiteTarget :=⟨R.center i,i,R.a i,R.b i,R.c i,R.d i⟩
  let bad (i:Fin 2) :=S.marks.filter (exception (Q i) S)
  have hb (i:Fin 2) : (bad i).card≤2*S.d*(S.h+S.d*q.totalDegree) := by
    have h: (Q i).height q≤q.totalDegree := by unfold SiteTarget.height; split <;> omega
    exact (local_test S hp (Q i)).trans (by gcongr)
  have hcover :S.marks.filter (fun γ=>S.num γ=0)⊆bad 0∪bad 1 := by
    intro γ hγ
    obtain ⟨hS,hzero⟩:=mem_filter.mp hγ
    obtain ⟨a,ha,_,i,hi⟩:=S.arc γ hS
    have hd:S.direction γ i≠0:= by
      unfold Sheet.direction
      rw [dite_eq_left hS,ha i]
      exact fun hz=>hi ((LaurentSeries.coeff_coe_powerSeries (a i) 1).symm.trans hz)
    have hn: (Q i).det≠0:=R.invertible i
    have hm:targetMatch (Q i) J γ:= by
      refine ⟨?_,R.target γ (S.Bp hS) i⟩
      change R.a i+R.b i*site x γ i≠0∨R.c i+R.d i*site x γ i≠0
      by_contra! hf
      apply hn
      dsimp only [Q,SiteTarget.det]
      linear_combination R.d i*hf.1 - R.b i*hf.2
    have hr :γ∈bad i:=mem_filter.mpr ⟨hS,hm,fun he =>
      ((he.mp (by simp [hzero])).elim hn hd)⟩
    fin_cases i
    · exact mem_union_left _ hr
    · exact mem_union_right _ hr
  calc
    _≤(bad 0).card+(bad 1).card:=(card_le_card hcover).trans (card_union_le _ _)
    _≤_:=(z9f (hb 0) (hb 1)).trans_eq (by ring)
theorem of_children (prep:c1) (local_test :c2) (pole :c3) :qy95ATd.c5:= by
  intro x U hU J T hT e u w hw F hF hdeg _ hweight hroot q hq
  by_cases hne :U.Nonempty
  swap
  · have ht : ¬ T.Nonempty := fun ⟨γ,hγ⟩=>hne ⟨γ,hT hγ⟩
    rw [not_nonempty_iff_eq_empty.mp ht,filter_empty,card_empty,Nat.cast_zero]
    unfold B
    positivity
  obtain ⟨_,hep,_,_,_,_,_,hW,_,_,_,hchar,_,_⟩:=hw
  have hwidth :=(qXdgDRd.chart_bounds J (marks x U hU) hne).1
  obtain ⟨S⟩:=prep x U hU J T hT e w.W hep F hF hdeg hweight hroot q hq
  obtain ⟨R⟩:=starts hU J
  let T' := T.filter fun γ=>Usable q (site x γ)
  let V:=univ.biUnion fun j=>(S.part j).marks
  let bw:=2*e*blockLength+poleRate e w.W+G*(4*e)
  have hV:V⊆T' := fun γ hγ=> by
    obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
    exact S.inside j hj
  have hsum : ∑ j,G*(S.part j).marks.card ≤
      bw*(∑ j,(S.part j).h)+(4*e*G*q.totalDegree)*(∑ j,(S.part j).d) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    let A:=S.part j
    have hd:A.d≤e :=(single_le_sum (fun i _=>Nat.zero_le (S.part i).d) hj).trans S.degree
    have hp:A.d<p:=hd.trans_lt hep
    calc
      G*A.marks.card≤blockLength*(2*A.d*A.h)+poleRate e w.W*A.h+G*(4*A.d*(A.h+A.d*q.totalDegree)) :=
        count hU A _ _ _ (word_budget local_test A hp) (pole A e w.W hd hep hwidth hW hchar (S.weight j)) (primary_budget local_test A hp R)
      _≤blockLength*(2*e*A.h)+poleRate e w.W*A.h+G*(4*e*(A.h+A.d*q.totalDegree)) := by gcongr
      _ = _:= by dsimp only [A,bw]; ring
  have hcount:G*T'.card≤lowRate e w.W*height F*q.totalDegree+G*(qQ9yWTb.base e*q.totalDegree) := by
    have hparts :V.card ≤ ∑ j,(S.part j).marks.card:=card_biUnion_le
    calc
      G*T'.card=G*(T' \ V).card+G*V.card:= by
        rw [show T'.card=(T' \ V).card+V.card from (card_sdiff_add_card_eq_card hV).symm,
          Nat.mul_add]
      _≤G*(T' \ V).card + ∑ j,G*(S.part j).marks.card:= by
        rw [← mul_sum]
        exact Nat.add_le_add_left (zBI G hparts) _
      _≤G*((7+2*e)*height F*q.totalDegree)+(bw*(height F*q.totalDegree)+(4*e*G*q.totalDegree)*e) :=
        z9f (zBI _ S.zJ)
          (hsum.trans (z9f (zBI _ S.height) (zBI _ S.degree)))
      _=lowRate e w.W*height F*q.totalDegree+G*(4*e*e*q.totalDegree) := by
        dsimp only [bw]
        unfold lowRate poleRate
        ring
      _≤_:= by unfold qQ9yWTb.base; gcongr; exact Nat.le_add_right _ _
  have hg:0<(G:ℚ) := by exact_mod_cast (show 0<G from by decide)
  have hc: (T'.card:ℚ)*G ≤
      (lowRate e w.W:ℚ)*height F*q.totalDegree+G*(qQ9yWTb.base e*q.totalDegree :ℕ) := by
    rw [mul_comm (T'.card:ℚ)]
    exact_mod_cast hcount
  apply (le_of_mul_le_mul_right ?_ hg)
  refine hc.trans_eq ?_
  unfold B
  push_cast
  field_simp
end
end qH2fULd
end
