import ProximityPrize.SubmissionLower.B
import ProximityPrize.SubmissionLower.Z9wruub
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6
open aw6 (bpp aDT ayM)
open private a1X from ProximityPrize.SubmissionLower.B
theorem auR (P:K[X]) (i:I) :
    (P.map twist).eval (node i)=twist (P.eval (node i)) :=
  aw6.auR P i
theorem dRB {cap u deleted} (F:Direction cap u deleted)
    (hmargin:k+3*cap≤blockLength) :Nonempty (by5 F) := by
  classical
  let d:=k+F.U.natDegree+F.s
  let w (i:I) :=(F.A 0).eval (node i)*u 1 i-(F.A 1).eval (node i)*u 0 i
  let A' (j:Fin 2) :=(F.A j).map twist
  let P (j:Fin 2) :=F.A 0*F.out j 1-F.A 1*F.out j 0
  let P' (j:Fin 2) :=A' 1*F.out 0 j - A' 0*F.out 1 j
  have hheight:=F.height
  change F.U.natDegree+F.s+deleted.card≤ cap at hheight
  have hroom:d+2*F.s+deleted.card≤blockLength:= by
    dsimp only [d]
    omega
  have hk :0<k := by decide
  have hpos :0<d:= by dsimp only [d]; omega
  have ha (j:Fin 2) : (F.A j).natDegree≤F.s := by
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have ha' (j:Fin 2) : (A' j).natDegree≤F.s :=natDegree_map_le.trans (ha j)
  have hout (i j:Fin 2) : (F.out i j).natDegree<d :=
    aDT hpos (F.out_degree i j)
  have hprod {a :K[X]} (ha :a.natDegree≤F.s) (i j:Fin 2) :
      (a*F.out i j).natDegree<d+F.s :=
    natDegree_mul_le.trans_lt (by have :=hout i j; omega)
  obtain ⟨leftLift,hY,hYn⟩:=a1X deleted (fun i=>F.U.eval (node i)*w i) A' P d F.s
    (by simp only [A',natDegree_map_eq_of_injective twist.injective]; rfl)
    (F.primitive.map (Polynomial.mapRingHom twist)) hpos hroom
    (fun j=>(natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha 0) j 1) (hprod (ha 1) j 0)))
    (by intro i hi j; simp only [P,A',w,eval_sub,eval_mul,F.nodes i hi]; ring)
  obtain ⟨rightLift,hZ,hZn⟩:=a1X deleted (fun i=>F.V.eval (node i)*twist (w i)) F.A P' d F.s
    rfl F.primitive hpos hroom
    (fun j=>(natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha' 1) 0 j) (hprod (ha' 0) 1 j)))
    (by intro i hi j
        simp only [P',A',w,eval_sub,eval_mul,F.nodes i hi,auR,map_sub,map_mul]
        ring)
  let f :RatFunc K:=algebraMap K[X] (RatFunc K) leftLift/algebraMap K[X] (RatFunc K) F.U
  have heq :f.num*F.U=leftLift*f.denom:=(RatFunc.num_mul_eq_mul_denom_iff F.U_ne).mpr rfl
  have hn (i:I) (hi:i∉deleted) :f.num.eval (node i)=f.denom.eval (node i)*w i:= by
    have h:=congrArg (eval (node i)) heq
    simp only [eval_mul,hYn i hi] at h
    apply mul_left_cancel₀ (ayM F.U_dvd (F.den_nodes i))
    linear_combination h
  have hleft:f.denom∣F.U:=RatFunc.denom_div_dvd _ _
  have hdegG:=natDegree_le_of_dvd hleft F.U_ne
  have hnf :f.num.natDegree<k+F.s+f.denom.natDegree := by
    by_cases hzero :f.num=0
    · simp [hzero]
    have hy :leftLift≠0:= by
      intro hz
      rw [hz,zero_mul] at heq
      exact mul_ne_zero hzero F.U_ne heq
    have h:=congrArg natDegree heq
    rw [natDegree_mul hzero F.U_ne,natDegree_mul hy f.denom_ne_zero] at h
    dsimp [d] at hY
    omega
  have heq' : f.denom.map twist*rightLift=f.num.map twist*F.V:= by
    apply bpp (deleted:=deleted) (d:=d+F.U.natDegree)
    · change d+F.U.natDegree+deleted.card≤blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have hg: (f.denom.map twist).natDegree≤f.denom.natDegree :=natDegree_map_le
      omega
    · apply natDegree_mul_le.trans_lt
      have hg: (f.num.map twist).natDegree≤f.num.natDegree :=natDegree_map_le
      have hh:=F.degrees_eq
      dsimp [d]
      omega
    · intro i hi
      simp only [eval_mul,auR,hn i hi,hZn i hi,map_mul]
      ring
  have hcop:IsCoprime (f.denom.map twist) (f.num.map twist) :=
    f.isCoprime_num_denom.symm.map (Polynomial.mapRingHom twist)
  exact ⟨⟨f.denom,f.num,f.monic_denom,hleft,
    hcop.dvd_of_dvd_mul_left (by rw [← heq']; exact dvd_mul_right _ _),
    degree_le_natDegree.trans_lt (by exact_mod_cast hnf),hn⟩⟩
end
end P6_5
end
section
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6 gR ProximityPrize.Benchmark
open aw6 (ayM cVy)
open private cIe from ProximityPrize.SubmissionLower.B
variable {A cap:ℕ} {u:e9} {deleted:Finset I} {F:Direction cap u deleted} {η γ:K}
  {anchor :a9J A u η}
private def bxZ (O:Offset F anchor) (m:a9J A u γ) :=
  m.decoder-anchor.decoder - C (γ-η)*O.qW
private def numerator (O:Offset F anchor) (m:a9J A u γ) :=
  O.E*bxZ O m - C (γ-η)*O.Q
private theorem aFF (O:Offset F anchor) (i:I) :O.E.eval (node i)≠0 :=
  ayM (O.left.trans F.U_dvd) (F.den_nodes i)
private theorem gDQ (O:Offset F anchor) (m:a9J A u γ) :
    (bxZ O m).degree<k := by
  unfold bxZ
  rw [C_mul']
  exact Principal.degree_sub_lt (Principal.degree_sub_lt m.degree anchor.degree)
    (Principal.aNc _ O.ajX)
private theorem af0 (O:Offset F anchor) (m:a9J A u γ) :
    (numerator O m).natDegree<k+O.E.natDegree := by
  have hQ:=O.proper.trans_le (degree_le_natDegree (p:=O.E))
  by_cases hz :numerator O m=0
  · simpa only [hz,natDegree_zero] using
      (Nat.lt_of_lt_of_le (show 0<k by decide) (Nat.le_add_right k O.E.natDegree))
  apply (natDegree_lt_iff_degree_lt hz).mpr
  apply Principal.degree_sub_lt (kL.ahy O.E (bxZ O m)
    O.E.natDegree k le_rfl (gDQ O m))
  rw [C_mul']
  exact Principal.aNc _ (hQ.trans_le (by exact_mod_cast Nat.le_add_left _ _))
private theorem lg (O:Offset F anchor) (W:K[X]) (hW:F.den=O.E*W)
    (m:a9J A u γ) (avoid :Disjoint m.support deleted) (i:I) (hi:i∈m.support) :
    W.eval (node i)*(numerator O m).eval (node i)=(F.amp γ).eval (node i)*O.raw i:= by
  have hd:=Finset.disjoint_left.mp avoid hi
  have he :=aFF O i
  have hf :=O.first i hd
  have hs :=O.second i hd
  have hn:=F.den_nodes i
  have hw:F.den.eval (node i)=O.E.eval (node i)*W.eval (node i) := by rw [hW,eval_mul]
  simp only [Direction.amp,eval_add,eval_C,eval_mul] at hf ⊢
  rw [eq_div_iff hn] at hf
  have hs' : O.E.eval (node i)*F.den.eval (node i)*(u 1 i - O.qW.eval (node i)) =
      F.den.eval (node i)*O.Q.eval (node i)+O.E.eval (node i)*((F.A 1).eval (node i)*O.raw i) := by
    rw [hs]
    field_simp [he,hn]
  simp only [numerator,bxZ,eval_sub,eval_mul,eval_C,m.lg i hi]
  apply mul_left_cancel₀ he
  rw [← mul_assoc,← hw]
  linear_combination O.E.eval (node i)*hf+(γ-η)*hs'
private theorem ec0 (hmargin:k+cap≤A)
    (O:Offset F anchor) (W:K[X]) (hW:F.den=O.E*W)
    (m:a9J A u γ) (avoid :Disjoint m.support deleted) (reg:Regular F γ) :
    ∃ N :K[X],numerator O m=F.amp γ*N∧(W*N).map twist=W*N := by
  classical
  obtain ⟨l,hl⟩:=O.left
  obtain ⟨r,hr⟩:=O.right
  have hl0:l≠0:= fun hz=>F.U_ne (by simp [hl,hz])
  have hr0:r≠0:= fun hz=>F.V_ne (by simp [hr,hz])
  have hWnodes (i:I) :W.eval (node i)≠0 :=
    ayM (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  have hEσ:O.E.map twist≠0:=(O.E_monic.map twist).ne_zero
  have hphase :l*W.map twist=r*W:= by
    apply mul_left_cancel₀ (mul_ne_zero O.E_monic.ne_zero hEσ)
    have h:=F.phase
    rw [hl,hr,hW,Polynomial.map_mul] at h
    linear_combination h
  let a :=F.amp γ
  let P:=numerator O m
  let diff :=l*a.map twist*P - r*a*P.map twist
  have zero_at (i:I) (hi:i∈m.support) :diff.eval (node i)=0:= by
    have hrw:=O.raw_fixed i (Finset.disjoint_left.mp avoid hi)
    have h1 :=lg O W hW m avoid i hi
    have h2 :=congrArg twist h1
    simp only [map_mul,hrw] at h2
    have h3:=congrArg (eval (node i)) hphase
    simp only [eval_mul,auR] at h3
    simp only [diff,eval_sub,eval_mul,auR]
    change W.eval (node i)*P.eval (node i)=a.eval (node i)*O.raw i at h1
    change twist (W.eval (node i))*twist (P.eval (node i)) =
      twist (a.eval (node i))*O.raw i at h2
    apply (mul_eq_zero.mp (show W.eval (node i)*_=0 from ?_)).resolve_left (hWnodes i)
    linear_combination l.eval (node i)*twist (a.eval (node i))*h1 -
      l.eval (node i)*a.eval (node i)*h2 +
      a.eval (node i)*twist (P.eval (node i))*h3
  have ident :diff=0:= by
    by_contra hne
    have hroot :=kL.agd node IRSProfile.domain.injective diff hne m.support zero_at
    have hld:O.E.natDegree+l.natDegree=F.U.natDegree := by
      rw [hl,natDegree_mul O.E_monic.ne_zero hl0]
    have hrd:O.E.natDegree+r.natDegree=F.U.natDegree := by
      rw [← F.degrees_eq,hr,natDegree_mul hEσ hr0,natDegree_map_eq_of_injective twist.injective]
    have hP:=af0 O m
    have hA:=reg.degree_eq
    have hheight:=F.height
    change F.U.natDegree+F.s+deleted.card≤ cap at hheight
    have hdeg:diff.natDegree≤ max (l.natDegree+a.natDegree+P.natDegree)
        (r.natDegree+a.natDegree+P.natDegree) := by
      apply (natDegree_sub_le _ _).trans
      exact max_le_max
        (natDegree_mul_le.trans (Nat.add_le_add_right
          (natDegree_mul_le.trans (Nat.add_le_add_left natDegree_map_le _)) _))
        (natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_map_le))
    change P.natDegree<_ at hP
    change a.natDegree= _ at hA
    have hcount:=m.dw
    omega
  have eqn:l*a.map twist*P=r*a*P.map twist:=sub_eq_zero.mp ident
  have hlU:l∣F.U:=hl ▸ dvd_mul_left l O.E
  have cop:IsCoprime a (l*a.map twist) :=
    (reg.content_unit.of_isCoprime_of_dvd_right hlU).mul_right reg.adjacent
  have hdvd:a∣P:= by
    apply cop.dvd_of_dvd_mul_left
    rw [eqn]
    exact (dvd_mul_left a r).mul_right _
  obtain ⟨N,hN⟩:=hdvd
  refine ⟨N,hN,?_⟩
  have hred:l*N=r*N.map twist:= by
    apply mul_left_cancel₀ (mul_ne_zero reg.amp_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr reg.amp_ne))
    rw [hN,Polynomial.map_mul] at eqn
    linear_combination eqn
  rw [Polynomial.map_mul]
  apply mul_left_cancel₀ hl0
  linear_combination N.map twist*hphase-W*hred
theorem normalize {u deleted} (F:Direction cap u deleted) (hmargin:k+cap≤A)
    (Γ:Finset K) (reg : ∀ γ∈Γ,Regular F γ) (m : ∀ g:Γ,a9J A u g.val)
    (avoid : ∀ g,Disjoint (m g).support deleted) (η ζ:Γ) (hne :ζ.val≠η.val)
    (O:Offset F (m η)) :
    ∃ M:FJ cap u deleted,∃ S:Γ→K[X],
      ∃ marks : ∀ g:Γ,P1.bjQ (A:=A) M g.val (S g),∀ g,(marks g).bad=m g:= by
  classical
  obtain ⟨W,hW⟩:=O.left.trans F.U_dvd
  have hWn (i:I) :W.eval (node i)≠0 :=
    ayM (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  obtain ⟨L,c,hL,hLf,hLn,hsplit⟩:=cVy W hWn
  change L.map twist=L at hLf
  have hcn (i:I) :c.eval (node i)≠0 :=
    ayM (hL ▸ dvd_mul_left c W) (hLn i)
  have hscalar (g:Γ) : ∃ S:K[X],S.map twist=S ∧
      numerator O (m g)=c*F.amp g.val*S:= by
    obtain ⟨N,hN,hfix⟩:=ec0 hmargin O W hW (m g) (avoid g) (reg g.val g.property)
    obtain ⟨S,hS,hNS⟩:=hsplit N hfix
    exact ⟨S,hS,by rw [hN,hNS]; ring⟩
  choose S hS ident using hscalar
  let word (i:I) :=if i∈deleted then 0 else O.raw i/L.eval (node i)
  have hword (i:I) (hi:i∉deleted) :word i=O.raw i/L.eval (node i) := by simp [word,hi]
  have hden (i:I) :F.den.eval (node i)=O.E.eval (node i)*W.eval (node i) := by
    rw [hW,eval_mul]
  have hLval (i:I) :L.eval (node i)=W.eval (node i)*c.eval (node i) := by rw [hL,eval_mul]
  have hs :uO (F.amp η.val) (F.A 1)=F.s := by
    unfold uO
    rw [(reg η.val η.property).degree_eq]
    exact max_eq_left (le_max_right _ _)
  have hcop:IsCoprime O.E c:=cIe (sub_ne_zero.mpr hne) O.reduced (ident ζ)
  let M:FJ cap u deleted := {
    shift:=η.val
    pencil₀:=(m η).decoder
    pencil₁:=O.qW
    pencil₀_degree :=(m η).degree
    pencil₁_degree :=O.ajX
    E :=O.E
    factor :=c
    Q:=O.Q
    A₀:=F.amp η.val
    A₁:=F.A 1
    word:=word
    word_fixed:= by
      intro i
      by_cases hi:i∈deleted
      · simp [word,hi]
      · rw [hword i hi,map_div₀,O.raw_fixed i hi,← auR L i,hLf]
    word_deleted:= fun i hi=> by simp [word,hi]
    E_monic:=O.E_monic
    aFF:=aFF O
    factor_nodes := fun i _=>hcn i
    coprime_factor :=hcop
    offset_proper :=O.proper
    offset_reduced:=O.reduced
    adjacent_coprime :=F.coprime.mono O.left O.right
    amplitudes_primitive := by
      obtain ⟨x,y,hxy⟩:=F.primitive
      exact ⟨x,y - x*C η.val,by unfold Direction.amp; linear_combination hxy⟩
    first_amplitude_unit :=(reg η.val η.property).content_unit.of_isCoprime_of_dvd_right O.left
    aVi:= by
      rw [hs]
      have h:=F.height
      change F.U.natDegree+F.s+deleted.card≤ cap at h
      have hd:=natDegree_le_of_dvd O.left F.U_ne
      omega
    first_word:= by
      intro i hi
      rw [O.first i hi,hword i hi]
      field_simp [F.den_nodes i,hLn i]
      rw [hden,hLval]
      ring
    second_word:= by
      intro i hi
      rw [O.second i hi,hword i hi]
      field_simp [aFF O i,F.den_nodes i,hLn i]
      rw [hden,hLval]
      ring }
  have amp_eq (g:Γ) :P1.FJ.wK M g.val=F.amp g.val := by
    change F.amp η.val+C (g.val-η.val)*F.A 1=F.amp g.val
    simp only [Direction.amp,map_sub]
    ring
  let marks (g:Γ) :P1.bjQ (A:=A) M g.val (S g) := by
    have hreg:=reg g.val g.property
    refine {
      bad:=m g
      avoids_deleted:=avoid g
      scalar_fixed:=hS g
      aic := ?_
      scalar_hits := ?_
      pole_unit := ?_
      identity := ?_ }
    · by_cases hz :S g=0
      · exact Or.inl hz
      right
      have hc:c≠0:= fun h=>hcn 0 (by rw [h,eval_zero])
      have hd:=af0 O (m g)
      rw [ident g,natDegree_mul (mul_ne_zero hc hreg.amp_ne) hz,
        natDegree_mul hc hreg.amp_ne,hreg.degree_eq] at hd
      change (S g).natDegree≤(k :ℤ) - 1+(O.E.natDegree - c.natDegree -
        (uO (F.amp η.val) (F.A 1) :ℤ))
      rw [hs]
      omega
    · intro i hi
      have lg:=lg O W hW (m g) (avoid g) i hi
      rw [ident g,eval_mul,eval_mul] at lg
      change (S g).eval (node i)=word i
      have hd:=Finset.disjoint_left.mp (avoid g) hi
      rw [hword i hd,eq_div_iff (hLn i),hLval]
      apply mul_left_cancel₀ (hreg.node_unit i hd)
      linear_combination lg
    · rw [amp_eq g]
      exact hreg.content_unit.of_isCoprime_of_dvd_right O.left
    · rw [amp_eq g]
      exact ident g
  exact ⟨M,S,marks,fun g=>rfl⟩
end
end P6_5
end
section
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6 gR ProximityPrize.Benchmark
open aw6 (bpp aDT ayM)
theorem eF9 {A cap u deleted} (F:Direction cap u deleted) (H :by5 F)
    (hagMargin:k+cap≤A) (hdetMargin:k+2*cap≤blockLength)
    {η:K} (m:a9J A u η) (avoid :Disjoint m.support deleted) (reg:Regular F η) :
    Nonempty (Offset F m) := by
  classical
  let a :=F.amp η
  let w (i:I) :=u 0 i+η*u 1 i
  let r (j:Fin 2) :=F.out 0 j+C (twist η)*F.out 1 j
  let out:=r 0+C η*r 1
  let d:=k+F.U.natDegree+F.s
  have hheight:=F.height
  change F.U.natDegree+F.s+deleted.card≤ cap at hheight
  have hk :0<k := by
    change 0<131072
    decide
  have hpos :0<d:= by dsimp only [d]; omega
  have hA1 : (F.A 1).natDegree≤F.s :=le_max_right _ _
  have ha :a.natDegree=F.s :=reg.degree_eq
  have ha' : (a.map twist).natDegree≤F.s :=natDegree_map_le.trans ha.le
  have hr (j:Fin 2) : (r j).natDegree<d:= by
    apply (natDegree_add_le _ _).trans_lt
    exact max_lt (aDT hpos (F.out_degree 0 j))
      ((natDegree_C_mul_le _ _).trans_lt (aDT hpos (F.out_degree 1 j)))
  have hout:out.natDegree<d:=(natDegree_add_le _ _).trans_lt
    (max_lt (hr 0) ((natDegree_C_mul_le _ _).trans_lt (hr 1)))
  have hrn (j:Fin 2) (i:I) (hi:i∉deleted) : (r j).eval (node i) =
      F.U.eval (node i)*(a.map twist).eval (node i)*u j i -
      F.V.eval (node i)*(F.A j).eval (node i)*twist (w i) := by
    simp only [r,w,a,Direction.amp,auR,eval_add,eval_mul,eval_C,
      F.nodes i hi,map_add,map_mul]
    ring
  have hspec (i:I) (hi:i∉deleted) :out.eval (node i) =
      F.U.eval (node i)*(a.map twist).eval (node i)*w i -
      F.V.eval (node i)*a.eval (node i)*twist (w i) := by
    simp only [out,eval_add,eval_mul,eval_C,hrn _ i hi,a,Direction.amp,w,eval_add,
      eval_mul,eval_C]
    ring
  have hp:=aDT hk m.degree
  have ident :F.U*a.map twist*m.decoder-F.V*a*m.decoder.map twist=out:= by
    let left:=F.U*a.map twist*m.decoder-F.V*a*m.decoder.map twist
    have hdeg:left.natDegree<d:= by
      apply (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · apply natDegree_mul_le.trans_lt
        have h: (F.U*a.map twist).natDegree≤F.U.natDegree+(a.map twist).natDegree :=
          natDegree_mul_le
        dsimp only [d]; omega
      · apply natDegree_mul_le.trans_lt
        have h: (F.V*a).natDegree≤F.V.natDegree+a.natDegree :=natDegree_mul_le
        have h' : (m.decoder.map twist).natDegree≤ m.decoder.natDegree :=natDegree_map_le
        have :=F.degrees_eq
        dsimp only [d]; omega
    apply sub_eq_zero.mp
    by_contra hne
    have hc:=kL.agd node IRSProfile.domain.injective (left-out) hne m.support
      (by intro i hi
          rw [eval_sub,hspec i (Finset.disjoint_left.mp avoid hi)]
          simp only [left,eval_sub,eval_mul,auR,m.lg i hi,w,sub_self])
    have hd:=natDegree_sub_le left out
    have hag:A≤ m.support.card:=m.dw
    dsimp only [d] at hdeg hout
    omega
  have hG:=natDegree_le_of_dvd H.left F.U_ne
  have hLd:=aDT (by omega :0<k+F.s+H.G.natDegree) H.degree_lt
  have determinant:H.G*(a*r 1-F.A 1*out)=F.U*a.map twist*H.L:= by
    apply bpp (deleted:=deleted) (d:=d+F.s+H.G.natDegree)
    · change d+F.s+H.G.natDegree+deleted.card≤blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have h1 := @natDegree_mul_le _ _ a (r 1)
      have h2 := @natDegree_mul_le _ _ (F.A 1) out
      have h3:=natDegree_sub_le (a*r 1) (F.A 1*out)
      have :=hr 1
      omega
    · apply natDegree_mul_le.trans_lt
      have h := @natDegree_mul_le _ _ F.U (a.map twist)
      dsimp only [d]; omega
    · intro i hi
      simp only [eval_mul,eval_sub,hrn 1 i hi,hspec i hi,H.nodes i hi,a,Direction.amp,
        eval_add,eval_mul,eval_C,w]
      ring
  have div :a∣H.L+H.G*F.A 1*m.decoder := by
    have cop:IsCoprime a (F.U*a.map twist) :=
      reg.content_unit.mul_right reg.adjacent
    apply cop.dvd_of_dvd_mul_left
    refine ⟨H.G*(r 1+F.A 1*F.V*m.decoder.map twist),?_⟩
    linear_combination H.G*F.A 1*ident - determinant
  obtain ⟨J,hJ⟩:=div
  have hjd:J.natDegree<k+H.G.natDegree := by
    by_cases hj:J=0
    · simp [hj]
    have h:=natDegree_add_le H.L (H.G*F.A 1*m.decoder)
    rw [hJ,natDegree_mul reg.amp_ne hj,ha] at h
    have h1 := @natDegree_mul_le _ _ H.G (F.A 1)
    have h2 := @natDegree_mul_le _ _ (H.G*F.A 1) m.decoder
    omega
  let f :RatFunc K:=algebraMap K[X] (RatFunc K) J/algebraMap K[X] (RatFunc K) H.G
  have hfrac:f.num*H.G=J*f.denom:=(RatFunc.num_mul_eq_mul_denom_iff H.monic.ne_zero).mpr rfl
  have hE :f.denom∣H.G:=RatFunc.denom_div_dvd _ _
  let Q:=f.num %ₘ f.denom
  let qW:=f.num /ₘ f.denom
  have division :Q+f.denom*qW=f.num :=modByMonic_add_div _ _
  have hn:f.num.natDegree<k+f.denom.natDegree := by
    by_cases hn:f.num=0
    · simp [hn]
    have hj:J≠0:= by
      intro hz
      rw [hz,zero_mul] at hfrac
      exact mul_ne_zero hn H.monic.ne_zero hfrac
    have h:=congrArg natDegree hfrac
    rw [natDegree_mul hn H.monic.ne_zero,natDegree_mul hj f.denom_ne_zero] at h
    omega
  have hpencil:qW.degree<k := by
    have hd:qW.natDegree<k := by
      rw [show qW.natDegree=f.num.natDegree - f.denom.natDegree from
        natDegree_divByMonic _ f.monic_denom]
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  let raw (i:I) :=F.den.eval (node i)*(w i - m.decoder.eval (node i))/a.eval (node i)
  have hUn (i:I) :=ayM F.U_dvd (F.den_nodes i)
  have hfixed (i:I) (hi:i∉deleted) :twist (raw i)=raw i:= by
    have h1 :=congrArg (eval (node i)) ident
    simp only [eval_sub,eval_mul,auR,hspec i hi] at h1
    have h2 :=congrArg (eval (node i)) F.phase
    simp only [eval_mul,auR] at h2
    have ha0:a.eval (node i)≠0:=reg.node_unit i hi
    have haσ:twist (a.eval (node i))≠0:=(map_ne_zero twist).mpr ha0
    simp only [raw,map_div₀,map_mul,map_sub]
    apply (div_eq_div_iff haσ ha0).mpr
    apply mul_left_cancel₀ (hUn i)
    linear_combination F.den.eval (node i)*h1 +
      a.eval (node i)*(twist (w i) - twist (m.decoder.eval (node i)))*h2
  refine ⟨{
    qW:=qW
    ajX:=hpencil
    E :=f.denom
    Q:= Q
    E_monic:=f.monic_denom
    left:=hE.trans H.left
    right:=(map_dvd (Polynomial.mapRingHom twist) hE).trans H.right
    proper :=degree_modByMonic_lt _ f.monic_denom
    reduced := ?_
    raw:=raw
    raw_fixed:=hfixed
    first := ?_
    second := ?_ }⟩
  · obtain ⟨x,y,h⟩:=f.isCoprime_num_denom
    rw [← division] at h
    exact ⟨x,x*qW+y,by linear_combination h⟩
  · intro i hi
    change w i - m.decoder.eval (node i)=a.eval (node i)*raw i/F.den.eval (node i)
    have ha0:a.eval (node i)≠0:=reg.node_unit i hi
    simp only [raw]
    field_simp [ha0,F.den_nodes i]
  · intro i hi
    have h1 :=congrArg (eval (node i)) hJ
    simp only [eval_add,eval_mul,H.nodes i hi] at h1
    have h2 :=congrArg (eval (node i)) hfrac
    simp only [eval_mul,← division,eval_add,eval_mul] at h2
    have hEn:=ayM ((hE.trans H.left).trans F.U_dvd) (F.den_nodes i)
    have hGn:=ayM (H.left.trans F.U_dvd) (F.den_nodes i)
    have ha0:a.eval (node i)≠0:=reg.node_unit i hi
    change u 1 i - qW.eval (node i)= Q.eval (node i)/f.denom.eval (node i) +
      (F.A 1).eval (node i)*raw i/F.den.eval (node i)
    simp only [raw]
    field_simp [F.den_nodes i,hEn,ha0]
    apply mul_left_cancel₀ hGn
    have h3:a.eval (node i)=(F.A 0).eval (node i)+η*(F.A 1).eval (node i) := by
      simp only [a,Direction.amp,eval_add,eval_mul,eval_C]
    dsimp [w]
    linear_combination f.denom.eval (node i)*h1-a.eval (node i)*h2 +
      f.denom.eval (node i)*H.G.eval (node i)*u 1 i*h3
end
end P6_5
end
