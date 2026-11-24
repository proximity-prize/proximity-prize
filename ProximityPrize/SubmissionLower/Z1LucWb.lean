import ProximityPrize.SubmissionLower.ZpYo3sb
import ProximityPrize.SubmissionLower.ZJ6ikSc
import ProximityPrize.SubmissionLower.Z7V3Ypa
import ProximityPrize.SubmissionLower.Zy3W3oe
set_option Elab.async false
section
set_option autoImplicit true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qXdgDRd
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7 (NativeWitness NativeSeedBound)
open P5_7_7
open qZCRTge
open P5_7_7R (atm)
open cu (L)
open private embed_bound from ProximityPrize.SubmissionLower.ZsWhgLc
open private boxed_bounds narrow from ProximityPrize.SubmissionLower.Z84uvqb
open private BA phys_injective cZl dLK from ProximityPrize.SubmissionLower.ZRSUmIe
theorem aIF {D l h u s :ℕ} (F:Dg) (x :NativeWitness)
    (hf :Irreducible F) (he :Irreducible (embed F)) (hl:F.natDegree=l)
    (hl₂:2≤l) (hh:0<h) (hF : ∀ i,(F.coeff i).natDegree≤h)
    (hw:2*u+s=width D) (hok :Witness D l x) (hbelow : ¬ BelowAt F u s x.W) :
    let E :=l+x.g
    let M:=x.W+1+x.j*width D
    ∃ (a :L) (H G B:Dg),
      H*F=G+C (C (((Polynomial.X:L[X]) - C a)^M))*B ∧
      G.natDegree≤E∧B.natDegree≤E∧NativeSeedBound (embed G) ((x.c+1)*h) ∧
      atm G E u s M∧IsCoprime (ek (embed F)) (ek (embed G)) := by
  subst l
  let l:=F.natDegree
  let g:=x.g
  let E :=l+g
  let M:=x.W+1+x.j*width D
  let v :=x.c*h
  let T:=v+h
  obtain ⟨hj,_,_,hs,_⟩:=hok
  have hM:0<M:= by dsimp only [M]; omega
  have hT:T=(x.c+1)*h:= by dsimp [T,v]; ring
  have hlarge : ∃ i j,(F.coeff i).coeff j≠0 ∧
      x.W<((F.coeff i).coeff j).natDegree+l*u+i*s := by
    unfold BelowAt at hbelow
    push Not at hbelow
    exact hbelow
  obtain ⟨a,R,hR,hrem⟩:=q81Yhob.proof F g h v M hf.ne_zero hM hF
  let top:= fun i:ℕ=>E*u+i*s
  let tail:= fun i:ℕ=>M-(x.W+1)-(g*u+i*s)
  let cuts : (ax0 g v (fun _=>M)→L) →ₗ[L] (ax0 E T top→L) :=
    LinearMap.pi fun r =>
      (cF0 r.1.1 r.2 (M-top r.1.1+(r.1.2 :ℕ))).comp R
  let good:cuts.ker →ₗ[L] Dg:=R.comp cuts.ker.subtype
  let bad: (ax0 g T tail→L) →ₗ[L] Dg :=
    (LinearMap.mulLeft L F).comp (pack g T tail)
  have narrow_good (q:cuts.ker) :P5_7_7R.atm (R q.val) E u s M:= by
    apply narrow (hrem q.val).1
    exact congrFun (LinearMap.mem_ker.mp q.property)
  suffices hex : ∃ q:cuts.ker,IsCoprime (ek (embed F)) (ek (embed (R q.val))) by
    obtain ⟨q,hq⟩:=hex
    obtain ⟨hb,B,hB,hrel⟩:=hrem q.val
    obtain ⟨hG,hseed⟩:=boxed_bounds hb
    refine ⟨a,pack g v (fun _=>M) q.val,R q.val,B,hrel,hG,hB,?_,narrow_good q,hq⟩
    apply embed_bound
    intro i
    rw [← hT]
    exact hseed i
  by_contra hnone
  have hsub:LinearMap.range good≤LinearMap.range bad:= by
    rintro G ⟨q,rfl⟩
    have hnot : ¬ IsCoprime (ek (embed F)) (ek (embed (R q.val))) :=
      fun hq=>hnone ⟨q,hq⟩
    obtain ⟨hdeg,hseed⟩:=boxed_bounds (hrem q.val).1
    obtain ⟨Q,hQ,hbox⟩:=qCAunta.proof F (R q.val) g T u s x.W M hf he (by omega)
      hlarge hdeg hseed (narrow_good q) hnot
    obtain ⟨b,hb⟩:=exists_pack hbox
    exact ⟨b,by change F*pack g T tail b=R q.val; rw [hb,← hQ]⟩
  have hdim:=cuts.finrank_range_add_finrank_ker
  have hcon :=cuts.range.finrank_le
  have hbadrank :Module.finrank L cuts.ker≤Module.finrank L (ax0 g T tail→L) := by
    rw [← LinearMap.finrank_range_of_inj (f :=good) (hR.comp Subtype.val_injective)]
    exact (Submodule.finrank_mono hsub).trans bad.finrank_range_le
  rw [slot_rank] at hdim hcon hbadrank
  have ht:=top_count E u s
  rw [hw] at ht
  change (∑ i:Fin (E+1),top i)= _ at ht
  rw [ht] at hcon
  have hb:=tail_count g x.j u s hj
  rw [hw] at hb
  have htail: (∑ i:Fin (g+1),tail i)≤width D*x.j*(x.j+1)/2 := by
    simpa only [tail,M,Nat.add_sub_cancel_left] using hb
  have hbd:=hbadrank.trans (Nat.mul_le_mul_right (T+1) htail)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hdim
  change (x.c+1)*(width D*E*(E+1)/2+width D*x.j*(x.j+1)/2) <
    (g+1)*x.c*M at hs
  have hstrict :=scale_surplus ((g+1)*M)
    (width D*E*(E+1)/2+width D*x.j*(x.j+1)/2) x.c h hh
    (by simpa only [mul_assoc,mul_left_comm x.c] using hs)
  rw [Nat.add_mul,← hT] at hstrict
  change _<((g+1)*M)*(v+1) at hstrict
  omega
theorem transfer {D w U S} (J:DualWord D w U S) {F H G B:Dg}
    {E M u s :ℕ} (hM:0<M) (a :L)
    (hrel :H*F=G+C (C (((Polynomial.X:L[X]) - C a)^M))*B)
    (hG:G.natDegree≤E) (hB:B.natDegree≤E)
    (hnarrow:atm G E u s M)
    {γ:K} (hγ:γ∈U) (z :K) (hden: (J.Q γ).natDegree≤u)
    (hnum : (J.P γ).natDegree≤u+s)
    (hr :atDual J F z γ=0) :nativeEval z (dualValue J γ) (embed G)=0:= by
  let d:=((Polynomial.X:L[X]) - C a)^M
  let ev :=(nativeEval z (dualValue J γ)).comp embed
  let P:=J.P γ
  let Q:=J.Q γ
  have hQ:Q≠0:=J.denominator γ hγ
  have hv :ev (C (C d))=phys d:= by
    simp [ev,embed,nativeEval,phys]
  have hcong:=congrArg ev hrel
  rw [map_mul,map_add,map_mul,hv] at hcong
  change ev H*atDual J F z γ=ev G+phys d*ev B at hcong
  rw [hr,mul_zero] at hcong
  have hmapped:=congrArg (· * phys Q^E) hcong
  simp only [zero_mul,add_mul,mul_assoc] at hmapped
  have heq :0=BA G E z P Q+d*BA B E z P Q:= by
    apply phys_injective
    simp only [map_zero,map_add,map_mul,cZl hG z P Q hQ,
      cZl hB z P Q hQ]
    exact hmapped
  have hdvd:d∣BA G E z P Q:= by
    refine ⟨-BA B E z P Q,?_⟩
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left heq.symm
  have hd:=dLK hM hnarrow z hnum hden
  have hzero :BA G E z P Q=0:= by
    by_contra hn
    have hb:=natDegree_le_of_dvd hdvd hn
    have hdm:d.natDegree=M:= by
      simp only [d,(monic_X_sub_C a).natDegree_pow,natDegree_X_sub_C,mul_one]
    exact hd.not_ge (hdm ▸ hb)
  have hroot :=cZl hG z P Q hQ
  rw [hzero,map_zero] at hroot
  exact (mul_eq_zero.mp hroot.symm).resolve_right
    (pow_ne_zero _ (map_ne_zero_iff _ phys_injective |>.2 hQ))
end
end qXdgDRd
end
section
set_option autoImplicit true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qXdgDRd
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open scoped Classical
open P5 (K I p blockLength)
open P5_7 (NativeWitness farAgreement OneSeedEquation)
open P5_7_7
open qGnV2ac
private theorem bv5 {D w U z S T F l h bw} (J:DualWord D w U S)
    (M:StrongMarks D w U z S) (hD:D ≤P6.dw) (ht:T⊆U) (C:Sections F) (hCT:C.CF⊆T)
    (hout: (T \ C.CF).card≤exclusions l*h)
    (hnodes : ∀ i:I,
      (C.CF.filter fun γ => ¬ hit w S γ i∧(C.A γ).eval (base i)≠0).card≤nodeRate l*h)
    (hpoles : ∑ γ∈C.CF,
      max (C.B γ).natDegree ((C.A γ).natDegree-relativeDegree J γ)≤bw*h) :
    gap D *T.card≤(exclusions l*gap D + nodeRate l*blockLength+bw)*h:= by
  let bad (γ:K) :=univ.filter fun i:I =>
    ¬ hit w S γ i∧(C.A γ).eval (base i)≠0
  let ν (γ:K) :=max (C.B γ).natDegree ((C.A γ).natDegree-relativeDegree J γ)
  have hγ (γ:K) (hm:γ∈C.CF) :gap D ≤(bad γ).card+ν γ:= by
    let miss :=univ \ sites w S γ
    have hcard:miss.card=blockLength-(sites w S γ).card:= by
      change (univ \ sites w S γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(C.A γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,mem_sites]
    have hsum:=card_filter_add_card_filter_not
      (s :=miss) (fun i=>(C.A γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hzero :=gR.kL.agd base base_injective
      (C.A γ) (C.nonzero γ hm) (miss.filter (fun i => ¬ (C.A γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hU:=ht (hCT hm)
    have ⟨ha,hq,hp⟩:=J.degree γ hU
    have horder :=J.order
    have hwidth :=J.gMz
    have hAgr :=M.strong γ hU
    have hN : (sites w S γ).card≤blockLength:= by
      simpa only [card_univ,index_card] using card_le_card (subset_univ (sites w S γ))
    have hmax :max (J.Q γ).natDegree ((J.P γ).natDegree-(J.u₁-J.u₀)) ≤
        farAgreement+J.u₀-(sites w S γ).card:=max_le hq (by omega)
    have hrel :relativeDegree J γ+(sites w S γ).card+gap D ≤blockLength:= by
      simp only [relativeDegree,gap]
      omega
    unfold ν
    omega
  have hswap : ∑ γ∈C.CF,(bad γ).card =
      ∑ i:I,(C.CF.filter fun γ => ¬ hit w S γ i∧(C.A γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈C.CF,(bad γ).card≤blockLength*(nodeRate l*h) := by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :Finset I))
      (f := fun _=>nodeRate l*h) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>hnodes i
  have hgood:C.CF.card*gap D ≤blockLength*(nodeRate l*h)+bw*h:= by
    rw [← sum_const_nat (s :=C.CF) (f := fun _=>gap D) (fun _ _=>rfl)]
    exact (sum_le_sum fun γ hmem=>hγ γ hmem).trans
      (sum_add_distrib.trans_le (Nat.add_le_add hb hpoles))
  have hz :=(card_sdiff_add_card_eq_card hCT).symm
  rw [hz,Nat.mul_add]
  calc
    _≤gap D *(exclusions l*h)+(blockLength*(nodeRate l*h)+bw*h) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hout) (by simpa only [Nat.mul_comm _ (gap D)] using hgood)
    _ = _:= by ring
theorem low_count {D e w U z S T u s} (node :NodeBound e) (poles :PoleBound (width D) e)
    (J:DualWord D w U S) (M:StrongMarks D w U z S) (hD:D ≤P6.dw)
    (f :OneSeedEquation) (F:qyWKMud.Changed J f) (x :NativeWitness)
    (hl:2≤f.natDegree) (hle :f.natDegree≤e) (hp:f.natDegree<p)
    (hh:0<gY f) (hw:2*u+s=width D) (hs :J.u₁-J.u₀=s)
    (hok :Witness D f.natDegree x) (hbelow:BelowAt F.F u s x.W)
    (ht:T⊆U) (hr : ∀ γ∈T,atDual J F.F (z γ) γ=0) :
    gap D *T.card≤lowPrice D f.natDegree x*gY f := by
  let l:=f.natDegree
  let h:=gY f
  obtain ⟨G,r,hrec,hd,hi,hgi,hg,hm⟩ :=
    compress F.F h F.irred F.generic_irred F.raw_height (raw_moving (F.height.symm ▸ hh))
  have H :EquationBounds G l h:=⟨hi,hd.trans F.jU,hl,hp,hg,hm⟩
  let z' γ:=z γ^(p^r)
  have hroot (γ:K) (hγ:γ∈T) :atDual J G (z' γ) γ=0:= by
    change atPair G (z γ^(p^r)) (J.P γ) (J.Q γ)=0
    rw [← pullback_atPair,← hrec]
    exact hr γ hγ
  obtain ⟨C,hC,hout,hseed,hP,hQ⟩ :=
    choose_sections J H hgi ht (powered_seeds r (M.Kw.mono ht)) hroot
  obtain ⟨_,hW,_,_,hchar⟩:=hok
  have hwt:HE G s (x.W-l*u) := by
    intro i j hj
    have he : (F.F.coeff i).coeff (j*(p^r))=(G.coeff i).coeff j:= by
      rw [hrec,pullback_coeff]
    have hb:=hbelow i (j*(p^r)) (he.symm ▸ hj)
    rw [he,F.jU] at hb
    change ((G.coeff i).coeff j).natDegree+l*u+i*s≤x.W at hb
    omega
  have hb:=poles G l h u s x.W hle H hw hW hwt hchar C
  have hreldeg (γ:K) :pN C s γ=relativeDegree J γ:= by
    unfold pN relativeDegree
    rw [hs]
    rw [hP,hQ]
  have hbudget :
      ∑ γ∈C.CF,max (C.B γ).natDegree ((C.A γ).natDegree-relativeDegree J γ) ≤
        pole D l x*h:= by
    change _≤((6*l-4)*x.W-(3*l*l-4*l+2)*width D)*h
    refine (le_of_eq ?_).trans hb
    exact sum_congr rfl fun γ _=> by rw [hreldeg]
  apply bv5 J M hD ht C hC hout ?_ hbudget
  intro i
  have heq : (C.CF.filter fun γ => ¬ hit w S γ i∧(C.A γ).eval (base i)≠0) =
      C.CF.filter (fun γ =>
        (C.P γ).eval (base i)*J.a₀.eval (base i) =
        (C.Q γ).eval (base i)*J.a₁.eval (base i)∧(C.A γ).eval (base i)≠0) := by
    ext γ
    simp only [mem_filter,hP,hQ]
    exact and_congr_right fun hg=>and_congr (J.dual_hits γ (ht (hC hg)) i).symm Iff.rfl
  rw [heq]
  exact node G l h hle H C (base i) _ _ (J.target i)
end
end qXdgDRd
end
section
set_option autoImplicit true
namespace P6_7_3
open Finset
open cu (Shape slots triangle ku)
open private deJ from ProximityPrize.SubmissionLower.D9
open private margin margin_line margin_eq marginSlope from ProximityPrize.SubmissionLower.Z7V3Ypa
open private cck from ProximityPrize.SubmissionLower.E7
private def weight (U v a :ℕ) :=slots U (a*v) - slots U ((a+1)*v)
private theorem stock (U v g:ℕ) :
    (∑ a∈range g,weight U v a)+slots U (g*v)=triangle U:= by
  induction g with
  | zero=>simp [slots]
  | succ g ih =>
    rw [sum_range_succ,add_assoc,weight,
      Nat.sub_add_cancel (deJ U (Nat.mul_le_mul_right v (Nat.le_succ g))),ih]
private def vo (h j g U v x :ℕ) :=
  (∑ a∈range g,weight U v a*(x-2*h*(j+a))) +
    slots U (g*v)*(x-2*h*(j+g))
private theorem gMW (h j g U v x y d:ℕ) (hy :y≤x+d) :
    vo h j g U v y≤vo h j g U v x+triangle U*d:= by
  have hw (a :ℕ) :y-2*h*(j+a)≤x-2*h*(j+a)+d:= by omega
  unfold vo
  calc
    _≤(∑ a∈range g,weight U v a*(x-2*h*(j+a)+d)) +
        slots U (g*v)*(x-2*h*(j+g)+d) :=
      add_le_add (sum_le_sum fun a _=>Nat.mul_le_mul_left _ (hw a))
        (Nat.mul_le_mul_left _ (hw g))
    _ = _:= by
      simp only [mul_add,sum_add_distrib,← sum_mul]
      rw [add_add_add_comm,← add_mul,stock]
private def step (s :Shape) :ℕ:=s.m*(P5.dw-P6.dw)
private def offset (s :Shape) :ℕ:=(s.B+1)*(s.J+1)*(triangle s.U*step s)
private theorem gain_le (s :Shape) (h E v :ℕ) :
    P5_7_1.ZN h s E v≤ZN h s E v+offset s := by
  have hm:s.m*P5.dw=s.m*P6.dw+step s := by
    unfold step
    rw [← Nat.mul_add]
    rfl
  let new (q j:ℕ) :=vo h j ((q-j)/E) s.U v (s.m*P6.dw+j-q*(131071-h))
  let r :=triangle s.U*step s
  calc
    _≤ku s (fun q j=>new q j+r) := by
      change P5_7_1.jointGainAt P5.dw h s E v≤_
      unfold P5_7_1.jointGainAt ku
      apply sum_le_sum
      intro q _
      apply sum_le_sum
      intro j _
      apply gMW
      rw [hm]
      omega
    _=ZN h s E v + ∑ q∈range (s.B+1),(min q s.J+1)*r := by
      change _=P5_7_1.jointGainAt P6.dw h s E v+_
      simp only [P5_7_1.jointGainAt,ku,new,vo,weight,sum_add_distrib,
        sum_const,Nat.nsmul_eq_mul,card_range]
    _≤_:= by
      apply Nat.add_le_add_left
      calc
        _ ≤ ∑ _∈range (s.B+1),(s.J+1)*r :=
          sum_le_sum fun q _=>Nat.mul_le_mul_right r (Nat.succ_le_succ (min_le_right q s.J))
        _=offset s := by simp only [offset,r,sum_const,Nat.nsmul_eq_mul,card_range,mul_assoc]
private abbrev packetLo:ℕ:=2390
private def check (s :Shape) (E v :ℕ) :Bool :=
  decide (0<E) && decide (s.J≤ s.B) &&
    decide (1440*(offset s :ℤ)< margin s packetLo E v) &&
    decide (1440*(offset s :ℤ)< margin s hi E v)
private theorem of_check {s :Shape} {h E v :ℕ} (hl:packetLo≤h) (hu:h≤hi)
    (hc:check s E v=true) :j3 h s<ZN h s E v := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he,hJ⟩,hlo⟩,hhi⟩:=hc
  rw [margin_line s hi packetLo E v he hJ] at hhi
  have hhi' : 0<(margin s packetLo E v - 1440*(offset s :ℤ)) +
      ((hi:ℤ)-packetLo)*marginSlope s E v := by linarith only [hhi]
  have hp:=cck (Int.ofNat_le.mpr hl) (Int.ofNat_le.mpr hu) (sub_pos.mpr hlo) hhi'
  have hline :=margin_line s h packetLo E v he hJ
  rw [margin_eq s h E v he hJ] at hline
  have hg:=qPTjEYd.phase_bound s h E v (hu.trans (by decide :hi≤131071)) he
  have hnew : (P5_7_1.ZN h s E v :ℤ)≤(ZN h s E v :ℤ)+offset s := by
    exact_mod_cast gain_le s h E v
  change 1440*(qPTjEYd.phase s h E v 0 - qPTjEYd.phase s h E v 1-(j3 h s :ℤ))= _ at hline
  apply Int.ofNat_lt.mp
  linarith only [hp,hline,hg,hnew]
private def checked :ℕ→List (ℕ×ℕ)→Prop
  | _,[]=>True
  | i,p :: ps=>check { terminal with U:=min p.2 terminal.U } i (p.1+1)=true ∧
      checked (i+1) ps
private theorem checked_get {ps :List (ℕ×ℕ)} {i:ℕ} (hc:checked i ps) (n:Fin ps.length) :
    check { terminal with U:=min (ps.get n).2 terminal.U } (i+n.val) ((ps.get n).1+1)=true := by
  induction ps generalizing i with
  | nil=>exact Fin.elim0 n
  | cons p ps ih =>
    refine Fin.cases hc.1 (fun j => ?_) n
    change check { terminal with U:=min (ps.get j).2 terminal.U } (i+(j.val+1))
      ((ps.get j).1+1)=true
    rw [← Nat.add_assoc,Nat.add_right_comm i j.val 1]
    exact ih hc.2 j
set_option maxRecDepth 1024 in
set_option maxHeartbeats 4000000 in
private theorem grade_checks :checked 1 gw:= by
  simp only [gw,List.cons_append,List.nil_append,List.map_cons,List.map_nil]
  repeat' first | exact True.intro | refine And.intro (by decide +kernel) ?_
private theorem ordinary_check :check terminal (gw.length+1) 0=true :=rfl
theorem terminal_signs (h:ℕ) (hl:2390≤h) (hu:h≤hi) (t:Test) :
    j3 h (Lc t)<ZN h (Lc t) (ordinateThreshold t) (apo t) := by
  apply of_check hl hu
  cases t with
  | none=>exact ordinary_check
  | some i =>
    change check { terminal with U:=min (gw.get i).2 terminal.U } (i.val+1)
      ((gw.get i).1+1)=true
    rw [Nat.add_comm i.val 1]
    exact checked_get grade_checks i
end P6_7_3
end
section
set_option autoImplicit true
namespace P6_7_3
noncomputable section
open Polynomial
open cu (Equation vm yq)
open Qt (gY Qc)
def c1 :Prop :=
  ∀ (x :Input) (P:Poles x) (t:Test),bbk x.h (Lc t) P.rows
def c2 :Prop :=
  ∀ (x :Input) (P:Poles x),Nonempty (Picks x.h P.rows)
def c3:Prop :=
  ∀ x :Input,Nonempty (TopPair x)
def c4 :Prop :=
  ∀ (x :Input) (P:Poles x) (pick :Picks x.h P.rows),TopPair x →
    Nonempty (OriginCover x (pick.main ⟨0,by decide⟩).free)
def c5:Prop :=
  ∀ (x :Input) (P:Poles x) (pick :Picks x.h P.rows),
    OriginCover x (pick.main ⟨0,by decide⟩).free→Nonempty (Prefix x P.rows)
def c6:Prop :=
  ∀ (x :Input) (T:Finset P6.K),T⊆x.Γ →
    ∀ (i:aKj) (f :Equation),Dt.Reduced f →
    f.natDegree=i.val+1→vm f (cV i).1 →
    (∀ γ∈T,yq f (x.M.label γ) (x.F.scalar γ)=0)→T.card≤ retainedFee
private theorem eiO {f :Equation} (hp:0<f.natDegree)
    (reject : ∀ t:Test,ordinateThreshold t≤f.natDegree →
      apo t≤gY f→False) :
    ∃ i:aKj,f.natDegree=i.val+1∧vm f (cV i).1 := by
  have he :f.natDegree≤gw.length:= by
    by_contra! hlo
    exact reject none hlo (Nat.zero_le _)
  let i:aKj:=⟨f.natDegree-1,by omega⟩
  have hidx :f.natDegree=i.val+1 := by dsimp [i]; omega
  refine ⟨i,hidx,(Qc _ _).mp ?_⟩
  by_contra! hlow
  exact reject (some i) hidx.ge hlow
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :P6_7.c3:= by
  classical
  intro u del M Γ F hw hs H hc
  let x :Input :=⟨u,del,M,Γ,F,hw,hs,H,hc⟩
  obtain ⟨P⟩:=poles x
  obtain ⟨pick⟩:=h2 x P
  obtain ⟨top⟩:=h3 x
  obtain ⟨init⟩:=h4 x P pick top
  obtain ⟨Q⟩:=h5 x P pick init
  let T:=x.Γ \ Q.book
  have hT:T⊆x.Γ:=Finset.sdiff_subset
  have hpaid : (x.Γ \ T).card≤prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.book_bound
    intro γ hγ
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ∈T,∃ q∈Q.parents,P6_7.axy x.M x.F q γ :=
    fun γ hγ=>(Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  have hkept:T.card≤ retainedFee := by
    by_cases hm:T.Nonempty
    · obtain ⟨γ,hγ⟩:=hm
      obtain ⟨q,hq,_⟩:=cover γ hγ
      obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
      obtain ⟨hl,hh⟩:=emz x
      obtain ⟨i,he,hb⟩:=eiO hf.positive (by
        intro t hE hv
        exact (terminal_signs x.h ((by decide :2390≤lo).trans hl) hh t).not_ge
          (eqx P t (h1 x P t) Q.geometric Q.terminal_pass hf hE hv))
      apply h6 x T hT i f ⟨hf.positive,hf.primitive,hf.separable⟩ he hb
      intro η hη
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz
    · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
  change x.Γ.card≤P6.gJ.graph.regular
  rw [← Finset.card_sdiff_add_card_eq_card hT]
  exact (Nat.add_le_add hpaid hkept).trans (by decide)
end
end P6_7_3
end
