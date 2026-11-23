import ProximityPrize.SubmissionLower.Zn9MhWd
import ProximityPrize.SubmissionLower.Z67mtTa
import ProximityPrize.SubmissionLower.Zmk5EEe
set_option Elab.async false
open _root_ renaming Finset → zJe, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Polynomial.map_mul → zNl
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q8SCoCa
noncomputable section
open Polynomial Finset q3u9Tnc
open P6 (I K p blockLength)
open P5_7_2 (A)
open qe6nVeb (SeedPlane width gap)
open qE3Ebna (SiteTarget Starts Sheet relativeDegree poleOrderAt)
open P5_7_7 (base mL mem_sites base_injective index_card)
open cu (L j9)
open qb0hmCe (CurveModel)
open scoped Classical
open private no_common_root target_nonzero from ProximityPrize.SubmissionLower.ZgfRUfb
theorem starts {J:Input} {U:zJe K} (hU:U⊆J.CF) (B:DualWord J U) :
    Nonempty (Starts (oldWord B)) := by
  let σ:=frobenius L p
  rcases J.bY with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let H :Fin 2→ L[X] := ![J.block,J.block.map σ]
  let C:Fin 2→ L[X] := ![j9 (J.model.factor*J.model.A₀),
    (j9 (J.model.factor*J.model.A₀)).map σ]
  let N :Fin 2→ L[X] := ![j9 (J.model.factor*J.model.A₁),
    (j9 (J.model.factor*J.model.A₁)).map σ]
  let O:Fin 2→ L[X] := ![j9 J.model.Q,(j9 J.model.Q).map σ]
  have he (i:Fin 2) : ∃ y,(H i).eval y=0:= by
    have hn: (H i).Monic:= by fin_cases i <;> first | exact hm | exact hm'
    have hdeg: (H i).natDegree=J.model.iF.toNat := by
      fin_cases i <;> first | exact hd | exact hd'
    apply IsAlgClosed.exists_root
    rw [degree_eq_natDegree hn.ne_zero,hdeg]
    exact_mod_cast J.positive_height.ne'
  choose y hy using he
  have hnode' (i:Fin 2) (j:I) :y i≠base j:= by
    intro hij
    have hz :=hy i
    rw [hij] at hz
    fin_cases i
    · exact (hnode j).1 hz
    · exact (hnode j).2 hz
  have hloc (i:Fin 2) (V:zJe I) : (mL V).eval (y i)≠0:= by
    rw [mL,eval_prod]
    exact prod_ne_zero_iff.mpr fun j _=> by
      simpa only [eval_sub,eval_X,eval_C] using sub_ne_zero.mpr (hnode' i j)
  let c (i:Fin 2) :=(C i).eval (y i)
  let n (i:Fin 2) :=(N i).eval (y i)
  let o (i:Fin 2) :=(O i).eval (y i)
  let a₀ (i:Fin 2) :=B.a₀.eval (y i)
  let a₁ (i:Fin 2) :=B.a₁.eval (y i)
  let b₀ (i:Fin 2) :=B.b₀.eval (y i)
  let b₁ (i:Fin 2) :=B.b₁.eval (y i)
  have hc (i:Fin 2) :o i*c i≠0:= by
    have hh:IsCoprime (O i*C i) (H i) := by
      fin_cases i
      · simpa [O,C,H,j9,mul_assoc] using hdet
      · simpa [O,C,H,j9,mul_assoc,σ,zNl] using hdet'
    simpa only [o,c,eval_mul] using no_common_root hh (hy i)
  have hb (i:Fin 2) :a₁ i*b₀ i-a₀ i*b₁ i≠0:= by
    obtain ⟨v,hv,hB⟩:=B.determinant
    have hj:=congrArg (fun f :L[X]=>f.eval (y i)) hB
    have hn:a₀ i*b₁ i-a₁ i*b₀ i≠0:= by
      simp only [eval_sub,eval_mul,eval_C] at hj
      change a₀ i*b₁ i-a₁ i*b₀ i= _ at hj
      rw [hj]
      exact mul_ne_zero hv (hloc i univ)
    exact fun h=>hn (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
  let R (i:Fin 2) :SiteTarget :=⟨y i,i,b₁ i*c i,b₁ i*n i-a₁ i*o i,
    b₀ i*c i,b₀ i*n i-a₀ i*o i⟩
  have hinv (i:Fin 2) : (R i).det≠0:= by
    convert mul_ne_zero (hb i) (hc i) using 1
    dsimp only [R,qb0hmCe.SiteTarget.det]
    ring
  refine ⟨⟨R,?_,fun _=>rfl,hinv,?_⟩⟩
  · intro h
    have hz :=hy 0
    change y 0=y 1 at h
    rw [h] at hz
    exact no_common_root hcop (hy 1) hz
  · intro γ hγ i
    let z :=algebraMap K L (J.model.label γ)
    have hz :j9 (J.model.factor*J.model.wK γ)=C 0+Polynomial.C z*N 0:= by
      simp [C,N,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    have hσ: (j9 (J.model.factor*J.model.wK γ)).map σ =
        C 1+Polynomial.C (z^p)*N 1 := by
      rw [hz,Polynomial.map_add,zNl,Polynomial.map_C]
      rfl
    have hres :H i∣(C i+Polynomial.C (dcQ J γ i)*N i) *
        j9 (J.family.scalar γ)+Polynomial.C (dcQ J γ i)*O i:= by
      obtain ⟨_,_,h0,h1⟩:=hmarks γ (hU hγ)
      fin_cases i
      · change J.block∣(C 0+Polynomial.C z*N 0)*_+Polynomial.C z*j9 J.model.Q
        rw [← hz]
        exact h0
      · change J.block.map σ∣(C 1+Polynomial.C (z^p)*N 1)*_ +
            Polynomial.C (z^p)*(j9 J.model.Q).map σ
        rw [← hσ]
        exact h1
    have hr :=eval_eq_zero_of_dvd_of_eval_eq_zero hres (hy i)
    simp only [eval_add,eval_mul,eval_C] at hr
    change (c i+dcQ J γ i*n i)*(j9 (J.family.scalar γ)).eval (y i) +
      dcQ J γ i*o i=0 at hr
    refine ⟨target_nonzero (hinv i) (dcQ J γ i),?_⟩
    have hP:=congrArg (fun f :L[X]=>f.eval (y i)) (B.numerator_id γ hγ)
    have hQ:=congrArg (fun f :L[X]=>f.eval (y i)) (B.denominator_id γ hγ)
    simp only [eval_add,eval_mul] at hP hQ
    change (B.P γ).eval (y i)*_=(B.Q γ).eval (y i)*_
    apply mul_left_cancel₀ (hloc i (sites J γ))
    rw [← mul_assoc,← mul_assoc,hP,hQ]
    change (a₁ i*_+b₁ i)*(b₀ i*c i+(b₀ i*n i-a₀ i*o i)*dcQ J γ i) =
      (a₀ i*_+b₀ i)*(b₁ i*c i+(b₁ i*n i-a₁ i*o i)*dcQ J γ i)
    linear_combination (a₁ i*b₀ i-a₀ i*b₁ i)*hr
theorem count {J:Input} {U:zJe K} (hU:U⊆J.CF) {B:DualWord J U}
    {q:SeedPlane} {C:CurveModel q} (S:Sheet (oldWord B) C) (n v a :ℕ)
    (hn : ∀ i:I,(S.marks.filter fun γ => ¬ hit J γ i∧(S.num γ).eval (base i)≠0).card≤n)
    (hv : ∑ γ∈S.marks,poleOrderAt S γ≤v)
    (ha : (S.marks.filter fun γ=>S.num γ=0).card≤a) :
    gap J.D*S.marks.card≤blockLength*n+v+gap J.D*a := by
  let good:=S.marks.filter fun γ=>S.num γ≠0
  let bad (γ:K) :=univ.filter fun i:I => ¬ hit J γ i∧(S.num γ).eval (base i)≠0
  have each (γ:K) (hm:γ∈good) :gap J.D ≤(bad γ).card+poleOrderAt S γ:= by
    have hg:=mem_filter.mp hm
    let miss :=univ \ sites J γ
    have hcard:miss.card=blockLength-(sites J γ).card:= by
      change (univ \ sites J γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(S.num γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,mem_sites]
    have hsum:=card_filter_add_card_filter_not (s :=miss) (fun i=>(S.num γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hzero :=gR.kL.agd base base_injective
      (S.num γ) hg.2 (miss.filter (fun i => ¬ (S.num γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hB:=S.Bp hg.1
    obtain ⟨hh,hq,hp⟩:=B.degrees γ hB
    have horder :=B.order
    have hw:32768≤width J.D:=qE3Ebna.width_floor (oldInput J)
    unfold width at hw
    have hwidth :B.u₀+B.u₁+2*A=blockLength+J.D:= by
      rw [B.gMz]
      exact Nat.sub_add_cancel (by omega)
    have hD:=J.degree_hi
    have hn' : (sites J γ).card≤blockLength:= by
      simpa only [card_univ,index_card] using card_le_card (subset_univ (sites J γ))
    have hAgr :A≤(sites J γ).card:= by
      let m:=J.family.mark γ (hU hB)
      exact m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi))
    have hmax :max (B.Q γ).natDegree ((B.P γ).natDegree-(B.u₁-B.u₀)) ≤
        A+B.u₀-(sites J γ).card:=max_le hq (by omega)
    have hrel :relativeDegree (oldWord B) γ+(sites J γ).card+gap J.D ≤blockLength:= by
      simp only [relativeDegree,gap]
      change B.u₁-B.u₀+2*max (B.Q γ).natDegree ((B.P γ).natDegree-(B.u₁-B.u₀)) +
        (sites J γ).card+(A-J.D)≤blockLength
      omega
    change gap J.D ≤(bad γ).card+max (S.den γ).natDegree
      ((S.num γ).natDegree-relativeDegree (oldWord B) γ)
    omega
  have hswap : ∑ γ∈good,(bad γ).card = ∑ i:I,
      (good.filter fun γ => ¬ hit J γ i∧(S.num γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈good,(bad γ).card≤blockLength*n:= by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :zJe I))
      (f := fun _=>n) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
  have hs : ∑ γ∈good,poleOrderAt S γ≤v :=
    (sum_le_sum_of_subset (filter_subset _ _)).trans hv
  have hgood:gap J.D*good.card≤blockLength*n+v := by
    rw [z5A (gap J.D),← sum_const_nat (s :=good) (f := fun _=>gap J.D) (fun _ _=>rfl)]
    exact (sum_le_sum fun γ hm=>each γ hm).trans
      (sum_add_distrib.trans_le (z9f hb hs))
  have hp:=card_filter_add_card_filter_not (s :=S.marks) (fun γ=>S.num γ=0)
  change (S.marks.filter fun γ=>S.num γ=0).card+good.card=S.marks.card at hp
  rw [← hp,Nat.mul_add]
  exact (z9f (zBI _ ha) hgood).trans_eq (by ac_rfl)
end
end q8SCoCa
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q8SCoCa
noncomputable section
open Polynomial Finset q3u9Tnc
open P6 (K I p blockLength)
open qe6nVeb (SeedPlane gap weightOK poleRate numerator constantFee immersedMarks immersedAt)
open qE3Ebna (Prepared Starts poleOrderAt)
open Qt (gY)
open scoped Classical
open private word_budget primary_budget linear_rate node_credit sum_cover from ProximityPrize.SubmissionLower.ZrU0ida
def c1 :Prop :=qE3Ebna.c1
def c2 :Prop :=qE3Ebna.c2
def c3:Prop :=qE3Ebna.c3
private theorem count_prepared (local_test :c2) (pole :c3)
    {J:Input} {U:zJe K} {B:DualWord J U} {q:SeedPlane} {T:zJe K}
    (hU:U⊆J.CF) (R:Starts (oldWord B)) {d e W h:ℕ} (hd:d≤e) (hw:weightOK J.D e W)
    (P:Prepared (oldWord B) q T d W h) :
    gap J.D*T.card≤numerator J.D e W*h*q.totalDegree+(4*e*gap J.D*q.totalDegree)*d:= by
  let g:=gap J.D
  let bw:=blockLength*(2*e-1)+(poleRate J.D e W+(2*e-2))+g*(4*e)
  let base :=4*e*g*q.totalDegree
  let V:=univ.biUnion fun j=>(P.part j).marks
  have hV:V⊆T:= fun _ hγ=> by
    obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
    exact P.inside j hj
  have hsum : ∑ j,g*(P.part j).marks.card≤bw*(∑ j,(P.part j).h)+base*(∑ j,(P.part j).d) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    let S:=P.part j
    have hsd:S.d≤e :=((single_le_sum (fun i _=>Nat.zero_le (P.part i).d) hj).trans P.degree).trans hd
    have hp:S.d<p:=hsd.trans_lt hw.2.2.1
    have hv : ∑ γ∈S.marks,poleOrderAt S γ≤(poleRate J.D e W+(2*e-2))*S.h:= by
      by_cases h:2≤S.d
      · exact pole S e W h hsd hw (P.weight j)
      · have hd1 :S.d = 1 := by
          change ¬ 2≤S.f.natDegree at h
          change S.f.natDegree=1
          have :=S.positive
          omega
        exact (qgbTAnb.proof S W hd1 (P.weight j)).trans
          (ztf _ ((linear_rate hw).trans (Nat.le_add_right _ _)))
    have hn (i:I) :=(word_budget local_test S hp i).trans
      (ztf _ (Nat.sub_le_sub_right (zBI 2 hsd) 1))
    calc
      _≤blockLength*((2*e-1)*S.h)+(poleRate J.D e W+(2*e-2))*S.h+
          g*(4*S.d*(S.h+S.d*q.totalDegree)) :=
        count hU S _ _ _ hn hv (primary_budget local_test S hp R)
      _≤blockLength*((2*e-1)*S.h)+(poleRate J.D e W+(2*e-2))*S.h+
          g*(4*e*(S.h+S.d*q.totalDegree)) := by gcongr
      _ = _:= by dsimp only [g,bw,base,S]; ring
  have hr : (7+2*e)*g+bw≤numerator J.D e W:= by
    have he :3≤e :=hw.2.1
    have hc:=node_credit (oldInput J) hw
    have hn:blockLength*(2*e-1)+(2*e-2)≤2*e*blockLength:= calc
      _≤blockLength*(2*e-1)+blockLength:=z3b hc _
      _=2*e*blockLength:= by
        rw [← Nat.mul_succ,show (2*e-1).succ=2*e by omega,z5A]
    calc
      _=(7+6*e)*g+(blockLength*(2*e-1)+(2*e-2))+poleRate J.D e W:= by dsimp only [bw]; ring
      _≤_:=zlr (z3b hn _) _
  calc
    _=g*(T \ V).card+g*V.card:= by rw [← Nat.mul_add,card_sdiff_add_card_eq_card hV]
    _≤g*(T \ V).card + ∑ j,g*(P.part j).marks.card :=
      z3b (sum_cover _ _ (Subset.refl V)) _
    _≤g*((7+2*e)*h*q.totalDegree)+(bw*(h*q.totalDegree)+base*d) := by
      have hout:=P.zJ.trans (show (7+2*d)*h*q.totalDegree≤(7+2*e)*h*q.totalDegree by gcongr)
      exact z9f (zBI _ hout)
        (hsum.trans (z9f (zBI _ P.height) (zBI _ P.degree)))
    _=((7+2*e)*g+bw)*h*q.totalDegree+base*d:= by ring
    _≤_:=zlr (ztf _ (ztf _ hr)) _
theorem of_children (prep:c1) (local_test :c2) (pole :c3) :q3u9Tnc.c2 := by
  intro J U B T hT hU e h W hw S q hq
  obtain ⟨R⟩:=starts hU B
  let M:=immersedMarks q (dcQ J) T
  let V (j:Fin S.size) :=M.filter fun γ=>atDual B (S.sheet j) γ=0
  have hmarks {γ:K} (hγ:γ∈M) :γ∈T∧immersedAt q (dcQ J γ) :=mem_filter.mp hγ
  have hcover :M⊆univ.biUnion V:= by
    intro γ hγ
    obtain ⟨j,hj⟩:=S.roots γ (hmarks hγ).1
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨hγ,hj⟩⟩
  let b:=4*e*gap J.D*q.totalDegree
  let n:=numerator J.D e W
  have hparts : ∑ j,gap J.D*(V j).card ≤
      (n*q.totalDegree)*(∑ j,gY (Y3.embed (S.sheet j)))+b*(∑ j,(S.sheet j).natDegree) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    let F:=S.sheet j
    have hd:F.natDegree≤e :=(single_le_sum (fun i _=>Nat.zero_le (S.sheet i).natDegree) hj).trans S.ordinate_sum
    have hin {γ:K} (hγ:γ∈V j) :γ∈M∧atDual B F γ=0:=mem_filter.mp hγ
    obtain ⟨P⟩:=prep (oldWord B) q hq (V j) (fun _ hγ=>hT (hmarks (hin hγ).1).1)
      (fun _ hγ=>(hmarks (hin hγ).1).2) F W (S.irreducible j) (S.positive j)
      (hd.trans_lt hw.2.2.1) (S.weight j) (fun _ hγ=>(hin hγ).2)
    exact (count_prepared local_test pole hU R hd hw P).trans_eq (by dsimp only [b,n,F]; ring)
  calc
    _≤_:=sum_cover V _ hcover
    _≤_:=hparts
    _≤(n*q.totalDegree)*h+b*e :=
      z9f (zBI _ S.seed_sum) (zBI _ S.ordinate_sum)
    _ = _:= by dsimp only [b,n,constantFee]; ring
end
end q8SCoCa
end
section
set_option autoImplicit true
namespace q8wgled
theorem proof :q3u9Tnc.c3 :=
  q7YMR4d.of_children qYzLClc.proof qLUrYJc.proof qGzrWfb.proof
end q8wgled
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qGBd8hb
noncomputable section
open Polynomial
open cu (triangle)

open qkgz7gb (Stock)

open qbIP9ia (seedMon)


private def seedOK :Stock→(Fin 2 →₀ ℕ)→Prop
  | .symmetric n,m=>m.degree≤n
  | .asymmetric a b,m=>m 0≤a∧m 1≤b
private abbrev atZ (s :Stock) := {m:Fin 2 →₀ ℕ // seedOK s m}
private def rectEquiv (a b:ℕ) :atZ (.asymmetric a b) ≃ Fin (a+1)×Fin (b+1) where
  toFun m:=⟨⟨m.val 0,zB1 m.property.1⟩,⟨m.val 1,zB1 m.property.2⟩⟩
  invFun ab:=⟨seedMon ab.1 ab.2,by
    exact ⟨zeh ab.1.isLt,zeh ab.2.isLt⟩⟩
  left_inv m:= by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv ab:=rfl
private instance (s :Stock) :Finite (atZ s) := by
  cases s with
  | symmetric n=>exact (Finsupp.finite_of_degree_le n).to_subtype
  | asymmetric a b=>exact Finite.of_equiv _ (rectEquiv a b).symm
private theorem goP (s :Stock) :Nat.card (atZ s)=s.size := by
  cases s with
  | symmetric n =>
    change {m:Fin 2 →₀ ℕ | m.degree≤n}.ncard=triangle n
    rw [Finsupp.ncard_setOf_degree_le]
    simp [Nat.choose_two_right,triangle,z5A (n+2)]
  | asymmetric a b =>
    rw [Nat.card_congr (rectEquiv a b),Nat.card_prod,Nat.card_fin,Nat.card_fin]
    rfl
end
end qGBd8hb
end
section
set_option autoImplicit true
namespace qjaPpFd
theorem proof :qCwf1nc.c1 :=
  qt5AtZa.of_children q89PToe.proof qGBd8hb.proof
end qjaPpFd
end
section
set_option autoImplicit true
namespace qCF0LEe
theorem proof :qCwf1nc.c3:=quj0Mle.proof
end qCF0LEe
end
