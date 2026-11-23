import ProximityPrize.SubmissionLower.ZBkbQJc
import ProximityPrize.SubmissionLower.ZlPdtnc
set_option Elab.async false
namespace qxPDCsa
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open cu (L FX j9)
open qkgz7gb (PlaneCurve branchDegree)
open P5_7_3_5_2 (Sheet Variation atPolynomial)
open qb0hmCe (CurveModel cLN)
open qFD8jve (sheetPole)
open P5_7_7 (phys)
open E7 (CurvePlace poleOrder KB)
open agN (b27 a6F)
open q1kuFjb (principal zero_budget)
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
def c1 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (D W:ℕ),F.d<p→F.weight D W →
    F.f.discr≠0∧F.f.discr.natDegree≤discDegree D F.d W ∧
      Bound F F.f.discr (2*F.d-2) ∧
      ∀ γ (hγ:γ∈F.marks),UnitAt F γ F.f.discr.leadingCoeff →
        atPolynomial (specialize F hγ).derivative (S γ)≠0
def c2 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (V:Variation F) (D W:ℕ),F.weight D W →
    Nonempty (References V D W)
def c3:Prop :=
  ∀ {E :Type} [Field E] [CharP E p] (g:E[X]),g≠0→ g.natDegree<p →
    ∃ r :E[X],RadicalOf g r
def c4 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (r t:Cq.E[X]),F.d<p→t.natDegree<p →
    RadicalOf F.f.discr r →
    RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t →
    ∀ γ (hγ:γ∈V.marks),Good A γ →
      let a :=F.atPlace γ (V.Bp hγ)
      (V.den γ).natDegree≤gcdDegree (reduce a r) (reduce a r.derivative) +
        2*(contentAt F (V.Bp hγ)).natDegree
def c5:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ} (A:References V D W),
    F.d<p→F.weight D W → ∀ γ∈V.marks,Good A γ →
    (S γ).natDegree≤D→(V.num γ).natDegree≤D+(V.den γ).natDegree
def c6:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (u v :Cq.E[X]),u.resultant v≠0 →
    ∀ γ (hγ:γ∈F.marks),BoundedAt (F.place γ).value u 1 →
      BoundedAt (F.place γ).value v 1 →
      gcdDegree (reduce (F.atPlace γ hγ) u) (reduce (F.atPlace γ hγ) v) ≤
        KB (F.place γ).value (u.resultant v)
def c7:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (D W:ℕ),F.weight D W →
    ∃ u v :Cq.E[X],u.resultant v≠0∧u.natDegree≤W∧v.natDegree≤W ∧
      Bound F u 1∧Bound F v 1 ∧ ∀ γ (hγ:γ∈F.marks),
        let a :=F.atPlace γ hγ
        let g:=GCDMonoid.gcd (reduce a u) (reduce a v)
        g≠0∧contentAt F hγ∣g
private theorem height_zero {F:Sheet Cq z S} {γ:K} (hγ:γ∈F.marks) :
   sheetPole (F.place γ).value F.f=0 :=
 (Finset.sup_eq_bot_iff _ _).mpr fun i _ =>
   (a6F _ _).mpr (F.integral γ hγ i.1 i.2)
private theorem bound_at {F:Sheet Cq z S} {g:Cq.E[X]} {n:ℕ} (h:Bound F g n)
  {γ:K} (hγ:γ∈F.marks) :BoundedAt (F.place γ).value g 1 := by
 simpa only [height_zero hγ,Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero] using h (F.place γ)
private theorem pole_sum (F:Sheet Cq z S) {c:Cq.E} (hc:c≠0) {n:ℕ}
  (h : ∀ w:CurvePlace L Cq.E,w.value c≤WithZero.exp ((n*sheetPole w.value F.f :ℕ) :ℤ)) :
  (∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value c)≤n*F.h:= by
 let P (w:CurvePlace L Cq.E) :=sheetPole w.value F.f
 have hf :P.HasFiniteSupport:=b27 (principal Cq) _
 change _≤n * ∑ᶠ w,P w
 rw [mul_finsum]
 apply finsum_le_finsum (principal Cq c).1
  (hf.subset fun w hw hz=>hw (by change n*P w=0; rw [hz,mul_zero]))
 intro w
 exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr hc)).mpr (h w))
private theorem guard_count (F:Sheet Cq z S) {g:Cq.E[X]} {j n:ℕ}
  (hc:g.coeff j≠0) (hg:Bound F g n) :
  (F.marks.filter fun γ => ¬ UnitAt F γ (g.coeff j)).card≤n*F.h:= by
 have hsub: (F.marks.filter fun γ => ¬ UnitAt F γ (g.coeff j)) ⊆
    F.marks.filter (fun γ=>(F.place γ).value (g.coeff j)<1) := by
  intro γ hγ
  obtain ⟨hm,hn⟩:=mem_filter.mp hγ
  exact mem_filter.mpr ⟨hm,lt_of_le_of_ne (bound_at hg hm j) hn⟩
 exact (card_le_card hsub).trans ((zero_budget F.marks F.place F.distinct hc).trans
  (pole_sum F hc (fun w=>hg w j)))
private theorem reduced_pair (n d:L[X]) (hd:d≠0) :
  ∃ a b:L[X],b≠0∧IsCoprime a b∧phys a/phys b=phys n/phys d:= by
 let g:=GCDMonoid.gcd n d
 have hg:g≠0:=gcd_ne_zero_of_right hd
 refine ⟨n/g,d/g,right_div_gcd_ne_zero hd,isCoprime_div_gcd_div_gcd hd,?_⟩
 rw [← mul_div_mul_left _ _ ((map_ne_zero_iff phys (IsFractionRing.injective L[X] FX)).mpr hg),
  ← map_mul,← map_mul,EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left n d),
  EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right n d)]
private theorem choose_variation (F:Sheet Cq z S)
    (h : ∀ γ (hγ:γ∈F.marks),UnitAt F γ F.f.discr.leadingCoeff →
      atPolynomial (specialize F hγ).derivative (S γ)≠0) :
    ∃ V:Variation F,V.marks=F.marks.filter (fun γ=>UnitAt F γ F.f.discr.leadingCoeff) := by
  let T:=F.marks.filter (fun γ=>UnitAt F γ F.f.discr.leadingCoeff)
  have hk :T⊆F.marks :=filter_subset _ _
  have hs (γ:K) (hγ:γ∈T) :=h γ (hk hγ) (mem_filter.mp hγ).2
  have hex (γ:K) : ∃ a b:L[X],∀ hγ:γ∈T,
      b≠0∧IsCoprime a b ∧
        phys a/phys b =
          -(atPolynomial (cLN (F.atPlace γ (hk hγ)) 1 F.f) (S γ) /
            atPolynomial (specialize F (hk hγ)).derivative (S γ)) := by
    by_cases hγ:γ∈T
    · let n := -((cLN (F.atPlace γ (hk hγ)) 1 F.f).eval (j9 (S γ)))
      let d:=(specialize F (hk hγ)).derivative.eval (j9 (S γ))
      have he (g:L[X][X]) :phys (g.eval (j9 (S γ)))=atPolynomial g (S γ) :=
        (eval₂_hom (p:=g) phys (j9 (S γ))).symm
      have hd:d≠0:= fun hz=>hs γ hγ (by
        rw [← he]
        change phys d=0
        rw [hz,map_zero])
      obtain ⟨a,b,hb,hcop,hab⟩:=reduced_pair n d hd
      refine ⟨a,b,fun _=>⟨hb,hcop,hab.trans ?_⟩⟩
      simp only [n,d,map_neg,neg_div,he]
    · exact ⟨0,1,fun h' => (hγ h').elim⟩
  choose a b hab using hex
  exact ⟨⟨T,hk,a,b,fun γ hγ=>(hab γ hγ).1,fun γ hγ=>(hab γ hγ).2.1,
    hs,fun γ hγ=>(hab γ hγ).2.2⟩,rfl⟩
private def restrict {F:Sheet Cq z S} (V:Variation F) {T:Finset K}
   (h:T⊆V.marks) :Variation F :=
 ⟨T,h.trans V.Bp,V.num,V.den,fun γ hγ=>V.den_ne γ (h hγ),
   fun γ hγ=>V.reduced γ (h hγ),fun γ hγ=>V.simple γ (h hγ),
   fun γ hγ=>V.formula γ (h hγ)⟩
private theorem zJ {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (hδ:F.f.discr≠0) (hb:Bound F F.f.discr (2*F.d-2)) :
    (F.marks \ F.marks.filter (Good A)).card≤(2*F.d-2+4)*F.h:= by
  let bad (c:Cq.E) :=F.marks.filter fun γ => ¬ UnitAt F γ c
  let B:=bad F.f.discr.leadingCoeff
  let f (i:Fin 2) :=bad (finiteRef F (A.a i)).leadingCoeff
  let g (i:Fin 2) :=bad ((infinityRef F D (A.b i)).coeff 0)
  have hs :F.marks \ F.marks.filter (Good A)⊆B∪((f 0∪f 1)∪(g 0∪g 1)) := by
    intro γ hγ
    obtain ⟨hm,hn⟩:=mem_sdiff.mp hγ
    by_contra he
    simp only [mem_union,not_or,B,f,g,bad,mem_filter,hm,true_and,not_not] at he
    exact hn (mem_filter.mpr ⟨hm,he.1,
      (fun i=> by fin_cases i; exacts [he.2.1.1,he.2.1.2]),
      (fun i=> by fin_cases i; exacts [he.2.2.1,he.2.2.2])⟩)
  have hB:B.card≤(2*F.d-2)*F.h :=
    guard_count F (leadingCoeff_ne_zero.mpr hδ) hb
  have hf (i:Fin 2) : (f i).card≤1*F.h :=
    guard_count F (leadingCoeff_ne_zero.mpr (A.finite_ne i)) (A.finite_bound i)
  have hg (i:Fin 2) : (g i).card≤1*F.h :=
    guard_count F (A.infinity_ne i) (A.infinity_bound i)
  calc
    _≤B.card+(((f 0).card+(f 1).card)+((g 0).card+(g 1).card)) :=
      (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left
        ((card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) (card_union_le _ _))) _))
    _≤(2*F.d-2)*F.h+((1*F.h+1*F.h)+(1*F.h+1*F.h)) :=
      Nat.add_le_add hB (Nat.add_le_add (Nat.add_le_add (hf 0) (hf 1)) (Nat.add_le_add (hg 0) (hg 1)))
    _ = _:= by ring
private theorem derivative_bound {F:Sheet Cq z S} {g:Cq.E[X]} {n:ℕ}
  (h:Bound F g n) :Bound F g.derivative n:= by
 intro w j
 have hn (i:ℕ) :w.value (i:Cq.E)≤1 := by
  induction i with
  | zero=>simp
  | succ i hi=>rw [Nat.cast_succ]; exact w.value.map_add_le hi (by simp)
 rw [coeff_derivative,map_mul,← Nat.cast_succ]
 exact (mul_le_mul' (h w (j+1)) (hn _)).trans_eq (mul_one _)
private theorem cfo {F:Sheet Cq z S} {u v :Cq.E[X]} {a b:ℕ}
   (hu:Bound F u a) (hv :Bound F v b) (w:CurvePlace L Cq.E) :
   w.value (u.resultant v) ≤
     WithZero.exp (((u.natDegree*b+v.natDegree*a)*sheetPole w.value F.f :ℕ) :ℤ) := by
 classical
 let m:=u.natDegree
 let n:=v.natDegree
 let M:=sylvester u v m n
 let c:=WithZero.exp (sheetPole w.value F.f :ℤ)
 let cost:Fin (m+n)→ℕ:= fun j=>Fin.addCases (fun _=>b) (fun _=>a) j
 have hb (j:ℕ) :c^j=WithZero.exp ((j*sheetPole w.value F.f :ℕ) :ℤ) := by
   simp [c,← WithZero.exp_nsmul]
 have hentry (i j:Fin (m+n)) :w.value (M i j)≤ c^(cost j) := by
   refine Fin.addCases ?_ ?_ j
   · intro k
     simp only [M,cost,hb,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · exact hv w _
     · simp
   · intro k
     simp only [M,cost,hb,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · exact hu w _
     · simp
 have hsum: (∑ i,cost i)=m*b+n*a := by
   rw [Fin.sum_univ_add]
   simp [cost]
 rw [← hb (m*b+n*a),← hsum,← prod_pow_eq_pow_sum]
 change w.value M.det≤_
 rw [Matrix.det_apply]
 apply w.value.map_sum_le
 intro π _
 have he :w.value (∏ i,M (π i) i) ≤ ∏ i,c^(cost i) := by
   rw [map_prod]
   exact prod_le_prod fun i _=>hentry (π i) i
 rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;>
   simpa [hh,Valuation.map_neg] using he
private def markGcd (F:Sheet Cq z S) (u v :Cq.E[X]) (γ:K) :ℕ :=
 if hγ:γ∈F.marks then gcdDegree (reduce (F.atPlace γ hγ) u) (reduce (F.atPlace γ hγ) v) else 0
private def markContent (F:Sheet Cq z S) (γ:K) :ℕ :=
 if hγ:γ∈F.marks then (contentAt F hγ).natDegree else 0
private theorem resultant_budget (exL:c6) (F:Sheet Cq z S)
   {T:Finset K} (hT:T⊆F.marks) {u v :Cq.E[X]} {a b:ℕ}
   (h:u.resultant v≠0) (hu:Bound F u a) (hv :Bound F v b) :
   ∑ γ∈T,markGcd F u v γ≤(u.natDegree*b+v.natDegree*a)*F.h:= by
 let g:=u.resultant v
 let Ju (w:CurvePlace L Cq.E) :=KB w.value g
 have hf :=(principal Cq g).2.1
 have hdir :=(principal Cq g).2.2.1
 calc
   _ ≤ ∑ γ∈T,Ju (F.place γ) :=sum_le_sum fun γ hγ=> by
     rw [markGcd,dite_eq_left (hT hγ)]
     exact exL F u v h γ (hT hγ) (bound_at hu (hT hγ)) (bound_at hv (hT hγ))
   _ = ∑ w∈T.image F.place,Ju w:= by rw [sum_image (F.distinct.mono hT)]
   _ ≤ ∑ w∈hf.toFinset∪T.image F.place,Ju w :=
     sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _=>Nat.zero_le _
   _ = ∑ᶠ w,Ju w:=(finsum_eq_finsetSum_of_support_subset Ju
     (s :=hf.toFinset∪T.image F.place) (fun w hw=>mem_union_left _ (hf.mem_toFinset.mpr hw))).symm
   _ = ∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value g:=hdir.symm
   _≤_:=pole_sum F h (cfo hu hv)
private theorem disc_degree_mono {d e D W:ℕ} (hd:0<d) (hde :d≤e) (hw:e*D ≤W) :
  discDegree D d W≤discDegree D e W:= by
 have he :0<e :=hd.trans_le hde
 have hmul :=Nat.mul_le_mul_right D hde
 have hs (j:ℕ) (hj:0<j) (hW:j*D ≤W) :
    j*(j-1)*D ≤(2*j-2)*W:= calc
  _=(j-1)*(j*D) := by ring
  _≤(2*j-2)*W:=Nat.mul_le_mul (by omega) hW
 have hd₁:1≤d:=hd
 have he₁:1≤e :=he
 have hd₂:2≤2*d:= by omega
 have he₂:2≤2*e := by omega
 unfold discDegree
 zify [hs d hd (hmul.trans hw),hs e he hw,hd₁,he₁,hd₂,he₂] at hde hw hmul ⊢
 have hD:0≤(D:ℤ) :=Int.natCast_nonneg _
 have hb:0≤2*(W:ℤ)-((e :ℤ)+d-1)*D:= by linarith
 nlinarith only [mul_nonneg (sub_nonneg.mpr hde) hb]
theorem of_children (disc:c1) (refs :c2) (rad:c3) (finite :c4)
    (infty :c5) (order :c6) (content:c7) :P5_7_3_5_2.c4 := by
  intro q Cq z S F D e W v₁ v₂ ok hde hW hS
  obtain ⟨_,_,_,hp,hEW,hchar⟩:=ok
  let m:=branchDegree D e W (.asymmetric v₁ v₂)
  have hd:F.d<p:=hde.trans_lt hp
  have hm:m+2*W<p:=hchar
  obtain ⟨hδ,hδd,hδb,hsimple⟩:=disc F D W hd hW
  have hδm:F.f.discr.natDegree≤ m :=
    hδd.trans (disc_degree_mono F.positive hde hEW)
  obtain ⟨V,hV⟩:=choose_variation F hsimple
  obtain ⟨A⟩:=refs V D W hW
  let T:=F.marks.filter (Good A)
  have hT:T⊆F.marks :=filter_subset _ _
  have ht:T⊆V.marks := by
    rw [hV]
    exact fun γ hγ=>mem_filter.mpr ⟨hT hγ,(mem_filter.mp hγ).2.1⟩
  let U:=restrict V ht
  let g:=F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)
  have hg:g≠0:=mul_ne_zero (mul_ne_zero hδ (A.finite_ne 0)) (A.finite_ne 1)
  have hgp:g.natDegree<p:= by
    apply lt_of_le_of_lt _ hm
    have h:=(natDegree_mul_le (p:=F.f.discr*finiteRef F (A.a 0))
      (q:=finiteRef F (A.a 1))).trans (Nat.add_le_add_right natDegree_mul_le _)
    exact h.trans (by simpa only [two_mul,add_assoc] using
      (Nat.add_le_add (Nat.add_le_add hδm (A.finite_degree 0)) (A.finite_degree 1)))
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP Cq.E p:=charP_of_injective_ringHom (algebraMap L Cq.E).injective p
  obtain ⟨r,hr⟩:=rad F.f.discr hδ (hδm.trans_lt (by omega))
  obtain ⟨t,hrad⟩:=rad g hg hgp
  have htp:t.natDegree<p:=(natDegree_le_of_dvd hrad.dvd hg).trans_lt hgp
  have hrb:Bound F r (2*F.d-2) := fun w=>hr.bound _ _ (hδb w)
  have hrm:r.natDegree≤ m:=(natDegree_le_of_dvd hr.dvd hδ).trans hδm
  have hbranch : ∑ γ∈T,markGcd F r r.derivative γ≤((2*e-2)*(2*m-1))*F.h:= by
    refine (resultant_budget order F hT (resultant_ne_zero _ _ hr.separable) hrb
      (derivative_bound hrb)).trans (Nat.mul_le_mul_right _ ?_)
    rw [← add_mul,Nat.mul_comm (2*e-2)]
    exact Nat.mul_le_mul (by have :=natDegree_derivative_le r; omega) (by omega)
  obtain ⟨a,b,hab,ha,hb,ha',hb',hc⟩:=content F D W hW
  have hcontent : ∑ γ∈T,markContent F γ≤(2*W)*F.h:= calc
    _ ≤ ∑ γ∈T,markGcd F a b γ:=sum_le_sum fun γ hγ=> by
      simp only [markContent,markGcd,dite_eq_left (hT hγ)]
      exact natDegree_le_of_dvd (hc γ (hT hγ)).2 (hc γ (hT hγ)).1
    _≤(a.natDegree*1+b.natDegree*1)*F.h:=resultant_budget order F hT hab ha' hb'
    _≤_:=Nat.mul_le_mul_right _ (by omega)
  refine ⟨U,(zJ A hδ hδb).trans (Nat.mul_le_mul_right _ (by omega)),?_⟩
  calc
    _ ≤ ∑ γ∈T,(markGcd F r r.derivative γ+2*markContent F γ) := by
      apply sum_le_sum
      intro γ hγ
      have hgood:=(mem_filter.mp hγ).2
      have hi:=infty A hd hW γ (ht hγ) hgood (hS γ (hT hγ))
      have hf :=finite A r t hd htp hr hrad γ (ht hγ) hgood
      change max (V.den γ).natDegree ((V.num γ).natDegree-D)≤_
      simp only [max_eq_left (by omega : (V.num γ).natDegree-D ≤(V.den γ).natDegree),
        markGcd,markContent,dite_eq_left (hT hγ)]
      exact hf
    _=(∑ γ∈T,markGcd F r r.derivative γ)+2*∑ γ∈T,markContent F γ:= by
      rw [sum_add_distrib,mul_sum]
    _≤((2*e-2)*(2*m-1))*F.h+2*((2*W)*F.h) :=
      Nat.add_le_add hbranch (Nat.mul_le_mul_left _ hcontent)
    _ = _:= by change _=((2*e-2)*(2*m-1)+4*W)*F.h; ring
end
end qxPDCsa
