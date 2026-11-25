import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic

set_option Elab.async false

-- merged module R6966ProofPadeClassification
section Merged_R6966ProofPadeClassification

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K : Type*} [Field K]

/-- The graph equation is a(Y)V=b(Y). -/
structure Row (K : Type*) [Semiring K] where
  a : K[X]
  b : K[X]

def Row.fits (F : Row K) (d : ℕ) : Prop :=
  (∀ j, d≤j → F.a.coeff j=0) ∧ (∀ j, d<j → F.b.coeff j=0)

def Row.err (F : Row K) (v : K→K) (x : K) := F.a.eval x * v x - F.b.eval x
def Row.det (F G : Row K) := F.a*G.b-G.a*F.b
def nodes (s : Finset K) : K[X] := ∏ y∈s,(X-C y)

/-- Divide-and-cancel interpolation. The two shifted degree caps always
sum to one plus the number of processed ordinates. -/
structure Frame (s : Finset K) (v : K→K) where
  left : Row K
  right : Row K
  l : ℕ
  r : ℕ
  lfit : left.fits l
  rfit : right.fits r
  total : l+r=s.card+1
  lhit : ∀ y∈s,left.err v y=0
  rhit : ∀ y∈s,right.err v y=0
  scalar : K
  scalar_ne : scalar≠0
  det_eq : left.det right=C scalar*nodes s

private def Frame.swap {s : Finset K} {v : K→K} (F : Frame s v) : Frame s v where
  left := F.right
  right := F.left
  l := F.r
  r := F.l
  lfit := F.rfit
  rfit := F.lfit
  total := (Nat.add_comm ..).trans F.total
  lhit := F.rhit
  rhit := F.lhit
  scalar := -F.scalar
  scalar_ne := neg_ne_zero.mpr F.scalar_ne
  det_eq := by
    rw [map_neg,neg_mul,← F.det_eq]
    unfold Row.det;ring

private def shift (F : Row K) (x : K) : Row K :=
  ⟨(X-C x)*F.a,(X-C x)*F.b⟩
private def cancel (F G : Row K) (t : K) : Row K :=
  ⟨G.a-C t*F.a,G.b-C t*F.b⟩

private theorem shift_fit {F : Row K} {d : ℕ} (hf : F.fits d) (x : K) :
    (shift F x).fits (d+1) := by
  constructor
  · rintro (_|j) hj
    · omega
    · simp only [shift,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,hf.1 j (by omega),
        hf.1 (j+1) (by omega),mul_zero,sub_zero]
  · rintro (_|j) hj
    · omega
    · simp only [shift,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,hf.2 j (by omega),
        hf.2 (j+1) (by omega),mul_zero,sub_zero]

private theorem cancel_fit {F G : Row K} {d e : ℕ} (hf : F.fits d) (hg : G.fits e)
    (t : K) (ok : d≤e ∨ t=0) : (cancel F G t).fits e := by
  rcases ok with le|rfl
  · constructor
    · intro j h
      simp [cancel,coeff_C_mul,hg.1 j h,hf.1 j (by omega)]
    · intro j h
      simp [cancel,coeff_C_mul,hg.2 j h,hf.2 j (by omega)]
  · simpa [Row.fits,cancel] using hg

private theorem shift_err (F : Row K) (v : K→K) (x y : K) :
    (shift F x).err v y=(y-x)*F.err v y := by
  simp [Row.err,shift];ring
private theorem cancel_err (F G : Row K) (t : K) (v : K→K) (y : K) :
    (cancel F G t).err v y=G.err v y-t*F.err v y := by
  simp [Row.err,cancel];ring

private theorem eval_nodes_ne {s : Finset K} {x : K} (hx : x∉s) : (nodes s).eval x≠0 := by
  classical
  simpa only [nodes,eval_prod,eval_sub,eval_X,eval_C] using
    (prod_ne_zero_iff.mpr (fun y hy=>sub_ne_zero.mpr (fun eq : x=y=>hx (eq ▸ hy))) :
      ∏ y∈s,(x-y)≠0)

private def Frame.step [DecidableEq K] {s : Finset K} {v : K→K}
    (F : Frame s v) (x : K) (fresh : x∉s) (active : F.left.err v x≠0)
    (cheap : F.l≤F.r ∨ F.right.err v x=0) : Frame (insert x s) v := by
  let t:=F.right.err v x/F.left.err v x
  refine ⟨shift F.left x,cancel F.left F.right t,F.l+1,F.r,shift_fit F.lfit x,
    cancel_fit F.lfit F.rfit _ (cheap.imp_right (by intro z;simp [t,z])),?_,?_,?_,
    F.scalar,F.scalar_ne,?_⟩
  · rw [card_insert_of_notMem fresh];have := F.total;omega
  · intro y hy
    rw [shift_err]
    rcases mem_insert.mp hy with rfl|mem
    · simp
    · simp [F.lhit _ mem]
  · intro y hy
    rw [cancel_err]
    rcases mem_insert.mp hy with rfl|mem
    · simp [t,active]
    · simp [F.lhit _ mem,F.rhit _ mem]
  · rw [show nodes (insert x s)=(X-C x)*nodes s by simp [nodes,fresh]]
    calc
      _=(X-C x)*F.left.det F.right := by simp only [shift,cancel,Row.det];ring
      _=_ := by rw [F.det_eq];ring

/-- Two actual slope-linear interpolation rows for every finite set of
distinct ordinates. Their determinant has exactly those simple roots. -/
theorem frame_exists (s : Finset K) (v : K→K) : Nonempty (Frame s v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⟨⟨1,0⟩,⟨0,1⟩,1,0,?_,?_,by simp,by simp,by simp,1,one_ne_zero,?_⟩⟩
    · constructor
      · intro j hj;simp [coeff_one,show j≠0 by omega]
      · simp
    · constructor
      · simp
      · intro j hj;simp [coeff_one,show j≠0 by omega]
    · simp [Row.det,nodes]
  | insert x s fresh ih =>
    obtain ⟨F⟩:=ih
    have some_active : F.left.err v x≠0 ∨ F.right.err v x≠0 := by
      by_contra! both
      have eq := congrArg (eval x) F.det_eq
      have le := sub_eq_zero.mp both.1
      have ri := sub_eq_zero.mp both.2
      change F.left.a.eval x*v x=F.left.b.eval x at le
      change F.right.a.eval x*v x=F.right.b.eval x at ri
      simp only [Row.det,eval_sub,eval_mul,eval_C,←le,←ri] at eq
      have impossible:=mul_ne_zero F.scalar_ne (eval_nodes_ne fresh)
      apply impossible
      rw [←eq];ring
    by_cases l : F.left.err v x=0
    · exact ⟨F.swap.step x fresh (some_active.resolve_left (not_not.mpr l)) (Or.inr l)⟩
    by_cases r : F.right.err v x=0
    · exact ⟨F.step x fresh l (Or.inr r)⟩
    by_cases cmp : F.l≤F.r
    · exact ⟨F.step x fresh l (Or.inl cmp)⟩
    · exact ⟨F.swap.step x fresh r (Or.inl (Nat.le_of_not_ge cmp))⟩

#print axioms frame_exists

def Row.graphDegree (F : Row K) := max (F.a.natDegree+1) F.b.natDegree
def Row.primitive (F : Row K) : Prop := F.a≠0 ∧ IsCoprime F.a F.b

private theorem fits_degree {F : Row K} {d : ℕ} (fit : F.fits d) (nz : F.a≠0) :
    F.graphDegree ≤ d := by
  apply max_le
  · by_contra! above
    have z := fit.1 F.a.natDegree (by omega)
    rw [coeff_natDegree] at z
    exact leadingCoeff_ne_zero.mpr nz z
  · exact natDegree_le_iff_coeff_eq_zero.mpr fit.2

private theorem nodes_ne (s : Finset K) : nodes s ≠ 0 := by
  classical
  exact prod_ne_zero_iff.mpr (fun y _=>X_sub_C_ne_zero y)

private theorem nodes_degree (s : Finset K) : (nodes s).natDegree=s.card := by
  classical
  unfold nodes
  rw [natDegree_prod s (fun x=>X-C x) (fun x _=>X_sub_C_ne_zero x)]
  simp

private theorem zero_count [DecidableEq K] (s : Finset K) (p : K[X]) (nz : p≠0) :
    (s.filter (fun x=>p.eval x=0)).card ≤ p.natDegree := by
  classical
  have sub : s.filter (fun x=>p.eval x=0) ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (mem_filter.mp hx).2)
  exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))

private theorem Frame.left_active {s : Finset K} {v : K→K} (F : Frame s v)
    (lt : F.l<s.card) : F.left.a≠0 := by
  classical
  intro az
  have hits (x) (hx:x∈s) : F.left.b.eval x=0 := by
    simpa [Row.err,az] using F.lhit x hx
  have bz : F.left.b=0 := by
    by_contra nz
    have count := zero_count s _ nz
    rw [filter_eq_self.mpr hits] at count
    have := natDegree_le_iff_coeff_eq_zero.mpr F.lfit.2
    omega
  have nd := mul_ne_zero (C_ne_zero.mpr F.scalar_ne) (nodes_ne s)
  rw [←F.det_eq] at nd
  simp [Row.det,az,bz] at nd

/-- Removing the vertical content loses at most one ordinate per unit of its degree. -/
theorem primitive_part [DecidableEq K] (F : Row K) (v : K→K) (s : Finset K)
    (nz : F.a≠0) (hits : ∀ x∈s,F.err v x=0) :
    ∃ (G : Row K) (t : Finset K), G.primitive ∧ t⊆s ∧
      s.card + G.graphDegree ≤ t.card + F.graphDegree ∧ ∀ x∈t,G.err v x=0 := by
  classical
  let g:=gcd F.a F.b
  have gn : g≠0 := gcd_ne_zero_of_left nz
  let G : Row K := ⟨F.a/g,F.b/g⟩
  have aa : g*G.a=F.a := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_left ..)
  have bb : g*G.b=F.b := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_right ..)
  have ga : G.a≠0 := by intro h;apply nz;rw [←aa,h,mul_zero]
  have adeg := natDegree_mul gn ga
  rw [aa] at adeg
  have bound : g.natDegree+G.graphDegree ≤ F.graphDegree := by
    by_cases zero : G.b=0
    · unfold Row.graphDegree
      rw [zero,natDegree_zero]
      omega
    · have deg := natDegree_mul gn zero
      rw [bb] at deg
      unfold Row.graphDegree
      omega
  let t:=s.filter (fun x=>g.eval x≠0)
  refine ⟨G,t,⟨ga,isCoprime_div_gcd_div_gcd_of_gcd_ne_zero gn⟩,filter_subset _ _,?_,?_⟩
  · have split:=s.card_filter_add_card_filter_not (fun x=>g.eval x=0)
    have loss:=zero_count s g gn
    dsimp [t]
    omega
  · intro x hx
    obtain ⟨xs,active⟩:=mem_filter.mp hx
    have eq:=hits x xs
    unfold Row.err at eq ⊢
    rw [←aa,←bb,eval_mul,eval_mul,mul_assoc,←mul_sub] at eq
    exact (mul_eq_zero.mp eq).resolve_left active

private theorem Frame.slope_pair {s : Finset K} {v : K→K} (F : Frame s v)
    {x : K} (hx : x∈s) : F.left.a.eval x ≠ 0 ∨ F.right.a.eval x ≠ 0 := by
  classical
  by_contra! both
  have lb : F.left.b.eval x=0 := by simpa [Row.err,both.1] using F.lhit x hx
  have rb : F.right.b.eval x=0 := by simpa [Row.err,both.2] using F.rhit x hx
  have rem : nodes s=nodes (s.erase x)*(X-C x) :=
    (s.prod_erase_mul (fun y=>(X-C y : K[X])) hx).symm
  have identity:=congrArg (fun p:K[X]=>p.derivative.eval x) F.det_eq
  simp [Row.det,rem,derivative_mul,derivative_sub,both.1,both.2,lb,rb,
    F.scalar_ne,eval_nodes_ne (notMem_erase x s)] at identity

private theorem coprime_at {p : K[X]} {x:K} (h:p.eval x≠0) : IsCoprime p (X-C x) := by
  have div : X-C x ∣ p-C (p.eval x) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
  obtain ⟨d,hd⟩ := div
  refine ⟨C (p.eval x)⁻¹,-C (p.eval x)⁻¹*d,?_⟩
  have inv : C (p.eval x)⁻¹*C (p.eval x)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ h,C_1]
  linear_combination C (p.eval x)⁻¹*hd + inv

private theorem det_bound (F G : Row K) : (F.det G).natDegree+1 ≤ F.graphDegree+G.graphDegree := by
  have h:=natDegree_sub_le (F.a*G.b) (G.a*F.b)
  have h₁:=natDegree_mul_le (p:=F.a) (q:=G.b)
  have h₂:=natDegree_mul_le (p:=G.a) (q:=F.b)
  unfold Row.graphDegree Row.det at *
  omega

/-- An independent interpolation row gives a primitive full-point graph of
the complementary degree, even when both shifted degrees coincide. -/
theorem Frame.full_graph [Infinite K] {s : Finset K} {v : K→K} (F : Frame s v)
    (ordered : F.l≤F.r) (short : F.l<s.card) :
    ∃ G : Row K,G.primitive ∧ G.graphDegree=F.r ∧ ∀x∈s,G.err v x=0 := by
  classical
  let rejected:=s.image (fun x=>F.right.a.eval x/F.left.a.eval x)
  obtain ⟨t,ok⟩:=rejected.exists_notMem
  let G:=cancel F.left F.right t
  have nz (x) (hx:x∈s) : G.a.eval x≠0 := by
    change (F.right.a-C t*F.left.a).eval x≠0
    simp only [eval_sub,eval_mul,eval_C,sub_ne_zero]
    intro eq
    by_cases z:F.left.a.eval x=0
    · have r := (F.slope_pair hx).resolve_left (not_not.mpr z)
      exact r (by rw [eq,z,mul_zero])
    · apply ok
      apply mem_image.mpr
      exact ⟨x,hx,(div_eq_iff z).mpr eq⟩
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<s.card by omega)
  have gn : G.a≠0 := fun z=>nz x hx (by rw [z,eval_zero])
  have det : F.left.det G=F.left.det F.right := by dsimp [G,cancel,Row.det];ring
  have dc := det.trans F.det_eq
  have left := F.left_active short
  have exactD : (F.left.det G).natDegree=s.card := by rw [dc,natDegree_C_mul F.scalar_ne,nodes_degree]
  have size:=det_bound F.left G
  have large:G.graphDegree≤F.r:=fits_degree (cancel_fit F.lfit F.rfit t (Or.inl ordered)) gn
  have little:=fits_degree F.lfit left
  have pair:=F.total
  rw [exactD] at size
  refine ⟨G,⟨gn,?_⟩,by omega,?_⟩
  · have cp : IsCoprime G.a (nodes s) := IsCoprime.prod_right (fun y h=>coprime_at (nz y h))
    obtain ⟨u,w,bz⟩ := cp
    let inv : K[X] := C F.scalar⁻¹
    have unit : inv*C F.scalar=(1:K[X]) := by dsimp [inv];rw [←C_mul,inv_mul_cancel₀ F.scalar_ne,C_1]
    have nd : nodes s=inv*F.left.det G := by rw [dc,←mul_assoc,unit,one_mul]
    rw [nd] at bz
    refine ⟨u-w*inv*F.left.b,w*inv*F.left.a,?_⟩
    unfold Row.det at bz
    linear_combination bz
  · intro y hy
    rw [show G=cancel F.left F.right t from rfl,cancel_err,F.rhit y hy,F.lhit y hy]
    ring

/-- The qualitative alternatives tested by the terminal-grade receipts. -/
theorem interpolation_alternatives [Infinite K] (s : Finset K) (v : K→K) (enough : 2≤s.card) :
    ∃ l : ℕ, 1≤l ∧ l≤(s.card+1)/2 ∧
      (∃ (G : Row K) (t : Finset K), G.primitive ∧ t⊆s ∧
        G.graphDegree≤l ∧ s.card+G.graphDegree≤t.card+l ∧ ∀ x∈t,G.err v x=0) ∧
      (∃ G : Row K,G.primitive ∧ G.graphDegree=s.card+1-l ∧ ∀x∈s,G.err v x=0) := by
  classical
  obtain ⟨F₀⟩:=frame_exists s v
  obtain ⟨F,sorted⟩ : ∃ F:Frame s v,F.l≤F.r := by
    by_cases h:F₀.l≤F₀.r
    · exact ⟨F₀,h⟩
    · exact ⟨F₀.swap,Nat.le_of_not_ge h⟩
  have total:=F.total
  have short:F.l<s.card:=by omega
  have nz:=F.left_active short
  have cap:=fits_degree F.lfit nz
  have pos:1≤F.left.graphDegree := (Nat.succ_le_succ (Nat.zero_le _)).trans (le_max_left ..)
  obtain ⟨G,t,prim,sub,kept,hits⟩ := primitive_part F.left v s nz F.lhit
  have ct:=card_le_card sub
  refine ⟨F.l,by omega,by omega,⟨G,t,prim,sub,by omega,by omega,hits⟩,?_⟩
  simpa only [show s.card+1-F.l=F.r by omega] using F.full_graph sorted short

#print axioms interpolation_alternatives
end
end Research6966.Pade

end Merged_R6966ProofPadeClassification

-- merged module R6966ProofPadeCoverage
section Merged_R6966ProofPadeCoverage

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def Row.scale (F : Row K) (c:K) : Row K := ⟨C c*F.a,C c*F.b⟩

theorem Row.err_scale (F:Row K) (c:K) (v:K→K) (x:K) :
    (F.scale c).err v x=c*F.err v x := by simp [Row.scale,Row.err];ring

theorem Row.degree_scale (F : Row K) {c:K} (nz:c≠0) :
    (F.scale c).graphDegree=F.graphDegree := by simp [Row.graphDegree,Row.scale,natDegree_C_mul nz]

theorem scale_of_det_zero {F G : Row K} (f:F.primitive) (g:G.primitive)
    (d:F.det G=0) : ∃ t : K,t≠0 ∧ G=F.scale t := by
  classical
  have eq : F.a*G.b=G.a*F.b := sub_eq_zero.mp d
  have fg : F.a∣G.a := f.2.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right ..)
  have gf : G.a∣F.a := g.2.dvd_of_dvd_mul_right (eq.symm ▸ dvd_mul_right ..)
  obtain ⟨p,hp⟩:=fg
  have pn : p≠0 := right_ne_zero_of_mul (hp ▸ g.1)
  have sz:=natDegree_le_of_dvd gf f.1
  rw [hp,natDegree_mul f.1 pn] at sz
  have cp:=eq_C_of_natDegree_eq_zero (show p.natDegree=0 by omega)
  have nz:p.coeff 0 ≠ 0 := by intro h;apply pn;rw [cp,h,C_0]
  let c:=p.coeff 0
  have aeq:G.a=C c*F.a := by rw [hp,mul_comm,←cp]
  have beq:G.b=C c*F.b := by
    apply mul_left_cancel₀ f.1
    rw [eq,aeq];ring
  refine ⟨c,nz,?_⟩
  cases G
  cases F
  congr

private def good [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :=
  s.filter (fun y=>F.err v y=0)

def misses [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :=
  s.filter (fun y=>F.err v y≠0)

private theorem partition [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :
    (good F v s).card+(misses F v s).card=s.card :=
  s.card_filter_add_card_filter_not _

private theorem same_of_hits [DecidableEq K] {F G:Row K} (f:F.primitive) (g:G.primitive)
    (v:K→K) (s:Finset K)
    (many:s.card+F.graphDegree+G.graphDegree≤(good F v s).card+(good G v s).card) :
    ∃ t : K,t≠0 ∧ G=F.scale t := by
  classical
  apply scale_of_det_zero f g
  by_contra dn
  let common:=good F v s ∩ good G v s
  have sub : common ⊆ (F.det G).roots.toFinset := by
    intro x hx
    obtain ⟨hf,hg⟩ := mem_inter.mp hx
    have hf' := sub_eq_zero.mp ((mem_filter.mp hf).2 : F.err v x=0)
    have hg' := sub_eq_zero.mp ((mem_filter.mp hg).2 : G.err v x=0)
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots dn).mpr
    simp only [IsRoot,Row.det,eval_sub,eval_mul,←hf',←hg']
    ring
  have cap := (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))
  have tot:=card_union_add_card_inter (good F v s) (good G v s)
  have union : good F v s ∪ good G v s ⊆ s := union_subset (filter_subset ..) (filter_subset ..)
  have size:=card_le_card union
  have dcap:=natDegree_sub_le (F.a*G.b) (G.a*F.b)
  have h₁:=natDegree_mul_le (p:=F.a) (q:=G.b)
  have h₂:=natDegree_mul_le (p:=G.a) (q:=F.b)
  dsimp [common,Row.det] at cap
  unfold Row.graphDegree at many
  omega

/-- Choose disjoint ordinate sets with specified numbers of good and bad
points, even when an ordinate can support either kind of slope. -/
private theorem choose_colours {K : Type*} [DecidableEq K] (g b : Finset K) (n m : ℕ)
    (hg:n≤g.card) (hb:m≤b.card) (hu:n+m≤(g∪b).card) :
    ∃ G B : Finset K,G⊆g ∧ B⊆b ∧ Disjoint G B ∧ G.card=n ∧ B.card=m := by
  classical
  by_cases enough : n≤(g\b).card
  · obtain ⟨G,inG,ng⟩:=exists_subset_card_eq enough
    obtain ⟨B,inB,nb⟩:=exists_subset_card_eq hb
    refine ⟨G,B,inG.trans sdiff_subset,inB,disjoint_left.mpr ?_,ng,nb⟩
    intro x hx hB
    exact (mem_sdiff.mp (inG hx)).2 (inB hB)
  · have split:=card_sdiff_add_card_inter g b
    obtain ⟨D,hin,hd⟩:= exists_subset_card_eq (show n-(g\b).card≤(g∩b).card by omega)
    have db : D⊆b := hin.trans inter_subset_right
    have dg : D⊆g := hin.trans inter_subset_left
    have disj : Disjoint (g\b) D := disjoint_left.mpr (fun x hx h=> (mem_sdiff.mp hx).2 (db h))
    have tot:=card_union_add_card_inter g b
    have remain:=card_sdiff_add_card_eq_card db
    obtain ⟨B,hB,nb⟩:=exists_subset_card_eq (show m≤(b\D).card by omega)
    refine ⟨(g\b)∪D,B,union_subset sdiff_subset dg,hB.trans sdiff_subset,disjoint_left.mpr ?_,?_,nb⟩
    · intro x hx hx'
      obtain ⟨xb,xd⟩:=mem_sdiff.mp (hB hx')
      rcases mem_union.mp hx with e|e
      · exact (mem_sdiff.mp e).2 xb
      · exact xd e
    · rw [card_union_of_disjoint disj];omega

/-- A graph controls every selectable off-graph ordinate in the fibre.
This formulation also covers an infinite ambient set of possible sheets. -/
def Controls (F:Row K) (sheet:K→K→Prop) (c:ℕ) : Prop :=
  ∀ (s:Finset K) (v:K→K), (∀x∈s,sheet x (v x) ∧ F.err v x≠0) →
    s.card+F.graphDegree≤c

theorem global_of_local [DecidableEq K] (sheet:K→K→Prop) (e c limit:ℕ) (gap:2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    (chooseGraph : ∀ (s:Finset K) (v:K→K),s.card=e → (∀x∈s,sheet x (v x)) →
      ∃ F : Row K,F.primitive ∧ F.graphDegree≤limit ∧ (misses F v s).card+F.graphDegree≤c) :
    ∃ F : Row K,F.primitive ∧ F.graphDegree≤limit ∧ Controls F sheet c := by
  classical
  obtain ⟨s,v,se,known⟩:=initial
  obtain ⟨F,fp,degree,fc⟩:=chooseGraph s v se known
  refine ⟨F,fp,degree,?_⟩
  intro T w off
  by_contra! heavy
  let G₀:=good F v s
  let B₀:=misses F v s
  change B₀.card+F.graphDegree≤c at fc
  let B:=T∪B₀
  let m:=c-F.graphDegree+1
  let n:=e-m
  have partition₀ : G₀.card+B₀.card=e := (partition ..).trans se
  have nm:n+m=e := by dsimp [n,m];omega
  have nG:n≤G₀.card := by dsimp [m,n];omega
  have mB:m≤B.card := by
    have :=card_le_card (subset_union_left (s₁:=T) (s₂:=B₀))
    dsimp [B,m];omega
  have covered : s⊆G₀∪B := by
    intro x hx
    by_cases z:F.err v x=0
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,z⟩)
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hx,z⟩))
  obtain ⟨U,V,gu,bv,disj,nu,mv⟩ := choose_colours G₀ B n m nG mB (nm ▸ se ▸ card_le_card covered)
  let slope (x:K) := if x∈V ∧ x∈T then w x else v x
  have badV (x) (hx:x∈V) : sheet x (slope x) ∧ F.err slope x≠0 := by
    rcases mem_union.mp (bv hx) with xt|xb
    · simpa [slope,Row.err,hx,xt] using off x xt
    · by_cases xt:x∈T
      · simpa [slope,Row.err,hx,xt] using off x xt
      · have hz:=mem_filter.mp xb
        simpa [slope,Row.err,hx,xt] using And.intro (known x hz.1) hz.2
  have goodU (x) (hx:x∈U) : sheet x (slope x) ∧ F.err slope x=0 := by
    have nv : x∉V := fun hv=>disjoint_left.mp disj hx hv
    have hz := mem_filter.mp (gu hx)
    simpa [slope,Row.err,nv] using And.intro (known x hz.1) hz.2
  let S:=U∪V
  have cs:S.card=e := by dsimp [S];rw [card_union_of_disjoint disj,nu,mv,nm]
  obtain ⟨G,gp,_,gc⟩ := chooseGraph S slope cs (by
    intro x hx;rcases mem_union.mp hx with h|h
    · exact (goodU x h).1
    · exact (badV x h).1)
  have us : U⊆good F slope S := fun x hx=>mem_filter.mpr ⟨mem_union_left _ hx,(goodU x hx).2⟩
  have gcount:=partition G slope S
  have many:=card_le_card us
  obtain ⟨t,tn,rfl⟩:=same_of_hits fp gp slope S (by dsimp [n,m] at *;omega)
  have subset : V⊆misses (F.scale t) slope S := by
    intro x hx
    exact mem_filter.mpr ⟨mem_union_right _ hx,by rw [Row.err_scale];exact mul_ne_zero tn (badV x hx).2⟩
  have := card_le_card subset
  rw [Row.degree_scale F tn] at gc
  dsimp [m] at mv
  omega

#print axioms global_of_local

/-- Two global controls for the same sheets define the same rational graph. -/
theorem unique_control (sheet : K→K→Prop) (e c : ℕ) (gap : 2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    {F G:Row K} (fp:F.primitive) (gp:G.primitive)
    (fc:Controls F sheet c) (gc:Controls G sheet c) :
    ∃ t:K,t≠0 ∧ G=F.scale t := by
  classical
  obtain ⟨s,v,size,sel⟩ := initial
  have count {Q : Row K} (qc:Controls Q sheet c) :
      (misses Q v s).card+Q.graphDegree≤c :=
    qc _ v (fun x hx=> ⟨sel x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩)
  have b₁ := count fc
  have b₂ := count gc
  have h₁ := partition F v s
  have h₂ := partition G v s
  exact same_of_hits fp gp v s (by omega)

theorem Row.primitive_scale {F : Row K} (p : F.primitive) {c:K} (nz:c≠0) :
    (F.scale c).primitive := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr nz) p.1,?_⟩
  obtain ⟨u,w,bez⟩:=p.2
  use u*C c⁻¹,w*C c⁻¹
  change u*C c⁻¹*(C c*F.a)+w*C c⁻¹*(C c*F.b)=1
  have inv:C c⁻¹*C c=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ nz,C_1]
  calc
    _ = (C c⁻¹*C c)*(u*F.a+w*F.b) := by ring
    _ = _ := by rw [inv,bez,one_mul]

theorem Controls.scale {F:Row K} {sheet:K→K→Prop} {c:ℕ} (h:Controls F sheet c)
    {t:K} (nz:t≠0) : Controls (F.scale t) sheet c := by
  intro s v hv
  rw [Row.degree_scale _ nz]
  exact h s v (fun x hx => ⟨(hv x hx).1,fun eq=>(hv x hx).2 (by rw [Row.err_scale,eq,mul_zero])⟩)

theorem unique_monic_control (sheet : K→K→Prop) (e c : ℕ) (gap : 2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    {F G:Row K} (fp:F.primitive) (gp:G.primitive) (fm:F.a.Monic) (gm:G.a.Monic)
    (fc:Controls F sheet c) (gc:Controls G sheet c) : G=F := by
  obtain ⟨u,nu,rfl⟩:=unique_control sheet e c gap initial fp gp fc gc
  have h:u=1 := (fm.leadingCoeff_C_mul u).symm.trans gm
  cases F
  simp [h,Row.scale]

#print axioms unique_monic_control
end
end Research6966.Pade

end Merged_R6966ProofPadeCoverage
