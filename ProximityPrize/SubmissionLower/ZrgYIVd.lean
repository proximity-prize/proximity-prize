import ProximityPrize.SubmissionLower.Z5KYTEa
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.Z7znM4a
import ProximityPrize.SubmissionLower.ZQDgS7b
import ProximityPrize.SubmissionLower.ZzWMDba
set_option Elab.async false
open _root_ renaming Finset.sum_range_succ → zpB, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.ringHom_ext → zXT, Nat.mul_le_mul_left → zBI, Submodule → zpI
set_option maxHeartbeats 800000
section
set_option autoImplicit true
namespace qPQ4nYa
noncomputable section
open aR (ao)
open qlc9qed (Bank)
def top (b:Bank) :P5_7_2.TopRow :=⟨⟨b.m,b.box.b,b.box.j,b.U⟩,b.box.t,0,0⟩
instance gO4 (b:Bank) (q k :ℕ) :zAa ao (Block b q k) :=
 qSxbgdc.gO4 (top b) q k
instance originRangeFinite (b:Bank) :zAa ao (originRange b) :=
 qSxbgdc.originRangeFinite (top b)
theorem originRange_le_sum (b:Bank) (p:ℕ→ℕ→Rj.kJ)
  (h : ∀ q<b.box.b+1,∀ k<b.m+b.box.j,
    zsE ao (LinearMap.range (af3 b q k))≤xR b q (offset b k) (p q k)) :
  zsE ao (originRange b)≤ rankBudget b p :=
 qSxbgdc.originRange_le_sum (top b) p h
end
end qPQ4nYa
end
section
set_option autoImplicit true
namespace qzLARrc
noncomputable section
open aR (ao Shape jF)
open jA
open NR (Lq TT amn O8 aVU)
open aFN (canonical GV)
open qlc9qed (Bank)
open private cFT bCP from ProximityPrize.SubmissionLower.DG


open scoped Polynomial BigOperators
def c1 :Prop :=
  ∀ (a :Shape) (U:ℕ) (α k d e :ao),k≠0→d≠0 →
    ∀ V:zpI ao jK,
      (∀ F∈V,Jn a F∧gY F≤U) →
      ∃ f :V →ₗ[ao] localImage a U,∀ F:V,
        f F=0↔(znf (O8 α) :Lq)^(a.b+a.j) ∣
          canonical (O8 α) (GV (projectivity k d e) F.val)
def c2 :Prop :=
  ∀ (a :Shape) (U:ℕ),a.b≤U →
    zsE ao (localImage a U)≤windowBudget a U
def c3:Prop :=windowBudget Bank.cheap.box Bank.cheap.U≤oneDebit .cheap
def c4 :Prop :=windowBudget Bank.strong.box Bank.strong.U≤oneDebit .strong
private theorem bank_bounds (h3:c3) (h4 :c4) (b:Bank) :
   b.box.b≤b.U∧windowBudget b.box b.U≤oneDebit b:= by
 cases b
 · exact ⟨by decide,h3⟩
 · exact ⟨by decide,h4⟩
set_option backward.isDefEq.respectTransparency false in
private theorem codim_le_rank {E :Type*} [AddCommMonoid E] [Module ao E]
  [zAa ao E] (V W:zpI ao jK) [zAa ao V]
  (f :V →ₗ[ao] E) (hker :f.ker=W.comap V.subtype) :
  TT V W≤zsE ao E := by
 let:AddCommGroup E :=Module.addCommMonoidToAddCommGroup ao
 have hd:zsE ao f.range+Module.finrank ao f.ker=zsE ao V:= by
  exact LinearMap.finrank_range_add_finrank_ker (K:=ao) (V := ↥V) (V₂:=E) f
 have hk :=Submodule.finrank_map_subtype_eq V f.ker
 rw [hker,Submodule.map_comap_subtype] at hk
 rw [hker,← hk] at hd
 have hr :=Submodule.finrank_le f.range
 unfold TT
 omega
private theorem simple_bound (h1 :c1) (h2 :c2) (a :Shape) (U r :ℕ)
  (hwidth :a.b≤U) (hbudget:windowBudget a U≤ r)
  {Γ s} (P:jF Γ s) (L:kH P)
  (α:ao) (V:zpI ao jK) [zAa ao V]
  (hcap : ∀ F∈V,Jn a F∧gY F≤U)
  (hroot :P.H.IsRoot α) (hsimple :P.H.derivative.eval α≠0) :
  TT V (amn P L a (O8 α))≤ r := by
 obtain ⟨k,d,e,hk,hd,hn⟩:=normalized_center P L α hroot hsimple
 obtain ⟨f,hf⟩:=h1 a U α k d e hk hd V hcap
 let:zAa ao (localImage a U) :=
  Module.Finite.span_of_finite ao (Set.finite_range (localColumn a U))
 have hker :f.ker=(amn P L a (O8 α)).comap V.subtype := by
  ext F
  exact (LinearMap.mem_ker.trans (hf F)).trans (hn a F.val).symm
 have hdim:=codim_le_rank (E := ↥(localImage a U))
  V (amn P L a (O8 α)) f hker
 exact hdim.trans ((h2 a U hwidth).trans hbudget)
private theorem separable_bound (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (b:Bank) {Γ s} (P:jF Γ s) (L:kH P)
    (V:zpI ao jK) [zAa ao V]
    (hcap : ∀ F∈V,Jn b.box F∧gY F≤b.U) (hsep:P.H.Separable) :
    TT V (amn P L b.box (jH P.H))≤P.H.natDegree*oneDebit b:= by
  classical
  let T:Finset ao:=⟨P.H.roots,Polynomial.nodup_roots hsep⟩
  have hcard:T.card=P.H.natDegree :=IsAlgClosed.card_roots_eq_natDegree
  have hroot (α:ao) (hα:α∈T) :P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod: (∏ α∈T,O8 α)=jH P.H := by
    have he : (∏ α∈T,(Polynomial.X-Polynomial.C α))=P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _=Polynomial.mapRingHom (algebraMap ao kS) P.H
    rw [← he,map_prod]
    simp [O8]
  let W:ao→zpI ao jK:= fun α=>amn P L b.box (O8 α)
  have hlocal (α:ao) (hα:α∈T) :TT V (W α)≤oneDebit b :=
    let hb:=bank_bounds h3 h4 b
    simple_bound h1 h2 b.box b.U (oneDebit b) hb.1 hb.2 P L α V hcap (hroot α hα)
      (hsep.eval₂_derivative_ne_zero (RingHom.id ao) (hroot α hα))
  have hsub:T.inf W≤amn P L b.box (jH P.H) := by
    intro F hF
    have hcop:=Polynomial.pairwise_coprime_X_sub_C
      (FaithfulSMul.algebraMap_injective ao kS)
    have h:=Finset.prod_dvd_of_coprime (t:=T)
      (s := fun α=>(znf (O8 α) :Lq)^(b.box.b+b.box.j))
      (fun α _ β _ hne=>(IsCoprime.map (f :=znf) (hcop hne)).pow)
      (fun α hα=>(aVU P L b.box _ _).mp
        ((Finset.inf_le hα:T.inf W≤W α) hF))
    rw [Finset.prod_pow,← map_prod znf,hprod] at h
    exact (aVU P L b.box _ _).mpr h
  have hdim:=bCP V T W (oneDebit b) hlocal
  rw [hcard] at hdim
  exact (cFT V hsub).trans hdim
end
end qzLARrc
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
namespace qzVScmb

open P5_7_2 (fO introduction)
open q7F2qKe (nV originCutter originBudget aur bTu)
open TD (auN)

open Finset
private theorem budget_induct (b:fO) (i:ℕ) (P:bTu→Prop)
   (h0:P (auN (nV b 0).free))
   (hs : ∀ a∈introduction b,∀ r,P r →
     P (fun j=>min (r j) (auN a.shape j/(a.dI+1)))) :
   P (originBudget b i) := by
 suffices hh : ∀ (l:List P5_7_2.Aux),(∀ a∈l,a∈introduction b) →
     ∀ r,P r→P (l.foldl (fun r a j=>min (r j) (auN a.shape j/(a.dI+1))) r) by
   exact hh _ (fun _ h=>List.mem_of_mem_take h) _ h0
 intro l
 induction l with
 | nil=>exact fun _ _ hr=>hr
 | cons a l ih =>
   intro hm r hr
   exact ih (fun a ha=>hm a (List.mem_cons_of_mem _ ha)) _
     (hs a (hm a (List.mem_cons_self ..)) r hr)
theorem budget_J (b:fO) (i:ℕ) :originBudget b i 1≤originBudget b i 0 :=
 budget_induct b i (fun r=>r 1≤ r 0) (staged (stage_0 b)).1.jb
  (fun _ ha _ hr=>min_le_min hr (Nat.div_le_div_right (intro_guard ha).1))
theorem enclosing (B J C U r t v :ℕ) (hJ:0<J) (hC:0<C)
  (hBC:J+C≤B) (ht:t≤ r) :
  let b:=B+C*(r-1)
  let j:=J+C*(t-1)
  j≤b∧t≤j∧r-t≤b-j∧r≤b∧v≤U+C*v := by
 have hmul (n:ℕ) :n≤C*n:=Nat.le_mul_of_pos_left _ hC
 have h1 :=hmul (t-1)
 have h2 :=hmul (r-1)
 have h3:=hmul (r-t)
 have h4 :=zBI C (Nat.sub_le_sub_right ht 1)
 have h5:=zBI C (show (t-1)+(r-t)≤(r-1)+1 by omega)
 rw [Nat.mul_add,Nat.mul_add,Nat.mul_one] at h5
 dsimp only
 exact ⟨by omega,by omega,by omega,by omega,(hmul _).trans (Nat.le_add_left _ _)⟩
theorem final_valid (b:fO) :
  let t:=originCutter b (last b)
  let s :=aur (originBudget b (last b))
  t.J≤t.B∧s.J≤t.J∧s.B - s.J≤t.B - t.J∧s.B≤t.B∧s.U≤t.U:= by
 obtain ⟨hJ,hC,hBC⟩:=top_arithmetic b
 have h:=List.getElem?_length (introduction b)
 simp only [originCutter,h,aur]
 exact enclosing _ _ _ _ _ _ _ hJ hC hBC (budget_J b (last b))
end qzVScmb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qo38hre
noncomputable section
open Polynomial Finset
open P5 (K I node)
open cu (L FX j9 jz)
open DQ (DT aKg XO specialize)
open MvPolynomial (totalDegree_add totalDegree_mul totalDegree_C totalDegree_finsetSum_le)
open Cu (sQ oO wJ yI
 EF W8 a9K aCn aa4 zT Mu)
open P5_7_7 (hit base)
open scoped Classical
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
open private cK5 from ProximityPrize.SubmissionLower.CR
private def liftCut (n:ℕ) :DT n →+* Cu.Gc n :=
 (aa4 n).comp (MvPolynomial.map (algebraMap L FX))
private theorem cut_eval {n:ℕ} (z :K) (t:Fin n→L) (q:DT n) :
  MvPolynomial.aeval (aCn z t) (liftCut n q)=algebraMap L FX (zY9 t q) := by
 have he : (zY9 (aCn z t)).comp (liftCut n) =
    (algebraMap L FX).comp (zY9 t) := by
  apply zXT
  · intro c
    simp [liftCut,aa4]
  · intro j
    simp [liftCut,aa4,aCn]
 exact DFunLike.congr_fun he q
private theorem taylor_degree {n:ℕ} (f : (DT n)[X]) (a :L)
  (hf : ∀ j,(f.coeff j).totalDegree≤1) (k :ℕ) :
  ((f.taylor (znf a)).coeff k).totalDegree≤1 := by
 rw [taylor_coeff,hasseDeriv_apply,Polynomial.sum_def,eval_finsetSum]
 apply totalDegree_finsetSum_le
 intro j _
 have hc: (↑(j.choose k) :DT n)=znf (j.choose k :L) :=
  (map_natCast _ _).symm
 rw [eval_monomial,hc,← map_pow]
 refine (totalDegree_mul _ _).trans ?_
 rw [totalDegree_C,add_zero]
 refine (totalDegree_mul _ _).trans ?_
 simpa only [totalDegree_C,zero_add] using hf j
private theorem linear_root {n:ℕ} {f :XO n}
   (hf :aKg f 1) (t:Fin n→L) (S:K[X])
   (hr : (specialize f t).eval (j9 S)=0) :
   (f.coeff 0).map (zY9 t) +
     (f.coeff 1).map (zY9 t)*j9 S=0:= by
 have hd: (specialize f t).natDegree<2 :=
   (natDegree_map_le.trans hf.1).trans_lt (by decide)
 rw [eval_eq_sum_range' hd,zpB,zpB] at hr
 simpa only [sum_range_zero,zero_add,pow_zero,pow_one,mul_one,
   specialize,coeff_map,coe_mapRingHom] using hr
private theorem leading_relation {a b S:L[X]} {k :ℕ} (h:a+b*S=0)
   (hb : ∀ j<k,b.coeff j=0) :
   a.coeff k+b.coeff k*S.eval 0=0:= by
 have hc:=congrArg (fun f :L[X]=>f.coeff k) h
 rw [coeff_add,coeff_mul,coeff_zero,sum_eq_single (k,0)] at hc
 · simpa only [coeff_zero_eq_eval_zero] using hc
 · intro j hj hj'
   rw [hb j.1 (by
     have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj
     rcases j with ⟨a,b⟩
     change a+b=k at hsum
     change a<k
     by_contra! hge
     obtain rfl :a=k := by omega
     obtain rfl :b=0:= by omega
     exact hj' rfl),zero_mul]
 · simp [Finset.HasAntidiagonal.mem_antidiagonal]
private theorem cGg {Q:sQ} [Fact (Irreducible Q)]
   {J n} {R:wJ Q J 1} (A:yI R n) :
   ((A.equation.coeff 1).map ((W8 A).comp (liftCut n)))≠0:= by
 let e :=MvPolynomial.eval₂Hom (zT Q) A.coordinate
 have he : (W8 A).comp (liftCut n)=(Mu Q).comp e := by
   apply zXT
   · intro a
     simp [liftCut,e,W8,aa4,b1t]
   · intro j
     simp [liftCut,e,W8,aa4]
 have hb:=congrArg (fun f : ((oO Q)[X])[X]=>f.coeff 1) A.generic_eq
 rw [coeff_map,coe_mapRingHom,coeff_C_mul] at hb
 have hR:R.equation.coeff 1≠0:= by
   have heq :R.equation.coeff 1=R.equation.leadingCoeff :=
     (congrArg R.equation.coeff R.degree).symm.trans coeff_natDegree
   rw [heq]
   exact leadingCoeff_ne_zero.mpr (fun hz=>R.irreducible.ne_zero (by simp [hz]))
 have hs : (A.scale :oO Q)≠0:=A.scale.ne_zero
 rw [he,← Polynomial.map_map]
 change ((A.equation.coeff 1).map e).map (Mu Q)≠0
 rw [show (A.equation.coeff 1).map e= _ from hb]
 intro h
 exact (mul_ne_zero (C_ne_zero.mpr hs) hR)
   ((Polynomial.map_injective _ (Mu Q).injective) (h.trans (Polynomial.map_zero _).symm))
theorem sections {Q:sQ} [Fact (Irreducible Q)] {J n H}
    {R:wJ Q J 1} (A:yI R n)
    (hH :a9K (EF A) H) {T:Finset K} {z :K→K} {s :K→K[X]}
    {t:K→Fin n→L} (hz :Set.InjOn z (T:Set K))
    (hbase : ∀ γ∈T,aCn (z γ) (t γ)∈MvPolynomial.zeroLocus FX (EF A))
    (hroot : ∀ γ∈T,(specialize A.equation (t γ)).eval (j9 (s γ))=0)
    (w:I→K) (i:I) :
    (T.filter fun γ=>hit w s γ i).card≤H ∨
    (T.filter fun γ => ¬ hit w s γ i).card≤H := by
  let point (γ:K) :=aCn (z γ) (t γ)
  let e (γ:K) :=zY9 (t γ)
  have ec (γ:K) (r :L) :e γ (znf r)=r :=z9X r
  let f :=A.equation
  let G:=(W8 A).comp (liftCut n)
  let a :=(f.coeff 0).taylor (znf (base i))
  let b:=(f.coeff 1).taylor (znf (base i))
  have hn:b.map G≠0:= by
    dsimp only [b]
    rw [map_taylor]
    exact fun h=>cGg A ((taylor_eq_zero _ _).mp h)
  have hex : ∃ k,G (a.coeff k)≠0∨G (b.coeff k)≠0:= by
    by_contra! h
    apply hn
    ext k
    simpa only [coeff_map,coeff_zero] using (h k).2
  let k :=Nat.find hex
  have hk :G (a.coeff k)≠0∨G (b.coeff k)≠0:=Nat.find_spec hex
  have at_zero (γ:K) (hγ:γ∈T) (q:DT n) (hq:G q=0) :
      e γ q=0:= by
    have h:=MvPolynomial.mem_zeroLocus_iff.mp (hbase γ hγ) (liftCut n q)
      (RingHom.mem_ker.mpr hq)
    rw [cut_eval] at h
    exact (algebraMap L FX).injective (h.trans (map_zero _).symm)
  have relation (γ:K) (hγ:γ∈T) :
      e γ (a.coeff k)+e γ (b.coeff k) *
        algebraMap K L ((s γ).eval (node i))=0:= by
    have he :=congrArg (taylorAlgHom (base i) :L[X] →ₐ[L] L[X])
      (linear_root A.degree (t γ) (s γ) (hroot γ hγ))
    have shift (p:L[X]) :taylorAlgHom (base i) p=p.taylor (base i) :=rfl
    have h:a.map (e γ)+b.map (e γ)*(j9 (s γ)).taylor (base i)=0:= by
      simpa only [a,b,e,map_add,map_zero,shift,taylor_mul,
        map_taylor,z9X] using he
    have hrel :=leading_relation h (fun j hj=> by
      rw [coeff_map]
      exact at_zero γ hγ _ (by
        by_contra hnz
        exact Nat.find_min hex hj (Or.inr hnz)))
    rw [coeff_map,coeff_map,taylor_eval,zero_add] at hrel
    simpa only [e,base,j9,eval_map_apply] using hrel
  have hpt:Set.InjOn point (T:Set K) := by
    intro γ hγ η hη h
    exact hz hγ hη (jz.injective (congrFun h (Sum.inl 0)))
  have gX (V:Finset K) (hV:V⊆T) (q:DT n) (hq:G q≠0)
      (hd:q.totalDegree≤1) (he : ∀ γ∈V,e γ q=0) :
      V.card≤H := by
    have hm: (MvPolynomial.map (algebraMap L FX) q).totalDegree≤1 :=
      (Finset.sup_mono (MvPolynomial.support_map_subset (algebraMap L FX) q)).trans hd
    refine (cK5 n H _ (RingHom.ker_isPrime (W8 A)) hH _
      (fun hh=>hq (RingHom.mem_ker.mp hh)) V point (hpt.mono hV) ?_).trans ?_
    · intro γ hγ
      exact ⟨hbase γ (hV hγ),(cut_eval _ _ _).trans (by rw [he γ hγ,map_zero])⟩
    · simpa only [one_mul] using Nat.mul_le_mul_right H hm
  let q:=a.coeff k+b.coeff k*znf (algebraMap K L (w i))
  have hd (j:ℕ) : (((f.coeff j).taylor (znf (base i))).coeff k).totalDegree≤1 :=
    taylor_degree _ _ (A.degree.2 j) _
  by_cases hq:G q=0
  · right
    have hb:G (b.coeff k)≠0:= by
      intro hb
      have ha :G (a.coeff k)=0:= by
        simpa only [q,map_add,map_mul,hb,zero_mul,add_zero] using hq
      exact hk.elim (fun h=>h ha) (fun h=>h hb)
    refine gX _ (filter_subset _ _) _ hb (hd 1) ?_
    intro γ hγ
    obtain ⟨hγ,hmiss⟩:=mem_filter.mp hγ
    have hr :=relation γ hγ
    have hv :=at_zero γ hγ q hq
    simp only [q,map_add,map_mul,ec] at hv
    have hm:algebraMap K L ((s γ).eval (node i))-algebraMap K L (w i)≠0 :=
      sub_ne_zero.mpr (fun he=>hmiss ((algebraMap K L).injective he))
    have hmul :e γ (b.coeff k) *
        (algebraMap K L ((s γ).eval (node i))-algebraMap K L (w i))=0:= by
      rw [mul_sub]
      linear_combination hr - hv
    exact (mul_eq_zero.mp hmul).resolve_right hm
  · left
    refine gX _ (filter_subset _ _) q hq ((totalDegree_add _ _).trans (max_le (hd 0) ?_)) ?_
    · exact (totalDegree_mul _ _).trans (by simpa only
        [totalDegree_C,add_zero] using (hd 1))
    · intro γ hγ
      obtain ⟨hγ,hhit⟩:=mem_filter.mp hγ
      have he : (s γ).eval (node i)=w i:=hhit
      simpa only [q,map_add,map_mul,ec,he] using relation γ hγ
end
end qo38hre
end
