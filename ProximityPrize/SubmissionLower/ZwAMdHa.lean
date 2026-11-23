import ProximityPrize.SubmissionLower.Z97nQia
import ProximityPrize.SubmissionLower.ZGijG6c
import ProximityPrize.SubmissionLower.ZVbskte
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qcYA6zd
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open cu (L)
open E7 (CurveField CurvePlace poleOrder KB)
open agN (O7 b27)
open qb0hmCe (coeffHeight)
open qFD8jve (sheetPole)
open private maxValue cu9 ew3 bca from ProximityPrize.SubmissionLower.V
open private Coeffs size entries lt_size from ProximityPrize.SubmissionLower.Zi3GgJd
open private gauss₂ gauss₂_C gauss₂_normal coeff_le_gauss₂ pole_le from ProximityPrize.SubmissionLower.ZhEC96c
open private adG b4s bHf from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E] [Algebra L E]
abbrev nY (u:E) (f :E[X][X]) :E[X][X] :=C (C u)*f
omit [Algebra L E] in
theorem gmm (u:E) (f :E[X][X]) (i j:ℕ) :
  ((nY u f).coeff i).coeff j=u*(f.coeff i).coeff j:= by
 rw [coeff_C_mul,coeff_C_mul]
private theorem gauss_le (v :CurvePlace L E) (f :E[X][X]) {M:ℤᵐ⁰}
  (h : ∀ i j,v.value ((f.coeff i).coeff j)≤M) :gauss₂ v.value f≤M:= by
 change adG (b4s v.value) (f.map (algebraMap E[X] (RatFunc E)))≤M
 exact Finset.sup_le fun i _=> by
  rw [coeff_map,bHf]
  exact Finset.sup_le fun j _=>h i j
private theorem gauss_max (v :CurvePlace L E) (f :E[X][X]) (h:f.leadingCoeff.leadingCoeff=1) :
   gauss₂ v.value f=maxValue v (entries f) := by
 have ha :entries f (⟨f.natDegree,by omega⟩,⟨(f.coeff f.natDegree).natDegree,lt_size f _⟩)=1 := by
   rw [entries,coeff_natDegree]
   exact h
 have h₁:1≤gauss₂ v.value f := by
   have hc:=coeff_le_gauss₂ v.value f f.natDegree (f.coeff f.natDegree).natDegree
   rwa [show (f.coeff f.natDegree).coeff (f.coeff f.natDegree).natDegree=1 from ha,map_one] at hc
 apply le_antisymm _ (max_le h₁ (Finset.sup_le fun i _=>coeff_le_gauss₂ v.value f i.1 i.2))
 apply gauss_le v f
 intro i j
 by_cases hi:i<f.natDegree+1
 · by_cases hj:j<size f
   · exact cu9 v (entries f) (⟨i,hi⟩,⟨j,hj⟩)
   · rw [coeff_eq_zero_of_natDegree_lt ((lt_size f i).trans_le (Nat.le_of_not_gt hj)),map_zero]
     exact zero_le
 · rw [coeff_eq_zero_of_natDegree_lt (by omega :f.natDegree< i),coeff_zero,map_zero]
   exact zero_le
private theorem gauss_attains (v :CurvePlace L E) (f :E[X][X])
   (h:f.leadingCoeff.leadingCoeff=1) :
   ∃ i:Coeffs f,gauss₂ v.value f=v.value (entries f i) := by
 obtain ⟨i,_,hi⟩:=exists_mem_eq_sup (univ :Finset (Coeffs f)) univ_nonempty
   (fun i=>v.value (entries f i))
 let j:Coeffs f :=(⟨f.natDegree,by omega⟩,⟨(f.coeff f.natDegree).natDegree,lt_size f _⟩)
 have hj:entries f j=1 := by
   rw [show entries f j=(f.coeff f.natDegree).coeff (f.coeff f.natDegree).natDegree from rfl,coeff_natDegree]
   exact h
 have h₀:1≤v.value (entries f i) := by
   simpa only [hi,hj,map_one] using
     (le_sup (f := fun j=>v.value (entries f j)) (mem_univ j))
 refine ⟨i,?_⟩
 rw [gauss_max v f h]
 change max 1 (univ.sup fun j=>v.value (entries f j))= _
 rw [hi,max_eq_right h₀]
private theorem choose_scalar (f :E[X][X]) (h:f.leadingCoeff.leadingCoeff=1)
   (T:Finset (CurvePlace L E)) :
   ∃ c:E,c≠0∧(∀ v :CurvePlace L E,v.value c≤gauss₂ v.value f) ∧
     ∀ v∈T,v.value c=gauss₂ v.value f := by
 by_cases hT:T.Nonempty
 · let r :=entries f
   have hproper (v :T) :bca v.val r ≠ ⊤ := by
     obtain ⟨i,hi⟩:=gauss_attains v.val f h
     have he :=(gauss_max v.val f h).symm.trans hi
     intro ht
     have hm: (Pi.single i (1 :L))∈bca v.val r := by rw [ht]; trivial
     change v.val.value (O7 (Pi.single i (1 :L)) r)< maxValue v.val r at hm
     simp [O7] at hm
     exact (lt_irrefl _) ((show v.val.value (entries f i)< maxValue v.val (entries f) from hm).trans_le he.le)
   have hcover : (⋃ v :T,(bca v.val r :Set (Coeffs f→L)))≠Set.univ := by
     intro he
     obtain ⟨v,hv⟩:=Subspace.exists_eq_top_of_iUnion_eq_univ he
     exact hproper v hv
   obtain ⟨a,ha⟩:=Set.nonempty_compl.2 hcover
   simp only [Set.mem_compl_iff,Set.mem_iUnion,not_exists] at ha
   let c:=O7 a r
   have hle (v :CurvePlace L E) :v.value c≤gauss₂ v.value f :=
     (ew3 v r a).trans (gauss_max v f h).symm.le
   have he (v :CurvePlace L E) (hv :v∈T) :v.value c=gauss₂ v.value f := by
     rw [gauss_max v f h]
     exact (ew3 v r a).antisymm (le_of_not_gt (ha ⟨v,hv⟩))
   obtain ⟨v,hv⟩:=hT
   refine ⟨c,fun hz => ?_,hle,he⟩
   have hp:=he v hv
   rw [hz,map_zero,gauss_max v f h] at hp
   exact (zero_lt_one.trans_le (le_max_left _ _)).ne hp
 · refine ⟨1,one_ne_zero,fun v => ?_,fun v hv=>(hT ⟨v,hv⟩).elim⟩
   rw [map_one,gauss_max v f h]
   exact le_max_left _ _
private theorem scale_height (hc:CurveField L E) (f :E[X][X])
    (h:f.leadingCoeff.leadingCoeff=1) {c:E} (hn:c≠0)
    (hle : ∀ v :CurvePlace L E,v.value c≤gauss₂ v.value f) :
    coeffHeight (nY c⁻¹ f)≤ coeffHeight f := by
  let P (v :CurvePlace L E) :=sheetPole v.value f
  let Q (v :CurvePlace L E) :=sheetPole v.value (nY c⁻¹ f)
  let A (v :CurvePlace L E) :=poleOrder v.value c
  let B (v :CurvePlace L E) :=KB v.value c
  have hlocal (v :CurvePlace L E) :A v+Q v≤P v+B v := by
    let l:=WithZero.log (v.value c)
    have hv :=v.value.ne_zero_iff.mpr hn
    have hp:l≤(P v :ℤ) := by
      have hh:=hle v
      rw [gauss₂_normal v.value f h] at hh
      exact (WithZero.log_le_iff_le_exp hv).mpr hh
    have hq:Q v≤((P v :ℤ)-l).toNat := by
      apply Finset.sup_le
      intro ij _
      apply pole_le v.value
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hp)]
      have he :gauss₂ v.value (nY c⁻¹ f)=WithZero.exp ((P v :ℤ)-l) := by
        change gauss₂ v.value (C (C c⁻¹)*f)= _
        rw [map_mul,gauss₂_C,map_inv₀,gauss₂_normal v.value f h,← WithZero.exp_log hv,
          ← WithZero.exp_neg,← WithZero.exp_add,neg_add_eq_sub]
      exact (coeff_le_gauss₂ v.value (nY c⁻¹ f) ij.1 ij.2).trans_eq he
    change l.toNat+Q v≤P v+(-l).toNat
    omega
  have hdiv :=aFU.of_children
    bRt.proof bRu.proof L E hc
  obtain ⟨hA,hB,hab,_⟩:=hdiv c
  have hP:P.HasFiniteSupport:=b27 hdiv _
  have hQ:Q.HasFiniteSupport:=b27 hdiv _
  have hh:=finsum_le_finsum (hA.add hQ) (hP.add hB) hlocal
  change (∑ᶠ v,(A v+Q v)) ≤ ∑ᶠ v,(P v+B v) at hh
  rw [finsum_add_distrib hA hQ,finsum_add_distrib hP hB,← hab,add_comm (∑ᶠ v,P v)] at hh
  exact Nat.le_of_add_le_add_left hh
theorem normalize (hc:CurveField L E) (f :E[X][X]) (h:f.leadingCoeff.leadingCoeff=1)
    (T:Finset (CurvePlace L E)) :
    ∃ c:E,c≠0∧coeffHeight (nY c⁻¹ f)≤ coeffHeight f ∧
      ∀ v∈T,(∀ i j,v.value (((nY c⁻¹ f).coeff i).coeff j)≤1) ∧
        ∃ i j,v.value (((nY c⁻¹ f).coeff i).coeff j)=1 := by
  obtain ⟨c,hn,hle,he⟩:=choose_scalar f h T
  refine ⟨c,hn,scale_height hc f h hn hle,fun v hv=>⟨fun i j => ?_,?_⟩⟩
  · rw [gmm,map_mul,map_inv₀]
    exact (mul_le_mul' le_rfl ((coeff_le_gauss₂ v.value f i j).trans_eq (he v hv).symm)).trans_eq
      (inv_mul_cancel₀ (v.value.ne_zero_iff.mpr hn))
  · obtain ⟨i,hi⟩:=gauss_attains v f h
    refine ⟨i.1,i.2,?_⟩
    rw [gmm,map_mul,map_inv₀,show v.value ((f.coeff i.1).coeff i.2)=v.value c from
      hi.symm.trans (he v hv).symm,inv_mul_cancel₀ (v.value.ne_zero_iff.mpr hn)]
end
end qcYA6zd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qcYA6zd
noncomputable section
open Polynomial Finset
open cu (L FX)
open E7 (CurvePlace)
open P5_7_7 (phys)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (expansion_coeff power_residue small_valuation)
open qfJaLMa (aJj)
open private scale_expansion from ProximityPrize.SubmissionLower.Z97nQia
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E]
private abbrev val :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
private theorem unit_coeff {x :LaurentSeries L} (h:val x=1) :x.coeff 0≠0:= by
 obtain ⟨r,hr⟩:=(LaurentSeries.val_le_one_iff_eq_coe L x).mp h.le
 intro hz
 have hle :=(small_valuation r).mpr ((power_residue x r hr.symm).symm.trans hz)
 rw [hr,h] at hle
 exact (not_le_of_gt (by simp :WithZero.exp (-1 :ℤ)<1)) hle
private theorem coeff_one_product {x y :LaurentSeries L} (hx :val x≤1) (hy :val y≤1) :
  (x*y).coeff 1=x.coeff 1*y.coeff 0 + x.coeff 0*y.coeff 1 := by
 obtain ⟨r,hr⟩:=(LaurentSeries.val_le_one_iff_eq_coe L x).mp hx
 obtain ⟨t,ht⟩:=(LaurentSeries.val_le_one_iff_eq_coe L y).mp hy
 rw [← hr,← ht,← PowerSeries.coe_mul]
 change ((↑(r*t) :LaurentSeries L)).coeff ((1 :ℕ) :ℤ) =
  (↑r :LaurentSeries L).coeff ((1 :ℕ) :ℤ)*(↑t:LaurentSeries L).coeff 0 +
  (↑r :LaurentSeries L).coeff 0*(↑t:LaurentSeries L).coeff ((1 :ℕ) :ℤ)
 rw [power_residue _ t rfl,power_residue _ r rfl]
 simp only [LaurentSeries.coeff_coe_powerSeries]
 rw [PowerSeries.coeff_one_mul,mul_comm (PowerSeries.coeff 1 t)]
private theorem exp_first (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (u:E)
   (hu:val (a u)≤1) (hf : ∀ i j,val (a ((f.coeff i).coeff j))≤1) :
   cLN a 1 (nY u f)=nY ((a u).coeff 1) (cLN a 0 f) +
     nY ((a u).coeff 0) (cLN a 1 f) := by
 ext i j
 simp only [expansion_coeff,gmm,coeff_add,map_mul]
 exact coeff_one_product hu (hf i j)
theorem transport_jet (v :CurvePlace L E) (a :E →ₐ[L] LaurentSeries L)
   (ha : ∀ c,v.value c=val (a c)) {f g:E[X][X]} {u:E}
   (hg:g=nY u f) (hf : ∀ i j,v.value ((f.coeff i).coeff j)≤1)
   (hf₀:cLN a 0 f≠0) (hg₀ : ∃ i j,v.value ((g.coeff i).coeff j)=1)
   (hgi : ∀ i j,v.value ((g.coeff i).coeff j)≤1) (P Q:L[X])
   (hr :specialize (cLN a 0 f) P Q=0) :
   ∃ m:L,m≠0∧cLN a 0 g=nY m (cLN a 0 f) ∧
     zD a g P Q=zD a f P Q:= by
 have hval (i j:ℕ) :v.value ((g.coeff i).coeff j)=v.value u*v.value ((f.coeff i).coeff j) := by
   rw [hg,gmm,map_mul]
 obtain ⟨i,hi⟩:=support_nonempty.mpr hf₀
 obtain ⟨j,hj⟩:=support_nonempty.mpr (mem_support_iff.mp hi)
 have h₁:=aJj v a (ha _) (hf i j) (by
   rw [← expansion_coeff]
   exact mem_support_iff.mp hj)
 have huv :v.value u=1 := by
   apply le_antisymm
   · have hh:=hgi i j
     rwa [hval,h₁,mul_one] at hh
   · obtain ⟨k,ℓ,hk⟩:=hg₀
     rw [hval] at hk
     exact hk.symm.le.trans ((mul_le_mul' le_rfl (hf k ℓ)).trans_eq (mul_one _))
 have hua :val (a u)=1 :=(ha _).symm.trans huv
 have hin (i j:ℕ) :val (a ((f.coeff i).coeff j))≤1 :=(ha _).symm.trans_le (hf i j)
 let m:=(a u).coeff 0
 have hm:m≠0:=unit_coeff hua
 have h₀:cLN a 0 g=nY m (cLN a 0 f) :=
   hg ▸ scale_expansion a f u hua.le hin
 refine ⟨m,hm,h₀,?_⟩
 unfold zD
 rw [h₀,derivative_C_mul,hg,exp_first a f u hua.le hin]
 simp only [specialize,eval₂_add,eval₂_mul,eval₂_C] at hr ⊢
 rw [hr,mul_zero,zero_add]
 exact congrArg (fun r :FX => -r*phys Q^2)
   (mul_div_mul_left _ _ ((map_ne_zero_iff phys (IsFractionRing.injective L[X] FX)).mpr (C_ne_zero.mpr hm)))
end
end qcYA6zd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qcYA6zd
noncomputable section
open Polynomial Finset qfJaLMa
open P5 (K)
open cu (L FX)
open E7 (CurveField)
open P5_7_7 (phys)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (expansion_coeff)
open qNu3xvc (Equation Sections qg finitePoles)
open qWIOgVd (bY rev width width_bound rev_ne rev_coprime rev_ratio rev_degree x x_ne)
open private layer_repr eval_change deriv_change cancel_ratio from ProximityPrize.SubmissionLower.ZGijG6c
open scoped Classical WithZero
theorem move_sections {E :Type} [Field E] [Algebra L E] (hE :CurveField L E)
    (A:Equation E) (S:Sections A) :
    ∃ (B:Equation E) (T:Sections B),B.d=A.d∧B.s=A.s∧B.b=A.b∧B.h≤A.h ∧
      (∑ γ∈S.marks,width (A.s+2*width A.s (S.P γ) (S.Q γ)) (S.num γ) (S.den γ))≤finitePoles T:= by
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset
    (S.marks.biUnion fun γ=>(S.den γ).roots.toFinset)
  have hfresh (γ:K) (hγ:γ∈S.marks) : (S.den γ).eval a≠0:= fun hz =>
    ha (mem_biUnion.mpr ⟨γ,hγ,Multiset.mem_toFinset.mpr ((mem_roots (S.den_ne γ hγ)).mpr hz)⟩)
  let s :=A.s
  obtain ⟨k,hkb,hb,hhit⟩:=choose_cap A.irreducible.ne_zero s A.b A.weight
  let D:=bY a
  let g:=move (algebraMap L E a) s k A.d A.f
  have hd:g.natDegree=A.d:=move_degree _ _ _ _ A.irreducible.ne_zero
  have hgwt (i:ℕ) : (g.coeff i).natDegree+i*s≤A.b+g.natDegree*s∨g.coeff i=0:= by
    by_cases hz :g.coeff i=0
    · exact Or.inr hz
    have hi:i≤A.d:=hd ▸ le_natDegree_of_ne_zero hz
    have hh: (g.coeff i).natDegree≤ cap s k A.d i:= by rw [move_coeff]; exact pad_bound _ (hb i)
    have he : (A.d-i)*s+i*s=A.d*s := by rw [← add_mul,Nat.sub_add_cancel hi]
    rw [hd]
    unfold cap at hh
    exact Or.inl (by omega)
  let B:Equation E :=⟨g,move_irred A.irreducible A.positive hb hhit,hd.symm ▸ A.positive,
    s,A.b,hgwt⟩
  let m (γ:K) :=width s (S.P γ) (S.Q γ)
  let t (γ:K) :=s+2*m γ
  let n (γ:K) :=width (t γ) (S.num γ) (S.den γ)
  let P' (γ:K) :=rev a (m γ+s) (S.P γ)
  let Q' (γ:K) :=rev a (m γ) (S.Q γ)
  let N' (γ:K) :=rev a (n γ+t γ) (S.num γ)
  let B' (γ:K) :=rev a (n γ) (S.den γ)
  let c:FX:=x^(k+A.d*s)
  let v :FX:=x^s
  have hc:c≠0:=pow_ne_zero _ x_ne
  have hv :v≠0:=pow_ne_zero _ x_ne
  let changeOrd:=changeY D.changeX v hv
  let e :=S.atPlace
  have repr (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      (cLN (e γ hγ) j g).map phys=C c*changeOrd ((cLN (e γ hγ) j A.f).map phys) :=
    layer_repr (e γ hγ) j D s k A.f hb
  have hdeg (γ:K) (hγ:γ∈S.marks) : (cLN (e γ hγ) 0 g).natDegree=A.d:= by
    rw [exp_move,move_degree]
    · exact S.degree γ hγ
    · exact fun h=>A.positive.ne' ((S.degree γ hγ).symm.trans (by rw [h,natDegree_zero]))
  have hval (γ:K) (hγ:γ∈S.marks) (i j:ℕ) :
      (S.place γ).value ((g.coeff i).coeff j)≤1 :=move_val_le _ a s k A.d A.f (S.regular γ hγ).1 i j
  have hreg (γ:K) (hγ:γ∈S.marks) :qg B (S.place γ) := by
    refine ⟨hval γ hγ,?_⟩
    let F:=cLN (e γ hγ) 0 g
    have hF:F.natDegree=A.d:=hdeg γ hγ
    have hn:F.coeff A.d≠0:= by
      rw [← hF,← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr (fun h=>A.positive.ne' (hF.symm.trans (by rw [h,natDegree_zero])))
    refine ⟨A.d,(F.coeff A.d).natDegree,aJj (S.place γ) (e γ hγ) (S.value γ hγ _)
      (hval γ hγ _ _) ?_⟩
    rw [← expansion_coeff,← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hn
  have hsep (γ:K) (hγ:γ∈S.marks) : ((cLN (e γ hγ) 0 g).map phys).Separable := by
    let F:=(cLN (e γ hγ) 0 A.f).map phys
    rw [repr,separable_def,deriv_change]
    exact (isCoprime_mul_units_left (hc.isUnit.map C)
      ((mul_ne_zero hc (inv_ne_zero hv)).isUnit.map C) _ _).mpr
      (((separable_def F).mp (S.separable γ hγ)).map changeOrd.toRingHom)
  have hratio (γ:K) :phys (P' γ)/phys (Q' γ) =
      v*D.changeX (phys (S.P γ)/phys (S.Q γ)) :=rev_ratio D s
  have hsp (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      specialize (cLN (e γ hγ) j g) (P' γ) (Q' γ) =
        c*D.changeX (specialize (cLN (e γ hγ) j A.f) (S.P γ) (S.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,hratio,repr,eval_mul,eval_C]
    rw [eval_change]
  have hdsp (γ:K) (hγ:γ∈S.marks) :
      specialize (cLN (e γ hγ) 0 g).derivative (P' γ) (Q' γ) =
        (c*v⁻¹)*D.changeX (specialize (cLN (e γ hγ) 0 A.f).derivative (S.P γ) (S.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,← derivative_map,hratio,repr]
    rw [deriv_change D.changeX v hv,eval_mul,eval_C,eval_change]
  let T:Sections B := {
    marks :=S.marks
    place :=S.place
    distinct :=S.distinct
    atPlace :=e
    value :=S.value
    regular :=hreg
    degree := fun γ hγ=>(hdeg γ hγ).trans hd.symm
    separable :=hsep
    P:=P'
    Q:= Q'
    denom:= fun γ hγ=>rev_ne a _ (S.denom γ hγ)
    coprime := fun γ hγ=>rev_coprime a s (S.denom γ hγ) (S.coprime γ hγ)
    root := fun γ hγ=> by rw [hsp,S.root γ hγ,map_zero,mul_zero]
    simple := fun γ hγ=> by
      rw [hdsp]
      exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero hv))
        ((map_ne_zero_iff _ D.changeX.injective).mpr (S.simple γ hγ))
    num :=N'
    den:=B'
    den_ne := fun γ hγ=>rev_ne a _ (S.den_ne γ hγ)
    reduced:= fun γ hγ=>rev_coprime a _ (S.den_ne γ hγ) (S.reduced γ hγ)
    formula := fun γ hγ=> by
      rw [rev_ratio D (t γ),S.formula γ hγ]
      unfold zD
      rw [hsp,hdsp,cancel_ratio _ _ _ _ hc,show Q' γ=rev a (m γ) (S.Q γ) from rfl,
        D.CJ _ _ (width_bound s (S.P γ) (S.Q γ)).2]
      simp only [map_mul,map_neg,map_pow,map_div₀,mul_pow,t,pow_add,v]
      rw [Nat.mul_comm 2 (m γ),pow_mul]
      simp only [e,m,neg_mul,mul_neg]
      exact congrArg Neg.neg (mul_mul_mul_comm _ _ _ _) }
  refine ⟨B,T,hd,rfl,rfl,move_height hE a s k A.d A.f,le_of_eq ?_⟩
  apply sum_congr rfl
  intro γ hγ
  change n γ=(B' γ).natDegree
  exact (rev_degree (width_bound (t γ) (S.num γ) (S.den γ)).2 (hfresh γ hγ)).symm
end
end qcYA6zd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qcYA6zd
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L)
open P5_7_7 (phys)
open qb0hmCe (cLN specialize zD)
open qNu3xvc (Equation Sections qg)

open scoped Classical WithZero
theorem proof :qJOpoVa.c1 := by
  intro D w U s z q J F V b hd hw
  let t:=J.u₁-J.u₀
  let E :=F.curve.E
  have hn:F.f.leadingCoeff.leadingCoeff=1 :=F.normalized
  obtain ⟨c,hc,hh,hreg⟩:=normalize F.curve.curve F.f hn (V.good.image F.place)
  let g:=nY c⁻¹ F.f
  have hc' : c⁻¹≠0:=inv_ne_zero hc
  have hg:g.natDegree=F.d:=natDegree_C_mul (C_ne_zero.mpr hc')
  have hi:Irreducible F.f :=
    (F.primitive.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing E[X])).mpr F.irreducible
  have hirr :Irreducible g:=(irreducible_isUnit_mul ((hc'.isUnit.map C).map C)).mpr hi
  have hpos :0<g.natDegree :=hg.symm ▸ (lt_of_lt_of_le (by decide :0<3) hd)
  have hwt (i:ℕ) : (g.coeff i).natDegree+i*t≤b+g.natDegree*t∨g.coeff i=0:= by
    by_cases hz :F.f.coeff i=0
    · exact Or.inr (by simp only [g,nY,coeff_C_mul,hz,mul_zero])
    have h:=hw i hz
    change (F.f.coeff i).natDegree+F.d*J.u₀+i*t≤b+F.d*(J.u₀+t) at h
    rw [Nat.mul_add] at h
    left
    rw [show g.coeff i=C c⁻¹*F.f.coeff i from coeff_C_mul _,natDegree_C_mul hc',hg]
    omega
  let A:Equation E :=⟨g,hirr,hpos,t,b,hwt⟩
  have hU (γ:K) (hγ:γ∈V.good) :γ∈U:=(mem_filter.mp (V.Bp hγ)).1
  let e (γ:K) (hγ:γ∈V.good) :=F.atPlace γ (hU γ hγ)
  have hR (γ:K) (hγ:γ∈V.good) :qg A (F.place γ) :=
    hreg _ (mem_image_of_mem _ hγ)
  have hsite (γ:K) (hγ:γ∈V.good) :
      (cLN (e γ hγ) 0 g).natDegree=A.d ∧
      ((cLN (e γ hγ) 0 g).map phys).Separable ∧
      specialize (cLN (e γ hγ) 0 g) (J.P γ) (J.Q γ)=0 ∧
      specialize (cLN (e γ hγ) 0 g).derivative (J.P γ) (J.Q γ)≠0 ∧
      phys (V.num γ)/phys (V.den γ)=zD (e γ hγ) g (J.P γ) (J.Q γ) := by
    let u:E :=F.scale γ
    let a :=e γ hγ
    let f :=nY u F.f
    have hmul :g=nY (c⁻¹*u⁻¹) f := by
      change C (C c⁻¹)*F.f=C (C (c⁻¹*u⁻¹))*(C (C u)*F.f)
      rw [← mul_assoc,← map_mul,← map_mul,mul_assoc,inv_mul_cancel₀ (F.scale γ).ne_zero,mul_one]
    have hint (i j:ℕ) : (F.place γ).value ((f.coeff i).coeff j)≤1 := by
      rw [gmm]
      exact F.integral γ (hU γ hγ) i j
    have hr :=F.root γ (hU γ hγ)
    obtain ⟨m,hm,h₀,hjet⟩:=transport_jet (F.place γ) a (F.value γ (hU γ hγ)) hmul hint
      (F.reduction_ne γ (hU γ hγ)) (hR γ hγ).2 (hR γ hγ).1 _ _ hr
    have hunit :=((hm.isUnit.map C).map phys).map (C:cu.FX →+* cu.FX[X])
    have heval (p:L[X][X]) :specialize (nY m p) (J.P γ) (J.Q γ) =
        phys (C m)*specialize p (J.P γ) (J.Q γ) := by
      simp only [specialize,nY,eval₂_mul,eval₂_C]
    have hs :=V.separable γ hγ
    change (cLN a 0 f).natDegree=F.d∧((cLN a 0 f).map phys).Separable at hs
    refine ⟨?_,?_,?_,?_,(V.formula γ hγ).trans hjet.symm⟩
    · rw [h₀,natDegree_C_mul (C_ne_zero.mpr hm),hs.1]
      exact hg.symm
    · rw [h₀,show nY m (cLN a 0 f)=C (C m)*cLN a 0 f from rfl,
        Polynomial.map_mul,map_C]
      exact hs.2.unit_mul hunit
    · rw [h₀,heval,hr,mul_zero]
    · rw [h₀,show nY m (cLN a 0 f)=C (C m)*cLN a 0 f from rfl,
        derivative_C_mul,heval]
      exact mul_ne_zero ((map_ne_zero_iff phys (IsFractionRing.injective L[X] cu.FX)).mpr (C_ne_zero.mpr hm)) (V.simple γ hγ)
  let S:Sections A := {
    marks :=V.good
    place :=F.place
    distinct := by
      intro γ hγ δ hδ he
      exact F.distinct (hU γ hγ) (hU δ hδ) he
    atPlace :=e
    value := fun γ hγ=>F.value γ (hU γ hγ)
    regular :=hR
    degree := fun γ hγ=>(hsite γ hγ).1
    separable := fun γ hγ=>(hsite γ hγ).2.1
    P:=J.P
    Q:=J.Q
    denom:= fun γ hγ=>J.denominator γ (hU γ hγ)
    coprime := fun γ hγ=>J.coprime γ (hU γ hγ)
    root := fun γ hγ=>(hsite γ hγ).2.2.1
    simple := fun γ hγ=>(hsite γ hγ).2.2.2.1
    num :=V.num
    den:=V.den
    den_ne :=V.den_ne
    reduced:=V.reduced
    formula := fun γ hγ=>(hsite γ hγ).2.2.2.2 }
  obtain ⟨B,T,hd',ht',hb',hh',hp⟩:=move_sections F.curve.curve A S
  exact ⟨B,T,hd'.trans hg,ht',hb',hh'.trans hh,hp⟩
end
end qcYA6zd
end
