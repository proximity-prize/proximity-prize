import ProximityPrize.SubmissionLower.ZGijG6c
import ProximityPrize.SubmissionLower.ZuJZkxc
import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.Zeo5Ibd
import ProximityPrize.SubmissionLower.ZiuGIoc
import ProximityPrize.SubmissionLower.ZvbAI4c
import ProximityPrize.SubmissionLower.ZfwYtia
import ProximityPrize.SubmissionLower.ZGcgEBb
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace q89Irde
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L FX j9)
open P5_7_7 (phys)
open P5_7_3_5_2 (atPolynomial)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (expansion_coeff)
open qNu3xvc (Equation Sections qg)
open qfJaLMa (cap choose_cap move move_coeff move_degree pad_bound move_irred changeY
 exp_ord_degree exp_move move_val_le move_height aJj)
open qWIOgVd (bY rev width width_bound rev_ne rev_coprime rev_ratio rev_degree x x_ne)
open private eval_change deriv_change cancel_ratio layer_repr from ProximityPrize.SubmissionLower.ZGijG6c
open scoped Classical WithZero
private theorem specialize_one (F:L[X][X]) (r :K[X]) :
  specialize F (j9 r) 1=atPolynomial F r := by
 simp [specialize,atPolynomial]
theorem proof :qZV9OWb.c1 := by
  intro q Cq z S₀ S V D W _ _ _ hDW hw hs hsep₀
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset
    (V.marks.biUnion fun γ=>(V.den γ).roots.toFinset)
  have hfresh (γ:K) (hγ:γ∈V.marks) : (V.den γ).eval a≠0:= fun hz =>
    ha (mem_biUnion.mpr ⟨γ,hγ,Multiset.mem_toFinset.mpr ((mem_roots (V.den_ne γ hγ)).mpr hz)⟩)
  let b:=W-S.d*D
  have hbW:b+S.d*D =W:=Nat.sub_add_cancel hDW
  have hpad (i:ℕ) : (S.f.coeff i).natDegree+i*D ≤b+S.d*D ∨S.f.coeff i=0:= by
    by_cases hn:S.f.coeff i=0
    · exact Or.inr hn
    exact Or.inl (by rw [hbW]; exact hw i hn)
  obtain ⟨k,hkb,hb,hhit⟩:=choose_cap S.irreducible.ne_zero D b hpad
  let M:=bY a
  let g:=move (algebraMap L Cq.E a) D k S.d S.f
  have hd:g.natDegree=S.d:=move_degree _ _ _ _ S.irreducible.ne_zero
  have hgwt (i:ℕ) : (g.coeff i).natDegree+i*D ≤b+g.natDegree*D ∨g.coeff i=0:= by
    by_cases hz :g.coeff i=0
    · exact Or.inr hz
    have hi:i≤S.d:=hd ▸ le_natDegree_of_ne_zero hz
    have hh: (g.coeff i).natDegree≤ cap D k S.d i:= by rw [move_coeff]; exact pad_bound _ (hb i)
    have he : (S.d-i)*D+i*D =S.d*D:= by rw [← add_mul,Nat.sub_add_cancel hi]
    rw [hd]
    unfold cap at hh
    exact Or.inl (by omega)
  let A:Equation Cq.E :=⟨g,move_irred S.irreducible S.positive hb hhit,hd.symm ▸ S.positive,
    D,b,hgwt⟩
  let P' (γ:K) :=rev a D (j9 (S₀ γ))
  let n (γ:K) :=width D (V.num γ) (V.den γ)
  let N' (γ:K) :=rev a (n γ+D) (V.num γ)
  let B' (γ:K) :=rev a (n γ) (V.den γ)
  let c:FX:=x^(k+S.d*D)
  let v :FX:=x^D
  have hc:c≠0:=pow_ne_zero _ x_ne
  have hv :v≠0:=pow_ne_zero _ x_ne
  let changeOrd:=changeY M.changeX v hv
  let e (γ:K) (hγ:γ∈V.marks) :=S.atPlace γ (V.Bp hγ)
  have repr (γ:K) (hγ:γ∈V.marks) (j:ℤ) :
      (cLN (e γ hγ) j g).map phys=C c*changeOrd ((cLN (e γ hγ) j S.f).map phys) :=
    layer_repr (e γ hγ) j M D k S.f hb
  have hdeg (γ:K) (hγ:γ∈V.marks) : (cLN (e γ hγ) 0 g).natDegree=S.d:= by
    have h₀: (cLN (e γ hγ) 0 S.f).coeff S.d≠0:= by
      intro hz
      have he :=expansion_coeff (e γ hγ) 0 S.f S.d (S.f.coeff S.d).natDegree
      rw [hz,coeff_zero,← leadingCoeff,S.normalized,map_one] at he
      simp [HahnSeries.coeff_one] at he
    rw [exp_move,move_degree _ _ _ _ (fun h=>h₀ (by rw [h,coeff_zero]))]
    exact (exp_ord_degree _ _ _).antisymm (le_natDegree_of_ne_zero h₀)
  have hval (γ:K) (hγ:γ∈V.marks) (i j:ℕ) :
      (S.place γ).value ((g.coeff i).coeff j)≤1 :=
    move_val_le _ a D k S.d S.f (S.integral γ (V.Bp hγ)) i j
  have hreg (γ:K) (hγ:γ∈V.marks) :qg A (S.place γ) := by
    refine ⟨hval γ hγ,?_⟩
    let F:=cLN (e γ hγ) 0 g
    have hF:F.natDegree=S.d:=hdeg γ hγ
    have hn:F.coeff S.d≠0:= by
      rw [← hF,← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr (fun h=>S.positive.ne' (hF.symm.trans (by rw [h,natDegree_zero])))
    refine ⟨S.d,(F.coeff S.d).natDegree,aJj (S.place γ) (e γ hγ) (S.value γ (V.Bp hγ) _)
      (hval γ hγ _ _) ?_⟩
    rw [← expansion_coeff,← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hn
  have hsep (γ:K) (hγ:γ∈V.marks) : ((cLN (e γ hγ) 0 g).map phys).Separable := by
    let F:=(cLN (e γ hγ) 0 S.f).map phys
    rw [repr γ hγ,separable_def,deriv_change]
    exact (isCoprime_mul_units_left (hc.isUnit.map C)
      ((mul_ne_zero hc (inv_ne_zero hv)).isUnit.map C) _ _).mpr
      (((separable_def F).mp (hsep₀ γ hγ)).map changeOrd.toRingHom)
  have hratio (γ:K) (hγ:γ∈V.marks) :
      phys (P' γ)=v*M.changeX (phys (j9 (S₀ γ))) :=
    M.CJ _ _ (natDegree_map_le.trans (hs γ hγ))
  have hsp (γ:K) (hγ:γ∈V.marks) (j:ℤ) :
      specialize (cLN (e γ hγ) j g) (P' γ) 1 =
        c*M.changeX (atPolynomial (cLN (e γ hγ) j S.f) (S₀ γ)) := by
    rw [← specialize_one]
    simp only [specialize,eval₂_eq_eval_map,map_one,div_one,hratio γ hγ,repr,eval_mul,eval_C]
    rw [eval_change]
  have hdsp (γ:K) (hγ:γ∈V.marks) :
      specialize (cLN (e γ hγ) 0 g).derivative (P' γ) 1 =
        (c*v⁻¹)*M.changeX (atPolynomial (cLN (e γ hγ) 0 S.f).derivative (S₀ γ)) := by
    rw [← specialize_one]
    simp only [specialize,eval₂_eq_eval_map,map_one,div_one,← derivative_map,hratio γ hγ,repr]
    rw [deriv_change M.changeX v hv,eval_mul,eval_C,eval_change]
  have hformula (γ:K) (hγ:γ∈V.marks) :
      phys (N' γ)/phys (B' γ)=zD (e γ hγ) g (P' γ) 1 := by
    change phys (rev a (width D (V.num γ) (V.den γ)+D) (V.num γ)) /
      phys (rev a (width D (V.num γ) (V.den γ)) (V.den γ))= _
    rw [rev_ratio M D,V.formula γ hγ]
    unfold zD
    rw [hsp γ hγ,hdsp γ hγ,cancel_ratio _ _ _ _ hc]
    simp only [e,map_one,one_pow,mul_one,map_neg,map_div₀,mul_neg,v]
  let T:Sections A := {
    marks :=V.marks
    place :=S.place
    distinct :=S.distinct.mono V.Bp
    atPlace :=e
    value := fun γ hγ=>S.value γ (V.Bp hγ)
    regular :=hreg
    degree := fun γ hγ=>(hdeg γ hγ).trans hd.symm
    separable :=hsep
    P:=P'
    Q:= fun _=>1
    denom:= fun _ _=>one_ne_zero
    coprime := fun _ _=>isCoprime_one_right
    root := fun γ hγ=> by rw [hsp γ hγ,S.root γ (V.Bp hγ),map_zero,mul_zero]
    simple := fun γ hγ=> by
      rw [hdsp γ hγ]
      exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero hv))
        ((map_ne_zero_iff _ M.changeX.injective).mpr (V.simple γ hγ))
    num :=N'
    den:=B'
    den_ne := fun γ hγ=>rev_ne a _ (V.den_ne γ hγ)
    reduced:= fun γ hγ=>rev_coprime a D (V.den_ne γ hγ) (V.reduced γ hγ)
    formula :=hformula }
  refine ⟨A,T,hd,rfl,?_,move_height Cq.curve a D k S.d S.f,rfl,rfl,
    fun _ _=>rfl,le_of_eq ?_⟩
  · change b+g.natDegree*D =W
    rw [hd,hbW]
  · apply sum_congr rfl
    intro γ hγ
    change n γ=(B' γ).natDegree
    exact (rev_degree (width_bound D (V.num γ) (V.den γ)).2 (hfresh γ hγ)).symm
end
end q89Irde
end
section
namespace qdVnFpc
theorem proof :qSHe4ub.c1 :=q89Irde.proof
end qdVnFpc
end
section
set_option autoImplicit true
namespace qBTeXSd
theorem proof :qSHe4ub.c2 :=
 qypA4Sc.of_children qWnROxa.proof
  qlcyGcd.proof qrrOjma.proof
end qBTeXSd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
namespace q53i3jb
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open E7 (CurvePlace)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (integralSeries residue fWQ expansion_coeff)
open P5_7_7 (phys)
open qqi5QRb (pointPrime pointVal)
open qNu3xvc
open qoCymac
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private chain from ProximityPrize.SubmissionLower.Z5cOcra
open private atY cK coeffIn from ProximityPrize.SubmissionLower.ZiuGIoc
open scoped WithZero Classical
variable {E :Type} [Field E] [Algebra L E]
private def red (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L)
  (h : ∀ c,w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)) :
  Integers w →+* L :=
 residue.comp ((a.toRingHom.comp (inc w)).codRestrict
  (LaurentSeries.powerSeries_as_subring L) fun c =>
    (integralSeries (a c) ((h c) ▸ c.property)).property)
@[simp] private theorem red_apply (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L) (h)
   (c:Integers w) :red w a h c=(a c).coeff 0:=fWQ _
private theorem coeff_pd {R:Type} [CommRing R] (f :R[X][X]) (i:ℕ) :
  (f.sum fun n b=>monomial n b.derivative).coeff i=(f.coeff i).derivative :=
 sum_coeff derivative (by simp) _ _
private theorem coeff_sd (δ:Derivation L E E) (f :E[X][X]) (i j:ℕ) :
  ((seedDerivative δ f).coeff i).coeff j=δ ((f.coeff i).coeff j) := by
 unfold seedDerivative
 rw [sum_coeff _ (by simp [Polynomial.sum_def])]
 exact sum_coeff _ (map_zero δ) _ _
private theorem aNu (F:L[X][X]) (P:L[X]) (h:F.eval P=0) :
   -((F.sum fun i b=>monomial i b.derivative).eval P) =
     P.derivative*F.derivative.eval P:= by
 let D:Derivation ℤ L[X] L[X] :=(Polynomial.derivative' (R:=L)).restrictScalars ℤ
 have hD (f :L[X]) :D f=f.derivative :=rfl
 have he :=chain D (RingHom.id L[X]) P F
 simp only [eval₂_id,RingHom.id_apply,h,map_zero,hD] at he
 rw [eval_sum]
 simp only [eval_monomial]
 have hz :=he.symm
 rw [add_comm] at hz
 exact (neg_eq_of_add_eq_zero_left hz).trans (mul_comm _ _)
private theorem spec_one (F:L[X][X]) (P:L[X]) :
  specialize F P 1=phys (F.eval P) := by
 rw [specialize,map_one,div_one,← eval₂_id,hom_eval₂,RingHom.comp_id]
theorem affine_specialization (A:Equation E) (S:Sections A) (γ:K) (hγ:γ∈S.marks)
    (δ:Derivation L E E) (hδ:LocalDerivation (S.atPlace γ hγ) (S.place γ) δ)
    (hQ:S.Q γ=1) (x :L) :
    Nonempty (MarkChart A S γ hγ δ x false) := by
  let w:=S.place γ
  let a :=S.atPlace γ hγ
  let R:=red w a (S.value γ hγ)
  let P:=S.P γ
  let F:=cLN a 0 A.f
  let g:=liftIn w A.f (S.regular γ hγ).1
  let gd:=g.derivative
  have hnat (j:ℕ) :w.value (j:E)≤1 := by
    induction j with
    | zero=>simp
    | succ j ih =>
      rw [Nat.cast_succ]
      exact (w.value.map_add _ _).trans (max_le ih (by rw [map_one]))
  have hdb (i j:ℕ) :w.value (((physicalDerivative A.f).coeff i).coeff j)≤1 := by
    rw [physicalDerivative,coeff_pd,coeff_derivative,map_mul]
    exact mul_le_one' ((S.regular γ hγ).1 i (j+1)) (by
      simpa only [Nat.cast_add,Nat.cast_one] using hnat (j+1))
  let b:=liftIn w (physicalDerivative A.f) hdb
  have hnb (i j:ℕ) :w.value (((seedDerivative δ A.f).coeff i).coeff j)≤1 := by
    rw [coeff_sd]
    exact (hδ _ ((S.regular γ hγ).1 i j)).1
  let n:=liftIn w (seedDerivative δ A.f) hnb
  have hg:map₂ (inc w) g=A.f :=map_liftIn _ _ _
  have hb:map₂ (inc w) b=physicalDerivative A.f :=map_liftIn _ _ _
  have hn:map₂ (inc w) n=seedDerivative δ A.f :=map_liftIn _ _ _
  have hgd:map₂ (inc w) gd=A.f.derivative := by
    change g.derivative.map (mapRingHom (inc w))= _
    rw [← derivative_map]
    exact congrArg derivative hg
  have hR (c:L) :R ⟨algebraMap L E c,by
        change w.value (algebraMap L E c)≤1
        by_cases hc:c=0
        · simp [hc]
        · exact (w.on_constants c hc).le⟩=c:= by
    simp only [R,red_apply,a.commutes,LaurentSeries.algebraMap_apply]
    simp
  have hG:g.map (mapRingHom R)=F:= by
    ext i j
    simp only [coe_mapRingHom,coeff_map,R,red_apply,g,coeff_liftIn,F,expansion_coeff]
  have hB:b.map (mapRingHom R)=F.sum fun i q=>monomial i q.derivative := by
    ext i j
    simp only [coe_mapRingHom,coeff_map,R,red_apply,b,coeff_liftIn,F,expansion_coeff,
      physicalDerivative,coeff_pd,coeff_derivative,map_mul]
    have hc:a ((j:E)+1)=HahnSeries.C ((j:L)+1) := calc
      _=a (algebraMap L E ((j:L)+1)) := by simp
      _ = _:=(a.commutes _).trans (LaurentSeries.algebraMap_apply L _)
    rw [hc,mul_comm,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,mul_comm]
  have hN :n.map (mapRingHom R)=cLN a 1 A.f := by
    ext i j
    simp only [coe_mapRingHom,coeff_map,R,red_apply,n,coeff_liftIn,
      expansion_coeff,coeff_sd]
    exact (hδ _ ((S.regular γ hγ).1 i j)).2
  have hD:gd.map (mapRingHom R)=F.derivative := by
    change g.derivative.map (mapRingHom R)= _
    rw [← derivative_map]
    exact congrArg derivative hG
  have hroot :F.eval P=0:= by
    apply IsFractionRing.injective L[X] FX
    rw [map_zero]
    change phys (F.eval P)=0
    rw [← spec_one]
    simpa only [hQ] using S.root γ hγ
  have hs :F.derivative.eval P≠0:= fun e=>S.simple γ hγ (by
    rw [hQ,spec_one]
    change phys (F.derivative.eval P)=0
    rw [e,map_zero])
  obtain ⟨φ,hφ,hj⟩:=affine_map A w g b gd hg
    (by simpa only [g,coeff_liftIn] using (S.regular γ hγ).2)
    hb hgd R P hR
    (by rwa [eval₂_eq_eval_map,hG])
    (by rwa [eval₂_eq_eval_map,hD])
    (by simp only [eval₂_eq_eval_map,hB,hD]; exact aNu F P hroot)
  have se (c:Integers w) :φ (aee A w false c)=algebraMap L FX (R c) := by
    have hc:coeffIn A w c=aee A w false c:=rfl
    rw [IsScalarTower.algebraMap_apply L L[X] FX]
    change φ (aee A w false c)=phys (C (R c))
    simpa only [evalIn,coe_eval₂RingHom,eval₂_C,coe_mapRingHom,map_C,hc] using hφ (C (C c))
  have xx :φ (xAt A w false)=phys Polynomial.X:= by
    simpa [evalIn] using hφ (C Polynomial.X)
  have yy :φ (atY A w)=phys P:= by simpa [evalIn] using hφ Polynomial.X
  have ple (g:L[X]) :pointVal x (phys g)≤1 :=(pointPrime x).valuation_le_one (K:=FX) g
  have reg (u:Chart A w false) :pointVal x (φ u)≤1 := by
    obtain ⟨u,hu⟩:=u
    induction hu using Algebra.adjoin_induction with
    | mem u hu =>
      rcases hu with ⟨c,rfl⟩ | hu
      · change pointVal x (φ (aee A w false c))≤1
        rw [se,IsScalarTower.algebraMap_apply L L[X] FX]
        exact ple _
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · change pointVal x (φ (xAt A w false))≤1
          rw [xx]; exact ple _
        · change pointVal x (φ (atY A w))≤1
          rw [yy]; exact ple _
        · change pointVal x (φ (cK A w))≤1
          rw [hj]; exact ple _
    | algebraMap c =>
      rw [show φ ⟨algebraMap L _ c,_⟩=φ (algebraMap L _ c) from rfl,
        AlgHom.commutes,IsScalarTower.algebraMap_apply L L[X] FX]
      exact ple _
    | add u v hu₀ hv₀ hu hv =>
      change pointVal x (φ ((⟨u,hu₀⟩:Chart A w false) + ⟨v,hv₀⟩))≤1
      rw [map_add]
      exact ((pointVal x).map_add _ _).trans (max_le hu hv)
    | mul u v hu₀ hv₀ hu hv =>
      change pointVal x (φ ((⟨u,hu₀⟩:Chart A w false)*⟨v,hv₀⟩))≤1
      rw [map_mul φ,map_mul (pointVal x)]
      exact mul_le_one' hu hv
  refine ⟨{
    map :=φ
    regular :=reg
    seed_eq := fun c=>(se c).trans (congrArg (algebraMap L FX) (red_apply w a _ c))
    physical_eq :=xx
    sep:=evalIn A w gd
    num := -evalIn A w n
    sep_eq := by rw [coe_evalIn,hgd,polar,eval_false]; rfl
    num_eq := by rw [Subalgebra.coe_neg,coe_evalIn,hn,eval_false]; rfl
    simple := by
      rw [hφ,eval₂_eq_eval_map,hD]
      exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr hs
    gK6 := ?_ }⟩
  refine ⟨1,map_one _,?_⟩
  rw [one_mul,S.formula γ hγ,zD,hQ,map_one,one_pow,mul_one,map_neg,hφ,hφ,
    eval₂_eq_eval_map,eval₂_eq_eval_map,hN,hD,spec_one,spec_one,neg_div]
end
end q53i3jb
end
section
namespace q53i3jb
noncomputable section
open Polynomial
open qqi5QRb (pointVal)
open qNu3xvc
open qoCymac
open private val_poly_lt from ProximityPrize.SubmissionLower.ZsE91Ed
open private center bsx integral_specializes mark_phys specialized_pole restriction charge_order from ProximityPrize.SubmissionLower.Zdj6KNe
open scoped Classical
def c1 :Prop :=qoCymac.c1
def c2 :Prop :=qoCymac.c3
def c3:Prop :=qoCymac.c4
def c4 :Prop :=qoCymac.c5
def c5:Prop :=qoCymac.c6
theorem of_children (h1 :c1) (h3:c2) (h4 :c3) (h5:c4) (h6:c5) :
   qZV9OWb.c3:= by
 intro E _ _ A S hcurve hd hp Oj γ hγ hQ x hx
 let w:=S.place γ
 obtain ⟨δ,hδ⟩:=h1 w (S.atPlace γ hγ) hcurve (S.value γ hγ)
 obtain ⟨T⟩:=affine_specialization A S γ hγ δ hδ hQ x
 let k :=(S.den γ).rootMultiplicity x
 let m:=k-1
 let b:=(xSub A w false x)^m*T.num
 let u:EC A:=(b:EC A)/T.sep
 let M:=center T
 have hx' := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
 have hk :0<k :=(rootMultiplicity_pos (S.den_ne γ hγ)).mpr hx'
 have hmark :1<pointVal x (T.map b/T.map T.sep) :=
   specialized_pole T hx' (by change k-1<k; omega)
 have hnon (a :Chart A w false) (ha :a∉M) : ¬ IsIntegral (Chart A w false) ((a :EC A)*u) := by
   intro hi
   have hval :pointVal x (T.map a)=1 :=
     le_antisymm (T.regular a) (le_of_not_gt (fun h=>ha ((bsx T a).mpr h)))
   have h' := integral_specializes T (a*b) T.sep T.simple
     (by simpa only [u,Subalgebra.coe_mul,mul_div_assoc] using hi)
   rw [map_mul,mul_div_assoc,map_mul,hval,one_mul] at h'
   exact hmark.not_ge h'
 obtain ⟨hnoeth,hfin⟩:=h4 A w hcurve false
 obtain ⟨P,hP,hht,hPM,hnonP⟩:=h5 A w false hnoeth M u hnon
 obtain ⟨v,hbounded,hv,hreg,hcurveRes⟩:=h6 A w hcurve false hnoeth hfin P hP hht
 have hu:u=(amm A - constant A x)^m*variation A false δ:= by
   simp only [u,b,Subalgebra.coe_mul,Subalgebra.coe_pow,coe_xSub,variation,T.sep_eq,
     T.num_eq,mul_div_assoc]
 have hlarge :1<v.val ((amm A - constant A x)^m*variation A false δ) := by
   rw [← hu]
   exact lt_of_not_ge (fun h=>hnonP ((hreg u).mp h))
 have hvar :1<v.val (variation A false δ) := by
   refine hlarge.trans_le ?_
   rw [map_mul,map_pow]
   exact mul_le_of_le_one_left' (pow_le_one₀ zero_le (coe_xSub A w false x ▸ hbounded (xSub A w false x)))
 have hsep:polar A false≠0:= fun e=>T.simple (by
   rw [show T.sep=0 from Subtype.ext (T.sep_eq.trans e),map_zero])
 have hpolar :v.val (polar A false)<1 := by
   rw [variation,← T.num_eq,map_div₀] at hvar
   exact ((one_lt_div₀ (v.val.pos_iff.mpr hsep)).mp hvar).trans_le (hbounded T.num)
 have hscale :=restriction v w hbounded (fun h=>hvar.not_ge (Oj false v δ h))
 obtain ⟨y,hy⟩:=h3 A S γ hγ hd hp false v hscale hpolar
 have hxy :=(bsx T (xSub A w false y)).mp
   (hPM ((hv _).mp (by rwa [coe_xSub])))
 rw [mark_phys,val_poly_lt,IsRoot.def,eval_sub,eval_X,eval_C,sub_eq_zero] at hxy
 have hsmall:v.val (amm A - constant A x)<1 :=hxy ▸ hy
 have hcharge :=charge_order v T hsmall (hbounded T.num) hsep hlarge
 exact ⟨v,⟨hscale,hsmall,hcurveRes hscale ⟨x,hsmall⟩⟩,by change k≤poleCharge v; omega⟩
end
end q53i3jb
end
section
namespace qbqCJve
def c1 :Prop :=qoCymac.c4
def c2 :Prop :=qoCymac.c6
theorem of_children (finite :c1) (valuation :c2) :qSHe4ub.c3 :=
 q53i3jb.of_children q5eiIAb.proof qvOlzpd.proof
  finite qpI7nyd.proof valuation
end qbqCJve
end
