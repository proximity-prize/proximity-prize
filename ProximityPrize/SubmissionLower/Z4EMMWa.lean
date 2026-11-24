import ProximityPrize.SubmissionLower.Zf9vSCd
import ProximityPrize.SubmissionLower.Zi3GgJd
import ProximityPrize.SubmissionLower.ZT8CHOb
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import ProximityPrize.SubmissionLower.ZvbAI4c
import ProximityPrize.SubmissionLower.ZhEC96c
import ProximityPrize.SubmissionLower.ZgKNZbc
import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.Zeo5Ibd
import ProximityPrize.SubmissionLower.ZhNzRYc
import ProximityPrize.SubmissionLower.Zqop1Ec
import ProximityPrize.SubmissionLower.ZvFqJTb
import ProximityPrize.SubmissionLower.ZHTtOyb
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZNiHFkd
import ProximityPrize.SubmissionLower.ZZpExZa
set_option Elab.async false
open _root_ renaming AlgHom.coe_toRingHom → zlv, AlgHom.toRingHom_eq_coe → ziQ, Algebra → zZE, Field → zrb, Function.Injective → zq4, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.ext → zXJ, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, RingHom.comp_apply → zQb, RingHom.ker → zdq, RingHom.mem_ker → zry, Set.range → zxp, Submodule.span → zLD
section
section
set_option maxSynthPendingDepth 12
namespace qIGP9Qa
open qNu3xvc qoCymac
theorem proof :qoCymac.c6:= by
 classical
 intro E _ _ A w hE r hN hfin P hP hp
 have :IsNoetherianRing (Normal A w r) :=hN
 have :Module.Finite (Chart A w r) (Normal A w r) :=hfin
 have :P.IsPrime :=hP
 obtain ⟨v,hbounded,hcenter,hreg⟩:=graphValuation A w r P hp
 refine ⟨v,hbounded,hcenter,hreg,fun hscale hx => ?_⟩
 by_contra h
 push Not at h
 obtain ⟨hy,hj⟩:=h
 have hheight:=normalClosedHeight A w hE r P
  (quotientConstants A w hE r P v hcenter hscale hx hy hj)
 rw [hp] at hheight
 exact (by decide : ¬ (2 :ℕ∞)≤1) hheight
end qIGP9Qa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qQKkxDd
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open qZu9hjc (Chart HE)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (expansion_coeff)
open qfJaLMa (cap choose_cap move move_coeff move_degree pad_bound move_irred move_repr
 exp_move exp_ord_degree exp_phys_degree move_val_le move_height changeY)
open qWIOgVd (bY rev width width_bound rev_ne rev_coprime rev_ratio rev_degree
 scaleY scaleY_apply x x_ne)
open scoped Classical
private theorem eval_change {F:Type*} [zrb F] (D:F ≃+* F) (v :F) (hv :v≠0)
  (f :F[X]) (t:F) :
  (changeY D v hv f).eval (v*D t)=D (f.eval t) := by
 change (scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.map D.toRingHom)).eval _ = _
 rw [scaleY_apply,eval_comp,eval_mul,eval_C,eval_X,← mul_assoc,inv_mul_cancel₀ hv,one_mul]
 exact eval_map_apply (p:=f) D.toRingHom t
private theorem deriv_change {F:Type*} [zrb F] (D:F ≃+* F) (v :F) (hv :v≠0)
  (m:F) (f :F[X]) :
  (C m*changeY D v hv f).derivative=C (m*v⁻¹)*changeY D v hv f.derivative := by
 change (C m*scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.map D.toRingHom)).derivative =
  C (m*v⁻¹)*scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.derivative.map D.toRingHom)
 rw [derivative_C_mul,scaleY_apply,derivative_comp,derivative_C_mul_X,scaleY_apply,
  derivative_map,map_mul]
 ac_rfl
private theorem cancel_ratio {F:Type*} [zrb F] (m a b v :F) (hm:m≠0) :
  (m*a)/((m*v⁻¹)*b)=v*(a/b) := by
 rw [mul_assoc m,mul_div_mul_left _ _ hm,inv_mul_eq_div,div_div_eq_mul_div,mul_comm a v,
  mul_div_assoc]
private theorem layer_repr {E :Type} [zrb E] [zZE L E]
    (e :E →ₐ[L] LaurentSeries L) (j:ℤ) {a :L} (D:qWIOgVd.Chart a)
    (s b:ℕ) (f :E[X][X]) (hb : ∀ i,(f.coeff i).natDegree≤ cap s b f.natDegree i) :
    (cLN e j (move (algebraMap L E a) s b f.natDegree f)).map phys =
      C (x^(b+f.natDegree*s)) *
        changeY D.changeX (x^s) (pow_ne_zero _ x_ne) ((cLN e j f).map phys) := by
  rw [exp_move]
  exact move_repr a D.changeX D.CJ s b f.natDegree _ (exp_ord_degree e j f)
    (fun i=>(exp_phys_degree e j f i).trans (hb i))
theorem proof :qZu9hjc.c1 := by
  intro J U B q Cq S a
  let s :=B.u₁-B.u₀
  change 2≤S.d→S.d*s≤a→HE S.f s a→Nonempty (Chart S s a)
  intro _ ha hw
  obtain ⟨r,hr⟩:=Infinite.exists_notMem_finset
    (S.marks.biUnion fun γ=>(S.den γ).roots.toFinset)
  have hfresh (γ:K) (hγ:γ∈S.marks) : (S.den γ).eval r≠0:= fun hz =>
    hr (mem_biUnion.mpr ⟨γ,hγ,Multiset.mem_toFinset.mpr ((mem_roots (S.den_ne γ hγ)).mpr hz)⟩)
  let b:=a-S.d*s
  have hab:b+S.d*s=a :=zxt ha
  obtain ⟨k,hkb,hb,hhit⟩:=choose_cap S.irreducible.ne_zero s b fun i=> by
    rw [hab]
    exact or_iff_not_imp_right.mpr (hw i)
  let D:=bY r
  let g:=move (algebraMap L Cq.E r) s k S.d S.f
  have hd:g.natDegree=S.d:=move_degree _ _ _ _ S.irreducible.ne_zero
  have hgwt:HE g s a := by
    intro i hi
    have hid :i≤S.d:=hd ▸ le_natDegree_of_ne_zero hi
    have hh: (g.coeff i).natDegree≤ cap s k S.d i:= by rw [move_coeff]; exact pad_bound _ (hb i)
    have he : (S.d-i)*s+i*s=S.d*s := by rw [← add_mul,zxt hid]
    unfold cap at hh
    omega
  let m (γ:K) :=width s (B.P γ) (B.Q γ)
  let t (γ:K) :=s+2*m γ
  let n (γ:K) :=width (t γ) (S.num γ) (S.den γ)
  let P' (γ:K) :=rev r (m γ+s) (B.P γ)
  let Q' (γ:K) :=rev r (m γ) (B.Q γ)
  let N' (γ:K) :=rev r (n γ+t γ) (S.num γ)
  let B' (γ:K) :=rev r (n γ) (S.den γ)
  let c:FX:=x^(k+S.d*s)
  let v :FX:=x^s
  have hc:c≠0:=pow_ne_zero _ x_ne
  have hv :v≠0:=pow_ne_zero _ x_ne
  let changeOrd:=changeY D.changeX v hv
  let e :=S.atPlace
  have repr (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      (cLN (e γ hγ) j g).map phys=C c*changeOrd ((cLN (e γ hγ) j S.f).map phys) :=
    layer_repr (e γ hγ) j D s k S.f hb
  have hdeg (γ:K) (hγ:γ∈S.marks) : (cLN (e γ hγ) 0 g).natDegree=S.d:= by
    have h₀: (cLN (e γ hγ) 0 S.f).coeff S.d≠0:= by
      intro hz
      have he :=expansion_coeff (e γ hγ) 0 S.f S.d (S.f.coeff S.d).natDegree
      rw [hz,coeff_zero,← leadingCoeff,S.normalized,map_one] at he
      simp [HahnSeries.coeff_one] at he
    rw [exp_move,move_degree _ _ _ _ (fun h=>h₀ (by rw [h,coeff_zero]))]
    exact (exp_ord_degree _ _ _).antisymm (le_natDegree_of_ne_zero h₀)
  have hsep (γ:K) (hγ:γ∈S.marks) : ((cLN (e γ hγ) 0 g).map phys).Separable := by
    let F:=(cLN (e γ hγ) 0 S.f).map phys
    rw [repr,separable_def,deriv_change]
    exact (isCoprime_mul_units_left (hc.isUnit.map C)
      ((mul_ne_zero hc (inv_ne_zero hv)).isUnit.map C) _ _).mpr
      (((separable_def F).mp (S.separable γ hγ)).map changeOrd.toRingHom)
  have hratio (γ:K) :phys (P' γ)/phys (Q' γ) =
      v*D.changeX (phys (B.P γ)/phys (B.Q γ)) :=rev_ratio D s
  have hsp (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      specialize (cLN (e γ hγ) j g) (P' γ) (Q' γ) =
        c*D.changeX (specialize (cLN (e γ hγ) j S.f) (B.P γ) (B.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,hratio,repr,eval_mul,eval_C]
    rw [eval_change]
  have hdsp (γ:K) (hγ:γ∈S.marks) :
      specialize (cLN (e γ hγ) 0 g).derivative (P' γ) (Q' γ) =
        (c*v⁻¹)*D.changeX (specialize (cLN (e γ hγ) 0 S.f).derivative (B.P γ) (B.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,← derivative_map,hratio,repr]
    rw [deriv_change D.changeX v hv,eval_mul,eval_C,eval_change]
  refine ⟨{
    f :=g
    irreducible :=move_irred S.irreducible S.positive hb hhit
    degree :=hd
    weight:=hgwt
    height:=move_height Cq.curve r s k S.d S.f
    integral:= fun γ hγ i j=>move_val_le _ r s k S.d S.f (S.integral γ hγ) i j
    P:=P'
    Q:= Q'
    denom:= fun γ hγ=>rev_ne r _ (B.denominator γ (S.Bp hγ))
    coprime := fun γ hγ=>rev_coprime r s (B.denominator γ (S.Bp hγ)) (B.coprime γ (S.Bp hγ))
    fWS:=hdeg
    root := fun γ hγ=> by rw [hsp,S.root γ hγ,map_zero,mul_zero]
    separable :=hsep
    simple := fun γ hγ=> by
      rw [hdsp]
      exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero hv))
        ((map_ne_zero_iff _ D.changeX.injective).mpr (S.simple γ hγ))
    num :=N'
    den:=B'
    den_ne := fun γ hγ=>rev_ne r _ (S.den_ne γ hγ)
    reduced:= fun γ hγ=>rev_coprime r _ (S.den_ne γ hγ) (S.reduced γ hγ)
    formula := fun γ hγ=> by
      change phys (N' γ)/phys (B' γ)=zD (e γ hγ) g (P' γ) (Q' γ)
      have hform :phys (S.num γ)/phys (S.den γ) =
          zD (e γ hγ) S.f (B.P γ) (B.Q γ) :=S.formula γ hγ
      rw [rev_ratio D (t γ),hform]
      unfold zD
      rw [hsp,hdsp,cancel_ratio _ _ _ _ hc,show Q' γ=rev r (m γ) (B.Q γ) from rfl,
        D.CJ _ _ (width_bound s (B.P γ) (B.Q γ)).2]
      simp only [map_mul,map_neg,map_pow,map_div₀,mul_pow,t,pow_add,v]
      rw [Nat.mul_comm 2 (m γ),pow_mul]
      simp only [e,m,neg_mul,mul_neg]
      exact congrArg Neg.neg (mul_mul_mul_comm _ _ _ _)
    moved:= fun γ hγ=> by
      change n γ≤(B' γ).natDegree
      exact (rev_degree (width_bound (t γ) (S.num γ) (S.den γ)).2 (hfresh γ hγ)).ge }⟩
end
end qQKkxDd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrGSFbd
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open qe6nVeb (Input DualWord SeedPlane)
open qE3Ebna (Sheet)
open qZu9hjc (Chart discrDegree)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (expansion_coeff)
open qfJaLMa (aJj)
open qNu3xvc (Equation Sections GraphVal horizontalDegree Over poleCharge)


open scoped Classical WithZero
variable {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {Cq:CurveModel q}
 {S:Sheet B Cq} {s a :ℕ}
def equation (R:Chart S s a) (cfw:S.d*s≤a) :Equation Cq.E where
  f :=R.f
  irreducible :=R.irreducible
  positive :=R.degree.symm ▸ S.positive
  s :=s
  b:=a-S.d*s
  weight i:= by
    by_cases h:R.f.coeff i=0
    · exact Or.inr h
    · exact Or.inl (by rw [R.degree,zxt cfw]; exact R.weight i h)
theorem equation_weight (R:Chart S s a) (cfw:S.d*s≤a) :
  (equation R cfw).b+(equation R cfw).d*s=a := by
 change a-S.d*s+R.f.natDegree*s=a
 rw [R.degree,zxt cfw]
theorem guard (R:Chart S s a) (cfw:S.d*s≤a) (hd:2≤S.d)
   (h:discrDegree S.d a s<(p:ℤ)) :horizontalDegree (equation R cfw)<p:= by
 have he : (horizontalDegree (equation R cfw) :ℤ)=discrDegree S.d a s := by
   change (↑((2*R.f.natDegree-2)*(a-S.d*s)+R.f.natDegree*(R.f.natDegree-1)*s) :ℤ)= _
   rw [R.degree]
   unfold discrDegree
   push_cast [Nat.cast_sub cfw,Nat.cast_sub (show 2≤2*S.d by omega),
     Nat.cast_sub (show 1≤S.d by omega)]
   ring
 rw [← he] at h
 exact_mod_cast h
def sections (R:Chart S s a) (cfw:S.d*s≤a) :Sections (equation R cfw) where
  marks :=S.marks
  place :=S.place
  distinct :=S.distinct
  atPlace :=S.atPlace
  value :=S.value
  regular := by
    intro γ hγ
    refine ⟨R.integral γ hγ,?_⟩
    let F:=cLN (S.atPlace γ hγ) 0 R.f
    have hd:F.natDegree=S.d:=R.fWS γ hγ
    have hn:F≠0:= fun hz=>S.positive.ne' (hd.symm.trans (hz ▸ natDegree_zero))
    let i:=F.natDegree
    let j:=(F.coeff i).natDegree
    refine ⟨i,j,aJj (S.place γ) (S.atPlace γ hγ) (S.value γ hγ _)
      (R.integral γ hγ i j) ?_⟩
    rw [← expansion_coeff]
    change (F.coeff i).leadingCoeff≠0
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
  degree := fun γ hγ=>(R.fWS γ hγ).trans R.degree.symm
  separable :=R.separable
  P:=R.P
  Q:=R.Q
  denom:=R.denom
  coprime :=R.coprime
  root :=R.root
  simple :=R.simple
  num :=R.num
  den:=R.den
  den_ne :=R.den_ne
  reduced:=R.reduced
  formula :=R.formula
open private same_center from ProximityPrize.SubmissionLower.ZT8CHOb
theorem local_sum {E :Type} [zrb E] [zZE L E] {A:Equation E} (T:Sections A)
    (γ:K) (r : ↥(T.den γ).roots.toFinset→Bool) (v : ∀ x,GraphVal A (r x))
    (h : ∀ x,Over (v x) (T.place γ) x.1∧(T.den γ).rootMultiplicity x.1≤poleCharge (v x)) :
    zq4 (fun x=>(v x).val) ∧
      (T.den γ).natDegree ≤ ∑ x,poleCharge (v x) := by
  refine ⟨fun x y he=>Subtype.ext (same_center (h x).1 (h y).1 he),?_⟩
  calc
    _ = ∑ x : ↥(T.den γ).roots.toFinset,(T.den γ).rootMultiplicity x.1 := by
      rw [← IsAlgClosed.card_roots_eq_natDegree]
      change _ = ∑ x∈(T.den γ).roots.toFinset.attach,(T.den γ).rootMultiplicity x.1
      rw [Finset.sum_attach ((T.den γ).roots.toFinset) (fun x=>(T.den γ).rootMultiplicity x),
        ← Multiset.toFinset_sum_count_eq]
      exact sum_congr rfl fun _ _=>count_roots _
    _≤_:=sum_le_sum fun x _=>(h x).2
end
end qrGSFbd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qPfoxUd
noncomputable section
open HahnSeries qps5rle qymFiQe
open P5 (K p)
open cu (L)
private def multiples (q:ℕ) (a :SeedSeries) :SeedSeries :=
 ⟨fun j=>if (q:ℤ)∣j then a.coeff j else 0,
   a.isPWO_support.mono (fun j hj ha=>hj (by
    change (if (q:ℤ)∣j then a.coeff j else 0)=0
    rw [ha,ite_self]))⟩
private def cut {q:ℕ} (i:Fin q) :ZeroHom SeedSeries SeedSeries where
 toFun a :=multiples q (single (-(i:ℤ)) 1*a)
 map_zero' := by
  apply HahnSeries.ext
  funext j
  simp [multiples]
private theorem cut_coeff {q:ℕ} (i:Fin q) (a :SeedSeries) (j:ℤ) :
   (cut i a*single (i:ℤ) 1).coeff j =
     if (q:ℤ)∣j-(i:ℤ) then a.coeff j else 0:= by
 rw [coeff_mul_single,mul_one]
 change (if (q:ℤ)∣j-(i:ℤ) then
   (single (-(i:ℤ)) 1*a).coeff (j-(i:ℤ)) else 0)= _
 rw [coeff_single_mul,one_mul,sub_neg_eq_add,sub_add_cancel]
private theorem cut_sum {q:ℕ} (hq:0<q) (a :SeedSeries) :
   a = ∑ i:Fin q,cut i a*single (i:ℤ) 1 := by
 apply HahnSeries.ext
 funext j
 simp only [coeff_sum,cut_coeff]
 have hp: (0:ℤ)<(q:ℤ) := by exact_mod_cast hq
 have h₀:=Int.emod_nonneg j hp.ne'
 have h₁:=Int.emod_lt_of_pos j hp
 let r :Fin q:=⟨(j % (q:ℤ)).toNat,(Int.toNat_lt h₀).mpr h₁⟩
 have hr : (r :ℤ)=j % (q:ℤ) :=Int.toNat_of_nonneg h₀
 have h (i:Fin q) : ((q:ℤ)∣j-(i:ℤ))↔i=r := by
   rw [← Int.modEq_iff_dvd]
   change (i:ℤ) % (q:ℤ)=j % (q:ℤ)↔i=r
   rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le (i:ℕ))
     (by exact_mod_cast i.isLt),← hr]
   exact ⟨fun he=>Fin.ext (by exact_mod_cast he),fun he=> by rw [he]⟩
 simp only [h,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
private def physicalCut {q:ℕ} (i:Fin q) (a :F) :F:=a.map (cut i)
private theorem physical_sum {q:ℕ} (hq:0<q) (a :F) :
  a = ∑ i:Fin q,physicalCut i a*seed^(i:ℕ) := by
 have hz (i:ℕ) :seed^i=(single 0 (single (i:ℤ) 1 :SeedSeries) :F) := by
  rw [seed,← map_pow,LaurentSeries.algebraMap_apply,HahnSeries.single_pow,one_pow,
    nsmul_eq_mul,mul_one]
  rfl
 apply HahnSeries.ext
 funext j
 simp only [hz,coeff_sum,coeff_mul_single_zero,physicalCut,HahnSeries.map_coeff]
 exact cut_sum hq (a.coeff j)
private theorem cut_constant {D:Derivation ℤ F F} (hD:coefficientwise D) (a :F) (i:Fin p) :
   physicalCut i a∈constants D:= by
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 change D (physicalCut i a)=0
 apply HahnSeries.ext
 funext j
 rw [hD,coeff_zero]
 apply HahnSeries.ext
 funext k
 rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,Ring.choose_one_right,
   coeff_zero]
 change (k+1)•(multiples p (single (-(i:ℤ)) 1*a.coeff j)).coeff (k+1)=0
 rw [zsmul_eq_mul]
 by_cases hk : (p:ℤ)∣k+1
 · rw [(CharP.intCast_eq_zero_iff L p _).mpr hk,zero_mul]
 · change ((k+1 :ℤ) :L)*(if (p:ℤ)∣k+1 then _ else 0)=0
   simp only [hk,ite_false,mul_zero]
private theorem pth_span (w:Roots) (hw:IsSeparable F w) :
   zLD F (zxp (fun b:Simple w=>b^p)) = ⊤ := by
 let f :=((algebraMap SeedSeries F).comp (algebraMap L SeedSeries)).comp (algebraMap K L)
 let:ExpChar F p:=expChar_of_injective_ringHom f.injective p
 let:Algebra.IsSeparable F (Simple w) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hw
 simpa only [pow_one,id_eq] using
   Field.span_map_pow_expChar_pow_eq_top_of_isSeparable p 1 (v :=id (α:=Simple w))
     (by rw [Set.range_id,Submodule.span_univ])
private theorem extend_span {A E :Type} [zrb A] [zrb E] [zZE A E]
   (q:ℕ) (S:Subfield E) (z :E)
   (hbase : ∀ b:A,∃ c:Fin q→S,algebraMap A E b = ∑ i,(c i:E)*z^(i:ℕ))
   (hpow : ∀ e :E,e^q∈S)
   (hspan:zLD A (zxp (fun e :E=>e^q)) = ⊤) (a :E) :
   ∃ c:Fin q→S,a = ∑ i,(c i:E)*z^(i:ℕ) := by
 let f :=algebraMap A E
 let M:=zLD S (zxp (fun i:Fin q=>z^(i:ℕ)))
 have h:a∈zLD A (zxp (fun e :E=>e^q)) := by
   rw [hspan]
   trivial
 have hmul : ∀ b:A,f b*a∈M:= by
   induction h using Submodule.span_induction with
   | mem x hx =>
     obtain ⟨e,rfl⟩:=hx
     intro b
     obtain ⟨c,hc⟩:=hbase b
     change f b= _ at hc
     rw [hc,Finset.sum_mul]
     apply Submodule.sum_mem
     intro i _
     rw [mul_right_comm]
     exact M.smul_mem ⟨_,S.mul_mem (c i).property (hpow e)⟩ (Submodule.subset_span ⟨i,rfl⟩)
   | zero=>intro b; rw [mul_zero]; exact M.zero_mem
   | add x y _ _ hx hy=>intro b; rw [mul_add]; exact M.add_mem (hx b) (hy b)
   | smul r x _ hx =>
     intro b
     rw [Algebra.smul_def,← mul_assoc]
     change f b*f r*x∈M
     rw [← map_mul]
     exact hx (b*r)
 have ha :a∈M:= by simpa only [f,map_one,one_mul] using hmul 1
 obtain ⟨c,hsum⟩:=(Submodule.mem_span_range_iff_exists_fun S).mp ha
 exact ⟨c,hsum.symm⟩
theorem proof :qymFiQe.c1 := by
 intro D hD w hw a
 let f :=algebraMap F (Simple w)
 let S:=smallConstants D w
 apply extend_span p S (f seed) _ _ (pth_span w hw) a
 · intro b
   have hl: (constants D).map f≤S:=le_sup_left
   have hc (i:Fin p) :f (physicalCut i b)∈S:=hl ⟨_,cut_constant hD b i,rfl⟩
   refine ⟨fun i=>⟨_,hc i⟩,?_⟩
   simpa only [map_sum,map_mul,map_pow] using
     congrArg f (physical_sum (q:=p) (by decide) b)
 · intro e
   have hr :Subfield.closure (zxp (fun b:Simple w=>b^p))≤S:=le_sup_right
   exact hr (Subfield.subset_closure ⟨e,rfl⟩)
end
end qPfoxUd
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qVHIGFe
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open E7 (CurvePlace)
open qb0hmCe (cLN)
open q1kuFjb (expansion_coeff)
open qNu3xvc qhFwyvc
open private gauss₂ gauss₂_bound coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
variable {E :Type} [zrb E] [zZE L E]
omit [zZE L E] in
private theorem chart_false (A:Equation E) :
   KM A false=a7W A:= by
 apply Polynomial.ringHom_ext
 · intro f
   simp [KM]
 · simp [KM,jU]
private theorem include_injective (w:CurvePlace L E) :
  zq4 (includeCoeffs w) :=
 zTo _ (zTo _ Subtype.val_injective)
variable {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks)
private theorem specialization_false :zdq (ek A (S.place γ) false) ≤
    zdq (aJB S γ hγ false) := by
  let w:=S.place γ
  intro U hU
  rw [zry,ek,chart_false,zQb] at hU
  have hk :AdjoinRoot.mk A.f (includeCoeffs w U)=0 :=
    zxb (AdjoinRoot A.f) (EC A) (hU.trans (map_zero _).symm)
  obtain ⟨G,hG⟩:=AdjoinRoot.mk_eq_zero.mp hk
  have hg:gauss₂ w.value G≤1 := by
    have hu:gauss₂ w.value (includeCoeffs w U)≤1 := by
      simpa only [Nat.cast_zero,WithZero.exp_zero] using
        gauss₂_bound w.value (includeCoeffs w U) (b:=0) (by
          intro i j
          simp only [coe_mapRingHom,coeff_map,Nat.cast_zero,WithZero.exp_zero]
          exact ((U.coeff i).coeff j).property)
    obtain ⟨i,j,hu'⟩:=(S.regular γ hγ).2
    have ha :gauss₂ w.value A.f=1 :=le_antisymm
      (by simpa only [Nat.cast_zero,WithZero.exp_zero] using
        gauss₂_bound w.value A.f (b:=0) (by
          intro i j
          simpa only [Nat.cast_zero,WithZero.exp_zero] using (S.regular γ hγ).1 i j))
      (hu' ▸ coeff_le_gauss₂ w.value A.f i j)
    simpa only [hG,map_mul,ha,one_mul] using hu
  obtain ⟨V,hV⟩:=j9 w G fun i j=>(coeff_le_gauss₂ w.value G i j).trans hg
  obtain ⟨F,hF⟩:=j9 w A.f (S.regular γ hγ).1
  have hprod:U=F*V:=include_injective w (by rw [map_mul,hF,hV,hG])
  have hred:F.map (mapRingHom (reduceSeed S γ hγ))=cLN (S.atPlace γ hγ) 0 A.f := by
    apply zXJ fun i=>zXJ fun j => ?_
    simp only [coeff_map,coe_mapRingHom,reduceSeed_eq,expansion_coeff]
    have hh:=congrArg (fun p:E[X][X]=>(p.coeff i).coeff j) hF
    simp only [coe_mapRingHom,coeff_map] at hh
    exact congrArg (fun t:E=>((S.atPlace γ hγ) t).coeff 0) hh
  have hs :aJB S γ hγ false F=0:= by
    change (F.map (mapRingHom (reduceSeed S γ hγ))).eval₂ phys
      (sectionOrdinate (S.P γ) (S.Q γ) false)=0
    rw [hred]
    exact S.root γ hγ
  rw [zry,hprod,map_mul,hs,zero_mul]
private theorem reverse_zero {R T:Type} [CommRing R] [zrb T] (j:R →+* T)
  (y :T) (hy :y≠0) (U:R[X]) :
  U.reverse.eval₂ j y=0↔U.eval₂ j y⁻¹=0:= by
 let:=invertibleOfNonzero (inv_ne_zero hy)
 simpa only [invOf_eq_inv,inv_inv] using eval₂_reverse_eq_zero_iff j y⁻¹ U
theorem specialization :qhFwyvc.c1 := by
  intro E _ _ A S γ hγ r hp
  cases r
  · exact specialization_false S γ hγ
  · let w:=S.place γ
    let y :=a7W A z7y
    let z :=phys (S.P γ)/phys (S.Q γ)
    have hz :z≠0:=div_ne_zero (fun h=>hp rfl
      (zxb L[X] FX (h.trans (map_zero phys).symm)))
      (fun h=>S.denom γ hγ (zxb L[X] FX (h.trans (map_zero phys).symm)))
    have hy :y≠0:= by
      intro hy
      have hx :z7y∈zdq (ek A w false) := by
        rw [zry,generic_ordinate]
        exact hy
      have h:=RingHom.mem_ker.mp (specialization_false S γ hγ hx)
      rw [specialized_eq,coe_eval₂RingHom,eval₂_X] at h
      exact hz h
    intro U hU
    have hU' : U.reverse∈zdq (ek A w false) := by
      rw [zry,generic_eq,coe_eval₂RingHom]
      apply (reverse_zero _ y hy U).2
      rwa [zry,generic_eq,coe_eval₂RingHom] at hU
    have hS:=RingHom.mem_ker.mp (specialization_false S γ hγ hU')
    rw [specialized_eq,coe_eval₂RingHom] at hS
    rw [zry,specialized_eq,coe_eval₂RingHom,
      show sectionOrdinate (S.P γ) (S.Q γ) true=z⁻¹ from (inv_div _ _).symm]
    exact (reverse_zero _ z hz U).1 hS
end
end qVHIGFe
end
end
section
section
namespace qFwMjQd
noncomputable section
open cu (L)
open q8Z6NHc (Slot Index jo)
open scoped Polynomial
abbrev LineData (E :Type) (d s a :ℕ) :=Slot d s a→E×E
abbrev Chart (E :Type) [CommSemiring E] :=z3y (Fin 3) E
abbrev aax (E :Type) :=Fin 3→E
def bY {E :Type} [zrb E] {d s a :ℕ} (rev :Bool) (f :LineData E d s a) :Chart E :=
  ∑ i,(znf (f i).1+MvPolynomial.C (f i).2*z9v 2) *
    z9v 0^i.val.2.val *
    z9v 1^(if rev then d - i.val.1.val else i.val.1.val)
theorem chart_boundary {E :Type} [zrb E] {d s a :ℕ} (f :LineData E d s a) (x z :E) :
   zY9 ![x,0,z] (bY true f) =
   ∑ i,if i.val.1.val=d then ((f i).1+(f i).2*z)*x^i.val.2.val else 0:= by
 classical
 rw [bY,map_sum]
 refine Finset.sum_congr rfl fun i _ => ?_
 by_cases hi:i.val.1.val=d
 · simp [hi]
 · have hle :i.val.1.val≤d:=Nat.le_of_lt_succ i.val.1.isLt
   have hn:d - i.val.1.val≠0:= by omega
   simp [hi,zero_pow hn]
def simple {E :Type} [zrb E] (f g h:Chart E) (q:aax E) :Prop :=
  zY9 q f=0∧zY9 q g=0∧zY9 q h=0 ∧
    Matrix.det (fun i j:Fin 3=>zY9 q
     (MvPolynomial.pderiv j ((![f,g,h] :Fin 3→Chart E) i)))≠0
abbrev LineRing (σ:Type) :=z3y (Option (Bool×σ)) L
abbrev Ez (σ:Type) :=AlgebraicClosure (FractionRing (LineRing σ))
abbrev Eline (d s a :ℕ) :=Ez (Index d s a)
def lineVar {σ:Type} (i:Option (Bool×σ)) :Ez σ :=
 algebraMap (LineRing σ) (Ez σ) (z9v i)
def fLine (d s a :ℕ) :LineData (Eline d s a) d s a :=
 fun i=>(lineVar (some (false,.inl i)),lineVar (some (true,.inl i)))
def gLine (d s a :ℕ) :LineData (Eline d s a) d s (a+s+1) :=
 fun i=>(lineVar (some (false,.inr i)),lineVar (some (true,.inr i)))
theorem weight_base {d s a :ℕ} (hd:2≤d) (ha :d*s≤a) :s≤a := by
 calc s=1*s :=(one_mul _).symm
      _≤d*s :=Nat.mul_le_mul_right _ (by omega)
      _≤a :=ha
def succSlot {d s a :ℕ} (hd:2≤d) (ha :s≤a)
    (i:Slot (d-1) s (a-s)) :Slot d s a := by
  have hi:=i.property
  refine ⟨(⟨i.val.1.val+1,by have :=i.val.1.isLt; omega⟩,
    ⟨i.val.2.val,by have :=i.val.2.isLt; omega⟩),?_⟩
  change i.val.2.val+(i.val.1.val+1)*s≤a
  rw [Nat.add_mul,one_mul]
  omega
def hLine (d s a :ℕ) (hd:2≤d) (ha :s≤a) (b c:L) :
    LineData (Eline d s a) (d-1) s (a-s) := fun i =>
  let E :=Eline d s a
  let f :=fLine d s a (succSlot hd ha i)
  let n:=(i.val.1.val+1 :ℕ)
  let l:E[X] :=z1z (algebraMap L E b) +
    z1z (algebraMap L E c)*z7y
  (n*f.1 - if i.val.2.val=0 then lineVar (σ:=Index d s a) none *
      (l^(d-2)).coeff i.val.1.val else 0,
    n*f.2)
def onLine {R σ S:Type} [CommRing R] [CommRing S] (k :R →+* S)
    (u v :σ→S) (T:S) : (z3y σ R)[X] →+* S[X] :=
  Polynomial.eval₂RingHom
    (zOD (Polynomial.C.comp k)
      (fun i=>z1z (u i)+Polynomial.C (v i)*z7y)) (z1z T)
def aOw {d s a :ℕ} (r : (jo d s a)[X]) : (Eline d s a)[X] :=
  onLine (algebraMap L _) (fun i=>lineVar (some (false,i)))
    (fun i=>lineVar (some (true,i))) (lineVar (σ:=Index d s a) none) r
end
end qFwMjQd
end
section
namespace qZbPQGe
noncomputable section
open Polynomial
open q8Z6NHc (Slot Index jo)
open cu (L)
open scoped Classical
abbrev Directions (E :Type) [zrb E] (d s a :ℕ) :=
 z3y (Index d s a) (AlgebraicClosure E)
abbrev LiftField (E :Type) [zrb E] (d s a :ℕ) :=
 FractionRing (Directions E d s a)
variable {E :Type} [zrb E] [zZE L E] {d s a :ℕ}
abbrev extend:AlgebraicClosure E →+* LiftField E d s a :=
 (algebraMap (Directions E d s a) (LiftField E d s a)).comp znf
def line (α:Index d s a→E) :jo d s a →+* (Directions E d s a)[X] :=
  zOD
    (Polynomial.C.comp (MvPolynomial.C.comp ((algebraMap E (AlgebraicClosure E)).comp
      (algebraMap L E))))
    (fun i=>z1z (znf (algebraMap E (AlgebraicClosure E) (α i))) +
      z1z (z9v i)*z7y)
def seriesLine (α:Index d s a→E) :
    jo d s a →+* PowerSeries (LiftField E d s a) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((mapRingHom (algebraMap (Directions E d s a) (LiftField E d s a))).comp (line α))
def shape {A:Type} [CommSemiring A] {d s a :ℕ} (u:Slot d s a→A) :A[X][X] :=
 ∑ i,monomial i.val.1.val (monomial i.val.2.val (u i))
abbrev avm {A:Type} [CommSemiring A] {d s a :ℕ}
  (u:jo d s a →+* A) :A[X][X] :=
 shape fun i=>u (z9v (Sum.inl i))
abbrev asa {A:Type} [CommSemiring A] {d s a :ℕ}
  (u:jo d s a →+* A) :A[X][X] :=
 shape fun i=>u (z9v (Sum.inr i))
abbrev aWi {A B:Type} [CommSemiring A] [CommSemiring B]
 (u:A →+* B) (f :A[X][X]) :B[X][X] :=f.map (mapRingHom u)
abbrev pairEval {A B:Type} [CommSemiring A] [CommSemiring B]
  (u:A →+* B) (x y :B) (f :A[X][X]) :B :=
 f.eval₂ (eval₂RingHom u x) y
@[simp] theorem pairMap_shape {A B:Type} [CommSemiring A] [CommSemiring B]
   {d s a :ℕ} (u:A →+* B) (v :Slot d s a→A) :
   aWi u (shape v)=shape (u ∘ v) := by
  simp only [aWi,shape,Polynomial.map_sum,map_monomial,coe_mapRingHom,Function.comp_apply]
theorem pairEval_map {A B D:Type} [CommSemiring A] [CommSemiring B] [CommSemiring D]
  (u:A →+* B) (v :B →+* D) (x y :D) (f :A[X][X]) :
  pairEval v x y (aWi u f)=pairEval (v.comp u) x y f := by
 simp only [aWi,pairEval,eval₂_map]
 congr 1
 apply RingHom.ext
 intro p
 simp only [zQb,coe_eval₂RingHom,coe_mapRingHom,eval₂_map]
theorem map_pairEval {A B D:Type} [CommSemiring A] [CommSemiring B] [CommSemiring D]
  (u:A →+* B) (v :B →+* D) (x y :B) (f :A[X][X]) :
  v (pairEval u x y f)=pairEval (v.comp u) (v x) (v y) f := by
 simp only [pairEval,hom_eval₂]
 congr 1
 apply RingHom.ext
 intro p
 simp only [zQb,coe_eval₂RingHom,hom_eval₂]
theorem map_pairEval_id {A B:Type} [CommSemiring A] [CommSemiring B]
   (v :A →+* B) (x y :A) (f :A[X][X]) :
   v (pairEval (RingHom.id _) x y f) =
     pairEval (RingHom.id _) (v x) (v y) (aWi v f) := by
 rw [map_pairEval,pairEval_map,RingHom.comp_id,RingHom.id_comp]
end
end qZbPQGe
end
section
set_option backward.isDefEq.respectTransparency false
namespace q4Zbmib
noncomputable section
open Polynomial qxPDCsa
open cu (L)
open scoped WithZero
open q1kuFjb (IntSeries residue fWQ expansion_coeff)
open q14iMuc (coeff_nonzero_of_val_eq)
open private j9 coeff_liftPoly from ProximityPrize.SubmissionLower.Z62SyBc
open private efc adG efd aMX from ProximityPrize.SubmissionLower.Y
open private discr_val_le from ProximityPrize.SubmissionLower.ZW8Nc6b
open private eval_bound from ProximityPrize.SubmissionLower.ZNiHFkd
variable {E :Type} [zrb E]
private theorem gauss_le (v :Valuation E ℤᵐ⁰) (g:E[X]) (c:ℤᵐ⁰) :
   adG v g≤ c↔BoundedAt v g c :=
 ⟨fun h i=>(aMX v g i).trans h,fun h=>Finset.sup_le fun i _=>h i⟩
private theorem afg {v :Valuation E ℤᵐ⁰} {g h:E[X]}
  (hg:BoundedAt v g 1) (hh:BoundedAt v h 1) :BoundedAt v (g*h) 1 := by
 apply (gauss_le _ _ _).mp
 rw [efd]
 simpa only [mul_one] using mul_le_mul' ((gauss_le _ _ _).mpr hg) ((gauss_le _ _ _).mpr hh)
private theorem radical_dvd {d r t u b:E[X]} (hr :RadicalOf d r)
  (ht:RadicalOf (d*u*b) t) :t∣r*u*b:= by
 obtain ⟨n,hn⟩:=hr.power
 have hs :=Nat.succ_ne_zero n
 apply (ht.separable.squarefree.dvd_pow_iff_dvd hs).mp
 refine ht.dvd.trans ?_
 rw [mul_pow,mul_pow]
 exact mul_dvd_mul (mul_dvd_mul (hn.trans (pow_dvd_pow _ (Nat.le_succ n)))
  (dvd_pow_self _ hs)) (dvd_pow_self _ hs)
variable [zZE L E]
private theorem coeff_reduce (a :E →ₐ[L] LaurentSeries L) (g:E[X]) (i:ℕ) :
  (reduce a g).coeff i=(a (g.coeff i)).coeff 0:= by
 simp only [reduce,expansion_coeff,coeff_C_zero]
private theorem reduce_ne (a :E →ₐ[L] LaurentSeries L) (g:E[X])
  (hc: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a g.leadingCoeff)=1) :
  reduce a g≠0:= by
 intro hz
 exact coeff_nonzero_of_val_eq hc (by
  simpa only [coeff_reduce,coeff_natDegree,coeff_zero] using
    congrArg (fun P:L[X]=>P.coeff g.natDegree) hz)
private theorem integral_lift (a :E →ₐ[L] LaurentSeries L) (g:E[X])
  (hg : ∀ i,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a (g.coeff i))≤1) :
  ∃ G:IntSeries[X],G.map IntSeries.subtype=g.map a.toRingHom:= by
 refine ⟨j9 (g.map a.toRingHom) (fun i=> by
  simpa only [coeff_map,ziQ,zlv] using hg i),?_⟩
 apply zXJ
 intro i
 rw [coeff_map,coeff_liftPoly]
 rfl
private theorem residue_of_map {a :E →ₐ[L] LaurentSeries L} {g:E[X]}
  {G:IntSeries[X]} (h:G.map IntSeries.subtype=g.map a.toRingHom) :
  G.map residue=reduce a g:= by
 apply zXJ
 intro i
 rw [coeff_map,fWQ,coeff_reduce]
 apply congrArg (fun c:LaurentSeries L=>c.coeff 0)
 simpa only [coeff_map,Subring.subtype_apply,ziQ,
  zlv] using congrArg (fun P: (LaurentSeries L)[X]=>P.coeff i) h
theorem proof :qqV3gre.c4 := by
  intro q Cq z S F V D W A r t hr ht γ hγ good
  let a :=F.atPlace γ (V.Bp hγ)
  let v :=(F.place γ).value
  let u:=finiteRef F (A.a 0)
  let b:=finiteRef F (A.a 1)
  change reduce a t≠0∧reduce a r*reduce a u*reduce a b≠0 ∧
    reduce a t∣reduce a r*reduce a u*reduce a b ∧
    (reduce a t).natDegree≤t.natDegree∧reduce a r.derivative=(reduce a r).derivative
  have hv (x :Cq.E) :
      v x=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a x) :=
    F.value γ (V.Bp hγ) x
  have hf (i j:ℕ) :v ((F.f.coeff i).coeff j)≤1 :=F.integral γ (V.Bp hγ) i j
  have hiD:BoundedAt v F.f.discr 1 := by
    apply (gauss_le _ _ _).mp
    change efc v F.f.discr≤1
    simpa only [one_pow] using discr_val_le (efc v) F.f F.positive 1
      (fun i=>(gauss_le _ _ _).mpr (hf i))
  have hiU:BoundedAt v u 1 :=eval_bound (F.place γ) F.f (A.a 0) hf
  have hiB:BoundedAt v b 1 :=eval_bound (F.place γ) F.f (A.a 1) hf
  have hiR:=hr.bound v 1 hiD
  have TA:=ht.bound v 1 (afg (afg hiD hiU) hiB)
  have hlD:v F.f.discr.leadingCoeff=1 :=good.1
  have hlU:v u.leadingCoeff=1 :=good.2.1 0
  have hlB:v b.leadingCoeff=1 :=good.2.1 1
  have hlR:v r.leadingCoeff=1 := by rw [hr.leading]; exact hlD
  have hlT:v t.leadingCoeff=1 := by
    have hlead:t.leadingCoeff=(F.f.discr*u*b).leadingCoeff :=ht.leading
    simp only [hlead,leadingCoeff_mul,map_mul,hlD,hlU,hlB,mul_one]
  have hne (g:Cq.E[X]) (h:v g.leadingCoeff=1) :reduce a g≠0 :=
    reduce_ne a g ((hv _).symm.trans h)
  have hdiv :t∣r*u*b:=radical_dvd hr ht
  obtain ⟨Q,hQ⟩:=hdiv
  have hiQ:BoundedAt v Q 1 := by
    have ht1 :adG v t=1 :=le_antisymm ((gauss_le _ _ _).mpr TA)
      (by simpa only [coeff_natDegree,hlT] using aMX v t t.natDegree)
    have hg:=(gauss_le _ _ _).mpr (afg (afg hiR hiU) hiB)
    rw [hQ,efd,ht1,one_mul] at hg
    exact (gauss_le _ _ _).mp hg
  have lift (g:Cq.E[X]) (h:BoundedAt v g 1) :
      ∃ G:IntSeries[X],G.map IntSeries.subtype=g.map a.toRingHom :=
    integral_lift a g (fun i=>hv _ ▸ h i)
  obtain ⟨R,hR⟩:=lift r hiR
  obtain ⟨T,hT⟩:=lift t TA
  obtain ⟨U,hU⟩:=lift u hiU
  obtain ⟨B,hB⟩:=lift b hiB
  obtain ⟨Q',hQ'⟩:=lift Q hiQ
  have hg:R*U*B=T*Q' := by
    apply zTo IntSeries.subtype Subtype.val_injective
    simp only [zNl,hR,hU,hB,hT,hQ']
    simpa only [zNl] using congrArg (Polynomial.map a.toRingHom) hQ
  refine ⟨hne t hlT,mul_ne_zero (mul_ne_zero (hne r hlR) (hne u hlU)) (hne b hlB),?_,?_,?_⟩
  · refine ⟨Q'.map residue,?_⟩
    simpa only [zNl,residue_of_map hR,residue_of_map hU,residue_of_map hB,
      residue_of_map hT] using congrArg (Polynomial.map residue) hg
  · have hd:T.natDegree=t.natDegree := by
      simpa only [natDegree_map_eq_of_injective (f :=IntSeries.subtype) Subtype.val_injective,
        natDegree_map_eq_of_injective (f :=a.toRingHom) a.injective] using congrArg natDegree hT
    rw [← residue_of_map hT,← hd]
    exact natDegree_map_le
  · have hd:R.derivative.map IntSeries.subtype=r.derivative.map a.toRingHom:= by
      rw [← derivative_map,← derivative_map,hR]
    rw [← residue_of_map hd,← residue_of_map hR,derivative_map]
end
end q4Zbmib
end
end
