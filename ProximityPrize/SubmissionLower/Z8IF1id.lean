import ProximityPrize.SubmissionLower.ZlnMfEd
import ProximityPrize.SubmissionLower.ZFdiUYb
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZhEC96c
import ProximityPrize.SubmissionLower.ZgKNZbc
import ProximityPrize.SubmissionLower.ZPZNNwd
import ProximityPrize.SubmissionLower.ZNiHFkd
set_option Elab.async false
section
set_option autoImplicit true
namespace q82zwcd
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K I blockLength)
open q7F2qKe (weakAgreement)
open cu (L j9)

open Cu (sQ)
open E7 (CurvePlace)
open P5_7_7 (base hit mL sites ic)
open qb0hmCe (CurveModel SiteTarget coeffHeight cLN specialize zD)
abbrev width (D:ℕ) :=262144+D-2*weakAgreement
abbrev gap (D:ℕ) :=weakAgreement-D
abbrev polar (D g W:ℕ) :=(2*g-2)*W-g*(g-1)*width D
abbrev poles (D g W:ℕ) :=(6*g-4)*W-(3*g*g-4*g+2)*width D
abbrev highFee (g k c:ℕ) :=g*(c+1)+(g+k)
def CompressionOK (D g k c j W B:ℕ) :Prop :=
 0<width D ∧0<c∧j≤k∧g*width D ≤W ∧
 B=W+1+j*width D ∧(g+k)*width D <B ∧
 (c+1)*(width D*((g+k)*(g+k+1)+j*(j+1))/2)<((k+1)*c)*B
def zN60d (w:I→K) (U:Finset K) (s :K→K[X]) (P:K→ L[X]) (a b:L[X]) :Prop :=
 ∀ γ∈U,mL (sites w s γ)*P γ=a*j9 (s γ)+b
structure WordChart (D:ℕ) (w:I→K) (U:Finset K) (s :K→K[X]) where
 a₀:L[X]
 a₁:L[X]
 b₀:L[X]
 b₁:L[X]
 u₀:ℕ
 u₁:ℕ
 order :u₀≤u₁
 xF:2*weakAgreement+(u₀+u₁)=blockLength+D
 row₀:ic D a₀ b₀ (weakAgreement+u₀)
 row₁:ic D a₁ b₁ (weakAgreement+u₁)
 determinant : ∃ c:L,c≠0∧a₀*b₁-a₁*b₀=C c*mL univ
 target : ∀ i,a₀.eval (base i)≠0∨a₁.eval (base i)≠0
 P:K→ L[X]
 Q:K→ L[X]
 denominator : ∀ γ∈U,Q γ≠0
 coprime : ∀ γ∈U,IsCoprime (P γ) (Q γ)
 numerator_ix : zN60d w U s P a₁ b₁
 denominator_ix : zN60d w U s Q a₀ b₀
 degree : ∀ γ∈U,(sites w s γ).card≤weakAgreement+u₀ ∧
   (Q γ).natDegree≤weakAgreement+u₀-(sites w s γ).card ∧
   (P γ).natDegree≤weakAgreement+u₁-(sites w s γ).card
 dual_hits : ∀ γ∈U,∀ i,
   (P γ).eval (base i)*a₀.eval (base i)=(Q γ).eval (base i)*a₁.eval (base i) ↔
     ¬ hit w s γ i
theorem WordChart.numerator_id {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]} (self:WordChart D w U s) :
 ∀ γ∈U,mL (sites w s γ)*self.P γ=self.a₁*j9 (s γ)+self.b₁ :=self.numerator_ix
theorem WordChart.denominator_id {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]} (self:WordChart D w U s) :
 ∀ γ∈U,mL (sites w s γ)*self.Q γ=self.a₀*j9 (s γ)+self.b₀ :=self.denominator_ix
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
def relativeDegree (J:WordChart D w U s) (γ:K) :ℕ :=
 let n:=J.u₁-J.u₀
 n+2*max (J.Q γ).natDegree ((J.P γ).natDegree-n)
def changed (J:WordChart D w U s) {E :Type} [Field E] [Algebra L E]
    (f :E[X][X]) :E[X][X] :=
  let l (a b:L[X]) :E[X][X] :=C (a.map (algebraMap L E)) +
    C (b.map (algebraMap L E))*X
  ∑ i∈range (f.natDegree+1),C (f.coeff i) *
    l (-J.b₁) J.b₀^i*l J.a₁ (-J.a₀)^(f.natDegree-i)
structure DualSheet (J:WordChart D w U s) (q:sQ) (z :K→K) where
 curve :CurveModel q
 f :curve.E[X][X]
 primitive :f.IsPrimitive
 irreducible :Irreducible (f.map (algebraMap curve.E[X] (FractionRing curve.E[X])))
 normalized: (f.coeff f.natDegree).leadingCoeff=1
 atPlace : ∀ γ∈U,curve.E →ₐ[L] LaurentSeries L
 place :K→CurvePlace L curve.E
 distinct :Set.InjOn place (U:Set K)
 value : ∀ γ (hγ:γ∈U) c,
   (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
 arc : ∀ γ (hγ:γ∈U),∃ a :Fin 2→PowerSeries L,
   (∀ i,atPlace γ hγ (curve.seed i)=(a i:LaurentSeries L)) ∧
   (∀ i,PowerSeries.constantCoeff (a i)=DP.Z7 (z γ) i) ∧
   (qK3TPae.RegularPoint q (DP.Z7 (z γ)) →
     ∃ i,PowerSeries.coeff 1 (a i)≠0)
 scale :K→curve.Eˣ
 integral : ∀ γ∈U,∀ i j,
   (place γ).value ((scale γ:curve.E)*((f.coeff i).coeff j))≤1
 reduction_ne : ∀ γ (hγ:γ∈U),
   cLN (atPlace γ hγ) 0 (C (C (scale γ:curve.E))*f)≠0
 root : ∀ γ (hγ:γ∈U),
   specialize (cLN (atPlace γ hγ) 0 (C (C (scale γ:curve.E))*f)) (J.P γ) (J.Q γ)=0
variable {q:sQ} {z :K→K} {J:WordChart D w U s}
abbrev DualSheet.d (F:DualSheet J q z) :=F.f.natDegree
abbrev DualSheet.h (F:DualSheet J q z) :=coeffHeight F.f
def DualSheet.aEA (F:DualSheet J q z) {E :Type} [Field E]
    (f :E[X][X]) (i:E →+* F.curve.E) :Prop :=
  ∃ a :F.curve.E[X],a≠0 ∧
    changed J (f.map (mapRingHom i))=C a*F.f
def DualSheet.Jm (F:DualSheet J q z) (W:ℕ) :Prop :=
 ∀ i,F.f.coeff i≠0→(F.f.coeff i).natDegree+F.d*J.u₀+i*(J.u₁-J.u₀)≤W
def DualSheet.direction (F:DualSheet J q z) (γ:K) (i:Fin 2) :L :=
 if h:γ∈U then (F.atPlace γ h (F.curve.seed i)).coeff 1 else 0
structure Variation (F:DualSheet J q z) where
 good:Finset K
 Bp:good⊆qK3TPae.regular q z U
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈good,den γ≠0
 reduced : ∀ γ∈good,IsCoprime (num γ) (den γ)
 separable : ∀ γ (hγ:γ∈good),
   let a :=F.atPlace γ (Finset.mem_filter.mp (Bp hγ)).1
   let f :=cLN a 0 (C (C (F.scale γ:F.curve.E))*F.f)
   f.natDegree=F.d∧(f.map P5_7_7.phys).Separable
 simple : ∀ γ (hγ:γ∈good),
   let a :=F.atPlace γ (Finset.mem_filter.mp (Bp hγ)).1
   specialize (cLN a 0 (C (C (F.scale γ:F.curve.E))*F.f)).derivative
     (J.P γ) (J.Q γ)≠0
 formula : ∀ γ (hγ:γ∈good),
   let a :=F.atPlace γ (Finset.mem_filter.mp (Bp hγ)).1
   P5_7_7.phys (num γ)/P5_7_7.phys (den γ) =
     zD a (C (C (F.scale γ:F.curve.E))*F.f) (J.P γ) (J.Q γ)
def Variation.DG {F:DualSheet J q z} (V:Variation F) (γ:K) :ℕ :=
 max (V.den γ).natDegree ((V.num γ).natDegree-relativeDegree J γ)
def targetHit (J:WordChart D w U s) (z :K→K) (R:SiteTarget) (γ:K) :Prop :=
 let t:=DP.Z7 (z γ) R.coord
 let a :=R.a+R.b*t
 let b:=R.c+R.d*t
 (a≠0∨b≠0)∧(J.P γ).eval R.center*b=(J.Q γ).eval R.center*a
def exception {F:DualSheet J q z} (V:Variation F) (R:SiteTarget) (γ:K) :Prop :=
 targetHit J z R γ ∧ ¬ ((V.num γ).eval R.center=0↔R.det=0∨F.direction γ R.coord=0)
end
end q82zwcd
end
section
set_option autoImplicit true
namespace qM10tBd
theorem proof :q1vkLGd.c2 :=qz11UBb.formalLift
end qM10tBd
end
section
namespace qb3Ndfc
noncomputable section
open Polynomial hiding expand coeff_expand
open Finset
open P5 (K)
open cu (L)
open qHEUR1a (Raw embed height)
open qbIP9ia (flatten exps flat_coeff exps_x exps_y wt_term)
open qPY5jQe (degree threshold weight)
open qkgz7gb (PlaneCurve SmoothAt rV Weighted)
open P5_7_3_5_2 (Prepared)
open qb0hmCe (CurveModel)
open q1kuFjb (AtSite restrict coeffIntegral headScalar)
open qGWTmVd (Factorization factorize factor_heights b5S head_C restrict_coeff restrict_degree)
open qFD8jve (aFA)
open qt5AtZa (HeightLE)
open scoped Classical WithZero
open private Sites Sites.mk Cover.n Cover.part Cover.inside Cover.zJ Cover.degree Cover.height Cover.weight single from ProximityPrize.SubmissionLower.ZSZKDCa
open private smooth_usable from ProximityPrize.SubmissionLower.ZNOTm7b
open private wdeg expand coeff_expand c0Q le_wdeg from ProximityPrize.SubmissionLower.ZgKNZbc
open private gauss₂ gauss₂_bound gauss₂_normal gauss₂_C coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
private theorem weight_bound (F:Raw) (hW:weight F≤threshold) :
  HeightLE degree threshold F:= by
 intro j m hm
 have h:exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support :=
  MvPolynomial.mem_support_iff.mpr (by rw [flat_coeff]; exact leadingCoeff_ne_zero.mpr hm)
 simpa only [exps_x,exps_y] using (wt_term degree h).trans hW
private theorem prepare (factor :P5_7_3_5_2_1.c3) :qPY5jQe.c1 := by
 intro F hF hW T z S hz hr q hq
 obtain ⟨Cq,hpole⟩:=q9Dxm8d.proof q hq
 let M:=T.filter fun γ=>SmoothAt q (rV z γ)
 change Nonempty (Prepared q z S M degree F.natDegree threshold (height F))
 by_cases hM:M.Nonempty
 swap
 · rw [not_nonempty_iff_eq_empty.mp hM]
   exact ⟨⟨Cq,0,Fin.elim0,fun j=>j.elim0,by simp,by simp,by simp,fun j=>j.elim0⟩⟩
 let A (γ:K) (h:γ∈M) :AtSite Cq (rV z γ) :=
   Classical.choice (q5azJba.arc hq Cq _
     (smooth_usable qM10tBd.proof (mem_filter.mp h).2))
 let v (γ:K) :=if h:γ∈M then (A γ h).place else (A hM.choose hM.choose_spec).place
 have hv (γ:K) (h:γ∈M) :v γ=(A γ h).place :=dite_eq_left h
 have hi:Set.InjOn v (M:Set K) := by
   intro γ hγ δ hδ heq
   rw [hv γ hγ,hv δ hδ] at heq
   have h:=congrFun ((A γ hγ).site_eq_of_place (A δ hδ) heq) 0
   exact hz (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 ((algebraMap K L).injective h)
 have hw:Weighted degree threshold (embed F) :=
   ⟨F,1,one_ne_zero,by rw [map_one,one_mul],weight_bound F hW⟩
 have hd: (embed F).natDegree=F.natDegree :=qVXVW4b.embed_degree F
 have hp: (embed F).IsPrimitive :=hF.2.1.isPrimitive (hd.symm ▸ hF.2.2.1.ne')
 let I:Sites Cq z M:=Sites.mk A v hv hi
 obtain ⟨R⟩:=single factor hq hpole I Subset.rfl hF.2.1 hp hw
   (fun γ hγ=>hr γ (mem_filter.mp hγ).1)
 exact ⟨⟨Cq,Cover.n R,Cover.part R,Cover.inside R,Cover.zJ R,
   (Cover.degree R).trans_eq hd,Cover.height R,Cover.weight R⟩⟩
private theorem restrict_weight {q:PlaneCurve} (B:CurveModel q) {Q:Raw} {D W:ℕ}
  (hW:HeightLE D W Q) :wdeg D (restrict B Q)≤W:= by
 apply Finset.sup_le
 intro d hd
 rw [c0Q]
 have hc:=MvPolynomial.mem_support_iff.mp hd
 rw [coeff_expand,restrict_coeff] at hc
 obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero hc
 have hk : ((Q.coeff (d none)).coeff a).coeff (d.some ())≠0 :=
  fun hz=>ha (by rw [hz,map_zero,zero_mul])
 have hn: (Q.coeff (d none)).coeff a≠0:= fun hz=>hk (by rw [hz,coeff_zero])
 exact (Nat.add_le_add_right (le_natDegree_of_ne_zero hk) _).trans (hW _ _ hn)
private theorem integral_factors {E :Type} [Field E] (v :Valuation E ℤᵐ⁰)
   {g:E[X][X]} (S:Factorization g) (hg:coeffIntegral v g)
   (hs : ¬ v (headScalar g)<1) :
   coeffIntegral v (C S.amm) ∧ ∀ j,coeffIntegral v (S.f j) := by
 let w:=gauss₂ v
 have h0:aFA v g 0:= fun i j=> by
   simpa only [Nat.cast_zero,WithZero.exp_zero] using hg i j
 have hG:w g≤1 := by
   simpa only [Nat.cast_zero,WithZero.exp_zero] using gauss₂_bound v g h0
 have hone (f :E[X][X]) (h:headScalar f=1) :1≤w f := by
   change 1≤gauss₂ v f
   rw [gauss₂_normal v f h]
   exact WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _)
 have hp:1≤w (C S.amm) :=hone _ (by rw [head_C]; exact S.monic)
 have hf (j:Fin S.n) :1≤w (S.f j) :=hone _ (S.normalized j)
 rw [S.product,map_mul,map_prod,map_mul C,map_mul w,
   show w (C (C (headScalar g)))=v (headScalar g) from gauss₂_C _ _,mul_assoc] at hG
 have hprod:w (C S.amm)*(∏ j,w (S.f j))≤1 :=
   (le_mul_of_one_le_left zero_le (le_of_not_gt hs)).trans hG
 have hphys :=(le_mul_of_one_le_right (a :=w (C S.amm)) zero_le
   (Finset.one_le_prod fun j _=>hf j)).trans hprod
 have hparts :=(le_mul_of_one_le_left (b := ∏ j,w (S.f j)) zero_le hp).trans hprod
 exact ⟨fun i k=>(coeff_le_gauss₂ v _ i k).trans hphys,
   fun j i k=>((coeff_le_gauss₂ v _ i k).trans
     (Finset.single_le_prod (fun j _=>hf j) (mem_univ j))).trans hparts⟩
theorem normalized_factors :P5_7_3_5_2_1.c3:= by
  intro q B hb Q D W hn hW
  obtain ⟨S⟩:=factorize hn
  obtain ⟨hs,hh⟩:=factor_heights B hb Q hn S
  refine ⟨⟨b5S hn,hs,S.amm,S.monic,S.n,S.f,S.product,S.irreducible,
    S.positive,S.normalized,(S.degree hn).le.trans (restrict_degree B Q),hh,?_⟩,
    fun v hg hu=>integral_factors v.value S hg hu⟩
  intro j i
  by_cases hi: (S.f j).coeff i=0
  · exact Or.inr hi
  have hd:S.f j∣restrict B Q:= by
    conv_rhs=>rw [S.product]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem S.f (mem_univ j)) _
  have hw:wdeg D (S.f j)≤wdeg D (restrict B Q) :=
    MvPolynomial.weightedTotalDegree_le_of_dvd _ (_root_.map_dvd expand hd)
      ((map_ne_zero_iff expand expand.injective).mpr hn)
  exact Or.inl (by simpa only [Nat.mul_zero,Nat.add_zero] using
    (le_wdeg (s :=D) (leadingCoeff_ne_zero.mpr hi)).trans (hw.trans (restrict_weight B hW)))
theorem proof :qPY5jQe.c1 :=prepare normalized_factors
end
end qb3Ndfc
end
section
set_option autoImplicit true
namespace qkLfS5c
theorem proof :P5_7_3_5_2_1.c3:=qb3Ndfc.normalized_factors
end qkLfS5c
end
section
namespace qbiuGTb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qxPDCsa
open qb0hmCe (CurveModel)
open q1kuFjb

open qrezXJe (sheet_bound)
private theorem exists_coprime_eval {E :Type} [Field E] [Algebra L E]
   {f :E[X][X]} (hf :f.IsPrimitive) (hu:f.leadingCoeff≠0) :
   ∃ t:L,IsCoprime f.leadingCoeff (f.eval (C (algebraMap L E t))) := by
 let A:=AlgebraicClosure E
 let b:L →+* A:=(algebraMap E A).comp (algebraMap L E)
 let B:Set A := {x | (f.leadingCoeff.map (algebraMap E A)).IsRoot x}
 let bad (x :A) :Set L:=b ⁻¹' {t | (f.map (aeval x).toRingHom).IsRoot t}
 have hn (x :A) :f.map (aeval x).toRingHom≠0:= by
   intro hz
   apply minpoly.not_isUnit E x
   apply (isPrimitive_iff_isUnit_of_C_dvd.mp hf) _
   apply (C_dvd_iff_dvd_coeff _ _).mpr
   intro i
   apply minpoly.dvd
   simpa only [coeff_map,coeff_zero,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
     congrArg (fun g:A[X]=>g.coeff i) hz
 have hB:B.Finite :=finite_setOfPred_isRoot (Polynomial.map_ne_zero hu)
 have ht: (⋃ x∈B,bad x).Finite :=hB.biUnion fun x _ =>
   (finite_setOfPred_isRoot (hn x)).preimage b.injective.injOn
 obtain ⟨t,_,h⟩:=(Set.infinite_univ : (Set.univ :Set L).Infinite).exists_notMem_finite ht
 refine ⟨t,(isCoprime_iff_aeval_ne_zero_of_isAlgClosed E A _ _).mpr ?_⟩
 intro x
 by_cases hx :aeval x f.leadingCoeff=0
 · right
   intro hy
   apply h
   refine Set.mem_biUnion (show x∈B from (eval_map_algebraMap _ _).trans hx) ?_
   change (f.map (aeval x).toRingHom).eval (b t)=0
   rw [show b t=(aeval x).toRingHom (C (algebraMap L E t)) by simp [b,aeval_C],
     eval_map_apply]
   exact hy
 · exact Or.inl hx
private theorem reduce_coeff {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (g:E[X]) (j:ℕ) :
  (reduce a g).coeff j=(a (g.coeff j)).coeff 0:= by
 simp only [reduce,expansion_coeff,coeff_C_zero]
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
private theorem cR9 (F:Sheet Cq z S) (t:L) :
  finiteRef F t = ∑ i∈F.f.support,F.f.coeff i*C (algebraMap L Cq.E t^i) := by
 simp only [finiteRef,eval_eq_sum,Polynomial.sum_def,← map_pow]
theorem proof :qxPDCsa.c7:= by
 intro q Cq z S F D W hw
 have hd (i:ℕ) : (F.f.coeff i).natDegree≤W:= by
   by_cases h:F.f.coeff i=0
   · simp [h]
   exact (Nat.le_add_right _ _).trans (hw i h)
 have hu:F.f.leadingCoeff.Monic:=F.normalized
 obtain ⟨t,ht⟩:=exists_coprime_eval (F.irreducible.isPrimitive F.positive.ne') hu.ne_zero
 refine ⟨F.f.leadingCoeff,finiteRef F t,resultant_ne_zero _ _ ht,hd F.d,?_,?_,?_,?_⟩
 · rw [cR9]
   exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
     (natDegree_mul_C_le _ _).trans (hd i)
 · intro w j
   simpa only [one_mul,leadingCoeff] using sheet_bound w.value F.f F.d j
 · intro w j
   rw [cR9,finsetSum_coeff]
   apply w.value.map_sum_le
   intro i _
   have hb:w.value (algebraMap L Cq.E t)≤1 := by
     by_cases h:t=0
     · simp [h]
     exact (w.on_constants t h).le
   rw [coeff_mul_C,map_mul,map_pow]
   simpa only [one_mul,one_pow,mul_one] using
     mul_le_mul' (sheet_bound w.value F.f i j) (pow_le_pow_left' hb i)
 · intro γ hγ
   let a :=F.atPlace γ hγ
   have hcoeff (i:ℕ) :reduce a (F.f.coeff i)=(specialize F hγ).coeff i:= by
     ext j
     rw [reduce_coeff,specialize,expansion_coeff]
   have hne :reduce a F.f.leadingCoeff≠0:= by
     intro h
     have hz :=congrArg (fun p:L[X]=>p.coeff F.f.leadingCoeff.natDegree) h
     rw [reduce_coeff,coeff_zero,coeff_natDegree,hu.leadingCoeff,map_one] at hz
     simp [HahnSeries.coeff_one] at hz
   refine ⟨gcd_ne_zero_of_left hne,dvd_gcd ?_ ?_⟩
   · rw [show F.f.leadingCoeff=F.f.coeff F.d from rfl,hcoeff]
     exact content_dvd_coeff _
   · rw [qU4m8Td.reduce_finite F hγ t]
     change (specialize F hγ).content∣(specialize F hγ).eval (C t)
     generalize specialize F hγ=s
     conv_rhs=>rw [s.eq_C_content_mul_primPart,eval_mul,eval_C]
     exact dvd_mul_right _ _
end
end qbiuGTb
end
