import ProximityPrize.SubmissionLower.ZvttkHa
import ProximityPrize.SubmissionLower.ZpdLrZa
import ProximityPrize.SubmissionLower.ZuJZkxc
import ProximityPrize.SubmissionLower.ZhNzRYc
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZZpExZa
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.ZWJjZ2a
import ProximityPrize.SubmissionLower.ZocsBpe
import ProximityPrize.SubmissionLower.ZFp80ca
import ProximityPrize.SubmissionLower.ZPpouqc
import ProximityPrize.SubmissionLower.ZsOxNPb
import ProximityPrize.SubmissionLower.Zm69VQc
import ProximityPrize.SubmissionLower.ZmXR7Cb
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.sum_univ_eq_sum_range → zdx, Finset → zJe, Finset.mul_sum → zxw, Finset.sum_congr → zUo, Function.Injective → zq4, LinearEquiv.ofInjective → zjT, MvPolynomial.X → z9v, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.weightedTotalDegree_le_of_dvd → zJD, Nat.card_eq_fintype_card → zey, Nat.le_of_lt_succ → zeh, Nat.mul_comm → z5A, Nat.sub_add_cancel → zxt, Polynomial → zM1, Polynomial.coeff_zero → zO6, Polynomial.lcoeff → z9j
section
section
namespace qR80KYd
def c1 :Prop :=qAW6lac.c1
def c2 :Prop :=qAW6lac.c2
def c3:Prop :=qAW6lac.c3
theorem of_children (ek :c1) (degree :c2) (specialize :c3) :
  qSHe4ub.c5 :=
 qAW6lac.of_children ek degree specialize
end qR80KYd
end
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_1_7Q4332
theorem proof : qhFwyvc.c2 := qVHIGFe.formula
theorem proof1 : qhFwyvc.c1 := qVHIGFe.specialization
end P5_7_1_7Q4332
end
section
section
set_option autoImplicit true
namespace qrsE1ie
noncomputable section
open Polynomial Finset
open P5 (K I)
open P5_7_7 (hit)
open Cu (sQ oO)
open scoped Classical
def discriminant {C₀:sQ} (f : ((oO C₀)[X])[X]) :
    (oO C₀)[X] :=
  (f.coeff 1)^2 - C 4*(f.coeff 2*f.coeff 0)
def geomSquare {C₀:sQ} [Fact (Irreducible C₀)]
    (f : ((oO C₀)[X])[X]) :Prop :=
  ∃ q: (AlgebraicClosure (oO C₀))[X],
    q^2=(discriminant f).map (algebraMap _ _)
def NodeAllowance (U:zJe K) (s :K→K[X]) (w:I→K) (B:ℕ) :Prop :=
  ∀ i:I,(U.filter fun γ=>hit w s γ i).card≤B ∨
    (U.filter fun γ => ¬hit w s γ i).card≤B
structure CoverIncidence (T:zJe K) (s :K→K[X]) (w:I→K) (H :ℕ) where
 left:zJe K
 right:zJe K
 left_sub:left⊆T
 right_sub:right⊆T
 zJ: (T \ (left∪right)).card≤5*H
 leftDegree :ℕ
 rightDegree :ℕ
 boS:leftDegree+rightDegree≤2
 left_nodes :NodeAllowance left s w (2*leftDegree*H)
 right_nodes :NodeAllowance right s w (2*rightDegree*H)
end
end qrsE1ie
end
section
set_option autoImplicit true
namespace qK3TPae
noncomputable section
open Polynomial MvPolynomial
open P5 (K p)

open cu (L)
open E7 (CurveField CurvePlace poleOrder KB)
open q7YMR4d (SmoothAt simpleQuadratic)
open Cu (sQ)
def highFee (e g c:ℕ) :ℕ:=e*(c+1)+e+g
def RegularPoint (Q:sQ) (a :Fin 2→L) :Prop :=
 SmoothAt Q a∨simpleQuadratic Q a
open scoped Classical in
def regular (Q:sQ) (z :K→K) (T:zJe K) :zJe K :=
 T.filter fun γ=>RegularPoint Q (DP.Z7 (z γ))
structure AmplifiedCut (T:zJe K) where
 E :Type
 [field :zrb E]
 [algebra :Algebra L E]
 curve :CurveField L E
 order :ℕ
 Lw:E
 nonzero :Lw≠0
 Ia :T ↪ CurvePlace L E
 ng:CurvePlace L E →₀ ℕ
 poles : ∀ v,poleOrder v.value Lw≤ng v
 vanishing : ∀ t:T,p^order+poleOrder (Ia t).value Lw ≤
   ng (Ia t)+KB (Ia t).value Lw
attribute [instance] AmplifiedCut.field AmplifiedCut.algebra
end
end qK3TPae
end
section
set_option backward.isDefEq.respectTransparency false
namespace qGBd8hb
noncomputable section
open Polynomial
open cu (L FX)
open Y3 (JS Dg embed)
open qkgz7gb (Stock ceilDiv physicalStock)
open qt5AtZa (HeightLE HeightLT)
open q89PToe (SeedOK atZ goP)
open qbIP9ia (Vars Exps flatten amm seed exps exps_x exps_y flat_coeff flat_coeff' ao8 rawSeed_apply wt wt_term wt_le)
open private weights from ProximityPrize.SubmissionLower.BJ
private theorem high_weight {D W:ℕ} {F:Dg} (hF : ¬ HeightLE D W F) :
  W<wt D (flatten F) := by
 by_contra hh
 apply hF
 intro j m hm
 have h:exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support := by
  apply MvPolynomial.mem_support_iff.mpr
  rw [flat_coeff]
  exact leadingCoeff_ne_zero.mpr hm
 simpa only [exps_x,exps_y] using (wt_term D h).trans (Nat.le_of_not_gt hh)
private theorem low_weight {D M:ℕ} {G:Dg} (hM:0<M)
  (hG:HeightLT D M G) :wt D (flatten G)<M:= by
 apply Nat.lt_of_le_pred hM
 apply wt_le
 intro v hv
 have hc:=MvPolynomial.mem_support_iff.mp hv
 rw [flat_coeff'] at hc
 have hm:=hG (v none) (ao8 v) (fun hz=>hc (by rw [hz,zO6]))
 exact Nat.le_pred_of_lt
  ((Nat.add_le_add_right (le_natDegree_of_ne_zero hc) _).trans_lt hm)
private def Tl:Vars→ℕ
 | some (.inl _)=>1
 | _=>0
private theorem bwf (v :Exps) :Finsupp.weight Tl v=(ao8 v).degree := by
 rw [Finsupp.weight_eq_sum,Fintype.sum_option,Fintype.sum_sum_type,Finsupp.degree_eq_sum]
 simp [Tl,smul_eq_mul,seed]
private theorem embed_support {G:Dg} {v :Exps} (hv :v∈(flatten G).support) :
  ao8 v∈((embed G).coeff (v none)).support := by
 rw [embed,coe_mapRingHom,coeff_map,
  MvPolynomial.support_map_of_injective _ (IsFractionRing.injective L[X] FX)]
 apply MvPolynomial.mem_support_iff.mpr
 intro hz
 exact MvPolynomial.mem_support_iff.mp hv (by rw [flat_coeff',hz,zO6])
private theorem quotient_seed {s :Stock} {F H :Dg} (hF:F≠0) (hH :H≠0)
    (hs :s.fits (embed (F*H))) {v :Exps} (hv :v∈(flatten H).support) :
    SeedOK s (ao8 v) := by
  have hd:flatten H∣flatten (F*H) :=map_dvd flatten ⟨F,mul_comm F H⟩
  have hp:=(map_ne_zero_iff _ flatten.injective).mpr (mul_ne_zero hF hH)
  cases s with
  | symmetric n =>
    have he : (flatten (F*H)).weightedTotalDegree Tl≤n :=
      Finset.sup_le fun u hu=> by
        rw [bwf]
        exact (MvPolynomial.le_totalDegree (embed_support hu)).trans (hs (u none))
    change (ao8 v).degree≤n
    rw [← bwf]
    exact (MvPolynomial.le_weightedTotalDegree _ hv).trans
      ((zJD _ hd hp).trans he)
  | asymmetric a b =>
    have he (i:Fin 2) : (ao8 v) i≤ if i=0 then a else b:= by
      rw [rawSeed_apply]
      apply (zTo (seed i) hv).trans
      apply le_trans (b:=(flatten (F*H)).degreeOf (seed i))
      · simp only [← MvPolynomial.weightedTotalDegree_piSingle (seed i)]
        exact zJD _ hd hp
      · apply MvPolynomial.degreeOf_le_iff.mpr
        intro u hu
        rw [← rawSeed_apply]
        have h:=zTo i (embed_support hu)
        fin_cases i
        · simpa using h.trans (hs (u none)).1
        · simpa using h.trans (hs (u none)).2
    exact ⟨by simpa using he 0,by simpa using he 1⟩
private theorem lt_ceil {a D j:ℕ} (hD:0<D) :j<ceilDiv a D↔j*D <a := by
 rw [ceilDiv,← Nat.succ_le_iff,Nat.le_div_iff_mul_le hD,Nat.succ_mul]
 omega
private abbrev PhysicalIndex (a D:ℕ) :=Σ j:Fin (ceilDiv a D),Fin (a - j.val*D)
private theorem physical_card (a D:ℕ) (hD:0<D) :
  Nat.card (PhysicalIndex a D)=physicalStock a D:= by
 rw [zey,Fintype.card_sigma]
 simp only [Fintype.card_fin]
 rw [zdx (fun j=>a - j*D)]
 have hk (j:ℕ) (hj:j∈Finset.range (ceilDiv a D)) :j*D ≤a :=
  ((lt_ceil hD).mp (Finset.mem_range.mp hj)).le
 rw [Finset.sum_tsub_distrib _ hk,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
  ← Finset.sum_mul,Finset.sum_range_id,z5A _ D]
 rfl
private abbrev Index (a D:ℕ) (s :Stock) :=PhysicalIndex a D×atZ s
private def aD (a D:ℕ) (s :Stock) :Dg →ₗ[L] (Index a D s→L) :=
  LinearMap.pi fun i =>
    (z9j L i.1.2.val).comp
      (((MvPolynomial.lcoeff L[X] i.2.val).restrictScalars L).comp
        ((z9j JS i.1.1.val).restrictScalars L))
theorem proof :qt5AtZa.c2 := by
  classical
  intro D M W s hD hM F hF V hV
  have hhigh:=high_weight hF
  have hF0:F≠0:= by
    intro hz
    apply hF
    rw [hz]
    intro j m hm
    exact (hm (by simp)).elim
  let _:AddCommGroup V := @Submodule.addCommGroup L Dg _ _ _ V
  let a :=M-W-1
  let mul :=LinearMap.mulLeft L F
  have hmul :zq4 mul := fun _ _ h=>mul_left_cancel₀ hF0 h
  let incl:V →ₗ[L] mul.range :=V.subtype.codRestrict mul.range fun G=> by
    obtain ⟨H,hH⟩:=(hV G.val G.property).2.2
    exact ⟨H,hH.symm⟩
  let quot:V →ₗ[L] Dg:=(zjT mul hmul).symm.toLinearMap.comp incl
  have hquot (G:V) :F*quot G=G.val := by
    change mul ((zjT mul hmul).symm (incl G))=(incl G).val
    exact LinearEquiv.ofInjective_symm_apply mul (incl G)
  let proj:=(aD a D s).comp quot
  have hinj:zq4 proj:= by
    apply (injective_iff_map_eq_zero proj.toAddMonoidHom).mpr
    intro G hG
    apply Subtype.ext
    change G.val=0
    rw [← hquot G]
    suffices hz :quot G=0 by rw [hz,mul_zero]
    by_contra hH
    let H :=quot G
    have hG' := (hV G.val G.property).1
    rw [← hquot G] at hG'
    have htop:=low_weight hM hG'
    rw [map_mul,show wt D (flatten F*flatten H)=wt D (flatten F)+wt D (flatten H) from
      MvPolynomial.weightedTotalDegree_mul (weights D) _ _
        ((map_ne_zero_iff _ flatten.injective).mpr hF0)
        ((map_ne_zero_iff _ flatten.injective).mpr hH)] at htop
    obtain ⟨v,hv⟩:=MvPolynomial.support_nonempty.mpr
      ((map_ne_zero_iff _ flatten.injective).mpr hH)
    have hterm :v amm+v none*D ≤wt D (flatten H) :=wt_term D hv
    have hp:v amm+v none*D <a := by dsimp only [a]; omega
    have hs :=(hV G.val G.property).2.1
    rw [← hquot G] at hs
    let i:Index a D s :=
      (⟨⟨v none,(lt_ceil hD).mpr (by omega)⟩,⟨v amm,by
          change v amm<a - v none*D
          omega⟩⟩,
        ⟨ao8 v,quotient_seed hF0 hH hs hv⟩)
    have hc:=congrFun hG i
    change ((H.coeff (v none)).coeff (ao8 v)).coeff (v amm)=0 at hc
    exact MvPolynomial.mem_support_iff.mp hv ((flat_coeff' H v).trans hc)
  let:Fintype (atZ s) :=Fintype.ofFinite _
  calc
    _≤Module.finrank L (Index a D s→L) :=LinearMap.finrank_le_finrank_of_injective hinj
    _ = _:= by
      rw [Module.finrank_fintype_fun_eq_card,← zey,Nat.card_prod,
        physical_card a D hD,goP]
end
end qGBd8hb
end
section
set_option autoImplicit true
namespace qVu1nGe
open P5_7_2 (fO)
open q7F2qKe
private theorem bandRows (b:fO) (hb:b.val<7) :BandRows b:= by
 rcases b with ⟨n,hn⟩
 change n<7 at hb
 interval_cases n
 · exact r0
 · exact r1
 · exact r2
 · exact r3
 · exact r4
 · exact r5
 · exact r6
theorem proof :q5oHm3d.c1 := by
 intro b hb o ho j hj hfree
 have hp:j<stopCount b:=Finset.mem_range.mp hj
 let i:Fin (stopCount b-afterFree b - 1) :=⟨j-(afterFree b+1),by omega⟩
 have hi:afterFree b+1+i.val=j:= by dsimp [i]; omega
 exact hi ▸ bandRows b hb ⟨o,Finset.mem_range.mp ho⟩ i
end qVu1nGe
end
section
set_option autoImplicit true
namespace qXrbKzb
open P5_7_2 (fO)
open q7F2qKe
open q5oHm3d (dqs)
private theorem of_grid {b:fO} {n:ℕ} (h:y8 b n)
  (ho:originCount b=13) (hf :afterFree b=8) (hs :stopCount b=9+n) :
  ∀ o∈origins b,∀ j∈stops b,afterFree b<j→dqs b o j:= by
 intro o hom j hjm hj
 have hoi:=Finset.mem_range.mp hom
 have hji:=Finset.mem_range.mp hjm
 have hts :j-9<n:= by omega
 have hsum:j-9+9=j:= by omega
 have hr :=h ⟨o,by omega⟩ ⟨j-9,hts⟩
 change dqs b o (j-9+9) at hr
 rwa [hsum] at hr
theorem proof :q5oHm3d.c2 := by
 intro b hlow hhigh
 have hb:b.val = 7∨b.val=8∨b.val=9∨b.val=10∨b.val=11 := by omega
 rcases hb with hb | hb | hb | hb | hb
 · have he :b=⟨7,by decide⟩:=Fin.ext hb
   subst b
   exact of_grid band7 (by decide) (by decide) (by decide)
 · have he :b=⟨8,by decide⟩:=Fin.ext hb
   subst b
   exact of_grid band8 (by decide) (by decide) (by decide)
 · have he :b=⟨9,by decide⟩:=Fin.ext hb
   subst b
   exact of_grid band9 (by decide) (by decide) (by decide)
 · have he :b=⟨10,by decide⟩:=Fin.ext hb
   subst b
   exact of_grid dx1 (by decide) (by decide) (by decide)
 · have he :b=⟨11,by decide⟩:=Fin.ext hb
   subst b
   exact of_grid dx2 (by decide) (by decide) (by decide)
end qXrbKzb
end
end
section
section
namespace qvWVeNa
noncomputable section
open qFwMjQd (Chart aax)
open MvPolynomial
abbrev bzm (n:Fin 3→ℕ) :=Σ i,Fin (n i)
structure Model (E :Type) [zrb E] (n t:Fin 3→ℕ) where
 base :bzm t→E
 graph:bzm n→zM1 E
 seed :Fin 3→E
structure Good {E :Type} [zrb E] {n t:Fin 3→ℕ} (s :ℕ) (m:Model E n t) :Prop where
 seed_inj:zq4 m.seed
 base_inj:zq4 m.base
 graph_degree : ∀ i,(m.graph i).natDegree≤ s
 leading_inj:zq4 fun i=>(m.graph i).coeff s
 base_avoid : ∀ i j,i≠j → ∀ l,(m.graph i - m.graph j).eval (m.base l)≠0
 ct4 : ∀ i j,i≠j → ∀ x,(m.graph i - m.graph j).eval x=0 →
  (m.graph i - m.graph j).derivative.eval x≠0
 no_three : ∀ i j l,i≠j→i≠l→j≠l → ∀ x,
  (m.graph i).eval x=(m.graph j).eval x→(m.graph i).eval x≠(m.graph l).eval x
def mark {E :Type} (v :E×E) (z :E) :aax E := ![v.1,v.2,z]
@[simp] theorem mark_x {E :Type} (v :E×E) (z :E) :mark v z 0=v.1 :=rfl
@[simp] theorem mark_y {E :Type} (v :E×E) (z :E) :mark v z 1=v.2 :=rfl
@[simp] theorem mark_z {E :Type} (v :E×E) (z :E) :mark v z 2=z :=rfl
variable {E :Type} [zrb E]
def graphCoeff (s :ℕ) (rx :Bool) (p:zM1 E) :Chart E :=
 ∑ j:Fin (s+1),C (p.coeff j.val)*z9v 0^(if rx then s-j.val else j.val)
def baseFactor (rx :Bool) (r :E) :Chart E :=
 if rx then 1 - C r*z9v 0 else z9v 0 - C r
def graphFactor (s :ℕ) (rx ry :Bool) (p:zM1 E) :Chart E :=
 if ry then 1 - graphCoeff s rx p*z9v 1 else z9v 1 - graphCoeff s rx p
def amm (s :ℕ) (rx ry :Bool) {n t:ℕ}
    (r :Fin t→E) (p:Fin n→zM1 E) :Chart E :=
  (∏ l,baseFactor rx (r l)) * ∏ j,graphFactor s rx ry (p j)
def seedFactor (rz :Bool) (z :E) :Chart E :=
 if rz then 1 - C z*z9v 2 else z9v 2 - C z
def physicalChart {n t:Fin 3→ℕ} (s :ℕ) (m:Model E n t) (rx ry :Bool) (i:Fin 3) :
    Chart E :=
  amm s rx ry (fun l=>m.base ⟨i,l⟩) (fun j=>m.graph ⟨i,j⟩)
def splitChart {n t:Fin 3→ℕ} (s :ℕ) (m:Model E n t) (rx ry rz :Bool)
    (i:Fin 3) :Chart E :=
  physicalChart s m rx ry i*seedFactor rz (m.seed i)
def Km {F:Type} [zrb F] {n t:Fin 3→ℕ} (k :E →+* F) (s :ℕ)
    (m:Model E n t) (rx ry :Bool) (i:Fin 3) (q:aax F) :F :=
  eval q (map k (physicalChart s m rx ry i))
def arS {F:Type} [zrb F] {n t:Fin 3→ℕ} (k :E →+* F) (s :ℕ)
    (m:Model E n t) (rx ry :Bool) (i j:Fin 3) (q:aax F) :Prop :=
  Km k s m rx ry i q=0∧Km k s m rx ry j q=0
def pairDegree (s n t n' t' : ℕ) :ℕ:=t*n' + n*t' + n*n'*s
def graphAt {F:Type} [zrb F] (k :E →+* F) (s :ℕ) (rx :Bool)
    (p:zM1 E) (x :F) :F :=
  ∑ j:Fin (s+1),k (p.coeff j.val)*x^(if rx then s-j.val else j.val)
theorem graphAt_finite {F:Type} [zrb F] (k :E →+* F) {s :ℕ} {p:zM1 E}
  (hp:p.natDegree≤ s) (x :F) :graphAt k s false p x=p.eval₂ k x := by
 rw [graphAt,Polynomial.eval₂_eq_sum_range' k (Nat.lt_succ_iff.mpr hp)]
 exact zdx (fun i=>k (p.coeff i)*x^i) _
theorem graphAt_infty {F:Type} [zrb F] (k :E →+* F) (s :ℕ) (p:zM1 E) :
   graphAt k s true p 0=k (p.coeff s) := by
 let j:Fin (s+1) :=⟨s,Nat.lt_succ_self s⟩
 change (∑ i:Fin (s+1),k (p.coeff i.val)*(0:F)^(s-i.val))= _
 rw [Finset.sum_eq_single j]
 · simp [j]
 · intro i _ hi
   have hle :i.val≤ s :=zeh i.isLt
   have hne :i.val≠s := fun e=>hi (Fin.ext e)
   simp [zero_pow (by omega :s - i.val≠0)]
 · simp
theorem graphAt_invert {F:Type} [zrb F] (k :E →+* F) {s :ℕ} {p:zM1 E}
   (hp:p.natDegree≤ s) {x :F} (hx :x≠0) :
   graphAt k s true p x=x^s*p.eval₂ k x⁻¹:= by
 rw [← graphAt_finite k hp,graphAt,graphAt,zxw]
 refine zUo rfl fun i _ => ?_
 change k (p.coeff i.val)*x^(s-i.val)=x^s*(k (p.coeff i.val)*(x⁻¹)^i.val)
 have he :x^(s-i.val)=x^s*(x⁻¹)^i.val := by
   rw [inv_pow,← div_eq_mul_inv,eq_div_iff (pow_ne_zero _ hx),← pow_add,
     zxt (zeh i.isLt)]
 rw [he,mul_left_comm]
theorem roots_descend [IsAlgClosed E] {F:Type} [zrb F] (k :E →+* F)
  {p:zM1 E} (hp:p≠0) {x :F} (hx :p.eval₂ k x=0) :
  ∃ r∈p.roots,x=k r := by
 have hm:=(Polynomial.mem_roots_map hp).mpr hx
 rw [(IsAlgClosed.splits p).roots_map_of_injective k.injective] at hm
 obtain ⟨r,hr,he⟩:=Multiset.mem_map.mp hm
 exact ⟨r,hr,he.symm⟩
theorem graph_sub_ne {n t:Fin 3→ℕ} {s :ℕ} {m:Model E n t}
  (hm:Good s m) {i j:bzm n} (h:i≠j) :m.graph i - m.graph j≠0 :=
 fun e=>h (hm.leading_inj (congrArg (fun p:zM1 E=>p.coeff s) (sub_eq_zero.mp e)))
theorem atPhysical_eq {F:Type} [zrb F] {n t:Fin 3→ℕ} (k :E →+* F)
    (s :ℕ) (m:Model E n t) (rx ry :Bool) (i:Fin 3) (q:aax F) :
    Km k s m rx ry i q =
      (∏ l:Fin (t i),if rx then 1 - k (m.base ⟨i,l⟩)*q 0 else q 0 - k (m.base ⟨i,l⟩)) *
      ∏ j:Fin (n i),if ry then 1 - graphAt k s rx (m.graph ⟨i,j⟩) (q 0)*q 1
        else q 1 - graphAt k s rx (m.graph ⟨i,j⟩) (q 0) := by
  cases rx <;> cases ry <;>
    simp [Km,physicalChart,amm,baseFactor,graphFactor,graphCoeff,graphAt]
theorem principal_hit {F:Type} [zrb F] {n t:Fin 3→ℕ} (k :E →+* F)
  {s :ℕ} {m:Model E n t} (hm:Good s m) (i:Fin 3) (q:aax F) :
  Km k s m false false i q=0 ↔
    (∃ l:Fin (t i),q 0=k (m.base ⟨i,l⟩)) ∨
    (∃ j:Fin (n i),q 1=(m.graph ⟨i,j⟩).eval₂ k (q 0)) := by
 have hg (j:Fin (n i)) :=graphAt_finite k (hm.graph_degree ⟨i,j⟩) (q 0)
 simp [atPhysical_eq,Finset.prod_eq_zero_iff,sub_eq_zero,hg]
end
end qvWVeNa
end
section
namespace qzhw4Oa
noncomputable section
open qFwMjQd (LineData aax)
open q9sUlTb (fullChart push b8A zeroAt zeroAt_map)
open MvPolynomial
variable {K:Type} [zrb K]
private theorem eval_chart {e s b:ℕ} (f :LineData K e s b) (rx ry rz :Bool)
  (x y z :K) :
  eval ![x,y,z] (fullChart rx ry rz f) =
  ∑ i,((if rz then (f i).2 else (f i).1)+(if rz then (f i).1 else (f i).2)*z) *
    x^(if rx then b - i.val.1.val*s - i.val.2.val else i.val.2.val) *
    y ^(if ry then e - i.val.1.val else i.val.1.val) := by
 simp only [fullChart,map_sum,map_mul,map_pow,map_add,eval_C,eval_X,
  Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
 rfl
private theorem cancel_scale {x :K} (hx :x≠0) (l m n:ℕ) :
  (x⁻¹)^l*x^m*x^(l+n)=x^(m+n) := by
 rw [pow_add x l n,pow_add x m n]
 calc
  _=((x⁻¹)^l*x^l)*(x^m*x^n) := by ac_rfl
  _ = _:= by rw [← mul_pow,inv_mul_cancel₀ hx,one_pow,one_mul]
private theorem scale {x :K} (hx :x≠0) {l m n p:ℕ} (he :l+p=m+n) :
  (x⁻¹)^l*x^m=(x⁻¹)^n*x^p:= by
 apply mul_right_cancel₀ (pow_ne_zero (l+n) hx)
 calc
  _=x^(m+n) :=cancel_scale hx l m n
  _=x^(p+l) := by rw [← he,Nat.add_comm l p]
  _ = _:= by rw [Nat.add_comm l n,cancel_scale hx]
private theorem Wn (c p r z :K) :c*p*(r*z)=(p*r)*(c*z) := by ac_rfl
private theorem flip_x {e s b:ℕ} (f :LineData K e s b) (ry rz :Bool)
    {x :K} (hx :x≠0) (y z :K) (hb:e*s≤b) :
    eval ![x⁻¹,(if ry then x^s else (x⁻¹)^s)*y,z] (fullChart true ry rz f) =
      (x⁻¹)^(if ry then b-e*s else b)*eval ![x,y,z] (fullChart false ry rz f) := by
  rw [eval_chart,eval_chart,zxw]
  refine zUo rfl fun ij _ => ?_
  let i:ℕ:=ij.val.1.val
  let j:ℕ:=ij.val.2.val
  let c:=(if rz then (f ij).2 else (f ij).1)+(if rz then (f ij).1 else (f ij).2)*z
  have hij:j+i*s≤b:=ij.property
  have hi:i≤e :=zeh ij.val.1.isLt
  cases ry
  · change c*(x⁻¹)^(b-i*s-j)*((x⁻¹)^s*y)^i=(x⁻¹)^b*(c*x^j*y^i)
    have he : (b-i*s-j)+s*i+j=0+b:= by rw [z5A s i]; omega
    have h:=scale hx he
    rw [pow_zero,mul_one,pow_add] at h
    calc
      _=((x⁻¹)^(b-i*s-j)*((x⁻¹)^s)^i)*(c*y^i) := by rw [mul_pow]; exact Wn _ _ _ _
      _ = _:= by rw [← pow_mul,h]; ac_rfl
  · change c*(x⁻¹)^(b-i*s-j)*(x^s*y)^(e-i)=(x⁻¹)^(b-e*s)*(c*x^j*y^(e-i))
    have hd: (e-i)*s+i*s=e*s := by rw [← Nat.add_mul,zxt hi]
    have he : (b-i*s-j)+j=s*(e-i)+(b-e*s) := by rw [z5A s (e-i)]; omega
    calc
      _=((x⁻¹)^(b-i*s-j)*x^(s*(e-i)))*(c*y^(e-i)) := by
        rw [mul_pow,pow_mul]
        exact Wn _ _ _ _
      _ = _:= by rw [scale hx he]; ac_rfl
private theorem flip_y {e s b:ℕ} (f :LineData K e s b) (rx ry rz :Bool)
   (x :K) {y :K} (hy :y≠0) (z :K) :
   eval ![x,y⁻¹,z] (fullChart rx (!ry) rz f) =
     (y⁻¹)^e*eval ![x,y,z] (fullChart rx ry rz f) := by
 rw [eval_chart,eval_chart,zxw]
 refine zUo rfl fun ij _ => ?_
 let i:ℕ:=ij.val.1.val
 have hi:i≤e :=zeh ij.val.1.isLt
 let l:=if !ry then e-i else i
 let p:=if ry then e-i else i
 have he :l+p=0+e := by cases ry <;> simp [l,p] <;> omega
 have h:=scale hy he
 rw [pow_zero,mul_one] at h
 change _ *(y⁻¹)^l=(y⁻¹)^e*(_ *y^p)
 rw [h]
 ac_rfl
private theorem flip_z {e s b:ℕ} (f :LineData K e s b) (rx ry :Bool)
   (x y :K) {z :K} (hz :z≠0) :
   eval ![x,y,z⁻¹] (fullChart rx ry true f) =
     z⁻¹*eval ![x,y,z] (fullChart rx ry false f) := by
 rw [eval_chart,eval_chart,zxw]
 refine zUo rfl fun i _ => ?_
 have h: (f i).2+(f i).1*z⁻¹=z⁻¹*((f i).1+(f i).2*z) := by
   rw [mul_add]
   calc
     _=z⁻¹*(f i).1+(z⁻¹*z)*(f i).2 := by rw [inv_mul_cancel₀ hz,one_mul]; ac_rfl
     _ = _:= by ac_rfl
 let j:=if rx then b - i.val.1.val*s - i.val.2.val else i.val.2.val
 let k :=if ry then e - i.val.1.val else i.val.1.val
 change ((f i).2+(f i).1*z⁻¹)*x^j*y^k=z⁻¹*(((f i).1+(f i).2*z)*x^j*y^k)
 rw [h]
 simp only [mul_assoc]
private def coord (r :Bool) (x :K) :K:=if r then x⁻¹ else x
private theorem normalize_coord (V:ValuationSubring K) (x :K) :
   ∃ (r :Bool) (u:V),(u:K)=coord r x ∧
     (r=true→x≠0∧IsLocalRing.residue V u=0) := by
 by_cases hx :x∈V
 · exact ⟨false,⟨x,hx⟩,rfl,fun e=>Bool.noConfusion e⟩
 · have hn:=V.inv_mem_nonunits_iff.mpr (Or.inr hx)
   let u:V:=⟨x⁻¹,V.nonunits_subset hn⟩
   exact ⟨true,u,rfl,fun _=>⟨fun h=>hx (h ▸ V.zero_mem),
     (IsLocalRing.residue_eq_zero_iff _).mpr (V.coe_mem_nonunits_iff.mp hn)⟩⟩
private def adjust (rx ry :Bool) (s :ℕ) (x y :K) :K :=
 if rx then (if ry then x^s else (x⁻¹)^s)*y else y
private def jU (rev flip:Bool) :Bool:=if flip then !rev else rev
private theorem bm2 {e s b:ℕ} (f :LineData K e s b) (hb:e*s≤b)
   (rev rx t rz :Bool) (x y z :K)
   (hx :rx=true→x≠0) (hy :t=true→adjust rx rev s x y≠0)
   (hz :rz=true→z≠0)
   (h:eval ![x,y,z] (fullChart false rev false f)=0) :
   eval ![coord rx x,coord t (adjust rx rev s x y),coord rz z]
     (fullChart rx (jU rev t) rz f)=0:= by
 let y' := adjust rx rev s x y
 have h₁:eval ![coord rx x,y',z] (fullChart rx rev false f)=0:= by
   cases rx
   · exact h
   · change eval ![x⁻¹,(if rev then x^s else (x⁻¹)^s)*y,z] (fullChart true rev false f)=0
     rw [flip_x f rev false (hx rfl) y z hb,h,mul_zero]
 have h₂:eval ![coord rx x,coord t y',z] (fullChart rx (jU rev t) false f)=0:= by
   cases t
   · exact h₁
   · change eval ![coord rx x,(y')⁻¹,z] (fullChart rx (!rev) false f)=0
     rw [flip_y f rx rev false (coord rx x) (hy rfl) z,h₁,mul_zero]
 cases rz
 · exact h₂
 · change eval ![coord rx x,coord t y',z⁻¹] (fullChart rx (jU rev t) true f)=0
   rw [flip_z f rx (jU rev t) (coord rx x) (coord t y') (hz rfl),h₂,mul_zero]
private theorem integral_zero (V:ValuationSubring K) {e s b:ℕ}
  (f :LineData V e s b) (rx ry rz :Bool) (p:aax V)
  (h:eval (V.subtype ∘ p) (fullChart rx ry rz (push V.subtype f))=0) :
  eval p (fullChart rx ry rz f)=0:= by
 apply V.subtype_injective
 rw [map_eval,b8A,map_zero,h]
theorem proof :q9sUlTb.c3:= by
  intro K _ V d s a hd ha f g h hno rev q hq
  let x :=q 0
  let y :=q 1
  let z :=q 2
  have hpoint : ![x,y,z]=q:= by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hf,hg,hh⟩:=hq
  have hgs :d*s≤a+s+1 := by omega
  have hhs : (d-1)*s≤a-s := by
    have he : (d-1)*s+s=d*s := by
      calc
        _=(d-1+1)*s := by rw [Nat.add_mul,one_mul]
        _ = _:= by rw [zxt (by omega :1≤d)]
    omega
  obtain ⟨rx,u,hu,hxu⟩:=normalize_coord V x
  obtain ⟨rz,w,hw,hzw⟩:=normalize_coord V z
  obtain ⟨t,v,hv,hyv⟩:=normalize_coord V (adjust rx rev s x y)
  let p:aax V := ![u,v,w]
  have hp:V.subtype ∘ p = ![coord rx x,coord t (adjust rx rev s x y),coord rz z] := by
    funext i
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  have transported {e b:ℕ} (F:LineData V e s b) (hb:e*s≤b)
      (hF:eval q (fullChart false rev false (push V.subtype F))=0) :
      eval p (fullChart rx (jU rev t) rz F)=0:= by
    apply integral_zero V
    rw [hp]
    exact bm2 (push V.subtype F) hb rev rx t rz x y z
      (fun r=>(hxu r).1) (fun r=>(hyv r).1) (fun r=>(hzw r).1) (hpoint.symm ▸ hF)
  have hz :zeroAt (fullChart rx (jU rev t) rz f) (fullChart rx (jU rev t) rz g)
      (fullChart rx (jU rev t) rz h) p :=
    ⟨transported f ha hf,transported g hgs hg,transported h hhs hh⟩
  have boundary :=hno rx (jU rev t) rz (IsLocalRing.residue V ∘ p)
    (by simpa only [b8A] using zeroAt_map (IsLocalRing.residue V) hz)
  have ex :rx=false := by
    cases rx
    · rfl
    · exact (boundary.1 rfl (hxu rfl).2).elim
  have ez :rz=false := by
    cases rz
    · rfl
    · exact (boundary.2.2 rfl (hzw rfl).2).elim
  subst rx
  subst rz
  have eu:x=(u:K) :=hu.symm
  have ew:z=(w:K) :=hw.symm
  cases rev <;> cases t
  · exact ⟨p,hz,eu,ew,hv.symm⟩
  · exact (boundary.2.1 rfl (hyv rfl).2).elim
  · have hres :IsLocalRing.residue V v≠0:=boundary.2.1 rfl
    have hnon : (v :K)∉V.nonunits := fun hmem =>
      hres ((IsLocalRing.residue_eq_zero_iff _).mpr (V.coe_mem_nonunits_iff.mp hmem))
    have vne : (v :K)≠0:= fun e=>hnon (e ▸ V.nonunits.zero_mem)
    have vin: (v :K)⁻¹∈V:= by
      by_contra hmem
      exact hnon (V.mem_nonunits_iff_or.mpr (Or.inr hmem))
    let p' : aax V := ![u,⟨(v :K)⁻¹,vin⟩,w]
    have hp' : V.subtype ∘ p' = ![(u:K),(v :K)⁻¹,(w:K)] := by
      funext i
      fin_cases i <;> rfl
    have hp₀:V.subtype ∘ p = ![(u:K),(v :K),(w:K)] := by
      funext i
      fin_cases i <;> rfl
    have return_chart {e b:ℕ} (F:LineData V e s b)
        (hF:eval p (fullChart false true false F)=0) :
        eval p' (fullChart false false false F)=0:= by
      have hF' := congrArg V.subtype hF
      rw [map_eval,b8A,hp₀,map_zero] at hF'
      apply integral_zero V
      rw [hp']
      rw [show fullChart false false false (push V.subtype F) =
        fullChart false (!true) false (push V.subtype F) from rfl]
      rw [flip_y (push V.subtype F) false true false _ vne _,hF',mul_zero]
    refine ⟨p',⟨return_chart f hz.1,return_chart g hz.2.1,return_chart h hz.2.2⟩,eu,ew,?_⟩
    change y*(v :K)⁻¹=1
    rw [show y=(v :K) from hv.symm,mul_inv_cancel₀ vne]
  · refine ⟨p,hz,eu,ew,?_⟩
    change y*(v :K)=1
    rw [show (v :K)=y⁻¹ from hv]
    exact mul_inv_cancel₀ ((hyv rfl).1)
end
end qzhw4Oa
end
end
