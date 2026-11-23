import ProximityPrize.SubmissionLower.Ztdy5wb
import ProximityPrize.SubmissionLower.ZFAtzgb
import ProximityPrize.SubmissionLower.ZhNzRYc
import ProximityPrize.SubmissionLower.ZfwYtia
import ProximityPrize.SubmissionLower.ZBlkecd
set_option Elab.async false
set_option maxHeartbeats 5000000
section
set_option autoImplicit true
set_option maxRecDepth 8192
namespace qXrbKzb
open P5_7_2 (fO)
open qoK3iCb (BandWitness)

open scoped qoK3iCb
private abbrev b:fO:=⟨8,by decide⟩
private def data :ℕ:=0x39424212fa174e2e3100f2094dd0b963394002001164d720498002000deade0231024215bf88c3902900f20a3b6e8d2c3100020013601f31414002000f76398941424210950fee633900f2088362a3ae31000200124e09c1414002000eb9766a39424213708253e03100f2097635b3da394022012404fa5049802200e9600e664182420ffcb2be343940f20850503c09414002000ef411df51c002000c00a8b9414b4a574b3902013940aa05dc6965304980aa04798028a05a00aa03925bd31f49b8736d37effda43940f207db2ff440418032016357cdf059c032011ddeabce51f8734aa1df46be41800a004741942659c032010ff5a6a672403200daaba99441424210d4feb0c7414022010b50da0351c02200cc15b05f6a402200a2b6515241400a004b7a947641800a0047d4cc8859c00a0036d8ec627240020008b04e1a62035210fc8d4ad162002200b3124c9f7a83520d597aa2a59b43520ab3186b8459c0aa03a0d1512259c0aa03c383d2a47240aa02df828fee9300aa024e26fbaa6a43520f394d7d8e6a00aa03300931c08ac3520c2a9119eaab835209c6490092
private theorem w:BandWitness b:=witnesses!
theorem band8:y8 b 4 :=grid_of_tests (data :=data) w (by
 intro o t
 fin_cases o <;> fin_cases t <;> (exact az (.inl checked!)))
end qXrbKzb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qVHIGFe
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open qb0hmCe (cLN)
open q1kuFjb (expansion_coeff)
open qNu3xvc qoCymac qhFwyvc
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private fVm bnm from ProximityPrize.SubmissionLower.ZfwYtia
open private chartIntegral from ProximityPrize.SubmissionLower.ZiuGIoc
private theorem bXI {E :Type} [Field E] (F:E[X][X]) (i:ℕ) :
  (physicalDerivative F).coeff i=(F.coeff i).derivative := by
 rw [physicalDerivative,sum_coeff _ (by simp)]
private theorem coeff_nat {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (j:ℕ) (e :E) :
  (a (e*(j:E))).coeff 0=(a e).coeff 0*(j:L) := by
 have h:a (j:E)=HahnSeries.C (j:L) := calc
  _=a (algebraMap L E (j:L)) := by simp only [map_natCast]
  _ = _:=(a.commutes _).trans (LaurentSeries.algebraMap_apply L _)
 rw [map_mul,h,mul_comm,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul,mul_comm]
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
 (S:Sections A) (γ:K) (hγ:γ∈S.marks) {δ:Derivation L E E} {r :Bool}
private abbrev reduce :=mapRingHom (mapRingHom (reduceSeed S γ hγ))
private theorem red_coeff (J:nC (S.place γ)) (i j:ℕ) :
  ((reduce S γ hγ J).coeff i).coeff j =
    ((S.atPlace γ hγ) (((includeCoeffs (S.place γ) J).coeff i).coeff j)).coeff 0:= by
 simp only [reduce,coe_mapRingHom,coeff_map,reduceSeed_eq]
 rfl
private theorem reduce_jets (hδ:LocalDerivation (S.atPlace γ hγ) (S.place γ) δ)
   (J:EM A (S.place γ) δ r) :
   let F:=cLN (S.atPlace γ hγ) 0 (chartEq A r)
   reduce S γ hγ J.sep=F.derivative ∧
   reduce S γ hγ J.dx = -physicalDerivative F ∧
   reduce S γ hγ J.num = -cLN (S.atPlace γ hγ) 1 (chartEq A r) := by
 dsimp only
 refine ⟨?_,?_,?_⟩ <;> apply Polynomial.ext fun i=>Polynomial.ext fun j => ?_
 · rw [red_coeff,J.sep_map,coeff_derivative,coeff_derivative,
     ← Nat.cast_succ,← Nat.cast_succ,coeff_mul_natCast,coeff_mul_natCast,coeff_nat,
     expansion_coeff]
 · rw [red_coeff,J.dx_map,coeff_neg,coeff_neg,map_neg,HahnSeries.coeff_neg,
     coeff_neg,coeff_neg,bXI,bXI,coeff_derivative,coeff_derivative,
     ← Nat.cast_succ,← Nat.cast_succ,coeff_nat,expansion_coeff]
 · rw [red_coeff,J.num_map,coeff_neg,coeff_neg,map_neg,HahnSeries.coeff_neg,
     coeff_neg,coeff_neg,seedDerivative,sum_coeff _ (by simp [Polynomial.sum_def]),
     sum_coeff _ (by simp),expansion_coeff]
   exact congrArg Neg.neg ((hδ _ (chartIntegral A _ (S.regular γ hγ) r i j)).2)
private theorem expand_reflect (k :ℤ) :
  cLN (S.atPlace γ hγ) k (chartEq A true) =
   (cLN (S.atPlace γ hγ) k A.f).reflect A.d:= by
 apply Polynomial.ext fun i=>Polynomial.ext fun j => ?_
 simp only [expansion_coeff,chartEq,ite_true,coeff_reflect,coeff_reverse]
private theorem expansion_degree (k :ℤ) : (cLN (S.atPlace γ hγ) k A.f).natDegree≤A.d:= by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 apply Polynomial.ext fun j => ?_
 simp [expansion_coeff,coeff_eq_zero_of_natDegree_lt hi]
private theorem c7J (F:L[X][X]) {d:ℕ} (hd:F.natDegree≤d)
   {y z :FX} (hyz :y*z=1) :
   (F.reflect d).eval₂ phys z=z^d*F.eval₂ phys y := by
 let:Invertible y :=invertibleOfRightInverse y z hyz
 calc
   _=z^d*((F.reflect d).eval₂ phys z*y^d) := by
     rw [mul_left_comm,← mul_pow,mul_comm z y,hyz,one_pow,mul_one]
   _ = _:=congrArg (z^d * ·) (eval₂_reflect_mul_pow phys y d F hd)
private theorem reflect_root_sep (F:L[X][X]) {y z :FX} (hyz :y*z=1)
  (hF:F.eval₂ phys y=0) :
  F.reverse.eval₂ phys z=0 ∧
    (F.reverse.derivative.eval₂ phys z) = -(z^F.natDegree*y^2*F.derivative.eval₂ phys y) := by
 have hz :z≠0:= fun e=> by simp [e] at hyz
 have hrev :F.reverse.eval₂ phys z=0:= by
  change (F.reflect F.natDegree).eval₂ phys z=0
  rw [c7J _ le_rfl hyz,hF,mul_zero]
 refine ⟨hrev,mul_left_cancel₀ hz ?_⟩
 have hd: (Polynomial.X*F.derivative).natDegree≤F.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [bnm,coeff_eq_zero_of_natDegree_lt hi,zero_mul]
 have h:=congrArg (fun f :L[X][X]=>f.eval₂ phys z) (fVm F)
 simp only [eval₂_add,eval₂_mul,eval₂_X,hrev,mul_zero,c7J _ hd hyz] at h
 calc
  z*F.reverse.derivative.eval₂ phys z = -(z^F.natDegree*(y*F.derivative.eval₂ phys y)) :=
    eq_neg_of_add_eq_zero_right h
  _=z * -(z^F.natDegree*y^2*F.derivative.eval₂ phys y) := by
    conv_lhs=>rw [← one_mul (-(z^F.natDegree*(y*F.derivative.eval₂ phys y))),← hyz]
    ring
theorem formula :qhFwyvc.c2 := by
  intro E _ _ A S γ hγ δ hδ r hr J
  obtain ⟨hs,hx,hn⟩:=reduce_jets S γ hγ hδ J
  let P:=S.P γ
  let Q:=S.Q γ
  let a :=S.atPlace γ hγ
  let F:=cLN a 0 A.f
  let G:=cLN a 1 A.f
  let y :=phys P/phys Q
  have hF:F.eval₂ phys y=0:=S.root γ hγ
  have hS:F.derivative.eval₂ phys y≠0:=S.simple γ hγ
  have hQ:phys Q≠0:= fun e=>(S.denom γ hγ) (IsFractionRing.injective L[X] FX (e.trans (map_zero phys).symm))
  have hT:phys (S.num γ)/phys (S.den γ) =
      -(G.eval₂ phys y/F.derivative.eval₂ phys y)*phys Q^2 :=S.formula γ hγ
  dsimp only
  have atSpec (J:nC (S.place γ)) :aJB S γ hγ r J =
      (reduce S γ hγ J).eval₂ phys (sectionOrdinate P Q r) :=rfl
  simp only [atSpec,hs,hx,hn,eval₂_neg]
  cases r
  · change F.derivative.eval₂ phys y≠0 ∧
      -(physicalDerivative F).eval₂ phys y/F.derivative.eval₂ phys y =
        phys (P.derivative*Q-P*Q.derivative)/phys Q^2∧_
    refine ⟨hS,section_jet F P Q hF hS,?_⟩
    rw [hT]
    change -(G.eval₂ phys y)/F.derivative.eval₂ phys y =
      (phys Q^2)⁻¹*(-(G.eval₂ phys y/F.derivative.eval₂ phys y)*phys Q^2)
    rw [neg_div,mul_left_comm,inv_mul_cancel₀ (pow_ne_zero _ hQ),mul_one]
  · let z :=phys Q/phys P
    have hP:phys P≠0:= fun e=>hr rfl (IsFractionRing.injective L[X] FX (e.trans (map_zero phys).symm))
    have hyz :y*z=1 := by dsimp [y,z]; field_simp [hP,hQ]
    have hdeg:F.natDegree=A.d:=S.degree γ hγ
    have hrev :F.reflect A.d=F.reverse := by rw [← hdeg]; rfl
    obtain ⟨hR,hsep⟩:=reflect_root_sep F hyz hF
    have hG:=c7J G (expansion_degree S γ hγ 1) hyz
    let sr :=F.reverse.derivative.eval₂ phys z
    have hsr :sr≠0:= by
      change F.reverse.derivative.eval₂ phys z≠0
      rw [hsep,hdeg]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (div_ne_zero hQ hP))
        (pow_ne_zero _ (div_ne_zero hP hQ))) hS)
    simp only [expand_reflect S γ hγ,
      ← show F=cLN (S.atPlace γ hγ) 0 A.f from rfl,
      ← show G=cLN (S.atPlace γ hγ) 1 A.f from rfl,hrev]
    change sr≠0 ∧ -(physicalDerivative F.reverse).eval₂ phys z/sr =
      phys (Q.derivative*P-Q*P.derivative)/phys P^2 ∧
      -((G.reflect A.d).eval₂ phys z)/sr =
        -(phys P^2)⁻¹*(phys (S.num γ)/phys (S.den γ))
    refine ⟨hsr,section_jet F.reverse Q P hR hsr,?_⟩
    rw [hT,hG,show sr= _ from hsep,hdeg]
    have hd:z^A.d≠0:=pow_ne_zero _ (div_ne_zero hQ hP)
    rw [div_eq_iff (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ (div_ne_zero hP hQ))) hS))]
    generalize F.derivative.eval₂ phys y=t at hS ⊢
    dsimp only [y]
    field_simp [hP,hQ,hS]
end
end qVHIGFe
end
