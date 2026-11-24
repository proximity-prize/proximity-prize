import ProximityPrize.SubmissionLower.AR
import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZW31ykd
import ProximityPrize.SubmissionLower.ZZ4xzRc
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
open _root_ renaming Finsupp.optionElim_some → zX5, Finsupp.some_optionElim → zpo, Finsupp.weight_optionElim → zVB, Function.Injective → zq4, LinearMap.finrank_le_finrank_of_injective → zdv, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, Submodule.mem_bot → zLn
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
section
set_option autoImplicit true
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2542 rfl (by decide +kernel) (by decide +kernel)
private theorem cc9:GG kA 108 3:=⟨kU,kU,kU,True.intro⟩
private theorem r111 :GG kA 111 3:=⟨kU,kU,kU,True.intro⟩
private theorem r114 :GG kA 114 3:=⟨kU,kU,kU,True.intro⟩
private theorem r117:GG kA 117 4 :=⟨kU,kU,kU,kU,True.intro⟩
theorem s :GG kA 108 13 :=
 appendGrades (appendGrades (appendGrades cc9 r111) r114) r117
end qyV6B3d
end
section
set_option autoImplicit true
namespace qmRQvQa
noncomputable section
open i4 P5_8 P5_8_3 PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial Finset
open private mem_rows from ProximityPrize.SubmissionLower.ZvFuy6d
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
private abbrev weight:=differentialWeight (d:=2) N
private abbrev Exponent:=Fin 3 →₀ ℕ
private def boundaryExponent (T:ℕ) (u:Exponent) :JetVariable 2 →₀ ℕ :=
 u.optionElim (T - u.weight (fun j=>N - j.val))
private theorem boundary_inj (T:ℕ) :zq4 (boundaryExponent T) :=
 fun _ _ h=> by
  simpa only [boundaryExponent,zpo] using congrArg Finsupp.some h
private def pullback {F α β:Type} [Semiring F] {f :α→β} (hf :zq4 f) :
   AddMonoidAlgebra F β →ₗ[F] AddMonoidAlgebra F α :=
 (AddMonoidAlgebra.coeffLinearEquiv F (S:=F) (M:= α)).symm.toLinearMap ∘ₗ
   Finsupp.lcomapDomain (R:=F) (M:=F) f hf ∘ₗ
   (AddMonoidAlgebra.coeffLinearEquiv F (S:=F) (M:=β)).toLinearMap
private def boundary (T:ℕ) :Equation →ₗ[K] z3y (Fin 3) K :=
 pullback (boundary_inj T)
private theorem boundary_coeff (T:ℕ) (R:Equation) (u:Exponent) :
  (boundary T R).coeff u=R.coeff (boundaryExponent T u) := by
 change (Finsupp.comapDomain (boundaryExponent T) (AddMonoidAlgebra.coeff R) (boundary_inj T).injOn) u= _
 exact Finsupp.comapDomain_apply _ _ _ _
private theorem bVx {T:ℕ} {R:Equation}
    (hR:R.weightedTotalDegree weight≤T) (hz :boundary T R=0) :
    ∀ u∈R.support,u.weight weight<T:= by
  intro u hu
  apply lt_of_le_of_ne ((le_weightedTotalDegree weight hu).trans hR)
  intro he
  have hw:u.weight weight=u none+u.some.weight (fun j=>N - j.val) := by
    calc
      _=(u.some.optionElim (u none)).weight weight:= by rw [zX5]
      _ = _:= by
        have h:weight=fun j=>j.elim 1 (fun i=>N - i.val) := by
          funext j
          cases j <;> rfl
        rw [h,zVB,one_mul]
  have hx :boundaryExponent T u.some=u:= by
    rw [boundaryExponent,← he,hw,Nat.add_sub_cancel,zX5]
  have hc:=congrArg (fun P:z3y (Fin 3) K=>P.coeff u.some) hz
  rw [boundary_coeff,hx,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
  exact (mem_support_iff.mp hu) hc
private theorem boundary_band {s :Jn} {R:Equation} (hR:R∈nativeBand s) (T:ℕ) :
   boundary T R∈symbolBand s := by
 apply (mem_restrictSupport_iff K).mpr
 intro u hu
 have hm:boundaryExponent T u∈R.support :=
   mem_support_iff.mpr (by simpa only [boundary_coeff] using mem_support_iff.mp hu)
 have ⟨hB,hJ,hC⟩:=mem_nativeBand.mp hR
 refine ⟨?_,?_,?_⟩
 · have h:=(le_weightedTotalDegree jetDegreeWeight hm).trans hB
   have hw: (jetDegreeWeight:JetVariable 2→ℕ)=fun j=>j.elim 0 (fun _=>1) := by
    funext j
    cases j <;> rfl
   simpa only [hw,Finsupp.weight_elim_zero_one,boundaryExponent,zpo] using h
 · have h:=(le_weightedTotalDegree i4.indexWeight hm).trans hJ
   change (boundaryExponent T u).weight (fun j=>j.elim 0 Fin.val)≤ s.J at h
   simpa only [boundaryExponent,zVB,zero_mul,zero_add] using h
 · have h:=(monomial_le_degreeOf (some (Fin.last 2)) hm).trans hC
   simpa only [boundaryExponent,Finsupp.optionElim_apply_some] using h
private instance finiteSymbols (s :Jn) :zAa K (symbolBand s) := by
 let v := fun _:Fin 3=>(1 :ℕ)
 let W:Submodule K (z3y (Fin 3) K) :=restrictWeightedDegree v s.B
 let:zAa K W :=
  Module.Finite.iff_fg.mpr (restrictWeightedDegree_fg v (fun _=>one_ne_zero) s.B)
 apply Submodule.finiteDimensional_of_le (S₂:=W)
 apply restrictSupport_mono
 intro u hu
 change u.weight (fun _=>1)≤ s.B
 rw [← Finsupp.degree_eq_weight_one]
 exact hu.1
private def previous (w:Node→K) (T:ℕ) :Submodule K Equation :=
 if T=0 then ⊥ else rows w (T - 1)
private instance finitePrevious (w:Node→K) (T:ℕ) :
   zAa K (previous w T) := by
 by_cases h:T=0
 · rw [previous,ite_eq_left h]
   infer_instance
 · rw [previous,ite_eq_right h]
   infer_instance
private theorem caps_pow (G:Equation) (hG:G≠0) (l:ℕ) :
    caps (G^l)=powerCaps (caps G) l:= by
  have hw (v :JetVariable 2→ℕ) (r :ℕ) :
      (G^r).weightedTotalDegree v=r*G.weightedTotalDegree v := by
    induction r with
    | zero=>rw [pow_zero,← C_1,weightedTotalDegree_C,Nat.zero_mul]
    | succ r ih =>
      calc
        _=(G^r*G).weightedTotalDegree v :=congrArg (weightedTotalDegree v) (pow_succ G r)
        _ = _:=(weightedTotalDegree_mul v (G^r) G (pow_ne_zero _ hG) hG).trans
          ((congrArg (· + G.weightedTotalDegree v) ih).trans (Nat.succ_mul ..).symm)
  unfold caps powerCaps jetTotalDegree jetDegree
  rw [hw,hw,← weightedTotalDegree_piSingle,← weightedTotalDegree_piSingle,hw]
private theorem S6 (w:Node→K) (T:ℕ) (H :Equation) (hH :H≠0)
    (hd : ∀ R∈rows w T,H∣R) :
    zsE K (rows w T)≤zsE K (previous w T) +
      if dM (caps H) donorCaps then
        zsE K (symbolBand (donorCaps.wD (caps H))) else 0:= by
  classical
  by_cases hs :dM (caps H) donorCaps∧H.weightedTotalDegree weight≤T
  swap
  · have he :rows w T = ⊥ := by
      apply bot_unique
      intro R hR
      rw [zLn]
      by_contra hn
      obtain ⟨hc,hw,_⟩:=mem_rows.mp hR
      have ⟨hb,hj,ht⟩:=caps_dvd (hd R hR) hn
      have ⟨cb,cj,ct⟩:=mem_nativeBand.mp hc
      exact hs ⟨⟨hb.trans cb,hj.trans cj,ht.trans ct⟩,
        (weightedTotalDegree_le_of_dvd weight (hd R hR) hn).trans hw⟩
    rw [he,finrank_bot]
    exact Nat.zero_le _
  rw [ite_eq_left hs.1]
  let mulH :=LinearMap.mulLeft K H
  let Q:=(rows w T).comap mulH
  let m:Q →ₗ[K] rows w T :=
    (mulH.comp Q.subtype).codRestrict _ (fun L=>L.property)
  have hm:zq4 m:= by
    intro L R he
    exact Subtype.ext (mul_left_cancel₀ hH (congrArg Subtype.val he))
  have hsurj:Function.Surjective m:= by
    intro R
    obtain ⟨L,hL⟩:=hd R.val R.property
    refine ⟨⟨L,?_⟩,Subtype.ext hL.symm⟩
    change H*L∈rows w T
    rw [← hL]
    exact R.property
  let e :=LinearEquiv.ofBijective m ⟨hm,hsurj⟩
  let:zAa K Q:=Module.Finite.of_injective m hm
  let s :=donorCaps.wD (caps H)
  let U:=T - H.weightedTotalDegree weight
  have hcap (L:Q) :L.val∈nativeBand s := by
    by_cases hz :L.val=0
    · rw [hz]
      exact Submodule.zero_mem _
    · have hn: (m L).val≠0:=mul_ne_zero hH hz
      exact mem_nativeBand.mpr
        (c54 hn dvd_rfl rfl (mem_nativeBand.mp (mem_rows.mp (m L).property).1))
  let b:Q →ₗ[K] symbolBand s :=
    ((boundary U).comp Q.subtype).codRestrict _ (fun L=>boundary_band (hcap L) U)
  have hb:zsE K b.range≤zsE K (symbolBand s) :=
    zdv b.range.subtype_injective
  have hk (L:b.ker) :H*L.val.val∈previous w T:= by
    obtain ⟨hc,hw,hl⟩:=mem_rows.mp (m L.val).property
    change (H*L.val.val).weightedTotalDegree weight≤T at hw
    have hstrict (hn:L.val.val≠0) : (H*L.val.val).weightedTotalDegree weight<T:= by
      have hz :boundary U L.val.val=0:=congrArg Subtype.val (LinearMap.mem_ker.mp L.property)
      rw [weightedTotalDegree_mul _ _ _ hH hn] at hw ⊢
      have hle :L.val.val.weightedTotalDegree weight≤U:=Nat.le_sub_of_add_le (by omega)
      obtain ⟨u,hu⟩:=support_nonempty.mpr hn
      have hu' := bVx hle hz u hu
      have hlt:L.val.val.weightedTotalDegree weight<U :=
        (Finset.sup_lt_iff (by omega :0<U)).mpr (bVx hle hz)
      exact (Nat.add_lt_add_left hlt _).trans_le (Nat.add_sub_of_le hs.2).le
    unfold previous
    split
    · rename_i hT
      rw [zLn]
      by_contra hn
      have :=hstrict (right_ne_zero_of_mul hn)
      omega
    · rename_i hT
      refine mem_rows.mpr ⟨hc,?_,hl⟩
      by_cases hn:L.val.val=0
      · rw [hn,mul_zero]
        exact Nat.zero_le _
      · exact Nat.le_sub_one_of_lt (hstrict hn)
  let g:b.ker →ₗ[K] previous w T :=
    ((mulH.comp Q.subtype).comp b.ker.subtype).codRestrict _ hk
  have hker :zsE K b.ker≤zsE K (previous w T) := by
    apply zdv (f :=g)
    intro L R he
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hH (congrArg Subtype.val he)))
  rw [← e.finrank_eq,← b.finrank_range_add_finrank_ker,Nat.add_comm]
  exact Nat.add_le_add hker hb
private theorem telescope (w:Node→K) (W:ℕ) (c:ℕ→ℕ)
   (h : ∀ T≤W,zsE K (rows w T)≤zsE K (previous w T)+c T) :
   zsE K (rows w W) ≤ ∑ T∈range (W+1),c T:= by
 induction W with
 | zero =>
   have h0:previous w 0 = ⊥ := by simp [previous]
   have hh:=h 0 le_rfl
   rw [h0,finrank_bot,zero_add] at hh
   simpa only [Nat.zero_add,sum_range_one] using hh
 | succ W ih =>
   have hW:=h (W+1) le_rfl
   have hprev :previous w (W+1)=rows w W:= by simp [previous]
   rw [hprev] at hW
   rw [sum_range_succ]
   exact hW.trans (Nat.add_le_add_right (ih (fun T hT=>h T (hT.trans (Nat.le_succ W)))) _)
end
end qmRQvQa
end
