import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZPKTqyb
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qZcMfNa
noncomputable section
open Polynomial Finset
open P5 (K I)
open cu (L FX)
open Cu (sQ)
open E7 (CurvePlace)
open agN (b27)
open q82zwcd (WordChart DualSheet)
open qBd5KZd (MarkedCurve Allowance mass small btN bounded)
open qb0hmCe (cLN specialize)
open q1kuFjb (IntSeries residue Ua liftAt_reduce coeff_liftAt small_valuation principal)
open qFD8jve (sheetPole)
open P5_7_7 (phys)
open private efc aMX from ProximityPrize.SubmissionLower.Y
open scoped Classical WithZero
theorem mass_eq {T:Type} (A:T →₀ ℕ) :mass A=A.sum (fun _ n=>n) := by
 rw [mass,Finsupp.liftAddHom_apply]
 rfl
theorem cleared_map {E F:Type} [CommRing E] [CommRing F] (a :E →+* F)
  (n:ℕ) (P Q:E[X]) (f :E[X][X]) :
  (BA n P Q f).map a=BA n (P.map a) (Q.map a) (f.map (mapRingHom a)) := by
 simp only [BA,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,coeff_map,
  coe_mapRingHom]
private theorem cleared_scale {E :Type} [CommRing E] (n:ℕ)
  (P Q:E[X]) (f :E[X][X]) (a :E) :
  BA n P Q (C (C a)*f)=C a*BA n P Q f := by
 simp only [BA,coeff_C_mul,mul_sum,mul_assoc]
private theorem cleared_zero {f :L[X][X]} {P Q:L[X]} {n:ℕ}
   (hn:f.natDegree≤n) (hQ:Q≠0) (hroot :specialize f P Q=0) :
   BA n P Q f=0:= by
 have hQ' : phys Q≠0:=(map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr hQ
 have h:phys (BA n P Q f)=specialize f P Q*phys Q^n:= by
   unfold specialize
   rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hn)]
   simp only [BA,map_sum,map_mul,map_pow,sum_mul]
   apply sum_congr rfl
   intro i hi
   have hn' : i+(n-i)=n:=Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hi))
   have he : (phys P/phys Q)^i*phys Q^n=phys P^i*phys Q^(n-i) := by
     rw [← hn',pow_add,div_pow,← mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hQ')]
     rw [hn']
   simp only [mul_assoc,he]
 rw [hroot,zero_mul] at h
 exact (map_eq_zero_iff _ (IsFractionRing.injective L[X] FX)).mp h
private theorem residue_order {E :Type} [Field E] [Algebra L E]
   (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (P Q:L[X]) (n:ℕ)
   (hf : ∀ i j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (a ((f.coeff i).coeff j))≤1)
   (hz :BA n P Q (cLN a 0 f)=0) (i:ℕ) :
   (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (a ((BA n (P.map (algebraMap L E)) (Q.map (algebraMap L E)) f).coeff i)) ≤
     WithZero.exp (-1) := by
 let b:L →+* IntSeries :=
   (LaurentSeries.powerSeriesEquivSubring L).toRingHom.comp PowerSeries.C
 let c:IntSeries →+* LaurentSeries L:=(LaurentSeries.powerSeries_as_subring L).subtype
 let g:=BA n (P.map b) (Q.map b) (Ua a f hf)
 have hr :residue.comp b=RingHom.id L:= by
   ext x
   change PowerSeries.constantCoeff ((LaurentSeries.powerSeriesEquivSubring L).symm
     (LaurentSeries.powerSeriesEquivSubring L (PowerSeries.C x)))=x
   rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_C]
 have h0:g.map residue=0:= by
   change (BA n (P.map b) (Q.map b) (Ua a f hf)).map residue=0
   rwa [cleared_map,liftAt_reduce,Polynomial.map_map,Polynomial.map_map,hr,Polynomial.map_id,Polynomial.map_id]
 have hc:c.comp b=a.toRingHom.comp (algebraMap L E) := by
   apply RingHom.ext
   intro x
   change ((LaurentSeries.powerSeriesEquivSubring L (PowerSeries.C x) :IntSeries) :
     LaurentSeries L)=a (algebraMap L E x)
   rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,PowerSeries.coe_C,a.commutes,
     LaurentSeries.algebraMap_apply]
 have hm: (Ua a f hf).map (mapRingHom c)=f.map (mapRingHom a.toRingHom) := by
   apply Polynomial.ext
   intro i
   apply Polynomial.ext
   intro j
   simp only [coeff_map,coe_mapRingHom]
   exact coeff_liftAt a f hf i j
 have he :g.map c=(BA n (P.map (algebraMap L E)) (Q.map (algebraMap L E)) f).map
     a.toRingHom:= by
   simp only [g,cleared_map,Polynomial.map_map,hc,hm]
 have hv : ∀ x :IntSeries,residue x=0 →
     (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (x :LaurentSeries L)≤WithZero.exp (-1) := by
   intro x hx
   obtain ⟨y,rfl⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective x
   rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,small_valuation]
   change PowerSeries.constantCoeff ((LaurentSeries.powerSeriesEquivSubring L).symm
     (LaurentSeries.powerSeriesEquivSubring L y))=0 at hx
   rwa [RingEquiv.symm_apply_apply] at hx
 have hh:=hv (g.coeff i) (by rw [← coeff_map,h0,coeff_zero])
 change (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (c (g.coeff i))≤_ at hh
 rwa [← coeff_map,he,coeff_map] at hh
theorem prepare {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
    {q:sQ} {z :K→K} {J:WordChart D w U s} (F:DualSheet J q z) :
    let C:MarkedCurve U:=⟨F.curve.E,F.curve.curve,
      ⟨fun t=>F.place t,fun t u h=>Subtype.ext (F.distinct t.property u.property h)⟩⟩
    ∃ A:Allowance C.E,mass A=F.h∧bounded A F.f ∧
      roots C (fun t=>J.P t) (fun t=>J.Q t) 1 F.f A:= by
  dsimp only
  let B (v :CurvePlace L F.curve.E) :=sheetPole v.value F.f
  have hB:B.HasFiniteSupport:=b27 (principal F.curve) _
  let A:=Finsupp.ofSupportFinite B hB
  refine ⟨A,?_,fun i j v=>qrezXJe.sheet_bound v.value F.f i j,?_⟩
  · rw [mass_eq]
    change A.sum (fun _ n=>n) = ∑ᶠ v,B v
    rw [finsum_eq_finsetSum_of_support_subset _ (s :=hB.toFinset)
      (fun v hv=>hB.mem_toFinset.mpr hv)]
    rfl
  · intro t i
    let a :=F.atPlace t t.property
    let v :=F.place t
    let u:F.curve.E :=F.scale t
    let g:=C (C u)*F.f
    let P:=(J.P t).map (algebraMap L F.curve.E)
    let Q:=(J.Q t).map (algebraMap L F.curve.E)
    have hinter (i j:ℕ) : (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
        (a ((g.coeff i).coeff j))≤1 := by
      rw [← F.value t t.property,show g=C (C u)*F.f from rfl,coeff_C_mul,coeff_C_mul]
      exact F.integral t t.property i j
    have hdeg: (cLN a 0 g).natDegree≤F.d:= by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      apply Polynomial.ext
      intro k
      rw [q1kuFjb.expansion_coeff,show g=C (C u)*F.f from rfl,coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt hj,mul_zero,coeff_zero,map_zero,HahnSeries.coeff_zero,
        coeff_zero]
    have hroot :=cleared_zero hdeg (J.denominator t t.property) (F.root t t.property)
    have hh:=residue_order a g (J.P t) (J.Q t) F.d hinter hroot i
    rw [← F.value t t.property] at hh
    change v.value ((BA F.d P Q g).coeff i)≤_ at hh
    rw [show g=C (C u)*F.f from rfl,cleared_scale,coeff_C_mul,map_mul] at hh
    let x :=(BA F.d P Q F.f).coeff i
    change small v ((B v :ℤ)-1) x
    by_cases hx :x=0
    · simp [small,hx]
    have hu:=v.value.ne_zero_iff.mpr (Units.ne_zero (F.scale t))
    have hx' := v.value.ne_zero_iff.mpr hx
    change v.value u*v.value x≤_ at hh
    have hlog:=(WithZero.log_le_iff_le_exp (mul_ne_zero hu hx')).mpr hh
    rw [WithZero.log_mul hu hx'] at hlog
    change WithZero.log (v.value u)+WithZero.log (v.value x) ≤ -1 at hlog
    have hlo:=qxDtRld.scale_log F t.property
    change -(B v :ℤ)≤WithZero.log (v.value u) at hlo
    exact (WithZero.log_le_iff_le_exp hx').mp (by omega)
theorem resultant_bounded {E :Type} [Field E] [Algebra L E] {f G:E[X][X]}
   {A B:Allowance E} (hf :bounded A f) (hG:bounded B G) (j:ℕ) :
   (f.resultant G).coeff j∈btN (f.natDegree•B+G.natDegree•A) := by
 intro v
 let m:=f.natDegree
 let n:=G.natDegree
 let w:=efc v.value
 let cost:Fin (m+n)→ℤ:= fun i=>Fin.addCases (fun _=>(B v :ℤ)) (fun _=>(A v :ℤ)) i
 let M:=f.sylvester G m n
 have hentry (i j:Fin (m+n)) :w (M i j)≤WithZero.exp (cost j) := by
   refine Fin.addCases ?_ ?_ j
   · intro k
     simp only [M,cost,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · exact Finset.sup_le fun r _=>hG _ r v
     · simp
   · intro k
     simp only [M,cost,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · exact Finset.sup_le fun r _=>hf _ r v
     · simp
 refine (aMX v.value _ j).trans ?_
 change w M.det≤WithZero.exp (((m•B+n•A) v :ℕ) :ℤ)
 have he : ∏ i,WithZero.exp (cost i)=WithZero.exp (((m•B+n•A) v :ℕ) :ℤ) := by
   rw [Fin.prod_univ_add]
   simp only [cost,Fin.addCases_left,Fin.addCases_right,prod_const,card_univ,
     Fintype.card_fin,← WithZero.exp_nsmul,← WithZero.exp_add,nsmul_eq_mul,
     Finsupp.add_apply,Finsupp.smul_apply,Nat.cast_add,Nat.cast_mul]
   rfl
 rw [← he,Matrix.det_apply]
 apply w.map_sum_le
 intro σ _
 have hterm :w (∏ i,M (σ i) i) ≤ ∏ i,WithZero.exp (cost i) := by
   rw [map_prod]
   exact prod_le_prod fun i _=>hentry (σ i) i
 rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
   simpa [hs,Valuation.map_neg] using hterm
end
end qZcMfNa
