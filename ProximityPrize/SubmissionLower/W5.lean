import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.G1
import ProximityPrize.SubmissionLower.V6
namespace ProximityPrize.SubmissionLower.RCN359
open scoped Classical nonZeroDivisors WithZero
open IsDedekindDomain
noncomputable section
section NormalizedEquality
variable {L:Type*} [Field L]
local instance:DecidableEq L:=Classical.decEq L
theorem value_le_exp_neg_one {z:ℤᵐ⁰} (hz:z < 1):
   z ≤ WithZero.exp (-1:ℤ):=by
 by_cases hz0:z=0
 · simp [hz0]
 have hlog:z.log < 0:=by
   have h:WithZero.exp z.log < WithZero.exp (0:ℤ):=by
     simpa only [WithZero.exp_log hz0,WithZero.exp_zero] using hz
   exact WithZero.exp_lt_exp.mp h
 calc
   z=WithZero.exp z.log:=(WithZero.exp_log hz0).symm
   _ ≤ WithZero.exp (-1:ℤ):=WithZero.exp_le_exp.mpr (by omega)
theorem eq_of_equiv_surjective (v w:Valuation L ℤᵐ⁰)
   (hv:Function.Surjective v) (hw:Function.Surjective w)
   (h:v.IsEquiv w):v=w:=by
 have hneg:WithZero.exp (-1:ℤ) < 1:=by
   rw [←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hvπlt:v π < 1:=hπ ▸ hneg
 have hwπlt:w π < 1:=h.lt_one_iff_lt_one.mp hvπlt
 have hlower:WithZero.exp (-1:ℤ) ≤ w π:=by
   obtain ⟨a,ha⟩:=hw (WithZero.exp (-1:ℤ))
   have haw:w a < 1:=ha ▸ hneg
   have hav:v a < 1:=h.lt_one_iff_lt_one.mpr haw
   have hal:v a ≤ v π:=hπ ▸ value_le_exp_neg_one hav
   have hal':w a ≤ w π:=(h a π).mp hal
   simpa only [ha] using hal'
 have hwπ:w π=WithZero.exp (-1:ℤ):=
   le_antisymm (value_le_exp_neg_one hwπlt) hlower
 ext x
 by_cases hx:x=0
 · simp [hx]
 have hvx:v x≠0:=(Valuation.ne_zero_iff v).mpr hx
 have hpower:v (π^(-(v x).log))=v x:=by
   simp [hπ,WithZero.exp_log hvx]
 have hpower':w (π^(-(v x).log))=v x:=by
   simp [hwπ,WithZero.exp_log hvx]
 exact hpower'.symm.trans (h.eq_iff.mp hpower)
end NormalizedEquality
section UnitBall
variable (R L:Type*) [CommRing R] [Field L] [Algebra R L]
variable (v:Valuation L ℤᵐ⁰) (hR:∀ r:R,v (algebraMap R L r) ≤ 1)
def unitBallMap:R →+*v.valuationSubring where
 toFun r:=⟨algebraMap R L r,hR r⟩
 map_zero':=Subtype.ext (map_zero _)
 map_one':=Subtype.ext (map_one _)
 map_add' r s:=Subtype.ext (map_add _ r s)
 map_mul' r s:=Subtype.ext (map_mul _ r s)
include hR in
theorem integral_le_one {x:L} (hx:IsIntegral R x):v x ≤ 1:=by
 letI:Algebra R v.valuationSubring:=(unitBallMap R L v hR).toAlgebra
 letI:IsScalarTower R v.valuationSubring L:=
   IsScalarTower.of_algebraMap_eq' rfl
 have hx':IsIntegral v.valuationSubring x:=hx.tower_top
 exact (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp hx'
def centerIdeal:Ideal R:=
 Ideal.comap (unitBallMap R L v hR) (IsLocalRing.maximalIdeal v.valuationSubring)
instance centerIdeal_isPrime:(centerIdeal R L v hR).IsPrime:=by
 unfold centerIdeal
 infer_instance
theorem mem_centerIdeal (r:R):
   r∈centerIdeal R L v hR ↔ v (algebraMap R L r) < 1:=by
 change unitBallMap R L v hR r∈IsLocalRing.maximalIdeal v.valuationSubring ↔ _
 exact Valuation.mem_maximalIdeal_iff L v
end UnitBall
section Center
variable (S L:Type*) [CommRing S] [IsDedekindDomain S] [Field L]
variable [Algebra S L] [IsFractionRing S L]
variable (v:Valuation L ℤᵐ⁰) (hS:∀ s:S,v (algebraMap S L s) ≤ 1)
theorem centerIdeal_ne_bot (hv:Function.Surjective v):
   centerIdeal S L v hS≠⊥:=by
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hπ0:π≠0:=by
   apply (Valuation.ne_zero_iff v).mp
   rw [hπ]
   exact WithZero.exp_ne_zero
 obtain ⟨a,b,hb,hfrac⟩:=IsFractionRing.div_surjective (A:=S) π
 have hb0:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have ha0:a≠0:=by
   intro hzero
   apply hπ0
   simpa [hzero] using hfrac.symm
 have hvb0:v (algebraMap S L b)≠0:=
   (Valuation.ne_zero_iff v).mpr (by
     simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0)
 have hfraclt:v (algebraMap S L a)/v (algebraMap S L b) < 1:=by
   rw [←map_div₀,hfrac,hπ, ←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 have halt:v (algebraMap S L a) < 1:=
   ((div_lt_one₀ (zero_lt_iff.mpr hvb0)).mp hfraclt).trans_le (hS b)
 intro hbot
 have ha:=(mem_centerIdeal S L v hS a).mpr halt
 exact ha0 (by simpa only [hbot,Ideal.mem_bot] using ha)
def centerPlace (hv:Function.Surjective v):HeightOneSpectrum S:=
 ⟨centerIdeal S L v hS,inferInstance,centerIdeal_ne_bot S L v hS hv⟩
theorem centerPlace_membership (hv:Function.Surjective v) (s:S):
   s∈(centerPlace S L v hS hv).asIdeal ↔
     v (algebraMap S L s) < 1:=
 mem_centerIdeal S L v hS s
open scoped algebraMap in
theorem center_localization_le (hv:Function.Surjective v):
   HeightOneSpectrum.valuationSubringAtPrime L (centerPlace S L v hS hv) ≤
     v.valuationSubring:=by
 rintro x ⟨a,s,hs,rfl⟩
 have hsnot:s∉(centerPlace S L v hS hv).asIdeal:=hs
 have hsvalue:v (algebraMap S L s)=1:=by
   apply le_antisymm (hS s)
   exact le_of_not_gt fun hlt↦hsnot ((centerPlace_membership S L v hS hv s).mpr hlt)
 suffices v ((algebraMap S L a)/(algebraMap S L s)) ≤ 1 by
   rwa [division_def] at this
 rw [map_div₀,hsvalue,div_one]
 exact hS a
theorem centerPlace_valuation (hv:Function.Surjective v):
   v=(centerPlace S L v hS hv).valuation L:=by
 let p:=centerPlace S L v hS hv
 have hnontrivial:v.IsNontrivial:=by
   obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
   refine ⟨π,?_⟩
   simp [hπ]
 have htop:v.valuationSubring≠⊤:=by
   simpa only [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not] using hnontrivial
 have hring:HeightOneSpectrum.valuationSubringAtPrime L p=v.valuationSubring:=
   ValuationSubring.eq_of_le_of_ne_top _
     (center_localization_le S L v hS hv) htop
 rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hring
 have hequiv:(p.valuation L).IsEquiv v:=
   (Valuation.isEquiv_iff_valuationSubring _ _).mpr hring
 exact (eq_of_equiv_surjective (p.valuation L) v
   (p.valuation_surjective L) hv hequiv).symm
include hS in
theorem exists_unique_place (hv:Function.Surjective v):
   ∃! p:HeightOneSpectrum S,v=p.valuation L:=by
 refine ⟨centerPlace S L v hS hv,centerPlace_valuation S L v hS hv,?_⟩
 intro q hq
 apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K:=L)
 exact Valuation.IsEquiv.of_eq
   (hq.symm.trans (centerPlace_valuation S L v hS hv))
end Center
end
end ProximityPrize.SubmissionLower.RCN359
