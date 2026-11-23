import ProximityPrize.SubmissionLower.Zgvu91a
set_option Elab.async false
open _root_ renaming MvPolynomial.eval → zY9, PowerSeries → zpm, PowerSeries.constantCoeff → zbO
set_option backward.isDefEq.respectTransparency false
namespace qZfVj1b
noncomputable section
open Polynomial Finset
open P5 (K p)
open P5_7_1 (degree)
open cu (L FX j9)
open gT (kM)
open DQ (specialize)
open Cu
open E7 (CurveField CurvePlace poleOrder)
open qK3TPae (RegularPoint)
open qb0hmCe (CurveModel coeffHeight cLN)
open q1kuFjb (mapTwice expansion_coeff power_residue)
open quN7Z4a (Sheet)
open qBajpRb (CurveRing incl yq equation equation_generic equation_mark)
open qRoCwuc (coord coeff_generic)

open P5_7_3_5_2 (atPolynomial)
open P5_7_7 (phys)
open scoped Classical WithZero
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
attribute [local instance] gRK
def c1 :Prop :=
 ∀ (Q:sQ) [Fact (Irreducible Q)],Q.totalDegree<p →
   ∃ _:CurvePlace L (oO Q),
     CurveField L (oO Q) ∧
     ∀ i,(∑ᶠ v :CurvePlace L (oO Q),poleOrder v.value (Wt Q i)) ≤
       Q.totalDegree
def c2 :Prop :=
 ∀ {Q:sQ} [Fact (Irreducible Q)] {J:Ideal kM}
   {e n H :ℕ} {R:wJ Q J e} (A:yI R n),
   CurveField L (oO Q)→a9K (EF A) H →
   coeffHeight (normalize R.equation)≤H
def c3:Prop :=
 ∀ {Q:sQ} [Fact (Irreducible Q)] {J:Ideal kM}
   {e n:ℕ} {R:wJ Q J e} (A:yI R n),
   Q.totalDegree<p→CurveField L (oO Q) →
   ∀ (x :K) (t:Fin n→L) (h:aCn x t∈MvPolynomial.zeroLocus FX (EF A)),
     Nonempty (ChartPlace A h)
def c4 :Prop :=
 ∀ {Q:sQ} [Fact (Irreducible Q)] (u:Fin 2→L),
   Q.totalDegree<p→Q.eval u=0→RegularPoint Q u →
   ∀ (v :CurvePlace L (oO Q)) (a :oO Q →ₐ[L] LaurentSeries L),
     (∀ c,v.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)) →
     ∀ b:Fin 2→zpm L,
       (∀ i,a (Wt Q i)=(b i:LaurentSeries L)) →
       (∀ i,zbO (b i)=u i) →
       ∃ i,PowerSeries.coeff 1 (b i)≠0
variable {Q:sQ} [Fact (Irreducible Q)]
private def curve (h:CurveField L (oO Q))
   (hh : ∀ i,(∑ᶠ v :CurvePlace L (oO Q),
     poleOrder v.value (Wt Q i))≤Q.totalDegree) :CurveModel Q where
 E :=oO Q
 seed :=Wt Q
 curve :=h
 equation := by
   ext q
   rw [RingHom.mem_ker]
   change MvPolynomial.aeval (Wt Q) q=0↔q∈auG Q
   rw [dc8,map_eq_zero_iff _
     (IsFractionRing.injective (abz Q) (oO Q)),
     Ideal.Quotient.eq_zero_iff_mem]
 generates := by
   have hm (a :abz Q) :
       algebraMap (abz Q) (oO Q) a ∈
         IntermediateField.adjoin L (Set.range (Wt Q)) := by
     obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective a
     apply IntermediateField.algebra_adjoin_le_adjoin L (Set.range (Wt Q))
     rw [Algebra.adjoin_range_eq_range_aeval]
     exact ⟨q,dc8 Q q⟩
   apply top_unique
   intro c _
   obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective (abz Q) c
   exact div_mem (hm a) (hm b)
 co6:=hh
variable {J:Ideal kM} {e H :ℕ} {T:Finset K}
 {z :K→K} {s :K→K[X]} (S:Sheet Q J e H T z s)
private theorem root_ne :S.root.equation≠0:= by
 intro h
 exact S.root.irreducible.ne_zero (by rw [h,Polynomial.map_zero])
private theorem b5S :S.root.equation.leadingCoeff.leadingCoeff≠0 :=
 leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (root_ne S))
private theorem head_coeff :
   (S.root.equation.coeff e).coeff (S.root.equation.coeff e).natDegree =
     S.root.equation.leadingCoeff.leadingCoeff := by
 rw [coeff_natDegree]
 exact congrArg (fun i=>(S.root.equation.coeff i).leadingCoeff) S.root.degree.symm
private theorem eLq :coord S (pivot S) =
   (S.bY.scale :oO Q)*S.root.equation.leadingCoeff.leadingCoeff := by
 have h:=congrArg (fun f : (oO Q)[X] =>
   f.coeff (S.root.equation.coeff e).natDegree) (coeff_generic S e)
 simpa only [coeff_map,coeff_C_mul,head_coeff S,pivot,qRoCwuc.coeff] using h
private theorem pivot_ne :coord S (pivot S)≠0:= by
 rw [eLq S]
 exact mul_ne_zero S.bY.scale.ne_zero (b5S S)
private theorem normal_degree : (normalize S.root.equation).natDegree=e :=
 (natDegree_C_mul (C_ne_zero.mpr (inv_ne_zero (b5S S)))).trans S.root.degree
private theorem normal_monic :
   (normalize S.root.equation).leadingCoeff.leadingCoeff=1 := by
 rw [normalize,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_mul,
   leadingCoeff_C,inv_mul_cancel₀ (b5S S)]
private theorem normal_irreducible :Irreducible (normalize S.root.equation) := by
 have hi:=(S.root.primitive.irreducible_iff_irreducible_map_fraction_map
   (K:=y7 Q)).mpr S.root.irreducible
 exact (irreducible_isUnit_mul ((inv_ne_zero (b5S S)).isUnit.map (C.comp C))).mpr hi
private abbrev ringPivot:CurveRing S.bY :=
 ((equation S.bY).coeff e).coeff (S.root.equation.coeff e).natDegree
private theorem normal_generic :
   normalize S.root.equation =
     C (C (incl S.bY (ringPivot S))⁻¹)*mapTwice (incl S.bY) (equation S.bY) := by
 have h:=congrArg (fun f : (oO Q)[X][X] =>
   (f.coeff e).coeff (S.root.equation.coeff e).natDegree) (equation_generic S.bY)
 simp only [coeff_map,coe_mapRingHom,coeff_C_mul,head_coeff S] at h
 change normalize S.root.equation=C (C (incl S.bY (ringPivot S))⁻¹) *
   (equation S.bY).map (mapRingHom (incl S.bY))
 rw [equation_generic S.bY,show incl S.bY (ringPivot S)= _ from h,
   normalize,← mul_assoc,← map_mul,← map_mul]
 congr 2
 rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ S.bY.scale.ne_zero,mul_one]
private theorem mark_pivot {γ:K} (hγ:γ∈T) :
   yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ) (ringPivot S) =
     zY9 (S.parameter γ) (pivot S) := by
 have h:=congrArg (fun f :L[X][X] =>
   (f.coeff e).coeff (S.root.equation.coeff e).natDegree) (equation_mark S.bY (S.onBase γ hγ))
 change (yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)).toRingHom (ringPivot S)= _
 simpa only [specialize,coeff_map,coe_mapRingHom,pivot,ringPivot] using h
private theorem at_normal {γ:K} {hγ:γ∈T}
   (A:ChartPlace S.bY (S.onBase γ hγ))
   (hp:zY9 (S.parameter γ) (pivot S)≠0) :
   (∀ i j,A.place.value (((normalize S.root.equation).coeff i).coeff j)≤1) ∧
   atPolynomial (cLN A.map 0 (normalize S.root.equation)) (s γ)=0:= by
 let c:=A.series (ringPivot S)
 have hc:zbO c≠0:= by
   change zbO (A.series (ringPivot S))≠0
   rwa [A.reduce,mark_pivot S hγ]
 let u:=(PowerSeries.isUnit_iff_constantCoeff.mpr hc.isUnit).unit
 have hu: (u:zpm L)=c:=(PowerSeries.isUnit_iff_constantCoeff.mpr hc.isUnit).unit_spec
 let g:=C (C (↑u⁻¹:zpm L))*mapTwice A.series.toRingHom (equation S.bY)
 let ι:zpm L →+* LaurentSeries L:=HahnSeries.ofPowerSeries ℤ L
 have hg (i j:ℕ) :
     ι ((g.coeff i).coeff j)=A.map (((normalize S.root.equation).coeff i).coeff j) := by
   have hu' : ι (↑u⁻¹:zpm L)=(A.map (incl S.bY (ringPivot S)))⁻¹:= by
     rw [← A.lift_eq,← show ι c=(c:LaurentSeries L) from rfl,← hu]
     exact Units.val_inv_eq_inv_val (u.map ι.toMonoidHom)
   rw [normal_generic S]
   simp only [g,mapTwice,coe_mapRingHom,coeff_C_mul,coeff_map,map_mul,map_inv₀]
   rw [hu']
   congr 1
   exact A.lift_eq _
 constructor
 · intro i j
   rw [A.value,← hg]
   exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨_,rfl⟩
 · have he :cLN A.map 0 (normalize S.root.equation) =
       mapTwice zbO g:= by
     ext i j
     rw [expansion_coeff,← hg]
     simp only [mapTwice,coe_mapRingHom,coeff_map]
     exact power_residue _ _ rfl
   have hm:mapTwice zbO
       (mapTwice A.series.toRingHom (equation S.bY)) =
         specialize S.bY.equation (S.parameter γ) := by
     rw [← equation_mark S.bY (S.onBase γ hγ)]
     ext i j
     simp only [mapTwice,coe_mapRingHom,coeff_map]
     change zbO (A.series (((equation S.bY).coeff i).coeff j)) =
       yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ) (((equation S.bY).coeff i).coeff j)
     exact A.reduce _
   rw [he,show mapTwice zbO g =
     C (C (zbO (↑u⁻¹:zpm L))) *
       specialize S.bY.equation (S.parameter γ) by
     simp only [g,map_mul,mapTwice,coe_mapRingHom,map_C] at *
     rw [hm]]
   unfold atPolynomial
   have hv : (specialize S.bY.equation (S.parameter γ)).eval₂ phys (phys (j9 (s γ)))=0:= by
     calc
       _=phys ((specialize S.bY.equation (S.parameter γ)).eval (j9 (s γ))) := by
         rw [← eval₂_id,hom_eval₂,RingHom.comp_id]
       _=0:= by rw [S.identity γ hγ,map_zero]
   rw [eval₂_mul,hv,mul_zero]
end
end qZfVj1b
