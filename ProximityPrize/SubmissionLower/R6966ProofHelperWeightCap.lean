import ProximityPrize.SubmissionLower.R6966ProofHelperWindowPrefix
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphMarks

set_option Elab.async false

namespace Research6966.HelperWeightCap
open Polynomial Finset Module
open K1_14 (Jet Seeds FX)
open K1_14_1 (PoleData CRTLift jetConstant)
open K1_14_1_4 (doubleMap specialized evalRaw)
open K1_14_2_2_2_1 (jetDegree jetDegree_le)
open Pade (totalJet)
open PadeRank (Plane box)
open scoped Polynomial
noncomputable section
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

private theorem total_constant {K:Type*} [Field K] (c:K) : totalJet (jetConstant c)=0 := by
  apply Nat.eq_zero_of_le_zero
  apply (Pade.totalJet_le _ _).mpr
  intro j i ne
  by_cases hj:j=0
  · subst j;by_cases hi:i=0
    · omega
    · exact False.elim (ne (by simp [jetConstant,coeff_C,hi]))
  · exact False.elim (ne (by simp [jetConstant,coeff_C,hj]))

theorem native_total {F:Type*} [Field F] (f:Seeds→+*F) (inj:Function.Injective f) (N:Jet) :
    totalJet (doubleMap f N)=jetDegree N := by
  have eq (b:ℕ) : totalJet (doubleMap f N)≤b ↔ jetDegree N≤b := by
    rw [Pade.totalJet_le,jetDegree_le]
    simp only [doubleMap,coe_mapRingHom,coeff_map,map_ne_zero_iff _ inj]
  exact le_antisymm ((eq _).mpr le_rfl) ((eq _).mp le_rfl)

private theorem chart_total {K:Type*} [Field K] (a b u d:K) (an:a≠0) {Q:Plane K} (qn:Q≠0) :
    totalJet (PadeChart.chart a b u d Q)=totalJet Q := by
  let T:=PadeChart.chart a b u d
  have inj:Function.Injective T:=(PadeChart.chart_equiv a b u d an).1
  have after:T Q≠0:=(map_ne_zero_iff _ inj).mpr qn
  let j:=Q.natDegree+(T Q).natDegree+1
  have source:Q.natDegree<j:=by dsimp only [j];omega
  have target:(T Q).natDegree<j:=by dsimp only [j];omega
  have rel (c:ℕ):totalJet Q<c ↔ totalJet (T Q)<c := by
    let V:=box K c j
    let r:↥V→ₗ[K]V:=T.toLinearMap.restrict (fun _ q=>PadeChart.chart_box a b u d _ _ q)
    have ri:Function.Injective r:=fun _ _ eq=>Subtype.ext (inj (congrArg Subtype.val eq))
    have onto:Function.Surjective r:=LinearMap.surjective_of_injective (K:=K) (V:=↥V) (f:=r) ri
    constructor
    · intro low
      exact ((PadeRank.mem_box after).mp (PadeChart.chart_box a b u d _ _ ((PadeRank.mem_box qn).mpr ⟨low,source⟩))).1
    · intro low
      obtain ⟨R,eq⟩:=onto ⟨T Q,(PadeRank.mem_box after).mpr ⟨low,target⟩⟩
      have id:R.val=Q:=inj (congrArg Subtype.val eq)
      exact ((PadeRank.mem_box qn).mp (id ▸ R.property)).1
  exact le_antisymm (Nat.le_of_lt_succ ((rel _).mp (Nat.lt_succ_self _)))
    (Nat.le_of_lt_succ ((rel _).mpr (Nat.lt_succ_self _)))

/-- The physical model pays w times total jet degree, with at most the
slope degree lost on the top diagonal. This holds for any positive-slope
prime and for products. -/
theorem weight_lower {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (nn:N≠0) (w:ℕ) (wp:0<w) :
    w*jetDegree N≤RawPhysicalDegree.weight w (w-1) M.raw+N.natDegree := by
  let f:=algebraMap Seeds K1_14_3.SeedField
  let R:=doubleMap evalRaw M.raw
  obtain ⟨a,b,u,d,an,form⟩:=K1_14_1_4.specialized_affine_form Crt
  have chart:specialized Crt N=PadeChart.chart a b u d (doubleMap f N) := by
    have id:=RingHom.congr_fun form N;change specialized Crt N=_ at id
    rw [id]
    change _=(K1_14_1_4.substitute (RingHom.id _) _ _).comp (doubleMap f) N
    rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  have fi:=IsFractionRing.injective Seeds K1_14_3.SeedField
  have nz:doubleMap f N≠0:=(map_ne_zero_iff (doubleMap f) (map_injective _ (map_injective _ fi))).mpr nn
  have spec:=K1_14_1_4.specialized_leading Crt nn
  have cn: (jetConstant M.c:Plane K1_14_3.SeedField)≠0:=C_ne_zero.mpr (C_ne_zero.mpr M.unit_c)
  have total:totalJet R=jetDegree N := by
    dsimp only [R];rw [M.eq,Pade.totalJet_mul cn spec.2.2,total_constant,zero_add,chart,
      chart_total a b u d an nz,native_total f fi]
  have slope:R.natDegree=N.natDegree := by
    dsimp only [R];rw [M.eq,natDegree_mul cn spec.2.2,spec.1]
    simp [jetConstant]
  let Lw:=RawPhysicalDegree.weight w (w-1) M.raw
  have bounded:K1_14_1_4.Bounded w (w-1) Lw M.raw:=(RawPhysicalDegree.bounded_iff ..).mpr le_rfl
  by_contra! no
  have pos:0<jetDegree N:=by by_contra! z;rw [Nat.eq_zero_of_le_zero z,mul_zero] at no;omega
  have reduced:totalJet R≤jetDegree N-1 := (Pade.totalJet_le ..).mpr (by
    intro j i ne
    have raw:(M.raw.coeff j).coeff i≠0:=by
      intro z;apply ne;simp only [R,doubleMap,coe_mapRingHom,coeff_map,z,map_zero]
    have js:j≤N.natDegree:=slope ▸ le_natDegree_of_ne_zero (show R.coeff j≠0 from fun z=>ne (by rw [z,coeff_zero]))
    have phys:=bounded j i ((M.raw.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr raw)
    have charge:(w-1)*j+j=w*j:=by rw [←Nat.succ_mul];congr 1;omega
    have small:w*(i+j)<w*jetDegree N := by rw [Nat.mul_add];change Lw+N.natDegree<w*jetDegree N at no;omega
    have lt:=Nat.lt_of_mul_lt_mul_left small
    omega)
  omega


theorem native_degree {G:Pade.Row K1_14_3.SeedField} (N:PadeNativeQuotient.Native G) (gp:G.primitive) :
    jetDegree N.poly=G.graphDegree := by
  let f:=algebraMap K1_14_3.SeedField K1_14_3.SeedClosure
  have inj:=f.injective.comp (IsFractionRing.injective Seeds K1_14_3.SeedField)
  have eq:=native_total K1_14_3.seedGeneric inj N.poly
  change totalJet (K1_14_3.fibreRow N.poly)=jetDegree N.poly at eq
  rw [←eq,N.eq]
  change totalJet (jetConstant N.scalar*(G.map f).polynomial)=_
  rw [Pade.totalJet_mul (show (jetConstant N.scalar:Plane K1_14_3.SeedClosure)≠0 from
    C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne ((G.primitive_map f).mpr gp)),
    total_constant,zero_add,(G.map f).total_polynomial ((G.primitive_map f).mpr gp),Pade.Row.degree_map]

end
end Research6966.HelperWeightCap
