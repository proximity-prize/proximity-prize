import ProximityPrize.SubmissionLower.R6966ProofPadePacket
import ProximityPrize.SubmissionLower.R6966ProofPadeRank
import ProximityPrize.SubmissionLower.R6966ProofTerminalBanks
import ProximityPrize.SubmissionLower.R6966ProofBoundaryRank

set_option Elab.async false

-- merged module R6966ProofPadeBankRank
section Merged_R6966ProofPadeBankRank

namespace Research6966.PadeBankRank
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset Module
open K1_14 (FX Seeds Jet Shape)
open K1_14_3 (SeedClosure SeedField fibreRow Surface Parent)
open K1_14_1 (CRTLift PoleData)
open PadeRank (Plane)
noncomputable section

private abbrev E := SeedClosure

private def seed : Seeds →ₐ[FX] E :=
  IsScalarTower.toAlgHom FX Seeds E

private theorem seed_eq : seed.toRingHom=K1_14_3.seedGeneric := by
  apply RingHom.ext
  exact IsScalarTower.algebraMap_apply Seeds SeedField E

def fibre : Jet →ₗ[FX] Plane E where
  toFun := fibreRow
  map_add' := by intro x y;simp [fibreRow]
  map_smul' := by
    intro r p
    ext j i
    simp only [fibreRow,coeff_map,coe_mapRingHom,AddMonoidAlgebra.coeff_smul_apply,RingHom.id_apply,←seed_eq]
    exact seed.toLinearMap.map_smul r _

private theorem fibre_inj : Function.Injective fibre :=
  map_injective _ (map_injective _ ((algebraMap SeedField E).injective.comp
    (IsFractionRing.injective Seeds SeedField)))

private def axes (U : Fin 2 → ℕ) (i:KoalaRect.AxisIndex U) : E :=
  seed (MvPolynomial.monomial (KoalaRect.axisExponent i) (1:FX))

def slots (U:Fin 2→ℕ) : Submodule FX E := Submodule.span FX (Set.range (axes U))

instance (U:Fin 2→ℕ) : FiniteDimensional FX (slots U) :=
  Module.Finite.span_of_finite _ (Set.finite_range _)

theorem slot_count (U:Fin 2→ℕ) : finrank FX (slots U)≤KoalaRect.area U := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_card,←KoalaRect.axis_card]
  exact Fintype.card_range_le _

theorem seed_in_slots {U:Fin 2→ℕ} {p:Seeds} (cap:∀ z,p.degreeOf z≤U z) : seed p∈slots U := by
  classical
  have expand := congrArg seed (MvPolynomial.as_sum p)
  rw [map_sum] at expand
  rw [expand]
  apply Submodule.sum_mem
  intro e he
  obtain ⟨i,eq⟩:=KoalaRect.exists_axisIndex (U:=U) e
    (fun z=>(MvPolynomial.le_degreeOf_of_mem_support z he).trans (cap z))
  have member : axes U i∈slots U:=Submodule.subset_span ⟨i,rfl⟩
  have mul := (slots U).smul_mem (p.coeff e) member
  change (p.coeff e) • seed.toLinearMap (MvPolynomial.monomial _ 1) ∈ _ at mul
  rwa [←LinearMap.map_smul,MvPolynomial.smul_monomial,smul_eq_mul,mul_one,eq] at mul

/-- Generic scalar span of the genuine rectangular evaluated bank. -/
def rows {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : Submodule E (Plane E) :=
  Submodule.span E (fibre '' (KoalaRect.rectEvaluated Crt word s W U : Set Jet))

theorem rows_shape {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : rows Crt word s W U ≤ PadeRank.box E (s.B+1) (s.J+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P,mem,rfl⟩ j i outside
  change ((fibreRow P).coeff j).coeff i = 0
  simp only [fibreRow,coeff_map,coe_mapRingHom]
  suffices orig: (P.coeff j).coeff i=0 by rw [orig,map_zero]
  by_contra ne
  obtain ⟨degree,slope,_⟩:=K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U mem) j i ne
  exact outside (by simp [PadeRank.positions];omega)

instance {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : FiniteDimensional E (rows Crt word s W U) := by
  exact Submodule.finiteDimensional_of_le (rows_shape Crt word s W U)

/-- The native axis rectangle is charged only once per independent generic jet. -/
theorem bank_dimension {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : finrank FX (KoalaRect.rectEvaluated Crt word s W U) ≤
      finrank E (rows Crt word s W U) * KoalaRect.area U := by
  classical
  let V:=KoalaRect.rectEvaluated Crt word s W U
  let H:=rows Crt word s W U
  by_cases finite:FiniteDimensional FX ↥V
  · let f:↥V→ₗ[FX]H := (fibre.comp V.subtype).codRestrict (H.restrictScalars FX)
      (fun x=>Submodule.subset_span ⟨x.val,x.property,rfl⟩)
    let L:Plane E →ₗ[E] (ℕ×ℕ→E) := LinearMap.pi (fun t=>
      (Polynomial.lcoeff E t.2).comp ((Polynomial.lcoeff E[X] t.1).restrictScalars E))
    have inject:Function.Injective L := by
      intro x y eq
      ext j i
      exact congrFun eq (j,i)
    apply le_trans (BoundaryRank.slots_times_rank (slots U) _ H V rfl (L.comp H.subtype) f
      (inject.comp Subtype.val_injective) (fun _ _ eq=>Subtype.ext (fibre_inj (congrArg Subtype.val eq))) ?_)
    · exact Nat.mul_le_mul_left _ (slot_count U)
    · intro x t
      change ((fibreRow x.val).coeff t.1).coeff t.2 ∈ slots U
      simp only [fibreRow,coeff_map,coe_mapRingHom]
      rw [←seed_eq]
      exact seed_in_slots (KoalaRect.rectEvaluated_axis Crt word x.property t.1 t.2)
  · rw [show finrank FX (KoalaRect.rectEvaluated Crt word s W U)=0 from Module.finrank_of_not_finite finite]
    exact Nat.zero_le _

/-- Every vector of the generic span carries the certified order of the
actual bank at each genuine retained parent sheet. -/
theorem rows_contact {h A} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    {s envelope:Shape} {W r:ℕ} (U:Fin 2→ℕ) (fits:TerminalBanks.inside s envelope)
    (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {y v:E} (sheet:∃ q∈parents,K1_14_3.OnSeedFibre q y v) :
    ∀ Q∈rows Crt word s W U,Q∈(TerminalProjection.fibrePoint y v)^(r+1) := by
  obtain ⟨parent,mem,fiber⟩:=sheet
  let I:Ideal (Plane E):=(TerminalProjection.fibrePoint y v)^(r+1)
  apply (show rows Crt word s W U ≤ I.restrictScalars E from ?_)
  apply Submodule.span_le.mpr
  rintro _ ⟨P,inBank,rfl⟩
  exact TerminalBanks.retained_order Crt word (geo _ mem) (pass _ mem) fits small cut
    (KoalaRect.rectEvaluated_le Crt word s W U inBank) y v fiber

#print axioms bank_dimension
#print axioms rows_contact
end
end Research6966.PadeBankRank

end Merged_R6966ProofPadeBankRank

-- merged module R6966ProofPadeChart
section Merged_R6966ProofPadeChart

namespace Research6966.PadeChart
set_option maxHeartbeats 1000000
open Polynomial Finset Module
open PadeRank (Plane box)
open Pade (totalJet)
open K1_14_1_4 (substitute substitute_C substitute_X doubleMap)
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def chart (a b u d:K) : Plane K →ₐ[K] Plane K where
  toRingHom := substitute (RingHom.id K) (C (C a*Polynomial.X+C b)) (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d))
  commutes' r := by change substitute _ _ _ (C (C r))=C (C r);simp [substitute,K1_14_1.jetConstant]

private theorem linear_total (a b:K) : totalJet (C (C a*Polynomial.X+C b):Plane K)≤1 := by
  apply (Pade.totalJet_le _ 1).mpr
  intro j i nonzero
  by_cases j0:j=0
  · subst j
    have n : (C a*Polynomial.X+C b:K[X]).coeff i≠0 := by simpa using nonzero
    have cap:=le_natDegree_of_ne_zero n
    have lim := (natDegree_add_le (C a*Polynomial.X) (C b)).trans
      (max_le_max (natDegree_mul_le ..) le_rfl)
    simp only [natDegree_C,natDegree_X] at lim
    omega
  · exact False.elim (nonzero (by simp [coeff_C,j0]))

private theorem slope_total (a u d:K) : totalJet (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d):Plane K)≤1 := by
  unfold totalJet
  rw [map_add]
  apply (MvPolynomial.totalDegree_add ..).trans (max_le _ (linear_total u d))
  apply (Pade.totalJet_le _ 1).mpr
  intro j i nz
  by_cases j1:j=1
  · subst j
    by_cases i0:i=0
    · omega
    · exact False.elim (nz (by simp [coeff_C_mul,coeff_C,i0]))
  · exact False.elim (nz (by simp [coeff_C_mul,coeff_X,Ne.symm j1,j1]))

theorem chart_box (a b u d:K) (B J:ℕ) {P:Plane K} (hp:P∈box K B J) :
    chart a b u d P∈box K B J := by
  classical
  let y : Plane K:=C (C a*Polynomial.X+C b)
  let v : Plane K:=C (C a)*Polynomial.X+C (C u*Polynomial.X+C d)
  change substitute (RingHom.id K) y v P ∈ _
  rw [P.as_sum_support_C_mul_X_pow,map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_mul,map_pow,(P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C,substitute_X,map_sum,map_mul,map_pow,Finset.sum_mul]
  simp only [coe_eval₂RingHom,eval₂_C,eval₂_X,RingHom.comp_apply,RingHom.id_apply]
  apply Submodule.sum_mem
  intro i hi
  let c := (P.coeff j).coeff i
  let m : Plane K := C (C c)*y^i*v^j
  change m∈_
  by_cases z:m=0
  · rw [z];exact Submodule.zero_mem _
  have active : (j,i)∈PadeRank.positions B J := by
    by_contra no
    exact (mem_support_iff.mp hi) (hp j i no)
  have caps:j<J ∧ j+i<B := by simp [PadeRank.positions] at active;omega
  apply (PadeRank.mem_box z).mpr
  constructor
  · have k0 : totalJet (C (C c):Plane K) ≤ 0 := by
      apply (Pade.totalJet_le _ _).mpr
      intro l t nz
      by_cases h:l=0
      · subst l
        by_cases g:t=0
        · omega
        · exact False.elim (nz (by simp [coeff_C,g]))
      · exact False.elim (nz (by simp [coeff_C,h]))
    have mul (p q:Plane K) : totalJet (p*q)≤totalJet p+totalJet q := by
      unfold totalJet;rw [map_mul];exact MvPolynomial.totalDegree_mul _ _
    have power (p:Plane K) (k:ℕ) : totalJet (p^k)≤totalJet p*k := by
      unfold totalJet;rw [map_pow];simpa only [Nat.mul_comm] using MvPolynomial.totalDegree_pow (Pade.jetVars p) k
    have hy:totalJet y≤1 := linear_total a b
    have hv:totalJet v≤1 := slope_total a u d
    have left:totalJet (y^i) ≤ i := (power y i).trans (by simpa only [one_mul] using Nat.mul_le_mul_right i hy)
    have right:totalJet (v^j) ≤ j := (power v j).trans (by simpa only [one_mul] using Nat.mul_le_mul_right j hv)
    have e:=mul (C (C c)*y^i) (v^j)
    have f:=mul (C (C c)) (y^i)
    change totalJet (C (C c)*y^i*v^j)<B
    omega
  · have vel:v.natDegree≤1 :=
      (natDegree_add_le (C (C a)*Polynomial.X:Plane K) (C (C u*Polynomial.X+C d))).trans
        (max_le ((show (C (C a)*Polynomial.X:Plane K).natDegree≤
          (C (C a):Plane K).natDegree+(Polynomial.X:Plane K).natDegree from natDegree_mul_le).trans (by simp))
          (by rw [natDegree_C];decide))
    have dy:y.natDegree=0:=natDegree_C _
    have cap: m.natDegree≤(C (C c)*y^i:Plane K).natDegree+(v^j).natDegree:=natDegree_mul_le ..
    have first: (C (C c)*y^i:Plane K).natDegree≤0 := (natDegree_mul_le ..).trans (by simp [dy,natDegree_pow])
    have second:(v^j).natDegree ≤ j := by rw [natDegree_pow];simpa using Nat.mul_le_mul_left j vel
    omega

#print axioms chart_box

set_option backward.isDefEq.respectTransparency false in
theorem chart_equiv (a b u d:K) (ne:a≠0) : Function.Bijective (chart a b u d) := by
  let T:=chart a b u d
  have inj:Function.Injective T := by
    apply (injective_iff_map_eq_zero T.toRingHom).mpr
    intro p zero
    by_contra pn
    exact (K1_14_1_4.affine_leading (RingHom.id K) Function.injective_id ne (b:=b)
      (C u*Polynomial.X+C d) pn).2.2 zero
  refine ⟨inj,fun P=>?_⟩
  by_cases zero:P=0
  · exact ⟨0,(map_zero _).trans zero.symm⟩
  let M:=box K (totalJet P+1) (P.natDegree+1)
  have inM:P∈M:=(PadeRank.mem_box zero).mpr ⟨Nat.lt_succ_self _,Nat.lt_succ_self _⟩
  let F:↥M→ₗ[K]M:=T.toLinearMap.restrict (fun Q hQ=>chart_box a b u d _ _ hQ)
  have : FiniteDimensional K ↥M := by dsimp only [M];infer_instance
  have injF:Function.Injective F:=fun x y eq=>Subtype.ext (inj (congrArg Subtype.val eq))
  have onto:Function.Surjective F:=LinearMap.surjective_of_injective (K:=K) (V:=↥M) (f:=F) injF
  obtain ⟨R,eq⟩:=onto ⟨P,inM⟩
  exact ⟨R.val,congrArg Subtype.val eq⟩

theorem chart_graph_primitive (a b u d:K) (ne:a≠0) {G:Pade.Row K} (gp:G.primitive) :
    (chart a b u d G.polynomial).IsPrimitive := by
  let e:=AlgEquiv.ofBijective (chart a b u d) (chart_equiv a b u d ne)
  let F:=FractionRing K[X]
  let f:=algebraMap K[X] F
  have inj:=IsFractionRing.injective K[X] F
  have ir:Irreducible G.polynomial := by
    apply (G.polynomial_primitive gp).irreducible_iff_irreducible_map_fraction_map (K:=F) |>.mpr
    apply Polynomial.irreducible_of_degree_eq_one
    have nz:G.polynomial.map f≠0:=(map_ne_zero_iff (mapRingHom f) (map_injective f inj)).mpr (G.polynomial_ne gp)
    change (G.polynomial.map f).degree=1
    rw [degree_eq_natDegree nz,
      natDegree_map_eq_of_injective inj,G.slope_degree gp]
    rfl
  have ir':Irreducible (e G.polynomial):=(MulEquiv.irreducible_iff e).mpr ir
  apply ir'.isPrimitive
  have cap:=K1_14_1_4.affine_leading (RingHom.id K) Function.injective_id ne (b:=b)
    (C u*Polynomial.X+C d) (G.polynomial_ne gp)
  change (chart a b u d G.polynomial).natDegree≠0
  exact (cap.1.trans (G.slope_degree gp)) ▸ one_ne_zero

#print axioms chart_graph_primitive

def window (K:Type*) [Field K] (S:Finset (ℕ×ℕ)) : Submodule K (Plane K) where
  carrier := {Q | ∀ j i,(j,i)∉S → (Q.coeff j).coeff i=0}
  zero_mem' := by simp
  add_mem' := by intro P Q hp hq j i outside;simp [hp j i outside,hq j i outside]
  smul_mem' := by intro r Q mem j i outside;simp [mem j i outside]

private def read (S:Finset (ℕ×ℕ)) : window K S→ₗ[K](S→K) where
  toFun Q t:=(Q.val.coeff t.val.1).coeff t.val.2
  map_add' := by intro P Q;funext t;simp
  map_smul' := by intro r P;funext t;simp

private theorem read_injective (S:Finset (ℕ×ℕ)) : Function.Injective (read (K:=K) S) := by
  intro P Q eq
  apply Subtype.ext
  ext j i
  by_cases yes:(j,i)∈S
  · exact congrFun eq ⟨(j,i),yes⟩
  · rw [P.property j i yes,Q.property j i yes]

/-- Only the unweighted inner rectangle is needed to measure the gain.
The whole physical window can have a ragged top edge. -/
theorem filtered_gain {G:Pade.Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (hits:∀ y∈ys,G.err v y=0) (k b j:ℕ) (S:Finset (ℕ×ℕ))
    (V:Submodule K (Plane K)) [FiniteDimensional K V]
    (T:Plane K→ₗ[K]Plane K) (inj:Function.Injective T)
    (bank:V≤(window K S).comap T) (inner:box K b j≤(window K S).comap T)
    (contact:∀ Q∈V,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K V + PadeRank.gain G.graphDegree ys.card k b j ≤ S.card := by
  classical
  let full:=V ⊔ box K b j
  have fits:full≤(window K S).comap T:=sup_le bank inner
  let F:full→ₗ[K]window K S:=(T.comp full.subtype).codRestrict _ (fun q=>fits q.property)
  have recov:Function.Injective ((read S).comp F) :=
    (read_injective S).comp (fun _ _ eq=>Subtype.ext (inj (congrArg Subtype.val eq)))
  have width := LinearMap.finrank_le_finrank_of_injective recov
  rw [Module.finrank_pi,Fintype.card_coe] at width
  have gain:=PadeRank.gain_bound gp ys v hits k b j (V ⊓ box K b j) inf_le_right
    (fun Q h=>contact Q h.1)
  have dim:=Submodule.finrank_sup_add_finrank_inf_eq V (box K b j)
  rw [PadeRank.box_dimension] at dim
  change finrank K ↥(V ⊔ box K b j)≤S.card at width
  omega

#print axioms filtered_gain
end
end Research6966.PadeChart

end Merged_R6966ProofPadeChart
