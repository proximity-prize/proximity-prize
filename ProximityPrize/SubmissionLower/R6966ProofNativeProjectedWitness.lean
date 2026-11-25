import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6966ProofPadeRawField

set_option Elab.async false

namespace Research6966.NativeProjectedWitness
open Polynomial Finset
open K1_14 (Jet Equation Seeds)
open K1_14_3 (SeedField SeedClosure Surface Parent OrderAt ProjectedProduct OnSeedFibre fibreRow)
open K1_14_1_4 (doubleMap)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open TerminalProjection (cleared)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

private abbrev E:=SeedClosure
private abbrev φ:=K1_14_3.seedGeneric
private theorem inj:Function.Injective φ:=(algebraMap SeedField E).injective.comp (IsFractionRing.injective Seeds SeedField)

theorem graph_eq {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    C (den N)*Polynomial.X-C (rhs N)=N.poly := by
  simpa only [den,rhs,map_neg,sub_neg_eq_add] using
    (Polynomial.eq_X_add_C_of_natDegree_le_one (NativeGraphMarks.slope_degree N gp).le).symm

private theorem map_clear (A B:Equation) (Q:Jet) (J:ℕ) (cap:Q.natDegree≤J) :
    (cleared A B Q J).map φ=cleared (A.map φ) (B.map φ) (fibreRow Q) J := by
  have top:(fibreRow Q).natDegree≤J:=by
    change (Q.map (mapRingHom φ)).natDegree≤J;exact natDegree_map_le.trans cap
  rw [cleared,cleared,Q.sum_over_range' (fun _=>by simp) (J+1) (by omega),
    (fibreRow Q).sum_over_range' (fun _=>by simp) (J+1) (by omega),Polynomial.map_sum]
  apply sum_congr rfl
  intro j _
  simp only [Polynomial.map_mul,Polynomial.map_pow,fibreRow,coeff_map,coe_mapRingHom]

/-- Fix the actual projected product once. Every avoiding row, including
one from a differently shaped bank, bounds this same native equation. -/
theorem projected_factor {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (parents:Finset Surface) (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (onGraph:∀ q∈parents,N.poly∈q.asIdeal) :
    ∃ H:Equation,ProjectedProduct parents H ∧ ∀ (Q:Jet) (J k:ℕ),Q.natDegree≤J →
      (∀ q∈parents,OrderAt q Q k) → H^k ∣ cleared (den N) (rhs N) Q J := by
  obtain ⟨H,T,v,proj,card,sheets⟩:=Pade.Native.projected_sheets parents nonempty geo
  let emb:Pade.Native.Sep→+*E:=(separableClosure SeedField E).val.toRingHom
  let ys:=T.image emb
  let vel (y:E):=if eq:∃ x∈T,emb x=y then emb (v eq.choose) else 0
  have velocity x (mem:x∈T):vel (emb x)=emb (v x) := by
    have yes:∃ z∈T,emb z=emb x:=⟨x,mem,rfl⟩
    simp only [vel,dite_eq_left yes,emb.injective yes.choose_spec.2]
  have root (y:E) (hy:y∈ys):∃ q∈parents,OnSeedFibre q y (vel y) := by
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
    rw [velocity x hx]
    exact (Pade.Native.sheets_iff ..).mp (sheets x hx)
  let D:E[X]:=∏y∈ys,(Polynomial.X-C y)
  have cardD:D.natDegree=H.natDegree := by
    dsimp only [D]
    rw [natDegree_prod ys (fun y=>Polynomial.X-C y) (fun y _=>X_sub_C_ne_zero y)]
    simpa only [natDegree_X_sub_C,sum_const,smul_eq_mul,mul_one,ys,card_image_of_injective _ emb.injective] using card
  have hn:H.map φ≠0:=(map_ne_zero_iff (mapRingHom φ) (map_injective φ inj)).mpr proj.primitive.ne_zero
  have divides:D∣H.map φ := by
    apply prod_dvd_of_coprime
    · intro x hx y hy ne;exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
    · intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=proj.vanishes q mem
      rw [←onq,RingHom.mem_ker] at zero
      apply dvd_iff_isRoot.mpr
      change (H.map φ).eval y=0
      rw [eval_map]
      simpa only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_C] using zero
  obtain ⟨a,eq⟩:=divides
  have da:D≠0:=left_ne_zero_of_mul (eq ▸ hn)
  have an:a≠0:=right_ne_zero_of_mul (eq ▸ hn)
  have total: (H.map φ).natDegree = D.natDegree+a.natDegree := by rw [eq,natDegree_mul da an]
  rw [natDegree_map_eq_of_injective inj,cardD] at total
  have const:a=C (a.coeff 0):=eq_C_of_natDegree_eq_zero (by omega)
  have cn:a.coeff 0≠0:=by intro z;apply an;rw [const,z,map_zero]
  have unit:IsUnit a:=const ▸ isUnit_C.mpr cn.isUnit
  have assoc:Associated (H.map φ) D:=eq ▸ associated_mul_unit_left _ _ unit
  refine ⟨H,proj,?_⟩
  intro Q J k cap order
  have projQ:=TerminalProjection.all_sheets ((den N).map φ) ((rhs N).map φ) (fibreRow Q) ys vel J k
    (natDegree_map_le.trans cap) (by
      intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=onGraph q mem
      rw [←onq,RingHom.mem_ker] at zero
      rw [←graph_eq N gp] at zero
      have hit:((den N).map φ).eval y*vel y=((rhs N).map φ).eval y := by
        simp only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X] at zero
        simpa only [eval_map] using sub_eq_zero.mp zero
      have nz:((den N).map φ).eval y≠0:=by
        intro z
        obtain ⟨l,w,id⟩:=NativeGraphExceptional.coprime_generic N gp
        have bad:=congrArg (eval y) id
        simp [←hit,z] at bad
      exact ⟨nz,hit,order q mem y (vel y) onq⟩)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Seeds)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
  have prim (i:ℕ) : (H^i).IsPrimitive := by
    induction i with
    | zero=>simp
    | succ i ih=>rw [pow_succ];exact ih.mul proj.primitive
  apply PadeRawField.primitive_divides φ inj (prim k)
  rw [Polynomial.map_pow,map_clear _ _ _ _ cap]
  exact (pow_dvd_pow_of_dvd assoc.dvd k).trans projQ

theorem axis_clear {G:Pade.Row SeedField} (N:Native G) (Q:Jet) (z:Fin 2) (J U u:ℕ)
    (cap:Q.natDegree≤J) (Qaxis:∀ j i,((Q.coeff j).coeff i).degreeOf z≤U)
    (Naxis:∀ j i,((N.poly.coeff j).coeff i).degreeOf z≤u) :
    KoalaRect.axisDegree (cleared (den N) (rhs N) Q J) z ≤ U+J*u := by
  let view:=K1_14_4.seedView
  have a:KoalaRect.axisDegree (den N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (Naxis 1)
  have b:KoalaRect.axisDegree (rhs N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (fun i=>by simpa [rhs] using Naxis 0 i)
  change (view (cleared (den N) (rhs N) Q J)).degreeOf z≤_
  rw [cleared,Polynomial.sum_def,map_sum]
  apply (MvPolynomial.degreeOf_sum_le ..).trans (Finset.sup_le _)
  intro j hj
  have jJ: j≤J:=(le_natDegree_of_mem_supp j hj).trans cap
  have q:KoalaRect.axisDegree (Q.coeff j) z≤U:=(KoalaRect.axisDegree_le_iff ..).mpr (Qaxis j)
  rw [map_mul,map_mul,map_pow,map_pow]
  calc
    _ ≤ (U+j*u)+(J-j)*u := (MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add
      ((MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add q
        ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left j b))))
      ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left (J-j) a)))
    _ = _ := by rw [Nat.add_assoc,←Nat.add_mul,Nat.add_sub_of_le jJ]

theorem avoiding_widths {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    {H:Equation} (hn:H≠0) (Q:Jet) (k J B:ℕ) (U u:Fin 2→ℕ)
    (notDiv:¬N.poly∣Q) (cap:Q.natDegree≤J) (joint:∀ j∈Q.support,(Q.coeff j).natDegree+j≤B)
    (Qa:∀ j i z,((Q.coeff j).coeff i).degreeOf z≤U z)
    (Na:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤u z)
    (divides:H^k∣cleared (den N) (rhs N) Q J) :
    k*H.natDegree≤B+(G.graphDegree-1)*J ∧ ∀ z,k*KoalaRect.axisDegree H z≤U z+J*u z := by
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  have eq:=graph_eq N gp
  have nz:=TerminalProjection.integral_nonzero_of_avoids (den N) (rhs N) Q J cap
    (NativeGraphExceptional.den_ne N gp) (eq ▸ N.primitive) (eq ▸ notDiv)
  have deg:=NativeGraphMarks.equation_degrees N gp
  have y:=TerminalProjection.ordinate_width (den N) (rhs N) Q J G.graphDegree B cap
    (by unfold Pade.Row.graphDegree;omega) deg.1 deg.2 joint
  have lower:=natDegree_le_of_dvd divides nz
  rw [natDegree_pow] at lower
  refine ⟨lower.trans y,?_⟩
  intro z
  obtain ⟨D,eq⟩:=divides
  have dn:=right_ne_zero_of_mul (eq ▸ nz)
  have axis:=axis_clear N Q z J (U z) (u z) cap (fun j i=>Qa j i z) (fun j i=>Na j i z)
  rw [eq,KoalaRect.axisDegree_mul (pow_ne_zero _ hn) dn,KoalaRect.axisDegree_pow hn] at axis
  omega

#print axioms projected_factor
#print axioms avoiding_widths
end
end Research6966.NativeProjectedWitness
