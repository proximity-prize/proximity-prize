import ProximityPrize.SubmissionLower.Z6969Pack0424
import ProximityPrize.SubmissionLower.R6966ProofNativeMarkedTariff
import ProximityPrize.SubmissionLower.Z6969Pack0096
import ProximityPrize.SubmissionLower.PortHighFinish

set_option Elab.async false

-- Source: Research6969.NearMarked
section Z6969Source0436
set_option autoImplicit true
namespace Research6969.NearMarked
open Polynomial Finset
open K1 (K)
open K1_14 (FX Seeds Equation graphEval atX)
open K1_14_2 (SeedField)
open KoalaRect (axisDegree)
open Research6966.NativeMarkedTariff (width)
noncomputable section

/-- A retained root of degree at most 47 can use the same field-theoretic
price at every transition height, including roots reassigned across packets. -/
theorem count {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:T⊆Γ) (hi:M.overhead.toNat≤2534)
    {f:Equation} (positive:0<f.natDegree) (separable:(f.map (algebraMap Seeds SeedField)).Separable)
    (n v x y:ℕ) (large:3≤n) (legal:n<48) (deg:f.natDegree≤n)
    (total:∀ i,(f.coeff i).totalDegree≤v) (xc:axisDegree f 0≤x) (yc:axisDegree f 1≤y)
    (small:(2*f.natDegree-1)*axisDegree f 0<K1.p)
    (roots:∀γ∈T,(f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0) :
    T.card≤(Far6969FactorPrice.rate n+2*f.natDegree-1)*width v x y+(n-1)*f.natDegree := by
  classical
  have inject:Function.Injective M.label:=fun _ _ h=>sub_left_inj.mp h
  obtain ⟨S,P,inside,pn,pe,wide,marks,split⟩:=Research6966.NativeMarkedTariff.split M.label F.scalar
    inject.injOn positive separable (Research6966.NativeMarkedTariff.coeff_cap total xc yc) small roots
  have domain:S⊆Γ:=inside.trans sub
  have words:RetainedShortening.Word 179740 164806 M.word F.scalar S:=by
    refine ⟨F.distinct.mono domain,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (domain hγ)).scalar_degree with zero|bd
      · simp [zero]
      · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at bd
        omega
    · intro γ hγ
      let m:=F.mark γ (domain hγ)
      exact ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩
  have pay:=Far6969FactorPrice.price words (fun γ=>algebraMap K K1_14.L (M.label γ))
    ((algebraMap K K1_14.L).injective.comp inject) P pn n _ large legal (pe.le.trans deg) wide marks
  rw [pe] at pay
  apply split.trans
  calc _ ≤ (2*f.natDegree-1)*width v x y+
        (Far6969FactorPrice.rate n*width v x y+(n-1)*f.natDegree) := Nat.add_le_add_left pay _
    _ = _ := by
      rw [show Far6969FactorPrice.rate n+2*f.natDegree-1=
        Far6969FactorPrice.rate n+(2*f.natDegree-1) by omega,Nat.add_mul]
      omega

end
end Research6969.NearMarked
end Z6969Source0436

-- Source: Research6969.NearMarked64
section Z6969Source0437
set_option autoImplicit true
-- Adapted from the promoted lower-track proof at 2a99570fe043b6dabeac1e52f807826c8859d717.
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
namespace Research6969.NearMarked
open Polynomial Finset
open K1 (K)
open K1_14 (FX Seeds Equation graphEval atX)
open K1_14_2 (SeedField)
open KoalaRect (axisDegree)
open Research6966.NativeMarkedTariff (width)
noncomputable section

/-- A retained root of degree at most 63 can use the same field-theoretic
price at every transition height, including roots reassigned across packets. -/
theorem count64 {u deleted} {M:P1.ModelAt 33735 u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:T⊆Γ) (hi:M.overhead.toNat≤2534)
    {f:Equation} (positive:0<f.natDegree) (separable:(f.map (algebraMap Seeds SeedField)).Separable)
    (n v x y:ℕ) (large:3≤n) (legal:n<64) (deg:f.natDegree≤n)
    (total:∀ i,(f.coeff i).totalDegree≤v) (xc:axisDegree f 0≤x) (yc:axisDegree f 1≤y)
    (small:(2*f.natDegree-1)*axisDegree f 0<K1.p)
    (roots:∀γ∈T,(f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0) :
    T.card≤(Near6969FactorPrice.rate n+2*f.natDegree-1)*width v x y+(n-1)*f.natDegree := by
  classical
  have inject:Function.Injective M.label:=fun _ _ h=>sub_left_inj.mp h
  obtain ⟨S,P,inside,pn,pe,wide,marks,split⟩:=Research6966.NativeMarkedTariff.split M.label F.scalar
    inject.injOn positive separable (Research6966.NativeMarkedTariff.coeff_cap total xc yc) small roots
  have domain:S⊆Γ:=inside.trans sub
  have words:RetainedShortening.Word 179740 133605 M.word F.scalar S:=by
    refine ⟨F.distinct.mono domain,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (domain hγ)).scalar_degree with zero|bd
      · simp [zero]
      · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at bd
        omega
    · intro γ hγ
      let m:=F.mark γ (domain hγ)
      exact ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩
  have pay:=Near6969FactorPrice.price words (fun γ=>algebraMap K K1_14.L (M.label γ))
    ((algebraMap K K1_14.L).injective.comp inject) P pn n _ large legal (pe.le.trans deg) wide marks
  rw [pe] at pay
  apply split.trans
  calc _ ≤ (2*f.natDegree-1)*width v x y+
        (Near6969FactorPrice.rate n*width v x y+(n-1)*f.natDegree) := Nat.add_le_add_left pay _
    _ = _ := by
      rw [show Near6969FactorPrice.rate n+2*f.natDegree-1=
        Near6969FactorPrice.rate n+(2*f.natDegree-1) by omega,Nat.add_mul]
      omega

end
end Research6969.NearMarked
end Z6969Source0437

-- Source: Research6969.JointMarked
section Z6969Source0438
set_option autoImplicit true
namespace Research6969.JointMarked
noncomputable section
open K1 (K I p)
open K1_14 (Equation Jet Seeds FX graphEval atX jetAt)
open K1_14_3 (Surface ProjectedProduct SeedField)
open Finset Polynomial
open scoped Classical

def price (e v:ℕ):ℕ:=
  if e=0 then 0 else
    (Near6969FactorPrice.rate (max 3 e)+2*e-1)*(p*v)+(max 3 e-1)*e

theorem owned_count {u del} {M:P1.ModelAt 33735 u del} {Γ S:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:S⊆Γ) (hi:M.overhead.toNat≤2534) (f:Equation)
    (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable) (grade:f.natDegree<64)
    {v:ℕ} (cap:K1_14_4.seedDegree f≤v) (small:(2*f.natDegree-1)*v<p)
    (roots:∀γ∈S,(f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0) :
    S.card≤price f.natDegree v := by
  classical
  by_cases zero:f.natDegree=0
  · have unit:=JointOwnership.zero_grade_unit prim zero
    have empty:S=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have nu:IsUnit ((f.map (graphEval (M.label z))).eval (atX (F.scalar z))):=
        (unit.map (mapRingHom (graphEval (M.label z)))).map (evalRingHom (atX (F.scalar z)))
      exact nu.ne_zero (roots z hz)
    simp [empty]
  have all:∀i,(f.coeff i).totalDegree≤v := (K1_14_4.seedDegree_le_iff ..).mp cap
  have axis (j:Fin 2):KoalaRect.axisDegree f j≤v:=
    (KoalaRect.axisDegree_le_iff ..).mpr fun i=>(MvPolynomial.degreeOf_le_totalDegree _ _).trans (all i)
  have actual:=NearMarked.count64 F sub hi (Nat.pos_of_ne_zero zero) sep (max 3 f.natDegree) v v v
    (le_max_left ..) (max_lt (by decide) grade) (le_max_right ..) all (axis 0) (axis 1)
    ((Nat.mul_le_mul_left _ (axis 0)).trans_lt small) roots
  exact actual.trans (by
    rw [price,if_neg zero]
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul_left _ (min_le_left _ _))

/-- Count the union of the two actual projected families, assigning every
mark on their common part to the primary projection exactly once. -/
theorem both {u del} {M:P1.ModelAt 33735 u del} {Γ S:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:S⊆Γ) (hi:M.overhead.toNat≤2534)
    {A B:Finset Surface} {primary rescue whole:Equation} (main:ProjectedProduct A primary)
    (other:ProjectedProduct B rescue) (union:ProjectedProduct (A∪B) whole)
    {v w:ℕ} (cmain:K1_14_4.seedDegree primary≤v) (cother:K1_14_4.seedDegree rescue≤w)
    (grade:whole.natDegree<64)
    (smallV:(2*whole.natDegree-1)*v<p) (smallW:(2*whole.natDegree-1)*w<p)
    (owners:∀z∈S,∃Q∈A∪B,∀P∈Q.asIdeal,jetAt P (M.label z) (F.scalar z)=0) :
    ∃ i j:ℕ,i=primary.natDegree ∧ i+j=whole.natDegree ∧
      S.card≤price i v+price j w := by
  classical
  obtain ⟨e,eq,dvd,_,degrees,sep,_⟩:=JointOwnership.exclusive main other union
  obtain ⟨prim,seed,_⟩:=JointOwnership.rescue_caps other dvd
  let ev (z:K):Equation→+*FX:=eval₂RingHom (graphEval (M.label z)) (atX (F.scalar z))
  let P:=S.filter fun z=>ev z primary=0
  let E:=S\P
  have actual (z:K) (hz:z∈S):ev z whole=0:=by
    obtain ⟨Q,hQ,hit⟩:=owners z hz
    simpa [ev,jetAt] using hit (C whole) (union.vanishes Q hQ)
  have read (z:K) (f:Equation):ev z f=(f.map (graphEval (M.label z))).eval (atX (F.scalar z)):=by
    simp [ev,Polynomial.eval_map]
  have mainSub:P⊆S:=filter_subset _ _
  have exclSub:E⊆S:=sdiff_subset
  have lp:primary.natDegree≤whole.natDegree:=by omega
  have le':e.natDegree≤whole.natDegree:=by omega
  have priceP:=owned_count F (mainSub.trans sub) hi primary main.primitive main.separable (lp.trans_lt grade) cmain
    ((Nat.mul_le_mul_right v (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 lp) 1)).trans_lt smallV) (by
      intro z hz;rw [←read];exact (mem_filter.mp hz).2)
  have priceE:=owned_count F (exclSub.trans sub) hi e prim sep (le'.trans_lt grade) (seed.trans cother)
    ((Nat.mul_le_mul_right w (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 le') 1)).trans_lt smallW) (by
      intro z hz
      have atZ:=actual z (exclSub hz)
      rw [eq,map_mul] at atZ
      rw [←read]
      exact (mul_eq_zero.mp atZ).resolve_left (fun zero=>(mem_sdiff.mp hz).2 (mem_filter.mpr ⟨exclSub hz,zero⟩)))
  refine ⟨_,_,rfl,degrees,?_⟩
  have split:E.card+P.card=S.card:=card_sdiff_add_card_eq_card mainSub
  omega

end
end Research6969.JointMarked
end Z6969Source0438

-- Source: Research6969.MixedSectionCredit
section Z6969Source0439
set_option autoImplicit true
namespace Research6969.MixedSectionCredit
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_2
open Finset

/-- The mixed generic line pays for at least the ordinate section on every active surface. -/
theorem section_le (I : Ideal Ambient) (active : Active I) :
    sectionDegree I 1 ≤ sectionDegree I 2 := by
  classical
  obtain ⟨nonempty,dimension⟩ := K1_14_2_2_7_2_1.proof I active
  obtain ⟨prime,_⟩ := K1_14_2_2_7_2_5.proof I active.prime nonempty
  let _ : (seedIdeal I).IsPrime := prime
  let _ : IsDomain (JetSeedSection I) := inferInstanceAs (IsDomain (SeedAmbient ⧸ seedIdeal I))
  have ids : K1_14_2_2_7_2.c2 := K1_14_2_2_7_2_2.of_children
    K1_14_2_2_7_2_2_1.proof K1_14_2_2_7_2_2_2.proof K1_14_2_2_7_2_2_3.proof
  obtain ⟨seed,y,mixed⟩ := ids I active
  let _ : CharP SeedField p := charP_of_injective_ringHom
    ((algebraMap FX SeedField).comp seedEmbedding).injective p
  obtain ⟨places⟩ := K1_14_2_2_7_2_3.proof p SeedField (JetSeedSection I) dimension
    (seedCoord I 1) (seedCoord I 2) (seedCoord I 3)
    (by rw [seed]; exact active.seed_size.1) (by rw [seed]; exact active.seed_size.2)
  rw [← y, ← mixed, places.degree_eq (seedCoord I 2), places.line_eq]
  exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ (le_max_left _ _)

/-- This is the mass comparison used on both lists of terminal parents. -/
theorem mass_le (S : Finset (Ideal Ambient)) (active : ∀ I ∈ S, Active I) :
    mass S 1 ≤ mass S 2 :=
  sum_le_sum fun I h => section_le I (active I h)

/-- A slope-free cut on a production surface has exactly the two mixed
coefficients in the shortened surface price on its moving curve components. -/
theorem moving_cut (I : Ideal Ambient) (active : Active I) (P : Jet) (y seed : ℕ)
    (caps : RowCaps P (⟨0,y,0,seed⟩ : Shape)) (proper : toJet P ∉ I) :
    curveSeedMass (K1_14_2_2_7.movingComponents I P) ≤
        seed * sectionDegree I 0 + y * sectionDegree I 1 ∧
    curveYMass (K1_14_2_2_7.movingComponents I P) ≤ seed * sectionDegree I 1 := by
  have a:=P0_10R.Bridge.cut_seed_mass (⟨0,y,0,seed⟩ : Shape) I P (Nat.zero_le _) active caps proper
  have b:=P0_10R.Bridge.cut_ordinate_mass (⟨0,y,0,seed⟩ : Shape) I P (Nat.zero_le _) active caps proper
  constructor
  · simpa [dot,weight,Fin.sum_univ_succ] using a
  · simpa [dot,weight,Fin.sum_univ_succ] using b

end
end Research6969.MixedSectionCredit
end Z6969Source0439
