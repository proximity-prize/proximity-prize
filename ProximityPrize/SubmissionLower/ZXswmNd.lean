import ProximityPrize.SubmissionLower.ZATKiYa
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, IsFractionRing.injective → zxb, Polynomial.X → z7y, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_pow → z5m, Polynomial.map_sub → z3A
section
namespace qcuqT2c
noncomputable section
open Polynomial
open cu (L)
open P5 (p)
open qbjv5ec (aQ lN EC)
open scoped WithZero
abbrev Simple (y :EC) :=IntermediateField.adjoin lN ({y} : Set EC)
def seed :lN :=
 algebraMap aQ[X] lN (C (algebraMap L[X] aQ (z7y (R:=L))))
def amm:lN :=algebraMap aQ[X] lN (z7y (R:=aQ))
def constant (a :L) :lN :=
 algebraMap aQ[X] lN (C (algebraMap L[X] aQ (C a)))
abbrev zIn (y :EC) :Simple y :=algebraMap lN (Simple y) seed
abbrev xIn (y :EC) :Simple y :=algebraMap lN (Simple y) amm
abbrev cIn (y :EC) (a :L) :Simple y :=algebraMap lN (Simple y) (constant a)
abbrev tIn (y :EC) (x :L) :Simple y :=xIn y - cIn y x
structure TamePlace {E :Type} [Field E] (v :Valuation E ℤᵐ⁰) (z t:E) :Prop where
 surj:Function.Surjective v
 ramified : ∃ e :ℕ,0<e∧e<p∧v t=WithZero.exp (-(e :ℤ))
 seed_unit :v z=1
 seed_not_power : ∀ a :IsLocalRing.ResidueField v.valuationSubring,
  a^p≠IsLocalRing.residue v.valuationSubring ⟨z,seed_unit.le⟩
end
end qcuqT2c
end
section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qkA2Qzc
noncomputable section
open Polynomial qbjv5ec
open cu (L)
open P5_7_7 (Dg seedDerivative)
open qGnV2ac (EquationBounds coeff_seedDerivative)
open private cut_map polar_degree from ProximityPrize.SubmissionLower.ZATKiYa
private theorem product {E :Type*} [Field E] (f b g:E[X]) (n:ℕ)
   (hf :f.Splits) (hb:b.natDegree≤n) (hg:g.natDegree≤n)
   (hn:f≠0) (hr : ∀ y∈f.roots,b.eval y≠0) :
   let P:=(f.map C).resultant (b.map C+C (z7y:E[X])*g.map C) f.natDegree n
   let Q:=(f.roots.map fun y=>1+Polynomial.X*C (g.eval y/b.eval y)).prod
   P.coeff 0≠0∧P=C (P.coeff 0)*Q:= by
 dsimp only
 let G:E[X][X] :=b.map C+C (z7y:E[X])*g.map C
 let d:=f.leadingCoeff^n*(f.roots.map b.eval).prod
 let q:E[X] :=(f.roots.map fun y=>1+Polynomial.X*C (g.eval y/b.eval y)).prod
 have hG:G.natDegree≤n :=
   (natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans hb)
     ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hg)))
 have he (y :E) (hy :y∈f.roots) :
     G.eval (C y)=C (b.eval y)*(1+Polynomial.X*C (g.eval y/b.eval y)) := by
   simp only [G,eval_add,eval_mul,eval_C,eval_map,eval₂_hom,mul_add,mul_one]
   rw [mul_left_comm,← map_mul,mul_div_cancel₀ _ (hr y hy)]
 let P:=(f.map C).resultant G f.natDegree n
 have hp:P=C d*q:= by
   unfold P
   rw [← natDegree_map_eq_of_injective C_injective f,
     resultant_eq_prod_eval _ _ _ hG (hf.map C),hf.roots_map C,
     leadingCoeff_map_of_injective C_injective,Multiset.map_map]
   change _ *(f.roots.map fun y=>G.eval (C y)).prod= _
   have hmap :=map_multiset_prod (C:E →+* E[X]) (f.roots.map b.eval)
   simp only [Multiset.map_map,Function.comp_def] at hmap
   rw [Multiset.map_congr rfl he,Multiset.prod_map_mul,← hmap,
     ← mul_assoc,← map_pow,← map_mul]
 have hq:q.coeff 0=1 := by
   change constantCoeff q=1
   simp [q,map_multiset_prod]
 have hc:P.coeff 0=d:= by rw [hp,coeff_C_mul,hq,mul_one]
 have hd:d≠0:= by
   apply mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hn))
   intro hz
   obtain ⟨y,hy,h⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
   exact hr y hy h
 exact ⟨hc ▸ hd,hc ▸ hp⟩
private theorem integralProduct {A E :Type*} [CommRing A] [Field E] [Algebra A E]
   (s :Multiset E) (a :E→E) (ha : ∀ y∈s,IsIntegral A (a y)) (i:ℕ) :
   IsIntegral A (((s.map fun y=>1+Polynomial.X*C (a y)).prod:E[X]).coeff i) := by
 induction s using Multiset.induction_on generalizing i with
 | empty=>cases i <;> simp [coeff_one,isIntegral_one,isIntegral_zero]
 | cons y s ih =>
   rw [Multiset.map_cons,Multiset.prod_cons,coeff_mul]
   apply IsIntegral.sum
   intro j _
   apply IsIntegral.mul _ (ih (fun z hz=>ha z (Multiset.mem_cons_of_mem hz)) j.2)
   have hy :=ha y (Multiset.mem_cons_self y s)
   cases j.1 with
   | zero=>simp [isIntegral_one]
   | succ k=>cases k <;> simp [coeff_one,hy,isIntegral_zero]
private def swapped:Coeff →+* aQ[X] :=
 (mapRingHom (algebraMap L[X] aQ)).comp Bivariate.swap.toRingHom
private def overRoots :Coeff →+* EC :=
 (algebraMap lN EC).comp qY
private theorem swapped_inj:zq4 swapped :=
 (zTo _ (zxb L[X] aQ)).comp
   Bivariate.swap.injective
private theorem overRoots_inj:zq4 overRoots :=
 (algebraMap lN EC).injective.comp
   ((zxb aQ[X] lN).comp swapped_inj)
private theorem normalized {F:Dg} {l h:ℕ} (H :EquationBounds F l h)
    (x r :L) (ht:TameAt F x r) :
    let R:=reciprocalResultant F r
    overRoots (R.coeff 0)≠0 ∧
      ∀ i:ℕ,IsIntegral (NodeRing x) (overRoots (R.coeff i)/overRoots (R.coeff 0)) := by
  let f :=F.map overRoots
  let b:=(polar F r).map overRoots
  let g:=(seedDerivative F).map overRoots
  let e :=mapRingHom overRoots
  let R:=reciprocalResultant F r
  have he :e.comp C=C.comp overRoots :=RingHom.ext fun _=>map_C overRoots
  have hr :R.map overRoots =
      (f.map C).resultant (b.map C+C (z7y:EC[X])*g.map C)
        f.natDegree f.natDegree := by
    change e (resultantOver F (seedDerivative F) (C (C r)))= _
    rw [resultantOver,← resultant_map_map (F.map C) (cutOver F (seedDerivative F) (C (C r))) _ _ e,
      cut_map,he,show e (z7y:Coeff[X])=z7y from map_X _,
      show F.natDegree=f.natDegree from (natDegree_map_eq_of_injective overRoots_inj _).symm]
    dsimp only [f,b,g]
    rw [zoi C e F,he,
      zoi overRoots C F,zoi overRoots C (polar F r),
      zoi overRoots C (seedDerivative F)]
  have ht' (y :EC) (hy :y∈f.roots) :
      b.eval y≠0∧IsIntegral (NodeRing x) (g.eval y/b.eval y) := by
    simpa only [f,b,g,eval_map,cTD,overRoots] using
      ht y (by simpa only [f,eval_map,cTD,overRoots,IsRoot] using
        (isRoot_of_mem_roots hy))
  have hl:0<F.natDegree := by rw [H.jU]; exact Nat.zero_lt_of_lt H.two_le
  have hb:b.natDegree≤f.natDegree := by
    rw [show f.natDegree=F.natDegree from natDegree_map_eq_of_injective overRoots_inj _]
    exact natDegree_map_le.trans (polar_degree F (C (C r)) hl)
  have hg:g.natDegree≤f.natDegree := by
    rw [show f.natDegree=F.natDegree from natDegree_map_eq_of_injective overRoots_inj _]
    apply natDegree_map_le.trans
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_seedDerivative,coeff_eq_zero_of_natDegree_lt hi,derivative_zero]
  have hn:f≠0:=(map_ne_zero_iff (mapRingHom _) (zTo _ overRoots_inj)).mpr
    H.irreducible.ne_zero
  have hh:=product f b g f.natDegree (IsAlgClosed.splits f) hb hg hn (fun y hy=>(ht' y hy).1)
  rw [← hr] at hh
  dsimp only at hh
  rw [coeff_map] at hh
  refine ⟨hh.1,fun i => ?_⟩
  have hc:=congrArg (fun p:EC[X]=>p.coeff i) hh.2
  rw [coeff_map,coeff_C_mul] at hc
  rw [hc,mul_div_cancel_left₀ _ hh.1]
  exact integralProduct f.roots (fun y=>g.eval y/b.eval y) (fun y hy=>(ht' y hy).2) i
private theorem adic_le (x :L) (a d:Coeff) (hd:overRoots d≠0)
  (ha :IsIntegral (NodeRing x) (overRoots a/overRoots d)) :
  (physicalPrime x).intValuation (swapped a)≤(physicalPrime x).intValuation (swapped d) := by
 let v :=physicalPrime x
 let c:=algebraMap aQ[X] lN
 let u:=c (swapped a)/ c (swapped d)
 let e :=IsScalarTower.toAlgHom (NodeRing x) lN EC
 have he :e u=overRoots a/overRoots d:=map_div₀ (algebraMap lN EC) _ _
 have hi:IsIntegral (NodeRing x) u:=(isIntegral_algHom_iff e e.injective).mp (he.symm ▸ ha)
 obtain ⟨b,hb⟩:=IsIntegrallyClosed.isIntegral_iff.mp hi
 have hm:u∈NodeRing x := by rw [← hb]; exact b.property
 change u∈v.valuationSubringAtPrime lN at hm
 rw [v.valuationSubringAtPrime_eq_valuationSubring] at hm
 have hv :=(Valuation.mem_valuationSubring_iff _ _).mp hm
 change v.valuation lN (c (swapped a)/ c (swapped d))≤1 at hv
 rw [map_div₀,v.valuation_of_algebraMap,v.valuation_of_algebraMap] at hv
 have hdn:swapped d≠0:= by
  intro hz
  apply hd
  change algebraMap lN EC (c (swapped d))=0
  rw [hz,map_zero,map_zero]
 have hpos :=pos_iff_ne_zero.mpr (v.intValuation_ne_zero _ hdn)
 simpa only [one_mul] using (div_le_iff₀ hpos).mp hv
private theorem rawPower (x :L) (k :ℕ) :
  Bivariate.swap (C (((z7y:L[X]) - C x)^k))=((z7y:Coeff) - C (C x))^k := by
 rw [Bivariate.swap_C,z5m,z3A,zSo,zrL]
private theorem specialize (x :L) (A:Coeff) :
   (Bivariate.swap A).eval (C x)=A.map (evalRingHom x) := by
 induction A using Polynomial.induction_on' with
 | add P Q hP hQ=>simp only [map_add,Polynomial.map_add,eval_add,hP,hQ]
 | monomial n f =>
   simp only [Bivariate.swap_monomial,eval_mul,eval_C,eval_map,eval₂_hom,
     map_monomial,coe_evalRingHom,C_mul_X_pow_eq_monomial]
private theorem strip (R:Coeff[X]) (x :L) (hd:R.coeff 0≠0)
    (h : ∀ i:ℕ,(physicalPrime x).intValuation (swapped (R.coeff i)) ≤
      (physicalPrime x).intValuation (swapped (R.coeff 0))) :
    ∃ (k :ℕ) (T:Coeff[X]),R=C (C (((z7y:L[X]) - C x)^k))*T ∧
      (T.coeff 0).map (evalRingHom x)≠0:= by
  let S:=Bivariate.swap (R:=L)
  let c:=algebraMap L[X] aQ
  let D:=S (R.coeff 0)
  let k :=D.rootMultiplicity (C x)
  let q:L[X] :=((z7y:L[X]) - C x)^k
  let v :=physicalPrime x
  have hn:D ≠0:= by exact (map_ne_zero_iff S S.injective).mpr hd
  obtain ⟨A,hA,hAn⟩:=exists_eq_pow_rootMultiplicity_mul_and_not_dvd D hn (C x)
  have hq (i:ℕ) :C q∣R.coeff i:= by
    have hu (a :aQ[X]) : (uniformizer x)^k∣a ↔
        v.intValuation a≤WithZero.exp (-(k :ℤ)) := by
      have hv :v.asIdeal=Ideal.span ({uniformizer x} : Set aQ[X]) :=rfl
      rw [v.intValuation_le_pow_iff_mem,hv,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    have he : (S (C q)).map c=(uniformizer x)^k := by
      rw [show S (C q)=((z7y:Coeff) - C (C x))^k from rawPower x k,
        z5m,z3A,zSo,zrL]
    have hc: (uniformizer x)^k∣swapped (R.coeff 0) := by
      refine ⟨A.map c,?_⟩
      change D.map c=(uniformizer x)^k*A.map c
      rw [hA,Polynomial.map_mul,z5m,z3A,zSo,
        zrL]
    have hi:=(hu _).mpr ((h i).trans ((hu _).mp hc))
    have hm: (S (C q)).map c∣(S (R.coeff i)).map c:=he.symm ▸ hi
    have hmon : (S (C q)).Monic:=(rawPower x k).symm ▸ (monic_X_sub_C (C x)).pow k
    exact (map_dvd_iff S).mp
      ((Polynomial.map_dvd_map c (zxb L[X] aQ) hmon).mp hm)
  obtain ⟨T,hT⟩:=(C_dvd_iff_dvd_coeff (C q) R).mpr hq
  refine ⟨k,T,hT,?_⟩
  have hs :D =((z7y:Coeff) - C (C x))^k*S (T.coeff 0) := by
    have hm:=congrArg (fun p:Coeff[X]=>S (p.coeff 0)) hT
    simpa only [coeff_C_mul,map_mul,S,q,rawPower] using hm
  have hcancel:S (T.coeff 0)=A :=
    mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) (hs.symm.trans hA)
  intro hz
  apply hAn
  apply dvd_iff_isRoot.mpr
  change A.eval (C x)=0
  rw [← hcancel,specialize]
  exact hz
theorem proof :qbjv5ec.c2 := by
 intro F l h H x r ht
 obtain ⟨hd,hi⟩:=normalized H x r ht
 exact strip _ x (fun hz=>hd (by rw [hz,map_zero])) (fun i=>adic_le _ _ _ hd (hi i))
end
end qkA2Qzc
end
