import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.ZjU0F6a
import ProximityPrize.SubmissionLower.Z6Jqnnb
import ProximityPrize.SubmissionLower.ZjG08xb
set_option Elab.async false
set_option maxRecDepth 4000
section
set_option backward.isDefEq.respectTransparency false
namespace qmgvT1d
noncomputable section
open Polynomial IsLocalRing
theorem power_sum_ne {E :Type} [Field E] {q:ℕ} [CharP E q]
  (hq:q.Prime) (S:Subfield E) {z :E} (hz :z∉S) (hzp:z^q∈S)
  (a :Fin q→S) (i:Fin q) (hi:a i≠0) :
  (∑ j,(a j:E)*z^(j:ℕ))≠0:= by
 classical
 let:Fact q.Prime :=⟨hq⟩
 let b:S:=⟨z^q,hzp⟩
 let f :S[X] :=Polynomial.X ^q - C b
 have hb (x :S) :x^q≠b:= by
  intro h
  have h' : (x :E)^q=z^q:=congrArg Subtype.val h
  have he : (x :E)=z :=(frobenius E q).injective h'
  exact hz (he ▸ x.property)
 have hf :Irreducible f :=X_pow_sub_C_irreducible_of_prime hq hb
 have hfz :aeval z f=0:= by
  simp only [f,map_sub,map_pow,aeval_X,aeval_C]
  exact sub_self _
 have hm:=minpoly.eq_of_irreducible_of_monic hf hfz (monic_X_pow_sub_C b hq.ne_zero)
 let T:=IntermediateField.adjoin S ({z} : Set E)
 let hc:IsIntegral S z :=⟨f,monic_X_pow_sub_C b hq.ne_zero,hfz⟩
 let B:=IntermediateField.adjoin.powerBasis hc
 have hd:B.dim=q:= by
  change (minpoly S z).natDegree=q
  rw [← hm]
  exact natDegree_X_pow_sub_C
 have hB:=B.basis.linearIndependent.map' T.val.toLinearMap
  (LinearMap.ker_eq_bot_of_injective T.val.injective)
 have he :T.val.toLinearMap ∘ B.basis=fun j:Fin B.dim=>z^(j:ℕ) := by
  funext j
  change T.val (B.basis j)= _
  rw [B.basis_eq_pow,map_pow]
  rfl
 rw [he] at hB
 have hl:LinearIndependent S (fun j:Fin B.dim=>z^(j:ℕ)) :=hB
 rw [hd] at hl
 intro hs
 exact hi (Fintype.linearIndependent_iff.mp hl a hs i)
def restrictedResidue {E :Type} [Field E] (V:ValuationSubring E) (S:Subfield E) :
    Subfield (ResidueField V) := by
  let T:Subring V:=S.toSubring.comap V.subtype
  let f :=(residue V).comp T.subtype
  refine { f.range with inv_mem' := ?_ }
  rintro _ ⟨x,rfl⟩
  by_cases hx :f x=0
  · simp only [hx,inv_zero]
    exact ⟨0,map_zero f⟩
  have hu:IsUnit (x :V) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact fun h=>hx ((residue_eq_zero_iff _).2 h)
  let y :V := ↑(hu.unit⁻¹)
  have hxy : (x :V)*y=1 := by simp [y]
  have hy : (y :E)=((x :V) :E)⁻¹:= by
    have H :=congrArg V.subtype hxy
    rw [map_mul,map_one] at H
    change ((x :V) :E)*(y :E)=1 at H
    exact eq_inv_of_mul_eq_one_right H
  have hyT:y∈T:= by
    change (y :E)∈S
    rw [hy]
    exact S.inv_mem x.property
  refine ⟨⟨y,hyT⟩,?_⟩
  change residue V y=(residue V (x :V))⁻¹
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul,mul_comm,hxy,map_one]
@[simp] theorem mem_restrictedResidue {E :Type} [Field E] (V:ValuationSubring E)
   (S:Subfield E) (x :ResidueField V) :
   x∈restrictedResidue V S ↔ ∃ y :V,(y :E)∈S∧residue V y=x := by
  change (∃ y :S.toSubring.comap V.subtype,residue V y=x)↔_
  exact ⟨fun ⟨y,h⟩=>⟨y,y.property,h⟩,fun ⟨y,hy,h⟩=>⟨⟨y,hy⟩,h⟩⟩
theorem normalize_row {A E :Type} [Field A] [Field E] {q:ℕ}
   (V:ValuationSubring E) (f :A →+* E) (c:Fin q→A) (k :Fin q)
   (hk :c k≠0) (hm : ∀ i,V.valuation (f (c i))≤V.valuation (f (c k))) :
   ∃ d:Fin q→A,d k=1∧(∀ i,f (d i)∈V) ∧
     ∀ z :E,f (c k)*(∑ i,f (d i)*z^(i:ℕ)) = ∑ i,f (c i)*z^(i:ℕ) := by
 let d (i:Fin q) :=c i/ c k
 have hfk :f (c k)≠0:=(_root_.map_ne_zero f).2 hk
 refine ⟨d,div_self hk,?_,?_⟩
 · intro i
   change f (c i/ c k)∈V
   rw [← V.valuation_le_one_iff,map_div₀,map_div₀,
     div_le_one₀ (V.valuation.pos_iff.mpr hfk)]
   exact hm i
 · intro z
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   change f (c k)*(f (c i/ c k)*z^(i:ℕ))= _
   rw [← mul_assoc,map_div₀,mul_comm (f (c k)),div_mul_cancel₀ _ hfk]
theorem residue_sum {E :Type} [Field E] (V:ValuationSubring E) {q:ℕ}
  (a :Fin q→V) (z t:V)
  (h: (∑ i,(a i:E)*(z :E)^(i:ℕ))=(t:E)) :
  (∑ i,residue V (a i)*residue V z^(i:ℕ))=residue V t:= by
 have H : (∑ i,a i*z^(i:ℕ))=t:= by
  apply V.subtype_injective
  simp only [map_sum,map_mul,map_pow]
  exact h
 simpa only [map_sum,map_mul,map_pow] using congrArg (residue V) H
theorem coefficients_mem {E :Type} [Field E] {q:ℕ}
   (hq:q.Prime) (V:ValuationSubring E) [CharP (ResidueField V) q]
   (S:Subfield E) (z :V)
   (hz :residue V z∉restrictedResidue V S)
   (hzp:residue V z^q∈restrictedResidue V S) (c:Fin q→S)
   (hc: (∑ j,(c j:E)*(z :E)^(j:ℕ))∈V) (i:Fin q) : (c i:E)∈V:= by
 classical
 by_contra hi
 obtain ⟨k,_,hk⟩:=Finset.exists_max_image Finset.univ
   (fun j=>V.valuation (c j:E)) ⟨i,Finset.mem_univ i⟩
 have hk' : (c k :E)∉V:= fun H =>
   hi ((V.valuation_le_one_iff _).1 ((hk i (Finset.mem_univ i)).trans
     ((V.valuation_le_one_iff _).2 H)))
 have hk0:c k≠0:= by
   intro H
   apply hk'
   rw [H]
   exact V.zero_mem
 obtain ⟨d,hdk,hdV,hscale⟩ :=
   normalize_row V S.subtype c k hk0 (fun j=>hk j (Finset.mem_univ j))
 let b (j:Fin q) :V:=⟨d j,hdV j⟩
 let B (j:Fin q) :restrictedResidue V S :=
   ⟨residue V (b j),(mem_restrictedResidue _ _ _).2 ⟨b j,(d j).property,rfl⟩⟩
 have hB:B k≠0:= by
   have hbk :b k=1 := by
     apply Subtype.ext
     change (d k :E)=1
     rw [hdk]
     rfl
   intro H
   have hh:residue V (b k)=0:=congrArg Subtype.val H
   rw [hbk,map_one] at hh
   exact one_ne_zero hh
 let t:V:=⟨∑ j,(b j:E)*(z :E)^(j:ℕ),
   V.toSubring.sum_mem fun j _=>V.toSubring.mul_mem (b j).property (V.pow_mem z.property _)⟩
 have htr :residue V t=0:= by
   by_contra H
   have hu:IsUnit t:= by
     rw [← IsLocalRing.notMem_maximalIdeal]
     exact fun h=>H ((residue_eq_zero_iff _).2 h)
   have ht1 :V.valuation (t:E)=1 :=(V.valuation_eq_one_iff t).1 hu
   have Hscale : (c k :E)*(t:E) = ∑ j,(c j:E)*(z :E)^(j:ℕ) :=
     hscale (z :E)
   have Hv :=(V.valuation_le_one_iff _).2 hc
   rw [← Hscale,map_mul,ht1,mul_one] at Hv
   exact hk' ((V.valuation_le_one_iff _).1 Hv)
 have hzero :=residue_sum V b z t rfl
 rw [htr] at hzero
 exact power_sum_ne hq (restrictedResidue V S) hz hzp B k hB hzero
end
end qmgvT1d
end
section
set_option backward.isDefEq.respectTransparency false
namespace qmgvT1d
noncomputable section
open Polynomial qps5rle qymFiQe
open P5 (K p)
open cu (L)
local instance :CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
theorem char_seed :CharP SeedSeries p :=
 charP_of_injective_ringHom (algebraMap L SeedSeries).injective p
attribute [local instance] char_seed
theorem char_F:CharP F p :=
 charP_of_injective_ringHom (algebraMap SeedSeries F).injective p
attribute [local instance] char_F
local instance :Fact p.Prime :=⟨CharP.char_prime_of_ne_zero K (by decide)⟩
local instance (w:Roots) :CharP (Simple w) p :=
 charP_of_injective_ringHom (algebraMap F (Simple w)).injective p
theorem prime_p:p.Prime :=CharP.char_prime_of_ne_zero K (by decide)
theorem pow_constant (D:Derivation ℤ F F) (a :F) :a^p∈constants D:= by
 change D (a^p)=0
 rw [D.leibniz_pow]
 simp only [smul_eq_mul,← Nat.cast_smul_eq_nsmul F,CharP.cast_eq_zero,zero_mul]
abbrev constantMap (D:Derivation ℤ F F) (w:Roots) :constants D →+* Simple w :=
 (algebraMap F (Simple w)).comp (constants D).subtype
private def powerMap (D:Derivation ℤ F F) :F →+* constants D :=
 (frobenius F p).codRestrict (constants D).toSubring (pow_constant D)
private theorem eval_power (D:Derivation ℤ F F) (w:Roots) (g:F[X]) :
   (g.eval₂ (algebraMap F (Simple w)) (point w))^p =
     (g.map (powerMap D)).eval₂ (constantMap D w) (point w^p) := by
 let f :=algebraMap F (Simple w)
 let φ:=frobenius (Simple w) p
 have h:φ.comp f=(constantMap D w).comp (powerMap D) := by
   apply RingHom.ext
   intro a
   change f a^p=f (a^p)
   exact (map_pow f a p).symm
 change φ (g.eval₂ f (point w))= _
 calc
   _=g.eval₂ (φ.comp f) (φ (point w)) :=hom_eval₂ g f φ _
   _=(g.map (powerMap D)).eval₂ (constantMap D w) (point w^p) := by
     rw [h,eval₂_map]
     rfl
private theorem eval_point (w:Roots) (g:F[X]) :
  (Simple w).val.toRingHom (g.eval₂ (algebraMap F (Simple w)) (point w))=aeval w g:= by
 rw [hom_eval₂,aeval_def]
 rfl
private theorem adjoin_relation {A E :Type} [Field A] [Field E] [Algebra A E] {q:ℕ}
   (z :E) (g:A[X]) (hg:g.Monic) (hz :aeval z g=0) (hd:g.natDegree<q)
   (x :E) (hx :x∈IntermediateField.adjoin A ({z} : Set E)) :
   ∃ a :Fin q→A,(∃ k,a k≠0) ∧
     (∑ i,algebraMap A E (a i)*x^(i:ℕ))=0:= by
 let T:=IntermediateField.adjoin A ({z} : Set E)
 have hz' : IsIntegral A z :=⟨g,hg,hz⟩
 let:FiniteDimensional A T:=IntermediateField.adjoin.finiteDimensional hz'
 have hdim:Module.finrank A T<q:= by
   rw [IntermediateField.adjoin.finrank hz']
   exact (natDegree_le_of_dvd (minpoly.dvd A z hz) hg.ne_zero).trans_lt hd
 let t:T:=⟨x,hx⟩
 let P:=minpoly A t
 have hP:P.natDegree<q:=(minpoly.natDegree_le t).trans_lt hdim
 have hm:P.Monic:=minpoly.monic (IsIntegral.of_finite _ t)
 refine ⟨fun i=>P.coeff (i:ℕ),⟨⟨P.natDegree,hP⟩,?_⟩,?_⟩
 · change P.coeff P.natDegree≠0
   rw [coeff_natDegree,hm.leadingCoeff]
   exact one_ne_zero
 · have h:aeval x P=0:= by
     change aeval (T.val t) P=0
     rw [aeval_algHom_apply,minpoly.aeval,map_zero]
   rwa [aeval_def,eval₂_eq_sum_range' _ hP,← Fin.sum_univ_eq_sum_range] at h
theorem short_relation (D:Derivation ℤ F F) (w:Roots) (hs :IsSeparable F w)
    (hd:Module.finrank F (Simple w)<p) (x :smallConstants D w) :
    ∃ a :Fin p→ constants D,(∃ k,a k≠0) ∧
      (∑ i,constantMap D w (a i)*(x :Simple w)^(i:ℕ))=0:= by
  classical
  let:Algebra (constants D) (Simple w) :=(constantMap D w).toAlgebra
  let z :=point w^p
  let T:=IntermediateField.adjoin (constants D) ({z} : Set (Simple w))
  have hm:smallConstants D w≤T.toSubfield := by
    apply sup_le
    · rintro _ ⟨a,ha,rfl⟩
      exact T.algebraMap_mem ⟨a,ha⟩
    · rw [Subfield.closure_le]
      rintro _ ⟨y,rfl⟩
      obtain ⟨r,s,hy⟩:=(IntermediateField.mem_adjoin_simple_iff F (y :Roots)).mp y.property
      have hy' : y=r.eval₂ (algebraMap F (Simple w)) (point w) /
          s.eval₂ (algebraMap F (Simple w)) (point w) := by
        apply (Simple w).val.injective
        rw [map_div₀,eval_point,eval_point]
        exact hy
      change y ^p∈T
      rw [hy',div_pow,eval_power D w r,eval_power D w s]
      apply T.div_mem
      all_goals
        change _∈T.toSubalgebra
        apply Algebra.adjoin_le (S:=T.toSubalgebra) _ (Polynomial.aeval_mem_adjoin_singleton _ z)
        exact Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self _ _)
  let f :=(minpoly F w).map (powerMap D)
  have hf :f.Monic:=(minpoly.monic hs.isIntegral).map _
  have hz :aeval z f=0:= by
    change ((minpoly F w).map (powerMap D)).eval₂ (constantMap D w) (point w^p)=0
    rw [← eval_power D w]
    have H : (minpoly F w).eval₂ (algebraMap F (Simple w)) (point w)=0:= by
      apply (Simple w).val.injective
      rw [eval_point,minpoly.aeval,map_zero]
    rw [H,zero_pow prime_p.ne_zero]
  have hdf :f.natDegree<p:= by
    change ((minpoly F w).map (powerMap D)).natDegree<p
    rwa [natDegree_map_eq_of_injective (powerMap D).injective,←
      IntermediateField.adjoin.finrank hs.isIntegral]
  exact adjoin_relation z f hf hz hdf x (hm x.property)
end
end qmgvT1d
end
section
set_option backward.isDefEq.respectTransparency false
namespace qmgvT1d
noncomputable section
open qps5rle qymFiQe HahnSeries IsLocalRing WithZero
open scoped WithZero
abbrev uniformizer :F:=HahnSeries.single 1 1
private theorem mem_integer_iff (a :F) :
  a∈IntegerRing ↔ ∀ i:ℤ,i<0→a.coeff i=0 :=
 LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=0)
theorem uniformizer_mem:uniformizer∈IntegerRing :=
 (mem_integer_iff _).2 fun i hi=>coeff_single_of_ne (by omega)
private theorem cHU (a :SeedSeries) :algebraMap SeedSeries F a∈IntegerRing:= by
 apply (mem_integer_iff _).2
 intro i hi
 simp [LaurentSeries.algebraMap_apply,C_apply,ne_of_lt hi]
private theorem physical_shift (a :F) {m:ℤ} (ha :vPhysical a=exp m) (n:ℤ) :
  vPhysical ((HahnSeries.single n 1 :F)*a)=exp (m - n) := by
 rw [map_mul,ha,LaurentSeries.valuation_single_zpow,← exp_add]
 congr 1
 omega
section
variable {E :Type} [Field E] (V:ValuationSubring E) (f :F →+* E)
variable (hV : ∀ a :IntegerRing,f (a :F)∈V)
include hV in
theorem contains_base (ht:f uniformizer⁻¹∈V) (a :F) :f a∈V:= by
 by_cases ha :a=0
 · rw [ha,map_zero]
   exact V.zero_mem
 let m:=log (vPhysical a)
 have hm:vPhysical a=exp m:=(exp_log (vPhysical.zero_iff.not.mpr ha)).symm
 let n:=m.toNat
 have hn: (n:ℤ)≥m:=Int.self_le_toNat _
 have hb:uniformizer^n*a∈IntegerRing:= by
   change vPhysical (_ *a)≤1
   rw [HahnSeries.single_pow,one_pow,nsmul_eq_mul,mul_one,
     physical_shift a hm,← exp_zero,exp_le_exp]
   omega
 have hτ:uniformizer≠0:=HahnSeries.single_ne_zero one_ne_zero
 have H :=V.toSubring.mul_mem (V.pow_mem ht n) (hV ⟨_,hb⟩)
 change f uniformizer⁻¹^n*f (uniformizer^n*a)∈V at H
 rw [map_mul,← mul_assoc,← map_pow,← map_mul,← mul_pow,
   inv_mul_cancel₀ hτ,one_pow,map_one,one_mul] at H
 exact H
include hV in
theorem mem_integer_of_nonunit (ht:f uniformizer⁻¹∉V) {a :F}
  (ha :f a∈V) :a∈IntegerRing:= by
 by_contra h
 have ha0:a≠0:= fun hn=>h (hn ▸ zero_mem _)
 let m:=log (vPhysical a)
 have hm:vPhysical a=exp m:=(exp_log (vPhysical.zero_iff.not.mpr ha0)).symm
 have hm1 :1≤ m:= by
  change ¬ vPhysical a≤1 at h
  rw [hm,← exp_zero,exp_le_exp] at h
  omega
 have hτ:uniformizer⁻¹=(HahnSeries.single (-1) 1 :F) := by
  rw [HahnSeries.inv_single,inv_one]
 have hi:vPhysical a⁻¹=exp (-m) := by rw [map_inv₀,hm,exp_neg]
 have hb:uniformizer⁻¹*a⁻¹∈IntegerRing:= by
  change vPhysical (_ *_)≤1
  rw [hτ,physical_shift _ hi,← exp_zero,exp_le_exp]
  omega
 apply ht
 have H :=V.toSubring.mul_mem (hV ⟨_,hb⟩) ha
 change f (uniformizer⁻¹*a⁻¹)*f a∈V at H
 rwa [← map_mul,mul_assoc,inv_mul_cancel₀ ha0,mul_one] at H
abbrev ringLift:IntegerRing →+* V :=
 (f.comp vPhysical.valuationSubring.subtype).codRestrict V.toSubring hV
abbrev aih:SeedSeries →+* V :=
 (ringLift V f hV).comp
   ((algebraMap SeedSeries F).codRestrict IntegerRing.toSubring cHU)
theorem fWQ (ht:f uniformizer⁻¹∉V) (a :IntegerRing) :
   residue V (ringLift V f hV a)=residue V (aih V f hV ((a :F).coeff 0)) := by
 let τ:IntegerRing:=⟨uniformizer,uniformizer_mem⟩
 let a₀:=((algebraMap SeedSeries F).codRestrict IntegerRing.toSubring cHU)
   ((a :F).coeff 0)
 have hτ:residue V (ringLift V f hV τ)=0:= by
   apply (residue_eq_zero_iff _).2
   apply (V.valuation_lt_one_iff _).2
   refine lt_of_le_of_ne (V.valuation_le_one _) fun h=>ht ?_
   change V.valuation (f uniformizer)=1 at h
   rw [← V.valuation_le_one_iff,map_inv₀,map_inv₀,h,inv_one]
 let b:=(HahnSeries.single (-1) 1 :F)*((a :F)-(a₀:F))
 have hb:b∈IntegerRing:= by
   apply (mem_integer_iff _).2
   intro i hi
   change ((HahnSeries.single (-1) 1 :F)*_).coeff i=0
   rw [coeff_single_mul,one_mul,HahnSeries.coeff_sub]
   have hle :i-(-1 :ℤ)≤0:= by omega
   rcases lt_or_eq_of_le hle with hlt | he
   · rw [(mem_integer_iff _).1 a.property _ hlt]
     have hn:i+1≠0:= by omega
     simp [a₀,LaurentSeries.algebraMap_apply,C_apply,hn]
   · simp [a₀,he,LaurentSeries.algebraMap_apply,C_apply]
 have he :a-a₀=τ*(⟨b,hb⟩:IntegerRing) := by
   apply Subtype.ext
   change (a :F)-(a₀:F)=uniformizer*b
   change _=uniformizer*((HahnSeries.single (-1) 1 :F)*_)
   rw [← mul_assoc,HahnSeries.single_mul_single]
   simp only [show (1 :ℤ) + -1=0 by decide,mul_one,HahnSeries.single_zero_one,one_mul]
 have hh:=congrArg ((residue V).comp (ringLift V f hV)) he
 simp only [map_sub,map_mul,RingHom.comp_apply,hτ,zero_mul] at hh
 exact sub_eq_zero.mp hh
end
theorem coeff_constant (D:Derivation ℤ F F) (hD:coefficientwise D)
   (a :constants D) :
   algebraMap SeedSeries F ((a :F).coeff 0)∈constants D:= by
 change D _=0
 apply HahnSeries.ext
 funext i
 rw [hD,HahnSeries.coeff_zero]
 have ha :D (a :F)=0:=a.property
 have h0:=hD (a :F) 0
 rw [ha,HahnSeries.coeff_zero] at h0
 by_cases hi:i=0
 · rw [hi]
   simpa [LaurentSeries.algebraMap_apply,C_apply] using h0.symm
 · simp [LaurentSeries.algebraMap_apply,C_apply,hi]
end
end qmgvT1d
end
section
set_option backward.isDefEq.respectTransparency false
namespace qmgvT1d
noncomputable section
open qps5rle qymFiQe IsLocalRing
open P5 (p)
attribute [local instance] char_F char_seed
private theorem seed_residue_not_mem (D:Derivation ℤ F F) (hD:coefficientwise D)
   (w:Roots) (hs :IsSeparable F w) (hd:Module.finrank F (Simple w)<p)
   (V:ValuationSubring (Simple w))
   (hV : ∀ a :IntegerRing,algebraMap F (Simple w) (a :F)∈V)
   (ht:algebraMap F (Simple w) uniformizer⁻¹∉V) :
   residue V (aih V (algebraMap F (Simple w)) hV (HahnSeries.single 1 1)) ∉
     restrictedResidue V (smallConstants D w) := by
 classical
 intro H
 obtain ⟨a,ha,hra⟩:=(mem_restrictedResidue _ _ _).1 H
 obtain ⟨b,⟨k,hk⟩,hb⟩:=short_relation D w hs hd ⟨a,ha⟩
 let f :=algebraMap F (Simple w)
 let z₀:SeedSeries :=HahnSeries.single 1 1
 let ρ:=(residue V).comp (aih V f hV)
 obtain ⟨j,_,hj⟩:=Finset.exists_max_image Finset.univ
   (fun i=>V.valuation (constantMap D w (b i))) ⟨k,Finset.mem_univ k⟩
 have hj0:b j≠0:= by
   intro H
   have h:=hj k (Finset.mem_univ k)
   rw [H,map_zero,map_zero] at h
   exact hk ((constantMap D w).injective
     ((V.valuation.zero_iff.mp (le_antisymm h zero_le)).trans (map_zero _).symm))
 obtain ⟨d,hdj,hdi,he⟩ :=
   normalize_row V (constantMap D w) b j hj0 (fun i=>hj i (Finset.mem_univ i))
 have H : (∑ i,constantMap D w (d i)*(a :Simple w)^(i:ℕ))=0:= by
   apply (mul_eq_zero.mp ((he (a :Simple w)).trans hb)).resolve_left
   exact (_root_.map_ne_zero (constantMap D w)).2 hj0
 let I (i:Fin p) :IntegerRing:=⟨(d i:F),mem_integer_of_nonunit V f hV ht (hdi i)⟩
 have Hr :=residue_sum V (fun i=>ringLift V f hV (I i)) a 0 H
 simp_rw [fWQ V f hV ht,hra,map_zero] at Hr
 have Hr' : ρ (∑ i,(d i:F).coeff 0*z₀^(i:ℕ))=ρ 0:= by
   rw [map_sum,map_zero]
   simp only [map_mul,map_pow,ρ,RingHom.comp_apply]
   exact Hr
 let e :SeedSeries →+* F:=algebraMap SeedSeries F
 let c (i:Fin p) :constants D:=⟨e ((d i:F).coeff 0),coeff_constant D hD (d i)⟩
 have hsum:=congrArg e (ρ.injective Hr')
 simp only [map_sum,map_mul,map_pow,map_zero] at hsum
 have hcj:c j≠0:= by
   intro hc
   have hh:e ((d j:F).coeff 0)=0:=congrArg Subtype.val hc
   rw [hdj] at hh
   have H : ((1 :F).coeff 0)=(1 :SeedSeries) := by
     rw [HahnSeries.coeff_one,ite_eq_left rfl]
   change e ((1 :F).coeff 0)=0 at hh
   rw [H,map_one] at hh
   exact one_ne_zero hh
 have hseed :seed∉constants D:= by
   intro H
   change D seed=0 at H
   rw [derive_seed hD] at H
   exact one_ne_zero H
 exact power_sum_ne prime_p (constants D) hseed (pow_constant D seed) c j hcj hsum
theorem proof :qymFiQe.c2 := by
 classical
 intro D hD w hs hd V hV c hc i
 let f :=algebraMap F (Simple w)
 have hV' (a :IntegerRing) :f (a :F)∈V:=hV a
 by_cases ht:f uniformizer⁻¹∈V
 · let:Algebra.IsSeparable F (Simple w) :=
     (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hs
   exact integral_mem V (contains_base V f hV' ht)
     (Algebra.IsSeparable.isSeparable F (c i:Simple w)).isIntegral
 let S:=smallConstants D w
 let z :=aih V f hV' (HahnSeries.single 1 1)
 let S₀:=restrictedResidue V S
 let:CharP (ResidueField V) p :=
   charP_of_injective_ringHom ((residue V).comp (aih V f hV')).injective p
 have hz :residue V z∉S₀:=seed_residue_not_mem D hD w hs hd V hV' ht
 have hzp:residue V z^p∈S₀:= by
   refine (mem_restrictedResidue _ _ _).2 ⟨z^p,?_,map_pow _ _ _⟩
   apply (show Subfield.closure (Set.range (fun a :Simple w=>a^p))≤S from le_sup_right)
   exact Subfield.subset_closure ⟨(z :Simple w),rfl⟩
 exact coefficients_mem prime_p V S z hz hzp c hc i
end
end qmgvT1d
end
section
namespace qMWkPHd
theorem proof :qCe4xzb.c2 :=
 qymFiQe.of_children qPfoxUd.proof qmgvT1d.proof 0
end qMWkPHd
end
section
set_option maxHeartbeats 600000
namespace qyUzJvd
noncomputable section
open Polynomial WithZero
open scoped Classical
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open qGnV2ac (Sections)
open qrKC9pb
open qqi5QRb (pointPrime pointVal)
open private detect_normal from ProximityPrize.SubmissionLower.ZjG08xb
open IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap)
def c1 :Prop :=
  ∀ (J:Input) (S:Sections J.F) (γ:K),γ∈S.CF →
    ∀ x :L,∃ r :Bool,Nonempty (MarkChart J S γ x r)
def c2 :Prop :=
 ∀ (J:Input) (r :Bool),Module.Finite (Chart J r) (Normal J r)
def c3:Prop :=
  ∀ (J:Input) (r :Bool),Module.Finite (Chart J r) (Normal J r) →
    ∀ (P:Ideal (Normal J r)),P.IsPrime→P.height = 1 →
      ∃ D:GraphPrime J r,
        (∀ a :Chart J r,
          D.val (a :EC J)<1↔algebraMap (Chart J r) (Normal J r) a∈P) ∧
        (∀ u:EC J,D.val u≤1↔NormalRegular J r P u)
private theorem detect (J:Input) (r :Bool) (hf :Module.Finite (Chart J r) (Normal J r))
   (M:Ideal (Chart J r)) [M.IsPrime] (b g:Chart J r) (hg:g≠0)
   (hu : ∀ a :Chart J r,a∉M →
     ¬ IsIntegral (Chart J r) ((a :EC J)*((b:EC J)/g))) :
   ∃ P:Ideal (Normal J r),P.IsPrime∧P.height = 1 ∧
     P.comap (algebraMap (Chart J r) (Normal J r))≤M ∧
     ¬ NormalRegular J r P ((b:EC J)/g) := by
 let:Algebra.FiniteType L (Chart J r) :=
   Algebra.FiniteType.adjoin_of_finite (Set.finite_range (aD J r))
 let:IsNoetherianRing (Chart J r) :=Algebra.FiniteType.isNoetherianRing L (Chart J r)
 exact detect_normal M _ hu ⟨g,fun e=>hg (Subtype.ext e),by
   change IsIntegral (Chart J r) ((g:EC J)*((b:EC J)/g))
   rw [mul_comm (g:EC J),div_mul_cancel₀ _ (show (g:EC J)≠0 from
     fun e=>hg (Subtype.ext e))]
   exact isIntegral_algebraMap (x :=b)⟩
variable {J:Input} {S:Sections J.F} {γ:K} {x :L} {r :Bool}
private def integerMap (T:MarkChart J S γ x r) :
  Chart J r →+* (pointVal x).valuationSubring :=
 T.map.toRingHom.codRestrict (pointVal x).valuationSubring.toSubring T.regular
private def markCenter (T:MarkChart J S γ x r) :Ideal (Chart J r) :=
 (IsLocalRing.maximalIdeal (pointVal x).valuationSubring).comap (integerMap T)
private instance (T:MarkChart J S γ x r) : (markCenter T).IsPrime := by
 unfold markCenter
 infer_instance
private theorem bsx (T:MarkChart J S γ x r) (a :Chart J r) :
   a∈markCenter T↔pointVal x (T.map a)<1 :=
 (pointVal x).mem_maximalIdeal_iff (a :=integerMap T a)
private theorem integral_specializes (T:MarkChart J S γ x r) (b g:Chart J r)
  (hg:T.map g≠0) (hint :IsIntegral (Chart J r) ((b:EC J)/g)) :
  pointVal x (T.map b/T.map g)≤1 := by
 let j:Chart J r →+* EC J:=algebraMap _ _
 have hj:Function.Injective j:=Subtype.val_injective
 have hg' : g≠0:= fun e=>hg (by simp [e])
 obtain ⟨f,hf,hzero⟩:=hint
 have hscaled:=scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero hj hzero
  (mem_nonZeroDivisors_iff_ne_zero.mpr hg')
 have he : (f.scaleRoots g).eval b=0:= by
  apply hj
  rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero]
  exact hscaled
 have hs :=congrArg T.map he
 change T.map.toRingHom ((f.scaleRoots g).eval b)= _ at hs
 rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero] at hs
 have hm:T.map g*(T.map b/T.map g)=T.map b:= by
  rw [← mul_div_assoc,mul_comm (T.map g),mul_div_cancel_right₀ _ hg]
 have hh:=scaleRoots_eval₂_mul (p:=f) T.map.toRingHom (T.map b/T.map g) g
 rw [show T.map.toRingHom g=T.map g from rfl,hm] at hh
 have hf' : f.eval₂ T.map.toRingHom (T.map b/T.map g)=0 :=
  (mul_eq_zero.mp (hh.symm.trans hs)).resolve_left (pow_ne_zero _ hg)
 apply ((Valuation.valuationSubring.integers (pointVal x)).isIntegral_iff_v_le_one).mp
 refine ⟨f.map (integerMap T),hf.map _,?_⟩
 rw [eval₂_map]
 exact hf'
private theorem val_poly_lt (x :L) (f :L[X]) :
  pointVal x (phys f)<1↔f.IsRoot x := by
 change (pointPrime x).valuation FX (algebraMap L[X] FX f)<1↔f.IsRoot x
 rw [(pointPrime x).valuation_lt_one_iff_mem,show (pointPrime x).asIdeal =
  Ideal.span {Polynomial.X - C x} from rfl,Ideal.mem_span_singleton,dvd_iff_isRoot]
private theorem exp_uniformizer_pow (m:ℕ) :exp (-1 :ℤ)^m=exp (-(m:ℤ)) := by
 rw [← exp_nsmul,smul_neg,nsmul_one]
private theorem val_uniformizer (x :L) :
  pointVal x (phys (Polynomial.X - C x))=exp (-1 :ℤ) := by
 change (pointPrime x).valuation FX (algebraMap L[X] FX _)= _
 rw [valuation_of_algebraMap]
 exact (pointPrime x).intValuation_singleton (X_sub_C_ne_zero x) rfl
private theorem val_poly (x :L) (f :L[X]) (hf :f≠0) :
  pointVal x (phys f)=exp (-(f.rootMultiplicity x :ℤ)) := by
 obtain ⟨q,he,hq⟩:=f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
 have hqv :pointVal x (phys q)=1 := by
  change (pointPrime x).valuation FX (algebraMap L[X] FX q)=1
  exact (pointPrime x).valuation_eq_one_iff_notMem.mpr (Ideal.mem_span_singleton.not.mpr hq)
 conv_lhs=>rw [he]
 rw [phys.map_mul,phys.map_pow,map_mul,map_pow,val_uniformizer,hqv,mul_one,
  exp_uniformizer_pow]
private theorem mark_phys (T:MarkChart J S γ x r) (y :L) :
  T.map (physDiff J r y)=phys (Polynomial.X - C y) := by
 rw [physDiff,map_sub,T.physical_eq,AlgHom.commutes,map_sub]
 rfl
private theorem b8N (T:MarkChart J S γ x r) (a :L) :
  T.map (seedDiff J r a)=phys (C (algebraMap K L (S.seed γ)-a)) := by
 rw [seedDiff,map_sub,T.seed_eq,AlgHom.commutes,← map_sub]
 exact IsScalarTower.algebraMap_apply L L[X] FX _
private theorem specialized_pole (T:MarkChart J S γ x r) (hγ:γ∈S.CF)
  (hx : (S.B γ).IsRoot x) {m:ℕ} (hm:m<(S.B γ).rootMultiplicity x) :
  1<pointVal x (T.map ((physDiff J r x)^m*num J r)/T.map (sep J r)) := by
 have hA : ¬ (S.A γ).IsRoot x := by
  intro hA
  obtain ⟨u,v,h⟩:=S.reduced γ hγ
  have q:=congrArg (fun f :L[X]=>f.eval x) h
  change (S.A γ).eval x=0 at hA
  change (S.B γ).eval x=0 at hx
  simp only [eval_add,eval_mul,hA,hx,mul_zero,add_zero,eval_one,zero_ne_one] at q
 obtain ⟨u,hu,he⟩:=T.gK6
 rw [map_mul,map_pow,mul_div_assoc,he,map_mul,map_pow,mark_phys,val_uniformizer,
  map_mul,hu,one_mul,map_div₀,val_poly x _ (S.nonzero γ hγ),
  val_poly x _ (S.pole_denominator γ hγ),rootMultiplicity_eq_zero hA,
  Nat.cast_zero,neg_zero,exp_zero,exp_uniformizer_pow,← mul_div_assoc,mul_one]
 apply (one_lt_div₀ exp_pos).2
 have hm' : (m:ℤ)<((S.B γ).rootMultiplicity x :ℤ) := by exact_mod_cast hm
 exact exp_lt_exp.mpr (neg_lt_neg hm')
private theorem small_value {v :ℤᵐ⁰} (h:v<1) :v≤exp (-1 :ℤ) := by
 apply (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
 simpa only [← exp_add,neg_add_cancel,exp_zero] using h
private theorem charge_order (D:GraphPrime J r) {m:ℕ}
    (hx :D.val (physDiff J r x :EC J)<1)
    (hp: (sep J r :EC J)≠0)
    (h:1<D.val (((physDiff J r x :EC J)^m)*variation J r)) :
    m<polarOrder D:= by
  by_contra! hle
  have hlog : -(m:ℤ)≤log (D.val (polar J r)) := by
    unfold polarOrder at hle
    omega
  have hp' : D.val (polar J r)≠0:=(D.val.ne_zero_iff).2 ((coe_sep J r ▸ hp))
  have hp'' := (le_log_iff_exp_le hp').mp hlog
  have hn:=chart_regular D (num J r)
  rw [gK6,← mul_div_assoc,map_div₀,map_mul,map_pow,coe_sep] at h
  have hbound :
      D.val (physDiff J r x :EC J)^m*D.val (num J r :EC J) ≤
        D.val (polar J r) := calc
    _≤D.val (physDiff J r x :EC J)^m:=mul_le_of_le_one_right' hn
    _≤exp (-1 :ℤ)^m:=pow_le_pow_left₀ zero_le (small_value hx) _
    _≤_:=exp_uniformizer_pow m ▸ hp''
  exact ((one_lt_div₀ (zero_lt_iff.mpr hp')).mp h).not_ge hbound
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :
   qrKC9pb.c3:= by
 intro J S Oj γ hγ x hx
 obtain ⟨r,⟨T⟩⟩:=h1 J S γ hγ x
 let M:=markCenter T
 let k :=(S.B γ).rootMultiplicity x
 let m:=k-1
 have hx' := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
 have hk :0<k :=(rootMultiplicity_pos (S.pole_denominator γ hγ)).mpr hx'
 let b:=(physDiff J r x)^m*num J r
 let u:EC J:=(b:EC J)/sep J r
 have hu:1<pointVal x (T.map b/T.map (sep J r)) :=
   specialized_pole T hγ hx' (by change k-1<k; omega)
 have hnon (a :Chart J r) (ha :a∉M) : ¬ IsIntegral (Chart J r) ((a :EC J)*u) := by
   intro hi
   have hval :pointVal x (T.map a)=1 :=
     le_antisymm (T.regular a) (le_of_not_gt (fun h=>ha ((bsx T a).mpr h)))
   have h' := integral_specializes T (a*b) (sep J r) T.simple
     (by simpa only [u,Subalgebra.coe_mul,mul_div_assoc] using hi)
   rw [map_mul,mul_div_assoc,map_mul,hval,one_mul] at h'
   exact hu.not_ge h'
 have hg:sep J r≠0:= fun e=>T.simple (e ▸ map_zero T.map)
 obtain ⟨P,hP,hht,hPM,hnonP⟩:=detect J r (h2 J r) M b (sep J r) hg hnon
 obtain ⟨D,hD,hreg⟩:=h3 J r (h2 J r) P hP hht
 have hlarge :1<D.val (((physDiff J r x :EC J)^m)*variation J r) := by
   have he :u=((physDiff J r x :EC J)^m)*variation J r := by
     simp only [u,b,Subalgebra.coe_mul,Subalgebra.coe_pow,gK6,mul_div_assoc]
   rw [← he]
   exact lt_of_not_ge (fun h=>hnonP ((hreg u).mp h))
 have hv :1<D.val (variation J r) := by
   refine hlarge.trans_le ?_
   rw [map_mul,map_pow]
   exact mul_le_of_le_one_left' (pow_le_one₀ zero_le (chart_regular D (physDiff J r x)))
 have hsep: (sep J r :EC J)≠0:= by
   intro h
   exact T.simple (by rw [show sep J r=0 from Subtype.ext h,map_zero])
 have hp:D.val (polar J r)<1 := by
   rw [gK6,map_div₀] at hv
   have hnz :=(D.val.ne_zero_iff).mpr hsep
   rw [← coe_sep]
   exact ((one_lt_div₀ (zero_lt_iff.mpr hnz)).mp hv).trans_le (chart_regular D (num J r))
 have hc (a :Chart J r) (ha :D.val (a :EC J)<1) :
     pointVal x (T.map a)<1 :=
   (bsx T a).mp (hPM ((hD a).mp ha))
 obtain ⟨a,ha⟩:=Oj r D hv
 have hza :=hc (seedDiff J r a) (by exact ha)
 rw [b8N,val_poly_lt,IsRoot.def,eval_C,sub_eq_zero] at hza
 rw [← hza] at ha
 obtain ⟨y,hy⟩:=physical_constant D S γ hγ ha hp
 have hxy :=hc (physDiff J r y) (by assumption)
 rw [mark_phys,val_poly_lt,IsRoot.def,eval_sub,eval_X,eval_C,sub_eq_zero] at hxy
 rw [← hxy] at hy
 have hm:=charge_order D (x :=x) (by assumption) hsep hlarge
 exact ⟨r,D,⟨ha,hy⟩,by change k≤polarOrder D; omega⟩
end
end qyUzJvd
end
