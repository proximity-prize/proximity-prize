import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import ProximityPrize.SubmissionLower.ZkEhKoc
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qlbihNe
noncomputable section
open Polynomial
open cu (L)
open P5 (K p)
open qqV3gre (aQ PhysicalField EC)
open qCtoYwb (tu Simple baseIn baseIn_injective)
section Span
variable {E :Type} [Field E] (q:ℕ) [ExpChar E q] (z t:E)
private abbrev kJ:=(frobenius E q).fieldRange
private def monomials :Fin q×Fin q→E :=
 fun ij=>z^(ij.2 :ℕ)*t^(ij.1 :ℕ)
private abbrev monomialSpan:Submodule (kJ (E :=E) q) E :=
 Submodule.span _ (Set.range (monomials q z t))
private theorem monomial_mem (i j:ℕ) :z^i*t^j∈monomialSpan q z t:= by
 have hq:=expChar_pos E q
 have hm:z^(i % q)*t^(j % q)∈monomialSpan q z t :=
  Submodule.subset_span ⟨(⟨j % q,Nat.mod_lt _ hq⟩,⟨i % q,Nat.mod_lt _ hq⟩),rfl⟩
 let b:kJ (E :=E) q :=
  ⟨(z^(i/q)*t^(j/q))^q,⟨_,rfl⟩⟩
 have h:=(monomialSpan q z t).smul_mem b hm
 change (z^(i/q)*t^(j/q))^q*(z^(i % q)*t^(j % q))∈_ at h
 rw [mul_pow,← pow_mul,← pow_mul,mul_mul_mul_comm,← pow_add,← pow_add,
  Nat.mul_comm (i/q) q,Nat.mul_comm (j/q) q,add_comm (q*(i/q)),
  add_comm (q*(j/q)),Nat.mod_add_div,Nat.mod_add_div] at h
 exact h
private abbrev monomialAdjoin:IntermediateField (kJ (E :=E) q) E :=
 IntermediateField.adjoin _ {z,t}
private abbrev monomialField:Subfield E :=(monomialAdjoin q z t).toSubfield
private theorem purely_of_powers (S:Subfield E) (h : ∀ a :E,a^q∈S) :
  IsPurelyInseparable S E := by
 let:ExpChar S q:=S.subtype.expChar S.subtype.injective q
 exact (isPurelyInseparable_iff_pow_mem S q).2 fun a =>
  ⟨1,⟨⟨a^q,h a⟩,by rw [pow_one]; rfl⟩⟩
private theorem expansion_of_mem {a :E} (ha :a∈monomialField q z t) :
   ∃ c:Fin q→Fin q→E,
     a = ∑ j,∑ i,c j i^q*z^(i:ℕ)*t^(j:ℕ) := by
 let:IsPurelyInseparable (kJ (E :=E) q) E :=purely_of_powers q _ (fun b=>⟨b,rfl⟩)
 change a∈(monomialAdjoin q z t).toSubalgebra.toSubmodule at ha
 rw [monomialAdjoin,IntermediateField.adjoin_toSubalgebra,Algebra.adjoin_eq_span] at ha
 have hspan:Submodule.span (kJ (E :=E) q) (Submonoid.closure ({z,t} : Set E) :Set E) ≤
     monomialSpan q z t:=Submodule.span_le.mpr fun u hu=> by
   obtain ⟨i,j,rfl⟩:=(Submonoid.mem_closure_pair z t u).mp hu
   exact monomial_mem q z t i j
 have ha :=hspan ha
 obtain ⟨b,hb⟩:=(Submodule.mem_span_range_iff_exists_fun (kJ (E :=E) q)).mp ha
 have h (ij:Fin q×Fin q) : ∃ c:E,c^q=(b ij:E) :=(b ij).property
 choose c hc using h
 refine ⟨fun j i=>c (j,i),hb.symm.trans ?_⟩
 rw [Fintype.sum_prod_type]
 refine Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _ => ?_
 change (b (j,i) :E)*(z^(i:ℕ)*t^(j:ℕ)) =
   c (j,i)^q*z^(i:ℕ)*t^(j:ℕ)
 rw [hc,mul_assoc]
end Span
private theorem bqo {R F E :Type} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field E]
  (S:Subfield E) (f :F →+* E) (h : ∀ r :R,f (algebraMap R F r)∈S) (a :F) :
  f a∈S:= by
 obtain ⟨r,s,-,rfl⟩:=IsFractionRing.div_surjective R a
 rw [map_div₀]
 exact S.div_mem (h r) (h s)
private theorem c4Q {R E :Type} [CommRing R] [Field E] (S:Subfield E)
   (f :R[X] →+* E) (hc : ∀ r :R,f (C r)∈S)
   (hx :f (Polynomial.X (R:=R))∈S) (a :R[X]) :f a∈S:= by
 induction a using Polynomial.induction_on' with
 | add u v hu hv=>simpa only [map_add] using S.add_mem hu hv
 | monomial n r =>
   rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
   exact S.mul_mem (hc r) (S.pow_mem hx n)
abbrev a8p (y :EC) :Simple y :=baseIn y (C seedScalar)
private theorem separable_of_root_derivative {F E :Type} [Field F] [Field E] [Algebra F E]
  (x :E) (Q:F[X]) (h:aeval x Q=0) (hd:aeval x Q.derivative≠0) :
  IsSeparable F x := by
 have hi:IsIntegral F x :=(isAlgebraic_iff_isIntegral.mp ⟨Q,fun hz=>hd (by simp [hz]),h⟩)
 change (minpoly F x).Separable
 apply (separable_iff_derivative_ne_zero (minpoly.irreducible hi)).2
 intro hzero
 obtain ⟨T,hT⟩:=minpoly.dvd F x h
 exact hd (by rw [hT,derivative_mul,hzero]; simp)
theorem cLN (π:tu) [Fact (Irreducible π)] (hπ:π.Separable) (y :EC)
    (hy :IsSeparable PhysicalField y) (w:Simple y) :
    ∃ c:Fin p→Fin p→Simple y,w =
      ∑ j,∑ i,c j i^p*a8p y ^(i:ℕ)*baseIn y π^(j:ℕ) := by
  let j:tu →+* Simple y :=baseIn y
  let m:aQ →+* Simple y :=j.comp C
  let k :K →+* aQ:=(algebraMap L aQ).comp (algebraMap K L)
  let:ExpChar PhysicalField p:=expChar_of_injective_ringHom
    (((algebraMap tu PhysicalField).comp C).comp k).injective p
  let:ExpChar (Simple y) p:=expChar_of_injective_ringHom (m.comp k).injective p
  let:Algebra.IsSeparable PhysicalField (Simple y) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hy
  let z :=a8p y
  let t:=j π
  let S:=monomialField p z t
  have hpow (a :Simple y) :a^p∈S :=
    (monomialAdjoin p z t).algebraMap_mem ⟨a^p,⟨a,rfl⟩⟩
  have hz :z∈S:=IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have ht:t∈S:=IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc (a :aQ) :m a∈S:= by
    apply bqo (R:=PowerSeries L) S m _ a
    intro b
    obtain ⟨c,he⟩:=series_expansion b
    let f :=m.comp (algebraMap (PowerSeries L) aQ)
    change f b∈S
    rw [he,map_sum]
    apply S.sum_mem
    intro i _
    rw [map_mul,map_pow,map_pow]
    exact S.mul_mem (hpow (f (c i))) (S.pow_mem hz _)
  let x :=j (Polynomial.X (R:=aQ))
  have hx :x∈S:= by
    let f :aQ →+* S:=m.codRestrict S hc
    let Q:S[X] :=π.map f - C ⟨t,ht⟩
    have hcomp: (algebraMap S (Simple y)).comp f=m:=rfl
    have he (g:tu) :g.eval₂ m x=j g:= by
      have heq :eval₂RingHom m x=j:= by
        apply Polynomial.ringHom_ext
        · intro b
          exact eval₂_C _ _
        · exact eval₂_X _ _
      exact DFunLike.congr_fun heq g
    have hQ:aeval x Q=0:= by
      simp only [Q,aeval_def,eval₂_sub,eval₂_map,hcomp,he,eval₂_C,sub_eq_zero]
      rfl
    have hd:aeval x Q.derivative≠0:= by
      simp only [Q,derivative_sub,derivative_C,sub_zero,derivative_map,aeval_def,
        eval₂_map,hcomp,he]
      exact (map_ne_zero_iff j (baseIn_injective y)).2
        ((separable_iff_derivative_ne_zero (Fact.out:Irreducible π)).1 hπ)
    let:IsPurelyInseparable S (Simple y) :=purely_of_powers p S hpow
    obtain ⟨b,hb⟩:=IsPurelyInseparable.inseparable S x (separable_of_root_derivative x Q hQ hd)
    exact hb ▸ b.property
  let I:=S.toIntermediateField (fun a=>bqo S (algebraMap PhysicalField (Simple y))
    (c4Q S j hc hx) a)
  have hi:IntermediateField.adjoin PhysicalField ((· ^ p) '' (Set.univ :Set (Simple y)))≤I:= by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨b,-,rfl⟩
    exact hpow b
  rw [← IntermediateField.adjoin_eq_adjoin_pow_expChar_of_isSeparable' PhysicalField (Simple y)
    Set.univ p,IntermediateField.adjoin_univ] at hi
  exact expansion_of_mem p z t (hi (show w ∈ ⊤ from trivial))
end
end qlbihNe
