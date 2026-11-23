import ProximityPrize.SubmissionLower.ZPZNNwd
import ProximityPrize.SubmissionLower.ZEy78Hb
import ProximityPrize.SubmissionLower.Z3PNGOd
import ProximityPrize.SubmissionLower.ZJbAGBd
import Mathlib.RingTheory.PowerSeries.Expand
import ProximityPrize.SubmissionLower.ZKxCNpa
set_option Elab.async false
open _root_ renaming Field → zrb, Function.Injective → zq4, Int.natCast_nonneg → zbO, Nat.pos_of_ne_zero → zOl, Nat.sub_add_cancel → zxt, Polynomial.X → z7y, Polynomial.induction_on' → zCU, Polynomial.map_ne_zero_iff → zeI, PowerSeries → zpm, PowerSeries.coeff → z2o, PowerSeries.coeff_map → zVO
section
set_option backward.isDefEq.respectTransparency false
namespace qaUrXTd
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open qziIa4d (SeedSeries)
open qnyP9Da
private theorem eval_lift {A M:Type} [CommRing A] [zrb M] (F:Subfield M)
  (j:A →+* M) (h : ∀ a,j a∈F) (g:A[X]) (r :M) :
  aeval r (g.map (j.codRestrict F.toSubring h))=g.eval₂ j r := by
 rw [aeval_def,eval₂_map]
 rfl
private theorem aeval_pure {M:Type} [zrb M] (F:Subfield M)
  (q:ℕ) (r :M) (hr :r^q∈F) :
  aeval r ((z7y:F[X])^q - C (⟨r^q,hr⟩:F))=0:= by
 simp only [map_sub,map_pow,aeval_X,aeval_C]
 exact sub_self _
private theorem mem_of_root {A M:Type} [CommRing A] [zrb M] {q:ℕ} [CharP M q]
   (hq:q.Prime) (F:Subfield M) (j:A →+* M) (hj:zq4 j)
   (h : ∀ a,j a∈F) (g:A[X]) (hg:g≠0) (hd:g.natDegree<q)
   (r :M) (hr :r^q∈F) (hroot :g.eval₂ j r=0) :r∈F:= by
 let:Fact q.Prime :=⟨hq⟩
 by_contra hm
 let f :F[X] :=z7y ^q - C (⟨r^q,hr⟩:F)
 let u:=j.codRestrict F.toSubring h
 have hu:zq4 u:= fun _ _ h' => hj (congrArg Subtype.val h')
 have hrad:Irreducible f :=X_pow_sub_C_irreducible_of_prime hq (fun a h' => by
   have eq : (a :M)^q=r^q:=congrArg Subtype.val h'
   exact hm (frobenius_inj M q eq ▸ a.property))
 have hf :f=minpoly F r :=
   minpoly.eq_of_irreducible_of_monic hrad (aeval_pure F q r hr)
     (monic_X_pow_sub_C _ hq.ne_zero)
 have hzero :aeval r (g.map u)=0:=(eval_lift F j h g r).trans hroot
 have hb:=natDegree_le_of_dvd (minpoly.dvd F r hzero) (zeI hu |>.mpr hg)
 rw [← hf,natDegree_map_eq_of_injective hu g,show f.natDegree=q from
   natDegree_X_pow_sub_C] at hb
 exact (not_le_of_gt hd) hb
private theorem expand_in_adjoin {M:Type} [zrb M] {q:ℕ} (hq:q≠0)
  (F:Subfield M) (s :M) (hs :s^q∈F) (r :M)
  (hr :r∈seedField F s) :
  ∃ b:Fin q→F,r = ∑ i,(b i:M)*s^(i:ℕ) := by
 let f :F[X] :=z7y ^q - C (⟨s^q,hs⟩:F)
 have hf :f.Monic:=monic_X_pow_sub_C _ hq
 have hz :aeval s f=0:=aeval_pure F q s hs
 have ha :IsAlgebraic F s :=⟨f,hf.ne_zero,hz⟩
 have hm:r∈(seedField F s).toSubalgebra :=hr
 rw [show (seedField F s).toSubalgebra=Algebra.adjoin F {s} from
  IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic ha,
  Algebra.adjoin_singleton_eq_range_aeval] at hm
 obtain ⟨g,hg⟩:=hm
 have hd:f.natDegree=q:=natDegree_X_pow_sub_C
 have hf1 :f≠1 := fun e=>hq (hd.symm.trans (by simp [e]))
 have hqg: (g %ₘ f).natDegree<q:=hd ▸ natDegree_modByMonic_lt g hf hf1
 have hmod:aeval s (g %ₘ f)=r :=(aeval_modByMonic_eq_self_of_root hz).trans hg
 refine ⟨fun i=>(g %ₘ f).coeff i,?_⟩
 rw [← hmod,aeval_def,eval₂_eq_sum_range' _ hqg,Finset.sum_fin_eq_sum_range]
 exact Finset.sum_congr rfl fun i hi=> by rw [dite_eq_left (Finset.mem_range.mp hi)]; rfl
private theorem root_data {A M:Type} [zrb A] [zrb M] {q:ℕ} [CharP M q]
    (hq:q.Prime) (ι:A[X] →+* M) (hi:zq4 ι) (π:A)
    (d:A→A) (hexp:PowerExpansion q π d)
    (F:Subfield M) (hC : ∀ a :A,ι (C (a^q))∈F) (hX:ι z7y∈F)
    (G:A[X][X]) (r :M) (hG:G≠0) (hd:G.natDegree<q)
    (hroot :G.eval₂ ι r=0) :
    let T:=IntermediateField.adjoin F {r^q}
    FiniteDimensional F T∧Module.finrank F T≤G.natDegree ∧
      ∃ b:Fin q→T,r = ∑ i,(b i:M)*(ι (C π))^(i:ℕ) := by
  let:Fact q.Prime :=⟨hq⟩
  let T:=IntermediateField.adjoin F {r^q}
  let j:=(frobenius M q).comp ι
  have hj:zq4 j:= fun _ _ h=>hi (frobenius_inj M q h)
  have hmem : ∀ a,j a∈F:= by
    intro a
    induction a using zCU with
    | add a b ha hb=>rw [map_add]; exact F.add_mem ha hb
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
      exact F.mul_mem (by simpa only [j,RingHom.comp_apply,frobenius_def,map_pow] using hC a)
        (pow_mem (pow_mem hX q) n)
  let u:=j.codRestrict F.toSubring hmem
  have hu:zq4 u:= fun _ _ h=>hj (congrArg Subtype.val h)
  have haz :aeval (r^q) (G.map u)=0:= by
    rw [eval_lift F j hmem,← show frobenius M q r=r^q from rfl,
      ← hom_eval₂,hroot,map_zero]
  have ha :IsIntegral F (r^q) :=IsAlgebraic.isIntegral
    ⟨G.map u,(zeI hu).mpr hG,haz⟩
  have hdim:Module.finrank F T≤G.natDegree := by
    rw [IntermediateField.adjoin.finrank ha,← natDegree_map_eq_of_injective hu G]
    exact natDegree_le_of_dvd (minpoly.dvd F (r^q) haz) ((zeI hu).mpr hG)
  refine ⟨IntermediateField.adjoin.finiteDimensional ha,hdim,?_⟩
  let s :=ι (C π)
  let F' := T.toSubfield
  let E :=(seedField F' s).toSubfield
  have hsub (x :M) (hx :x∈F) :x∈F' := T.algebraMap_mem (⟨x,hx⟩:F)
  have hsub' (x :M) (hx :x∈F') :x∈E :=
    (seedField F' s).algebraMap_mem (⟨x,hx⟩:F')
  have hs :s∈E :=IntermediateField.mem_adjoin_simple_self F' s
  have hs' : s^q∈F' := hsub _ (by simpa only [s,map_pow] using hC π)
  have hC' (a :A) :ι (C a)∈E := by
    obtain ⟨b,hb,_⟩:=hexp a
    have he :ι (C a) = ∑ i,ι (C (b i^q))*s^(i:ℕ) := by
      rw [hb,map_sum,map_sum]
      simp only [map_mul,map_pow,s]
    rw [he]
    exact E.sum_mem fun i _=>E.mul_mem (hsub' _ (hsub _ (hC _))) (pow_mem hs _)
  have hE : ∀ a,ι a∈E := by
    intro a
    induction a using zCU with
    | add a b ha hb=>rw [map_add]; exact E.add_mem ha hb
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
      exact E.mul_mem (hC' a) (pow_mem (hsub' _ (hsub _ hX)) n)
  have hr :r^q∈F' := IntermediateField.mem_adjoin_simple_self F _
  exact expand_in_adjoin hq.ne_zero F' s hs' r
    (mem_of_root hq E ι hi hE G hG hd r (hsub' _ hr) hroot)
theorem roots :FrobeniusRootData := by
 intro h M _ ι hi G r hG hd hr
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP M p:=charP_of_injective_ringHom
  ((ι.comp C).comp (algebraMap L SeedSeries)).injective p
 exact root_data (show p.Prime from KoalaBear.is_prime) ι hi LX
  _ h.2 (frobBase ι) (fun a=>Subfield.subset_closure (Or.inl ⟨a,rfl⟩))
  (Subfield.subset_closure (Or.inr rfl)) G r hG hd hr
end
end qaUrXTd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qaUrXTd
noncomputable section
open HahnSeries
open P5 (K p)
open cu (L)
open qnyP9Da (PowerExpansion SeedExpansion LX)
private theorem coeff_of_powerSeries {A:Type} [zrb A] (f :zpm A)
   (n:ℤ) :
   (HahnSeries.ofPowerSeries ℤ A f).coeff n =
     if 0≤n then z2o n.toNat f else 0:= by
 split_ifs with h
 · lift n to ℕ using h
   simpa only [Int.toNat_natCast] using ofPowerSeries_apply_coeff f n
 · rw [ofPowerSeries_apply,embDomain_of_notMem_range]
   rintro ⟨k,hk⟩
   exact h (hk ▸ zbO k)
private theorem coeff_powerSeries_pow {A:Type} [zrb A] {q:ℕ} [Fact q.Prime] [CharP A q]
    (hq:q≠0) (f :zpm A) (n:ℤ) :
    (HahnSeries.ofPowerSeries ℤ A (f^q)).coeff n =
      if (q:ℤ)∣n then ((HahnSeries.ofPowerSeries ℤ A f).coeff (n/q))^q else 0:= by
  have hqz : (0:ℤ)<(q:ℤ) :=Int.natCast_pos.mpr (zOl hq)
  by_cases hn:0≤n
  · lift n to ℕ using hn
    simp only [Int.natCast_dvd_natCast,← Int.natCast_ediv,ofPowerSeries_apply_coeff,
      ← PowerSeries.map_frobenius_expand q hq,zVO,
      PowerSeries.coeff_expand]
    split_ifs <;> simp [frobenius_def,hq]
  · rw [coeff_of_powerSeries,ite_eq_right hn]
    split_ifs
    · rw [coeff_of_powerSeries,ite_eq_right (Int.ediv_neg_of_neg_of_pos (lt_of_not_ge hn) hqz).not_ge,
        zero_pow hq]
    · rfl
private theorem coeff_laurent_pow {A:Type} [zrb A] {q:ℕ} [Fact q.Prime] [CharP A q]
    (hq:q≠0) (a :LaurentSeries A) (n:ℤ) :
    (a^q).coeff n=if (q:ℤ)∣n then a.coeff (n/q)^q else 0:= by
  let f :=HahnSeries.ofPowerSeries ℤ A a.powerSeriesPart
  have ha :single a.order 1*f=a :=LaurentSeries.single_order_mul_powerSeriesPart a
  have hqz : (q:ℤ)≠0:=Int.natCast_ne_zero.mpr hq
  calc
    (a^q).coeff n=(f^q).coeff (n-(q:ℤ)*a.order) := by
      conv_lhs=>rw [← ha,mul_pow,single_pow,nsmul_eq_mul,one_pow,coeff_single_mul,one_mul]
    _ = _:= by
      rw [← map_pow,coeff_powerSeries_pow hq]
      have hd: (q:ℤ)∣n-(q:ℤ)*a.order↔(q:ℤ)∣n :=
        dvd_sub_left (dvd_mul_right _ _)
      simp only [hd]
      split_ifs <;> try rfl
      rw [mul_comm (q:ℤ) a.order,Int.sub_mul_ediv_right _ _ hqz]
      have h:=congrArg (fun z :LaurentSeries A=>z.coeff (n/(q:ℤ))) ha
      rw [coeff_single_mul,one_mul] at h
      rw [h]
private def sectionSeries {A:Type} [zrb A] {q:ℕ} [Fact q.Prime] [CharP A q]
  [PerfectRing A q] (a :LaurentSeries A) (i:Fin q) :LaurentSeries A :=
 HahnSeries.ofSuppBddBelow (fun n=>(frobeniusEquiv A q).symm (a.coeff ((q:ℤ)*n+(i:ℕ)))) (by
  refine ⟨a.order/(q:ℤ),fun n hn => ?_⟩
  by_contra! h
  have hq: (0:ℤ)<(q:ℤ) :=Int.natCast_pos.mpr (Fact.out:q.Prime).pos
  have h₁:=mul_le_mul_of_nonneg_left (show n+1≤a.order/(q:ℤ) by omega) hq.le
  have h₂:=Int.emod_add_mul_ediv a.order (q:ℤ)
  have h₃:=Int.emod_nonneg a.order hq.ne'
  have hi: (i:ℕ)<q:=i.isLt
  have hlt: (q:ℤ)*n+(i:ℕ)<a.order := by
    rw [mul_add,mul_one] at h₁
    omega
  exact hn (by simp [coeff_eq_zero_of_lt_order hlt]))
private theorem cLN {A:Type} [zrb A] {q:ℕ} [Fact q.Prime] [CharP A q]
    [PerfectRing A q] :
    PowerExpansion q (HahnSeries.single (1 :ℤ) (1 :A)) (LaurentSeries.derivative A) := by
  classical
  intro a
  let s :LaurentSeries A:=single 1 1
  let b:=sectionSeries (q:=q) a
  have hq:q≠0:=(Fact.out:q.Prime).ne_zero
  have hqz : (0:ℤ)<(q:ℤ) :=Int.natCast_pos.mpr (zOl hq)
  let j (n:ℤ) :Fin q :=
    ⟨(n % (q:ℤ)).toNat,by have :=Int.emod_lt_of_pos n hqz; omega⟩
  have hj (n:ℤ) : ((j n:ℕ) :ℤ)=n % (q:ℤ) :=Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have term (i:Fin q) (n:ℤ) :
      (b i^q*s^(i:ℕ)).coeff n=if j n=i then a.coeff n else 0:= by
    have hi: (0:ℤ)≤(i:ℕ) :=zbO _
    have hi' : ((i:ℕ) :ℤ)<(q:ℤ) :=Int.ofNat_lt.mpr i.isLt
    have hd: (q:ℤ)∣n-(i:ℕ)↔j n=i:= by
      rw [Int.dvd_iff_emod_eq_zero,← Int.emod_eq_emod_iff_emod_sub_eq_zero,
        Int.emod_eq_of_lt hi hi']
      constructor
      · intro h
        exact Fin.ext (Int.natCast_inj.mp ((hj n).trans h))
      · rintro rfl
        exact (hj n).symm
    rw [show s^(i:ℕ)=single ((i:ℕ) :ℤ) (1 :A) by
          simp [s,single_pow],coeff_mul_single,mul_one,coeff_laurent_pow hq]
    simp only [hd]
    split_ifs with he <;> try rfl
    have hc: (q:ℤ)*((n-(i:ℕ))/(q:ℤ))+(i:ℕ)=n:= by
      have e :=Int.emod_add_mul_ediv (n-(i:ℕ)) (q:ℤ)
      rw [(Int.dvd_iff_emod_eq_zero.mp (hd.mpr he)),zero_add] at e
      omega
    change ((frobeniusEquiv A q).symm (a.coeff _))^q= _
    rw [hc,frobeniusEquiv_symm_pow_p]
  have hsum:a = ∑ i,b i^q*s^(i:ℕ) := by
    apply HahnSeries.ext
    funext n
    rw [coeff_sum]
    simp only [term,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  refine ⟨b,hsum,?_⟩
  apply HahnSeries.ext
  funext n
  rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,Ring.choose_one_right,
    zsmul_eq_mul]
  change ((n+1 :ℤ) :A)*a.coeff (n+1)= _
  have hs' (k :ℕ) :s^k=single (k :ℤ) (1 :A) := by
    simp [s,single_pow]
  have dterm (i:Fin q) :
      (b i^q*(i:ℕ)*s^((i:ℕ)-1)).coeff n =
        ((i:ℕ) :A)*(b i^q*s^(i:ℕ)).coeff (n+1) := by
    by_cases h: (i:ℕ)=0
    · simp [h]
    rw [show b i^q*(i:ℕ)*s^((i:ℕ)-1) =
      (i:ℕ)•(b i^q*s^((i:ℕ)-1)) by rw [nsmul_eq_mul]; ac_rfl]
    rw [HahnSeries.coeff_nsmul,Pi.smul_apply,nsmul_eq_mul,hs',hs',
      coeff_mul_single,coeff_mul_single,mul_one,mul_one]
    have hi: (i:ℕ) - 1+1=(i:ℕ) :=zxt (zOl h)
    have he :n-(((i:ℕ) - 1 :ℕ) :ℤ)=n+1-(i:ℕ) := by omega
    rw [he]
  have hcast: ((n+1 :ℤ) :A)=((j (n+1) :ℕ) :A) := by
    have e :=Int.emod_add_mul_ediv (n+1) (q:ℤ)
    rw [← hj] at e
    have he :=congrArg (fun x :ℤ=>(x :A)) e
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,CharP.cast_eq_zero A q,
      zero_mul,add_zero] using he.symm
  rw [hcast,hsum,coeff_sum,coeff_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dterm,term]
  split_ifs with he
  · rw [he]
  · simp
theorem Kw:SeedExpansion := by
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:Fact p.Prime :=⟨KoalaBear.is_prime⟩
 refine ⟨?_,cLN⟩
 intro a h
 have h' := congrArg (fun b:LaurentSeries L=>b.coeff 1) h
 rw [coeff_laurent_pow (Fact.out:p.Prime).ne_zero,ite_eq_right,LX,coeff_single_same] at h'
 · exact zero_ne_one h'
 · exact fun hd=>(Fact.out:p.Prime).ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd))
end
end qaUrXTd
end
section
set_option autoImplicit true
namespace q3zqDZc
theorem proof :qnyP9Da.c1 :=qaUrXTd.Kw
end q3zqDZc
end
section
set_option autoImplicit true
namespace qJQ0Sxd
theorem proof :qnyP9Da.c2 :=
 qaUrXTd.roots
end qJQ0Sxd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qL2osVa
noncomputable section
open Finset Polynomial ProximityPrize.Benchmark
open P5 (K I p node)
open qAxtVye (wX branchDegree)
open quN7Z4a (physicalWeight)
open cu (L j9)
open DQ (DT)
open Cu (sQ)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (γ:K),γ∈C.smoothMarks→Nonempty (Arc C γ)
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (A:ArcFamily C) (m:ℕ),
    2≤C.g→C.g<p→m<p →
    2*C.g*physicalWeight C.D C.sheet.root.equation - C.g*C.g*C.D ≤ m →
    Nonempty (Branch C A m)
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (A:ArcFamily C) (m:ℕ) (B:Branch C A m),
    2≤C.g→C.g<p→m<p → ∀ γ∈B.keep,
    (A.variation γ).denom.natDegree≤B.DG γ ∧
    (A.variation γ).num.natDegree≤C.D + (A.variation γ).denom.natDegree
def c4 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (A:ArcFamily C) (m:ℕ) (B:Branch C A m),m<p →
    ∃ q:DT C.sheet.n,C.genericParam q≠0 ∧
      q.totalDegree≤2*C.g*(2*m-1) ∧
      ∀ γ∈B.keep,A.aiq γ q (B.DG γ)
def c5:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (A:ArcFamily C) (q:DT C.sheet.n) (V:Finset K) (v :K→ℕ),
    C.genericParam q≠0→(∀ γ∈V,A.aiq γ q (v γ)) →
    ∑ γ∈V,v γ≤q.totalDegree*C.H
def c6:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (q:Cut C.sheet.n) (u v :ℕ),MixedDegree q u v→C.bee q≠0 →
    (C.smoothMarks.filter fun γ=>C.markedCut γ q=0).card≤u*C₀.totalDegree+v*C.H
def c7:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (A:ArcFamily C) (x :L) (r :Target),2≤C.g→C.g<p →
    ∃ q₁ q₂:Cut C.sheet.n,
      MixedDegree q₁ ((2*C.g-1)*C.g*r.cost) (2*C.g-1) ∧
      MixedDegree q₂ (C.g*r.cost) 1∧C.bee q₁≠0∧C.bee q₂≠0 ∧
      ∀ γ∈C.smoothMarks,C.simple γ→ r.hit (C:=C) x γ →
        C.markedCut γ q₁≠0→C.markedCut γ q₂≠0 →
        ValueAt (A.variation γ) x (r.slope A γ)
private def bad {C₀:sQ} [Fact (Irreducible C₀)] {C:MarkedSheet C₀}
  (A:ArcFamily C) (U:Finset K) (x :L) (r :Target) :Finset K :=
 U.filter fun γ=>r.hit (C:=C) x γ ∧ ¬ ValueAt (A.variation γ) x (r.slope A γ)
private theorem bad_card (h6:c6) (h7:c7)
    {C₀:sQ} [Fact (Irreducible C₀)] {C:MarkedSheet C₀}
    (A:ArcFamily C) {U:Finset K} (hU:U⊆C.smoothMarks)
    (hs : ∀ γ∈U,C.simple γ) (hg:2≤C.g) (hp:C.g<p) (x :L) (r :Target) :
    (bad A U x r).card≤2*C.g*C.H+2*C.g*C.g*r.cost*C₀.totalDegree := by
  obtain ⟨q₁,q₂,hd₁,hd₂,hq₁,hq₂,hspec⟩:=h7 C₀ C A x r hg hp
  let cutZeros (q:Cut C.sheet.n) :=C.smoothMarks.filter fun γ=>C.markedCut γ q=0
  have hcov :bad A U x r⊆cutZeros q₁∪cutZeros q₂:= by
    intro γ hγ
    obtain ⟨hγU,hh,hfail⟩:=mem_filter.mp hγ
    by_cases h:C.markedCut γ q₁=0
    · exact mem_union_left _ (mem_filter.mpr ⟨hU hγU,h⟩)
    · by_cases h' : C.markedCut γ q₂=0
      · exact mem_union_right _ (mem_filter.mpr ⟨hU hγU,h'⟩)
      · exact (hfail (hspec γ (hU hγU) (hs γ hγU) hh h h')).elim
  have hsum:2*C.g-1+1=2*C.g:= by omega
  calc
    _≤(cutZeros q₁).card+(cutZeros q₂).card :=
      (card_le_card hcov).trans (card_union_le _ _)
    _≤((2*C.g-1)*C.g*r.cost)*C₀.totalDegree+(2*C.g-1)*C.H +
        (C.g*r.cost*C₀.totalDegree+1*C.H) :=
      Nat.add_le_add (h6 C₀ C q₁ _ _ hd₁ hq₁) (h6 C₀ C q₂ _ _ hd₂ hq₂)
    _ = _:= by
      conv_rhs=>rw [← hsum]
      ring
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) (h7:c7) :
    quN7Z4a.c1 := by
  classical
  intro b C₀ inst J T z s w g d H S _ hg hd hd0 hdp hm hlight hz W P
  let C:MarkedSheet C₀:=⟨J,T,z,s,g,H,wX b,S,hz,W.degree⟩
  let A:ArcFamily C:= fun γ=>Classical.choice (h1 C₀ C γ γ.property)
  have hgp:g<p:=(Nat.le_mul_of_pos_left g hd0).trans_lt hdp
  have hweight:2*g*physicalWeight (wX b) S.root.equation - g*g*wX b ≤
      branchDegree b g :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hlight.le) _
  obtain ⟨B⟩:=h2 C₀ C A (branchDegree b g) hg hgp hm hweight
  obtain ⟨q,hq,hqdeg,hqorder⟩:=h4 C₀ C A _ B hm
  have hexcess : ∑ γ∈B.keep,B.DG γ≤2*g*(2*branchDegree b g-1)*H :=
    (h5 C₀ C A q B.keep B.DG hq hqorder).trans (Nat.mul_le_mul_right _ hqdeg)
  let start (i:Fin 2) :=Target.projective i (P.a i) (P.b i) (P.c i)
  let fail (i:Fin 2) :=bad A B.keep (P.x i) (start i)
  let good:=B.keep \ (fail 0∪fail 1)
  have hfail (i:Fin 2) : (fail i).card≤2*g*H+2*g*g*d:= by
    have h:=bad_card h6 h7 A B.subset B.simple_at_mark hg hgp (P.x i) (start i)
    change (fail i).card≤2*g*H+2*g*g*1*C₀.totalDegree at h
    simpa only [hd,mul_one] using h
  have good_sub:good⊆B.keep:=sdiff_subset
  have excluded: (C.smoothMarks \ good).card≤(8+6*g)*H+4*g*g*d:= by
    have hcov :C.smoothMarks \ good⊆(C.smoothMarks \ B.keep)∪(fail 0∪fail 1) := by
      intro γ hγ
      obtain ⟨hγU,hγG⟩:=mem_sdiff.mp hγ
      by_cases hγB:γ∈B.keep
      · exact mem_union_right _ (by
          by_contra h
          exact hγG (mem_sdiff.mpr ⟨hγB,h⟩))
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hγU,hγB⟩)
    have h:=(card_le_card hcov).trans (card_union_le _ _)
    have h₁:=card_union_le (fail 0) (fail 1)
    have h₂: (C.smoothMarks \ B.keep).card≤2*g*H :=B.excluded
    have h₃:=hfail 0
    have h₄:=hfail 1
    have he :2*g*H+(2*g*H+2*g*g*d)+(2*g*H+2*g*g*d)+8*H =
        (8+6*g)*H+4*g*g*d:= by ring
    omega
  have nonzero (γ:K) (hγ:γ∈good) :A.variation γ≠0:= by
    have hγB:=good_sub hγ
    have hγU:=B.subset hγB
    have hγT:γ∈T:=(mem_filter.mp hγU).1
    obtain ⟨i,hi⟩:=(A ⟨γ,hγU⟩).zD
    have hjet:A.seedJet γ i≠0:= by
      simpa only [ArcFamily.seedJet,dite_eq_left hγU] using hi
    have hden:=P.den_ne γ hγT i
    have hhit : (start i).hit (C:=C) (P.x i) γ:=⟨hden,P.value γ hγT i⟩
    have hn:γ∉fail i:= by
      fin_cases i
      · exact fun h=>(mem_sdiff.mp hγ).2 (mem_union_left _ h)
      · exact fun h=>(mem_sdiff.mp hγ).2 (mem_union_right _ h)
    have hv :ValueAt (A.variation γ) (P.x i) ((start i).slope A γ) := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hγB,hhit,h⟩)
    have hsl: (start i).slope A γ≠0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero (P.a_ne i) (P.c_ne i)) hjet)
        (pow_ne_zero 2 hden)
    intro he
    have hn:=hv.2
    have hd:=hv.1
    rw [he] at hn hd
    rw [RatFunc.num_zero,eval_zero] at hn
    exact (mul_ne_zero hsl hd) hn.symm
  let x (i:I) :L:=algebraMap K L (node i)
  let Ju (γ:K) :=univ.filter fun i=>ValueAt (A.variation γ) (x i) 0
  let poles (γ:K) :=(A.variation γ).denom.natDegree
  refine ⟨⟨good,good_sub.trans B.subset,excluded,Ju,poles,?_,?_,?_⟩⟩
  · intro γ hγ
    refine (gR.kL.agd x
      ((algebraMap K L).injective.comp IRSProfile.domain.injective) (A.variation γ).num
      (RatFunc.num_ne_zero (nonzero γ hγ)) _ ?_).trans
        (h3 C₀ C A _ B hg hgp hm γ (good_sub hγ)).2
    intro i hi
    simpa only [zero_mul] using ((mem_filter.mp hi).2 :ValueAt _ _ _).2
  · calc
      _ ≤ ∑ γ∈good,B.DG γ :=
        sum_le_sum fun γ hγ=>(h3 C₀ C A _ B hg hgp hm γ (good_sub hγ)).1
      _ ≤ ∑ γ∈B.keep,B.DG γ:=sum_le_sum_of_subset_of_nonneg good_sub (by simp)
      _≤_:=hexcess
  · intro i
    have hcard:=bad_card h6 h7 A B.subset B.simple_at_mark hg hgp (x i)
      (.constant (algebraMap K L (w i)))
    refine (card_le_card (t:=bad A B.keep (x i) (.constant (algebraMap K L (w i)))) ?_).trans ?_
    · intro γ hγ
      obtain ⟨hγG,hhit,hmiss⟩:=mem_filter.mp hγ
      have he : (j9 (s γ)).eval (x i)=algebraMap K L ((s γ).eval (node i)) :=
        Polynomial.eval_map_apply (p:=s γ) (algebraMap K L) (node i)
      exact mem_filter.mpr ⟨good_sub hγG,he.trans (congrArg (algebraMap K L) hhit),
        fun hv=>hmiss (mem_filter.mpr ⟨mem_univ _,hv⟩)⟩
    · simpa only [Target.cost,mul_zero,zero_mul,add_zero] using hcard
end
end qL2osVa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qlbihNe
noncomputable section
open cu (L)
open P5 (K p)
open qqV3gre (aQ)
open scoped WithZero
abbrev seedSeries :zpm L:=PowerSeries.X
abbrev seedScalar :aQ:=algebraMap (zpm L) aQ seedSeries
theorem prime_p:p.Prime :=
 (CharP.char_is_prime_or_zero K p).resolve_right (by decide)
theorem seed_not_power (a :aQ) :a^p≠seedScalar := by
 let v :Valuation aQ ℤᵐ⁰:=Valued.v
 have hv :v seedScalar=WithZero.exp (-1 :ℤ) := by
  change Valued.v (algebraMap (zpm L) aQ PowerSeries.X)= _
  rw [LaurentSeries.coe_algebraMap]
  simpa only [pow_one,Nat.cast_one] using LaurentSeries.valuation_X_pow L 1
 intro h
 have he :=congrArg (fun a=>WithZero.log (v a)) h
 simp only [map_pow,hv,WithZero.log_pow,WithZero.log_exp,nsmul_eq_mul] at he
 have hd: (p:ℤ)∣(-1 :ℤ) :=⟨WithZero.log (v a),he.symm⟩
 have hd' : p∣1 := by simpa using Int.natAbs_dvd_natAbs.mpr hd
 exact (not_le_of_gt prime_p.one_lt) (Nat.le_of_dvd Nat.one_pos hd')
theorem series_expansion (a :zpm L) :
    ∃ b:Fin p→zpm L,a = ∑ i,b i^p*seedSeries^(i:ℕ) := by
  classical
  let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let:Fact p.Prime :=⟨prime_p⟩
  obtain ⟨b,hb⟩ : ∃ b:Fin p→ℕ→L,∀ i k,
      b i k^p=z2o (p*k+(i:ℕ)) a := by
    have h (i:Fin p) (k :ℕ) :=IsAlgClosed.exists_pow_nat_eq
      (z2o (p*k+(i:ℕ)) a) prime_p.pos
    choose b hb using h
    exact ⟨b,hb⟩
  refine ⟨fun i=>PowerSeries.mk (b i),PowerSeries.ext fun n => ?_⟩
  let r :Fin p:=⟨n % p,Nat.mod_lt _ prime_p.pos⟩
  have hr :p*(n/p)+(r :ℕ)=n:= by
    rw [add_comm]
    exact Nat.mod_add_div _ _
  have coeff_pow (i:Fin p) (k :ℕ) :
      z2o k ((PowerSeries.mk (b i))^p) =
        if p∣k then b i (k/p)^p else 0:= by
    rw [← PowerSeries.map_frobenius_expand (hp:=prime_p.ne_zero),
      zVO,PowerSeries.coeff_expand]
    split <;> simp [PowerSeries.coeff_mk,frobenius]
  rw [map_sum,Finset.sum_eq_single r]
  · rw [PowerSeries.coeff_mul_X_pow',ite_eq_left (by omega : (r :ℕ)≤n),coeff_pow,
      show n-(r :ℕ)=p*(n/p) by omega,ite_eq_left (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ prime_p.pos,hb,hr]
  · intro i _ hi
    rw [PowerSeries.coeff_mul_X_pow']
    split
    · rename_i hle
      rw [coeff_pow,ite_eq_right fun h=>hi (Fin.ext (by
        have hd:=Nat.mod_eq_zero_of_dvd h
        change (i:ℕ)=n % p
        rw [← zxt hle,Nat.add_mod,hd,zero_add,
          Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt i.isLt]))]
    · rfl
  · simp
end
end qlbihNe
end
