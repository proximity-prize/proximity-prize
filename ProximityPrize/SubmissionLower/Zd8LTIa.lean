import ProximityPrize.SubmissionLower.Zqop1Ec
set_option Elab.async false
section
namespace qps5rle
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna
open P5 (K p)
open cu (L)
open E7 (CurvePlace poleOrder KB)
open qb0hmCe (CurveModel SiteTarget.height)
open scoped Classical WithZero
def c2 :Prop :=
  ∀ {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C:CurveModel q}
    (S:Sheet B C),S.d<p → ∀ (R:SiteTarget) (T:SiteChart S R),
    let D:=initialAt R.center S.f.discr
    D ≠0 ∧
    (∑ᶠ v :CurvePlace L C.E,poleOrder v.value D)≤(2*S.d-2)*S.h ∧
    ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ→1≤(S.place γ).value D →
      (initialAt R.center (atArc (S.atPlace γ hγ) T.g).discr).coeff 0≠0
def c3:Prop :=
  ∀ (x :L) (f :SeedSeries[X][X]),0<f.natDegree→f.natDegree<p →
    leadAt x f≠0→f.discr≠0→tameDerivative x f
def c4 :Prop :=
  ∀ (x :L) (f :SeedSeries[X][X]),
    (∀ i j,vSeed ((f.coeff i).coeff j)≤1) →
    (leadAt x f).coeff 0≠0→(initialAt x f.discr).coeff 0≠0 →
    tameDerivative x f → ∀ A:SiteJet f x,finiteAt x A.delta
private theorem zero_count {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
    {C:CurveModel q} (S:Sheet B C) (e :C.E) (he :e≠0) :
    (S.marks.filter fun γ=>(S.place γ).value e<1).card ≤
      ∑ᶠ v :CurvePlace L C.E,poleOrder v.value e := by
  let F:=S.marks.filter fun γ=>(S.place γ).value e<1
  obtain ⟨_,hfin,heq,_⟩ :=
    aFU.of_children bRt.proof bRu.proof
      L C.E C.curve e
  have hone (v :CurvePlace L C.E) (hv :v∈F.image S.place) :
      1≤KB v.value e := by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hv
    have h:=(WithZero.log_lt_iff_lt_exp (a :=0)
      ((S.place γ).value.ne_zero_iff.mpr he)).mpr (by
        simpa only [WithZero.exp_zero] using (mem_filter.mp hγ).2)
    unfold KB
    omega
  have hsub:F.image S.place⊆hfin.toFinset :=
    fun v hv=>hfin.mem_toFinset.mpr (by simpa only [Function.mem_support] using
      (Nat.ne_of_gt (hone v hv)))
  rw [heq]
  calc
    F.card=(F.image S.place).card :=
      (card_image_of_injOn (S.distinct.mono (filter_subset _ _))).symm
    _ = ∑ _∈F.image S.place,(1 :ℕ) := by simp
    _ ≤ ∑ v∈F.image S.place,KB v.value e :=sum_le_sum hone
    _ ≤ ∑ v∈hfin.toFinset,KB v.value e :=sum_le_sum_of_subset hsub
    _ = ∑ᶠ v :CurvePlace L C.E,KB v.value e :=
      (finsum_eq_sum_of_support_subset _ (fun _ hv=>hfin.mem_toFinset.mpr hv)).symm
private theorem lead_nonzero {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] SeedSeries) (x :L) (f :E[X][X])
    (hint : ∀ i j,vSeed (((atArc a f).coeff i).coeff j)≤1)
    (hu:1≤vSeed (a (leadAt x f))) :
    (leadAt x (atArc a f)).coeff 0≠0:= by
  have hm:leadAt x (atArc a f)=a (leadAt x f) := by
    unfold leadAt atArc
    rw [leadingCoeff_map_of_injective (Polynomial.map_injective _ a.injective),coe_mapRingHom,
      eval_map,← a.commutes x]
    exact eval₂_hom a.toRingHom _
  have hr :vSeed (leadAt x (atArc a f))≤1 := by
    unfold leadAt
    rw [eval_eq_sum,Polynomial.sum]
    apply vSeed.map_sum_le
    intro j _
    rw [map_mul,map_pow]
    have hc:vSeed (algebraMap L SeedSeries x)≤1 := by
      rw [LaurentSeries.algebraMap_apply,← WithZero.exp_zero]
      apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mpr
      intro n hn
      simp [HahnSeries.C_apply,HahnSeries.coeff_single_of_ne (ne_of_lt hn)]
    exact (mul_le_mul_of_nonneg_right (hint _ _) bot_le).trans (by
      rw [one_mul]
      exact pow_le_one₀ bot_le hc)
  intro hz
  have hsmall:vSeed (leadAt x (atArc a f))≤WithZero.exp (-1 :ℤ) := by
    apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L).mpr
    intro n hn
    by_cases h:n=0
    · simpa only [h] using hz
    · apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mp
        (by simpa only [neg_zero,WithZero.exp_zero] using hr)
      omega
  have hbad:WithZero.exp (-1 :ℤ)<(1 :ℤᵐ⁰) := by
    exact WithZero.exp_lt_one_iff.mpr (by omega)
  exact (not_le_of_gt (hsmall.trans_lt hbad)) (hm.symm ▸ hu)
private theorem chart_budget (R:SiteTarget) (d h:ℕ) (q:SeedPlane) (hd:0<d) :
   (h+d*R.height q)+(2*d-2)*h≤ siteBudget R d h q:= by
 have hh:h+(2*d-2)*h=(2*d-1)*h:= by
   rw [show 2*d-1=1+(2*d-2) by omega,Nat.add_mul,Nat.one_mul]
 rw [add_right_comm,hh]
 by_cases hR:R.b=0∧R.d=0
 · simp [siteBudget,SiteTarget.height,hR]
 · rw [siteBudget,ite_eq_right hR,Nat.mul_add]
   exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
     (by simpa only [one_mul] using Nat.mul_le_mul_right (d*R.height q) (show 1≤2*d by omega))
end
end qps5rle
end
section
namespace qZu9hjc
noncomputable section
open Polynomial Finset
open P5 (K p)
open qe6nVeb (Input DualWord SeedPlane width weightOK poleRate)
open qE3Ebna (Sheet)
open qb0hmCe (CurveModel coeffHeight)
open cu (L)
open E7 (CurveField CurvePlace axV poleOrder KB Tq Gb)
open scoped Classical
def c1 :Prop :=
  ∀ {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C:CurveModel q}
    (S:Sheet B C) (a :ℕ),let s :=B.u₁-B.u₀
    2≤S.d→S.d*s≤a→HE S.f s a →
      Nonempty (Chart S s a)
def c2 :Prop :=
  ∀ {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C:CurveModel q}
    (S:Sheet B C) {s a :ℕ} (R:Chart S s a),2≤S.d→S.d<p→S.d*s≤a →
      discrDegree S.d a s<(p:ℤ) →
      ∃ T:Slice R.f s a,∀ γ∈S.marks,
        (R.den γ).natDegree≤valueZeros (S.place γ).value T.N
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E],CurveField L E →
    ∀ (f :E[X][X]) (s a :ℕ),2≤f.natDegree→f.natDegree<p →
      f.natDegree*s≤a→HE f s a → ∀ T:Slice f s a,
      Gb L E (valueCoeffs T.N)≤(valueDegree f.natDegree a s).toNat*coeffHeight f
private theorem sum_values {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (N :C.E[X]) :
   (∑ γ∈S.marks,valueZeros (S.place γ).value N)≤Gb L C.E (valueCoeffs N) := by
 let pord (v :CurvePlace L C.E) :=poleOrder v.value (N.coeff 0)
 let zord (v :CurvePlace L C.E) :=KB v.value (N.coeff 0)
 let w (v :CurvePlace L C.E) :=Tq v.value (valueCoeffs N)
 have hdiv :axV L C.E :=aFU.of_children
   bRt.proof bRu.proof L C.E C.curve
 obtain ⟨hp,hz,hEq,_⟩:=hdiv (N.coeff 0)
 have hw:=agN.b27 hdiv (valueCoeffs N)
 let T:=S.marks.image S.place
 let V:=T∪hw.toFinset∪hp.toFinset∪hz.toFinset
 have hsP:Function.support pord⊆(V:Set (CurvePlace L C.E)) := fun v hv =>
   mem_union_left _ (mem_union_right _ (hp.mem_toFinset.mpr hv))
 have hsZ:Function.support zord⊆(V:Set (CurvePlace L C.E)) := fun v hv =>
   mem_union_right _ (hz.mem_toFinset.mpr hv)
 have hsW:Function.support w⊆(V:Set (CurvePlace L C.E)) := fun v hv =>
   mem_union_left _ (mem_union_left _ (mem_union_right _ (hw.mem_toFinset.mpr hv)))
 have hTV:T⊆V:= fun v hv =>
   mem_union_left _ (mem_union_left _ (mem_union_left _ hv))
 have heq : ∑ v∈V,pord v = ∑ v∈V,zord v := by
   rw [← finsum_eq_sum_of_support_subset pord hsP,← finsum_eq_sum_of_support_subset zord hsZ]
   exact hEq
 have htot: (∑ v∈V,valueZeros v.value N)+(∑ v∈V,pord v) =
     (∑ v∈V,w v) + ∑ v∈V,zord v := by
   rw [← sum_add_distrib,← sum_add_distrib]
   refine sum_congr rfl fun v _ => ?_
   have hb:pord v≤w v :=Finset.le_sup (f := fun i=>poleOrder v.value (valueCoeffs N i))
     (mem_univ (⟨0,Nat.zero_lt_succ _⟩:Fin (N.natDegree+1)))
   change w v - pord v+zord v+pord v=w v+zord v
   omega
 calc
   _ = ∑ v∈T,valueZeros v.value N := by
     dsimp only [T]
     rw [sum_image]
     exact S.distinct
   _ ≤ ∑ v∈V,valueZeros v.value N :=sum_le_sum_of_subset hTV
   _ = ∑ v∈V,w v := by omega
   _ = _:=(finsum_eq_sum_of_support_subset w hsW).symm
private theorem tariffs {D d e u s W:ℕ} (hd:2≤d) (hde :d≤e)
    (hwidth :2*u+s=width D) (hw:weightOK D e W) :
    d*s≤W-d*u∧discrDegree d (W-d*u) s<(p:ℤ) ∧
      (valueDegree d (W-d*u) s).toNat≤poleRate D e W+(2*e-2) := by
  obtain ⟨_,he,_,hW,hD,hchar,hR⟩:=hw
  have hlow:=(Nat.mul_le_mul_right (width D) hde).trans hW
  have hu:d*u≤W:=(Nat.mul_le_mul_left d (show u≤width D by omega)).trans hlow
  have hL: (width D:ℤ)=2*(u:ℤ)+s := by exact_mod_cast hwidth.symm
  have ha : ((W-d*u:ℕ) :ℤ)=W-(d:ℤ)*u:= by rw [Nat.cast_sub hu,Nat.cast_mul]
  have hdeZ:0≤(e :ℤ)-d:=sub_nonneg.mpr (by exact_mod_cast hde)
  have hDZ:0≤(W:ℤ)-(d:ℤ)*width D:=sub_nonneg.mpr (by exact_mod_cast hlow)
  have hEZ:0≤(W:ℤ)-(e :ℤ)*width D:=sub_nonneg.mpr (by exact_mod_cast hW)
  have hx :0≤(width D:ℤ) :=Int.natCast_nonneg _
  have huZ:0≤(u:ℤ) :=Int.natCast_nonneg _
  have hdZ:0≤(d:ℤ) :=Int.natCast_nonneg _
  have hroom: (d:ℤ)*s≤((W-d*u:ℕ) :ℤ) := by
    apply sub_nonneg.mp
    calc
      _=(W-(d:ℤ)*width D)+(d:ℤ)*u:= by rw [ha,hL]; ring
      _≥0:=add_nonneg hDZ (mul_nonneg hdZ huZ)
  refine ⟨by exact_mod_cast hroom,?_,?_⟩
  · have hactual:discrDegree d (W-d*u) s=discrDegree d W (width D) := by
      unfold discrDegree
      rw [ha,hL]
      ring
    have hmono:discrDegree d W (width D)≤discrDegree e W (width D) := by
      apply sub_nonneg.mp
      calc
        _=((e :ℤ)-d)*(2*(W-(e :ℤ)*width D)+((e :ℤ)-d+1)*width D) := by
          unfold discrDegree
          ring
        _≥0:=mul_nonneg hdeZ
          (add_nonneg (mul_nonneg (by decide) hEZ)
            (mul_nonneg (add_nonneg hdeZ (by decide)) hx))
    have hcast: (↑((2*e-2)*W-e*(e-1)*width D) :ℤ)=discrDegree e W (width D) := by
      unfold discrDegree
      push_cast [Nat.cast_sub hD,Nat.cast_sub (show 2≤2*e by omega),
        Nat.cast_sub (show 1≤e by omega)]
      rfl
    rw [hactual]
    apply hmono.trans_lt
    rw [← hcast]
    exact_mod_cast hchar
  · have hactual:valueDegree d (W-d*u) s =
        valueDegree d W (width D)-(4*(d:ℤ)-4)*u:= by
      unfold valueDegree
      rw [ha,hL]
      ring
    have hmono:valueDegree d W (width D)≤valueDegree e W (width D) := by
      apply sub_nonneg.mp
      calc
        _=((e :ℤ)-d)*(6*(W-(e :ℤ)*width D)+(3*((e :ℤ)-d)+4)*width D+2) := by
          unfold valueDegree
          ring
        _≥0:=mul_nonneg hdeZ (add_nonneg
          (add_nonneg (mul_nonneg (by decide) hEZ)
            (mul_nonneg (add_nonneg (mul_nonneg (by decide) hdeZ) (by decide)) hx)) (by decide))
    have hcap:valueDegree d (W-d*u) s≤valueDegree e W (width D) := by
      rw [hactual]
      exact (sub_le_self _ (mul_nonneg (by omega) huZ)).trans hmono
    have heP:4*e≤3*e*e :=Nat.mul_le_mul_right e (by omega)
    have hcast: (↑(poleRate D e W+(2*e-2)) :ℤ)=valueDegree e W (width D) := by
      unfold poleRate valueDegree
      push_cast [Nat.cast_sub hR,Nat.cast_sub heP,
        Nat.cast_sub (show 2≤2*e by omega),Nat.cast_sub (show 4≤6*e by omega)]
      ring
    have h:=Int.toNat_le_toNat hcap
    simpa only [← hcast,Int.toNat_natCast] using h
theorem of_children (bY:c1) (compare :c2) (QI:c3) :qE3Ebna.c3:= by
 intro J U B q C S e W hd hde hw hb
 let s :=B.u₁-B.u₀
 let a :=W-S.d*B.u₀
 have hwidth :2*B.u₀+s=width J.D:= by
   have :=B.order
   have :=B.gMz
   dsimp only [s]
   omega
 obtain ⟨hroom,hguard,hcap⟩:=tariffs hd hde hwidth hw
 have hp:=hde.trans_lt hw.2.2.1
 have hwt:HE S.f s a := by
   intro i hi
   have h:=(hb i).resolve_left hi
   change (S.f.coeff i).natDegree+S.d*B.u₀+i*s≤W at h
   dsimp only [a]
   omega
 obtain ⟨R⟩:=bY S a hd hroom hwt
 obtain ⟨T,hT⟩:=compare S R hd hp hroom hguard
 have hN := QI C.curve R.f s a (R.degree.symm ▸ hd) (R.degree.symm ▸ hp)
   (R.degree.symm ▸ hroom) R.weight T
 rw [R.degree] at hN
 calc
   _ ≤ ∑ γ∈S.marks,valueZeros (S.place γ).value T.N :=
     sum_le_sum fun γ hγ=>(R.moved γ hγ).trans (hT γ hγ)
   _≤Gb L C.E (valueCoeffs T.N) :=sum_values S T.N
   _≤_:=hN.trans (Nat.mul_le_mul hcap R.height)
end
end qZu9hjc
end
