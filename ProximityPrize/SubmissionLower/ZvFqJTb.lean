import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZQfUTPd
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qb2k8ya
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe q1kuFjb
open P5 (K p)
open cu (L FX)
open P5_7_7 (phys)
open qFD8jve (sheetPole polarResultant)
open qrezXJe (resultant_val_le sheet_bound bD9 cast_ne_zero)
open E7 (CurvePlace poleOrder)
open agN (b27)
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private efc adG cTA aMX from ProximityPrize.SubmissionLower.Y
open scoped Classical WithZero
private def CJ {R:Type} [CommRing R] (d:ℕ) (f :R[X]) :R :=
 f.resultant f.derivative d (d-1)
private theorem padded_map {R S:Type} [CommRing R] [CommRing S]
  (b:R →+* S) (d:ℕ) (f :R[X]) :CJ d (f.map b)=b (CJ d f) := by
 unfold CJ
 rw [Polynomial.derivative_map,Polynomial.resultant_map_map]
private theorem resultant_nonzero {E :Type} [Field E] [Algebra L E] {f :E[X][X]}
   (hi:Irreducible f) (hd:0<f.natDegree) (hp:f.natDegree<p) :
   polarResultant f≠0:= by
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let _:CharP E[X] p:=inferInstance
 let B:=FractionRing E[X]
 let b:E[X] →+* B:=algebraMap _ _
 let _:CharP B p:=charP_of_injective_ringHom (IsFractionRing.injective E[X] B) p
 have hdeg: (f.map b).natDegree=f.natDegree :=
   natDegree_map_eq_of_injective (IsFractionRing.injective E[X] B) _
 have hpos :0<(f.map b).natDegree :=hdeg.symm ▸ hd
 have hlt: (f.map b).natDegree<p:=hdeg.symm ▸ hp
 have hirr :Irreducible (f.map b) :=
   ((hi.isPrimitive hd.ne').irreducible_iff_irreducible_map_fraction_map (K:=B)).mp hi
 have hder : (f.map b).derivative≠0:= by
   intro hz
   have hc:=coeff_derivative (f.map b) ((f.map b).natDegree-1)
   rw [hz,coeff_zero,← Nat.cast_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel hpos,
     ← leadingCoeff] at hc
   exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero) (cast_ne_zero hpos hlt)) hc.symm
 have hres :=resultant_ne_zero _ _ ((separable_iff_derivative_ne_zero hirr).mpr hder)
 rw [bD9 hpos hlt,hdeg] at hres
 change CJ f.natDegree (f.map b)≠0 at hres
 rw [padded_map] at hres
 exact fun hz=>hres (by rw [show CJ f.natDegree f=polarResultant f from rfl,hz,map_zero])
private theorem coeff_resultant_bound {E :Type} [Field E] (w:Valuation E ℤᵐ⁰)
  {f :E[X][X]} (hd:0<f.natDegree) (j:ℕ) :
  w ((polarResultant f).coeff j)≤WithZero.exp (((2*f.natDegree-1)*sheetPole w f :ℕ) :ℤ) := by
 let d:=f.natDegree
 let b:=sheetPole w f
 let v :=efc w
 let u:ℤᵐ⁰:=WithZero.exp (b:ℤ)
 have hf (i:ℕ) :v (f.coeff i)≤u:=Finset.sup_le fun k _=>sheet_bound w f i k
 have hg (i:ℕ) :v (f.derivative.coeff i)≤u:= by
  rw [coeff_derivative,map_mul,← Nat.cast_succ,← C_eq_natCast]
  change _ *adG w (C ((i+1 :ℕ) :E))≤_
  rw [cTA]
  exact (mul_le_mul' (hf _) (cast_le_one (v :=w) (i+1))).trans_eq (mul_one _)
 refine (aMX w _ j).trans ((resultant_val_le v f f.derivative d (d-1) u hf hg).trans_eq ?_)
 rw [show d+(d-1)=2*d-1 by dsimp [d]; omega,← WithZero.exp_nsmul]
 simp [b,d]
private theorem pole_sum {q:Curve} {Cq:CurveModel q} {f :Cq.E[X][X]}
  {c:Cq.E} (hc:c≠0) {n:ℕ}
  (h : ∀ w:CurvePlace L Cq.E,w.value c≤WithZero.exp ((n*sheetPole w.value f :ℕ) :ℤ)) :
  (∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value c)≤n*coeffHeight f := by
 let P (w:CurvePlace L Cq.E) :=sheetPole w.value f
 have hf :P.HasFiniteSupport:=b27 (principal Cq) _
 change _≤n * ∑ᶠ w,P w
 rw [mul_finsum]
 apply finsum_le_finsum (principal Cq c).1
  (hf.subset fun w hw hz=>hw (by change n*P w=0; rw [hz,mul_zero]))
 intro w
 exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr hc)).mpr (h w))
private theorem reduced_degree {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] LaurentSeries L) {f :E[X][X]} (hn:headScalar f=1) :
    ((cLN a 0 f).map phys).natDegree=f.natDegree := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hz :f.coeff i=0:=coeff_eq_zero_of_natDegree_lt hi
    rw [coeff_map]
    suffices (cLN a 0 f).coeff i=0 by rw [this,map_zero]
    apply Polynomial.ext
    intro j
    simp only [expansion_coeff,hz,coeff_zero,map_zero,HahnSeries.coeff_zero]
  · apply le_natDegree_of_ne_zero
    rw [coeff_map]
    intro hz
    have he :=(map_eq_zero_iff phys (IsFractionRing.injective L[X] FX)).mp hz
    have hj: ((cLN a 0 f).coeff f.natDegree).coeff
        (f.coeff f.natDegree).natDegree=1 := by
      rw [expansion_coeff,coeff_natDegree,show (f.coeff f.natDegree).leadingCoeff=1 from hn,
        map_one]
      simp
    rw [he,coeff_zero] at hj
    exact zero_ne_one hj
private theorem bad_reduction {q:Curve} {Cq:CurveModel q} {s :Fin 2→L}
   (A:AtSite Cq s) {f :Cq.E[X][X]} (hd:0<f.natDegree) (hp:f.natDegree<p)
   (hn:headScalar f=1) (hf :coeffIntegral A.place.value f)
   (hs : ¬ ((cLN A.map 0 f).map phys).Separable) (j:ℕ) :
   A.place.value ((polarResultant f).coeff j)<1 := by
 let g:=Ua A.map f (fun i k=>A.value _ ▸ hf i k)
 let r :=cLN A.map 0 f
 let d:=f.natDegree
 have h₁:g.map (mapRingHom IntSeries.subtype)=f.map (mapRingHom A.map.toRingHom) :=
   map_liftAt _ _ _
 have h₂:g.map (mapRingHom residue)=r :=liftAt_reduce _ _ _
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP L[X] p:=inferInstance
 let _:CharP FX p:=charP_of_injective_ringHom (IsFractionRing.injective L[X] FX) p
 have hdeg: (r.map phys).natDegree=d:=reduced_degree A.map hn
 have hpos :0<(r.map phys).natDegree :=hdeg.symm ▸ hd
 have hlt: (r.map phys).natDegree<p:=hdeg.symm ▸ hp
 have hz : (r.map phys).resultant (r.map phys).derivative=0 :=
   resultant_eq_zero_iff.mpr ⟨Or.inl (ne_zero_of_natDegree_gt hpos),hs⟩
 rw [bD9 hpos hlt,hdeg] at hz
 change CJ d (r.map phys)=0 at hz
 rw [padded_map] at hz
 have hr :CJ d r=0:=(map_eq_zero_iff phys (IsFractionRing.injective L[X] FX)).mp hz
 have hsub: (CJ d g).map IntSeries.subtype=(polarResultant f).map A.map.toRingHom:= by
   change mapRingHom IntSeries.subtype (CJ d g)=mapRingHom A.map.toRingHom (CJ d f)
   rw [← padded_map,h₁,padded_map]
 have hred: (CJ d g).map residue=0:= by
   change mapRingHom residue (CJ d g)=0
   rw [← padded_map,h₂,hr]
 let u:=(CJ d g).coeff j
 have hu: (u:LaurentSeries L)=A.map ((polarResultant f).coeff j) := by
   change ((CJ d g).coeff j:LaurentSeries L)=A.map.toRingHom ((polarResultant f).coeff j)
   simpa only [coeff_map,Subring.subtype_apply] using
     congrArg (fun t: (LaurentSeries L)[X]=>t.coeff j) hsub
 have hv :residue u=0:= by
   simpa only [coeff_map,coeff_zero] using congrArg (fun t:L[X]=>t.coeff j) hred
 obtain ⟨t,ht⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective u
 have ht' : (u:LaurentSeries L)=(t:LaurentSeries L) := by
   rw [← ht,LaurentSeries.powerSeriesEquivSubring_coe_apply]
 have hsmall:=(small_valuation t).mpr
   ((power_residue _ t ht').symm.trans ((fWQ u).symm.trans hv))
 rw [A.value,← hu,ht']
 exact hsmall.trans_lt (WithZero.exp_lt_one_iff.mpr (by decide))
theorem proof :q1kuFjb.c4 := by
  intro q Cq ι I s A hv f hi hd hp hn
  let j:=(polarResultant f).natDegree
  have hj: (polarResultant f).coeff j≠0:=leadingCoeff_ne_zero.mpr (resultant_nonzero hi hd hp)
  let v := fun i=>(A i).place
  let c:=(polarResultant f).coeff j
  let poles :=I.filter fun i => ¬ coeffIntegral (v i).value f
  let Ju:=I.filter fun i=>(v i).value c<1
  have hcover : (I.filter fun i => ¬ (coeffIntegral (v i).value f ∧
      ((cLN (A i).map 0 f).map phys).Separable))⊆poles∪Ju:= by
    intro i h
    obtain ⟨hI,hb⟩:=mem_filter.mp h
    by_cases hf :coeffIntegral (v i).value f
    · exact mem_union_right _ (mem_filter.mpr
        ⟨hI,bad_reduction (A i) hd hp hn hf (fun hs=>hb ⟨hf,hs⟩) j⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hI,hf⟩)
  have hP:poles.card≤ coeffHeight f :=integral_budget I v hv f
  have hZ:Ju.card≤(2*f.natDegree-1)*coeffHeight f :=
    (zero_budget I v hv hj).trans (pole_sum (f :=f) hj (fun w=>coeff_resultant_bound w.value hd j))
  calc
    _≤(poles∪Ju).card:=card_le_card hcover
    _≤poles.card+Ju.card:=card_union_le _ _
    _≤ coeffHeight f+(2*f.natDegree-1)*coeffHeight f :=Nat.add_le_add hP hZ
    _=(1+(2*f.natDegree-1))*coeffHeight f := by rw [Nat.add_mul,one_mul]
    _=2*f.natDegree*coeffHeight f := by
      rw [show 1+(2*f.natDegree-1)=2*f.natDegree by omega]
end
end qb2k8ya
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qbnx7gb
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe
open P5 (K)
open P5_7_1 (Input)


open qwGrtCa (form transform transform_sum)
private theorem top {R:Type} [CommRing R] (a b d:R) (n:ℕ) (f :R[X])
    (hf :f.natDegree≤n) :
    (transform a b 1 d n f).natDegree≤n∧(transform a b 1 d n f).coeff n=f.eval a := by
  have hl (a b:R) : (form a b).natDegree≤1 :=
    (natDegree_add_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have hc (a b:R) : (form a b).coeff 1=a := by simp [form,coeff_C]
  have hp (a b:R) (i:ℕ) : (form a b^i).natDegree≤ i:= by
    simpa only [mul_one] using natDegree_pow_le_of_le i (hl a b)
  have he (a b:R) (i:ℕ) : (form a b^i).coeff i=a^i:= by
    induction i with
    | zero=>simp
    | succ i ih =>
      rw [pow_succ,coeff_mul_add_eq_of_natDegree_le (hp a b _) (hl a b),
        ih,hc,pow_succ]
  rw [transform_sum]
  constructor
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hh:i≤n:=Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le.trans ((Nat.add_le_add (hp a b i) (hp 1 d (n-i))).trans_eq
        (Nat.add_sub_of_le hh)))
  · rw [finsetSum_coeff,eval_eq_sum_range' (Nat.lt_succ_of_le hf)]
    apply sum_congr rfl
    intro i hi
    have hh:i≤n:=Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [mul_assoc,coeff_C_mul]
    congr 1
    calc
      _=(form a b^i*form 1 d^(n-i)).coeff (i+(n-i)) := by rw [Nat.add_sub_of_le hh]
      _ = _:= by
        rw [coeff_mul_add_eq_of_natDegree_le (hp a b i) (hp 1 d (n-i)),he,he,one_pow,mul_one]
variable {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C₀:CurveModel q}
end
end qbnx7gb
end
