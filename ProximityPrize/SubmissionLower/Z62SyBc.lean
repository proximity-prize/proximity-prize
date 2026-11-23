import ProximityPrize.SubmissionLower.ZbbSEle
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Finset.sum_eq_single → zi6, Polynomial.ext → zXJ, Polynomial.finsetSum_coeff → zaW, Polynomial.map_map → zoi, Polynomial.sum_def → zBJ, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, PowerSeries.constantCoeff → zbO
section
namespace q1kuFjb
noncomputable section
open Polynomial qQ9yWTb qb0hmCe


open P5_7_7 (phys)
open cu (L FX)
open scoped Classical WithZero
abbrev IntSeries :=LaurentSeries.powerSeries_as_subring L
def residue :IntSeries →+* L :=
 PowerSeries.constantCoeff.comp (LaurentSeries.powerSeriesEquivSubring L).symm.toRingHom
@[simp] theorem fWQ (c:IntSeries) :
   residue c=(c:LaurentSeries L).coeff 0:= by
  obtain ⟨g,rfl⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective c
  change zbO ((LaurentSeries.powerSeriesEquivSubring L).symm
   (LaurentSeries.powerSeriesEquivSubring L g))= _
  rw [RingEquiv.symm_apply_apply,LaurentSeries.powerSeriesEquivSubring_coe_apply]
  simpa only [Nat.cast_zero,zW1] using
   (LaurentSeries.coeff_coe_powerSeries g 0).symm
def integralSeries (c:LaurentSeries L)
    (h: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) c≤1) :IntSeries :=
  ⟨c,by
    obtain ⟨g,hg⟩:=(LaurentSeries.val_le_one_iff_eq_coe L c).mp h
    exact Subring.mem_map.mpr ⟨g,trivial,hg⟩⟩
theorem power_residue (c:LaurentSeries L) (g:PowerSeries L)
  (h:c=(g:LaurentSeries L)) :
  c.coeff 0=zbO g:= by
 rw [h]
 simpa only [Nat.cast_zero,zW1] using
  LaurentSeries.coeff_coe_powerSeries g 0
theorem small_valuation (u:PowerSeries L) :
  (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (u:LaurentSeries L)≤WithZero.exp (-1) ↔
    zbO u=0:= by
 simpa [Nat.lt_one_iff] using (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L (d:=1) u)
private theorem sum_coeff {R S:Type} [Semiring R] [Semiring S] (b:R→S)
   (hb:b 0=0) (f :R[X]) (i:ℕ) :
   (f.sum fun j c=>monomial j (b c)).coeff i=b (f.coeff i) := by
 simp only [zBJ,zaW,coeff_monomial]
 rw [zi6 i]
 · simp
 · intro j _ hj
   simp [hj]
 · intro hi
   simp [notMem_support_iff.mp hi,hb]
theorem expansion_coeff {E :Type} [zrb E] [zZE L E]
  (a :E →ₐ[L] LaurentSeries L) (k :ℤ) (f :E[X][X]) (i j:ℕ) :
  ((cLN a k f).coeff i).coeff j=(a ((f.coeff i).coeff j)).coeff k := by
 unfold cLN
 rw [sum_coeff _ (by simp [zBJ])]
 exact sum_coeff _ (by simp) _ _
private def j9 (f : (LaurentSeries L)[X])
   (h : ∀ j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (f.coeff j)≤1) :
   IntSeries[X] :=
 ∑ j∈f.support,monomial j (integralSeries (f.coeff j) (h j))
@[simp] private theorem coeff_liftPoly (f : (LaurentSeries L)[X]) (h) (j:ℕ) :
    (j9 f h).coeff j=integralSeries (f.coeff j) (h j) := by
  rw [j9,zaW,zi6 j]
  · rw [coeff_monomial_same]
  · intro b _ hb
    rw [coeff_monomial_of_ne _ (Ne.symm hb)]
  · intro hj
    rw [coeff_monomial_same]
    apply Subtype.ext
    exact notMem_support_iff.mp hj
def Ua {E :Type} [zrb E] [zZE L E] (a :E →ₐ[L] LaurentSeries L)
    (f :E[X][X])
    (h : ∀ i j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a ((f.coeff i).coeff j))≤1) :
    IntSeries[X][X] :=
  ∑ i∈f.support,monomial i (j9 ((f.coeff i).map a.toRingHom) (by
    intro j
    rw [coeff_map]
    exact h i j))
@[simp] theorem coeff_liftAt {E :Type} [zrb E] [zZE L E]
    (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (h) (i j:ℕ) :
    ((((Ua a f h).coeff i).coeff j:IntSeries) :LaurentSeries L) =
      a ((f.coeff i).coeff j) := by
  rw [Ua,zaW,zi6 i]
  · simp only [coeff_monomial_same,coeff_liftPoly,integralSeries,coeff_map,
      AlgHom.toRingHom_eq_coe]
    rfl
  · intro b _ hb
    rw [coeff_monomial_of_ne _ (Ne.symm hb)]
  · intro hi
    rw [coeff_monomial_same]
    apply zXJ
    intro j
    apply Subtype.ext
    simp [notMem_support_iff.mp hi,integralSeries]
theorem liftAt_reduce {E :Type} [zrb E] [zZE L E]
  (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (h) :
  (Ua a f h).map (mapRingHom residue)=cLN a 0 f := by
 apply zXJ
 intro i
 apply zXJ
 intro j
 simp only [coeff_map,coe_mapRingHom,fWQ,coeff_liftAt,expansion_coeff]
def mapTwice {E E' : Type} [za6 E] [za6 E'] (b:E →+* E') :
    E[X][X] →+* E'[X][X] :=mapRingHom (mapRingHom b)
theorem mapTwice_restrict {E E' : Type} [za6 E] [za6 E']
   (b:L →+* E) (z :Fin 2→E) (m:E →+* E') (F:Raw) :
   mapTwice m (restrictOver b z F)=restrictOver (m.comp b) (m ∘ z) F:= by
 unfold restrictOver mapTwice
 simp only [coe_mapRingHom,zoi,MvPolynomial.comp_eval₂Hom]
 refine congrArg (fun f=>F.map f) ?_
 apply MvPolynomial.ringHom_ext
 · intro r
   simp only [MvPolynomial.eval₂Hom_C,RingHom.comp_apply,coe_mapRingHom,zoi]
 · intro i
   simp only [MvPolynomial.eval₂Hom_X',Function.comp_apply,map_C]
theorem reduced_pair (t:FX) :
   ∃ a b:L[X],b≠0∧IsCoprime a b∧phys a/phys b=t :=
 ⟨IsFractionRing.num L[X] t,IsFractionRing.den L[X] t,
   mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den L[X] t).2,
   (IsFractionRing.num_den_reduced L[X] t).isCoprime,IsFractionRing.mk'_num_den' L[X] t⟩
end
end q1kuFjb
end
section
namespace qFD8jve
noncomputable section
open Polynomial Finset
open scoped WithZero
variable {E :Type} [zrb E] {v :Valuation E ℤᵐ⁰}
private def Bounded (g:E[X]) (c:ℤᵐ⁰) :Prop := ∀ i,v (g.coeff i)≤ c
private theorem afg {g h:E[X]} {a b:ℤᵐ⁰}
  (hg:Bounded (v :=v) g a) (hh:Bounded (v :=v) h b) :
  Bounded (v :=v) (g*h) (a*b) := by
 intro i
 rw [coeff_mul]
 exact v.map_sum_le fun j _=> by
  rw [map_mul]
  exact mul_le_mul' (hg j.1) (hh j.2)
private theorem bmr {ι:Type} {g:ι→E[X]} {c:ℤᵐ⁰} (s :Finset ι)
   (h : ∀ j∈s,Bounded (v :=v) (g j) c) :
   Bounded (v :=v) (∏ j∈s,g j) (c^s.card) := by
 classical
 induction s using Finset.induction_on with
 | empty=>intro i; by_cases hi:i=0 <;> simp [hi,coeff_one]
 | insert j s hj ih =>
   rw [prod_insert hj,card_insert_of_notMem hj,pow_succ']
   exact afg (h j (mem_insert_self _ _)) (ih fun k hk=>h k (mem_insert_of_mem hk))
private theorem cast_le_one (n:ℕ) :v (n:E)≤1 := by
 induction n with
 | zero=>simp
 | succ n ih=>rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)
theorem guard_le {F:E[X][X]} {b:ℕ} (hd:0<F.natDegree)
    (h:aFA v F b) :v (guard F)≤WithZero.exp ((2*F.natDegree*b:ℕ) :ℤ) := by
  classical
  let d:=F.natDegree
  let c:ℤᵐ⁰:=WithZero.exp (b:ℤ)
  let M:=sylvester F F.derivative d (d-1)
  have he (i j:Fin (d+(d-1))) :Bounded (v :=v) (M i j) c:= by
    intro k
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
      split
      · rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast,
          coeff_mul_C,map_mul]
        simpa using mul_le_mul' (h ((i:ℕ)-(a :ℕ)+1) k)
          (cast_le_one (v :=v) ((i:ℕ)-(a :ℕ)+1))
      · simp
    · intro a
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
      split
      · exact h _ k
      · simp
  have hM:Bounded (v :=v) M.det (c^(d+(d-1))) := by
    intro k
    rw [Matrix.det_apply,finsetSum_coeff]
    apply v.map_sum_le
    intro π _
    have hπ:=bmr (v :=v) univ (fun j _=>he (π j) j) k
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;>
      simpa [hs,Valuation.map_neg] using hπ
  have hr :=hM (polarResultant F).natTrailingDegree
  have hz :v ((aaD F).trailingCoeff)≤ c:= by
    simpa only [trailingCoeff,aaD,coeff_map,coe_evalRingHom,← coeff_zero_eq_eval_zero] using
      h (aaD F).natTrailingDegree 0
  rw [guard,map_mul]
  calc
    _≤ c^(d+(d-1))*c:=mul_le_mul' hr hz
    _ = _:= by
      rw [← pow_succ,show d+(d-1)+1=2*d by dsimp [d]; omega]
      simp [c,d,← WithZero.exp_nsmul]
end
end qFD8jve
end
section
namespace qypA4Sc
noncomputable section
open Polynomial qNu3xvc
open cu (L)
open scoped WithZero
variable {E :Type} [zrb E] [zZE L E]
def ajm (A:Equation E) :E[X] →+* EC A:=(a7W A).comp C
def Horizontal {A:Equation E} {r :Bool} (v :GraphVal A r) :Prop :=
 ∀ c,c≠0→v.val (seed A c)=1
def a8p {A:Equation E} {r :Bool} (v :GraphVal A r) (h:Horizontal v) :
    E →+* v.val.valuationSubring :=
  (seed A).codRestrict v.val.valuationSubring.toSubring fun c=> by
    by_cases hc:c=0
    · simp [hc]
    · exact (h c hc).le
def SeparableResidue {F:Type} [zrb F] {v :Valuation F ℤᵐ⁰}
    (i:E →+* v.valuationSubring) :Prop :=
  letI:zZE E (IsLocalRing.ResidueField v.valuationSubring) :=
    ((IsLocalRing.residue _).comp i).toAlgebra
  zw7 E (IsLocalRing.ResidueField v.valuationSubring)
end
end qypA4Sc
end
section
namespace P5_7_1_7_4_3_4
noncomputable section
open Polynomial qNu3xvc
open qFD8jve (aFA sheetPole)
open cu (L)
open scoped WithZero
variable {E :Type} [zrb E] [zZE L E]
def gauge (A:Equation E) (l:L) :EC A :=
 1+constant A l*jU A false
def PencilBound (A:Equation E) (g:E[X][X]) :Prop :=
  g.natDegree≤A.d ∧
    ∀ i,(g.coeff i).natDegree+i*A.s≤A.b+A.d*A.s+A.s+1∨g.coeff i=0
structure Pencil (A:Equation E) where
 num :E[X][X]
 den:E[X][X]
 tilt:L
 num_weight:PencilBound A num
 den_weight:PencilBound A den
 num_height : ∀ w:E7.CurvePlace L E,
  aFA w.value num (sheetPole w.value A.f)
 den_height : ∀ w:E7.CurvePlace L E,
  aFA w.value den (sheetPole w.value A.f)
 den_ne :KM A false den≠0
 gauge_ne :gauge A tilt≠0
 polar_ne :polar A false≠0
 base :RatFunc E →+* EC A
 base_seed : ∀ c,base (RatFunc.C c)=seed A c
 base_X:base RatFunc.X=KM A false num/ KM A false den
 finite :letI:=base.toAlgebra; Module.Finite (RatFunc E) (EC A)
 separable :letI:=base.toAlgebra; zw7 (RatFunc E) (EC A)
def relativePolar {A:Equation E} (C:Pencil A) :EC A :=
 polar A false/gauge A C.tilt^(A.d-2)
def pairDegree (s b d c e :ℕ) :ℕ:=b*e+d*c+d*e*s
def elimDegree (A:Equation E) :ℕ :=
 pairDegree A.s A.b A.d (A.b+A.s+1) A.d +
 pairDegree A.s A.b A.d A.b (A.d-1) +
 pairDegree A.s (A.b+A.s+1) A.d A.b (A.d-1)
def adG (w:Valuation E ℤᵐ⁰) (g:E[X]) :ℤᵐ⁰ :=
 g.support.sup (fun j=>w (g.coeff j))
def bix {F:Type} [zrb F] (m:RatFunc E →+* F) (q:F)
    (hf :letI:=m.toAlgebra; Module.Finite (RatFunc E) F) : (RatFunc E)[X] :=
  letI:=m.toAlgebra
  letI:=hf
  (Algebra.lmul (RatFunc E) F q).charpoly
end
end P5_7_1_7_4_3_4
end
