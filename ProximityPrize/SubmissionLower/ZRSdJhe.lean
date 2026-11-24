import ProximityPrize.SubmissionLower.ZpdLrZa
import ProximityPrize.SubmissionLower.ZDI0Pnd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Function.Injective → zq4, IsScalarTower.algebraMap_apply → zG3, MvPolynomial.eval₂_comp_left → zqI, Polynomial.X → z7y, PowerSeries.coeff → z2o, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, PowerSeries.constantCoeff → zbO, RingHom.id → zz4
set_option backward.isDefEq.respectTransparency false
namespace qpVvmab
noncomputable section
open Polynomial Finset
open scoped Classical
open cu (L)
open axj (a5F)
open bay (aER cph)
open qNu3xvc (Equation)
open qZV9OWb (ValueSlice)
open qZu9hjc (atPair)
open q8Z6NHc (Slot)
open qAW6lac (Index jo spectral ic aMp deform extract extract_coeff)
def c1 :Prop :=
  ∀ {E :Type} [Field E] [zZE L E] (A:Equation E) (B:ValueSlice A) (δ:Direction A),
    Nonempty (Lift A B δ)
def c2 :Prop :=
  ∀ {E :Type} [Field E] [zZE L E] (A:Equation E),0<A.s→2≤A.d →
    ∀ (B:ValueSlice A) (δ:Direction A) (U:Lift A B δ)
      (Q:jo A.d A.s (A.b+A.d*A.s)),
      sample (actual A B) δ Q≠0 →
      ∃ δ' : Direction A,
        (∀ j,δ' (.inl j)=δ (.inl j)) ∧
        (∀ j,δ' (.inr (.inl j))=δ (.inr (.inl j))) ∧
        sample (actual A B) δ' Q≠0∧zq4 (value A B δ δ' U)
variable {E :Type} [Field E] [zZE L E]
private theorem exists_sample {d s W:ℕ} (α:Index d s W→E)
  {Q:jo d s W} (hQ:Q≠0) :
  ∃ δ,sample α δ Q≠0:= by
 by_contra! h
 let j:=algebraMap L E
 let S (i:Index d s W) :=Set.range (fun a :L=>α i+j a)
 have hS (i) : (S i).Infinite :=Set.infinite_range_of_injective fun a b hab =>
  j.injective (add_left_cancel hab)
 apply hQ
 apply (MvPolynomial.map_injective _ j.injective)
 rw [map_zero]
 apply MvPolynomial.funext_set S hS
 intro x hx
 choose δ hδ using fun i=>hx i (Set.mem_univ i)
 have he :x=fun i=>α i+j (δ i) :=funext fun i=>(hδ i).symm
 rw [he,MvPolynomial.eval_map]
 simpa [sample,j] using h δ
private theorem deform_ne {d s W:ℕ} (α:Index d s W→E) (δ:Index d s W→L)
   (Q:jo d s W) (h:sample α δ Q≠0) :deform α δ Q≠0:= by
 let ev :=(evalRingHom (1 :E)).comp (evalRingHom (0:E[X]))
 have hQ:ev (deform α δ Q)=sample α δ Q:= by
   rw [deform,zqI,sample]
   have hc:ev.comp (C.comp (C.comp (algebraMap L E)))=algebraMap L E := by
     ext a
     simp [ev]
   have hv :ev ∘ ic α δ=fun i=>α i+algebraMap L E (δ i) := by
     funext i
     by_cases hi:i=spectral d s W <;> simp [ev,ic,hi]
   rw [hc,hv]
 exact fun hz=>h (by rw [← hQ,hz,map_zero])
private def inner :E[X] →+* Series E :=(Polynomial.coeToPowerSeries.algHom _).toRingHom
omit [zZE L E] in
private theorem inner_C (a :E) :inner (C a)=PowerSeries.C (algebraMap E _ a) := by
 simp [inner]
omit [zZE L E] in
private theorem inner_X:inner (z7y:E[X])=PowerSeries.X:= by
 simp [inner]
private theorem eval_deform {d s W:ℕ} (α:Index d s W→E) (δ:Index d s W→L)
    (Q:jo d s W) (t:Series E) :
    ((deform α δ Q).map inner).eval t =
      Q.eval₂ (algebraMap L (Series E))
        (fun i=>base α δ i - if i=spectral d s W then t else 0) := by
  rw [eval_map,← coe_eval₂RingHom,deform,zqI]
  have hc: (eval₂RingHom inner t).comp (C.comp (C.comp (algebraMap L E))) =
      algebraMap L (Series E) := by
    ext a
    simp [inner_C,PowerSeries.algebraMap_apply,
      zG3 L E (AlgebraicClosure E)]
  have hv : (eval₂RingHom inner t) ∘ ic α δ =
      fun i=>base α δ i - if i=spectral d s W then t else 0:= by
    funext i
    by_cases hi:i=spectral d s W <;>
      simp [ic,base,hi,inner_C,inner_X,PowerSeries.algebraMap_apply,
        zG3 L E (AlgebraicClosure E)]
  rw [hc,hv]
private theorem block_sub {F:Type} [CommRing F] {d s W:ℕ}
   (u:Slot (d-1) s (W-s)→F) (x y t:F) :
   aMp (fun j=>u j - if Sum.inr (Sum.inr j)=spectral d s W then t else 0) x y =
     aMp u x y - t:= by
 let z :Slot (d-1) s (W-s) :=⟨(0,0),by simp⟩
 have he (j:Slot (d-1) s (W-s)) :
     (Sum.inr (Sum.inr j)=spectral d s W)↔j=z := by simp [spectral,z]
 simp only [aMp,he,sub_mul,sum_sub_distrib]
 congr 1
 rw [Finset.sum_eq_single z]
 · simp [z]
 · intro j _ hj
   simp [hj]
 · simp
omit [zZE L E] in
theorem block_actual {F:Type} [Field F] (j:E →+* F) (x y :F)
    (p:E[X][X]) {d s W:ℕ} (hd:p.natDegree≤d)
    (hw : ∀ i,p.coeff i≠0→(p.coeff i).natDegree+i*s≤W) :
    aMp (fun u:Slot d s W=>j ((p.coeff u.val.1).coeff u.val.2)) x y =
      atPair j x y p:= by
  unfold aMp atPair
  let a (u:Fin (d+1)×Fin (W+1)) :=j ((p.coeff u.1).coeff u.2)*x^u.2.val*y^u.1.val
  let P (u:Fin (d+1)×Fin (W+1)) :=u.2.val+u.1.val*s≤W
  change (∑ u : {u // P u},a u.val)= _
  rw [← Finset.subtype_univ P,Finset.sum_subtype_eq_sum_filter]
  rw [Finset.sum_subset (Finset.filter_subset _ _)]
  · rw [Fintype.sum_prod_type,eval₂_eq_sum_range' _ (show p.natDegree<d+1 by omega),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hdeg: (p.coeff i).natDegree<W+1 := by
      by_cases h:p.coeff i=0
      · simp [h]
      · have :=hw i h
        omega
    rw [coe_eval₂RingHom,eval₂_eq_sum_range' _ hdeg,← Fin.sum_univ_eq_sum_range,Finset.sum_mul]
  · intro u _ hu
    have hb : ¬P u:= by simpa using hu
    suffices hz : (p.coeff u.1).coeff u.2=0 by simp [a,hz]
    by_cases hp:p.coeff u.1=0
    · simp [hp]
    · apply coeff_eq_zero_of_natDegree_lt
      have hh:=hw u.1 hp
      dsimp [P] at hb
      omega
private theorem value₀ (A:Equation E) (B:ValueSlice A)
   (δ δ' : Direction A) (U:Lift A B δ) (i:Fin B.size) :
   zbO (value A B δ δ' U i) =
     atPair (algebraMap E _) (B.point i).1 (B.point i).2 A.f.derivative := by
 unfold value aMp
 simp only [map_sum,map_mul,map_pow,U.x₀,U.y₀,base,map_add,
   PowerSeries.constantCoeff_C,PowerSeries.constantCoeff_X,mul_zero,add_zero]
 apply block_actual _ _ _ _ (natDegree_derivative_le A.f)
 intro n hn
 rw [coeff_derivative] at hn ⊢
 have hz :A.f.coeff (n+1)≠0:= by
   intro h
   simp [h] at hn
 obtain hw | h:=A.weight (n+1)
 · have hdeg:=natDegree_mul_le (p:=A.f.coeff (n+1)) (q:=(n:E[X])+1)
   rw [← Nat.cast_succ (R:=E[X]) n] at hdeg
   simp only [natDegree_natCast,add_zero] at hdeg
   rw [Nat.cast_succ] at hdeg
   rw [Nat.add_mul,one_mul] at hw
   change _≤A.b+A.f.natDegree*A.s - A.s
   omega
 · exact (hz h).elim
private theorem linear_product {S:Type} [CommRing S] [IsDomain S]
  {ι:Type} [Fintype ι] (t:ι→S) (ht:zq4 t) (D:S[X])
  (hroot : ∀ i,D.eval (t i)=0) :
  (∏ i,((z7y:S[X]) - C (t i)))∣D:= by
 let j:=algebraMap S (FractionRing S)
 have hj:=IsFractionRing.injective S (FractionRing S)
 rw [← map_dvd_map j hj (monic_prod_of_monic _ _ fun i _=>monic_X_sub_C (t i)),
  Polynomial.map_prod]
 simp only [Polynomial.map_sub,map_X,map_C]
 apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (hj.comp ht))
 intro i
 rw [dvd_iff_isRoot,IsRoot]
 change (D.map j).eval (j (t i))=0
 rw [eval_map_apply,hroot,map_zero]
private theorem bOH {d s W:ℕ} (α:Index d s W→E) (δ:Index d s W→L)
   (Q:jo d s W) (n:ℕ) :
   z2o n (aER (zz4 (Series E)) ((deform α δ Q).map inner)) =
     (extract α δ Q n).map (algebraMap E (AlgebraicClosure E)) := by
 rw [cph _ (z2o n) _ (fun _=>rfl)]
 ext i
 rw [a5F,coeff_map,coeff_map,extract_coeff]
 simp [inner,Polynomial.coeff_coe]
private theorem extract_dvd {d s W:ℕ} (α:Index d s W→E) (δ:Index d s W→L)
    (Q:jo d s W) (h:deform α δ Q≠0)
    {ι:Type} [Fintype ι] (t:ι→Series E) (ht:zq4 t)
    (hroot : ∀ i,((deform α δ Q).map inner).eval (t i)=0) (N :E[X]) (hN :N.Monic)
    (hprod:N.map (algebraMap E (AlgebraicClosure E)) =
      ∏ i,((z7y: (AlgebraicClosure E)[X]) - C (zbO (t i)))) :
    ∃ n,extract α δ Q n≠0∧N∣extract α δ Q n:= by
  let V := ∏ i,((z7y: (Series E)[X]) - C (t i))
  obtain ⟨G,hG⟩:=linear_product t ht _ hroot
  let swap:=aER (zz4 (Series E))
  have hV:zbO (swap V)=N.map (algebraMap E (AlgebraicClosure E)) := by
    rw [hprod]
    simp [V,swap,← zW1,
      -PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map]
  have hGne :swap G≠0:= by
    intro hz
    have hd:swap ((deform α δ Q).map inner)=0:= by rw [hG,map_mul,hz,mul_zero]
    apply h
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro n
    have hz :=bOH α δ Q n
    rw [show aER (zz4 (Series E)) ((deform α δ Q).map inner)=0 from hd,
      map_zero] at hz
    have hi:=congrArg (fun p: (AlgebraicClosure E)[X]=>p.coeff i) hz.symm
    rw [coeff_map,extract_coeff,coeff_zero] at hi
    exact (algebraMap E (AlgebraicClosure E)).injective (hi.trans (map_zero _).symm)
  let n:=(swap G).order.toNat
  have hcoeff :
      (extract α δ Q n).map (algebraMap E (AlgebraicClosure E)) =
        N.map (algebraMap E (AlgebraicClosure E)) *
          zbO (PowerSeries.divXPowOrder (swap G)) := by
    rw [← bOH,show aER (zz4 (Series E)) _=swap (V*G) from
      congrArg swap hG,map_mul]
    conv_lhs=>rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f :=swap G),mul_left_comm]
    simpa only [zero_add,zW1,map_mul,hV] using
      PowerSeries.coeff_X_pow_mul (swap V*PowerSeries.divXPowOrder (swap G)) n 0
  refine ⟨n,?_,?_⟩
  · intro hz
    rw [hz,Polynomial.map_zero] at hcoeff
    exact (mul_ne_zero (hN.map _).ne_zero
      (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hGne)) hcoeff.symm
  · exact (map_dvd_map _ (algebraMap E (AlgebraicClosure E)).injective hN).mp ⟨_,hcoeff⟩
theorem of_children (h1 :c1) (h2 :c2) :qAW6lac.c3:= by
 intro E _ _ A hs hd B R
 obtain ⟨δ,hδ⟩:=exists_sample (actual A B) R.nonzero
 obtain ⟨U⟩:=h1 A B δ
 obtain ⟨δ',hf,hg,hQ,ht⟩:=h2 A hs hd B δ U R.poly hδ
 let t:=value A B δ δ' U
 have hroot (i:Fin B.size) : ((deform (actual A B) δ' R.poly).map inner).eval (t i)=0:= by
   rw [eval_deform]
   apply R.aiq _ (U.x i) (U.y i)
   · simpa [spectral,base,hf] using U.f_zero i
   · simpa [spectral,base,hg] using U.g_zero i
   · rw [block_sub]
     exact sub_self _
 have hp:B.N.map (algebraMap E (AlgebraicClosure E)) =
     ∏ i,((z7y: (AlgebraicClosure E)[X]) - C (zbO (t i))) := by
   simpa only [t,value₀] using B.product
 obtain ⟨n,hn,hdiv⟩:=extract_dvd (actual A B) δ' R.poly
   (deform_ne _ _ _ hQ) t ht hroot B.N B.monic hp
 exact ⟨δ',n,hn,hdiv⟩
end
end qpVvmab
