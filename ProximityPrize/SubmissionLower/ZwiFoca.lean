import ProximityPrize.SubmissionLower.ZzOuVbd
import ProximityPrize.SubmissionLower.ZX4kd1a
set_option Elab.async false
set_option autoImplicit true
namespace q8NBBre
noncomputable section
open P6_6 P6_6_7
open aR (af Shape extend wU)
open dN (GeoJets bC Ch AX)
open BO (bfW bsq)
open agL (BV EY)
open GJ (bf6 bZi)
open Dr (tW)
open lB (amo aFf)
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
open scoped BigOperators
def c1 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (assigned:SurfaceAssignment C R G) (A:Cuts assigned) (h:Shape),
      let p:=chartBody C R cs
      let b:=commonBody C R ell cs
      h=weightedChart bf p∨h=p∨h=b →
      32*A.degree h≤(wP (firstSlot C R cs) (cutterBody C ell) b h:ℚ)
def c2 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (T:Ideal GeoJets) (M:Finset P6.K),
      T.IsPrime→ ringKrullDim (GeoJets ⧸ T)=1→bC R∈T→M⊆C.Δ →
      (∀ γ∈M,T≤Ch (extend (C.s γ))) →
      let p:=chartBody C R cs
      (mV:ℚ)*M.card ≤
        (P6.t:ℚ)*tW T [weightedChart bf p] +
          2*(mV:ℚ)*tW T [p]
def c3:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (assigned:SurfaceAssignment C R G) (A:Cuts assigned) (B:Branch),
      B∈A.branches →
      ∀ a :Exponent,EY a=A.order B →
        bC (BV a (A.polynomial B))∉B.2 →
        (∀ γ∈A.marks B,
          wU (BV a (A.polynomial B)) (extend (C.s γ)) (A.a4Q B γ)) →
        (∑ γ∈A.marks B,(A.a4Q B γ:ℚ))≤tW B.2 [commonBody C R ell cs]
variable {C:Context} {R G:af 4} {assigned:SurfaceAssignment C R G}
private theorem active_spec {γ:P6.K} (h:γ∈active assigned) :
    γ∈C.Δ∧0<ord C R γ∧0<excessAt assigned γ:= by
  obtain ⟨hm,he⟩:=Finset.mem_filter.mp h
  exact ⟨hm,Nat.pos_of_ne_zero fun hz=> by simp [excessAt,hz] at he,he⟩
private theorem first_order {γ:P6.K} (hγ:0<ord C R γ) (a :Exponent)
    (ha :EY a=genericOrder R (assigned.aI γ)) :
    wU (BV a R) (extend (C.s γ)) (excessAt assigned γ) := by
  simpa only [excessAt,surfaceOrder,ite_eq_left hγ,ha] using
    cUA R (extend (C.s γ)) a (ord C R γ) (orderAt_ord C R γ)
private theorem choose_cuts (A:SurfaceAssignment C R G) (hR:R≠0) :
    Nonempty (Cuts A) := by
  classical
  let cutIndex (z :Ideal GeoJets) :Exponent :=
    if hz :z.IsPrime then (cSn R z hz hR).choose else 0
  have select (γ:P6.K) (hγ:γ∈active A) : ∃ T,
      let z₀:=A.aI γ
      let u₀:=BV (cutIndex z₀) R
      EY (cutIndex z₀)=genericOrder R z₀∧bC u₀∉z₀ ∧
        (AX z₀ u₀).IsMinimalPrime T∧T≤Ch (extend (C.s γ)) := by
    obtain ⟨hm,ho,he⟩:=active_spec hγ
    obtain ⟨hprime,hmark⟩:=A.valid γ hm ho
    have hD:EY (cutIndex (A.aI γ))=genericOrder R (A.aI γ) ∧
        bC (BV (cutIndex (A.aI γ)) R)∉A.aI γ:= by
      simpa only [cutIndex,dif_pos hprime.isPrime] using
        (cSn R (A.aI γ) hprime.isPrime hR).choose_spec
    obtain ⟨T,hT,hpoint⟩:=bsq hmark
      (bfW he (first_order ho _ hD.1))
    exact ⟨T,hD.1,hD.2,hT,hpoint⟩
  refine ⟨⟨cutIndex,fun γ=>if hγ:γ∈active A then (select γ hγ).choose else ⊥,?_⟩⟩
  intro γ hγ
  simpa only [dif_pos hγ] using (select γ hγ).choose_spec
private theorem curve_geometry {ell cs} (hp:PairInput C R G ell cs)
    (A:Cuts assigned) {B:Branch} (hB:B∈A.branches) :
    B.2.IsPrime∧ringKrullDim (GeoJets ⧸ B.2)=1∧bC R∈B.2 ∧
      bC (A.polynomial B)∈B.2∧A.polynomial B≠0:= by
  classical
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hB
  obtain ⟨hm,ho,_⟩:=active_spec hγ
  have hZ:=(assigned.valid γ hm ho).1
  obtain ⟨_,hU,hT,_⟩:=A.valid γ hγ
  have hR:bC R≠0:= fun hr =>
    hp.factor.1.ne_zero (aFf (hr.trans (map_zero _).symm))
  have hd:=bf6 hR (amo R G hp.factor.1 hp.proper) hZ
  have hcurve :=bZi hZ.isPrime hd
    (hZ.le (Ideal.subset_span (by simp)) :bC R∈assigned.aI γ) hU hT
  refine ⟨hcurve.prime,hcurve.dim,hcurve.contains,
    hT.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)),?_⟩
  intro h
  change BV (A.first (assigned.aI γ)) R=0 at h
  exact hU (by rw [h]; simp [bC])
private theorem branch_estimate (h2 :c2) (h3:c3) {ell cs} (hp:PairInput C R G ell cs)
    (A:Cuts assigned) {B:Branch} (hB:B∈A.branches) :
    (mV:ℚ)*(∑ γ∈A.marks B,(excessAt assigned γ:ℚ)) ≤
      (P6.t:ℚ)*((A.order B:ℚ)*tW B.2 [weightedChart bf (chartBody C R cs)]) +
      2*(mV:ℚ)*((A.order B:ℚ)*tW B.2 [chartBody C R cs]) +
      (mV:ℚ)*((A.order B:ℚ)*tW B.2 [commonBody C R ell cs]) := by
  classical
  obtain ⟨hprime,hdim,hR,hU,hne⟩:=curve_geometry hp A hB
  have he :1≤A.order B:=generic_positive hprime hne hU
  obtain ⟨a,ha,hproper⟩:=cSn (A.polynomial B) B.2 hprime hne
  have mark (γ) (hγ:γ∈A.marks B) :γ∈active assigned∧A.tag γ=B :=
    Finset.mem_filter.mp hγ
  have hcurve :=h2 C R G ell cs hp B.2 (A.marks B) hprime hdim hR
    (fun γ hγ=>(active_spec (mark γ hγ).1).1) (fun γ hγ=> by
      obtain ⟨hm,heq⟩:=mark γ hγ
      rw [← heq]
      exact (A.valid γ hm).2.2.2)
  have hjump:=h3 C R G ell cs hp assigned A B hB a ha hproper (fun γ hγ=> by
    obtain ⟨hm,heq⟩:=mark γ hγ
    have hm' := first_order (active_spec hm).2.1 _ (A.valid γ hm).1
    have hfirst:wU (A.polynomial B) (extend (C.s γ)) (excessAt assigned γ) := by
      rw [← heq]
      exact hm'
    simpa only [Cuts.a4Q,Cuts.order,ha] using cUA _ _ a _ hfirst)
  let J:ℚ := ∑ γ∈A.marks B,(A.a4Q B γ:ℚ)
  have hnonneg:0≤J:=Finset.sum_nonneg fun _ _=>Nat.cast_nonneg _
  have hJ:J≤(A.order B:ℚ)*tW B.2 [commonBody C R ell cs] :=
    (le_mul_of_one_le_left hnonneg (by exact_mod_cast he)).trans
      (mul_le_mul_of_nonneg_left hjump (Nat.cast_nonneg _))
  have hsplit : (∑ γ∈A.marks B,(excessAt assigned γ:ℚ)) ≤
      (A.order B:ℚ)*(A.marks B).card+J:= by
    calc
      _ ≤ ∑ γ∈A.marks B,((A.order B:ℚ)+(A.a4Q B γ:ℚ)) := by
        apply Finset.sum_le_sum
        intro γ _
        exact_mod_cast (show excessAt assigned γ≤A.order B+A.a4Q B γ by
          unfold Cuts.a4Q
          omega)
      _ = _:= by simp [J,Finset.sum_add_distrib,mul_comm]
  calc
    _≤(mV:ℚ)*((A.order B:ℚ)*(A.marks B).card+J) :=
      mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg _)
    _=(A.order B:ℚ)*((mV:ℚ)*(A.marks B).card)+(mV:ℚ)*J:= by ring
    _≤_:=(add_le_add (mul_le_mul_of_nonneg_left hcurve (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _))).trans_eq (by ring)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_6_7.c1 := by
  classical
  intro C R G ell cs hp assigned
  let p:=chartBody C R cs
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  let b:=commonBody C R ell cs
  let w:=weightedChart bf p
  obtain ⟨A⟩:=choose_cuts assigned hp.factor.1.ne_zero
  have hsum: (∑ B∈A.branches,∑ γ∈A.marks B,(excessAt assigned γ:ℚ)) =
      (DG C R G assigned:ℚ) := by
    unfold Cuts.branches Cuts.marks
    rw [Finset.sum_fiberwise_of_maps_to
      (fun γ hγ=>Finset.mem_image_of_mem A.tag hγ) (fun γ=>(excessAt assigned γ:ℚ))]
    change (∑ γ∈C.Δ.filter (fun γ=>0<excessAt assigned γ),(excessAt assigned γ:ℚ)) =
      (↑(∑ γ∈C.Δ,excessAt assigned γ) :ℚ)
    rw [Finset.sum_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro γ _
    by_cases h:0<excessAt assigned γ
    · exact ite_eq_left h
    · simp [h,Nat.eq_zero_of_not_pos h]
  have hbudget: (mV:ℚ)*(DG C R G assigned:ℚ) ≤
      (P6.t:ℚ)*A.degree w+2*(mV:ℚ)*A.degree p +
      (mV:ℚ)*A.degree b:= by
    rw [← hsum,Finset.mul_sum]
    unfold Cuts.degree
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro B hB
    simpa only [Finset.mul_sum] using branch_estimate h2 h3 hp A hB
  have hw:=h1 C R G ell cs hp assigned A w (Or.inl rfl)
  have hp' := h1 C R G ell cs hp assigned A p (Or.inr (Or.inl rfl))
  have hb:=h1 C R G ell cs hp assigned A b (Or.inr (Or.inr rfl))
  have hscaled: (32 :ℚ)*(mV:ℚ)*(DG C R G assigned:ℚ) ≤
      (P6.t:ℚ)*(wP r q b w:ℚ) +
      2*(mV:ℚ)*(wP r q b p:ℚ) +
      (mV:ℚ)*(wP r q b b:ℚ) := by
    calc
      _≤32*((P6.t:ℚ)*A.degree w+2*(mV:ℚ)*A.degree p +
          (mV:ℚ)*A.degree b) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hbudget (by positivity)
      _=(P6.t:ℚ)*(32*A.degree w)+2*(mV:ℚ)*(32*A.degree p) +
          (mV:ℚ)*(32*A.degree b) := by ring
      _≤_:=add_le_add (add_le_add (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hp' (by positivity))) (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  change (feeScale :ℤ)*DG C R G assigned≤ curve32 p r q b+point32 r q b
  have hf : (feeScale :ℚ)=32*(mV:ℚ) := by simp [feeScale]
  have hi: (↑((feeScale :ℤ)*DG C R G assigned) :ℚ) ≤
      (↑(curve32 p r q b+point32 r q b) :ℚ) := by
    simp only [curve32,point32,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,hf]
    exact hscaled
  exact_mod_cast hi
end
end q8NBBre
