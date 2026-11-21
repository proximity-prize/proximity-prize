import ProximityPrize.SubmissionLower.Rect51HilbertBase

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Rect51Hilbert

noncomputable section

open K1_14 (FX)
open HighCore82706Tangent_3 (JetRing ordinate)
open MvPolynomial
open scoped BigOperators MonomialOrder

def Stable (L : Layer) : Prop :=
  (∀ d, L d ≤ homogeneous d) ∧
  ∀ d e {p q : Cox}, p ∈ homogeneous e → q ∈ L d → p * q ∈ L (e + d)
def exponentCount (U : Set Exponent) (d : Degree) : ℕ :=
  {m | m ∈ U ∧ Finsupp.weight coxWeight m = d}.ncard
structure Block where
  base : Exponent
  free : Finset CoxVar
def Block.exponents (B : Block) : Set Exponent :=
  {m | ∃ u : Exponent, (∀ i ∉ B.free, u i = 0) ∧ m = B.base + u}
def blockCount (blocks : Finset Block) (d : Degree) : ℕ :=
  ∑ B ∈ blocks, exponentCount B.exponents d
private theorem homogeneous_mul {p q : Cox} {d e : Degree}
    (hp : p ∈ homogeneous e) (hq : q ∈ homogeneous d) : p * q ∈ homogeneous (e + d) :=
  IsWeightedHomogeneous.mul hp hq
theorem homogeneous_stable : Stable homogeneous := by
  refine ⟨fun _ => le_rfl, ?_⟩
  intro d e p q hp hq
  exact homogeneous_mul hp hq
private theorem qmap_mem (Q : Ideal JetRing) {d : Degree} {p : Cox}
    (hp : p ∈ homogeneous d) : qmap Q p ∈ gradedPiece Q d :=
  Submodule.mem_map.mpr ⟨p, hp, rfl⟩
private theorem piece_mul {Q : Ideal JetRing} {d e : Degree} {x y : JetRing ⧸ Q}
    (hx : x ∈ gradedPiece Q e) (hy : y ∈ gradedPiece Q d) :
    x * y ∈ gradedPiece Q (e + d) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  exact Submodule.mem_map.mpr ⟨p * q, homogeneous_mul hp hq, map_mul (qmap Q) p q⟩
private def pullback (Q : Ideal JetRing) (V : Degree → Submodule FX (JetRing ⧸ Q)) :
    Layer := fun d => homogeneous d ⊓ (V d).comap (qmap Q).toLinearMap
private theorem stable_pullback (Q : Ideal JetRing)
    (V : Degree → Submodule FX (JetRing ⧸ Q))
    (hV : ∀ d e {x y : JetRing ⧸ Q}, x ∈ gradedPiece Q e → y ∈ V d → x * y ∈ V (e + d)) :
    Stable (pullback Q V) := by
  refine ⟨fun _ => inf_le_left, ?_⟩
  intro d e p q hp hq
  refine ⟨homogeneous_mul hp hq.1, ?_⟩
  change qmap Q (p * q) ∈ V (e + d)
  rw [map_mul]
  exact hV d e (qmap_mem Q hp) hq.2
def kernelLayer (Q : Ideal JetRing) : Layer := pullback Q fun _ => ⊥
theorem kernelLayer_stable (Q : Ideal JetRing) : Stable (kernelLayer Q) := by
  apply stable_pullback
  intro d e x y _ hy
  rw [(Submodule.mem_bot FX).mp hy, mul_zero]
  exact Submodule.zero_mem _
theorem kernelLayer_rank (Q : Ideal JetRing) (d : Degree) :
    Module.finrank FX (kernelLayer Q d) + Module.finrank FX (gradedPiece Q d) =
      Module.finrank FX (homogeneous d) := by
  have : Module.Finite FX (homogeneous d) := cox_piece_finite d
  let F := (qmap Q).toLinearMap.domRestrict (homogeneous d)
  have hker : LinearMap.ker F = (kernelLayer Q d).comap (homogeneous d).subtype := by
    ext x
    exact ⟨fun hx => ⟨x.prop, hx⟩, fun hx => hx.2⟩
  have hr := LinearMap.finrank_range_add_finrank_ker (K := FX)
    (V := ↥(homogeneous d)) (V₂ := JetRing ⧸ Q) F
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe ((kernelLayer_stable Q).1 d)).finrank_eq, add_comm] at hr
  exact hr
private def sectionImage (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) (d : Degree) :
    Submodule FX (JetRing ⧸ Q) :=
  if k ≤ d then (gradedPiece Q (d - k)).map (LinearMap.mulLeft FX u) else ⊥
def cutLayer (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) : Layer :=
  pullback Q (sectionImage Q k u)
theorem cutLayer_stable (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) :
    Stable (cutLayer Q k u) := by
  apply stable_pullback
  intro d e x y hx hy
  by_cases hd : k ≤ d
  · have he : k ≤ e + d := hd.trans le_add_self
    rw [sectionImage, ite_eq_left hd] at hy
    rw [sectionImage, ite_eq_left he, add_tsub_assoc_of_le hd]
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨x * z, piece_mul hx hz, by
      simp only [LinearMap.mulLeft_apply]
      ac_rfl⟩
  · rw [sectionImage, ite_eq_right hd] at hy
    rw [(Submodule.mem_bot FX).mp hy, mul_zero]
    exact Submodule.zero_mem _
theorem cutLayer_le {Q R : Ideal JetRing} (hQR : Q ≤ R) (k : Degree) {u : JetRing}
    (hu : u ∈ R) (d : Degree) :
    cutLayer Q k (Ideal.Quotient.mk Q u) d ≤ kernelLayer R d := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  change qmap R p = 0
  have hcomp : Ideal.Quotient.factor hQR (qmap Q p) = qmap R p :=
    Ideal.Quotient.factor_mk hQR (dehom p)
  rw [← hcomp]
  have hmem : qmap Q p ∈ sectionImage Q k (Ideal.Quotient.mk Q u) d := hp.2
  by_cases hd : k ≤ d
  · rw [sectionImage, ite_eq_left hd] at hmem
    obtain ⟨z, _, hz⟩ := Submodule.mem_map.mp hmem
    rw [← hz, LinearMap.mulLeft_apply, map_mul, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_mul]
  · rw [sectionImage, ite_eq_right hd] at hmem
    rw [(Submodule.mem_bot FX).mp hmem, map_zero]
private theorem cut_rank_aux (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q)
    (d : Degree) (hV : sectionImage Q k u d ≤ gradedPiece Q d) :
    Module.finrank FX (kernelLayer Q d) + Module.finrank FX (sectionImage Q k u d) =
      Module.finrank FX (cutLayer Q k u d) := by
  have : Module.Finite FX (homogeneous d) := cox_piece_finite d
  have : Module.Finite FX (cutLayer Q k u d) :=
    Submodule.finiteDimensional_of_le ((cutLayer_stable Q k u).1 d)
  let F := (qmap Q).toLinearMap.domRestrict (cutLayer Q k u d)
  have hle : kernelLayer Q d ≤ cutLayer Q k u d := by
    intro p hp
    have hz : qmap Q p = 0 := hp.2
    exact ⟨hp.1, show qmap Q p ∈ sectionImage Q k u d by rw [hz]; exact Submodule.zero_mem _⟩
  have hker : LinearMap.ker F = (kernelLayer Q d).comap (cutLayer Q k u d).subtype := by
    ext x
    exact ⟨fun hx => ⟨x.prop.1, hx⟩, fun hx => hx.2⟩
  have hrange : LinearMap.range F = sectionImage Q k u d := by
    rw [LinearMap.range_domRestrict]
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
      exact hp.2
    · intro x hx
      obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp (hV hx)
      refine Submodule.mem_map.mpr ⟨p, ⟨hp, ?_⟩, he⟩
      change qmap Q p ∈ sectionImage Q k u d
      change qmap Q p = x at he
      rwa [he]
  have hr := LinearMap.finrank_range_add_finrank_ker (K := FX)
    (V := ↥(cutLayer Q k u d)) (V₂ := JetRing ⧸ Q) F
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, add_comm] at hr
  exact hr
structure CoxSection (Q : Ideal JetRing) (d : Degree) where
  order : ℕ
  finiteChart : Cox
  inverseChart : Cox
  finite_degree : finiteChart.IsWeightedHomogeneous coxWeight (d + order • (1,0,0,0))
  inverse_degree : inverseChart.IsWeightedHomogeneous coxWeight (d + order • (1,0,0,0))
  glue : ordinate ^ order * dehom finiteChart - dehom inverseChart ∈ Q

def CoxSection.affine {Q : Ideal JetRing} {d : Degree} (S : CoxSection Q d) : JetRing :=
  dehom S.finiteChart

private theorem affine_X_h₀ : dehom (MvPolynomial.X h₀) = 1 := by simp [dehom, affineCoord, h₀]
private theorem affine_X_h₁ : dehom (MvPolynomial.X h₁) = ordinate := by simp [dehom, affineCoord, h₁]
private theorem shifted_monomial {Q : Ideal JetRing} {d : Degree}
    (S : CoxSection Q d) {h t s₀ s₁ : ℕ} (hh : 2*S.order ≤ h)
    (m : CoxVar →₀ ℕ) (a : FX) (hm : Finsupp.weight coxWeight m = nefDegree h t s₀ s₁) :
    Ideal.Quotient.mk Q S.affine * qmap Q (monomial m a) ∈
      gradedPiece Q (nefDegree h t s₀ s₁ + d) := by
  classical
  have hbase : h ≤ m h₀ + m h₁ := by
    have h' := hm
    rw [weight_coordinates] at h'
    have ha := congrArg Prod.fst h'
    have hb := congrArg (fun d : Degree => d.2.1) h'
    change m h₀ + m h₁ + 2*m v₁ = h + 2*t at ha
    change m v₀ + m v₁ = t at hb
    omega
  have helper (i : CoxVar) (hi : coxWeight i = (1, 0, 0, 0)) (hm' : S.order ≤ m i)
      (p : Cox) (hp : p.IsWeightedHomogeneous coxWeight (d + S.order • (1,0,0,0)))
      (heq : Ideal.Quotient.mk Q S.affine * qmap Q (MvPolynomial.X i ^ S.order) =
        qmap Q p) :
      Ideal.Quotient.mk Q S.affine * qmap Q (monomial m a) ∈
        gradedPiece Q (nefDegree h t s₀ s₁ + d) := by
    let u := m - Finsupp.single i S.order
    have hle : Finsupp.single i S.order ≤ m := Finsupp.single_le_iff.mpr hm'
    have hu : u + Finsupp.single i S.order = m := tsub_add_cancel_of_le hle
    have hwt : Finsupp.weight coxWeight u + S.order • (1, 0, 0, 0) = nefDegree h t s₀ s₁ := by
      rw [← hm, ← hu, map_add, Finsupp.weight_single, hi]
    have hw : (monomial u a : Cox).IsWeightedHomogeneous coxWeight
        (Finsupp.weight coxWeight u) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hmem : qmap Q (monomial u a * p) ∈
        gradedPiece Q (Finsupp.weight coxWeight u + (d + S.order • (1,0,0,0))) :=
      qmap_mem _ (hw.mul hp)
    rw [show Finsupp.weight coxWeight u + (d + S.order • (1,0,0,0)) =
      nefDegree h t s₀ s₁ + d by rw [← hwt]; ac_rfl] at hmem
    have hmdecomp : (monomial m a : Cox) = monomial u a * MvPolynomial.X i ^ S.order := by
      rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, hu, mul_one]
    rw [hmdecomp, map_mul, mul_left_comm, heq, ← map_mul]
    exact hmem
  by_cases h₀ex : S.order ≤ m h₀
  · apply helper h₀ rfl h₀ex S.finiteChart S.finite_degree
    simp [qmap, CoxSection.affine, affine_X_h₀]
  · have h₁ex : S.order ≤ m h₁ := by omega
    apply helper h₁ rfl h₁ex S.inverseChart S.inverse_degree
    have hg := Ideal.Quotient.eq_zero_iff_mem.mpr S.glue
    simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hg
    change Ideal.Quotient.mk Q S.affine *
      Ideal.Quotient.mk Q (dehom (MvPolynomial.X h₁ ^ S.order)) =
        Ideal.Quotient.mk Q (dehom S.inverseChart)
    rw [map_pow, affine_X_h₁, map_pow, mul_comm]
    exact hg
theorem relativeSection_mul_gradedPiece {Q : Ideal JetRing} {d : Degree}
    (S : CoxSection Q d) {h t s₀ s₁ : ℕ} (hh : 2*S.order ≤ h)
    {a : JetRing ⧸ Q} (ha : a ∈ gradedPiece Q (nefDegree h t s₀ s₁)) :
    Ideal.Quotient.mk Q S.affine * a ∈ gradedPiece Q (nefDegree h t s₀ s₁ + d) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  change p.IsWeightedHomogeneous coxWeight (nefDegree h t s₀ s₁) at hp
  change Ideal.Quotient.mk Q S.affine * qmap Q p ∈ _
  have he : qmap Q p = ∑ m ∈ p.support, qmap Q (monomial m (p.coeff m)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he, Finset.mul_sum]
  exact Submodule.sum_mem _ fun m hm =>
    shifted_monomial S hh m (p.coeff m) (hp (mem_support_iff.mp hm))

theorem cutLayer_rank {Q : Ideal JetRing} {a b c f : ℕ}
    (S : CoxSection Q (nefDegree a b c f))
    (hreg : IsLeftRegular (Ideal.Quotient.mk Q S.affine))
    {h t s₀ s₁ : ℕ} (hh : 2 * S.order ≤ h) :
    Module.finrank FX (kernelLayer Q (nefDegree (h+a) (t+b) (s₀+c) (s₁+f))) + hilbert Q h t s₀ s₁ =
      Module.finrank FX (cutLayer Q (nefDegree a b c f) (Ideal.Quotient.mk Q S.affine)
        (nefDegree (h+a) (t+b) (s₀+c) (s₁+f))) := by
  let k := nefDegree a b c f
  let e := nefDegree h t s₀ s₁
  let u := Ideal.Quotient.mk Q S.affine
  have he : e + k = nefDegree (h+a) (t+b) (s₀+c) (s₁+f) := by
    simp only [e, k, nefDegree, Prod.mk_add_mk]
    simp only [Nat.add_assoc,Nat.mul_add,Nat.add_left_comm,Nat.add_comm]
  have hI : sectionImage Q k u (e + k) =
      (gradedPiece Q e).map (LinearMap.mulLeft FX u) := by
    have hk : k ≤ e + k := le_add_self
    rw [sectionImage, ite_eq_left hk, add_tsub_cancel_right]
  have hV : sectionImage Q k u (e + k) ≤ gradedPiece Q (e + k) := by
    rw [hI]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact relativeSection_mul_gradedPiece S hh hy
  have hr := cut_rank_aux Q k u (e + k) hV
  rw [hI, ← (Submodule.equivMapOfInjective (LinearMap.mulLeft FX u) hreg _).finrank_eq, he] at hr
  exact hr
private theorem finite_generators (U : Set Exponent) (hU : IsUpperSet U) :
    ∃ F : Finset Exponent, ∀ m, m ∈ U ↔ ∃ b ∈ F, b ≤ m := by
  classical
  have hf : {b | Minimal (· ∈ U) b}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain fun a ha b hb hab hle =>
      hab (le_antisymm hle (hb.2 ha.1 hle))
  refine ⟨hf.toFinset, fun m => ?_⟩
  constructor
  · intro hm
    obtain ⟨b, hbm, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ U) m hm
    exact ⟨b, hf.mem_toFinset.mpr hb, hbm⟩
  · rintro ⟨b, hb, hbm⟩
    exact hU hbm (hf.mem_toFinset.mp hb).1
private theorem mem_inf_iff {U : Set Exponent} (hU : IsUpperSet U)
    (F : Finset Exponent) (hF : ∀ m, m ∈ U ↔ ∃ b ∈ F, b ≤ m)
    {M : Exponent} (hM : ∀ b ∈ F, b ≤ M) (m : Exponent) :
    m ⊓ M ∈ U ↔ m ∈ U := by
  refine ⟨hU inf_le_left, fun hm => ?_⟩
  obtain ⟨b, hb, hbm⟩ := (hF m).mp hm
  exact (hF _).mpr ⟨b, hb, le_inf hbm (hM b hb)⟩
private def blockAt (M b : Exponent) : Block :=
  ⟨b, Finset.univ.filter fun i : CoxVar => b i = M i⟩
private theorem mem_blockAt_iff {M b m : Exponent} (hb : b ≤ M) :
    m ∈ (blockAt M b).exponents ↔ m ⊓ M = b := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    ext i
    change min (b i + u i) (M i) = b i
    by_cases he : b i = M i
    · rw [he, min_eq_right (by omega)]
    · have hz := hu i (by simp [blockAt, he])
      rw [hz, add_zero, min_eq_left (hb i)]
  · intro he
    have hm : b ≤ m := he ▸ inf_le_left
    refine ⟨m-b, ?_, (add_tsub_cancel_of_le hm).symm⟩
    intro i hi
    have hne : b i ≠ M i := by simpa [blockAt] using hi
    have h := congrArg (fun v : Exponent => v i) he
    change min (m i) (M i) = b i at h
    change m i - b i = 0
    omega
theorem orthant_partition (U V : Set Exponent) (hU : IsUpperSet U) (hV : IsUpperSet V) :
    ∃ blocks : Finset Block, ∀ d, exponentCount (V \ U) d = blockCount blocks d := by
  classical
  obtain ⟨FU, hFU⟩ := finite_generators U hU
  obtain ⟨FV, hFV⟩ := finite_generators V hV
  let M := (FU ∪ FV).sup id
  have same (m : Exponent) : m ⊓ M ∈ V \ U ↔ m ∈ V \ U := by
    have hu := mem_inf_iff hU FU hFU (M := M)
      (fun b hb => Finset.le_sup (f := id) (Finset.mem_union_left FV hb)) m
    have hv := mem_inf_iff hV FV hFV (M := M)
      (fun b hb => Finset.le_sup (f := id) (Finset.mem_union_right FU hb)) m
    change m ⊓ M ∈ V ∧ m ⊓ M ∉ U ↔ m ∈ V ∧ m ∉ U
    rw [hu, hv]
  let bases := (Finset.Iic M).filter fun b => b ∈ V \ U
  have hbase (b : Exponent) : b ∈ bases ↔ b ≤ M ∧ b ∈ V \ U := by simp [bases]
  let enc : Exponent ↪ Block := ⟨blockAt M, fun _ _ h => congrArg Block.base h⟩
  refine ⟨bases.map enc, fun d => ?_⟩
  let fiber (b : Exponent) := {m : Exponent | m ∈ (blockAt M b).exponents ∧
    Finsupp.weight coxWeight m = d}
  have hEq : {m : Exponent | m ∈ V \ U ∧ Finsupp.weight coxWeight m = d} =
      ⋃ b ∈ (bases : Set Exponent), fiber b := by
    ext m
    rw [Set.mem_iUnion₂]
    constructor
    · rintro ⟨hm, hd⟩
      have hb : m ⊓ M ≤ M := inf_le_right
      exact ⟨m ⊓ M, (hbase _).mpr ⟨hb, (same m).mpr hm⟩, (mem_blockAt_iff hb).mpr rfl, hd⟩
    · rintro ⟨b, hb, hm, hd⟩
      obtain ⟨hle, hmem⟩ := (hbase b).mp hb
      exact ⟨(same m).mp ((mem_blockAt_iff hle).mp hm ▸ hmem), hd⟩
  have hdisj : (bases : Set Exponent).PairwiseDisjoint fiber := by
    intro b hb z hz hne
    refine Set.disjoint_left.mpr fun m hm hm' => hne ?_
    have h₁ := (mem_blockAt_iff ((hbase b).mp hb).1).mp hm.1
    have h₂ := (mem_blockAt_iff ((hbase z).mp hz).1).mp hm'.1
    exact h₁.symm.trans h₂
  have hf (b : Exponent) (_ : b ∈ (bases : Set Exponent)) : (fiber b).Finite :=
    (finite_weight d).subset fun _ hm => hm.2
  change {m : Exponent | m ∈ V \ U ∧ Finsupp.weight coxWeight m = d}.ncard =
    ∑ B ∈ bases.map enc, exponentCount B.exponents d
  rw [hEq, bases.finite_toSet.ncard_biUnion hf hdisj,
    finsum_mem_eq_finite_toFinset_sum _ bases.finite_toSet,
    Finset.finite_toSet_toFinset, Finset.sum_map]
  rfl
private def finiteDegLex (α : Type) [Fintype α] : MonomialOrder α := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' _ (Fintype.equivFin α).injective
  have : WellFoundedGT α := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
private def termOrder : MonomialOrder CoxVar := finiteDegLex CoxVar
private def leading (L : Layer) (d : Degree) : Set Exponent :=
  {m | ∃ p : Cox, p ∈ L d ∧ p ≠ 0 ∧ termOrder.degree p = m}
private def initial (L : Layer) : Set Exponent :=
  {m | m ∈ leading L (Finsupp.weight coxWeight m)}
private theorem leading_weight {L : Layer} {d : Degree} (hL : Stable L)
    {m : Exponent} (hm : m ∈ leading L d) : Finsupp.weight coxWeight m = d := by
  obtain ⟨p, hp, hp0, rfl⟩ := hm
  have hp' : p.IsWeightedHomogeneous coxWeight d := hL.1 d hp
  exact hp' (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0)
private theorem initial_upper {L : Layer} (hL : Stable L) : IsUpperSet (initial L) := by
  classical
  intro m n hmn hm
  obtain ⟨p, hp, hp0, hd⟩ := hm
  let q : Cox := monomial (n - m) 1
  have hq : q ∈ homogeneous (Finsupp.weight coxWeight (n - m)) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  have hq0 : q ≠ 0 := by simp [q]
  have he : Finsupp.weight coxWeight (n - m) + Finsupp.weight coxWeight m =
      Finsupp.weight coxWeight n := by
    rw [← map_add, tsub_add_cancel_of_le hmn]
  refine ⟨q * p, ?_, mul_ne_zero hq0 hp0, ?_⟩
  · rw [← he]
    exact hL.2 _ _ hq hp
  · rw [termOrder.degree_mul hq0 hp0, hd]
    simp only [q, termOrder.degree_monomial, one_ne_zero, ite_false, tsub_add_cancel_of_le hmn]
private theorem leading_finite {L : Layer} (hL : Stable L) (d : Degree) :
    (leading L d).Finite :=
  (finite_weight d).subset fun _ hm => leading_weight hL hm
private theorem mem_leading_iff {L : Layer} (hL : Stable L) {d : Degree} {m : Exponent} :
    m ∈ leading L d ↔ m ∈ initial L ∧ Finsupp.weight coxWeight m = d := by
  constructor
  · intro hm
    have hw := leading_weight hL hm
    exact ⟨show m ∈ leading L (Finsupp.weight coxWeight m) from hw.symm ▸ hm, hw⟩
  · rintro ⟨hm, hw⟩
    exact hw ▸ (show m ∈ leading L (Finsupp.weight coxWeight m) from hm)
private theorem independent_of_leading {σ K ι : Type} [Field K] [Fintype ι]
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0)
    (hd : Function.Injective fun i => m.degree (p i)) : LinearIndependent K p := by
  classical
  refine (Fintype.linearIndependent_iff (v := p)).mpr ?_
  intro w hw j
  by_contra hj
  let active : Finset ι := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i, hi, hmax⟩ := active.exists_max_image (fun a => m.toSyn (m.degree (p a)))
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let e := m.degree (p i)
  have hz := congrArg (lcoeff K e) hw
  simp only [map_sum, map_smul, map_zero] at hz
  change ∑ a : ι, w a * (p a).coeff e = 0 at hz
  rw [Finset.sum_eq_single i] at hz
  · exact (mul_ne_zero hwi (MonomialOrder.coeff_degree_ne_zero_iff.mpr (hp i))) hz
  · intro a _ hai
    by_cases ha : w a = 0
    · rw [ha, zero_mul]
    · have hle := hmax a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      have hlt := lt_of_le_of_ne hle (fun he => hai (hd (m.toSyn.injective he)))
      rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
  · simp
private theorem rank_leading {L : Layer} (hL : Stable L) (d : Degree) :
    Module.finrank FX (L d) = (leading L d).ncard := by
  classical
  let : Fintype (leading L d) := (leading_finite hL d).fintype
  let coeffs : L d →ₗ[FX] (leading L d → FX) :=
    LinearMap.pi fun i => (lcoeff FX i.val).comp (L d).subtype
  have hinj : Function.Injective coeffs := by
    intro u v huv
    apply sub_eq_zero.mp
    let p := u - v
    change p = 0
    have hz : coeffs p = 0 := (coeffs.map_sub u v).trans (sub_eq_zero.mpr huv)
    apply Subtype.ext
    by_contra hp
    have hp0 : (p : Cox) ≠ 0 := hp
    let i : leading L d := ⟨termOrder.degree (p : Cox), p, p.property, hp0, rfl⟩
    have hc : (p : Cox).coeff (termOrder.degree (p : Cox)) = 0 :=
      congrFun hz i
    exact (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0) hc
  have : Module.Finite FX (L d) := Module.Finite.of_injective coeffs hinj
  choose p hp hp0 hd using (fun i : leading L d => i.property)
  let v : leading L d → L d := fun i => ⟨p i, hp i⟩
  have he : Function.Injective (fun i => termOrder.degree (p i)) := by
    intro i j hij
    exact Subtype.ext ((hd i).symm.trans (hij.trans (hd j)))
  have hind : LinearIndependent FX v := by
    exact LinearIndependent.of_comp (v := v) (L d).subtype
      (independent_of_leading termOrder p hp0 he)
  rw [← Set.fintypeCard_eq_ncard]
  refine le_antisymm ?_ hind.fintype_card_le_finrank
  rw [← Module.finrank_pi FX]
  exact LinearMap.finrank_le_finrank_of_injective (f := coeffs) hinj
theorem initial_rank (A B : Layer) (hA : Stable A) (hB : Stable B) (hab : ∀ d, A d ≤ B d) :
    ∃ U V : Set Exponent, IsUpperSet U ∧ IsUpperSet V ∧ U ⊆ V ∧
      ∀ d, Module.finrank FX (A d) + exponentCount (V \ U) d =
        Module.finrank FX (B d) := by
  have hsub (d : Degree) : leading A d ⊆ leading B d := by
    rintro m ⟨p, hp, hp0, hd⟩
    exact ⟨p, hab d hp, hp0, hd⟩
  refine ⟨initial A, initial B, initial_upper hA, initial_upper hB,
    fun m hm => hsub (Finsupp.weight coxWeight m) hm, fun d => ?_⟩
  have he : {m | m ∈ initial B \ initial A ∧ Finsupp.weight coxWeight m = d} =
      leading B d \ leading A d := by
    ext m
    change (m ∈ initial B ∧ m ∉ initial A) ∧ Finsupp.weight coxWeight m = d ↔
      m ∈ leading B d ∧ m ∉ leading A d
    rw [mem_leading_iff hA, mem_leading_iff hB]
    tauto
  rw [rank_leading hA, rank_leading hB, exponentCount, he, add_comm]
  exact Set.ncard_sdiff_add_ncard_of_subset (hsub d) (leading_finite hB d)

end
end Rect51Hilbert
