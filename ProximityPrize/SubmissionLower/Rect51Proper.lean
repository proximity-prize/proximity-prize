import ProximityPrize.SubmissionLower.Rect51ProperTariff
import ProximityPrize.SubmissionLower.Rect51Point
import ProximityPrize.SubmissionLower.Rect51Budget
import ProximityPrize.SubmissionLower.Rect51HilbertCover
import ProximityPrize.SubmissionLower.Rect51TangentNodes

/-! Single-cut rectangular geometry from the public kaankolcu 69.50 note
f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 32
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Rect51Proper
noncomputable section

open P1 (K I node)
open K1_14 (FX)
open P1_7 (degreeAt quotientOrder ceilRatio)
open HighCore82706Tangent (Input ResidueLift Factors componentMarks rootOn card_le_cover)
open HighCore82706Tangent_3 (JetRing CurveMarks markPoint graphIdeal openFactor)
open HighCore82706Tangent_3_2 (cutoffIdeal cutoff_le_mark mark_regular graph_le_prime)
open Rect51Tangent (Axes SeedBound NodeSections)
open Rect51Point (Probe)
open Rect51Budget (feeAxis)
open Rect51MixedPoly (diagonal directionalCoeff)
open Finset Polynomial
open scoped Polynomial BigOperators
open private mark_seed_inj HighCore82706Tangent_3_2.jet_noetherian from ProximityPrize.SubmissionLower.HighCore82706TangentDeps
open private slope_le eval_affine from ProximityPrize.SubmissionLower.Rect51HilbertProbe
open private cut from ProximityPrize.SubmissionLower.Rect51MixedPoly

private theorem ceiling_mul {p q : ℕ} (hq : 0<q) : p≤ceilRatio p q*q := by
  unfold ceilRatio
  have hm := Nat.mod_lt (p+(q-1)) hq
  have he := Nat.div_add_mod (p+(q-1)) q
  rw [Nat.mul_comm q] at he
  omega

private theorem kappa_caps (J : Input) (v : Axes) :
    0<kappa J.hi (v 0) (v 1) ∧
    2*J.w≤kappa J.hi (v 0) (v 1)*max 1 (v 0) ∧
    2*J.w≤kappa J.hi (v 0) (v 1)*max 1 (v 1) := by
  unfold kappa
  refine ⟨lt_of_lt_of_le (by decide) (le_max_left _ _),?_,?_⟩
  · exact (Nat.mul_le_mul_left 2 J.upper).trans ((ceiling_mul (by omega)).trans
      (Nat.mul_le_mul_right _ ((le_max_left _ _).trans (le_max_right _ _))))
  · exact (Nat.mul_le_mul_left 2 J.upper).trans ((ceiling_mul (by omega)).trans
      (Nat.mul_le_mul_right _ ((le_max_right _ _).trans (le_max_right _ _))))

private theorem persistent_le (J : Input) {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) {v : Axes} (N : NodeSections C v) (h : 1<C.marks.card) :
    N.persistent.card≤degreeAt J.hi := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h
  let P := J.family.scalar a-J.family.scalar b
  have hp : P≠0 := sub_ne_zero.mpr fun he=>hab
    (J.family.distinct (J.marks_sub (C.sub ha)) (J.marks_sub (C.sub hb)) he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node
    ProximityPrize.Benchmark.IRSProfile.domain.injective P hp N.persistent ?_).trans ?_
  · intro x hx
    change (J.family.scalar a-J.family.scalar b).eval (node x)=0
    rw [eval_sub,N.hits a ha x hx,N.hits b hb x hx,sub_self]
  · have h := HighCore82706Tangent.fixed_word J C.sub
    exact (natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb))

private theorem section_points (J : Input) {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) {v : Axes} (N : NodeSections C v) (T : Probe C.prime)
    (he : 4≤J.e) (δ : ℕ) (hδ : (δ:ℚ)=T.mass (J.e-3) 1 (max 1 (v 0)) (max 1 (v 1)))
    (x : I) (hx : x∉N.persistent) :
    (C.marks.filter fun γ=>(J.family.scalar γ).eval (node x)=J.model.word x).card≤
      (J.ell-N.persistent.card+kappa J.hi (v 0) (v 1))*δ := by
  classical
  obtain ⟨S,hS,hzero⟩ := N.cuts x hx
  let U := C.marks.filter fun γ=>(J.family.scalar γ).eval (node x)=J.model.word x
  let r := J.ell-N.persistent.card
  let k := kappa J.hi (v 0) (v 1)
  have hpoints := Rect51Point.count_relative_section C.prime C.isPrime T S hS U (markPoint J)
    (mark_seed_inj J U) (fun γ hγ=>C.liesOn γ (mem_filter.mp hγ).1)
    (fun γ hγ=>hzero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have hk := kappa_caps J v
  have hw := Rect51Budget.feeAxis_le J (r:=r) he (le_max_right 1 (v 0)) (le_max_right 1 (v 1))
    hk.1 hk.2.1 hk.2.2
  have bound (i : Fin 4) : (feeAxis J v r i:ℚ) ≤
      ((r+k):ℚ)*(diagonal J.e (max 1 (v 0)) (max 1 (v 1)) i:ℚ) := by exact_mod_cast hw i
  have s0 := mul_le_mul_of_nonneg_right (bound 0) (T.nonnegative 0)
  have s1 := mul_le_mul_of_nonneg_right (bound 1) (T.nonnegative 1)
  have s2 := mul_le_mul_of_nonneg_right (bound 2) (T.nonnegative 2)
  have s3 := mul_le_mul_of_nonneg_right (bound 3) (T.nonnegative 3)
  change U.card≤(r+k)*δ
  apply (Nat.cast_le (α:=ℚ)).mp
  push_cast
  rw [hδ]
  unfold Probe.mass at *
  change (U.card:ℚ) ≤ (feeAxis J v r 0:ℚ)*T.coeff 0+
    (feeAxis J v r 1:ℚ)*T.coeff 1+(feeAxis J v r 2:ℚ)*T.coeff 2+
    (feeAxis J v r 3:ℚ)*T.coeff 3 at hpoints
  have eq0 : diagonal J.e (max 1 (v 0)) (max 1 (v 1)) 0=J.e-3 := rfl
  have eq1 : diagonal J.e (max 1 (v 0)) (max 1 (v 1)) 1=1 := rfl
  have eq2 : diagonal J.e (max 1 (v 0)) (max 1 (v 1)) 2=max 1 (v 0) := rfl
  have eq3 : diagonal J.e (max 1 (v 0)) (max 1 (v 1)) 3=max 1 (v 1) := rfl
  rw [eq0] at s0; rw [eq1] at s1; rw [eq2] at s2; rw [eq3] at s3
  nlinarith only [hpoints,s0,s1,s2,s3]

private theorem curve_charge (A : ℕ) (J : Input) {B : ResidueLift J} {D : Factors J B}
    (he : 4≤J.e) (hAn : A≤262144) (hd : degreeAt J.hi<A) (hL : quotientOrder J.lo≤A)
    (hhits : ∀ γ∈J.marks, ∃ T : Finset I, A≤T.card ∧
      ∀ i∈T,(J.family.scalar γ).eval (node i)=J.model.word i)
    (C : CurveMarks J B D) {v : Axes} (N : NodeSections C v) (T : Probe C.prime)
    (δ : ℕ) (hδpos : 0<δ)
    (hδ : (δ:ℚ)=T.mass (J.e-3) 1 (max 1 (v 0)) (max 1 (v 1))) :
    (A*(A-degreeAt J.hi))*C.marks.card ≤
      (262144*(A-degreeAt J.hi)*quotientOrder J.lo+
        A*(262144-degreeAt J.hi)*kappa J.hi (v 0) (v 1))*δ := by
  classical
  let d := degreeAt J.hi
  let L := quotientOrder J.lo
  let k := kappa J.hi (v 0) (v 1)
  have hJL : J.ell≤L := Nat.sub_le_sub_left J.lower _
  by_cases hsmall : C.marks.card≤1
  · have hLo : 1≤L := J.quotient_pos.trans_le hJL
    have hmul : A*(A-d)≤262144*(A-d)*L :=
      (Nat.mul_le_mul_right _ hAn).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (262144*(A-d)) hLo)
    change (A*(A-d))*C.marks.card ≤ (262144*(A-d)*L+A*(262144-d)*k)*δ
    calc
      _ ≤ (A*(A-d))*1 := Nat.mul_le_mul_left _ hsmall
      _ ≤ (262144*(A-d)*L+A*(262144-d)*k)*1 :=
        Nat.mul_le_mul_right _ (hmul.trans (Nat.le_add_right _ _))
      _ ≤ _ := Nat.mul_le_mul_left _ hδpos
  let s := N.persistent.card
  let r := J.ell-s
  let sites := (univ : Finset I) \ N.persistent
  let hit (γ : K) (x : I) := (J.family.scalar γ).eval (node x)=J.model.word x
  have hs : s≤d := persistent_le J C N (by omega)
  have hsites : sites.card=262144-s := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ]
    exact congrArg (· - s) ProximityPrize.Benchmark.IRSProfile.card_index
  have hagree (γ : K) (hγ : γ∈C.marks) : A-s≤(sites.filter (hit γ)).card := by
    obtain ⟨good,hgood,hh⟩ := hhits γ (C.sub hγ)
    have hsub : good \ N.persistent ⊆ sites.filter (hit γ) := by
      intro i hi
      obtain ⟨hi,hp⟩ := mem_sdiff.mp hi
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hp⟩,hh i hi⟩
    have hb := card_le_card hsub
    have hp := card_sdiff_add_card_eq_card (inter_subset_left : good∩N.persistent ⊆ good)
    have hc := card_le_card (inter_subset_right : good∩N.persistent ⊆ N.persistent)
    have hEq : good \ (good∩N.persistent)=good \ N.persistent := by
      ext x
      simp only [mem_sdiff,mem_inter]
      tauto
    rw [hEq] at hp
    omega
  apply Rect51Fee.scaled_node_charge (s:=s) (r:=r) (k:=k) (δ:=δ) hAn hd hL hs
    (Nat.sub_le_sub_right hJL _)
  calc
    (A-s)*C.marks.card = ∑ γ∈C.marks,(A-s) := by rw [sum_const,smul_eq_mul,Nat.mul_comm]
    _ ≤ ∑ γ∈C.marks,(sites.filter (hit γ)).card := sum_le_sum hagree
    _ = ∑ x∈sites,(C.marks.filter (fun γ=>hit γ x)).card := by
      simp only [card_filter]; rw [sum_comm]
    _ ≤ ∑ _x∈sites,(r+k)*δ :=
      sum_le_sum fun x hx=>section_points J C N T he δ hδ x (mem_sdiff.mp hx).2
    _ = (262144-s)*(r+k)*δ := by rw [sum_const,smul_eq_mul,hsites,Nat.mul_assoc]

theorem count (A : ℕ) (J : Input) (he : 4≤J.e) (hAn : A≤262144)
    (hd : degreeAt J.hi<A) (hL : quotientOrder J.lo≤A) {v : Axes}
    (hv : SeedBound J.f v)
    (hhits : ∀ γ∈J.marks, ∃ T : Finset I, A≤T.card ∧
      ∀ i∈T,(J.family.scalar γ).eval (node i)=J.model.word i)
    {B : ResidueLift J} (D : Factors J B) :
    (componentMarks J D.proper).card≤properFee A J.lo J.hi J.e (v 0) (v 1) := by
  classical
  let r := J.ell+1
  let b := max 1 (v 0)
  let c := max 1 (v 1)
  let k := kappa J.hi (v 0) (v 1)
  let L := quotientOrder J.lo
  let d := degreeAt J.hi
  let T := Classical.choice (Rect51Tangent.taylor_sections J B D hv r le_rfl)
  let E := Rect51Budget.sectionIdeal T
  let Bnd := cutoffIdeal J B D
  let onOpen : Set (Ideal JetRing) := {P | P∈Bnd.minimalPrimes ∧ openFactor J B∉P}
  letI : IsNoetherianRing JetRing := HighCore82706Tangent_3_2.jet_noetherian
  have hfin : onOpen.Finite :=
    Bnd.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h=>h.1)
  letI := hfin.fintype
  let n := Fintype.card onOpen
  let enumer := (Fintype.equivFin onOpen).symm
  let P (i : Fin n) : Ideal JetRing := (enumer i).val
  have hmin (i : Fin n) : Bnd.IsMinimalPrime (P i) := (enumer i).property.1
  have hreg (i : Fin n) : openFactor J B∉P i := (enumer i).property.2
  have hp (i : Fin n) : (P i).IsPrime := (hmin i).isPrime
  have hgraph (i : Fin n) : graphIdeal J B D≤P i :=
    graph_le_prime (hp i) (hmin i).le (hreg i)
  have hsection (i : Fin n) : E≤P i := by
    apply sup_le (hgraph i)
    rw [Ideal.span_singleton_le_iff_mem]
    exact (Rect51Tangent.cutoff_agrees T (P i) (hp i) (hgraph i) (hreg i)).mpr
      ((hmin i).le (Ideal.subset_span (by simp)))
  have hinc : Pairwise fun i j=>¬P i≤P j := by
    intro i j hij hle
    apply hij
    apply enumer.injective
    apply Subtype.ext
    exact le_antisymm hle ((hmin j).2 (hmin i).1 hle)
  let C (i : Fin n) : CurveMarks J B D := {
    prime := P i
    isPrime := hp i
    onGraph := hgraph i
    onCutoff := (hmin i).le (Ideal.subset_span (by simp))
    regular := hreg i
    marks := J.marks.filter (fun γ=>P i≤RingHom.ker (markPoint J γ).toRingHom)
    sub := filter_subset _ _
    liesOn := fun γ hγ=>(mem_filter.mp hγ).2 }
  obtain ⟨pE,hpE,hpEt,hdegree,hconstant,hlinear⟩ := Rect51Budget.cut_profile J B D he hv T b c
  let Te := Probe.ofProfile hpE hdegree hpEt
  have probe (i : Fin n) : ∃ U : Probe (P i), 0<U.mass (J.e-3) 1 b c := by
    obtain ⟨p,hp',ht'⟩ := Rect51Hilbert.profile_exists (P i)
    have hgap := Rect51Hilbert.inclusion_gap (hsection i) hpE hp'
    have hdeg := (cut hdegree ht' hgap).1
    let U := Probe.ofProfile hp' hdeg ht'
    have ht := HighCore82706Tangent_3_2_2.proof J B D (P i) (hmin i) (hreg i)
    exact ⟨U,U.mass_positive ht _ _ _ _ (by dsimp [b]; omega) (by dsimp [c]; omega)⟩
  choose V hV using probe
  choose δ hδ using (fun i=> (V i).mass_nat (J.e-3) 1 b c)
  have hδpos (i) : 0<δ i := by
    have hp := hV i
    rw [← hδ i] at hp
    exact_mod_cast hp
  have hsum := Rect51Point.probe_sums P V (Rect51Hilbert.separator_bound E P hp hinc hsection)
    Te.coeff (N:=Te.threshold) (offset:=Te.offset)
    (fun h t u v hh ht hu hv=>(Te.profile h t u v hh ht hu hv).le)
    (J.e-3) 1 b c
  change (∑ i,(V i).mass (J.e-3) 1 b c)≤Te.mass (J.e-3) 1 b c at hsum
  have hdiag : Te.mass (J.e-3) 1 b c≤
      directionalCoeff J.e (v 0) (v 1) b c (fun i=>feeAxis J v r i) := by
    apply slope_le (N:=0) (a:=pE.coeff 0) (b:=hconstant)
    intro m _
    have heq : (fun i=>(m:ℚ)*(diagonal J.e b c i:ℚ)) =
        ![((m*(J.e-3):ℕ):ℚ),(m:ℚ),((m*b:ℕ):ℚ),((m*c:ℕ):ℚ)] := by
      funext i
      fin_cases i <;> simp [diagonal,Nat.cast_mul]
    have hm := hlinear m
    rw [heq] at hm
    change Rect51Hilbert.evalHilbert pE (m*(J.e-3)) m (m*b) (m*c)≤_ at hm
    rw [eval_affine hdegree] at hm
    convert hm using 1
    · unfold Probe.mass
      simp only [Te,Probe.ofProfile]
      push_cast
      ring
  let G := Rect51Fee.graphDegree J.e (v 0) (v 1) b c
  have hJL : J.ell≤L := Nat.sub_le_sub_left J.lower _
  have hk := kappa_caps J v
  have hD : directionalCoeff J.e (v 0) (v 1) b c (fun i=>feeAxis J v r i)≤
      ((r+k)*G:ℕ) := by
    have hdom := Rect51Budget.feeAxis_le J (r:=r) he (le_max_right 1 (v 0))
      (le_max_right 1 (v 1)) hk.1 hk.2.1 hk.2.2
    have hd' := Rect51MixedPoly.direction_le J.e (v 0) (v 1) b c (by omega)
      (feeAxis J v r) (r+k) hdom
    have h3 : 3≤3*J.e := by omega
    have h4 : 4≤2*J.e := by omega
    simpa only [G,Rect51Fee.graphDegree,Nat.cast_sub h3,Nat.cast_sub h4,
      Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hd'
  have hδSum : (∑ i,δ i)≤G*(L+1+k) := by
    have hh : (∑ i,δ i)≤(r+k)*G := by
      apply (Nat.cast_le (α:=ℚ)).mp
      rw [Nat.cast_sum]
      simp_rw [hδ]
      exact hsum.trans (hdiag.trans hD)
    exact hh.trans (by
      rw [Nat.mul_comm (r+k) G]
      apply Nat.mul_le_mul_left G
      dsimp [r]
      omega)
  have hcover : ∀ γ∈componentMarks J D.proper,∃ i,γ∈(C i).marks := by
    intro γ hγ
    obtain ⟨hm,hr⟩ := HighCore82706Tangent.mem_componentMarks.mp hγ
    let ker := RingHom.ker (markPoint J γ).toRingHom
    letI : ker.IsPrime := RingHom.ker_isPrime (markPoint J γ).toRingHom
    obtain ⟨p,hp,hple⟩ := Ideal.exists_minimalPrimes_le (cutoff_le_mark J B D hm hr)
    let p' : onOpen := ⟨p,hp,fun h=>mark_regular J B hm (hple h)⟩
    refine ⟨enumer.symm p',mem_filter.mpr ⟨hm,?_⟩⟩
    change (enumer (enumer.symm p')).val≤ker
    rw [Equiv.apply_symm_apply]
    exact hple
  let Kf := 262144*(A-d)*L + A*(262144-d)*k
  have hlocal (i : Fin n) : (A*(A-d))*(C i).marks.card≤Kf*δ i := by
    let N := Classical.choice (Rect51Tangent.node_sections J B D hv (C i))
    exact curve_charge A J he hAn hd hL hhits (C i) N (V i) (δ i) (hδpos i) (hδ i)
  have hcard : (A*(A-d))*(componentMarks J D.proper).card≤Kf*(G*(L+1+k)) := by
    calc
      _ ≤ (A*(A-d))*(∑ i,(C i).marks.card) :=
        Nat.mul_le_mul_left _ (card_le_cover _ _ hcover)
      _ = ∑ i,(A*(A-d))*(C i).marks.card := Finset.mul_sum _ _ _
      _ ≤ ∑ i,Kf*δ i := Finset.sum_le_sum fun i _=>hlocal i
      _ = Kf*(∑ i,δ i) := (Finset.mul_sum _ _ _).symm
      _ ≤ Kf*(G*(L+1+k)) := Nat.mul_le_mul_left _ hδSum
  have hpos : 0<A*(A-d) := Nat.mul_pos (Nat.zero_lt_of_lt hd) (Nat.sub_pos_of_lt hd)
  apply P1_7_8.ratio_le_ceil hpos
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Kf,G,L,d,k,b,c,P1_7.degreeAt,P1_7.quotientOrder] using hcard

#print axioms count
end
end Rect51Proper
