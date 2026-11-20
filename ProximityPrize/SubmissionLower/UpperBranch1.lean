import ProximityPrize.SubmissionLower.GoldBranch6N8
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1
noncomputable section
open P1 (AnchorModel AnchoredFamily K p)
open P1_7 (AdjacentChart)
open K1_14 (L liftPoly)
open K1_14_1 Polynomial
open scoped Polynomial
theorem chart_poles {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      fun i => by fin_cases i <;> first | exact hm | exact hm',
      fun i => by fin_cases i <;> first | exact hd | exact hd',
      hcop, fun i => by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
end
end P1_7_1
end
section
namespace P1_7_1
open K1_14 (Shape shapeSum)
open scoped BigOperators
def poleRows (s : Shape) : ℕ :=
  shapeSum s (fun q _ => s.B + s.J - q)
def nodeRows (s : Shape) : ℕ :=
  262144 * shapeSum s (fun q j => s.m + min q s.J - (q + 2*j))
def columnCount (B J t q : ℕ) : ℕ :=
  let low := J - t
  let high := min J (B + 2*J - 1 - t)
  min q high + 1 - low
def pivotCount (B J t q : ℕ) : ℕ :=
  min (columnCount B J t q) (B + 2*J - (t + q))
def largestGradeSum (B J t R : ℕ) : ℕ :=
  (Finset.range (B+1)).inf' Finset.nonempty_range_add_one fun k =>
    R*k + ∑ q ∈ Finset.range (B+1), (q-k) * columnCount B J t q
def offsetMoment (B J t : ℕ) : ℕ :=
  let R := ∑ q ∈ Finset.range (B+1), pivotCount B J t q
  largestGradeSum B J t R - ∑ q ∈ Finset.range (B+1), q * pivotCount B J t q
def groupedPoleMoment (B J : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (B+2*J), offsetMoment B J t
end P1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P1_7_1
noncomputable section
open K1 (I)
open K1_14 (L FX Shape)
open K1_14_1 Polynomial
open scoped Polynomial BigOperators
open private leading_forward from ProximityPrize.SubmissionLower.Fast065
open private boundaryMap boundary_rank_le strict_of_ker ker_step_le from ProximityPrize.SubmissionLower.Fast065
private theorem zero_of_strict_cutoff {h} (hhi : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (s : Shape) (P : Source) (hp : P ∈ poleSpace Crt s)
    (hs : ∀ j i a e, coeffAt P j i a e ≠ 0 →
      a+(i+j)*(131071+h) < (s.B+s.J)*(2*h)+j) : P = 0 := by
  by_contra hP
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  let g := P.leadingCoeff.leadingCoeff
  have hg : g ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  obtain ⟨e, he⟩ : ∃ e, g.leadingCoeff.coeff e ≠ 0 := by
    by_contra! hh
    exact (leadingCoeff_ne_zero.mpr hg) (MvPolynomial.eq_zero_iff.mpr hh)
  have hcoeff : coeffAt P j i g.natDegree e ≠ 0 := by
    simpa [coeffAt, j, i, g, coeff_natDegree] using he
  have hlt := hs j i g.natDegree e hcoeff
  let H := rawBlock D
  have hm : H.Monic := ((D.monic 0).mul (D.monic 1)).map _
  have hd : H.natDegree = 2*h := K1_14_1_4.rawBlock_degree D
  have hinj : Function.Injective (algebraMap SeedPoly SeedField) :=
    IsFractionRing.injective SeedPoly SeedField
  have hg' : genericCoefficients g ≠ 0 := Polynomial.map_ne_zero_iff hinj |>.2 hg
  have hdeg : (genericCoefficients g).natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hinj g
  obtain ⟨Q, hQ⟩ := hp
  have hdvd : H^(s.B+s.J) ∣ genericCoefficients g * H^(i+j) := by
    refine ⟨(Q.coeff j).coeff i, ?_⟩
    have hc := congrArg (fun R : RawSource => (R.coeff j).coeff i) hQ
    change ((forward Crt P).coeff j).coeff i = _ at hc
    have hlead := leading_forward Crt P
    dsimp only at hlead
    rw [show j = P.natDegree from rfl, show i = P.leadingCoeff.natDegree from rfl, hlead] at hc
    simpa only [jetConstant, RingHom.comp_apply, coeff_C_mul, H, i, j, g] using hc
  have hlo := natDegree_le_of_dvd hdvd (mul_ne_zero hg' (pow_ne_zero _ hm.ne_zero))
  rw [natDegree_mul hg' (pow_ne_zero _ hm.ne_zero), hdeg, natDegree_pow, natDegree_pow, hd] at hlo
  have hweights : (i+j)*(131071+h) = (i+j)*(2*h) + (i+j)*(131071-h) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hj : j ≤ (i+j)*(131071-h) := (Nat.le_add_left j i).trans
    (by simpa using Nat.mul_le_mul_left (i+j) (show 1 ≤ 131071-h by omega))
  rw [hweights] at hlt
  omega
private theorem ker_zero {h} (hhi : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) (s : Shape) : (boundaryMap Crt word s 0).ker = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply zero_of_strict_cutoff hhi Crt s P P.property.2
  intro j i a e hn
  simpa only [zero_add] using strict_of_ker ⟨P, hP⟩ hn
theorem telescope {h : ℕ} (hraw : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (complete Crt word s W) ≤
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t) := by
  induction W with
  | zero =>
    have hr := (boundaryMap Crt word s 0).finrank_range_add_finrank_ker
    rw [ker_zero hraw Crt word s, finrank_bot, add_zero] at hr
    simpa [← hr] using boundary_rank_le Crt word s 0
  | succ W ih =>
    rw [Finset.sum_range_succ]
    have hr := (boundaryMap Crt word s (W+1)).finrank_range_add_finrank_ker
    have ha := boundary_rank_le Crt word s (W+1)
    have hb := ker_step_le Crt word s W
    omega
end
end P1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P1_7_1
noncomputable section
open Polynomial
open K1_14 (L FX Shape liftPoly triangle)
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open P1 (K I)
open P1_7 (Listed)
open scoped BigOperators Polynomial
open private poleTest_of_local from ProximityPrize.SubmissionLower.Fast065
open private regular_deformation from ProximityPrize.SubmissionLower.PortHighBase
def c1 : Prop :=
  ∀ (F : Type) [Field F] [CharP F K1.p] (s : Shape),
    s.B < K1.p →
    ∀ (H : F[X]) (lift : (SeedFrac F)[X])
      (α : F) (side : Fin 2) (a b c : F),
      H.eval α = 0 → H.derivative.eval α ≠ 0 → b ≠ 0 →
      lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c →
      ∃ d : Fin (poleRows s) → ℕ,
        (∑ r, d r) ≤ groupedPoleMoment s.B s.J ∧
        ∃ tests : Fin (poleRows s) → TrueSource F →ₗ[F] Seed F,
          (∀ r P, Shaped s P → SeedWindow s.U (d r) side (tests r P)) ∧
          ∀ P, Shaped s P → (∀ r, tests r P = 0) →
            (jetConstant ((Polynomial.X (R := SeedFrac F) -
                Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
              JetPolys (SeedFrac F)) ∣ forward H lift P
def c2 : Prop :=
  ∀ (b : P1.HighBand) (t : P1_7.Bank), Listed b t → nodeRows t.shape ≤ t.nodeRows
def c3 : Prop :=
  ∀ (b : P1.HighBand) (t : P1_7.Bank), Listed b t →
    groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p
private abbrev ScalarRow {h : ℕ} (s : Shape) (d : Fin (2*h) → Fin (poleRows s) → ℕ) :=
  Σ t : Fin (2*h), Σ r : Fin (poleRows s), Fin (triangle s.U + (s.U+1)*d t r)
private theorem scalarRow_card_le {h : ℕ} (s : Shape)
    (d : Fin (2*h) → Fin (poleRows s) → ℕ) (hd : ∀ t, (∑ r, d t r) ≤ groupedPoleMoment s.B s.J) :
    Fintype.card (ScalarRow s d) ≤ poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
  classical
  simp only [ScalarRow, Fintype.card_sigma, Fintype.card_fin]
  calc
    (∑ t : Fin (2*h), ∑ r : Fin (poleRows s), (triangle s.U + (s.U+1)*d t r)) ≤
        ∑ _ : Fin (2*h), (poleRows s * triangle s.U + (s.U+1)*groupedPoleMoment s.B s.J) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _ = poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (2*h)*(poleRows s * triangle s.U + (s.U+1)*groupedPoleMoment s.B s.J) = _
      unfold poleCredit poleRows
      ring
private theorem simple_rank_le (hlocal : c1)
    {F ι : Type} [Field F] [CharP F K1.p] [Fintype ι] {h : ℕ}
    {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (s : Shape) (hs : s.B < K1.p) (P : ι → TrueSource F)
    (hP : ∀ k, Shaped s (P k)) {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
  classical
  have ht (t : Fin (2*h)) := hlocal F s hs H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.vanishes t) (G.simple t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  have hread (t : Fin (2*h)) (r : Fin (poleRows s)) := seedWindow_read F s.U (d t r) (G.side t)
  choose read hread using hread
  let f : (ι → F) →ₗ[F] (ScalarRow s d → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    have hv' := shaped_combination hP v
    apply htest t _ hv'
    intro r
    apply hread t r _ (hwindow t r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤
      poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
    refine (LinearMap.range f).finrank_le.trans ?_
    rw [Module.finrank_pi]
    exact scalarRow_card_le s d hd
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega
private theorem pole_bound (hlocal : c1) {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (hs : s.B < K1.p) (W : ℕ) :
    Module.finrank L (contacted h word s W) ≤
      poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J +
        Module.finrank L (complete Crt word s W) := by
  classical
  obtain ⟨E⟩ := regular_deformation hpos hchar D Crt
  let A := contacted h word s W
  let _ : Module.Finite L A := contacted_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property
  obtain ⟨n, M, hspecial, hg⟩ := K1_14_1_7_4.proof E s (Fin d) P hP
  let embed := genericPoint.comp (Polynomial.C (R := L))
  let _ : CharP L K1.p := charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _ : CharP GenericField K1.p :=
    charP_of_injective_ringHom (f := embed) (generic_injective.comp Polynomial.C_injective) K1.p
  have hgen := simple_rank_le hlocal E.genericPoles s hs _
    (fun k => shaped_map embed (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ complete Crt word s W := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete Crt word s W => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega
theorem of_children (hlocal : c1) (hnodeRows : c2) (hmoment : c3) : P1_7.c1 := by
  intro b u del M Γ F hband _ H hH
  let h := M.overhead.toNat
  have hg := P1_7.terminal_guards b
  have hlo : 0 < h := by
    obtain ⟨hlo, _⟩ := hband
    have := hg.1
    dsimp [h]
    omega
  have hhi : h ≤ 33327 := by
    obtain ⟨_, hhi⟩ := hband
    have := hg.2.1
    dsimp [h]
    omega
  have hraw : h ≤ 131070 := hhi.trans (by decide)
  have hchar : h < K1.p := hhi.trans_lt (by decide)
  obtain ⟨D, hnode, hres⟩ := chart_poles M F H hH
  obtain ⟨Crt⟩ := P0_10_1.crt_lift D
  let word : I → L := fun i => algebraMap K L (M.word i)
  refine ⟨evaluated Crt word, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t _ t' _ hm hB hJ hU W W' hW
    exact evaluated_mono Crt word hm hB hJ hU hW
  · intro t _ W hW P hP γ hγ
    let B := F.mark γ hγ
    have hdegree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + h := by
      rw [liftPoly, Polynomial.natDegree_map]
      rcases B.scalar_degree with hzero | hd
      · simp [hzero]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        dsimp [h]
        omega
    refine P0_10_1.contact_vanish Crt word hnode _ _ (hres γ hγ) hdegree B.bad.support
      B.bad.agreement ?_ t.shape W hW P hP
    intro i hit
    rw [liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom, B.scalar_hits i hit]
  · intro t _ W P hP j i hne
    exact evaluated_shape Crt word hP j i hne
  · intro t _ W P hP hne
    exact P0_10_1.leading_bound hlo hraw Crt word t.shape W P hP hne
  · intro t _ W P hP i r
    exact P0_10_1.evaluated_shift Crt word hP i r
  · intro t ht W _ hW
    obtain ⟨hm, hB⟩ := hmoment b t ht
    have hvol := P0_10_1.ambient_bound (hraw.trans (by decide)) t.shape W hW
    have hcontact := P0_10_1.physical_bound h word t.shape W
    have hpole := pole_bound hlocal hlo hchar Crt word t.shape hB W
    have hsum := telescope hraw Crt word t.shape W
    have hphys : physicalDebit t.shape ≤ triangle t.shape.U * t.nodeRows := by
      have he : physicalDebit t.shape = triangle t.shape.U * nodeRows t.shape := by
        unfold physicalDebit nodeRows
        rw [Nat.mul_assoc]
      rw [he]
      exact Nat.mul_le_mul_left _ (hnodeRows b t ht)
    have hextra := Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hm
    change rawVolumeAt h t.shape W ≤
      (triangle t.shape.U * t.nodeRows + 2*h*(t.shape.U+1)*t.poleMoment) +
        ∑ w ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word t.shape w)
    omega
end
end P1_7_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open Polynomial
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount pivotCount)
open scoped BigOperators Polynomial
abbrev Offset (s : Shape) := Fin (s.B + 2*s.J)
def firstJet (s : Shape) (t : Offset s) : ℕ := s.J - t.val
def outputLength (s : Shape) (t : Offset s) (q : Grade s) : ℕ :=
  s.B + 2*s.J - (t.val + q.val)
abbrev Column (s : Shape) (t : Offset s) :=
  Σ q : Grade s, Fin (columnCount s.B s.J t.val q.val)
abbrev Pivot (s : Shape) (t : Offset s) :=
  Σ q : Grade s, Fin (pivotCount s.B s.J t.val q.val)
def columnJet {s : Shape} {t : Offset s} (u : Column s t) : ℕ :=
  firstJet s t + u.2.val
def columnOrder {s : Shape} {t : Offset s} (u : Column s t) : ℕ :=
  t.val + columnJet u - s.J
def pascal {R : Type} [Semiring R] (l n h : ℕ) :
    Matrix (Fin (min n h)) (Fin n) R :=
  fun i j => ((l + j.val).choose i.val : R)
def PascalSpans (F : Type) [Field F] (l n h : ℕ) : Prop :=
  ∀ i < h, ∃ w : Fin (min n h) → F, ∀ j : Fin n,
    ((l + j.val).choose i : F) = ∑ r, w r * pascal l n h r j
def PascalMinor (F : Type) [Field F] (l n h : ℕ) : Prop :=
  ∃ e : Fin (min n h) ↪ Fin n,
    ((pascal (R := F) l n h).submatrix id e).det ≠ 0
def poleMatrix {R : Type} [CommSemiring R] (s : Shape) (t : Offset s) (z : R) :
    Matrix (Pivot s t) (Column s t) R :=
  fun r u =>
    let j := columnJet u
    if r.1.val ≤ u.1.val ∧ j ≤ r.1.val then
      ((j.choose r.2.val : R) * ((u.1.val - j).choose (r.1.val - j) : R)) *
        z ^ (u.1.val - r.1.val)
    else 0
def input {F : Type} [Field F] (α : F) {s : Shape} {t : Offset s} (u : Column s t) :
    TrueSource F →ₗ[F] Seed F :=
  inputTaylorCoeff α (columnJet u) (u.1.val - columnJet u) (columnOrder u)
abbrev OneSeedFrac (F : Type) [Field F] := FractionRing F[X]
def oneResidue {F : Type} [Field F] (a b c : F) : OneSeedFrac F :=
  let z := algebraMap F[X] (OneSeedFrac F) Polynomial.X
  algebraMap F (OneSeedFrac F) a * z /
    (algebraMap F (OneSeedFrac F) b + algebraMap F (OneSeedFrac F) c * z)
def BoundedMinors {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ (OneSeedFrac F)) (D : ℕ) : Prop :=
  (∃ e : ι ↪ κ, (M.submatrix id e).det ≠ 0) ∧
  ∃ scale : OneSeedFrac F, scale ≠ 0 ∧
    ∀ e : ι ↪ κ, ∃ g : F[X], g.natDegree ≤ D ∧
      algebraMap F[X] (OneSeedFrac F) g = scale * (M.submatrix id e).det
end
end P1_7_1_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open K1_14 (Shape shapeSum)
open K1_14_1_7 (Grade GradeSlot LocalRow)
open P1_7_1 (columnCount pivotCount poleRows groupedPoleMoment)
open scoped BigOperators
theorem jet_bounds (s : Shape) (t : Offset s) (q : Grade s) (i : ℕ)
    (hi : i < columnCount s.B s.J t.val q.val) :
    firstJet s t + i ≤ min q.val s.J ∧
      t.val + (firstJet s t + i) - s.J < s.B + s.J := by
  change i < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 -
    (s.J - t.val) at hi
  have hq : min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) ≤ q.val := min_le_left ..
  have hj := (min_le_right q.val _).trans (min_le_left s.J (s.B + 2*s.J - 1 - t.val))
  have ht := (min_le_right q.val _).trans (min_le_right s.J (s.B + 2*s.J - 1 - t.val))
  have htl : t.val < s.B + 2*s.J := t.isLt
  unfold firstJet
  rw [le_min_iff]
  omega
private abbrev AllPivots (s : Shape) := Σ t : Offset s, Pivot s t
private abbrev AllLocalRows (s : Shape) := Σ q : Grade s, LocalRow s q.val
private def toLocal (s : Shape) (r : AllPivots s) : AllLocalRows s :=
  let t := r.1
  let q := r.2.1
  let i := r.2.2.val
  let j := firstJet s t + i
  let x := t.val + j - s.J
  have hi : i < min (columnCount s.B s.J t.val q.val) (outputLength s t q) := r.2.2.isLt
  have hj := (jet_bounds s t q i (hi.trans_le (min_le_left ..))).1
  have hrow : x < s.B + s.J - q.val := by
    have h := hi.trans_le (min_le_right _ _)
    have hjJ := hj.trans (min_le_right _ _)
    have hq := q.isLt
    dsimp [x, j, firstJet, outputLength] at *
    omega
  ⟨q, ⟨x, hrow⟩, ⟨j, Nat.lt_succ_of_le hj⟩⟩
private theorem toLocal_injective (s : Shape) : Function.Injective (toLocal s) := by
  rintro ⟨t, q, i⟩ ⟨t', q', i'⟩ h
  have hq : q = q' := congrArg Sigma.fst h
  have hx := congrArg (fun y : AllLocalRows s => y.2.1.val) h
  have hj := congrArg (fun y : AllLocalRows s => y.2.2.val) h
  change t.val + (firstJet s t + i.val) - s.J =
    t'.val + (firstJet s t' + i'.val) - s.J at hx
  change firstJet s t + i.val = firstJet s t' + i'.val at hj
  have ht : t = t' := by
    apply Fin.ext
    unfold firstJet at hx hj
    omega
  subst t'
  subst q'
  have hi : i = i' := Fin.ext (by omega)
  subst i'
  rfl
private theorem toLocal_surjective (s : Shape) : Function.Surjective (toLocal s) := by
  rintro ⟨q, x, j⟩
  have hq := q.isLt
  have hx := x.isLt
  have hj : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
  have hjq := hj.trans (min_le_left _ _)
  have hjJ := hj.trans (min_le_right _ _)
  let t : Offset s := ⟨x.val + s.J - j.val, by omega⟩
  have ht : t.val + j.val = x.val + s.J := by dsimp [t]; omega
  have hfirst : firstJet s t ≤ j.val := by unfold firstJet; omega
  let i := j.val - firstJet s t
  have hji : firstJet s t + i = j.val := by dsimp [i]; omega
  have hhigh : j.val ≤ s.B + 2*s.J - 1 - t.val := by omega
  have hcol : i < columnCount s.B s.J t.val q.val := by
    unfold columnCount
    change i < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 - firstJet s t
    have hmin := le_min hjq (le_min hjJ hhigh)
    omega
  have hrow : i < outputLength s t q := by
    unfold outputLength
    unfold firstJet at hji
    omega
  let r : AllPivots s := ⟨t, q, ⟨i, lt_min hcol hrow⟩⟩
  refine ⟨r, Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext ?_) (Fin.ext ?_)))⟩
  · change t.val + (firstJet s t + i) - s.J = x.val
    omega
  · exact hji
private theorem allPivots_card (s : Shape) :
    Fintype.card (AllPivots s) = poleRows s := by
  classical
  rw [Fintype.card_congr (Equiv.ofBijective _ ⟨toLocal_injective s, toLocal_surjective s⟩)]
  simp only [AllLocalRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    poleRows, shapeSum]
  rw [Fin.sum_univ_eq_sum_range (fun q => (s.B + s.J - q) * (min q s.J + 1)) (s.B+1)]
  apply Finset.sum_congr rfl
  intro q _
  simp [Nat.mul_comm]
def rowIndex (s : Shape) : Fin (poleRows s) ≃ AllPivots s :=
  (Fintype.equivFinOfCardEq (allPivots_card s)).symm
theorem rowIndex_sum (s : Shape) (d : ∀ t : Offset s, Pivot s t → ℕ)
    (hd : ∀ t, (∑ r, d t r) ≤ P1_7_1.offsetMoment s.B s.J t.val) :
    (∑ k, d (rowIndex s k).1 (rowIndex s k).2) ≤ groupedPoleMoment s.B s.J := by
  calc
    _ = ∑ k : AllPivots s, d k.1 k.2 :=
      Fintype.sum_equiv (rowIndex s) _ _ (fun _ => rfl)
    _ = ∑ t : Offset s, ∑ r, d t r := Fintype.sum_sigma _
    _ ≤ ∑ t : Offset s, P1_7_1.offsetMoment s.B s.J t.val :=
      Finset.sum_le_sum fun t _ => hd t
    _ = _ := Fin.sum_univ_eq_sum_range _ _
end
end P1_7_1_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open Matrix
open scoped BigOperators Matrix
private def consecutive {R : Type} [Semiring R] (l m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => ((l + j.val).choose i.val : R)
private theorem consecutive_det {R : Type} [CommRing R] (l m : ℕ) :
    (consecutive (R := R) l m).det = 1 := by
  let L : Matrix (Fin m) (Fin m) R := fun i k =>
    if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0
  let U : Matrix (Fin m) (Fin m) R := fun k j => (j.val.choose k.val : R)
  have hLU : consecutive l m = L * U := by
    ext i j
    rw [Matrix.mul_apply]
    change ((l + j.val).choose i.val : R) =
      ∑ k : Fin m,
        (if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0) *
          (j.val.choose k.val : R)
    rw [Nat.add_comm l j.val, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum,
      Fin.sum_univ_eq_sum_range (fun k =>
        (if k ≤ i.val then (l.choose (i.val - k) : R) else 0) * (j.val.choose k : R)) m]
    calc
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (if k ≤ i.val then (l.choose (i.val - k) : R) else 0) * (j.val.choose k : R) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), mul_comm]
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
        intro k _ hk
        have hki : ¬ k ≤ i.val := fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
        simp [hki]
  have hL : L.IsLowerTriangular := by
    intro i k hik
    change (if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0) = 0
    exact ite_eq_right (not_le_of_gt (show i.val < k.val from hik))
  have hU : U.IsUpperTriangular := by
    intro i j hij
    change (j.val.choose i.val : R) = 0
    rw [Nat.choose_eq_zero_of_lt (show j.val < i.val from hij), Nat.cast_zero]
  rw [hLU, Matrix.det_mul, Matrix.det_of_isLowerTriangular L hL, Matrix.det_of_isUpperTriangular hU]
  simp [L, U]
theorem pascal_minor (F : Type) [Field F] (l n h : ℕ) : PascalMinor F l n h := by
  let e : Fin (min n h) ↪ Fin n := Fin.castLEEmb (min_le_left n h)
  refine ⟨e, ?_⟩
  change (consecutive (R := F) l (min n h)).det ≠ 0
  rw [consecutive_det]
  exact one_ne_zero
theorem pascal_spans (F : Type) [Field F] (l n h : ℕ) : PascalSpans F l n h := by
  classical
  intro i hi
  unfold pascal
  by_cases hle : h ≤ n
  · rw [min_eq_right hle]
    let k : Fin h := ⟨i, hi⟩
    refine ⟨fun r => if r = k then 1 else 0, fun j => ?_⟩
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [k]
    · intro r _ hne
      simp [hne]
  · rw [min_eq_left (le_of_not_ge hle)]
    let B := consecutive (R := F) l n
    have hB : B.det = 1 := consecutive_det l n
    let : Invertible B := B.invertibleOfIsUnitDet (hB.symm ▸ isUnit_one)
    let v : Fin n → F := fun j => ((l + j.val).choose i : F)
    refine ⟨v ᵥ* ⅟B, fun j => ?_⟩
    change v j = ((v ᵥ* ⅟B) ᵥ* B) j
    rw [Matrix.vecMul_vecMul, invOf_mul_self, Matrix.vecMul_one]
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 (Grade)
open P1_7_1 (columnCount pivotCount largestGradeSum offsetMoment)
open scoped BigOperators Matrix Polynomial
private def minorGrade {s : Shape} {t : Offset s} (e : Pivot s t ↪ Column s t) : ℕ :=
  (∑ r, (e r).1.val) - ∑ r : Pivot s t, r.1.val
private theorem minorGrade_le {s : Shape} {t : Offset s} (e : Pivot s t ↪ Column s t) :
    minorGrade e ≤ offsetMoment s.B s.J t.val := by
  classical
  have hpivot : (∑ r : Pivot s t, r.1.val) =
      ∑ q ∈ Finset.range (s.B+1), q * pivotCount s.B s.J t.val q := by
    simp only [Pivot, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id]
    rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount s.B s.J t.val q * q) (s.B+1)]
    simp only [Nat.mul_comm (pivotCount s.B s.J t.val _) _]
  unfold minorGrade offsetMoment
  rw [hpivot]
  apply Nat.sub_le_sub_right
  unfold largestGradeSum
  apply Finset.le_inf'
  intro k _
  have hexcess :
      (∑ r, ((e r).1.val - k)) ≤ ∑ u : Column s t, (u.1.val - k) := by
    calc
      _ = ∑ u ∈ Finset.univ.map e, (u.1.val - k) :=
        (Finset.sum_map (Finset.univ : Finset (Pivot s t)) e (fun u => u.1.val - k)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros
        positivity)
  calc
    (∑ r, (e r).1.val) ≤ ∑ r, (k + ((e r).1.val - k)) :=
      Finset.sum_le_sum fun r _ => by omega
    _ ≤ Fintype.card (Pivot s t) * k + ∑ u : Column s t, (u.1.val - k) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.add_le_add_left hexcess _
    _ = _ := by
      simp only [Pivot, Column, Fintype.sum_sigma, Fintype.card_sigma, Fintype.card_fin,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount s.B s.J t.val q) (s.B+1),
        Fin.sum_univ_eq_sum_range (fun q => columnCount s.B s.J t.val q * (q-k)) (s.B+1)]
      simp only [Nat.mul_comm (columnCount s.B s.J t.val _) (_ - _)]
private theorem minor_power {R : Type} [CommRing R] {s : Shape} {t : Offset s}
    (e : Pivot s t ↪ Column s t) (z : R) :
    ((poleMatrix s t z).submatrix id e).det =
      ((poleMatrix s t (1 : R)).submatrix id e).det * z ^ minorGrade e := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply, id_eq, mul_assoc]
  congr 1
  by_cases hgood : ∀ i, (σ i).1.val ≤ (e i).1.val
  · have he (i : Pivot s t) :
        poleMatrix s t z (σ i) (e i) = poleMatrix s t (1 : R) (σ i) (e i) *
          z ^ ((e i).1.val - (σ i).1.val) := by
      by_cases hj : columnJet (e i) ≤ (σ i).1.val <;> simp [poleMatrix, hgood i, hj]
    have hw : (∑ i, ((e i).1.val - (σ i).1.val)) = minorGrade e := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hgood i), minorGrade,
        Equiv.sum_comp σ (fun r : Pivot s t => r.1.val)]
    simp only [he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  · push Not at hgood
    obtain ⟨i, hi⟩ := hgood
    have hz (v : R) : poleMatrix s t v (σ i) (e i) = 0 := by
      simp [poleMatrix, not_le_of_gt hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz z),
      Finset.prod_eq_zero (Finset.mem_univ i) (hz 1), zero_mul]
private theorem nonzero_minor {R : Type} [Field R] (s : Shape) (t : Offset s) (z : R) :
    ∃ e : Pivot s t ↪ Column s t, ((poleMatrix s t z).submatrix id e).det ≠ 0 := by
  classical
  have h (q : Grade s) := pascal_minor R (firstJet s t) (columnCount s.B s.J t.val q.val)
    (outputLength s t q)
  choose eq hEq using h
  let e : Pivot s t ↪ Column s t := ⟨fun r => ⟨r.1, eq r.1 r.2⟩, by
    rintro ⟨q, i⟩ ⟨q', j⟩ hh
    have hq : q = q' := congrArg Sigma.fst hh
    subst q'
    have heq : eq q i = eq q j := eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
    exact congrArg (Sigma.mk q) ((eq q).injective heq)⟩
  let A := (poleMatrix s t z).submatrix id e
  have htri : A.BlockTriangular (fun r => r.1) := by
    intro i j hij
    change poleMatrix s t z i (e j) = 0
    have hlt : (e j).1.val < i.1.val := hij
    simp [poleMatrix, not_le_of_gt hlt]
  refine ⟨e, ?_⟩
  change A.det ≠ 0
  rw [htri.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  let f : Fin (pivotCount s.B s.J t.val q.val) ≃ {r : Pivot s t // r.1 = q} :=
    Equiv.ofBijective (fun j => ⟨⟨q, j⟩, rfl⟩) (by
      constructor
      · intro i j hh
        exact eq_of_heq ((Sigma.mk.inj_iff.mp (congrArg Subtype.val hh)).2)
      · rintro ⟨⟨q', j⟩, hq⟩
        change q' = q at hq
        subst q'
        exact ⟨j, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self f]
  have hblock : ((A.toSquareBlock (fun r => r.1) q).submatrix f f) =
      (pascal (R := R) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)).submatrix id (eq q) := by
    ext i j
    have hj := ((jet_bounds s t q (eq q j).val (eq q j).isLt).1).trans (min_le_left _ _)
    change poleMatrix s t z ⟨q, i⟩ ⟨q, eq q j⟩ =
      ((firstJet s t + (eq q j).val).choose i.val : R)
    simp [poleMatrix, columnJet, hj]
  rw [hblock]
  exact hEq q
set_option maxHeartbeats 600000 in
theorem bounded_pole_minors (F : Type) [Field F] (s : Shape) (t : Offset s) (a b c : F)
    (hb : b ≠ 0) :
    BoundedMinors (poleMatrix s t (oneResidue a b c)) (offsetMoment s.B s.J t.val) := by
  let δ := offsetMoment s.B s.J t.val
  let N : F[X] := C a * Polynomial.X
  let D : F[X] := C b + C c * Polynomial.X
  let f := algebraMap F[X] (OneSeedFrac F)
  have hc (u : F) : f (C u) = algebraMap F (OneSeedFrac F) u :=
    (IsScalarTower.algebraMap_apply F F[X] (OneSeedFrac F) u).symm
  have hD : D ≠ 0 := by
    intro hz
    apply hb
    simpa [D] using congrArg (fun p : F[X] => p.coeff 0) hz
  have hDf : f D ≠ 0 := by
    simpa only [f, map_zero] using (IsFractionRing.injective F[X] (OneSeedFrac F)).ne hD
  have hz : oneResidue a b c = f N / f D := by
    simp only [oneResidue, N, D, map_mul, map_add, hc]
    rfl
  have hNdeg : N.natDegree ≤ 1 :=
    (Polynomial.natDegree_mul_le (p := C a) (q := Polynomial.X)).trans (by simp)
  have hDdeg : D.natDegree ≤ 1 := by
    unfold D
    rw [Polynomial.natDegree_C_add]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  refine ⟨nonzero_minor s t _, f D ^ δ, pow_ne_zero _ hDf, ?_⟩
  intro e
  let d := minorGrade e
  let m := ((poleMatrix s t (1 : F)).submatrix id e).det
  have hd : d ≤ δ := minorGrade_le e
  let g := C m * N ^ d * D ^ (δ-d)
  refine ⟨g, ?_, ?_⟩
  · have hNd : (N ^ d).natDegree ≤ d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left d hNdeg)
    have hDd : (D ^ (δ-d)).natDegree ≤ δ-d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (δ-d) hDdeg)
    have hg := Polynomial.natDegree_mul_le (p := C m * N ^ d) (q := D ^ (δ-d))
    have hm := Polynomial.natDegree_mul_le (p := C m) (q := N ^ d)
    rw [Polynomial.natDegree_C, zero_add] at hm
    change (C m * N ^ d * D ^ (δ-d)).natDegree ≤ δ
    omega
  · have hmapped : ((poleMatrix s t (1 : F)).submatrix id e).map (algebraMap F (OneSeedFrac F)) =
        (poleMatrix s t (1 : OneSeedFrac F)).submatrix id e := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, poleMatrix, apply_ite, map_zero,
        map_mul, map_natCast, map_pow, map_one]
      split_ifs <;> rfl
    have hm : f (C m) = ((poleMatrix s t (1 : OneSeedFrac F)).submatrix id e).det := by
      rw [hc]
      change (algebraMap F (OneSeedFrac F)) ((poleMatrix s t (1 : F)).submatrix id e).det = _
      rw [RingHom.map_det]
      exact congrArg Matrix.det hmapped
    have hpow : f D ^ δ * (f N / f D) ^ d = f N ^ d * f D ^ (δ-d) := by
      calc
        _ = f N ^ d * (f D ^ δ / f D ^ d) := by rw [div_pow]; ring
        _ = _ := by
          congr 1
          apply (div_eq_iff (pow_ne_zero _ hDf)).2
          rw [← pow_add, Nat.sub_add_cancel hd]
    rw [minor_power, hz]
    change f (C m * N ^ d * D ^ (δ-d)) =
      f D ^ δ * (((poleMatrix s t (1 : OneSeedFrac F)).submatrix id e).det * (f N / f D) ^ d)
    rw [map_mul, map_mul, map_pow, map_pow, hm, mul_left_comm (f D ^ δ), hpow]
    ac_rfl
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1 (otherBlock)
open K1_14_1_7 K1_14_1_7_2
open scoped BigOperators Matrix Polynomial
open private taylor_seed_degree seedWeight_add window_sum from ProximityPrize.SubmissionLower.Fast065
private def seedMap (F : Type) [Field F] (side : Fin 2) : F[X] →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (Polynomial.toMvPolynomial side).toRingHom
private def fractionSeedMap (F : Type) [Field F] (side : Fin 2) :
    OneSeedFrac F →+* SeedFrac F :=
  IsFractionRing.lift (g := seedMap F side)
    ((IsFractionRing.injective (Seed F) (SeedFrac F)).comp
      (Polynomial.toMvPolynomial_injective side))
private theorem fractionSeedMap_polynomial {F : Type} [Field F] (side : Fin 2) (g : F[X]) :
    fractionSeedMap F side (algebraMap F[X] (OneSeedFrac F) g) =
      algebraMap (Seed F) (SeedFrac F) (g.toMvPolynomial side) := by
  rw [fractionSeedMap, IsFractionRing.lift_algebraMap]
  rfl
private theorem fractionSeedMap_scalar {F : Type} [Field F] (side : Fin 2) (a : F) :
    fractionSeedMap F side (algebraMap F (OneSeedFrac F) a) =
      algebraMap F (SeedFrac F) a := by
  rw [IsScalarTower.algebraMap_apply F F[X] (OneSeedFrac F), fractionSeedMap_polynomial]
  change algebraMap (Seed F) (SeedFrac F) ((Polynomial.C a).toMvPolynomial side) = _
  rw [Polynomial.toMvPolynomial_C]
  exact (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) a).symm
private theorem fractionSeedMap_residue {F : Type} [Field F] (side : Fin 2) (a b c : F) :
    fractionSeedMap F side (oneResidue a b c) = residue side a b c := by
  simp only [oneResidue, residue, map_div₀, map_add, map_mul, fractionSeedMap_scalar,
    fractionSeedMap_polynomial, Polynomial.toMvPolynomial_X]
def polynomialTest {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → F[X]) : TrueSource F →ₗ[F] Seed F :=
  ∑ u, (v u).toMvPolynomial side • input α u
private theorem polynomialTest_apply {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → F[X]) (P : TrueSource F) :
    polynomialTest α side v P = ∑ u, (v u).toMvPolynomial side * input α u P := by
  simp only [polynomialTest, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
private theorem side_degrees {F : Type} [Field F] (side : Fin 2) (p : F[X]) :
    (p.toMvPolynomial side).degreeOf (otherBlock side) ≤ 0 ∧
    (p.toMvPolynomial side).totalDegree ≤ p.natDegree := by
  classical
  have hsum : p.toMvPolynomial side =
      ∑ k ∈ p.support, MvPolynomial.C (p.coeff k) * MvPolynomial.X side ^ k := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X]
  have hne : otherBlock side ≠ side := by fin_cases side <;> decide
  rw [hsum]
  constructor
  · refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    simpa [MvPolynomial.degreeOf_X_of_ne hne] using
      MvPolynomial.degreeOf_pow_le (otherBlock side) (MvPolynomial.X (R := F) side) k
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact ((MvPolynomial.totalDegree_pow (MvPolynomial.X (R := F) side) k).trans
      (by simp)).trans (Polynomial.le_natDegree_of_mem_supp k hk)
theorem polynomialTest_window {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → F[X]) {d : ℕ}
    (hd : ∀ u, (v u).natDegree ≤ d) {P : TrueSource F} (hP : Shaped s P) :
    SeedWindow s.U d side (polynomialTest α side v P) := by
  rw [polynomialTest_apply]
  apply window_sum
  intro u
  let f := (v u).toMvPolynomial side
  let g := input α u P
  have hf := side_degrees side (v u)
  have hg : g.totalDegree ≤ s.U := taylor_seed_degree s α P hP _ _ _
  have hother : (f * g).degreeOf (otherBlock side) ≤ s.U := by
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    exact (Nat.add_le_add hf.1 ((MvPolynomial.degreeOf_le_totalDegree g _).trans hg)).trans_eq
      (Nat.zero_add _)
  have htotal : (f * g).totalDegree ≤ s.U + d :=
    (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (hf.2.trans (hd u)) hg).trans_eq (Nat.add_comm _ _))
  intro e he
  have hMem : e ∈ (f * g).support := MvPolynomial.mem_support_iff.mpr he
  refine ⟨(MvPolynomial.le_degreeOf_of_mem_support _ hMem).trans hother, ?_⟩
  rw [← seedWeight_add side e]
  exact (show K1_14_1.seedWeight e ≤ _ from MvPolynomial.le_totalDegree hMem).trans htotal
theorem polynomialTests_to_poleMatrix {F : Type} [Field F] {s : Shape} (t : Offset s)
    (α : F) (side : Fin 2) (a b c : F) (P : TrueSource F)
    (Q : Matrix (Pivot s t) (Column s t) F[X])
    (L : Matrix (Pivot s t) (Pivot s t) (OneSeedFrac F))
    (hL : poleMatrix s t (oneResidue a b c) = L * Q.map (algebraMap F[X] (OneSeedFrac F)))
    (hz : ∀ r, polynomialTest α side (Q r) P = 0) :
    poleMatrix s t (residue side a b c) *ᵥ
      (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0 := by
  let f := fractionSeedMap F side
  let V : Column s t → SeedFrac F := fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)
  let Q' : Matrix (Pivot s t) (Column s t) (SeedFrac F) := Q.map (seedMap F side)
  have hM : (poleMatrix s t (oneResidue a b c)).map f = poleMatrix s t (residue side a b c) := by
    ext r u
    simp only [Matrix.map_apply, poleMatrix, f, apply_ite, map_zero, map_mul, map_natCast,
      map_pow, fractionSeedMap_residue]
    split_ifs <;> rfl
  have hQ : (Q.map (algebraMap F[X] (OneSeedFrac F))).map f = Q' := by
    ext r u
    exact fractionSeedMap_polynomial side (Q r u)
  have hV : Q' *ᵥ V = 0 := by
    funext r
    change (∑ u, algebraMap (Seed F) (SeedFrac F) ((Q r u).toMvPolynomial side) *
      algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0
    have hh := congrArg (algebraMap (Seed F) (SeedFrac F)) (hz r)
    simpa only [polynomialTest_apply, map_sum, map_mul, map_zero] using hh
  change poleMatrix s t (residue side a b c) *ᵥ V = 0
  rw [← hM, hL, Matrix.map_mul, hQ, ← Matrix.mulVec_mulVec, hV, Matrix.mulVec_zero]
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount)
open scoped BigOperators Matrix Polynomial
def c1 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (α : F) (z : SeedFrac F),
    (∀ (t : Offset s) (q : Grade s),
      PascalSpans (SeedFrac F) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)) →
    ∀ P : TrueSource F, Shaped s P →
      (∀ t : Offset s, poleMatrix s t z *ᵥ
        (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0) →
      ∀ (q : Grade s) (k : GradeSlot s q.val),
        (Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J) ∣
          zeroGrade s q.val (localSlots s α z P q) k
def c2 : Prop :=
  ∀ (F ι κ : Type) [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ (OneSeedFrac F)) (D : ℕ), BoundedMinors M D →
    ∃ (Q : Matrix ι κ F[X]) (L : Matrix ι ι (OneSeedFrac F)) (d : ι → ℕ),
      M = L * Q.map (algebraMap F[X] (OneSeedFrac F)) ∧
      (∀ r u, (Q r u).natDegree ≤ d r) ∧ (∑ r, d r) ≤ D
theorem of_children (hLocal : c1) (hBasis : c2) :
    P1_7_1.c1 := by
  classical
  intro F _ _ s _ H lift α side a b c hH _ hb hz
  have hRows (t : Offset s) :=
    hBasis F (Pivot s t) (Column s t) _ _ (bounded_pole_minors F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset s) (r : Pivot s t) := polynomialTest α side (Q t r)
  let e := rowIndex s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomialTest_window α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset s) (r : Pivot s t) : tests t r P = 0 := by
      let testAt (k : Σ t : Offset s, Pivot s t) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := hLocal F s α z
      (fun t q => pascal_spans (SeedFrac F) (firstJet s t)
        (columnCount s.B s.J t.val q.val) (outputLength s t q)) P hP
      (fun t => polynomialTests_to_poleMatrix t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := K1_14_1_7_2_2.proof F s (localSlots s α z P) hslots
    rw [← K1_14_1_7_2_1.proof F s α z P hP] at hd
    exact transfer_dvd H lift α z (s.B+s.J) P hH hz
      (linear_pole_dvd α z (s.B+s.J) P hd)
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2 P1_7_1_1
open P1_7_1 (columnCount pivotCount)
open scoped BigOperators Matrix Polynomial
open private coeff_zeroGrade from ProximityPrize.SubmissionLower.Fast065
private abbrev JetIndex (s : Shape) (t : Offset s) (q : Grade s) :=
  Fin (columnCount s.B s.J t.val q.val)
private theorem sum_embedding {A D M : Type} [Fintype A] [Fintype D] [AddCommMonoid M]
    (e : A ↪ D) (f : D → M) (h : ∀ d, (∀ a, e a ≠ d) → f d = 0) :
    ∑ d, f d = ∑ a, f (e a) := by
  classical
  rw [← Finset.sum_map Finset.univ e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  exact h d fun a ha => hd (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ha⟩)
private theorem column_index (s : Shape) (t : Offset s) (q : Grade s) (j : ℕ)
    (hj : j ≤ min q.val s.J) (hfirst : firstJet s t ≤ j)
    (hx : t.val + j - s.J < s.B + s.J) :
    j - firstJet s t < columnCount s.B s.J t.val q.val := by
  have ht := t.isLt
  have hhigh : j ≤ s.B + 2*s.J - 1 - t.val := by omega
  have hmin := le_min (hj.trans (min_le_left _ _))
    (le_min (hj.trans (min_le_right _ _)) hhigh)
  change j - firstJet s t < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 -
    firstJet s t
  omega
private theorem columnCount_le (s : Shape) (t : Offset s) {q q' : Grade s}
    (h : q.val ≤ q'.val) :
    columnCount s.B s.J t.val q.val ≤ columnCount s.B s.J t.val q'.val := by
  unfold columnCount
  exact Nat.sub_le_sub_right (Nat.add_le_add_right (min_le_min_right _ h) 1) _
private def gradeShift (s : Shape) (q : Grade s) : Shift s q ↪ Grade s where
  toFun p := ⟨q.val + p.val, by
    have hq := q.isLt
    have hp := p.isLt
    omega⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def slotEmbedding (s : Shape) (t : Offset s) (q : Grade s) :
    JetIndex s t q ↪ GradeSlot s q.val where
  toFun a := ⟨firstJet s t + a.val,
    Nat.lt_succ_of_le (jet_bounds s t q a.val a.isLt).1⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def translatedCoeff {F : Type} [Field F] {s : Shape}
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s) (j x : ℕ) : SeedFrac F :=
  ∑ p : Shift s q,
    (((q.val - j + p.val).choose (q.val - j) : SeedFrac F) * z ^ p.val) *
      algebraMap (Seed F) (SeedFrac F) (inputTaylorCoeff α j (q.val - j + p.val) x P)
private theorem localSlots_coeff {F : Type} [Field F] (s : Shape)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s) (j : GradeSlot s q.val)
    (x : ℕ) :
    (localSlots s α z P q j).coeff x = translatedCoeff α z P q j.val x := by
  simp only [localSlots, finsetSum_coeff, coeff_C_mul, coeff_map, inputOrdinate,
    translatedCoeff, inputTaylorCoeff_apply]
private theorem pivot_read {F : Type} [Field F] (s : Shape) (t : Offset s)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s)
    (i : Fin (pivotCount s.B s.J t.val q.val)) :
    (poleMatrix s t z *ᵥ
        (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P))) ⟨q, i⟩ =
      ∑ a : JetIndex s t q, ((firstJet s t + a.val).choose i.val : SeedFrac F) *
        translatedCoeff α z P q (firstJet s t + a.val)
          (t.val + (firstJet s t + a.val) - s.J) := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  let f (q' : Grade s) (a : JetIndex s t q') :=
    poleMatrix s t z ⟨q, i⟩ ⟨q', a⟩ *
      algebraMap (Seed F) (SeedFrac F) (input α ⟨q', a⟩ P)
  change (∑ q', ∑ a, f q' a) = _
  rw [sum_embedding (gradeShift s q) (fun q' => ∑ a, f q' a)]
  · simp only [translatedCoeff, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    let q' := gradeShift s q p
    have hqq : q.val ≤ q'.val := Nat.le_add_right _ _
    let e : JetIndex s t q ↪ JetIndex s t q' :=
      Fin.castLEEmb (columnCount_le s t hqq)
    change (∑ a, f q' a) = _
    rw [sum_embedding e (f q')]
    · apply Finset.sum_congr rfl
      intro a _
      let j := firstJet s t + a.val
      have hj : j ≤ q.val := (jet_bounds s t q a.val a.isLt).1.trans (min_le_left _ _)
      have hp : q'.val - q.val = p.val := by
        change q.val + p.val - q.val = p.val
        omega
      have hOrd : q'.val - j = q.val - j + p.val := by
        change q.val + p.val - j = q.val - j + p.val
        omega
      change (if q.val ≤ q'.val ∧ j ≤ q.val then
        ((j.choose i.val : SeedFrac F) * ((q'.val - j).choose (q.val - j) : SeedFrac F)) *
          z ^ (q'.val - q.val) else 0) *
          algebraMap (Seed F) (SeedFrac F)
            (inputTaylorCoeff α j (q'.val - j) (t.val + j - s.J) P) = _
      rw [ite_eq_left ⟨hqq, hj⟩, hp, hOrd]
      simp only [j, mul_assoc]
    · intro a ha
      have hj : ¬ firstJet s t + a.val ≤ q.val := by
        intro hj
        have hb := jet_bounds s t q' a.val a.isLt
        have hi := column_index s t q (firstJet s t + a.val)
          (le_min hj (hb.1.trans (min_le_right _ _))) (Nat.le_add_right _ _) hb.2
        have ha' : a.val < columnCount s.B s.J t.val q.val := by omega
        exact ha ⟨a.val, ha'⟩ (Fin.ext rfl)
      simp [f, poleMatrix, columnJet, hj]
  · intro q' h
    have hl : ¬ q.val ≤ q'.val := by
      intro hqq
      have hq' := q'.isLt
      let p : Shift s q := ⟨q'.val - q.val, by omega⟩
      exact h p (Fin.ext (by change q.val + (q'.val - q.val) = q'.val; omega))
    apply Finset.sum_eq_zero
    intro a _
    have hz : poleMatrix s t z ⟨q, i⟩ ⟨q', a⟩ = 0 := by
      unfold poleMatrix
      exact ite_eq_right (fun h => hl h.1)
    simp only [f, hz, zero_mul]
private theorem coeff_read {F : Type} [Field F] (s : Shape) (t : Offset s)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s)
    (k : GradeSlot s q.val) (l : ℕ) (hl : l < s.B + s.J)
    (ht : t.val + q.val + k.val = l + s.J) :
    (zeroGrade s q.val (localSlots s α z P q) k).coeff l =
      ∑ a : JetIndex s t q, ((firstJet s t + a.val).choose k.val : SeedFrac F) *
        translatedCoeff α z P q (firstJet s t + a.val)
          (t.val + (firstJet s t + a.val) - s.J) := by
  classical
  rw [coeff_zeroGrade, sum_embedding (slotEmbedding s t q)]
  · apply Finset.sum_congr rfl
    intro a _
    let j := firstJet s t + a.val
    have hj := (jet_bounds s t q a.val a.isLt).1.trans (min_le_left _ _)
    have hshift : q.val - j + k.val ≤ l := by
      have hfirst : s.J ≤ t.val + j := by
        dsimp [j, firstJet]
        omega
      omega
    have hx : l - (q.val - j + k.val) = t.val + j - s.J := by omega
    change (if k.val ≤ j ∧ q.val - j + k.val ≤ l then
      (j.choose k.val : SeedFrac F) * (localSlots s α z P q (slotEmbedding s t q a)).coeff
        (l - (q.val - j + k.val)) else 0) = _
    by_cases hk : k.val ≤ j
    · rw [ite_eq_left ⟨hk, hshift⟩, hx, localSlots_coeff]
      rfl
    · change _ = (j.choose k.val : SeedFrac F) *
        translatedCoeff α z P q j (t.val + j - s.J)
      rw [ite_eq_right (fun h => hk h.1), Nat.choose_eq_zero_of_lt (lt_of_not_ge hk),
        Nat.cast_zero, zero_mul]
  · intro j hj
    split_ifs with h
    · exfalso
      have hjmin : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
      have hjq := hjmin.trans (min_le_left _ _)
      have hshift := h.2
      have hfirst : firstJet s t ≤ j.val := by unfold firstJet; omega
      have hx : t.val + j.val - s.J < s.B + s.J := by omega
      let a : JetIndex s t q := ⟨j.val - firstJet s t, column_index s t q j.val hjmin hfirst hx⟩
      apply hj a
      apply Fin.ext
      change firstJet s t + (j.val - firstJet s t) = j.val
      omega
    · rfl
private theorem pascal_sum_zero {E : Type} [Field E] {a n h : ℕ}
    (hs : PascalSpans E a n h) (v : Fin n → E)
    (hv : ∀ r, (∑ j, pascal a n h r j * v j) = 0) (k : ℕ) (hk : k < h) :
    (∑ j : Fin n, ((a + j.val).choose k : E) * v j) = 0 := by
  obtain ⟨w, hw⟩ := hs k hk
  simp only [hw, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hv, mul_zero, Finset.sum_const_zero]
theorem proof : P1_7_1_1.c1 := by
  intro F _ s α z hs P _ hm q k
  apply Polynomial.X_pow_dvd_iff.mpr
  intro l hl
  by_cases ht : q.val + k.val ≤ l + s.J
  · let t : Offset s := ⟨l + s.J - (q.val + k.val), by omega⟩
    have ht' : t.val + q.val + k.val = l + s.J := by dsimp [t]; omega
    have hk : k.val < outputLength s t q := by unfold outputLength; omega
    rw [coeff_read s t α z P q k l hl ht']
    let v (j : JetIndex s t q) :=
      translatedCoeff α z P q (firstJet s t + j.val) (t.val + (firstJet s t + j.val) - s.J)
    apply pascal_sum_zero (hs t q) v _ k.val hk
    intro r
    have hr := congrFun (hm t) (⟨q, r⟩ : Pivot s t)
    rw [pivot_read] at hr
    exact hr
  · rw [coeff_zeroGrade]
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
    have hjq := hj.trans (min_le_left _ _)
    have hjJ := hj.trans (min_le_right _ _)
    have hn : ¬ q.val - j.val + k.val ≤ l := by omega
    simp [hn]
end
end P1_7_1_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap F[X] K
private theorem clear_denominators (M : Matrix ι κ K) (e : ι ↪ κ)
    (he : (M.submatrix id e).det ≠ 0) :
    ∃ (A : Matrix ι κ F[X]) (b : K), b ≠ 0 ∧ A.map φ = b • M ∧
      (A.submatrix id e).det ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors F[X]) (fun p : ι × κ => M p.1 p.2)
  choose a ha using hb
  let A : Matrix ι κ F[X] := fun i j => a (i, j)
  have hmap : A.map φ = φ b • M := by
    apply Matrix.ext
    intro i j
    change φ (a (i, j)) = φ b * M i j
    simpa only [Algebra.smul_def] using ha (i, j)
  have hb0 : φ b ≠ 0 :=
    fun h => (nonZeroDivisors.ne_zero b.property)
      (IsFractionRing.injective F[X] K (h.trans (map_zero φ).symm))
  refine ⟨A, φ b, hb0, hmap, ?_⟩
  intro h
  have hdet : φ (A.submatrix id e).det = (φ b • M.submatrix id e).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (congrArg (fun B : Matrix ι κ K => B.submatrix id e) hmap)
  rw [h, map_zero, Matrix.det_smul] at hdet
  exact (mul_ne_zero (pow_ne_zero _ hb0) he) hdet.symm
theorem exists_split_rows (M : Matrix ι κ K)
    (hM : ∃ e : ι ↪ κ, (M.submatrix id e).det ≠ 0) :
    ∃ (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (L : Matrix ι ι K),
      Q * T = 1 ∧ M = L * Q.map φ := by
  classical
  obtain ⟨e, he⟩ := hM
  obtain ⟨A, b, hb, hA, hminor⟩ := clear_denominators M e he
  let N := LinearMap.range A.vecMulLinear
  have hAi : Function.Injective A.vecMulLinear := by
    intro x y hxy
    apply Matrix.vecMul_injective_iff.mpr (Matrix.linearIndependent_rows_of_det_ne_zero hminor)
    exact funext fun j => congrFun hxy (e j)
  have hN : Module.finrank F[X] N = Fintype.card ι := by
    rw [LinearMap.finrank_range_of_inj hAi, Module.finrank_pi]
  obtain ⟨n, S⟩ := N.smithNormalForm (Pi.basisFun F[X] κ)
  let re : ι ≃ Fin n := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis S.bN, hN])
  let Q : Matrix ι κ F[X] := fun i => S.bM (S.f (re i))
  let T : Matrix κ ι F[X] := fun j i => S.bM.coord (S.f (re i)) (Pi.single j 1)
  have hQT : Q * T = 1 := by
    apply Matrix.ext
    intro i j
    have hsum : (∑ k : κ, Q i k • (Pi.single k 1 : κ → F[X])) = Q i := by
      funext k
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
    have hcoord := congrArg (S.bM.coord (S.f (re j))) hsum
    simp only [map_sum, map_smul, smul_eq_mul] at hcoord
    change (∑ k : κ, Q i k * S.bM.coord (S.f (re j)) (Pi.single k 1)) = _
    rw [hcoord]
    change S.bM.coord (S.f (re j)) (S.bM (S.f (re i))) = _
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
  have hrow (i : ι) : A i ∈ N := by
    refine ⟨Pi.single i 1, ?_⟩
    exact Matrix.single_one_vecMul i A
  let W : Matrix ι ι F[X] := fun i j => S.bN.repr ⟨A i, hrow i⟩ (re j) * S.a (re j)
  have hW : W * Q = A := by
    apply Matrix.ext
    intro i j
    have hsum := S.bN.sum_repr ⟨A i, hrow i⟩
    let l : N →ₗ[F[X]] F[X] := (LinearMap.proj j).comp N.subtype
    have hc := congrArg l hsum
    rw [Matrix.mul_apply, ← Equiv.sum_comp re.symm]
    simpa only [l, map_sum, map_smul, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, W, Q, S.snf, Equiv.apply_symm_apply, ← mul_assoc,
      Pi.smul_apply, smul_eq_mul] using hc
  refine ⟨Q, T, b⁻¹ • W.map φ, hQT, ?_⟩
  have h := congrArg (fun B : Matrix ι κ F[X] => B.map φ) hW
  rw [Matrix.map_mul, hA] at h
  rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hb, one_smul]
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap F[X] K
def leadingRows (Q : Matrix ι κ F[X]) (d : ι → ℕ) : Matrix ι κ F :=
  fun i j => (Q i j).coeff (d i)
omit [Fintype ι] in
private theorem no_zero_row {Q : Matrix ι κ F[X]} {T : Matrix κ ι F[X]}
    (h : Q * T = 1) (p : ι) : Q p ≠ 0 := by
  intro hp
  have hpp := congrFun (congrFun h p) p
  rw [Matrix.mul_apply, hp] at hpp
  simp at hpp
private theorem reduce_step (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (d : ι → ℕ)
    (hQT : Q * T = 1) (hdeg : ∀ r u, (Q r u).natDegree ≤ d r)
    (hbad : ¬ LinearIndependent F (leadingRows Q d).row) :
    ∃ (E : Matrix ι ι F[X]) (d' : ι → ℕ), IsUnit E.det ∧
      (∀ r u, ((E * Q) r u).natDegree ≤ d' r) ∧ (∑ r, d' r) < ∑ r, d r := by
  classical
  rw [Fintype.linearIndependent_iff] at hbad
  push Not at hbad
  obtain ⟨a, ha, i, hi⟩ := hbad
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨p, hp, hmax⟩ := s.exists_max_image d hs
  have hap : a p ≠ 0 := (Finset.mem_filter.mp hp).2
  have hle (r : ι) (hr : a r ≠ 0) : d r ≤ d p :=
    hmax r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
  let c (r : ι) : F[X] := C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)
  let E := (1 : Matrix ι ι F[X]).updateRow p c
  have hc : c p = C (a p) := by simp [c]
  have hE : IsUnit E.det := by
    have hrow : (∑ k, c k • (1 : Matrix ι ι F[X]) k) = c := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_one]
    change IsUnit ((1 : Matrix ι ι F[X]).updateRow p c).det
    rw [← hrow, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one, hc]
    exact (isUnit_iff_ne_zero.mpr hap).map C
  have hform : E * Q = Q.updateRow p (∑ r, c r • Q r) := by
    change (1 : Matrix ι ι F[X]).updateRow p c * Q = _
    rw [Matrix.updateRow_mul, Matrix.one_mul, Matrix.vecMul_eq_sum]
  have hbound (u : κ) : ((E * Q) p u).natDegree ≤ d p := by
    rw [hform, Matrix.updateRow_self, Finset.sum_apply]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r _
    by_cases hz : a r = 0
    · simp [c, hz]
    · have hr := hle r hz
      change ((C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)) * Q r u).natDegree ≤ _
      rw [mul_assoc]
      have hm : ((Polynomial.X (R := F)) ^ (d p - d r) * Q r u).natDegree ≤
          (d p - d r) + d r :=
        Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_pow_le _) (hdeg r u)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hm.trans (by omega))
  have hcoeff (u : κ) : ((E * Q) p u).coeff (d p) = 0 := by
    rw [hform, Matrix.updateRow_self, Finset.sum_apply, Polynomial.finsetSum_coeff]
    have hA := congrFun ha u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hA
    rw [← hA]
    apply Finset.sum_congr rfl
    intro r _
    change ((C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)) * Q r u).coeff (d p) =
      a r * (Q r u).coeff (d r)
    rw [mul_assoc, Polynomial.coeff_C_mul]
    by_cases hz : a r = 0
    · simp [hz]
    · congr 1
      have hr := hle r hz
      have heq : d r + (d p - d r) = d p := by omega
      exact (congrArg (((Polynomial.X (R := F)) ^ (d p - d r) * Q r u).coeff) heq.symm).trans
        (Polynomial.coeff_X_pow_mul _ _ _)
  have hpos : 0 < d p := by
    by_contra! hp0
    have heq : d p = 0 := Nat.eq_zero_of_le_zero hp0
    have hright : (E * Q) * (T * E⁻¹) = 1 := by
      rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Q, hQT, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hE]
    apply no_zero_row hright p
    funext u
    have hdeg0 : ((E * Q) p u).natDegree ≤ 0 := heq ▸ hbound u
    have hz : ((E * Q) p u).coeff 0 = 0 := heq ▸ hcoeff u
    change ((E * Q) p u) = 0
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg0, hz, map_zero]
  let d' := Function.update d p (d p - 1)
  refine ⟨E, d', hE, ?_, ?_⟩
  · intro r u
    by_cases hr : r = p
    · subst r
      change ((E * Q) p u).natDegree ≤ Function.update d p (d p - 1) p
      rw [Function.update_self]
      exact Polynomial.natDegree_le_pred (hbound u) (hcoeff u)
    · rw [hform, Matrix.updateRow_ne hr]
      change (Q r u).natDegree ≤ Function.update d p (d p - 1) r
      rw [Function.update_of_ne hr]
      exact hdeg r u
  · apply Finset.sum_lt_sum
    · intro r _
      by_cases hr : r = p
      · simp [d', hr]
      · simp [d', Function.update_of_ne hr]
    · exact ⟨p, Finset.mem_univ p, by simpa [d'] using Nat.sub_lt hpos (by decide : 0 < 1)⟩
theorem exists_reduced_rows (M : Matrix ι κ K)
    (hM : ∃ (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (L : Matrix ι ι K),
      Q * T = 1 ∧ M = L * Q.map φ) :
    ∃ (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (L : Matrix ι ι K) (d : ι → ℕ),
      Q * T = 1 ∧ M = L * Q.map φ ∧
      (∀ r u, (Q r u).natDegree ≤ d r) ∧ LinearIndependent F (leadingRows Q d).row := by
  classical
  let P (n : ℕ) :=
    ∃ (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (L : Matrix ι ι K) (d : ι → ℕ),
      Q * T = 1 ∧ M = L * Q.map φ ∧ (∀ r u, (Q r u).natDegree ≤ d r) ∧ (∑ r, d r) = n
  have hP : ∃ n, P n := by
    obtain ⟨Q, T, L, hQT, hL⟩ := hM
    let d (i : ι) := Finset.univ.sup (fun u : κ => (Q i u).natDegree)
    exact ⟨_, Q, T, L, d, hQT, hL, fun r u => Finset.le_sup (f := fun v : κ => (Q r v).natDegree) (Finset.mem_univ u), rfl⟩
  obtain ⟨Q, T, L, d, hQT, hL, hdeg, hn⟩ := Nat.find_spec hP
  refine ⟨Q, T, L, d, hQT, hL, hdeg, ?_⟩
  by_contra hbad
  obtain ⟨E, d', hE, hdeg', hlt⟩ := reduce_step Q T d hQT hdeg hbad
  let V := E⁻¹
  have hEV : E * V = 1 := Matrix.mul_nonsing_inv _ hE
  have hVE : V * E = 1 := Matrix.nonsing_inv_mul _ hE
  have hnew : P (∑ i, d' i) := by
    refine ⟨E * Q, T * V, L * V.map φ, d', ?_, ?_, hdeg', rfl⟩
    · rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Q, hQT, Matrix.one_mul, hEV]
    · rw [Matrix.map_mul, Matrix.mul_assoc L, ← Matrix.mul_assoc (V.map φ),
        ← Matrix.map_mul, hVE, Matrix.map_one _ (map_zero φ) (map_one φ),
        Matrix.one_mul, hL]
  exact (not_lt_of_ge (Nat.find_min' hP hnew)) (hn ▸ hlt)
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap F[X] K
omit [Fintype ι] in
private theorem coeff_weighted_prod {s : Finset ι} (p : ι → F[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (p i).natDegree ≤ d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self _ _))]
    · exact congrArg ((p i).coeff (d i) * ·) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem exists_full_minor (B : Matrix ι κ F) (hB : LinearIndependent F B.row) :
    ∃ e : ι ↪ κ, (B.submatrix id e).det ≠ 0 := by
  classical
  have hr : B.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hB]
  obtain ⟨α, a, ha, hspan, hli⟩ := exists_linearIndependent' F B.col
  let : Finite α := Finite.of_injective a ha
  let : Fintype α := Fintype.ofFinite α
  have hc : Fintype.card ι = Fintype.card α := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]
  let u := Fintype.equivOfCardEq hc
  let e : ι ↪ κ := u.toEmbedding.trans ⟨a, ha⟩
  have hli' : LinearIndependent F (B.submatrix id e).col := hli.comp u u.injective
  exact ⟨e, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hli')).ne_zero⟩
theorem exists_minor_of_degree_sum (Q : Matrix ι κ F[X]) (d : ι → ℕ)
    (hdeg : ∀ r u, (Q r u).natDegree ≤ d r)
    (hlead : LinearIndependent F (leadingRows Q d).row) :
    ∃ e : ι ↪ κ, (Q.submatrix id e).det ≠ 0 ∧ (∑ r, d r) ≤ (Q.submatrix id e).det.natDegree := by
  obtain ⟨e, he⟩ := exists_full_minor (leadingRows Q d) hlead
  have hcoeff :
      (Q.submatrix id e).det.coeff (∑ r, d r) = ((leadingRows Q d).submatrix id e).det := by
    rw [← Matrix.det_transpose (Q.submatrix id e), ← Matrix.det_transpose ((leadingRows Q d).submatrix id e),
      Matrix.det_apply', Matrix.det_apply', Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← map_intCast (C : F →+* F[X]), Polynomial.coeff_C_mul]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, leadingRows]
    rw [coeff_weighted_prod _ d (fun i _ => hdeg i (e (σ i)))]
  have hne : (Q.submatrix id e).det.coeff (∑ r, d r) ≠ 0 := hcoeff.trans_ne he
  exact ⟨e, fun hz => hne (by rw [hz, Polynomial.coeff_zero]), Polynomial.le_natDegree_of_ne_zero hne⟩
private theorem det_rectangular_mul {R : Type} [CommRing R]
    (Q : Matrix ι κ R) (T : Matrix κ ι R) :
    (Q * T).det = ∑ f : ι → κ, (∏ j, T (f j) j) * (Q.submatrix id f).det := by
  classical
  calc
    (Q * T).det = ∑ f : ι → κ, ∑ σ : Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign σ) : R) * ∏ i, Q (σ i) (f i) * T (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Finset.mul_sum, Matrix.submatrix_apply, id_eq,
        Finset.prod_mul_distrib, mul_comm, mul_assoc]
private theorem scale_polynomial (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X])
    (hQT : Q * T = 1) (t : K)
    (h : ∀ f : ι → κ, ∃ g : F[X], φ g = t * φ (Q.submatrix id f).det) :
    ∃ g : F[X], φ g = t := by
  classical
  choose g hg using h
  refine ⟨∑ f : ι → κ, (∏ j, T (f j) j) * g f, ?_⟩
  have hh := det_rectangular_mul Q T
  rw [hQT, Matrix.det_one] at hh
  have he := congrArg φ hh
  simp only [map_one, map_sum, map_mul] at he
  simp only [map_sum, map_mul, hg]
  calc
    _ = t * ∑ f : ι → κ, φ (∏ j, T (f j) j) * φ (Q.submatrix id f).det := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ => mul_left_comm _ _ _
    _ = t := by rw [← he, mul_one]
theorem minor_degree_le (M : Matrix ι κ K) (D : ℕ)
    (Q : Matrix ι κ F[X]) (T : Matrix κ ι F[X]) (L : Matrix ι ι K)
    (hQT : Q * T = 1) (hM : M = L * Q.map φ) (hb : P1_7_1_1.BoundedMinors M D)
    (e : ι ↪ κ) (he : (Q.submatrix id e).det ≠ 0) :
    (Q.submatrix id e).det.natDegree ≤ D := by
  classical
  obtain ⟨⟨e₀, he₀⟩, scale, hscale, hminors⟩ := hb
  have hdet (f : ι → κ) :
      (M.submatrix id f).det = L.det * φ (Q.submatrix id f).det := by
    rw [hM, Matrix.submatrix_mul _ _ id id f Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.det_mul, RingHom.map_det]
    rfl
  have hL : L.det ≠ 0 := by
    intro hz
    exact he₀ (by rw [hdet, hz, zero_mul])
  have hall (f : ι → κ) : ∃ g : F[X], φ g = (scale * L.det) * φ (Q.submatrix id f).det := by
    by_cases hf : Function.Injective f
    · let e' : ι ↪ κ := ⟨f, hf⟩
      obtain ⟨g, _, hg⟩ := hminors e'
      change φ g = scale * (M.submatrix id f).det at hg
      rw [hdet, ← mul_assoc] at hg
      exact ⟨g, hg⟩
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
      have hz : (Q.submatrix id f).det = 0 :=
        Matrix.det_zero_of_column_eq hne (fun u => congrArg (Q u) hij)
      exact ⟨0, by rw [hz, map_zero, mul_zero]⟩
  obtain ⟨p, hp⟩ := scale_polynomial Q T hQT (scale * L.det) hall
  have hp0 : p ≠ 0 := by
    intro hz
    exact (mul_ne_zero hscale hL) (by rw [← hp, hz, map_zero])
  obtain ⟨g, hg, hge⟩ := hminors e
  have hmul : g = p * (Q.submatrix id e).det := by
    apply IsFractionRing.injective F[X] K
    rw [hge, hdet, map_mul, hp, mul_assoc]
  rw [hmul, Polynomial.natDegree_mul hp0 he] at hg
  exact (Nat.le_add_left _ _).trans hg
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
namespace P1_7_1_1_2
open scoped BigOperators
theorem proof : P1_7_1_1.c2 := by
  intro F ι κ _ _ _ _ M D hM
  obtain ⟨Q, T, L, d, hQT, hL, hdeg, hlead⟩ :=
    exists_reduced_rows M (exists_split_rows M hM.1)
  obtain ⟨e, he, hd⟩ := exists_minor_of_degree_sum Q d hdeg hlead
  exact ⟨Q, L, d, hL, hdeg, hd.trans (minor_degree_le M D Q T L hQT hL hM e he)⟩
end P1_7_1_1_2
end
section
namespace P1_7_1_2
open Finset
open K1_14 (Shape shapeSum)
open P1_7_1 (nodeRows)
open scoped BigOperators
open private shape_sum_flip from ProximityPrize.SubmissionLower.Fast063
private def atNode (m J q j : ℕ) : ℕ := m + min q J - (q + 2*j)
private def twiceGrade (k i : ℕ) : ℕ :=
  k*(k+1) + (6*k+2)*i + 8*i*i
def sixPerNode (k J : ℕ) : ℕ :=
  3*(J+1)*k*(k+1) + 3*(3*k+1)*J*(J+1) + 4*J*(J+1)*(2*J+1)
private theorem twice_descending (d : ℕ) :
    2 * (∑ i ∈ range d, (d-i)) = d*(d+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, mul_add, ih]
    ring
private theorem three_grade_sum (k J : ℕ) :
    3 * (∑ i ∈ range (J+1), twiceGrade k i) = sixPerNode k J := by
  induction J with
  | zero => simp [twiceGrade, sixPerNode, mul_assoc]
  | succ J ih =>
    rw [sum_range_succ, mul_add, ih]
    unfold twiceGrade sixPerNode
    ring
private theorem twice_at_derivative {m B J j : ℕ} (hm : 2*J ≤ m)
    (hB : m+J ≤ B+1) (hj : j ≤ J) :
    2 * (∑ q ∈ Ico j (B+1), atNode m J q j) = twiceGrade (m-2*J) (J-j) := by
  let d := m - 2*j
  have hhead : (∑ q ∈ Ico j J, atNode m J q j) = (J-j)*d := by
    calc
      _ = ∑ _q ∈ Ico j J, d := by
        apply sum_congr rfl
        intro q hq
        unfold atNode
        rw [min_eq_left (mem_Ico.mp hq).2.le]
        dsimp [d]
        omega
      _ = _ := by simp [Nat.card_Ico]
  have htail : (∑ q ∈ Ico J (B+1), atNode m J q j) =
      ∑ i ∈ range d, (d-i) := by
    rw [sum_Ico_eq_sum_range]
    calc
      _ = ∑ i ∈ range (B+1-J), (d-i) := by
        apply sum_congr rfl
        intro i _
        unfold atNode
        rw [min_eq_right (by omega : J ≤ J+i)]
        dsimp [d]
        omega
      _ = _ := by
        symm
        apply sum_subset (range_mono (show d ≤ B+1-J by dsimp [d]; omega))
        intro i _ hi
        have hdi : d ≤ i := by simpa only [mem_range, not_lt] using hi
        exact Nat.sub_eq_zero_of_le hdi
  rw [← sum_Ico_consecutive (atNode m J · j) hj (show J ≤ B+1 by omega),
    hhead, htail, mul_add, twice_descending]
  have hd : d = (m-2*J) + 2*(J-j) := by dsimp [d]; omega
  rw [hd]
  unfold twiceGrade
  ring
theorem six_nodeRows (s : Shape) (hm : 2*s.J ≤ s.m) (hB : s.m+s.J ≤ s.B+1) :
    6 * nodeRows s = 262144 * sixPerNode (s.m-2*s.J) s.J := by
  change 6 * (262144 * shapeSum s (fun q j => atNode s.m s.J q j)) = _
  unfold shapeSum
  rw [shape_sum_flip]
  let f (j : ℕ) := ∑ q ∈ Ico j (s.B+1), atNode s.m s.J q j
  let k := s.m-2*s.J
  change 6 * (262144 * (∑ j ∈ range (s.J+1), f j)) = 262144 * sixPerNode k s.J
  calc
    _ = 262144 * (3 * (2 * ∑ j ∈ range (s.J+1), f j)) := by ring
    _ = 262144 * (3 * ∑ j ∈ range (s.J+1), twiceGrade k (s.J-j)) := by
      rw [mul_sum]
      refine congrArg (fun n : ℕ => 262144 * (3*n)) (sum_congr rfl fun j hj => ?_)
      exact twice_at_derivative hm hB (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = _ := by
      have hreflect : (∑ j ∈ range (s.J+1), twiceGrade k (s.J-j)) =
          ∑ j ∈ range (s.J+1), twiceGrade k j := by
        simpa only [Nat.add_sub_cancel] using sum_range_reflect (twiceGrade k) (s.J+1)
      rw [hreflect, three_grade_sum]
end P1_7_1_2
end
section
namespace P1_7_1_3
open P1 (HighBand)
open P1_7 (Bank terminal stages)
def ramp (a q : ℕ) : ℕ := q + 1 - a
def low (J t : ℕ) : ℕ := J - t
def high (B J t : ℕ) : ℕ := min J (B + 2*J - 1 - t)
def width (B J t : ℕ) : ℕ := high B J t + 1 - low J t
def edge (B J t : ℕ) : ℕ := B + 2*J - t
def peak (B J t : ℕ) : ℕ :=
  min (width B J t) ((edge B J t - low J t + 1) / 2)
def productSum6 (n a b : ℕ) : ℕ :=
  6*n*a*b + 3*(a+b)*n*(n-1) + n*(n-1)*(2*(n-1)+1)
def rampCount6 (N a : ℕ) : ℕ :=
  let n := N-a
  3*n*(n+1)
def rampWeight6 (N a : ℕ) : ℕ := productSum6 (N-a) a 1
def rampExcess6 (N k a : ℕ) : ℕ :=
  let s := max (k+1) a
  productSum6 (N-s) (s-k) (s+1-a)
def pivotVolume6 (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  let a := low J t
  let e := edge B J t
  let h := peak B J t
  stat a + stat (e+1) - (stat (a+h) + stat (e+1-h))
def columnVolume6 (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  let a := low J t
  stat a - stat (a + width B J t)
def pivotRank6 (B J t : ℕ) : ℕ := pivotVolume6 B J t (rampCount6 (B+1))
def pivotWeight6 (B J t : ℕ) : ℕ := pivotVolume6 B J t (rampWeight6 (B+1))
def excess6 (B J t k : ℕ) : ℕ := columnVolume6 B J t (rampExcess6 (B+1) k)
def triangularCut (omitted : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let mid := (lo+hi)/2
      if mid*(mid+1) ≤ 2*omitted then triangularCut omitted fuel mid hi
      else triangularCut omitted fuel lo mid
    else lo
def threshold (B J t : ℕ) : ℕ :=
  let R := pivotRank6 B J t / 6
  let w := width B J t
  let h := high B J t
  if R ≤ w * (B+1-h) then B - (R-1)/w else
    let omitted := columnVolume6 B J t (rampCount6 (B+1)) / 6 - R
    min B (low J t + triangularCut omitted 16 0 (w+1))
def offsetEstimate (B J t : ℕ) : ℕ :=
  let k := threshold B J t
  (pivotRank6 B J t * k + excess6 B J t k - pivotWeight6 B J t) / 6
def evaluate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evaluate f n + f n
def blockEstimate (B J start length : ℕ) : ℕ :=
  evaluate (fun i => offsetEstimate B J (start+i)) length
def momentEstimate (B J : ℕ) : ℕ := blockEstimate B J J (B+J)
def FullListed (b : HighBand) (t : Bank) : Prop :=
  t = terminal b ∨ ∃ s ∈ stages b, t = s.free ∨ t = s.moving
def BankEstimate (t : Bank) : Prop :=
  momentEstimate t.shape.B t.shape.J ≤ t.poleMoment
def RangeEstimate (lo hi : ℕ) : Prop :=
  ∀ (b : HighBand) (t : Bank), FullListed b t → lo ≤ t.shape.B → t.shape.B < hi → BankEstimate t
end P1_7_1_3
end
section
namespace P1_7_1_3
open Finset P1_7_1
private theorem product_sum (n a b : ℕ) :
    6 * (∑ i ∈ range n, (a+i)*(b+i)) = productSum6 n a b := by
  induction n with
  | zero => simp [productSum6]
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    cases n with
    | zero => simp [productSum6, Nat.mul_assoc]
    | succ m => simp only [productSum6, Nat.succ_sub_one]; ring
private theorem count_sum (n : ℕ) :
    6 * (∑ i ∈ range n, (i+1)) = 3*n*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, Nat.mul_add, ih]; ring
private theorem sum_after (f : ℕ → ℕ) (N s : ℕ) (hz : ∀ q < s, f q = 0) :
    (∑ q ∈ range N, f q) = ∑ i ∈ range (N-s), f (s+i) := by
  by_cases h : s ≤ N
  · conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
    rw [sum_eq_zero (fun q hq => hz q (mem_range.mp hq)), zero_add]
  · rw [Nat.sub_eq_zero_of_le (by omega : N ≤ s), sum_range_zero]
    exact sum_eq_zero fun q hq => hz q (by have := mem_range.mp hq; omega)
private theorem ramp_count (N a : ℕ) :
    6 * (∑ q ∈ range N, ramp a q) = rampCount6 N a := by
  rw [sum_after (ramp a) N a (fun q hq => by unfold ramp; omega)]
  unfold rampCount6
  rw [← count_sum]
  congr 1
  exact sum_congr rfl fun i _ => by unfold ramp; omega
private theorem ramp_weight (N a : ℕ) :
    6 * (∑ q ∈ range N, q * ramp a q) = rampWeight6 N a := by
  rw [sum_after (fun q => q * ramp a q) N a
    (fun q hq => by rw [show ramp a q = 0 by unfold ramp; omega, mul_zero])]
  unfold rampWeight6
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by
    rw [show ramp a (a+i) = 1+i by unfold ramp; omega]
private theorem ramp_excess (N k a : ℕ) :
    6 * (∑ q ∈ range N, (q-k) * ramp a q) = rampExcess6 N k a := by
  let s := max (k+1) a
  have hs₁ : k+1 ≤ s := le_max_left _ _
  have hs₂ : a ≤ s := le_max_right _ _
  have hz (q : ℕ) (hq : q < s) : (q-k) * ramp a q = 0 := by
    by_cases h : q ≤ k
    · rw [Nat.sub_eq_zero_of_le h, zero_mul]
    · rw [show ramp a q = 0 by dsimp [s, ramp] at *; omega, mul_zero]
  rw [sum_after _ N s hz]
  change _ = productSum6 (N-s) (s-k) (s+1-a)
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by
    rw [show s+i-k = s-k+i by omega, show ramp a (s+i) = s+1-a+i by unfold ramp; omega]
private theorem column_row (B J t q : ℕ) :
    columnCount B J t q + ramp (low J t + width B J t) q = ramp (low J t) q := by
  unfold columnCount ramp width low high
  dsimp only
  omega
private theorem pivot_row (B J t q : ℕ) :
    pivotCount B J t q + ramp (low J t + peak B J t) q +
      ramp (edge B J t + 1 - peak B J t) q =
        ramp (low J t) q + ramp (edge B J t + 1) q := by
  have hc := column_row B J t q
  let a := low J t
  let e := edge B J t
  let w := width B J t
  let h := peak B J t
  change columnCount B J t q + ramp (a+w) q = ramp a q at hc
  have hae : a ≤ e := by dsimp [a, e, low, edge]; omega
  have hh : h = min w ((e-a+1)/2) := rfl
  have hp : pivotCount B J t q = min (columnCount B J t q) (e-q) := by
    unfold pivotCount
    rw [show B + 2*J - (t+q) = e-q by dsimp [e, edge]; omega]
  change pivotCount B J t q + ramp (a+h) q + ramp (e+1-h) q =
    ramp a q + ramp (e+1) q
  simp only [ramp] at hc ⊢
  by_cases hq : q < a+h
  · omega
  · by_cases hq' : q < e+1-h
    · omega
    · omega
private theorem pivot_volume (B J t : ℕ) (f stat : ℕ → ℕ)
    (hs : ∀ a, stat a = 6 * (∑ q ∈ range (B+1), f q * ramp a q)) :
    6 * (∑ q ∈ range (B+1), f q * pivotCount B J t q) = pivotVolume6 B J t stat := by
  unfold pivotVolume6
  simp only [hs]
  have heq :
      (∑ q ∈ range (B+1), (f q * pivotCount B J t q + f q * ramp (low J t + peak B J t) q +
        f q * ramp (edge B J t + 1 - peak B J t) q)) =
      ∑ q ∈ range (B+1), (f q * ramp (low J t) q + f q * ramp (edge B J t + 1) q) := by
    apply sum_congr rfl
    intro q _
    simp only [← Nat.mul_add, pivot_row]
  simp only [sum_add_distrib] at heq
  omega
private theorem column_volume (B J t : ℕ) (f stat : ℕ → ℕ)
    (hs : ∀ a, stat a = 6 * (∑ q ∈ range (B+1), f q * ramp a q)) :
    6 * (∑ q ∈ range (B+1), f q * columnCount B J t q) = columnVolume6 B J t stat := by
  unfold columnVolume6
  simp only [hs]
  have heq :
      (∑ q ∈ range (B+1), (f q * columnCount B J t q + f q * ramp (low J t + width B J t) q)) =
      ∑ q ∈ range (B+1), f q * ramp (low J t) q := by
    apply sum_congr rfl
    intro q _
    rw [← Nat.mul_add, column_row]
  simp only [sum_add_distrib] at heq
  omega
theorem pivot_rank (B J t : ℕ) :
    6 * (∑ q ∈ range (B+1), pivotCount B J t q) = pivotRank6 B J t := by
  simpa only [one_mul, pivotRank6] using
    pivot_volume B J t (fun _ => 1) (rampCount6 (B+1))
      (fun a => by simpa only [one_mul] using (ramp_count (B+1) a).symm)
theorem pivot_weight (B J t : ℕ) :
    6 * (∑ q ∈ range (B+1), q * pivotCount B J t q) = pivotWeight6 B J t :=
  pivot_volume B J t id (rampWeight6 (B+1)) (fun a => (ramp_weight (B+1) a).symm)
theorem column_excess (B J t k : ℕ) :
    6 * (∑ q ∈ range (B+1), (q-k) * columnCount B J t q) = excess6 B J t k :=
  column_volume B J t (fun q => q-k) (rampExcess6 (B+1) k)
    (fun a => (ramp_excess (B+1) k a).symm)
private theorem threshold_le (B J t : ℕ) : threshold B J t ≤ B := by
  dsimp only [threshold]
  split
  · exact Nat.sub_le _ _
  · exact min_le_left _ _
theorem offset_bound (B J t : ℕ) : offsetMoment B J t ≤ offsetEstimate B J t := by
  let k := threshold B J t
  let R := ∑ q ∈ range (B+1), pivotCount B J t q
  let W := ∑ q ∈ range (B+1), q * pivotCount B J t q
  let E := ∑ q ∈ range (B+1), (q-k) * columnCount B J t q
  have hk : k ∈ range (B+1) := mem_range.mpr (Nat.lt_succ_of_le (threshold_le B J t))
  have htop : largestGradeSum B J t R ≤ R*k + E := by
    unfold largestGradeSum
    exact inf'_le _ hk
  change largestGradeSum B J t R - W ≤
    (pivotRank6 B J t * k + excess6 B J t k - pivotWeight6 B J t) / 6
  rw [← pivot_rank, ← pivot_weight, ← column_excess]
  change largestGradeSum B J t R - W ≤ (6*R*k + 6*E - 6*W) / 6
  rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ (by decide)]
  exact Nat.sub_le_sub_right htop W
theorem evaluate_eq (f : ℕ → ℕ) (n : ℕ) : evaluate f n = ∑ t ∈ range n, f t := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => rw [evaluate, sum_range_succ, ih]
private theorem offset_zero (B J t : ℕ) (ht : t < J) : offsetMoment B J t = 0 := by
  have hp (q : ℕ) (hq : q ∈ range (B+1)) : pivotCount B J t q = columnCount B J t q := by
    have hq' := mem_range.mp hq
    have hc : columnCount B J t q ≤ t+1 := by
      dsimp only [columnCount]
      omega
    exact min_eq_left (hc.trans (by omega))
  unfold offsetMoment
  dsimp only
  apply Nat.sub_eq_zero_of_le
  calc
    _ ≤ (∑ q ∈ range (B+1), pivotCount B J t q)*0 +
        ∑ q ∈ range (B+1), (q-0) * columnCount B J t q := by
      unfold largestGradeSum
      exact inf'_le _ (mem_range.mpr (Nat.zero_lt_succ B))
    _ = _ := by
      simp only [mul_zero, Nat.sub_zero, zero_add]
      exact sum_congr rfl fun q hq => congrArg (q * ·) (hp q hq).symm
theorem grouped_bound (B J : ℕ) : groupedPoleMoment B J ≤ momentEstimate B J := by
  rw [momentEstimate, blockEstimate, evaluate_eq, groupedPoleMoment,
    show B+2*J = J+(B+J) by omega, sum_range_add,
    sum_eq_zero (fun t ht => offset_zero B J t (mem_range.mp ht)), zero_add]
  exact sum_le_sum fun t _ => offset_bound B J (J+t)
theorem evaluate_append {f : ℕ → ℕ} {a b n x y z : ℕ}
    (ha : evaluate f a = x) (hb : evaluate (fun t => f (a+t)) b = y)
    (hn : a+b = n) (hz : x+y = z) : evaluate f n = z := by
  rw [← hn, ← hz]
  have h := sum_range_add f a b
  simp only [← evaluate_eq] at h
  exact h.trans (congrArg₂ (· + ·) ha hb)
theorem block_append {B J start next a b n x y z : ℕ}
    (ha : blockEstimate B J start a = x) (hb : blockEstimate B J next b = y)
    (hs : start+a = next) (hn : a+b = n) (hz : x+y = z) :
    blockEstimate B J start n = z := by
  unfold blockEstimate at *
  rw [← hs] at hb
  exact evaluate_append ha (by simpa only [Nat.add_assoc] using hb) hn hz
theorem bank_of_moment (t : P1_7.Bank) {M : ℕ}
    (hm : momentEstimate t.shape.B t.shape.J = M) (hb : M ≤ t.poleMoment) :
    BankEstimate t :=
  (Nat.le_of_eq hm).trans hb
theorem bank_of_literals (t : P1_7.Bank) {B J M : ℕ}
    (hB : t.shape.B = B) (hJ : t.shape.J = J)
    (hm : momentEstimate B J = M) (hb : M ≤ t.poleMoment) : BankEstimate t := by
  apply bank_of_moment t _ hb
  simpa only [hB, hJ] using hm
end P1_7_1_3
end
section
namespace P1_7_1_3_2
open P1_7_1_3 (blockEstimate block_append momentEstimate)
def CheckedBlocks (B J : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | start, (length, total) :: rest =>
    blockEstimate B J start length = total ∧ CheckedBlocks B J (start + length) rest
private theorem block_total {B J : ℕ} (blocks : List (ℕ × ℕ)) (start : ℕ)
    (checked : CheckedBlocks B J start blocks) :
    blockEstimate B J start (blocks.map Prod.fst).sum = (blocks.map Prod.snd).sum := by
  induction blocks generalizing start with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨length, total⟩ := head
    exact block_append checked.1 (ih _ checked.2) rfl rfl rfl
theorem moment_from_blocks {B J total : ℕ} (blocks : List (ℕ × ℕ))
    (checked : CheckedBlocks B J J blocks)
    (length_eq : (blocks.map Prod.fst).sum = B + J)
    (total_eq : (blocks.map Prod.snd).sum = total) :
    momentEstimate B J = total := by
  rw [momentEstimate, ← length_eq, ← total_eq]
  exact block_total blocks J checked
class ExactMoment (B J total : ℕ) : Prop where
  eq_moment : momentEstimate B J = total
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 500 105 1700679003 where
  eq_moment := by
    refine moment_from_blocks
      [(128,144037782),(128,567478208),(128,637814720),(128,319210721),
      (93,32137572)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 501 105 1711611949 where
  eq_moment := by
    refine moment_from_blocks
      [(128,144393518),(128,569377728),(128,641450944),(128,323182467),
      (94,33207292)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 521 117 2110154682 where
  eq_moment := by
    refine moment_from_blocks
      [(128,152229145),(128,646266176),(128,776764736),(128,455019674),
      (126,79874951)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 523 117 2136298939 where
  eq_moment := by
    refine moment_from_blocks
      [(128,152944225),(128,650314048),(128,784679232),(128,464485709),
      (128,83875725)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 535 112 2221379895 where
  eq_moment := by
    refine moment_from_blocks
      [(128,157045140),(128,658437440),(128,804697408),(128,501243104),
      (128,99930187),(7,26616)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 546 113 2387645191 where
  eq_moment := by
    refine moment_from_blocks
      [(128,161023860),(128,683587776),(128,852621504),(128,560448099),
      (128,129579472),(19,384480)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 547 109 2335147916 where
  eq_moment := by
    refine moment_from_blocks
      [(128,161134435),(128,671528000),(128,832828480),(128,546827594),
      (128,122589587),(16,239820)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 552 116 2523691858 where
  eq_moment := by
    refine moment_from_blocks
      [(128,163284615),(128,705699072),(128,893558016),(128,605669194),
      (128,154329076),(28,1151885)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 572 120 2904427648 where
  eq_moment := by
    refine moment_from_blocks
      [(128,170524574),(128,759701888),(128,997597568),(128,735310082),
      (128,234301265),(52,6992271)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 577 129 3158702492 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172350880),(128,798366400),(128,1074191040),(128,813443001),
      (128,286344633),(66,14006538)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 578 117 2944634929 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172608925),(128,761630528),(128,1002327872),(128,752644119),
      (128,247118139),(55,8305346)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 578 129 3176332897 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172708640),(128,800496320),(128,1078450880),(128,819433681),
      (128,290590600),(67,14652776)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 580 119 3017027973 where
  eq_moment := by
    refine moment_from_blocks
      [(128,173369590),(128,772688640),(128,1023363840),(128,775246907),
      (128,262158826),(59,10200170)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 591 124 3308696108 where
  eq_moment := by
    refine moment_from_blocks
      [(128,177354875),(128,812312000),(128,1101080000),(128,868637578),
      (128,328555618),(75,20756037)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 597 126 3460443224 where
  eq_moment := by
    refine moment_from_blocks
      [(128,179505610),(128,831445632),(128,1139399296),(128,916997523),
      (128,365008090),(83,28087073)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 598 125 3457603226 where
  eq_moment := by
    refine moment_from_blocks
      [(128,179861955),(128,830265408),(128,1136826432),(128,916910704),
      (128,365601387),(83,28137340)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 607 139 3938005884 where
  eq_moment := by
    refine moment_from_blocks
      [(128,183083680),(128,891468085),(128,1268686720),(128,1061576997),
      (128,475434639),(106,57755763)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 609 128 3734056387 where
  eq_moment := by
    refine moment_from_blocks
      [(128,183799200),(128,863305152),(128,1203584448),(128,1003805395),
      (128,434638067),(97,44924125)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 612 121 3630535593 where
  eq_moment := by
    refine moment_from_blocks
      [(128,184845250),(128,845461952),(128,1166277056),(128,975711462),
      (128,418227357),(93,40012516)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 613 121 3649568203 where
  eq_moment := by
    refine moment_from_blocks
      [(128,185202954),(128,847523264),(128,1170337216),(128,981727130),
      (128,423442731),(94,41334908)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 617 127 3870016120 where
  eq_moment := by
    refine moment_from_blocks
      [(128,186661280),(128,876941312),(128,1230311424),(128,1047177034),
      (128,473263516),(104,55661554)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 621 139 4237643334 where
  eq_moment := by
    refine moment_from_blocks
      [(128,188092320),(128,922329405),(128,1331657600),(128,1154779018),
      (128,556283521),(120,84501470)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 634 132 4351456177 where
  eq_moment := by
    refine moment_from_blocks
      [(128,192743200),(128,929702719),(128,1339363200),(128,1191222484),
      (128,599015438),(126,99409136)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 662 139 5203785784 where
  eq_moment := by
    refine moment_from_blocks
      [(128,202760480),(128,1012708985),(128,1516072320),(128,1432350080),
      (128,830129570),(128,207552923),(33,2211426)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 662 149 5491466699 where
  eq_moment := by
    refine moment_from_blocks
      [(128,202760480),(128,1040567045),(128,1591483200),(128,1514068800),
      (128,893654100),(128,244219046),(43,4714028)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 665 139 5279846034 where
  eq_moment := by
    refine moment_from_blocks
      [(128,203833760),(128,1019322125),(128,1529566080),(128,1452725120),
      (128,852255965),(128,219295492),(36,2847492)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 674 140 5543427992 where
  eq_moment := by
    refine moment_from_blocks
      [(128,207053600),(128,1042265009),(128,1578062976),(128,1522619520),
      (128,926834473),(128,260764188),(46,5828226)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 675 140 5569859382 where
  eq_moment := by
    refine moment_from_blocks
      [(128,207411360),(128,1044476175),(128,1582584000),(128,1529450688),
      (128,934549636),(128,265178067),(47,6209456)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 686 138 5800691370 where
  eq_moment := by
    refine moment_from_blocks
      [(128,211346720),(128,1062371996),(128,1615682624),(128,1586076736),
      (128,1007022200),(128,307734158),(56,10456936)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 726 153 7540240839 where
  eq_moment := by
    refine moment_from_blocks
      [(128,225657120),(128,1196811466),(128,1928242624),(128,2015290816),
      (128,1469051275),(128,625151582),(111,80035956)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 734 165 8281195601 where
  eq_moment := by
    refine moment_from_blocks
      [(128,228519200),(128,1244003969),(128,2067127616),(128,2199035200),
      (128,1649353090),(128,762657762),(128,130493632),(3,5132)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 740 167 8580372579 where
  eq_moment := by
    refine moment_from_blocks
      [(128,230665760),(128,1262245730),(128,2113698048),(128,2266462464),
      (128,1726864884),(128,824321763),(128,155995520),(11,118410)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 776 163 9809476816 where
  eq_moment := by
    refine moment_from_blocks
      [(128,243545120),(128,1337858951),(128,2261641344),(128,2502125696),
      (128,2055573998),(128,1110845387),(128,292335874),(43,5550446)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 779 173 10401501082 where
  eq_moment := by
    refine moment_from_blocks
      [(128,244618400),(128,1366300947),(128,2364345408),(128,2642299968),
      (128,2192053949),(128,1223114534),(128,356838378),(56,11929498)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 781 178 10721014375 where
  eq_moment := by
    refine moment_from_blocks
      [(128,245333920),(128,1380003801),(128,2416574464),(128,2715713536),
      (128,2266117448),(128,1285945362),(128,394514228),(63,16811616)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 782 178 10765253509 where
  eq_moment := by
    refine moment_from_blocks
      [(128,245691680),(128,1382396018),(128,2421878592),(128,2723950400),
      (128,2277127269),(128,1296134164),(128,400457082),(64,17618304)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 783 165 10192726271 where
  eq_moment := by
    refine moment_from_blocks
      [(128,246049440),(128,1358944053),(128,2314921792),(128,2580096832),
      (128,2149468958),(128,1194949591),(128,338612451),(52,9683154)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 784 164 10186247915 where
  eq_moment := by
    refine moment_from_blocks
      [(128,246407200),(128,1358949795),(128,2310908160),(128,2575837440),
      (128,2149048385),(128,1196318864),(128,339082164),(52,9695907)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 792 167 10673329627 where
  eq_moment := by
    refine moment_from_blocks
      [(128,249269280),(128,1384644162),(128,2378713344),(128,2674608384),
      (128,2266006484),(128,1302457939),(128,400572546),(63,17057488)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 808 165 11274483946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,254993440),(128,1417586953),(128,2441347392),(128,2774516032),
      (128,2411430208),(128,1452816319),(128,490659052),(77,31134550)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 821 188 13132884772 where
  eq_moment := by
    refine moment_from_blocks
      [(128,259644320),(128,1491434191),(128,2714935104),(128,3170131776),
      (128,2832620376),(128,1824571448),(128,743401218),(113,96146339)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 822 188 13184443531 where
  eq_moment := by
    refine moment_from_blocks
      [(128,260002080),(128,1493853093),(128,2720414592),(128,3178707840),
      (128,2844287584),(128,1836656028),(128,751766439),(114,98755875)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 825 173 12507204741 where
  eq_moment := by
    refine moment_from_blocks
      [(128,261075360),(128,1475597499),(128,2604081216),(128,3013173312),
      (128,2692456512),(128,1721466865),(128,667497478),(102,71856499)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 828 189 13552061015 where
  eq_moment := by
    refine moment_from_blocks
      [(128,262148640),(128,1509721915),(128,2761675840),(128,3242628160),
      (128,2926662720),(128,1920285208),(128,810698549),(121,118239983)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 853 192 15095933357 where
  eq_moment := by
    refine moment_from_blocks
      [(128,271092640),(128,1574237488),(128,2925089472),(128,3497431744),
      (128,3260273344),(128,2274160185),(128,1071003387),(128,221846864),
      (21,798233)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 856 174 14142442253 where
  eq_moment := by
    refine moment_from_blocks
      [(128,272165920),(128,1551390955),(128,2775528000),(128,3277288000),
      (128,3045044800),(128,2111237198),(128,945222943),(128,164535408),
      (6,29029)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 882 186 16399828679 where
  eq_moment := by
    refine moment_from_blocks
      [(128,281467680),(128,1635894932),(128,3030381376),(128,3664589632),
      (128,3514463040),(128,2598697640),(128,1325282868),(128,342290592),
      (44,6760919)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 883 197 17210339526 where
  eq_moment := by
    refine moment_from_blocks
      [(128,281825440),(128,1653196253),(128,3135857472),(128,3828458304),
      (128,3690586944),(128,2749316070),(128,1446953881),(128,410568928),
      (56,13576234)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 912 194 18868434791 where
  eq_moment := by
    refine moment_from_blocks
      [(128,292200480),(128,1720155840),(128,3271220160),(128,4041186240),
      (128,3993263040),(128,3133663239),(128,1774996188),(128,599346999),
      (82,42402605)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 926 195 19894196946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,297209120),(128,1755504711),(128,3358888064),(128,4179366016),
      (128,4177760384),(128,3356603776),(128,1974410087),(128,724289538),
      (97,70165250)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 958 195 22186492210 where
  eq_moment := by
    refine moment_from_blocks
      [(128,308657440),(128,1833375943),(128,3537916032),(128,4461154432),
      (128,4562309248),(128,3841387932),(128,2439290735),(128,1036067666),
      (128,166331824),(1,958)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 960 205 23224363038 where
  eq_moment := by
    refine moment_from_blocks
      [(128,309372960),(128,1849612615),(128,3645738560),(128,4639706688),
      (128,4769648192),(128,4035677606),(128,2602917483),(128,1155992984),
      (128,215455408),(13,240542)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 968 204 23761225895 where
  eq_moment := by
    refine moment_from_blocks
      [(128,312235040),(128,1868238645),(128,3682311680),(128,4696645120),
      (128,4851146240),(128,4145818989),(128,2716742287),(128,1237702419),
      (128,249594080),(20,791395)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
scoped instance : ExactMoment 996 207 26338011946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,322252320),(128,1939676596),(128,3872068096),(128,5001777664),
      (128,5259072000),(128,4643951104),(128,3228690796),(128,1623238100),
      (128,435562624),(51,11722646)] ?_ rfl rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate block_append)
theorem appendBlock {B J start length total : ℕ} (a b next x y : ℕ)
    (hprefix : blockEstimate B J start a = x)
    (hsuffix : blockEstimate B J next b = y := by rfl)
    (hstart : start + a = next := by decide)
    (hlength : a + b = length := by decide)
    (htotal : x + y = total := by decide) :
    blockEstimate B J start length = total :=
  block_append hprefix hsuffix hstart hlength htotal
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
theorem moment1028_211 : momentEstimate 1028 211 = 29591361675 := by
  change blockEstimate 1028 211 211 1239 = 29591361675
  refine appendBlock 1152 87 1363 29534311429 57050246 ?_
  refine appendBlock 960 192 1171 27945900514 1588410915 ?_
  refine appendBlock 768 192 979 22801775699 5144124815 ?_
  refine appendBlock 576 192 787 14699091603 8102684096 ?_
  refine appendBlock 384 192 595 6451826899 8247264704 ?_
  refine appendBlock 192 192 403 1060057904 5391768995 ?_
  rfl
theorem moment1043_235 : momentEstimate 1043 235 = 33710825496 := by
  change blockEstimate 1043 235 235 1278 = 33710825496
  refine appendBlock 1152 126 1387 33540780424 170045072 ?_
  refine appendBlock 960 192 1195 31290830721 2249949703 ?_
  refine appendBlock 768 192 1003 25136594525 6154236196 ?_
  refine appendBlock 576 192 811 15933247773 9203346752 ?_
  refine appendBlock 384 192 619 6803850205 9129397568 ?_
  refine appendBlock 192 192 427 1078030064 5725820141 ?_
  rfl
theorem moment1058_225 : momentEstimate 1058 225 = 34123764741 := by
  change blockEstimate 1058 225 225 1283 = 34123764741
  refine appendBlock 1152 131 1377 33930464733 193300008 ?_
  refine appendBlock 960 192 1185 31557098306 2373366427 ?_
  refine appendBlock 768 192 993 25214951080 6342147226 ?_
  refine appendBlock 576 192 801 15956483208 9258467872 ?_
  refine appendBlock 384 192 609 6852143720 9104339488 ?_
  refine appendBlock 192 192 417 1096002224 5756141496 ?_
  rfl
theorem moment1072_239 : momentEstimate 1072 239 = 37305519000 := by
  change blockEstimate 1072 239 239 1311 = 37305519000
  refine appendBlock 1152 159 1391 36961641040 343877960 ?_
  refine appendBlock 960 192 1199 34016813735 2944827305 ?_
  refine appendBlock 768 192 1007 26874253340 7142560395 ?_
  refine appendBlock 576 192 815 16810170140 10064083200 ?_
  refine appendBlock 384 192 623 7095557660 9714612480 ?_
  refine appendBlock 192 192 431 1112776240 5982781420 ?_
  rfl
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
theorem moment1183_249 : momentEstimate 1183 249 = 52867790342 := by
  change blockEstimate 1183 249 249 1432 = 52867790342
  refine appendBlock 1344 88 1593 52799553932 68236410 ?_
  refine appendBlock 1152 192 1401 50912668199 1886885733 ?_
  refine appendBlock 960 192 1209 44561140535 6351527664 ?_
  refine appendBlock 768 192 1017 33358848250 11202292285 ?_
  refine appendBlock 576 192 825 20051804250 13307044000 ?_
  refine appendBlock 384 192 633 8177848250 11873956000 ?_
  refine appendBlock 192 192 441 1245770224 6932078026 ?_
  rfl
theorem moment1237_263 : momentEstimate 1237 263 = 63680038117 := by
  change blockEstimate 1237 263 263 1500 = 63680038117
  refine appendBlock 1344 156 1607 63300910797 379127320 ?_
  refine appendBlock 1152 192 1415 59871488268 3429422529 ?_
  refine appendBlock 960 192 1223 51089714962 8781773306 ?_
  refine appendBlock 768 192 1031 37368291730 13721423232 ?_
  refine appendBlock 576 192 839 22016742418 15351549312 ?_
  refine appendBlock 384 192 647 8772191890 13244550528 ?_
  refine appendBlock 192 192 455 1310470000 7461721890 ?_
  rfl
theorem moment1307_273 : momentEstimate 1307 273 = 78245537261 := by
  change blockEstimate 1307 273 273 1580 = 78245537261
  refine appendBlock 1536 44 1809 78235443067 10094194 ?_
  refine appendBlock 1344 192 1617 76909230331 1326212736 ?_
  refine appendBlock 1152 192 1425 71012066432 5897163899 ?_
  refine appendBlock 960 192 1233 58877842812 12134223620 ?_
  refine appendBlock 768 192 1041 42054010460 16823832352 ?_
  refine appendBlock 576 192 849 24295860028 17758150432 ?_
  refine appendBlock 384 192 657 9482074140 14813785888 ?_
  refine appendBlock 192 192 465 1394340080 8087734060 ?_
  rfl
theorem moment1324_279 : momentEstimate 1324 279 = 82958819253 := by
  change blockEstimate 1324 279 279 1603 = 82958819253
  refine appendBlock 1536 67 1815 82924192327 34626926 ?_
  refine appendBlock 1344 192 1623 81186298503 1737893824 ?_
  refine appendBlock 1152 192 1431 74468147998 6718150505 ?_
  refine appendBlock 960 192 1239 61305370910 13162777088 ?_
  refine appendBlock 768 192 1047 43522069150 17783301760 ?_
  refine appendBlock 576 192 855 24990428190 18531640960 ?_
  refine appendBlock 384 192 663 9674065310 15316362880 ?_
  refine appendBlock 192 192 471 1414708528 8259356782 ?_
  rfl
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
theorem moment1426_290 : momentEstimate 1426 290 = 108520269689 := by
  change blockEstimate 1426 290 290 1716 = 108520269689
  refine appendBlock 1536 180 1826 107851505684 668764005 ?_
  refine appendBlock 1344 192 1634 103097856676 4753649008 ?_
  refine appendBlock 1152 192 1442 91457133838 11640722838 ?_
  refine appendBlock 960 192 1250 72759871690 18697262148 ?_
  refine appendBlock 768 192 1058 50319059818 22440811872 ?_
  refine appendBlock 576 192 866 28253707786 22065352032 ?_
  refine appendBlock 384 192 674 10683146410 17570561376 ?_
  refine appendBlock 192 192 482 1536919216 9146227194 ?_
  rfl
theorem moment1443_329 : momentEstimate 1443 329 = 124373325152 := by
  change blockEstimate 1443 329 329 1772 = 124373325152
  refine appendBlock 1728 44 2057 124362164310 11160842 ?_
  refine appendBlock 1536 192 1865 122885196118 1476968192 ?_
  refine appendBlock 1344 192 1673 116195234106 6689962012 ?_
  refine appendBlock 1152 192 1481 101913528837 14281705269 ?_
  refine appendBlock 960 192 1289 80203851750 21709677087 ?_
  refine appendBlock 768 192 1097 54696504390 25507347360 ?_
  refine appendBlock 576 192 905 30058963110 24637541280 ?_
  refine appendBlock 384 192 713 10962633990 19096329120 ?_
  refine appendBlock 192 192 521 1557287664 9405346326 ?_
  rfl
theorem moment1513_321 : momentEstimate 1513 321 = 142108334350 := by
  change blockEstimate 1513 321 321 1834 = 142108334350
  refine appendBlock 1728 106 2049 141956799433 151534917 ?_
  refine appendBlock 1536 192 1857 139032366225 2924433208 ?_
  refine appendBlock 1344 192 1665 129520905569 9511460656 ?_
  refine appendBlock 1152 192 1473 111545743344 17975162225 ?_
  refine appendBlock 960 192 1281 86392767440 25152975904 ?_
  refine appendBlock 768 192 1089 58313785264 28078982176 ?_
  refine appendBlock 576 192 897 31866956688 26446828576 ?_
  refine appendBlock 384 192 705 11610441584 20256515104 ?_
  refine appendBlock 192 192 513 1641157744 9969283840 ?_
  rfl
theorem moment1516_321 : momentEstimate 1516 321 = 143016000830 := by
  change blockEstimate 1516 321 321 1837 = 143016000830
  refine appendBlock 1728 109 2049 142851241228 164759602 ?_
  refine appendBlock 1536 192 1857 139842992964 3008248264 ?_
  refine appendBlock 1344 192 1665 130184401858 9658591106 ?_
  refine appendBlock 1152 192 1473 112025219376 18159182482 ?_
  refine appendBlock 960 192 1281 86706060560 25319158816 ?_
  refine appendBlock 768 192 1089 58496506096 28209554464 ?_
  refine appendBlock 576 192 897 31954715856 26541790240 ?_
  refine appendBlock 384 192 705 11638849712 20315866144 ?_
  refine appendBlock 192 192 513 1644752176 9994097536 ?_
  rfl
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
theorem moment1550_329 : momentEstimate 1550 329 = 156562227172 := by
  change blockEstimate 1550 329 329 1879 = 156562227172
  refine appendBlock 1728 151 2057 156124882322 437344850 ?_
  refine appendBlock 1536 192 1865 151827130107 4297752215 ?_
  refine appendBlock 1344 192 1673 140046559016 11780571091 ?_
  refine appendBlock 1152 192 1481 119303634670 20742924346 ?_
  refine appendBlock 960 192 1289 91550555470 27753079200 ?_
  refine appendBlock 768 192 1097 61297544110 30253011360 ?_
  refine appendBlock 576 192 905 33216006670 28081537440 ?_
  refine appendBlock 384 192 713 11977349230 21238657440 ?_
  refine appendBlock 192 192 521 1685489072 10291860158 ?_
  rfl
theorem moment1585_333 : momentEstimate 1585 333 = 169805327500 := by
  change blockEstimate 1585 333 333 1918 = 169805327500
  refine appendBlock 1728 190 2061 168929513748 875813752 ?_
  refine appendBlock 1536 192 1869 163199575959 5729937789 ?_
  refine appendBlock 1344 192 1677 149234840389 13964735570 ?_
  refine appendBlock 1152 192 1485 125946593907 23288246482 ?_
  refine appendBlock 960 192 1293 95922949139 30023644768 ?_
  refine appendBlock 768 192 1101 63824635315 32098313824 ?_
  refine appendBlock 576 192 909 34379681619 29444953696 ?_
  refine appendBlock 384 192 717 12316117235 22063564384 ?_
  refine appendBlock 192 192 525 1727424112 10588693123 ?_
  rfl
theorem moment1587_334 : momentEstimate 1587 334 = 170894624907 := by
  change blockEstimate 1587 334 334 1921 = 170894624907
  refine appendBlock 1920 1 2254 170894623320 1587 ?_
  refine appendBlock 1728 192 2062 169976636416 917986904 ?_
  refine appendBlock 1536 192 1870 164130204232 5846432184 ?_
  refine appendBlock 1344 192 1678 149995495333 14134708899 ?_
  refine appendBlock 1152 192 1486 126511683360 23483811973 ?_
  refine appendBlock 960 192 1294 96300750880 30210932480 ?_
  refine appendBlock 768 192 1102 64039811360 32260939520 ?_
  refine appendBlock 576 192 910 34471049760 29568761600 ?_
  refine appendBlock 384 192 718 12336651040 22134398720 ?_
  refine appendBlock 192 192 526 1729820400 10606830640 ?_
  rfl
theorem moment1642_341 : momentEstimate 1642 341 = 193780511162 := by
  change blockEstimate 1642 341 341 1983 = 193780511162
  refine appendBlock 1920 63 2261 193744454474 36056688 ?_
  refine appendBlock 1728 192 2069 191638564858 2105889616 ?_
  refine appendBlock 1536 192 1877 183042551561 8596013297 ?_
  refine appendBlock 1344 192 1685 165044631160 17997920401 ?_
  refine appendBlock 1152 192 1493 137314443525 27730187635 ?_
  refine appendBlock 960 192 1301 103394582565 33919860960 ?_
  refine appendBlock 768 192 1109 68119416645 35275165920 ?_
  refine appendBlock 576 192 917 36330221157 31789195488 ?_
  refine appendBlock 384 192 725 12868271493 23461949664 ?_
  refine appendBlock 192 192 533 1795718320 11072553173 ?_
  rfl
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
theorem moment1672_344 : momentEstimate 1672 344 = 206796824881 := by
  change blockEstimate 1672 344 344 2016 = 206796824881
  refine appendBlock 1920 96 2264 206671130081 125694800 ?_
  refine appendBlock 1728 192 2072 203687841601 2983288480 ?_
  refine appendBlock 1536 192 1880 193400055312 10287786289 ?_
  refine appendBlock 1344 192 1688 173155136818 20244918494 ?_
  refine appendBlock 1152 192 1496 143088273670 30066863148 ?_
  refine appendBlock 960 192 1304 107171466310 35916807360 ?_
  refine appendBlock 768 192 1112 70288084870 36883381440 ?_
  refine appendBlock 576 192 920 37321872070 32966212800 ?_
  refine appendBlock 384 192 728 13156570630 24165301440 ?_
  refine appendBlock 192 192 536 1831662640 11324907990 ?_
  rfl
theorem moment1678_356 : momentEstimate 1678 356 = 214874896611 := by
  change blockEstimate 1678 356 356 2034 = 214874896611
  refine appendBlock 1920 114 2276 214666244888 208651723 ?_
  refine appendBlock 1728 192 2084 211155091984 3511152904 ?_
  refine appendBlock 1536 192 1892 199948196396 11206895588 ?_
  refine appendBlock 1344 192 1700 178536137167 21412059229 ?_
  refine appendBlock 1152 192 1508 147157242239 31378894928 ?_
  refine appendBlock 960 192 1316 109883403455 37273838784 ?_
  refine appendBlock 768 192 1124 71767295999 38116107456 ?_
  refine appendBlock 576 192 932 37862531903 33904764096 ?_
  refine appendBlock 384 192 740 13222723199 24639808704 ?_
  refine appendBlock 192 192 548 1838851504 11383871695 ?_
  rfl
theorem moment1696_357 : momentEstimate 1696 357 = 222859445142 := by
  change blockEstimate 1696 357 357 2053 = 222859445142
  refine appendBlock 1920 133 2277 222528099213 331345929 ?_
  refine appendBlock 1728 192 2085 218380247909 4147851304 ?_
  refine appendBlock 1536 192 1893 206080043635 12300204274 ?_
  refine appendBlock 1344 192 1701 183273702811 22806340824 ?_
  refine appendBlock 1152 192 1509 150498778521 32774924290 ?_
  refine appendBlock 960 192 1317 112055621561 38443156960 ?_
  refine appendBlock 768 192 1125 73011986905 39043634656 ?_
  refine appendBlock 576 192 933 38435642361 34576344544 ?_
  refine appendBlock 384 192 741 13394355737 25041286624 ?_
  refine appendBlock 192 192 549 1860418096 11533937641 ?_
  rfl
theorem moment1725_359 : momentEstimate 1725 359 = 236367501665 := by
  change blockEstimate 1725 359 359 2084 = 236367501665
  refine appendBlock 1920 164 2279 235744698217 622803448 ?_
  refine appendBlock 1728 192 2087 230432375753 5312322464 ?_
  refine appendBlock 1536 192 1895 216241362480 14191013273 ?_
  refine appendBlock 1344 192 1703 191077006410 25164356070 ?_
  refine appendBlock 1152 192 1511 156007206090 35069800320 ?_
  refine appendBlock 960 192 1319 115635625290 40371580800 ?_
  refine appendBlock 768 192 1127 75058343370 40577281920 ?_
  refine appendBlock 576 192 935 39371439690 35686903680 ?_
  refine appendBlock 384 192 743 13670993610 25700446080 ?_
  refine appendBlock 192 192 551 1895164272 11775829338 ?_
  rfl
end P1_7_1_3_3
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
theorem moment4189 : momentEstimate 4189 858 = 8094070384976 := by
  change blockEstimate 4189 858 858 5047 = 8094070384976
  refine block_append (a := 4992) (b := 55) (next := 5850) (x := 8094007835188) (y := 62549788)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5466) (x := 8065693820276) (y := 28314014912)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5082) (x := 7916398977204) (y := 149294843072)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 4698) (x := 7563993186476) (y := 352405790728)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4314) (x := 6960100365995) (y := 603892820481)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 3930) (x := 6098097021403) (y := 862003344592)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3546) (x := 5043233586395) (y := 1054863435008)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3162) (x := 3892358305755) (y := 1150875280640)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 2778) (x := 2742749672155) (y := 1149608633600)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2394) (x := 1691686178267) (y := 1051063493888)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2010) (x := 836446316763) (y := 855239861504)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1626) (x := 273895652800) (y := 562550663963)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1242) (x := 37109700320) (y := 236785952480)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment4436 : momentEstimate 4436 940 = 10452218230345 := by
  change blockEstimate 4436 940 940 5376 = 10452218230345
  refine block_append (a := 4992) (b := 384) (next := 5932) (x := 10431896682889) (y := 20321547456)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5548) (x := 10297426054345) (y := 134470628544)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5164) (x := 9954783774349) (y := 342642279996)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 4780) (x := 9341134125332) (y := 613649649017)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4396) (x := 8429961938421) (y := 911172186911)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4012) (x := 7250439968501) (y := 1179521969920)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3628) (x := 5899137951733) (y := 1351302016768)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3244) (x := 4482620569845) (y := 1416517381888)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 2860) (x := 3107452504565) (y := 1375168065280)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2476) (x := 1880198437621) (y := 1227254066944)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2092) (x := 907423050741) (y := 972775386880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1708) (x := 292616434880) (y := 614806615861)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1324) (x := 39458927200) (y := 253157507680)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment7630 : momentEstimate 7630 1607 = 90974896361155 := by
  change blockEstimate 7630 1607 1607 9237 = 90974896361155
  refine block_append (a := 9216) (b := 21) (next := 10823) (x := 90974889151880) (y := 7209275)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 8832) (b := 384) (next := 10439) (x := 90933246171384) (y := 41642980496)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 8448) (b := 384) (next := 10055) (x := 90676007819368) (y := 257238352016)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 8064) (b := 384) (next := 9671) (x := 90018888895448) (y := 657118923920)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 7680) (b := 384) (next := 9287) (x := 88797988516680) (y := 1220900378768)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 7296) (b := 384) (next := 8903) (x := 86876467979582) (y := 1921520537098)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6912) (b := 384) (next := 8519) (x := 84157559470705) (y := 2718908508877)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6528) (b := 384) (next := 8135) (x := 80576596867036) (y := 3580962603669)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6144) (b := 384) (next := 7751) (x := 76108718638382) (y := 4467878228654)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5760) (b := 384) (next := 7367) (x := 70779064528730) (y := 5329654109652)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5376) (b := 384) (next := 6983) (x := 64718252933210) (y := 6060811595520)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 6599) (x := 58107703546202) (y := 6610549387008)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 6215) (x := 51129516270170) (y := 6978187276032)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5831) (x := 43965791007578) (y := 7163725262592)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 5447) (x := 36798627660890) (y := 7167163346688)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 5063) (x := 29810126132570) (y := 6988501528320)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4679) (x := 23182386325082) (y := 6627739807488)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 4295) (x := 17097508140890) (y := 6084878184192)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3911) (x := 11737591482458) (y := 5359916658432)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 3527) (x := 7284736252250) (y := 4452855230208)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 3143) (x := 3920679935360) (y := 3364056316890)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2759) (x := 1728687439392) (y := 2191992495968)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 2375) (x := 534698127040) (y := 1193989312352)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1991) (x := 69837188960) (y := 464860938080)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
end P1_7_1_3_5
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
theorem moment4213 : momentEstimate 4213 889 = 8476646500811 := by
  change blockEstimate 4213 889 889 5102 = 8476646500811
  refine block_append (a := 4992) (b := 110) (next := 5881) (x := 8476165777869) (y := 480722942)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5497) (x := 8436276415453) (y := 39889362416)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5113) (x := 8261095610861) (y := 175180804592)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 4729) (x := 7871472406309) (y := 389623204552)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4345) (x := 7222583173908) (y := 648889232401)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 3961) (x := 6311189054730) (y := 911394119178)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3577) (x := 5205213338570) (y := 1105975716160)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3193) (x := 4004944671370) (y := 1200268667200)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 2809) (x := 2811172178250) (y := 1193772493120)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2425) (x := 1724684984330) (y := 1086487193920)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2041) (x := 846272214730) (y := 878412769600)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1657) (x := 275714676160) (y := 570557538570)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1273) (x := 37337965280) (y := 238376710880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment4830 : momentEstimate 4830 1019 = 14637581938425 := by
  change blockEstimate 4830 1019 1019 5849 = 14637581938425
  refine block_append (a := 5760) (b := 89) (next := 6779) (x := 14637286197088) (y := 295741337)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5376) (b := 384) (next := 6395) (x := 14596549607568) (y := 40736589520)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 6011) (x := 14404053579200) (y := 192496028368)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5627) (x := 13959602730553) (y := 444450848647)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5243) (x := 13195286240248) (y := 764316490305)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 4859) (x := 12079150788065) (y := 1116135452183)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4475) (x := 10630093427205) (y := 1449057360860)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4091) (x := 8944530044805) (y := 1685563382400)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3707) (x := 7137965743365) (y := 1806564301440)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3323) (x := 5325911655045) (y := 1812054088320)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 2939) (x := 3623878912005) (y := 1702032743040)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2555) (x := 2147378646405) (y := 1476500265600)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2171) (x := 1011921990405) (y := 1135456656000)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1787) (x := 322478735040) (y := 689443255365)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1403) (x := 43206276960) (y := 279272458080)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment7181 : momentEstimate 7181 1517 = 71551444218860 := by
  change blockEstimate 7181 1517 1517 8698 = 71551444218860
  refine block_append (a := 8448) (b := 250) (next := 9965) (x := 71542079365313) (y := 9364853547)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 8064) (b := 384) (next := 9581) (x := 71404201141073) (y := 137878224240)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 7680) (b := 384) (next := 9197) (x := 70959412394465) (y := 444788746608)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 7296) (b := 384) (next := 8813) (x := 70048296084593) (y := 911116309872)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6912) (b := 384) (next := 8429) (x := 68535469519816) (y := 1512826564777)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6528) (b := 384) (next := 8045) (x := 66324644740336) (y := 2210824779480)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6144) (b := 384) (next := 7661) (x := 63352276743739) (y := 2972367996597)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5760) (b := 384) (next := 7277) (x := 59594043360664) (y := 3758233383075)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5376) (b := 384) (next := 6893) (x := 55076945451451) (y := 4517097909213)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 6509) (x := 49930621122811) (y := 5146324328640)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 6125) (x := 44326659577915) (y := 5603961544896)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5741) (x := 38436968560507) (y := 5889691017408)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 5357) (x := 32433455814331) (y := 6003512746176)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4973) (x := 26488029083131) (y := 5945426731200)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4589) (x := 20772596110651) (y := 5715432972480)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 4205) (x := 15459064640635) (y := 5313531470016)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3821) (x := 10719342416827) (y := 4739722223808)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 3437) (x := 6725337182971) (y := 3994005233856)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 3053) (x := 3648956682811) (y := 3076380500160)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2669) (x := 1613982350496) (y := 2034974332315)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 2285) (x := 500667231680) (y := 1113315118816)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1901) (x := 65566732000) (y := 435100499680)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
end P1_7_1_3_5
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
theorem moment4714 : momentEstimate 4714 997 = 13307662181427 := by
  change blockEstimate 4714 997 997 5711 = 13307662181427
  refine block_append (a := 5376) (b := 335) (next := 6373) (x := 13293190894919) (y := 14471286508)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 5989) (x := 13171216668327) (y := 121974226592)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5605) (x := 12836550788780) (y := 334665879547)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5221) (x := 12212427175383) (y := 624123613397)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 4837) (x := 11257616482002) (y := 954810693381)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4453) (x := 9974418830209) (y := 1283197651793)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4069) (x := 8441569360833) (y := 1532849469376)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3685) (x := 6771639337985) (y := 1669930022848)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3301) (x := 5077648477249) (y := 1693990860736)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 2917) (x := 3472616494209) (y := 1605031983040)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2533) (x := 2069563104449) (y := 1403053389760)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2149) (x := 981508023553) (y := 1088055080896)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1765) (x := 313686788800) (y := 667821234753)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1381) (x := 42102996320) (y := 271583792480)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment5688 : momentEstimate 5688 1209 = 28309856493724 := by
  change blockEstimate 5688 1209 1209 6897 = 28309856493724
  refine block_append (a := 6528) (b := 369) (next := 7737) (x := 28286480041562) (y := 23376452162)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6144) (b := 384) (next := 7353) (x := 28118877000586) (y := 167603040976)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5760) (b := 384) (next := 6969) (x := 27675833330874) (y := 443043669712)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5376) (b := 384) (next := 6585) (x := 26850126737415) (y := 825706593459)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 6201) (x := 25570667217134) (y := 1279459520281)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5817) (x := 23801524109560) (y := 1769143107574)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5433) (x := 21552753981330) (y := 2248770128230)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 5049) (x := 18920013562450) (y := 2632740418880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4665) (x := 16039712951570) (y := 2880300610880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4281) (x := 13048880060370) (y := 2990832891200)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3897) (x := 10084542800530) (y := 2964337259840)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3513) (x := 7283729083730) (y := 2800813716800)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 3129) (x := 4783466821650) (y := 2500262262080)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2745) (x := 2720783925970) (y := 2062682895680)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2361) (x := 1232568769824) (y := 1488215156146)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1977) (x := 387508820160) (y := 845059949664)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1593) (x := 51366749280) (y := 336142070880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
theorem moment5798 : momentEstimate 5798 1223 = 30381132426145 := by
  change blockEstimate 5798 1223 1223 7021 = 30381132426145
  refine block_append (a := 6912) (b := 109) (next := 8135) (x := 30380486284103) (y := 646142042)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6528) (b := 384) (next := 7751) (x := 30325030115447) (y := 55456168656)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 6144) (b := 384) (next := 7367) (x := 30076738077095) (y := 248292038352)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5760) (b := 384) (next := 6983) (x := 29507898226563) (y := 568839850532)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 5376) (b := 384) (next := 6599) (x := 28518894167223) (y := 989004059340)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4992) (b := 384) (next := 6215) (x := 27046179406579) (y := 1472714760644)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4608) (b := 384) (next := 5831) (x := 25062913657050) (y := 1983265749529)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 4224) (b := 384) (next := 5447) (x := 22596200533050) (y := 2466713124000)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3840) (b := 384) (next := 5063) (x := 19761577004346) (y := 2834623528704)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3456) (b := 384) (next := 4679) (x := 16697645829690) (y := 3063931174656)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 3072) (b := 384) (next := 4295) (x := 13543020367674) (y := 3154625462016)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2688) (b := 384) (next := 3911) (x := 10436313976890) (y := 3106706390784)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 2304) (b := 384) (next := 3527) (x := 7516140015930) (y := 2920173960960)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1920) (b := 384) (next := 3143) (x := 4921111843386) (y := 2595028172544)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1536) (b := 384) (next := 2759) (x := 2789842817850) (y := 2131269025536)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 1152) (b := 384) (next := 2375) (x := 1260670239264) (y := 1529172578586)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 768) (b := 384) (next := 1991) (x := 395846010560) (y := 864824228704)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  refine block_append (a := 384) (b := 384) (next := 1607) (x := 52412963680) (y := 343433046880)
    ?_ (by rfl) (by decide) (by decide) (by decide)
  rfl
end P1_7_1_3_5
end
section
namespace P1_7_1_3_6
open P1_7_1_3 (blockEstimate block_append)
theorem append {B J start a x : ℕ} (left : blockEstimate B J start a = x)
    (next b y n z : ℕ) (hstart : start + a = next) (hlen : a + b = n) (hvalue : x + y = z)
    (right : blockEstimate B J next b = y) :
    blockEstimate B J start n = z :=
  block_append left right hstart hlen hvalue
end P1_7_1_3_6
end
section
namespace P1_7_1_3_6
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 8000
private theorem part0 : blockEstimate 10506 2218 2218 3072 = 38879167664736 := by
  have h0 : blockEstimate 10506 2218 2218 768 = 752677759680 := rfl
  have h1 := append h0 2986 768 4908442151616 1536 5661119911296 rfl rfl rfl rfl
  have h2 := append h1 3754 768 12256198429024 2304 17917318340320 rfl rfl rfl rfl
  have h3 := append h2 4522 768 20961849324416 3072 38879167664736 rfl rfl rfl rfl
  exact h3
private theorem part1 : blockEstimate 10506 2218 5290 3072 = 135349442891264 := by
  have h0 : blockEstimate 10506 2218 5290 768 = 28122400568192 := rfl
  have h1 := append h0 6058 768 33272605127552 1536 61395005695744 rfl rfl rfl rfl
  have h2 := append h1 6826 768 36412463002496 2304 97807468698240 rfl rfl rfl rfl
  have h3 := append h2 7594 768 37541974193024 3072 135349442891264 rfl rfl rfl rfl
  exact h3
private theorem part2 : blockEstimate 10506 2218 8362 3072 = 121728680363516 := by
  have h0 : blockEstimate 10506 2218 8362 768 = 36661138699136 := rfl
  have h1 := append h0 9130 768 33769956520832 1536 70431095219968 rfl rfl rfl rfl
  have h2 := append h1 9898 768 28870580603797 2304 99301675823765 rfl rfl rfl rfl
  have h3 := append h2 10666 768 22427004539751 3072 121728680363516 rfl rfl rfl rfl
  exact h3
private theorem part3 : blockEstimate 10506 2218 11434 3072 = 31498976875795 := by
  have h0 : blockEstimate 10506 2218 11434 768 = 15768359579110 := rfl
  have h1 := append h0 12202 768 9664895896493 1536 25433255475603 rfl rfl rfl rfl
  have h2 := append h1 12970 768 4686148763072 2304 30119404238675 rfl rfl rfl rfl
  have h3 := append h2 13738 768 1379572637120 3072 31498976875795 rfl rfl rfl rfl
  exact h3
private theorem part4 : blockEstimate 10506 2218 14506 436 = 71892394141 := by
  have h0 : blockEstimate 10506 2218 14506 436 = 71892394141 := rfl
  exact h0
theorem moment10506 : momentEstimate 10506 2218 = 327528160189452 := by
  change blockEstimate 10506 2218 2218 12724 = 327528160189452
  have h1 : blockEstimate 10506 2218 2218 6144 = 174228610556000 :=
    block_append part0 part1 rfl rfl rfl
  have h2 : blockEstimate 10506 2218 2218 9216 = 295957290919516 :=
    block_append h1 part2 rfl rfl rfl
  have h3 : blockEstimate 10506 2218 2218 12288 = 327456267795311 :=
    block_append h2 part3 rfl rfl rfl
  exact block_append h3 part4 rfl rfl rfl
end P1_7_1_3_6
end
