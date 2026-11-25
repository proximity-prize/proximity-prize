import ProximityPrize.SubmissionLower.KoalaCompression
import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ArkLib.Data.Polynomial.ResultantSpecialization

-- merged module R6960HeightCompression
section Merged_R6960HeightCompression
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Lower6960.HeightCompression
open Polynomial Matrix
open scoped BigOperators Polynomial Matrix
variable {F : Type*} [Field F] {ι α : Type*} [Fintype ι]
abbrev Coeffs (F : Type*) [Field F] {ι : Type*} (weight : ι→ℕ) (width : ℕ) :=
  ∀ j,degreeLT F (width-weight j)
def evaluation (A : Matrix α ι (Polynomial F)) (weight : ι→ℕ) (width : ℕ) :
    Coeffs F weight width →ₗ[F] (α→(Polynomial F)) where
  toFun v i := ∑ j,A i j*(v j : (Polynomial F))
  map_add' v w := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c v := by funext i; simp [Finset.smul_sum]
theorem weighted_kernel [Finite α] (A : Matrix α ι (Polynomial F)) (weight : ι→ℕ) (width : ℕ)
    (col : ∀ i j,(A i j).natDegree≤weight j) (k : ℕ)
    (ker : k≤Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    (∑ j : ι, (width-weight j)) ≤ (Fintype.card ι-k)*width+
      Module.finrank F (LinearMap.ker (evaluation A weight width)) := by
  classical
  let E:=FractionRing (Polynomial F)
  let a:=algebraMap (Polynomial F) E
  let M:=A.map a
  let R:=Submodule.span E (Set.range M.row)
  let m:=Module.finrank E R
  have rank : m+Module.finrank E (LinearMap.ker M.mulVecLin)=Fintype.card ι := by
    have h:=M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank+_= _ at h
    rw [M.rank_eq_finrank_span_row,Module.finrank_pi_fintype] at h
    simpa [m,R] using h
  have bound : m≤Fintype.card ι-k := by
    change k≤Module.finrank E (LinearMap.ker M.mulVecLin) at ker
    omega
  obtain ⟨B,mem,span,_⟩:=Submodule.exists_fun_fin_finrank_span_eq E (Set.range M.row)
  change Fin m → (ι→E) at B
  choose row hrow using mem
  have fits (v : Coeffs F weight width) (i : α) :
      (evaluation A weight width v i)∈degreeLT F width := by
    apply Submodule.sum_mem
    intro j _
    by_cases z : (v j : (Polynomial F))=0
    · simp [z]
    by_cases c : A i j=0
    · simp [c]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero c z)).mp
    have h:= (natDegree_lt_iff_degree_lt z).mpr (mem_degreeLT.mp (v j).property)
    have u:= (natDegree_mul_le (p:=A i j) (q:=(v j:(Polynomial F)))).trans (Nat.add_le_add_right (col i j) _)
    omega
  let small : Coeffs F weight width →ₗ[F] (Fin m → degreeLT F width) :=
    LinearMap.pi fun i => (((LinearMap.proj (row i)).comp (evaluation A weight width)).codRestrict
      (degreeLT F width) (fun v => fits v (row i)))
  have eq : LinearMap.ker small=LinearMap.ker (evaluation A weight width) := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv
      let ev : ι→E:=fun j=>a (v j : (Polynomial F))
      have hb (i : Fin m) : B i ⬝ᵥ ev=0 := by
        rw [←hrow i]
        have h:=congrArg (fun g : Fin m → degreeLT F width => (g i : (Polynomial F))) hv
        change (∑ j,A (row i) j*(v j : (Polynomial F)))=0 at h
        simpa [ev,M,Matrix.row,dotProduct] using congrArg a h
      funext i
      apply IsFractionRing.injective (Polynomial F) E
      have hi : M.row i∈Submodule.span E (Set.range B) := by
        rw [span]; exact Submodule.subset_span ⟨i,rfl⟩
      have zero : M.row i ⬝ᵥ ev=0 := by
        refine Submodule.span_induction (p:=fun x _=>x ⬝ᵥ ev=0) ?_ ?_ ?_ ?_ hi
        · rintro _ ⟨j,rfl⟩; exact hb j
        · exact zero_dotProduct _
        · intro x y _ _ hx hy; rw [add_dotProduct,hx,hy,add_zero]
        · intro c x _ hx; rw [smul_dotProduct,hx,smul_zero]
      simpa [evaluation,ev,M,Matrix.row,dotProduct] using zero
    · intro hv
      funext i
      apply Subtype.ext
      exact congrFun hv (row i)
  have source : Module.finrank F (Coeffs F weight width)=∑ j : ι, (width-weight j) := by
    simp [Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have target : Module.finrank F (Fin m → degreeLT F width)=m*width := by
    simp [Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have size:=small.finrank_range_add_finrank_ker
  rw [source,eq] at size
  rw [←size]
  exact Nat.add_le_add_right ((Submodule.finrank_le ..).trans
    (target.le.trans (Nat.mul_le_mul_right _ bound))) _
#print axioms weighted_kernel
end Lower6960.HeightCompression

end
end Merged_R6960HeightCompression

-- merged module R6960RetainedCompressionVolume
section Merged_R6960RetainedCompressionVolume
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix
abbrev Slots (a b : ℕ) := Fin (a+1) × Fin (b+1)
def columnWeight {a b : ℕ} (d : ℕ) (m : Slots a b) : ℕ := d*m.1.val
private theorem twice_width_sum (a b d W : ℕ) (hW : d*a≤W) :
    2*(∑ m : Slots a b, (W - columnWeight d m))+d*(b+1)*a*(a+1) =
      2*((a+1)*(b+1))*W := by
  have split : (∑ m : Slots a b, (W - columnWeight d m)) +
      (∑ m : Slots a b, columnWeight d m) = ((a+1)*(b+1))*W := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Slots a b, W := Finset.sum_congr rfl (fun m _ => Nat.sub_add_cancel
        ((Nat.mul_le_mul_left d (Nat.le_of_lt_succ m.1.isLt)).trans hW))
      _ = _ := by simp
  have weight : 2*(∑ m : Slots a b, columnWeight d m)=d*(b+1)*a*(a+1) := by
    rw [Fintype.sum_prod_type]
    simp only [columnWeight, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    simp only [← mul_assoc, ← Finset.mul_sum]
    have sum : (∑ i : Fin (a+1), i.val) = ∑ i∈range (a+1), i :=
      Fin.sum_univ_eq_sum_range (fun i => i) (a+1)
    rw [sum]
    calc
      _ = d*(b+1)*((∑ i∈range (a+1), i)*2) := by ring
      _ = _ := by rw [Finset.sum_range_id_mul_two,Nat.add_sub_cancel]; ring
  calc
    _ = 2*((∑ m : Slots a b, (W - columnWeight d m)) +
        (∑ m : Slots a b, columnWeight d m)) := by rw [← weight, ← Nat.mul_add]
    _ = _ := by rw [split]; ring
def paddedSeed (v : ℕ) : ℕ := 10*v
def quotientSeed (v : ℕ) : ℕ := 9*v
def quotientOrdinate (e : ℕ) : ℕ := 3*e
def boxOrdinate (e : ℕ) : ℕ := 4*e
def heightCap (e d : ℕ) : ℕ := ((3*e+1)/2)*d
def quotientWidth (e d : ℕ) : ℕ := 3*e*d+1
def width (e d : ℕ) : ℕ := heightCap e d+quotientWidth e d
abbrev Rect (e v : ℕ) := Slots (boxOrdinate e) (paddedSeed v)
abbrev QuotRect (e v : ℕ) := Slots (quotientOrdinate e) (quotientSeed v)
private theorem count_comparison (e v d : ℕ) (he : 2≤e) (hd : 0<d) :
    (Fintype.card (Rect e v)-Fintype.card (QuotRect e v))*width e d +
      (∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)) <
      ∑ m : Rect e v, (width e d - columnWeight d m) := by
  let N := (4*e+1)*(10*v+1)
  let K := (3*e+1)*(9*v+1)
  have kN : K≤N := Nat.mul_le_mul (by omega) (by omega)
  have large : d*(4*e)≤width e d := by
    unfold width heightCap quotientWidth
    have h1 : 4*e ≤ (3*e+1)/2 + 3*e := by omega
    calc d*(4*e) = (4*e)*d := Nat.mul_comm _ _
      _ ≤ ((3*e+1)/2 + 3*e)*d := Nat.mul_le_mul_right d h1
      _ = ((3*e+1)/2)*d + 3*e*d := Nat.add_mul _ _ _
      _ ≤ _ := by omega
  have small : d*(3*e)≤quotientWidth e d := by
    unfold quotientWidth; rw [Nat.mul_comm d (3*e)]; omega
  let src := ∑ m : Rect e v, (width e d - columnWeight d m)
  let qt := ∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)
  have dl : 2*src+d*(10*v+1)*(4*e)*(4*e+1)=2*N*width e d :=
    twice_width_sum (4*e) (10*v) d (width e d) large
  have ds : 2*qt+d*(9*v+1)*(3*e)*(3*e+1)=2*K*quotientWidth e d :=
    twice_width_sum (3*e) (9*v) d (quotientWidth e d) small
  have total : 2*N*width e d=2*((N-K)*width e d)+2*K*width e d := by
    calc
      _ = 2*(N-K+K)*width e d := by rw [Nat.sub_add_cancel kN]
      _ = _ := by ring
  have hhc : 3*e*d ≤ 2*heightCap e d := by
    unfold heightCap
    have h1 : 3*e ≤ 2*((3*e+1)/2) := by omega
    calc 3*e*d ≤ (2*((3*e+1)/2))*d := Nat.mul_le_mul_right d h1
      _ = 2*(((3*e+1)/2)*d) := by ring
  have h2Kw : 2*K*quotientWidth e d + 3*e*d*K ≤ 2*K*width e d := by
    have h1 := Nat.mul_le_mul_left K hhc
    unfold width
    linarith only [h1]
  have hdiff : d*(10*v+1)*(4*e)*(4*e+1) + d*(e*((2*e+14)*v+2*e+2)) =
      d*(9*v+1)*(3*e)*(3*e+1) + 3*e*d*K := by
    dsimp only [K]; ring
  have positive : 0<d*(e*((2*e+14)*v+2*e+2)) := by positivity
  have cards : Fintype.card (Rect e v)=N ∧ Fintype.card (QuotRect e v)=K := by
    constructor
    · change Fintype.card (Fin (4*e+1) × Fin (10*v+1))=(4*e+1)*(10*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
    · change Fintype.card (Fin (3*e+1) × Fin (9*v+1))=(3*e+1)*(9*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
  rw [cards.1,cards.2]
  change (N-K)*width e d+qt<src
  omega
theorem relation_space_gt {F : Type*} [Field F] {α : Type*} [Finite α]
    {e v d : ℕ} (he : 2≤e) (hd : 0<d) (A : Matrix α (Rect e v) (Polynomial F))
    (columns : ∀ i j,(A i j).natDegree≤columnWeight d j)
    (ker : Fintype.card (QuotRect e v) ≤ Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) <
      Module.finrank F (LinearMap.ker (HeightCompression.evaluation A
        (columnWeight d) (width e d))) := by
  have lower := HeightCompression.weighted_kernel A (columnWeight d) (width e d)
    columns (Fintype.card (QuotRect e v)) ker
  have large := count_comparison e v d he hd
  have dim : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) =
      ∑ j : QuotRect e v, (quotientWidth e d - columnWeight d j) := by
    simp [HeightCompression.Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  rw [dim]
  omega
def TameBand (e d : ℕ) : Prop := (e < 48 ∧ d ≤ 164670) ∨ (e < 64 ∧ d ≤ 133453)
theorem TameBand.lt_64 {e d : ℕ} (h : TameBand e d) : e < 64 := by unfold TameBand at h; omega
theorem TameBand.lt_p {e d : ℕ} (h : TameBand e d) : e < K1.p := h.lt_64.trans (by decide)
theorem TameBand.mono_left {e n d : ℕ} (h : e ≤ n) (hn : TameBand n d) : TameBand e d := by
  rcases hn with ⟨hn, hd⟩ | ⟨hn, hd⟩
  · exact Or.inl ⟨by omega, hd⟩
  · exact Or.inr ⟨by omega, hd⟩
theorem tame_resultant_bound {e d : ℕ} (he : 2 ≤ e) (ht : TameBand e d) :
    2 * ((2*e - 1) * heightCap e d - d * e^2) + 2 * (e - 1) < K1.p := by
  have h48 : ∀ i : Fin 48, 2 ≤ i.val →
      2 * ((2*i.val - 1) * heightCap i.val 164670 - 164670 * i.val^2) + 2 * (i.val - 1) < K1.p := by
    decide +kernel
  have h64 : ∀ i : Fin 64, 2 ≤ i.val →
      2 * ((2*i.val - 1) * heightCap i.val 133453 - 133453 * i.val^2) + 2 * (i.val - 1) < K1.p := by
    decide +kernel
  have hfactor (e' d' : ℕ) :
      (2*e' - 1) * heightCap e' d' - d' * e'^2 = ((2*e' - 1) * ((3*e' + 1) / 2) - e'^2) * d' := by
    unfold heightCap
    rw [← Nat.mul_assoc (2*e' - 1), Nat.mul_comm d' (e'^2), ← Nat.mul_sub_right_distrib]
  rcases ht with ⟨hl, hd⟩ | ⟨hl, hd⟩
  · have h := h48 ⟨e, hl⟩ he
    dsimp only at h
    rw [hfactor] at h ⊢
    have hm := Nat.mul_le_mul_left ((2*e - 1) * ((3*e + 1) / 2) - e^2) hd
    omega
  · have h := h64 ⟨e, hl⟩ he
    dsimp only at h
    rw [hfactor] at h ⊢
    have hm := Nat.mul_le_mul_left ((2*e - 1) * ((3*e + 1) / 2) - e^2) hd
    omega
theorem tame_vertical_bound {e d : ℕ} (ht : TameBand e d) :
    2 * ((e - 1) * heightCap e d) < K1.p := by
  have h48 : ∀ i : Fin 48, 2 * ((i.val - 1) * heightCap i.val 164670) < K1.p := by decide +kernel
  have h64 : ∀ i : Fin 64, 2 * ((i.val - 1) * heightCap i.val 133453) < K1.p := by decide +kernel
  rcases ht with ⟨hl, hd⟩ | ⟨hl, hd⟩
  · have h := h48 ⟨e, hl⟩
    dsimp only at h
    unfold heightCap at h ⊢
    have hm := Nat.mul_le_mul_left (e - 1) (Nat.mul_le_mul_left ((3*e + 1) / 2) hd)
    omega
  · have h := h64 ⟨e, hl⟩
    dsimp only at h
    unfold heightCap at h ⊢
    have hm := Nat.mul_le_mul_left (e - 1) (Nat.mul_le_mul_left ((3*e + 1) / 2) hd)
    omega
theorem tame_height {e d : ℕ} (he : e≤47) (hd : d≤164650) :
    2*((3*e-2)*(e-1)*d+(e-1))<2130706433 :=
  (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 he) 2)
      (Nat.sub_le_sub_right he 1)) hd)
    (Nat.sub_le_sub_right he 1))).trans_lt (by decide +kernel)
#print axioms relation_space_gt
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionVolume

-- merged module R6960RetainedCompressionBox
section Merged_R6960RetainedCompressionBox
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial MvPolynomial Finset
open scoped Polynomial BigOperators Pointwise
abbrev Index : Type := Option PUnit
abbrev Exponent := Index →₀ ℕ
abbrev Curve (A : Type*) [CommSemiring A] := MvPolynomial Index A
abbrev ordinate : Index := none
abbrev parameter : Index := some PUnit.unit
def Exponents (a b : ℕ) : Set Exponent :=
  {m | m ordinate≤a ∧ m parameter≤b}
def exponent {a b} (m : Slots a b) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun i : Index => i.elim m.1.val (fun _ => m.2.val))
@[simp] theorem exponent_y {a b} (m : Slots a b) :
    exponent m ordinate=m.1.val := by simp [exponent]
@[simp] theorem exponent_z {a b} (m : Slots a b) :
    exponent m parameter=m.2.val := by simp [exponent]
theorem exponent_injective {a b} : Function.Injective (exponent (a:=a) (b:=b)) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    simpa only [exponent_y] using congrArg (fun m : Exponent => m ordinate) h
  · apply Fin.ext
    simpa only [exponent_z] using congrArg (fun m : Exponent => m parameter) h
theorem exponent_exhaustive {a b} {t : Exponent} (h : t∈Exponents a b) :
    ∃ m : Slots a b, exponent m=t := by
  refine ⟨⟨⟨_,Nat.lt_succ_of_le h.1⟩,⟨_,Nat.lt_succ_of_le h.2⟩⟩,?_⟩
  ext i
  cases i with
  | none => simp
  | some i => cases i; simp
abbrev Box (A : Type*) [CommSemiring A] (a b : ℕ) :=
  MvPolynomial.restrictSupport A (Exponents a b)
theorem box_iff {A : Type*} [CommSemiring A] (Q : Curve A) (a b : ℕ) :
    Q∈Box A a b ↔ Q.degreeOf ordinate≤a ∧ Q.degreeOf parameter≤b := by
  change (∀ m∈Q.support,m∈Exponents a b) ↔ _
  simp only [MvPolynomial.degreeOf_le_iff,Exponents,Set.mem_setOf_eq]
  exact ⟨fun h => ⟨fun m mQ => (h m mQ).1,fun m mQ => (h m mQ).2⟩,
    fun h m mQ => ⟨h.1 m mQ,h.2 m mQ⟩⟩
private def underlyingWeight (d : ℕ) (i : Option Index) : ℕ :=
  i.elim 1 (fun j => j.elim d (fun _ => 0))
def height {F : Type*} [Field F] (d : ℕ) (Q : Curve (Polynomial F)) : ℕ :=
  ((MvPolynomial.optionEquivRight F Index).symm Q).weightedTotalDegree (underlyingWeight d)
theorem height_mul {F : Type*} [Field F] (d : ℕ) {P Q : Curve (Polynomial F)} (pn : P≠0) (qn : Q≠0) :
    height d (P*Q)=height d P+height d Q := by
  let f := (MvPolynomial.optionEquivRight F Index).symm
  unfold height
  rw [map_mul,MvPolynomial.weightedTotalDegree_mul]
  · exact (map_ne_zero_iff f.toRingHom f.injective).mpr pn
  · exact (map_ne_zero_iff f.toRingHom f.injective).mpr qn
private theorem weight_exp (d i : ℕ) (m : Exponent) :
    (m.optionElim i).weight (underlyingWeight d)=i+d*m ordinate := by
  unfold underlyingWeight
  rw [Finsupp.weight_optionElim, one_mul]
  congr 1
  conv_lhs => rw [← Finsupp.optionElim_some m]
  rw [Finsupp.weight_optionElim]
  simp [Finsupp.weight_apply]
private theorem coeff_split {F : Type*} [Field F] (Q : Curve (Polynomial F)) (m : Exponent) (i : ℕ) :
    ((MvPolynomial.optionEquivRight F Index).symm Q).coeff (m.optionElim i) =
      (Q.coeff m).coeff i := by
  rw [← MvPolynomial.optionEquivRight_coeff_coeff,
    AlgEquiv.apply_symm_apply]
theorem coeff_height {F : Type*} [Field F] (d : ℕ) (Q : Curve (Polynomial F)) (m : Exponent)
    (nz : Q.coeff m≠0) : (Q.coeff m).natDegree+d*m ordinate≤height d Q := by
  have pos : m.optionElim (Q.coeff m).natDegree ∈
      ((MvPolynomial.optionEquivRight F Index).symm Q).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [coeff_split,Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr nz
  have bound := MvPolynomial.le_weightedTotalDegree (underlyingWeight d) pos
  rwa [weight_exp] at bound
theorem height_lt_of_coeff {F : Type*} [Field F] {d W : ℕ} (positive : 0<W) (Q : Curve (Polynomial F))
    (caps : ∀ m, Q.coeff m≠0 → (Q.coeff m).natDegree+d*m ordinate<W) :
    height d Q<W := by
  apply Nat.lt_of_le_of_lt _ (Nat.sub_lt positive (by decide : 0 < (1 : ℕ)))
  unfold height MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  rw [← Finsupp.optionElim_some m] at hm ⊢
  rw [weight_exp]
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_split] at hn
  have hi := Polynomial.le_natDegree_of_ne_zero hn
  have hc := caps m.some (fun z => hn (by rw [z,Polynomial.coeff_zero]))
  have h := (Nat.add_le_add_right hi _).trans_lt hc
  omega
def packed {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    Curve (Polynomial F) := ∑ m : Slots a b, MvPolynomial.monomial (exponent m) (v m : (Polynomial F))
def packLinear (F : Type*) [Field F] (a b d W : ℕ) :
    HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W →ₗ[F] Curve (Polynomial F) where
  toFun := packed
  map_add' v u := by
    simp only [packed,Pi.add_apply,Submodule.coe_add,map_add,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [packed,Pi.smul_apply,Submodule.coe_smul,RingHom.id_apply,
      Finset.smul_sum,MvPolynomial.smul_monomial]
@[simp] theorem coeff_pack {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W)
    (m : Slots a b) :
    (packLinear F a b d W v).coeff (exponent m)=(v m : (Polynomial F)) := by
  classical
  change (packed v).coeff (exponent m)=_
  rw [packed,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
  · simp
  · intro j _ ne
    rw [MvPolynomial.coeff_monomial, if_neg (exponent_injective.ne ne)]
private theorem coeff_pack_other {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W)
    {m : Exponent} (no : ∀ j : Slots a b, exponent j≠m) :
    (packLinear F a b d W v).coeff m=0 := by
  change (packed v).coeff m=0
  rw [packed,MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero (fun j _ => by rw [MvPolynomial.coeff_monomial, if_neg (no j)])
theorem pack_injective {F : Type*} [Field F] (a b d W : ℕ) :
    Function.Injective (packLinear F a b d W) := by
  intro v w eq
  funext i
  apply Subtype.ext
  rw [← coeff_pack v i,← coeff_pack w i,eq]
theorem pack_box {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    packLinear F a b d W v∈Box (Polynomial F) a b := by
  classical
  change ∀ m∈(packed v).support,m∈Exponents a b
  intro m pm
  by_contra hm
  have no (j : Slots a b) : exponent j≠m := by
    intro e
    apply hm
    rw [← e]
    exact ⟨by simpa only [exponent_y] using Nat.le_of_lt_succ j.1.isLt,
      by simpa only [exponent_z] using Nat.le_of_lt_succ j.2.isLt⟩
  exact MvPolynomial.mem_support_iff.mp pm (coeff_pack_other v no)
theorem pack_height {F : Type*} [Field F] {a b d W : ℕ} (positive : 0<W)
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    height d (packLinear F a b d W v)<W := by
  apply height_lt_of_coeff positive
  intro m nz
  have fit : m∈Exponents a b := (pack_box v) (MvPolynomial.mem_support_iff.mpr nz)
  obtain ⟨j,rfl⟩ := exponent_exhaustive fit
  rw [coeff_pack] at nz ⊢
  rw [exponent_y]
  have hc := (Polynomial.natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp (v j).property)
  change (v j : (Polynomial F)).natDegree < W-d*j.1.val at hc
  omega
theorem represented {F : Type*} [Field F] {a b d W : ℕ}
    (Q : Curve (Polynomial F)) (box : Q∈Box (Polynomial F) a b) (cap : height d Q<W) :
    ∃ v, packLinear F a b d W v=Q := by
  classical
  let v (j : Slots a b) : degreeLT F (W-columnWeight d j) :=
    ⟨Q.coeff (exponent j),by
      by_cases h : Q.coeff (exponent j)=0
      · rw [h]; exact Submodule.zero_mem _
      apply mem_degreeLT.mpr
      apply (Polynomial.natDegree_lt_iff_degree_lt h).mp
      have le := (coeff_height d Q (exponent j) h).trans_lt cap
      rw [exponent_y] at le
      change _ < W-d*j.1.val
      omega⟩
  refine ⟨v,?_⟩
  ext m
  by_cases hz : Q.coeff m=0
  · by_cases hi : ∃ j : Slots a b, exponent j=m
    · obtain ⟨j,rfl⟩ := hi
      rw [coeff_pack]
    · rw [coeff_pack_other v (fun j hj => hi ⟨j,hj⟩), hz]
  · obtain ⟨j,rfl⟩ := exponent_exhaustive (box (MvPolynomial.mem_support_iff.mpr hz))
    rw [coeff_pack]
#print axioms height_mul
#print axioms represented
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionBox

-- merged module R6960RetainedCompressionRelations
section Merged_R6960RetainedCompressionRelations
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix
private def vectorPoly {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) : Curve A :=
  ∑ m : Slots a b, MvPolynomial.monomial (exponent m) (v m)
private theorem coeff_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (v : Slots a b→A) (j : Slots a b) : (vectorPoly v).coeff (exponent j)=v j := by
  classical
  rw [vectorPoly,MvPolynomial.coeff_sum,Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ neq
    rw [MvPolynomial.coeff_monomial, if_neg (exponent_injective.ne neq)]
private theorem vector_box {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) :
    vectorPoly v∈Box A a b := by
  classical
  change ∀ m∈(vectorPoly v).support,m∈Exponents a b
  intro m mem
  by_contra fit
  apply MvPolynomial.mem_support_iff.mp mem
  rw [vectorPoly,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_monomial]
  apply if_neg
  intro eq
  apply fit
  rw [← eq]
  exact ⟨by simpa only [exponent_y] using Nat.le_of_lt_succ j.1.isLt,
    by simpa only [exponent_z] using Nat.le_of_lt_succ j.2.isLt⟩
private theorem vector_recover {A : Type*} [CommSemiring A] {a b : ℕ} (Q : Curve A)
    (fit : Q∈Box A a b) : vectorPoly (fun j : Slots a b => Q.coeff (exponent j))=Q := by
  classical
  ext m
  by_cases has : ∃ j : Slots a b, exponent j=m
  · obtain ⟨j,rfl⟩ := has
    exact coeff_vector _ j
  have zero (W : Curve A) (hW : W∈Box A a b) : W.coeff m=0 := by
    by_contra hn
    exact has (exponent_exhaustive (hW (MvPolynomial.mem_support_iff.mpr hn)))
  rw [zero _ (vector_box _), zero _ fit]
def evaluate {F : Type*} [Field F] (z : F) (S : (Polynomial F)) : Curve (Polynomial F) →+* (Polynomial F) :=
  MvPolynomial.eval (fun j : Index => j.elim S (fun _ => C z))
def markMatrix {F α : Type*} [Field F] (z : α→F) (S : α→(Polynomial F)) (a b : ℕ) :
    Matrix α (Slots a b) (Polynomial F) :=
  Matrix.of fun i j => S i ^ j.1.val * C (z i ^ j.2.val)
private theorem mark_degree {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) (d a b : ℕ) (deg : ∀ i,(S i).natDegree≤d) :
    ∀ i j,(markMatrix z S a b i j).natDegree≤columnWeight d j := by
  intro i j
  have h := Polynomial.natDegree_mul_le
    (p:=S i ^ j.1.val) (q:=C (z i ^ j.2.val))
  rw [natDegree_C,add_zero] at h
  exact h.trans ((Polynomial.natDegree_pow_le_of_le _ (deg i)).trans_eq (Nat.mul_comm _ _))
private theorem eval_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (s z : A) (V : Slots a b→A) :
    MvPolynomial.eval (fun j : Index => j.elim s (fun _ => z)) (vectorPoly V) =
      ∑ j : Slots a b, (s^j.1.val*z^j.2.val)*V j := by
  classical
  rw [vectorPoly,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option]
  simp only [Option.elim_none,Option.elim_some,exponent_y,Fintype.prod_unique,exponent_z]
  ac_rfl
private theorem eval_map_incl {F : Type*} [Field F] (z : F) (S : (Polynomial F)) (Q : Curve (Polynomial F)) :
    MvPolynomial.eval (fun j : Index => j.elim
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) S)
        (fun _ => algebraMap (Polynomial F) (FractionRing (Polynomial F)) (C z)))
      (MvPolynomial.map (algebraMap (Polynomial F) (FractionRing (Polynomial F))) Q) =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) (evaluate z S Q) := by
  let incl := algebraMap (Polynomial F) (FractionRing (Polynomial F))
  have ring : (MvPolynomial.eval (fun j : Index => j.elim (incl S) (fun _ => incl (C z)))).comp
      (MvPolynomial.map incl) = incl.comp (evaluate z S) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [evaluate]
    · intro i; cases i <;> simp [evaluate]
  exact DFunLike.congr_fun ring Q
theorem rational_kernel {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (f : Curve (Polynomial F)) (fn : f≠0) (e v : ℕ)
    (box : f∈Box (Polynomial F) e v) (marks : ∀ i,evaluate (z i) (S i) f=0) :
    Fintype.card (QuotRect e v)≤Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker ((markMatrix z S (boxOrdinate e) (paddedSeed v)).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin) := by
  classical
  let E := FractionRing (Polynomial F)
  let j := algebraMap (Polynomial F) E
  let g := MvPolynomial.map j f
  let W := markMatrix z S (boxOrdinate e) (paddedSeed v)
  have gn : g≠0 := (map_ne_zero_iff _ (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial F) E))).mpr fn
  have gbox : g∈Box E e v := by
    change ∀ m∈g.support,m∈Exponents e v
    have supp : g.support=f.support :=
      MvPolynomial.support_map_of_injective f (IsFractionRing.injective (Polynomial F) E)
    rw [supp]
    exact box
  let mulVec : (QuotRect e v→E) →ₗ[E] (Rect e v→E) := {
    toFun := fun u m => (g*vectorPoly u).coeff (exponent m)
    map_add' := fun u w => by
      funext m
      have add : vectorPoly (u+w)=vectorPoly u+vectorPoly w := by
        simp only [vectorPoly, Pi.add_apply, map_add, Finset.sum_add_distrib]
      change (g*vectorPoly (u+w)).coeff (exponent m)=_
      rw [add,mul_add,MvPolynomial.coeff_add]
      rfl
    map_smul' := fun a u => by
      funext m
      have smul : vectorPoly (a • u)=a • vectorPoly u := by
        simp only [vectorPoly,Pi.smul_apply,Finset.smul_sum,MvPolynomial.smul_monomial]
      change (g*vectorPoly (a • u)).coeff (exponent m)=_
      rw [smul,mul_smul_comm,MvPolynomial.coeff_smul]
      rfl }
  have recovered (u : QuotRect e v→E) : vectorPoly (mulVec u)=g*vectorPoly u := by
    apply vector_recover
    have h := (box_iff _ _ _).mp gbox
    have hs := (box_iff _ _ _).mp (vector_box u)
    apply (box_iff _ _ _).mpr
    refine ⟨(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_,(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_⟩
    · exact (Nat.add_le_add h.1 hs.1).trans (by unfold boxOrdinate quotientOrdinate; omega)
    · exact (Nat.add_le_add h.2 hs.2).trans (by unfold paddedSeed quotientSeed; omega)
  have kernel (u : QuotRect e v→E) : mulVec u∈LinearMap.ker (W.map j).mulVecLin := by
    rw [LinearMap.mem_ker]
    funext i
    have h := eval_vector (j (S i)) (j (C (z i))) (mulVec u)
    have eq : (W.map j).mulVecLin (mulVec u) i =
        MvPolynomial.eval (fun v : Index => v.elim (j (S i)) (fun _ => j (C (z i))))
          (vectorPoly (mulVec u)) := by
      rw [h]
      change (∑ m : Rect e v, j (W i m) * mulVec u m)=_
      simp only [W,markMatrix,Matrix.of_apply,map_mul,map_pow,C_pow]
    rw [eq,recovered,map_mul]
    change MvPolynomial.eval _ (MvPolynomial.map j f) * _ = 0
    rw [eval_map_incl,marks i,map_zero,zero_mul]
  have inject : Function.Injective (mulVec.codRestrict _ kernel) := by
    intro u w eq
    have eu : mulVec u=mulVec w := congrArg Subtype.val eq
    have ew := congrArg vectorPoly eu
    rw [recovered,recovered] at ew
    have V := mul_left_cancel₀ gn ew
    funext j
    exact (coeff_vector _ j).symm.trans ((congrArg (fun P : Curve E => P.coeff (exponent j)) V).trans (coeff_vector _ j))
  have dim := LinearMap.finrank_le_finrank_of_injective inject
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,card_univ,
    nsmul_eq_mul,mul_one,Nat.cast_id,W,j,E] using dim
private theorem eval_packed {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) {a b d W : ℕ}
    (u : HeightCompression.Coeffs F (fun j : Slots a b => columnWeight d j) W) (i : α) :
    evaluate (z i) (S i) (packLinear F a b d W u) =
      HeightCompression.evaluation (markMatrix z S a b) (columnWeight d) W u i := by
  change evaluate (z i) (S i) (vectorPoly (fun j => (u j : (Polynomial F))))=_
  unfold evaluate
  rw [eval_vector]
  simp [HeightCompression.evaluation,markMatrix,C_pow]
theorem escape {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (d : ℕ) (hd : 0<d) (degree : ∀ i,(S i).natDegree≤d)
    (f : Curve (Polynomial F)) (fn : f≠0) {e v : ℕ} (he : 2≤e)
    (ed : f.degreeOf ordinate=e) (vd : f.degreeOf parameter=v)
    (marks : ∀ i,evaluate (z i) (S i) f=0) (hlarge : heightCap e d<height d f) :
    ∃ G : Curve (Polynomial F), G≠0 ∧ ¬ f∣G ∧ G∈Box (Polynomial F) (boxOrdinate e) (paddedSeed v) ∧
      height d G<width e d ∧ ∀ i,evaluate (z i) (S i) G=0 := by
  classical
  let A := markMatrix z S (boxOrdinate e) (paddedSeed v)
  let ker := LinearMap.ker (HeightCompression.evaluation A (columnWeight d) (width e d))
  let pack := packLinear F (boxOrdinate e) (paddedSeed v) d (width e d)
  let mult := (LinearMap.mulLeft F f).comp (packLinear F (quotientOrdinate e) (quotientSeed v) d (quotientWidth e d))
  have ker_size : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) < Module.finrank F ker :=
    relation_space_gt he hd A (mark_degree z S d _ _ degree)
      (rational_kernel z S f fn e v ((box_iff _ _ _).mpr ⟨ed.le,vd.le⟩) marks)
  by_contra! h
  have all (u : ker) : f ∣ pack u.val := by
    by_cases zero : pack u.val=0
    · rw [zero]; exact dvd_zero f
    by_contra! bad
    obtain ⟨i,wrong⟩ := h (pack u.val) zero bad (pack_box u.val)
      (pack_height (by unfold width quotientWidth; omega) u.val)
    apply wrong
    change evaluate (z i) (S i) (packLinear F (boxOrdinate e) (paddedSeed v) d (width e d) u.val)=0
    rw [eval_packed]
    exact congrFun (LinearMap.mem_ker.mp u.property) i
  have fits (u : ker) : pack u.val∈LinearMap.range mult := by
    by_cases zero : pack u.val=0
    · exact zero ▸ Submodule.zero_mem _
    obtain ⟨Q,eq⟩ := all u
    have qn : Q≠0 := fun no => zero (by rw [eq,no,mul_zero])
    have dQ : Q∈Box (Polynomial F) (quotientOrdinate e) (quotientSeed v) := by
      have fit := (box_iff _ _ _).mp (pack_box u.val)
      change (pack u.val).degreeOf ordinate≤_ ∧ (pack u.val).degreeOf parameter≤_ at fit
      rw [eq,MvPolynomial.degreeOf_mul_eq fn qn,MvPolynomial.degreeOf_mul_eq fn qn,ed,vd] at fit
      apply (box_iff _ _ _).mpr
      unfold boxOrdinate quotientOrdinate paddedSeed quotientSeed at *
      omega
    have wQ : height d Q<quotientWidth e d := by
      have top := pack_height (by unfold width quotientWidth; omega) u.val
      change height d (pack u.val)<width e d at top
      rw [eq,height_mul d fn qn] at top
      unfold width at top
      omega
    obtain ⟨w,hw⟩ := represented Q dQ wQ
    refine ⟨w,?_⟩
    change f*(packLinear F (quotientOrdinate e) (quotientSeed v) d (quotientWidth e d) w)=_
    rw [hw,eq]
  let emb := (pack.comp ker.subtype).codRestrict _ fits
  have hn : Function.Injective emb := by
    intro u v eq
    apply Subtype.ext
    exact pack_injective _ _ _ _ (congrArg Subtype.val eq)
  have short := LinearMap.finrank_le_finrank_of_injective hn
  exact (not_lt_of_ge (short.trans mult.finrank_range_le)) ker_size
#print axioms rational_kernel
#print axioms escape
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionRelations

-- merged module R6960RetainedCompressionCut
section Merged_R6960RetainedCompressionCut
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1_14 (L)
open CurvatureSquares (Ordinate zView coeff_swap)
open scoped Polynomial
private def raw {A : Type*} [CommSemiring A] : Curve A ≃+* Polynomial (Polynomial A) :=
  (MvPolynomial.optionEquivLeft A PUnit).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv A PUnit).toRingEquiv)
def view : Curve (Polynomial L) ≃+* Ordinate :=
  raw.trans (Polynomial.mapEquiv Bivariate.swap.toRingEquiv)
private theorem raw_y {A : Type*} [CommSemiring A] (Q : Curve A) :
    (raw Q).natDegree=Q.degreeOf ordinate := by
  change (((MvPolynomial.optionEquivLeft A PUnit Q).map
    (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom).natDegree)=_
  trans (MvPolynomial.optionEquivLeft A PUnit Q).natDegree
  · exact natDegree_map_eq_of_injective
      (f := (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom)
      (MvPolynomial.uniqueAlgEquiv A PUnit).injective _
  · exact MvPolynomial.natDegree_optionEquivLeft A Q
theorem view_y (Q : Curve (Polynomial L)) : (view Q).natDegree=Q.degreeOf ordinate := by
  change (((raw Q).map Bivariate.swap.toRingHom).natDegree)=_
  exact (natDegree_map_eq_of_injective (f:=Bivariate.swap.toRingHom)
    Bivariate.swap.injective _).trans (raw_y Q)
private theorem coeff_raw {A : Type*} [CommSemiring A] (Q : Curve A) (i j : ℕ) :
    ((raw Q).coeff i).coeff j =
      Q.coeff ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i) := by
  change (((MvPolynomial.optionEquivLeft A PUnit Q).map
    (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom).coeff i).coeff j=_
  rw [coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv A PUnit)
    ((MvPolynomial.optionEquivLeft A PUnit Q).coeff i)).coeff j = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,MvPolynomial.optionEquivLeft_coeff_coeff]
private theorem raw_seed {A : Type*} [CommSemiring A] (Q : Curve A) (i : ℕ) :
    ((raw Q).coeff i).natDegree≤Q.degreeOf parameter := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_raw]
  by_contra nz
  have deg := MvPolynomial.le_degreeOf_of_mem_support parameter (MvPolynomial.mem_support_iff.mpr nz)
  simp [parameter] at deg
  exact (not_lt_of_ge (show j ≤ Q.degreeOf parameter from deg)) hj
theorem view_z (Q : Curve (Polynomial L)) : (zView (view Q)).natDegree=Q.degreeOf parameter := by
  have swap_twice : (view Q).map Bivariate.swap.toRingHom=raw Q := by
    apply Polynomial.ext
    intro i
    change (((raw Q).map Bivariate.swap.toRingHom).map Bivariate.swap.toRingHom).coeff i=_
    rw [coeff_map,coeff_map]
    exact Bivariate.swap_swap_apply _
  change (Bivariate.swap ((view Q).map Bivariate.swap.toRingHom)).natDegree=_
  rw [swap_twice]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [coeff_swap,coeff_zero]
    exact coeff_eq_zero_of_natDegree_lt ((raw_seed Q i).trans_lt hj)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    let i := m ordinate
    let j := m parameter
    have same : (Finsupp.single (PUnit.unit : PUnit) j).optionElim i=m := by
      ext k
      cases k with
      | none => simp [i,ordinate]
      | some l => cases l; simp [j,parameter]
    have h := MvPolynomial.mem_support_iff.mp hm
    rw [← same, ← coeff_raw, ← coeff_swap] at h
    have term : ((Bivariate.swap (raw Q)).coeff j)≠0 := fun hzero => h (by rw [hzero,coeff_zero])
    exact Polynomial.le_natDegree_of_ne_zero term
theorem abscissa_coeff_height (Q : Curve (Polynomial L)) (d i : ℕ)
    (nz : (view Q).coeff i≠0) :
    ((view Q).coeff i).natDegree+d*i≤height d Q := by
  let n := ((view Q).coeff i).natDegree
  have nonzero : ((view Q).coeff i).coeff n≠0 := by
    change ((view Q).coeff i).leadingCoeff≠0
    exact leadingCoeff_ne_zero.mpr nz
  obtain ⟨j,hj⟩ := Polynomial.support_nonempty.mpr nonzero
  have term := Polynomial.mem_support_iff.mp hj
  change (((((raw Q).map Bivariate.swap.toRingHom).coeff i).coeff n).coeff j)≠0 at term
  rw [coeff_map] at term
  change ((Bivariate.swap ((raw Q).coeff i)).coeff n).coeff j≠0 at term
  rw [coeff_swap,coeff_raw] at term
  have cap := coeff_height d Q ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i)
    (fun zero => term (by rw [zero,Polynomial.coeff_zero]))
  rw [Finsupp.optionElim_apply_none] at cap
  exact (Nat.add_le_add_right (Polynomial.le_natDegree_of_ne_zero term) _).trans cap
theorem abscissa_le_height (Q : Curve (Polynomial L)) (d : ℕ) :
    (CurvatureSquares.xView (view Q)).natDegree≤height d Q := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i j
  change (((Bivariate.swap (view Q)).coeff n).coeff i).coeff j=0
  rw [coeff_swap]
  change ((((raw Q).map Bivariate.swap.toRingHom).coeff i).coeff n).coeff j=0
  rw [coeff_map]
  change ((Bivariate.swap ((raw Q).coeff i)).coeff n).coeff j=0
  rw [coeff_swap,coeff_raw]
  by_cases zero : Q.coeff ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i)=0
  · simp [zero]
  apply coeff_eq_zero_of_natDegree_lt
  have h := coeff_height d Q _ zero
  omega
private theorem eval_raw {F : Type*} [Field F] (z : F) (S : (Polynomial F)) (Q : Curve (Polynomial F)) :
    evaluate z S Q=((raw Q).map (evalRingHom (C z))).eval S := by
  rw [evaluate,MvPolynomial.optionEquivLeft_elim_eval]
  change ((MvPolynomial.optionEquivLeft (Polynomial F) PUnit Q).map (MvPolynomial.eval (fun _=>C z))).eval S =
    ((((MvPolynomial.optionEquivLeft (Polynomial F) PUnit Q).map
      (MvPolynomial.uniqueAlgEquiv (Polynomial F) PUnit).toRingHom).map (evalRingHom (C z)))).eval S
  rw [Polynomial.map_map]
  congr 2
  apply RingHom.ext
  intro a
  change MvPolynomial.eval (fun _ : PUnit => C z) a =
    (((MvPolynomial.uniqueAlgEquiv (Polynomial F) PUnit) a : Polynomial (Polynomial F))).eval (C z)
  exact (MvPolynomial.eval₂_const_uniqueAlgEquiv (φ:=RingHom.id (Polynomial F)) (f:=a) (a:=C z)).symm
theorem evaluate_view (z : L) (S : (Polynomial L)) (Q : Curve (Polynomial L)) :
    evaluate z S Q=(specialize (view Q) z).eval S := by
  rw [eval_raw]
  apply congrArg (fun E : Polynomial (Polynomial L) => E.eval S)
  apply Polynomial.ext
  intro i
  change ((raw Q).map (evalRingHom (C z))).coeff i =
    (((raw Q).map Bivariate.swap.toRingHom).map (mapRingHom (evalRingHom z))).coeff i
  rw [coeff_map,coeff_map,coeff_map]
  have eq := eval_swap (Bivariate.swap ((raw Q).coeff i)) z
  rw [Bivariate.swap_swap_apply] at eq
  exact eq
private theorem resultant_ne_of_cut {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    (P Q : (Polynomial R)) (ir : Irreducible P) (positive : 0<P.natDegree) (cut : ¬ P∣Q) :
    P.resultant Q≠0 := by
  let φ := algebraMap R (FractionRing R)
  have ph := ir.isPrimitive (ne_of_gt positive)
  have irr : Irreducible (P.map φ) := ph.irreducible_iff_irreducible_map_fraction_map.mp ir
  have cop : IsCoprime (P.map φ) (Q.map φ) :=
    irr.coprime_iff_not_dvd.mpr (fun dvd=> cut (ph.dvd_of_fraction_map_dvd_fraction_map dvd))
  have rn := Polynomial.resultant_ne_zero _ _ cop
  intro zero
  apply rn
  have injective := IsFractionRing.injective R (FractionRing R)
  rw [natDegree_map_eq_of_injective injective,natDegree_map_eq_of_injective injective,
    Polynomial.resultant_map_map,zero,map_zero]
theorem proper_cut_price {F : Type} [Field F] {ι : Type*} (T : Finset ι)
    (z : ι → F) (S : ι → Polynomial F) (inj : Set.InjOn z (T:Set ι))
    (f g : Curve (Polynomial F)) (ir : Irreducible f) (cut : ¬ f∣g) {e v : ℕ} (he : 0<e)
    (fy : f.degreeOf ordinate=e) (fz : f.degreeOf parameter=v)
    (gy : g.degreeOf ordinate≤4*e) (gz : g.degreeOf parameter≤10*v)
    (fmarks : ∀ i∈T,evaluate (z i) (S i) f=0)
    (gmarks : ∀ i∈T,evaluate (z i) (S i) g=0) :
    T.card≤14*e*v := by
  classical
  let P := raw f
  let Q := raw g
  have pd : P.natDegree=e := (raw_y f).trans fy
  have qd : Q.natDegree≤4*e := (raw_y g).trans_le gy
  have irr : Irreducible P := (MulEquiv.irreducible_iff (raw (A:=(Polynomial F)))).mpr ir
  have notdvd : ¬ P∣Q := by
    rintro ⟨a, h⟩
    apply cut
    refine ⟨(raw (A:=(Polynomial F))).symm a, (raw (A:=(Polynomial F))).injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact h
  let R := P.resultant Q
  have rn : R≠0 := resultant_ne_of_cut P Q irr (by rw [pd]; exact he) notdvd
  have rdeg : R.natDegree≤14*e*v := by
    have hp i := (raw_seed f i).trans_eq fz
    have hq i := (raw_seed g i).trans gz
    have bound := natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree v (10*v) hp hq
    calc
      R.natDegree ≤ Q.natDegree*v+P.natDegree*(10*v) := bound
      _ ≤ (4*e)*v+e*(10*v) := Nat.add_le_add (Nat.mul_le_mul_right _ qd) (Nat.mul_le_mul_right _ pd.le)
      _ = _ := by ring
  have sn : Bivariate.swap R≠0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr rn
  let coeff := (Bivariate.swap R).leadingCoeff
  have cn : coeff≠0 := leadingCoeff_ne_zero.mpr sn
  have cdeg : coeff.natDegree≤R.natDegree := by
    have h := CurvatureSquares.coeff_height (Bivariate.swap R) (Bivariate.swap R).natDegree
    simpa only [CurvatureSquares.height,Bivariate.swap_swap_apply,coeff_natDegree] using h
  have roots : T.image z ⊆ coeff.roots.toFinset := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots cn).mpr
    have atRoot := Polynomial.map_resultant_eq_zero_of_common_root
      (evalRingHom (C (z i))) P Q (m:=P.natDegree) (n:=Q.natDegree) le_rfl le_rfl
      (Or.inl (by omega)) (S i) ((eval_raw (z i) (S i) f).symm.trans (fmarks i hi))
      ((eval_raw (z i) (S i) g).symm.trans (gmarks i hi))
    change R.eval (C (z i))=0 at atRoot
    have swapped : (Bivariate.swap R).map (evalRingHom (z i))=0 := by
      have e := eval_swap (Bivariate.swap R) (z i)
      rw [Bivariate.swap_swap_apply,atRoot] at e
      exact e.symm
    have killed := congrArg (fun A : (Polynomial F) => A.coeff (Bivariate.swap R).natDegree) swapped
    simpa only [Polynomial.IsRoot,coeff_map,coeff_natDegree,coeff_zero,coe_evalRingHom] using killed
  rw [← card_image_of_injOn inj]
  exact (card_le_card roots).trans ((Multiset.toFinset_card_le ..).trans
    ((Polynomial.card_roots' coeff).trans (cdeg.trans rdeg)))
#print axioms view_z
#print axioms proper_cut_price
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionCut

-- merged module R6960RetainedCompressionReduction
section Merged_R6960RetainedCompressionReduction
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L liftPoly)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open CurvatureSquares (Ordinate ordEval xView zView)
open scoped Polynomial
open CurvatureSquares (degree_two_count)
abbrev wordDegree : ℕ := 164670
def FactorPriceAt (rate:ℕ→ℕ) : Prop :=
  ∀ (degD : ℕ), 0<degD → degD<179808 →
    ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
      Word 179808 degD M.word F.scalar T →
      ∀ f : Curve (Polynomial L), Irreducible f →
        3≤f.degreeOf ordinate → TameBand (f.degreeOf ordinate) degD → 0<f.degreeOf parameter →
        height degD f≤heightCap (f.degreeOf ordinate) degD →
        (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
        T.card≤rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
          (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
abbrev BoundedFactorPrice := FactorPriceAt MarkedSheet.rate
theorem rate_mono {e n : ℕ} (h : e≤n) : MarkedSheet.rate e≤MarkedSheet.rate n := by
  unfold MarkedSheet.rate
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 9 h) 6)
      (Nat.sub_le_sub_right h 1))
    (Nat.mul_le_mul_left 2 h)) 1
theorem vote_scale : CurvatureVotes.VoteScale 179808 wordDegree 18 :=
  Or.inl (by decide +kernel)
private theorem word_roots {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ)
    (Q : Ordinate) (H : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    ∀ γ∈U, ordEval (scalar M γ) ((F.scalar γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (scalar M γ))) (liftPoly (F.scalar γ))=0
  rw [← eval_map]
  exact (H γ hγ).root
theorem factor_price (rate:ℕ→ℕ) (mono:Monotone rate) (small:28≤rate 3)
    (proper:∀e,3≤e→e<64→14*e≤rate e) (bounded : FactorPriceAt rate)
    (degD : ℕ) (hd0 : 0<degD) (hdA : degD<179808) (hvote : CurvatureVotes.VoteScale 179808 degD 18)
    {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ) (sub : U⊆Γ)
    (words : Word 179808 degD M.word F.scalar U)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : TameBand n degD)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    U.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases U.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 28≤rate n := small.trans (mono lo)
  have vRate : 18≤rate n := (by decide : 18≤28).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn (scalar M) (U : Set K) := (scalar_injective M).injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (F.scalar x)) (U:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q U (scalar M) (fun x=>liftPoly (F.scalar x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots F Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) (scalar M) inj
      hdA hvote Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e degD < height degD q
  · let parameter (j : U) := scalar M j.val
    let root (j : U) := liftPoly (F.scalar j.val)
    have d (j : U) : (root j).natDegree≤degD := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : U) : evaluate (parameter j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape parameter root degD hd0 d q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price U (scalar M) (fun w=>liftPoly (F.scalar w))
      inj q G qp nondiv pos y z gy gz (fun γ hγ=>rootsF ⟨γ,hγ⟩)
      (fun γ hγ=>rootsG ⟨γ,hγ⟩)
    have ceiling : 14*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using tRate
      have three : 3≤e := by omega
      exact (proper e three (degree.trans_lt hi.lt_64)).trans (mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q degD
        rw [RingEquiv.apply_symm_apply] at a
        have hcap2 : heightCap 2 degD = 3*degD := by unfold heightCap; omega
        have hle := a.trans (two ▸ wt)
        rw [hcap2] at hle
        change 2*(xView Q).natDegree < 2130706433
        omega
      have count := degree_two_count words (algebraMap K L) (scalar M) inj
        hdA hvote Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have charge := bounded degD hd0 hdA F U sub words q qp three
      (y.symm ▸ hi.mono_left degree)
      (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt)
      (fun γ hγ => by simpa only [q,RingEquiv.apply_symm_apply] using mark γ hγ)
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))
theorem retained_of_tariff (rate:ℕ→ℕ) (mono:Monotone rate) (small:28≤rate 3)
    (proper:∀e,3≤e→e<64→14*e≤rate e)
    (paid:∀e a b,3≤e→e<48→a+b≤2400→b<(TerminalReceipts.witness e).order 1→
      rate e*(a+p*b)+(e-1)*e≤retainedCap) (bounded : FactorPriceAt rate) : RetainedCount := by
  intro u deleted M Γ F lo hi D Crt regular residues T f sub emin emax axes graded marks
  obtain ⟨W,P,pn,deg,seed,fibre⟩ :=
    marked_projection F f sub emin axes hi (fun γ hγ => (marks γ hγ).1)
  have pmin : 3≤P.natDegree := deg.symm ▸ emin
  have pmax : P.natDegree<48 := deg.symm ▸ emax
  have count := aggregate P T (scalar M) (fun γ=>liftPoly (F.scalar γ))
    (rate P.natDegree) (P.natDegree-1) pn fibre (by
      intro Q ir dvd U us qmark
      have words : Word 179808 wordDegree M.word F.scalar U :=
        ⟨W.distinct.mono us,fun γ hγ=>W.degree γ (us hγ),fun γ hγ=>W.hits γ (us hγ)⟩
      exact factor_price rate mono small proper bounded wordDegree (by decide) (by decide) vote_scale
        F (us.trans sub) words ir _ pmin (Or.inl ⟨pmax, le_rfl⟩)
        (natDegree_le_of_dvd dvd pn) qmark)
  rw [deg] at count
  have priced := Nat.add_le_add_right (Nat.mul_le_mul_left (rate f.natDegree) seed)
    ((f.natDegree-1)*f.natDegree)
  exact count.trans (priced.trans (paid f.natDegree _ _ emin emax axes (graded 1)))
theorem retained_of_bounded (bounded : BoundedFactorPrice) : RetainedCount :=
  retained_of_tariff MarkedSheet.rate (fun _ _ h=>rate_mono h) (by decide)
    (by
      intro e he hi
      have h64 : ∀ i : Fin 64, 3 ≤ i.val → 14*i.val ≤ MarkedSheet.rate i.val := by decide +kernel
      exact h64 ⟨e, hi⟩ he) graded_budget bounded
#print axioms factor_price
#print axioms retained_of_bounded
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionReduction

-- merged module R6960RetainedCompressionPureNodes
section Merged_R6960RetainedCompressionPureNodes
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate zView coeff_caps)
open RetainedShortening (Word)
open RescueGeometry (Model Family)
open scoped Polynomial
open Lower6960.RetainedCompression (rate_mono)
open CurvatureSquares (node_eval node_height node_ne root_count)
private abbrev embed := algebraMap K L
def atNode (P : Ordinate) (i : I) : Polynomial (Polynomial L) :=
  P.map (evalRingHom (C (embed (node i))))
def PureNodes (w : I → K) (P : Ordinate) : Prop :=
  ∀ i, (atNode P i).eval (C (embed (w i))) = 0 →
    atNode P i = C (atNode P i).leadingCoeff * (Polynomial.X-C (C (embed (w i))))^P.natDegree
private theorem node_coefficient (P : Ordinate) (i : I) (j : ℕ) :
    ((atNode P i).coeff j).natDegree≤(zView P).natDegree := by
  rw [atNode,coeff_map,coe_evalRingHom]
  exact (CurvatureSquares.node_height ..).trans (coeff_caps P j).2
private theorem root_at_node {P : Ordinate} {z : L} {S : (Polynomial K)}
    (mark : MarkedFiber P z (liftPoly S)) (i : I) :
    ((atNode P i).map (evalRingHom z)).eval (embed (S.eval (node i)))=0 := by
  let x := embed (node i)
  have commute : (specialize P z).map (evalRingHom x)=(atNode P i).map (evalRingHom z) := by
    apply Polynomial.ext
    intro n
    simp only [specialize,atNode,x,coeff_map,coe_mapRingHom,coe_evalRingHom]
    exact (CurvatureSquares.node_eval (P.coeff n) (embed (node i)) z).symm
  have value : (liftPoly S).eval x=embed (S.eval (node i)) := by
    rw [liftPoly,show x=embed (node i) from rfl,Polynomial.eval_map_apply]
  have h := congrArg (Polynomial.eval x) mark.root
  have eq := Polynomial.eval_map_apply (f:=evalRingHom x)
    (p:=specialize P z) (x:=liftPoly S)
  rw [commute,coe_evalRingHom,value] at eq
  exact eq.trans (h.trans eval_zero)
theorem pure_node_price {d : ℕ} {w s T} (W : Word 179808 d w s T)
    (hd : d < 179808) (hvote : CurvatureVotes.VoteScale 179808 d 18)
    (z : K → L) (inj : Set.InjOn z (T:Set K)) (P : Ordinate) (irr : Irreducible P)
    (pos : 0<P.natDegree) (pure : PureNodes w P)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (liftPoly (s γ))) :
    T.card≤18*(zView P).natDegree+1 := by
  classical
  apply CurvatureVotes.minority_count W hd hvote
  intro i
  let Q := atNode P i
  let a := Q.leadingCoeff
  let g := Q.eval (C (embed (w i)))
  have cn (j : ℕ) : (Q.coeff j).natDegree≤(zView P).natDegree := node_coefficient P i j
  have fits : g.natDegree≤(zView P).natDegree := by
    dsimp only [g]
    rw [eval_eq_sum,Polynomial.sum_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (cn j)
  by_cases nonzero : g≠0
  · left
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) g nonzero _).trans fits
    intro γ hγ
    obtain ⟨active,hit⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have eq := Polynomial.eval_map_apply (f:=evalRingHom (z γ))
      (p:=Q) (x:=C (embed (w i)))
    rw [coe_evalRingHom,eval_C] at eq
    rw [hit] at hz
    exact eq.symm.trans hz
  · right
    have qn : Q≠0 := CurvatureSquares.node_ne P irr pos _
    have an : a≠0 := leadingCoeff_ne_zero.mpr qn
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) a an _).trans
      (by simpa only [a,coeff_natDegree] using cn Q.natDegree)
    intro γ hγ
    obtain ⟨active,miss⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have packed := pure i (not_ne_iff.mp nonzero)
    change Q=C a*(Polynomial.X-C (C (embed (w i))))^P.natDegree at packed
    change (Q.map (evalRingHom (z γ))).eval (embed ((s γ).eval (node i)))=0 at hz
    rw [packed,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
      eval_C,coe_evalRingHom,eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (embed.injective.ne miss)))
def NonPureFactorPrice : Prop :=
  ∀ (degD : ℕ), 0<degD → degD<179808 →
    ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
      Word 179808 degD M.word F.scalar T →
      ∀ f : Curve (Polynomial L), Irreducible f →
        3≤f.degreeOf ordinate → TameBand (f.degreeOf ordinate) degD → 0<f.degreeOf parameter →
        height degD f≤heightCap (f.degreeOf ordinate) degD →
        ¬PureNodes M.word (view f) →
        (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
        T.card≤MarkedSheet.rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
          (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
theorem bounded_of_nonpure (other : NonPureFactorPrice) : BoundedFactorPrice := by
  intro degD hd0 hdA u deleted M Γ F T sub W f irr lo hi sv cap marks
  by_cases pure : PureNodes M.word (view f)
  · let P := view f
    have ir : Irreducible P := (MulEquiv.irreducible_iff view).mpr irr
    have positive : 0<P.natDegree := by change 0<(view f).natDegree; rw [view_y]; omega
    have hvote : CurvatureVotes.VoteScale 179808 degD 18 := by
      apply Or.inl
      have hle : degD ≤ 164670 := by rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      omega
    have fee := pure_node_price W hdA hvote (scalar M) (scalar_injective M).injOn P ir positive pure marks
    change _≤18*(zView (view f)).natDegree+1 at fee
    rw [view_z] at fee
    have rate : 18≤MarkedSheet.rate (f.degreeOf ordinate) := (by decide :
      18≤MarkedSheet.rate 3).trans (rate_mono lo)
    have additive : 1≤(f.degreeOf ordinate-1)*(f.degreeOf ordinate) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    exact fee.trans (Nat.add_le_add (Nat.mul_le_mul_right _ rate) additive)
  · exact other degD hd0 hdA F T sub W f irr lo hi sv cap pure marks
theorem retained_of_nonpure (other : NonPureFactorPrice) : RetainedCount :=
  retained_of_bounded (bounded_of_nonpure other)
#print axioms pure_node_price
#print axioms retained_of_nonpure
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionPureNodes
