import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes

set_option Elab.async false

-- Source: Research6969.NearCompression
set_option autoImplicit true
-- Adapted from the promoted 69.62 lower proof at 2a99570fe043b6dabeac1e52f807826c8859d717.

section
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Lower6960.Near6969Compression
open _root_.Lower6960.RetainedCompression
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
def TameBand (e d : ℕ) : Prop := (e < 48 ∧ d ≤ 164670) ∨ (e < 64 ∧ d ≤ 133605)
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
      2 * ((2*i.val - 1) * heightCap i.val 133605 - 133605 * i.val^2) + 2 * (i.val - 1) < K1.p := by
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
  have h64 : ∀ i : Fin 64, 2 * ((i.val - 1) * heightCap i.val 133605) < K1.p := by decide +kernel
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
end
end Lower6960.Near6969Compression

end

section
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
namespace Lower6960.Near6969Compression
open _root_.Lower6960.RetainedCompression
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
end
end Lower6960.Near6969Compression

end

section
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000
namespace Lower6960.Near6969Compression
open _root_.Lower6960.RetainedCompression
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
end
end Lower6960.Near6969Compression

end

