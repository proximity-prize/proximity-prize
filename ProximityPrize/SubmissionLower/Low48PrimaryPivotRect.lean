import ProximityPrize.SubmissionLower.AnchorNinth82190
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.PrimaryTaperBudget
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false

-- merged module Low48PrimaryPivotRows
section Merged_Low48PrimaryPivotRows

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open AnchorPivot82180 (independent)
open K1_13_2_2 (active_range_le)

def key (e : E) : ℕ :=
  8177403*e.a + 5451602*e.b + 2725802*e.c + 1651*e.f

noncomputable def encode : Form →ₐ[Geom] Polynomial Geom :=
  aeval (fun i => (Polynomial.X : Polynomial Geom)^(![8177403,5451602,2725802,1651] i : ℕ))

private theorem encode_mon (e : E) : encode (mon e) = Polynomial.X ^ key e := by
  simp [mon, encode, key, ← pow_mul, ← pow_add]

private theorem degree_le (xs : List Term) (v : ℕ)
    (h : xs.all (fun t => decide (key t.2 ≤ v)) = true) :
    (encode (poly xs)).degree ≤ (v : ℕ) := by
  induction xs with
  | nil => simp [poly]
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    rw [poly, map_add, map_zsmul, encode_mon]
    apply Polynomial.degree_add_le_of_degree_le _ (ih hr)
    rw [← Int.cast_smul_eq_zsmul (R := Geom)]
    exact (Polynomial.degree_smul_le _ _).trans ((Polynomial.degree_X_pow_le _).trans
      (WithBot.coe_le_coe.mpr (of_decide_eq_true hp)))

private theorem leading {e : E} {v : ℕ} (xs : List Term) (h : v < key e)
    (ht : xs.all (fun t => decide (key t.2 ≤ v)) = true) :
    (encode (poly ((1,e)::xs))).degree = (key e : ℕ) := by
  rw [poly, one_zsmul, map_add, encode_mon, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (degree_le xs _ ht).trans_lt (WithBot.coe_lt_coe.mpr h)

private theorem leading0 : (encode (poly src0)).degree = (key ⟨1,0,0,0⟩ : ℕ) := by
  unfold src0
  exact leading _ (v := key ⟨0,1,0,0⟩) (by decide) (by decide)
private theorem leading3 : (encode (poly src3)).degree = (key ⟨1,1,0,0⟩ : ℕ) := by
  unfold src3
  exact leading _ (v := key ⟨1,0,1,0⟩) (by decide) (by decide)
private theorem leading6 : (encode (poly src6)).degree = (key ⟨2,0,1,0⟩ : ℕ) := by
  unfold src6
  exact leading _ (v := key ⟨1,2,0,0⟩) (by decide) (by decide)
private theorem leading7 : (encode (poly src7)).degree = (key ⟨1,3,0,0⟩ : ℕ) := by
  unfold src7
  exact leading _ (v := key ⟨2,1,0,1⟩) (by decide) (by decide)
structure Triple where
  b : ℕ
  c : ℕ
  f : ℕ
  deriving DecidableEq

def Triple.index (p : Triple) := p.b+2*p.c+3*p.f
def Triple.exponent (p : Triple) : E := ⟨1650-p.b-p.c-p.f,p.b,p.c,p.f⟩
def Triple.room (p : Triple) := 1650-p.index
structure Groups where
  fourth : ℕ
  first : ℕ
  second : ℕ

def Groups.width (g : Groups) : ℕ := g.fourth+g.first+g.second
def Groups.gain (g : Groups) : ℕ := 2*g.fourth+g.first+g.second

def Triple.packet (p : Triple) : Groups :=
  let q := min (p.b/3) (min p.room ((p.b+p.c-p.room)/2))
  let singles := min (p.room-q) (p.b+p.c-3*q)
  let first := min (p.b-3*q) singles
  ⟨q,first,singles-first⟩

def Triple.contact (p : Triple) : ℕ := p.c+2*p.f+p.room+p.packet.gain

private theorem packet_valid (p : Triple) :
    p.packet.width ≤ p.room ∧ 3*p.packet.fourth+p.packet.first ≤ p.b ∧
      p.packet.second ≤ p.c := by
  simp only [Triple.packet, Groups.width]
  omega

theorem contact_eq (p : Triple) :
    p.contact = p.c+2*p.f+p.room+
      min (p.b+p.c) (p.room + min (p.b/3) (min p.room ((p.b+p.c-p.room)/2))) := by
  simp only [Triple.contact, Triple.packet, Groups.gain]
  omega

private def linear (p : Triple) := p.room-p.packet.width
private def remainder (p : Triple) : E :=
  let g := p.packet
  ⟨p.exponent.a-(linear p+g.fourth+g.first+2*g.second),
    p.b-(3*g.fourth+g.first),p.c-g.second,p.f⟩

noncomputable def polynomial (p : Triple) : Form :=
  mon (remainder p) * poly src0 ^ linear p *
    poly src3 ^ p.packet.first * poly src6 ^ p.packet.second *
    poly src7 ^ p.packet.fourth

private theorem bot_nsmul (n k : ℕ) :
    k • (n : WithBot ℕ) = ((k*n : ℕ) : WithBot ℕ) := by
  have hn : k • n = k*n := rfl
  exact (WithBot.coe_nsmul n k).symm.trans (congrArg WithBot.some hn)

private theorem bot_add (n k : ℕ) :
    (n : WithBot ℕ) + (k : WithBot ℕ) = ((n+k : ℕ) : WithBot ℕ) := rfl

private theorem row_bounds (p : Triple) (h : p.index ≤ 1650) :
    polynomial p ∈ bandSpace 1650 (p.index : ℤ) 1650 550 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact := by
  obtain ⟨hu,hb,hc⟩ := packet_valid p
  have hs := ((((sound_monomial (remainder p)).mul (spec0.pow (linear p))).mul
    (spec3.pow p.packet.first)).mul (spec6.pow p.packet.second)).mul
    (spec7.pow p.packet.fourth)
  have hp : linear p + p.packet.width = p.room := by unfold linear; omega
  have hTotal : p.exponent.a + p.b + p.c + p.f = 1650 := by
    simp only [Triple.exponent, Triple.index] at *
    omega
  have ha : linear p+p.packet.fourth+p.packet.first+
      2*p.packet.second ≤ p.exponent.a := by
    simp only [Groups.width, Triple.exponent, Triple.room, Triple.index] at *
    omega
  have helpDegree : (remainder p).deg + linear p + p.packet.first*2 + p.packet.second*3 +
      p.packet.fourth*4 = 1650 := by
    simp only [remainder, E.deg]
    omega
  have helpIndex : (remainder p).index + p.packet.first + 2*p.packet.second +
      3*p.packet.fourth = p.index := by
    simp only [remainder, E.index, Triple.index]
    omega
  have helpTop : p.f + p.packet.second+p.packet.fourth ≤ 550 := by
    simp only [Groups.width, Triple.room, Triple.index] at *
    omega
  have helpUpper : (remainder p).index + linear p + 2*p.packet.first +3*p.packet.second +
      4*p.packet.fourth = 1650 := by
    simp only [Groups.width, Triple.room] at hp
    omega
  have helpOrder : (remainder p).c+2*(remainder p).f + linear p +
      p.packet.first*2+p.packet.second*3+p.packet.fourth*3 = p.contact := by
    simp only [remainder, Triple.contact, Groups.gain]
    unfold Groups.width at hp
    omega
  have hd := hs.band
  simp only [AnchorPivot82180.Data.plus, AnchorPivot82180.Data.times,
    AnchorPivot82180.monoData, AnchorPivot82180.data0, AnchorPivot82180.data3,
    AnchorPivot82180.data6, AnchorPivot82180.data7] at hd
  have he (f : Fin 4 →₀ ℕ) (hf : f ∈ (polynomial p).support) :=
    (mem_restrictSupport_iff Geom).mp hd hf
  refine ⟨(mem_restrictSupport_iff Geom).mpr ?_, ?_⟩
  · intro e helem
    obtain ⟨h0,h1,h2,h3⟩ := he e helem
    refine ⟨?_,?_,?_,?_⟩
    · simpa [Nat.mul_comm] using (h0.trans (by omega))
    · omega
    · have := helpUpper
      omega
    · exact h3.trans (by simpa [remainder,Nat.mul_comm] using helpTop)
  · have hContact := hs.contact
    simp only [AnchorPivot82180.Data.plus, AnchorPivot82180.Data.times,
      AnchorPivot82180.monoData, AnchorPivot82180.data0, AnchorPivot82180.data3,
      AnchorPivot82180.data6, AnchorPivot82180.data7] at hContact
    exact restrictWeightedOrder_anti _ (by omega) hContact
private theorem degree_products (A B C D E : Polynomial Geom) (k l m n a b c d e : ℕ)
    (hA : A.degree = (a : WithBot ℕ)) (hB : B.degree = (b : WithBot ℕ))
    (hC : C.degree = (c : WithBot ℕ)) (hD : D.degree = (d : WithBot ℕ))
    (hE : E.degree = (e : WithBot ℕ)) :
    (A*B^k*C^l*D^m*E^n).degree = ((a+k*b+l*c+m*d+n*e : ℕ) : WithBot ℕ) := by
  simp only [Polynomial.degree_mul, Polynomial.degree_pow, hA, hB, hC, hD, hE,
    bot_nsmul, bot_add]

private theorem row_key (p : Triple) (h : p.index ≤ 1650) :
    key (remainder p) + linear p * key ⟨1,0,0,0⟩ +
      p.packet.first * key ⟨1,1,0,0⟩ + p.packet.second * key ⟨2,0,1,0⟩ +
      p.packet.fourth * key ⟨1,3,0,0⟩ = key p.exponent := by
  obtain ⟨hu,hb,hc⟩ := packet_valid p
  have hp : linear p + p.packet.width = p.room := by unfold linear; omega
  have ha : linear p+p.packet.fourth+p.packet.first+2*p.packet.second ≤ p.exponent.a := by
    simp only [Groups.width, Triple.exponent, Triple.room, Triple.index] at *
    omega
  have hA : (remainder p).a + (linear p+p.packet.fourth+p.packet.first+2*p.packet.second) =
      p.exponent.a := Nat.sub_add_cancel ha
  have hB : (remainder p).b + (3*p.packet.fourth+p.packet.first) =
      p.exponent.b := Nat.sub_add_cancel hb
  have hC : (remainder p).c + p.packet.second = p.exponent.c := Nat.sub_add_cancel hc
  have hF : p.exponent.f = (remainder p).f := rfl
  unfold key
  rw [← hA, ← hB, ← hC, hF]
  ring

private theorem deg_remainder (p : Triple) :
    (encode (mon (remainder p))).degree = (key (remainder p) : WithBot ℕ) := by
  rw [encode_mon, Polynomial.degree_X_pow]

private theorem row_degree (p : Triple) (h : p.index ≤ 1650) :
    (encode (polynomial p)).degree = (key p.exponent : ℕ) := by
  rw [polynomial, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  exact (degree_products _ _ _ _ _ (linear p) p.packet.first p.packet.second p.packet.fourth
    _ _ _ _ _ (deg_remainder p) leading0 leading3 leading6 leading7).trans
      (congrArg (fun n : ℕ => (n : WithBot ℕ)) (row_key p h))

theorem row_sound (p : Triple) (h : p.index ≤ 1650) :
    polynomial p ∈ bandSpace 1650 (p.index : ℤ) 1650 550 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact ∧
      (encode (polynomial p)).degree = (key p.exponent : ℕ) :=
  ⟨(row_bounds p h).1, (row_bounds p h).2, row_degree p h⟩

theorem key_injective (p q : Triple) (hp : p.index ≤ 1650) (hq : q.index ≤ 1650)
    (h : key p.exponent = key q.exponent) : p = q := by
  have hform (r : Triple) (hr : r.index ≤ 1650) :
      key r.exponent = 2725801*(4950-r.index) + 1651*r.f + r.c := by
    simp only [key, Triple.exponent, Triple.index] at *
    omega
  rw [hform p hp,hform q hq] at h
  have hi : p.index=q.index := by unfold Triple.index at *; omega
  rw [hi] at h
  have hcf : p.c=q.c ∧ p.f=q.f := by unfold Triple.index at *; omega
  rcases p with ⟨pb,pc,pf⟩
  rcases q with ⟨qb,qc,qf⟩
  simp only [Triple.index] at hi
  simp only at hcf
  obtain ⟨rfl,rfl⟩ := hcf
  congr
  omega


end Low48PrimaryPivot

end Merged_Low48PrimaryPivotRows

-- merged module Low48PrimaryPivotCore
section Merged_Low48PrimaryPivotCore

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open AnchorPivot82180 (independent)
open K1_13_2_2 (active_range_le)

private def ofExp (e : JetExp) : Triple := ⟨e 1,e 2,e 3⟩

private theorem old_jet_index (e : JetExp) :
    e.weight oldWeight = (ofExp e).index := by
  simp [oldWeight, ofExp, Triple.index, Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, mul_comm]

private theorem old_jet_degree (e : JetExp) :
    e.weight gradeWeight = e 0 + e 1 + e 2 + e 3 := by
  simp [gradeWeight, Finsupp.weight_eq_sum, Fin.sum_univ_four]

private theorem source_data {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    {e : JetExp} (he : e ∈ oldColumns (initialFlag i)) :
    (ofExp e).index ≤ 1650 ∧ -(offset i) ≤ ((ofExp e).index : ℤ) ∧
      e 0 + e 1 + e 2 + e 3 = 1650 := by
  obtain ⟨hgrade,hlo,hhi,_⟩ := mem_oldColumns.mp he
  rw [old_jet_index] at hlo hhi
  rw [old_jet_degree] at hgrade
  have hg : (initialFlag i).degree = 1650 := by
    change min (i.1.val : ℤ) 1650 = 1650
    omega
  change ((ofExp e).index : ℤ) ≤ 1650 at hhi
  rw [hg] at hgrade
  push_cast at hgrade
  exact ⟨by omega,hlo,by omega⟩

private theorem triple_injOn {i : BlockIndex} (hs : 1650 ≤ i.1.val) :
    Set.InjOn ofExp (↑(oldColumns (initialFlag i)) : Set JetExp) := by
  intro e he f hf h
  have h1 := congrArg Triple.b h
  have h2 := congrArg Triple.c h
  have h3 := congrArg Triple.f h
  simp only [ofExp] at h1 h2 h3
  have hd : e 0 + e 1 + e 2 + e 3 = 1650 := (source_data hs he).2.2
  have hdf : f 0 + f 1 + f 2 + f 3 = 1650 := (source_data hs hf).2.2
  ext j
  fin_cases j
  · change e 0 = f 0
    omega
  · exact h1
  · exact h2
  · exact h3

private def good (i : BlockIndex) (e : JetExp) : Prop :=
  (initialFlag i).order.toNat ≤ (ofExp e).contact

private instance (i : BlockIndex) (e : JetExp) : Decidable (good i e) := by
  unfold good
  infer_instance

private theorem good_kernel {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    (e : ↑((oldColumns (initialFlag i)).filter (good i))) :
    ∃ w : LinearMap.ker (flagContact (initialFlag i)),
      (encode (w.val : Form)).degree = (key (ofExp e).exponent : ℕ) := by
  obtain ⟨he,hg⟩ := Finset.mem_filter.mp e.property
  let p := ofExp e
  obtain ⟨hi,hl,_⟩ := source_data hs he
  obtain ⟨hBand,hContact,hKey⟩ := row_sound p hi
  have hOld : polynomial p ∈ oldSpace (initialFlag i) := by
    intro e he
    have h := (mem_restrictSupport_iff Geom).mp hBand he
    change K1_13_1_1.BandExponent 1650 p.index 1650 550 e at h
    obtain ⟨hd,hlow,hupp,ht⟩ := h
    refine ⟨?_,hl.trans hlow,hupp,?_⟩
    · have hweight : gradeWeight = (fun _ : Fin 4 => (1 : ℕ)) := rfl
      have hg : (initialFlag i).degree = 1650 := by
        change min (i.1.val : ℤ) 1650 = 1650
        omega
      rw [hweight, ← Finsupp.degree_eq_weight_one, hg]
      exact_mod_cast hd
    · change (e 3 : ℤ) ≤ 550
      exact_mod_cast ht
  let q : oldSpace (initialFlag i) := ⟨polynomial p,hOld⟩
  have hz : q ∈ LinearMap.ker (flagContact (initialFlag i)) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ hg hContact
  exact ⟨⟨q,hz⟩,hKey⟩

private theorem rank_le_bad (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤
      ((oldColumns (initialFlag i)).filter (fun e => ¬ good i e)).card := by
  classical
  let S := (oldColumns (initialFlag i)).filter (good i)
  let w : S → LinearMap.ker (flagContact (initialFlag i)) :=
    fun e => Classical.choose (good_kernel hs e)
  let L : LinearMap.ker (flagContact (initialFlag i)) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((oldSpace (initialFlag i)).subtype.comp (LinearMap.ker _).subtype)
  have keyInj : Function.Injective (fun e : S => key (ofExp e).exponent) := by
    intro p q hkey
    have hp := (Finset.mem_filter.mp p.property).1
    have hq := (Finset.mem_filter.mp q.property).1
    exact Subtype.ext (triple_injOn hs hp hq
      (key_injective _ _ (source_data hs hp).1 (source_data hs hq).1 hkey))
  have hind := independent L w (fun e => key (ofExp e).exponent) keyInj
    (fun e => Classical.choose_spec (good_kernel hs e))
  have hdim := hind.fintype_card_le_finrank
  rw [Fintype.card_coe] at hdim
  have hnull := (flagContact (initialFlag i)).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hnull
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := oldColumns (initialFlag i)) (good i)
  have hbound := (K1_13_2_2_1.proof i).trans (Submodule.finrank_mono (active_range_le i))
  change S.card ≤ _ at hdim
  change S.card + _ = _ at hpartition
  omega

abbrev Column := Fin 551 × Fin 826 × Fin 1651

def columnPoint (q : Column) : Triple := ⟨q.2.2.val,q.2.1.val,q.1.val⟩

private def slot (p : Triple) (h : p.index ≤ 1650) : Column :=
  ⟨⟨p.f,by unfold Triple.index at h; omega⟩,
    ⟨p.c,by unfold Triple.index at h; omega⟩,
    ⟨p.b,by unfold Triple.index at h; omega⟩⟩

private theorem slot_inv (p : Triple) (h : p.index ≤ 1650) : columnPoint (slot p h) = p := by
  cases p
  rfl

def pays (i : BlockIndex) (q : Column) : Prop :=
  let p := columnPoint q
  p.index ≤ 1650 ∧ -offset i ≤ (p.index : ℤ) ∧ p.contact < (initialFlag i).order.toNat

instance (i : BlockIndex) (q : Column) : Decidable (pays i q) := by
  unfold pays
  infer_instance

def charge (i : BlockIndex) (q : Column) : ℕ := if pays i q then 1 else 0

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 26000 in
theorem block_le_charge (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ ∑ q, charge i q := by
  classical
  let f : JetExp → Column := fun e =>
    if hp : (ofExp e).index ≤ 1650 then slot (ofExp e) hp else default
  let S : Finset JetExp := (oldColumns (initialFlag i)).filter (fun e => ¬ good i e)
  let T : Finset (Column) := Finset.univ.filter (pays i)
  have hT : (∑ q, charge i q) = T.card := by
    unfold charge T
    rw [Finset.sum_boole]
    rfl
  rw [hT]
  refine (rank_le_bad i hs).trans (Finset.card_le_card_of_injOn (s := S) (t := T) f ?_ ?_)
  · intro e he
    have helem : e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) := he
    obtain ⟨hm,hbad⟩ := Finset.mem_filter.mp helem
    obtain ⟨hi,hl,_⟩ := source_data hs hm
    unfold f
    rw [dite_eq_left hi]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    unfold pays
    rw [slot_inv]
    exact ⟨hi,hl,lt_of_not_ge hbad⟩
  · intro e he q hq h
    have hem := (Finset.mem_filter.mp
      (show e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from he)).1
    have hqm := (Finset.mem_filter.mp
      (show q ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from hq)).1
    have hei := (source_data hs hem).1
    have hqi := (source_data hs hqm).1
    simp only [f, dite_eq_left hei, dite_eq_left hqi] at h
    have heq := congrArg columnPoint h
    rw [slot_inv,slot_inv] at heq
    exact triple_injOn hs hem hqm heq


end Low48PrimaryPivot

end Merged_Low48PrimaryPivotCore

-- merged module Low48PrimaryPivotRect
section Merged_Low48PrimaryPivotRect

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

/-- Twice the triangular number of the positive part of an integer. -/
def twiceTri (x : ℤ) : ℤ := max 0 x * (max 0 x + 1)

private theorem tri_step (x : ℤ) : twiceTri (x+1) - twiceTri x = 2 * max 0 (x+1) := by
  by_cases hx : 0 ≤ x
  · simp only [twiceTri, max_eq_right hx, max_eq_right (show 0 ≤ x+1 by omega)]
    ring
  · have h1 : x+1 ≤ 0 := by omega
    simp [twiceTri, max_eq_left h1, max_eq_left (le_of_not_ge hx)]

private theorem sum_ramp (a b k : ℤ) (h : a ≤ b) :
    (∑ l ∈ Ico a b, 2 * max 0 (l-k+1)) = twiceTri (b-k) - twiceTri (a-k) := by
  rw [Int.Ico_eq_finset_map, sum_map]
  let n := (b-a).toNat
  have hn : a+(n : ℤ) = b := by dsimp [n]; omega
  have eq (l : ℕ) :
      2 * max 0 (a+(l : ℤ)-k+1) =
        twiceTri (a+((l+1 : ℕ) : ℤ)-k) - twiceTri (a+(l : ℤ)-k) := by
    push_cast
    rw [show a+((l : ℤ)+1)-k = a+(l : ℤ)-k+1 by ring, tri_step]
  change (∑ l ∈ range n, 2 * max 0 (a+(l : ℤ)-k+1)) = _
  simp_rw [eq]
  rw [sum_range_sub (fun l : ℕ => twiceTri (a+(l : ℤ)-k)) n, hn]
  simp

private theorem cut_card (q0 q1 l k : ℤ) (hq : q0 ≤ q1) :
    (((Ico q0 q1).filter (fun q => k ≤ l-q)).card : ℤ) =
      max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
  have eq : (Ico q0 q1).filter (fun q => k ≤ l-q) = Ico q0 (min q1 (l-k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, lt_min_iff]
    omega
  rw [eq, Int.card_Ico]
  omega

def cutFee (l0 l1 q0 q1 k : ℤ) : ℤ :=
  twiceTri (l1-k-q0) - twiceTri (l0-k-q0) -
    (twiceTri (l1-k-q1) - twiceTri (l0-k-q1))

private theorem sum_cut (l0 l1 q0 q1 k : ℤ) (hl : l0 ≤ l1) (hq : q0 ≤ q1) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter (fun x => k ≤ x.1-x.2)).card =
      cutFee l0 l1 q0 q1 k := by
  rw [natCast_card_filter (fun x : ℤ × ℤ => k ≤ x.1-x.2)]
  have hprod :
      (∑ x ∈ (Ico l0 l1).product (Ico q0 q1), if k ≤ x.1-x.2 then (1 : ℤ) else 0) =
        ∑ l ∈ Ico l0 l1, ∑ q ∈ Ico q0 q1, if k ≤ l-q then (1 : ℤ) else 0 :=
    sum_product (Ico l0 l1) (Ico q0 q1) (fun x : ℤ × ℤ => if k ≤ x.1-x.2 then (1 : ℤ) else 0)
  rw [hprod]
  unfold cutFee
  have eq (l : ℤ) :
      (∑ q ∈ Ico q0 q1, (if k ≤ l-q then (1 : ℤ) else 0)) =
        max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
    rw [← cut_card q0 q1 l k hq, natCast_card_filter]
  simp_rw [eq, mul_sum, mul_sub]
  rw [sum_sub_distrib]
  have ramp (q : ℤ) : (∑ l ∈ Ico l0 l1, 2 * max 0 (l-k+1-q)) =
      twiceTri (l1-k-q) - twiceTri (l0-k-q) := by
    have h (l : ℤ) : l-k+1-q = l-(k+q)+1 := by ring
    simp_rw [h]
    simpa only [sub_add_eq_sub_sub] using sum_ramp l0 l1 (k+q) hl
  rw [ramp, ramp]

def fee2 (l0 l1 q0 q1 a b : ℤ) : ℤ :=
  cutFee l0 l1 q0 q1 a - cutFee l0 l1 q0 q1 b

theorem band_card (l0 l1 q0 q1 a b : ℤ)
    (hl : l0 ≤ l1) (hq : q0 ≤ q1) (hab : a ≤ b) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter
      (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)).card = fee2 l0 l1 q0 q1 a b := by
  let S := (Ico l0 l1).product (Ico q0 q1)
  let A := S.filter (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)
  let B := S.filter (fun x => b ≤ x.1-x.2)
  have disjoint : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have ha := (mem_filter.mp hx).2.2
    have hb := (mem_filter.mp hy).2
    omega
  have union : A ∪ B = S.filter (fun x => a ≤ x.1-x.2) := by
    ext x
    by_cases h : x ∈ S
    · simp only [A, B, mem_union, mem_filter, h, true_and]
      omega
    · simp [A, B, h]
  have hcard : (A.card : ℤ) + B.card = ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) := by
    exact_mod_cast ((card_union_of_disjoint disjoint).symm.trans (congrArg card union))
  have hA := sum_cut l0 l1 q0 q1 a hl hq
  have hB := sum_cut l0 l1 q0 q1 b hl hq
  change 2 * (A.card : ℤ) = _
  change 2 * ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) = _ at hA
  change 2 * (B.card : ℤ) = _ at hB
  unfold fee2
  omega

def indexLo (w : Window) : ℤ := 1650-w.offsetHi
def indexHi (w : Window) (p : Triple) : ℤ :=
  max (indexLo w) (min (1651-(w.offsetLo : ℤ)) (p.index+1 : ℤ))
def orderHi (w : Window) : ℤ := 4651-w.diagonalLo
def orderLo (w : Window) (p : Triple) : ℤ :=
  min (orderHi w) (max (4650-(w.diagonalHi : ℤ)) (p.contact+1 : ℤ))

def columnFee2 (w : Window) (p : Triple) : ℤ :=
  if p.index ≤ 1650 then
    fee2 (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
  else 0

def debit (w : Window) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0

private theorem column_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (q : Column) (rows : Finset BlockIndex) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then charge i q else 0) ≤
      columnFee2 w (columnPoint q) := by
  let p := columnPoint q
  by_cases hp : p.index ≤ 1650
  · rw [columnFee2, ite_eq_left hp]
    let S := rows.filter (fun i => w.Contains i ∧ pays i q)
    let R := ((Ico (indexLo w) (indexHi w p)).product (Ico (orderLo w p) (orderHi w))).filter
      (fun x => (w.gradeLo : ℤ)-3000 ≤ x.1-x.2 ∧ x.1-x.2 < (w.gradeHi : ℤ)-3000)
    have hsum : (∑ i ∈ rows, if w.Contains i then charge i q else 0) = S.card := by
      calc
        _ = ∑ i ∈ rows, if w.Contains i ∧ pays i q then 1 else 0 := by
          apply sum_congr rfl
          intro i _
          by_cases hw : w.Contains i <;> simp [charge,hw]
        _ = _ := sum_boole _ _
    have hc : S.card ≤ R.card := by
      let f (i : BlockIndex) : ℤ × ℤ := (1650-i.2.val,4650-(i.1.val : ℤ)-i.2.val)
      refine card_le_card_of_injOn f ?_ ?_
      · intro i hi
        change i ∈ rows.filter (fun i => w.Contains i ∧ pays i q) at hi
        have hm : w.Contains i ∧ pays i q :=
          ((Finset.mem_filter (s := rows)
            (p := fun i => w.Contains i ∧ pays i q)).mp hi).2
        obtain ⟨hw,hpays⟩ := hm
        obtain ⟨hgl,hgh,hol,hoh,hdl,hdh⟩ := hw
        have hpos : 0 ≤ (initialFlag i).order := by
          dsimp [pays,p] at hpays
          have h := hpays.2.2
          omega
        obtain ⟨_, hidx, hcontact⟩ := hpays
        change -offset i ≤ (p.index : ℤ) at hidx
        change p.contact < (initialFlag i).order.toNat at hcontact
        change f i ∈ R
        simp only [initialFlag, offset] at hidx hcontact hpos
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · change f i ∈ (Ico (indexLo w) (indexHi w p)) ×ˢ (Ico (orderLo w p) (orderHi w))
          rw [Finset.mem_product]
          simp only [mem_Ico, f, indexLo, indexHi, orderLo, orderHi]
          omega
        · dsimp [f]
          omega
      · intro i _ j _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        simp only [f] at h1 h2
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hf := band_card (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
      (le_max_left _ _) (min_le_left _ _) (by omega)
    change 2 * (R.card : ℤ) = _ at hf
    rw [hsum, ← hf]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by decide)
  · rw [columnFee2, ite_eq_right hp]
    have hz (i : BlockIndex) : charge i q = 0 := by
      unfold charge pays
      simp [p,hp]
    simp [hz]

private theorem debit_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (rows : Finset BlockIndex) (columns : Finset Column) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then ∑ q ∈ columns, charge i q else 0) ≤
      ∑ q ∈ columns, columnFee2 w (columnPoint q) := by
  have h (i : BlockIndex) :
      (if w.Contains i then ∑ q ∈ columns, charge i q else 0) =
        ∑ q ∈ columns, if w.Contains i then charge i q else 0 := by
    split <;> simp [*]
  simp_rw [h]
  rw [sum_comm]
  push_cast
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hq := column_le_fee_on w hgrade q rows
  push_cast at hq
  exact hq

theorem debit_le_fee (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi) :
    2 * (debit w : ℤ) ≤ ∑ q : Column, columnFee2 w (columnPoint q) :=
  debit_le_fee_on w hgrade univ univ

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotRect
