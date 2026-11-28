import ProximityPrize.SubmissionLower.AnchorNinth82190
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.PrimaryTaperBudget
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false

-- merged module ExpandedPivotOpt6970Rows
section Merged_ExpandedPivotOpt6970Rows

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace ExpandedPivotOpt6970
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open AnchorPivot82180 (independent)
open K1_13_2_2 (active_range_le)

def key (e : E) : ℕ :=
  8467200*e.a + 5644800*e.b + 2822401*e.c + 1680*e.f

noncomputable def encode : Form →ₐ[Geom] Polynomial Geom :=
  aeval (fun i => (Polynomial.X : Polynomial Geom)^(![8467200,5644800,2822401,1680] i : ℕ))

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
def Triple.exponent (p : Triple) : E := ⟨1679-p.b-p.c-p.f,p.b,p.c,p.f⟩
def Triple.room (p : Triple) := 1679-p.index
structure Groups where
  fourth : ℕ
  first : ℕ
  second : ℕ

def Groups.width (g : Groups) : ℕ := g.fourth+g.first+g.second
def Groups.gain (g : Groups) : ℕ := 2*g.fourth+g.first+g.second

def Triple.gainAt (p : Triple) (q : ℕ) : ℕ :=
  min (p.room + q) (min (p.b + p.c - q) (p.b + (500-p.f) - 2*q))

def Triple.fourthCap (p : Triple) : ℕ := min (min (p.b/3) p.room) (500-p.f)

def Triple.fourth (p : Triple) : ℕ :=
  let u := min p.fourthCap
    (min ((p.b+p.c-p.room)/2) ((p.b + (500-p.f)-p.room)/3))
  if u < p.fourthCap ∧ p.gainAt u < p.gainAt (u+1) then u+1 else u

private theorem fourth_le (p : Triple) : p.fourth ≤ p.fourthCap := by
  unfold Triple.fourth
  dsimp
  split <;> omega

def Triple.packet (p : Triple) : Groups :=
  let q := p.fourth
  let first := min (p.room-q) (p.b-3*q)
  ⟨q,first,min (min p.c (p.room-q-first)) (500-p.f-q)⟩

def Triple.contact (p : Triple) : ℕ := p.c+2*p.f+p.room+p.packet.gain

private theorem packet_valid (p : Triple) :
    p.packet.width ≤ p.room ∧ 3*p.packet.fourth+p.packet.first ≤ p.b ∧
      p.packet.second ≤ p.c ∧ p.packet.second + p.packet.fourth ≤ 500-p.f := by
  have h := fourth_le p
  simp only [Triple.fourthCap] at h
  simp only [Triple.packet, Groups.width]
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

private theorem row_bounds (p : Triple) (h : p.index ≤ 1679) (hf : p.f ≤ 500) :
    polynomial p ∈ bandSpace 1679 (p.index : ℤ) 1679 500 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact := by
  obtain ⟨hu,hb,hc,ht⟩ := packet_valid p
  have hs := ((((sound_monomial (remainder p)).mul (spec0.pow (linear p))).mul
    (spec3.pow p.packet.first)).mul (spec6.pow p.packet.second)).mul
    (spec7.pow p.packet.fourth)
  have hp : linear p + p.packet.width = p.room := by unfold linear; omega
  have hTotal : p.exponent.a + p.b + p.c + p.f = 1679 := by
    simp only [Triple.exponent, Triple.index] at *
    omega
  have ha : linear p+p.packet.fourth+p.packet.first+
      2*p.packet.second ≤ p.exponent.a := by
    simp only [Groups.width, Triple.exponent, Triple.room, Triple.index] at *
    omega
  have helpDegree : (remainder p).deg + linear p + p.packet.first*2 + p.packet.second*3 +
      p.packet.fourth*4 = 1679 := by
    simp only [remainder, E.deg]
    omega
  have helpIndex : (remainder p).index + p.packet.first + 2*p.packet.second +
      3*p.packet.fourth = p.index := by
    simp only [remainder, E.index, Triple.index]
    omega
  have helpTop : p.f + p.packet.second+p.packet.fourth ≤ 500 := by
    simp only [Groups.width, Triple.room, Triple.index] at *
    omega
  have helpUpper : (remainder p).index + linear p + 2*p.packet.first +3*p.packet.second +
      4*p.packet.fourth = 1679 := by
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

private theorem row_key (p : Triple) (h : p.index ≤ 1679) :
    key (remainder p) + linear p * key ⟨1,0,0,0⟩ +
      p.packet.first * key ⟨1,1,0,0⟩ + p.packet.second * key ⟨2,0,1,0⟩ +
      p.packet.fourth * key ⟨1,3,0,0⟩ = key p.exponent := by
  obtain ⟨hu,hb,hc,ht⟩ := packet_valid p
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

private theorem row_degree (p : Triple) (h : p.index ≤ 1679) :
    (encode (polynomial p)).degree = (key p.exponent : ℕ) := by
  rw [polynomial, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  exact (degree_products _ _ _ _ _ (linear p) p.packet.first p.packet.second p.packet.fourth
    _ _ _ _ _ (deg_remainder p) leading0 leading3 leading6 leading7).trans
      (congrArg (fun n : ℕ => (n : WithBot ℕ)) (row_key p h))

theorem row_sound (p : Triple) (h : p.index ≤ 1679) (hf : p.f ≤ 500) :
    polynomial p ∈ bandSpace 1679 (p.index : ℤ) 1679 500 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact ∧
      (encode (polynomial p)).degree = (key p.exponent : ℕ) :=
  ⟨(row_bounds p h hf).1, (row_bounds p h hf).2, row_degree p h⟩

theorem key_injective (p q : Triple) (hp : p.index ≤ 1679) (hq : q.index ≤ 1679)
    (h : key p.exponent = key q.exponent) : p = q := by
  have hform (r : Triple) (hr : r.index ≤ 1679) :
      key r.exponent = 2822400*(5037-r.index) + 1680*r.f + r.c := by
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


end ExpandedPivotOpt6970

end Merged_ExpandedPivotOpt6970Rows
