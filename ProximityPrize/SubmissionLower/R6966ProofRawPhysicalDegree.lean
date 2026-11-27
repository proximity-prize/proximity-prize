import ProximityPrize.SubmissionLower.ListProofA
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.RawPhysicalDegree
open Polynomial
open scoped Polynomial
noncomputable section

variable {k : Type*} [Field k]
private abbrev Jets (k : Type*) [Semiring k] := k[X][X]
private abbrev Raw (k : Type*) [Semiring k] := k[X][X][X]

/-- The outer indeterminate records physical weight. Two independent tags in
the coefficient ring retain the ordinate and slope positions. -/
def encode (u v : ℕ) : Raw k →+* (Jets k)[X] :=
  let c : k →+* Jets k := C.comp C
  let phys : k[X] →+* (Jets k)[X] := mapRingHom c
  let y : (Jets k)[X] := monomial u (monomial 0 (monomial 1 (1:k)))
  let slope : (Jets k)[X] := monomial v (monomial 1 (monomial 0 (1:k)))
  eval₂RingHom (eval₂RingHom phys y) slope

private theorem encode_term (u v j i a : ℕ) (c : k) :
    encode u v (monomial j (monomial i (monomial a c))) =
      monomial (a+u*i+v*j) (monomial j (monomial i c)) := by
  simp only [encode,coe_eval₂RingHom,eval₂_monomial,coe_mapRingHom,map_monomial,
    RingHom.comp_apply,←monomial_zero_left,monomial_pow,monomial_mul_monomial,
    zero_mul,one_mul,one_pow,mul_one,zero_add,add_zero]

theorem coeff_encode (u v : ℕ) (P : Raw k) (n j i : ℕ) :
    (((encode u v P).coeff n).coeff j).coeff i =
      if u*i+v*j≤n then (((P.coeff j).coeff i).coeff (n-(u*i+v*j))) else 0 := by
  classical
  induction P using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add,coeff_add,hF,hG];split <;> simp
  | monomial l F =>
    induction F using Polynomial.induction_on' with
    | add F G hF hG =>
      simp only [map_add,coeff_add,hF,hG];split <;> simp
    | monomial m F =>
      induction F using Polynomial.induction_on' with
      | add F G hF hG =>
        simp only [map_add,coeff_add,hF,hG];split <;> simp
      | monomial b c =>
        rw [encode_term]
        by_cases hj : l=j
        · subst l
          by_cases hi : m=i
          · subst m
            by_cases eq : b+u*i+v*j=n
            · subst n;simp [coeff_monomial,show u*i+v*j≤b+u*i+v*j by omega,
                            show b+u*i+v*j-(u*i+v*j)=b by omega]
            · by_cases le : u*i+v*j≤n
              · have ne : b≠n-(u*i+v*j) := by omega
                simp [coeff_monomial,eq,le,ne]
              · simp [coeff_monomial,eq,le]
          · by_cases t : b+u*m+v*j=n <;> simp [coeff_monomial,hi,t]
        · by_cases t : b+u*m+v*l=n <;> simp [coeff_monomial,hj,t]

theorem encode_injective (u v : ℕ) : Function.Injective (encode (k:=k) u v) := by
  intro F G eq
  ext j i a
  have converted:=congrArg (fun p : (Jets k)[X] => ((p.coeff (a+u*i+v*j)).coeff j).coeff i) eq
  simpa only [coeff_encode,ite_eq_left (show u*i+v*j≤a+u*i+v*j by omega),
    show a+u*i+v*j-(u*i+v*j)=a by omega] using converted

def weight (u v : ℕ) (P : Raw k) := (encode u v P).natDegree

theorem bounded_iff (u v W : ℕ) (P : Raw k) :
    K1_14_1_4.Bounded u v W P ↔ weight u v P≤W := by
  constructor
  · intro h
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    ext j i
    rw [coeff_encode]
    split
    · rename_i hw
      by_contra ne
      have nonzero : ((P.coeff j).coeff i).coeff (n-(u*i+v*j))≠0 := by simpa using ne
      have := h j i _ nonzero
      omega
    · simp
  · intro h j i a nonzero
    by_contra! larger
    have vanish:=coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h larger)
    have z := congrArg (fun q:Jets k => (q.coeff j).coeff i) vanish
    apply nonzero
    simpa only [coeff_encode,ite_eq_left (show u*i+v*j≤a+u*i+v*j by omega),
      show a+u*i+v*j-(u*i+v*j)=a by omega,coeff_zero] using z

theorem weight_product (u v : ℕ) {F G : Raw k} (f:F≠0) (g:G≠0) :
    weight u v (F*G)=weight u v F+weight u v G := by
  simp only [weight,map_mul,natDegree_mul
    ((map_ne_zero_iff _ (encode_injective u v)).mpr f)
    ((map_ne_zero_iff _ (encode_injective u v)).mpr g)]

/-- Paying the primitive graph's weight at every forced division shrinks the
actual raw quotient. This conclusion is for integral raw rows. -/
theorem quotient_cap (u v W t : ℕ) {F G Q : Raw k} (nz : F≠0) (eq : F=G^t*Q)
    (bounded : K1_14_1_4.Bounded u v W F) :
    K1_14_1_4.Bounded u v (W-t*weight u v G) Q := by
  have prod : G^t*Q≠0 := eq ▸ nz
  have cap := (bounded_iff u v W F).mp bounded
  rw [eq,weight_product u v (left_ne_zero_of_mul prod) (right_ne_zero_of_mul prod)] at cap
  have power:weight u v (G^t)=t*weight u v G := by simp [weight,natDegree_pow]
  rw [power] at cap
  apply (bounded_iff ..).mpr
  omega


/-- The complete integral bank pays the full raw weight of a graph factor
after clearing the two CRT poles. -/
theorem complete_graph_quotient {h : ℕ} (hpos : 0<h) (hh : h≤131070)
    {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D) (word : K1.I→K1_14.L)
    {s W P} (mem : P∈K1_14_1.complete Crt word s W) (G Q : K1_14_1.RawSource) (t : ℕ)
    (gn : G≠0)
    (exact_div : K1_14_1.forward Crt P =
      K1_14_1.jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)) * (G^t*Q)) :
    K1_14_1_4.Bounded (131071-h) (131071-h-1)
      (W-t*weight (131071-h) (131071-h-1) G) Q := by
  obtain ⟨R,eq,bounded⟩:=P0_10_1.complete_raw_bounded hpos hh Crt word mem
  have pole : K1_14_1.jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)) ≠ 0 := by
    exact C_ne_zero.mpr (C_ne_zero.mpr ((K1_14_1_4.rawBlock_monic D).pow _).ne_zero)
  have desc := mul_left_cancel₀ pole (eq.symm.trans exact_div)
  by_cases zero : Q=0
  · subst Q;intro j i a ne;simp at ne
  · have rn : R≠0 := desc ▸ mul_ne_zero (pow_ne_zero _ gn) zero
    exact quotient_cap _ _ _ _ rn desc bounded

end
end Research6966.RawPhysicalDegree
