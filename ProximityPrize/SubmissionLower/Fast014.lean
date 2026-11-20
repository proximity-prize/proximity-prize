import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fast002
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Fast010
import ProximityPrize.SubmissionLower.Fast012
set_option Elab.async false

section PackSource_MCABridge
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
local instance decidableMCABridge (P : Prop) : Decidable P := Classical.propDecidable P

variable {F ι : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]

/-- No non-jointness information is needed for the full-rank stratum. -/
theorem isMCA_implies_decodable (x : ι ↪ F) (u : Fin 2 → ι → F)
    (k t : ℕ) [NeZero k] (δ : ℝ)
    (hthreshold : ∀ T : Finset ι,
      (Fintype.card ι : ℝ) * (1 - δ) ≤ T.card → Fintype.card ι - t ≤ T.card)
    (γ : F) (hmca : IsMCA (AffineLineGenerator F) (ReedSolomon.code x k) γ u δ) :
    Decodable x (u 0) (u 1) k t γ := by
  classical
  obtain ⟨T, hT, hcomb, _⟩ := hmca
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨c, hc, hproj⟩ := hcomb
  obtain ⟨P, hP, heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  refine ⟨P, Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hP), ?_⟩
  have hagree : ∀ i ∈ T, u 0 i + γ * u 1 i = P.eval (x i) := by
    intro i hi
    have hh := congrFun hproj ⟨i, hi⟩
    simpa [AffineLineGenerator, Fin.sum_univ_two, LinearCode.projectedWord,
      heval i, smul_eq_mul, mul_comm] using hh
  have hs : Finset.univ.filter (fun i => u 0 i + γ * u 1 i ≠ P.eval (x i)) ⊆
      Finset.univ \ T := by
    intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hit => hne (hagree i hit)⟩
  have hcard := Finset.card_le_card hs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ] at hcard
  have := hthreshold T hT
  omega

end
end FrobeniusLocator
end PackSource_MCABridge

section PackSource_BadSlope
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
local instance decidableBadSlope (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Same-support MCA badness in polynomial form. -/
def BadSlope (x : ι → F) (u v : ι → F) (k A : ℕ) (γ : F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧
    ExtendsOn x (fun i => u i + γ * v i) k S ∧
    ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)

theorem degree_smul_lt (a : F) {P : F[X]} {k : ℕ} (hP : P.degree < k) :
    (a • P).degree < k := (Polynomial.degree_smul_le a P).trans_lt hP

theorem degree_sub_lt {P Q : F[X]} {k : ℕ}
    (hP : P.degree < k) (hQ : Q.degree < k) : (P-Q).degree < k :=
  (Polynomial.degree_sub_le P Q).trans_lt (max_lt hP hQ)

/-- A nonzero constant linear relation modulo the code leaves at most
one possible bad slope. This uses the original same witness set. -/
theorem bad_slope_relation (x : ι → F) (u v : ι → F) (k A : ℕ)
    (a b γ : F)
    (hrel : ExtendsOn x (fun i => a * u i + b * v i) k Finset.univ)
    (hbad : BadSlope x u v k A γ) : a * γ = b := by
  classical
  by_contra hne
  obtain ⟨P, hP, hPv⟩ := hrel
  obtain ⟨S, hAS, ⟨Q, hQ, hQv⟩, hnonjoint⟩ := hbad
  have hd : b-a*γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let V : F[X] := (b-a*γ)⁻¹ • (P-a • Q)
  let U : F[X] := Q-γ • V
  have hV : V.degree < k := degree_smul_lt _ (degree_sub_lt hP (degree_smul_lt a hQ))
  have hU : U.degree < k := degree_sub_lt hQ (degree_smul_lt γ hV)
  have hVv : ∀ i ∈ S, V.eval (x i) = v i := by
    intro i hi
    dsimp [V]
    simp only [Polynomial.eval_smul, Polynomial.eval_sub, smul_eq_mul]
    rw [hPv i (Finset.mem_univ i), hQv i hi]
    field_simp
    ring
  have hUv : ∀ i ∈ S, U.eval (x i) = u i := by
    intro i hi
    dsimp [U]
    simp only [Polynomial.eval_sub, Polynomial.eval_smul, smul_eq_mul]
    rw [hQv i hi, hVv i hi]
    ring
  exact hnonjoint ⟨⟨U,hU,hUv⟩, ⟨V,hV,hVv⟩⟩

theorem bad_slope_card_le_one_of_relation (x : ι → F) (u v : ι → F) (k A : ℕ)
    (a b : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (hrel : ExtendsOn x (fun i => a*u i+b*v i) k Finset.univ)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) : Γ.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro γ hγ γ' hγ'
  have hg := bad_slope_relation x u v k A a b γ hrel (hΓ γ hγ)
  have hg' := bad_slope_relation x u v k A a b γ' hrel (hΓ γ' hγ')
  rcases hab with ha | hb
  · exact mul_left_cancel₀ ha (hg.trans hg'.symm)
  · have ha : a ≠ 0 := by intro hz; simp [hz] at hg; exact hb hg.symm
    exact mul_left_cancel₀ ha (hg.trans hg'.symm)

/-- Exact-A witness extraction, preserving the nonjoint condition. -/
theorem bad_slope_exact (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k A : ℕ) (hkA : k < A) (γ : F)
    (hbad : BadSlope x u v k A γ) :
    ∃ T : Finset ι, T.card = A ∧
      ExtendsOn x (fun i => u i+γ*v i) k T ∧
      ¬ (ExtendsOn x u k T ∧ ExtendsOn x v k T) := by
  obtain ⟨S,hS,⟨P,hP,hPv⟩,hbad⟩ := hbad
  obtain ⟨T,_,hT,hP',hPv',hbad'⟩ :=
    exact_A_bad_witness x hx u v γ k A hkA S hS P hP hPv hbad
  exact ⟨T,hT,⟨P,hP',hPv'⟩,hbad'⟩

end
end FrobeniusLocator.Principal
end PackSource_BadSlope

section PackSource_TwistedRelation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Coefficient conjugation preserves evaluation at fixed nodes. -/
theorem eval_coefficient_map (σ : F →+* F) (P : F[X]) (a : F)
    (ha : σ a = a) : (P.map σ).eval a = σ (P.eval a) := by
  simpa only [ha] using (Polynomial.eval_map_apply σ a (p := P))

/-- Multiplication by a degree-at-most-h coefficient preserves the strict
RS degree convention. This includes zero polynomials and k=0. -/
theorem degree_mul_lt_add (U P : F[X]) (h k : ℕ)
    (hU : U.natDegree ≤ h) (hP : P.degree < k) :
    (U*P).degree < k+h := by
  by_cases hp : P=0
  · simp [hp]
  have hpn : P.natDegree < k := (natDegree_lt_iff_degree_lt hp).mpr hP
  have hb : (U*P).natDegree < k+h :=
    natDegree_mul_le.trans_lt (by omega)
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hb)

/-- One specialized twisted relation. Its existence is a separate theorem;
this structure itself is not an axiom or a claim about arbitrary pairs. -/
structure TwistedRelation (σ : F →+* F) (x w : ι → F)
    (k h : ℕ) (U V R : F[X]) : Prop where
  degree_U : U.natDegree ≤ h
  degree_V : V.natDegree ≤ h
  degree_R : R.degree < k+h
  nodes : ∀ i, U.eval (x i)*w i + V.eval (x i)*σ (w i) = R.eval (x i)

/-- Root counting turns the node relation into a polynomial identity for
EVERY close decoder. No affine-closure claim about close decoders is used. -/
theorem decoder_polynomial_identity (σ : F →+* F)
    (x w : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (k h : ℕ) (U V R : F[X]) (rel : TwistedRelation σ x w k h U V R)
    (S : Finset ι) (hS : k+h ≤ S.card) (P : F[X]) (hP : P.degree < k)
    (hagree : ∀ i ∈ S, P.eval (x i)=w i) :
    U*P+V*(P.map σ)=R := by
  classical
  let Q := U*P+V*(P.map σ)-R
  have hmap : (P.map σ).degree < k := (Polynomial.degree_map_le).trans_lt hP
  have hQ : Q.degree < (k+h : ℕ) := by
    apply (Polynomial.degree_sub_le _ _).trans_lt
    exact max_lt
      ((Polynomial.degree_add_le _ _).trans_lt
        (max_lt (degree_mul_lt_add U P h k rel.degree_U hP)
          (degree_mul_lt_add V (P.map σ) h k rel.degree_V hmap))) rel.degree_R
  have hz : ∀ i ∈ S, Q.eval (x i)=0 := by
    intro i hi
    dsimp [Q]
    rw [eval_sub, eval_add, eval_mul, eval_mul,
      eval_coefficient_map σ P (x i) (hfixed i), hagree i hi,
      rel.nodes i, sub_self]
  have hzero : Q=0 := by
    by_contra hne
    have hc : (S.image x).card ≤ Q.natDegree :=
      Polynomial.card_le_degree_of_subset_roots (fun a ha =>
        (Polynomial.mem_roots hne).mpr (by
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
          exact hz i hi))
    rw [Finset.card_image_of_injective S hx] at hc
    have hdeg : Q.natDegree < k+h := (natDegree_lt_iff_degree_lt hne).mpr hQ
    omega
  exact sub_eq_zero.mp hzero

/-- At all nodes, including actual errors and common coefficient zeros,
the error satisfies U e + V sigma(e)=0. -/
theorem decoder_error_identity (σ : F →+* F)
    (x w : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (k h : ℕ) (U V R : F[X]) (rel : TwistedRelation σ x w k h U V R)
    (S : Finset ι) (hS : k+h ≤ S.card) (P : F[X]) (hP : P.degree < k)
    (hagree : ∀ i ∈ S, P.eval (x i)=w i) (i : ι) :
    U.eval (x i)*(w i-P.eval (x i)) +
      V.eval (x i)*σ (w i-P.eval (x i))=0 := by
  have hpoly := decoder_polynomial_identity σ x w hx hfixed k h U V R rel S hS P hP hagree
  have he := congrArg (Polynomial.eval (x i)) hpoly
  rw [eval_add, eval_mul, eval_mul, eval_coefficient_map σ P (x i) (hfixed i)] at he
  have hr := rel.nodes i
  rw [map_sub]
  linear_combination hr - he

/-- The Frobenius specialization requested by the residual ledger. -/
theorem frobenius_error_identity (p : ℕ) [ExpChar F p]
    (x w : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (k h : ℕ) (U V R : F[X])
    (rel : TwistedRelation (frobenius F p) x w k h U V R)
    (S : Finset ι) (hS : k+h ≤ S.card) (P : F[X]) (hP : P.degree < k)
    (hagree : ∀ i ∈ S, P.eval (x i)=w i) (i : ι) :
    U.eval (x i)*(w i-P.eval (x i)) +
      V.eval (x i)*(w i-P.eval (x i))^p=0 :=
  decoder_error_identity (frobenius F p) x w hx hfixed k h U V R rel S hS P hP hagree i

end
end FrobeniusLocator.Strata
end PackSource_TwistedRelation

section PackSource_CoprimeSpan
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F]

/-- Elementary bounded Bezout decomposition when v attains the maximum
degree. Reduction of a Bezout coefficient modulo v gives the bound. -/
theorem coprime_bounded_decomposition_right (u v P : F[X]) (d L : ℕ)
    (hu : u.natDegree≤d) (hv : v≠0) (hvd : v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) (hP : P.degree < (L+d : ℕ)) :
    ∃ A B : F[X], A.degree<L ∧ B.degree<L ∧ P=u*A+v*B := by
  obtain ⟨s,t,hst⟩ := hcop
  let A := (s*P)%v
  let B := t*P+u*((s*P)/v)
  have hA : A.degree<L := by
    apply (Polynomial.degree_mod_lt (s*P) hv).trans_le
    exact Polynomial.degree_le_natDegree.trans (by exact_mod_cast (hvd.trans_le hdL))
  have heq : P=u*A+v*B := by
    have hm := EuclideanDomain.mod_add_div (s*P) v
    calc
      P = (s*u+t*v)*P := by rw [hst,one_mul]
      _ = u*(A+v*((s*P)/v))+v*(t*P) := by rw [show A+v*((s*P)/v)=s*P from hm]; ring
      _ = u*A+v*B := by dsimp [B]; ring
  have hB : B.degree<L := by
    by_cases hb : B=0
    · simp [hb]
    have hprod : (v*B).degree < (L+d : ℕ) := by
      rw [show v*B=P-u*A by rw [heq]; ring]
      exact (degree_sub_le _ _).trans_lt
        (max_lt hP (degree_mul_lt_add u A d L hu hA))
    have hbn := (natDegree_lt_iff_degree_lt (mul_ne_zero hv hb)).mpr hprod
    rw [natDegree_mul hv hb,hvd] at hbn
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show B.natDegree<L by omega))
  exact ⟨A,B,hA,hB,heq⟩

/-- The two coprime degree-d numerator blocks with L≥d span the ENTIRE
polynomial space of degree <L+d, even with unequal affine degrees. -/
theorem coprime_bounded_decomposition (u v P : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) (hP : P.degree<(L+d : ℕ)) :
    ∃ A B : F[X], A.degree<L ∧ B.degree<L ∧ P=u*A+v*B := by
  by_cases hvd : v.natDegree=d
  · exact coprime_bounded_decomposition_right u v P d L
      (by omega) hv hvd hcop hdL hP
  · have hud : u.natDegree=d := by omega
    obtain ⟨B,A,hB,hA,heq⟩ := coprime_bounded_decomposition_right v u P d L
      (by omega) hu hud hcop.symm hdL hP
    exact ⟨A,B,hA,hB,by rw [heq,add_comm]⟩

/-- In particular, no homogeneous Hilbert--Burch theorem is needed for
the two-generator span step. -/
theorem coprime_span_iff (u v P : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) :
    P.degree<(L+d : ℕ) ↔
      ∃ A B : F[X], A.degree<L ∧ B.degree<L ∧ P=u*A+v*B := by
  constructor
  · exact coprime_bounded_decomposition u v P d L hu hv hd hcop hdL
  · rintro ⟨A,B,hA,hB,rfl⟩
    exact (degree_add_le _ _).trans_lt
      (max_lt (degree_mul_lt_add u A d L (by omega) hA)
        (degree_mul_lt_add v B d L (by omega) hB))

end
end FrobeniusLocator.Strata
end PackSource_CoprimeSpan

section PackSource_GcdSpan
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]

/-- Removing a polynomial gcd preserves the maximum degree with the
expected subtraction. Both original polynomials may have unequal degrees. -/
theorem gcd_reduction_degrees (u v : F[X]) (hu : u≠0) (hv : v≠0) :
    (GCDMonoid.gcd u v).natDegree≤max u.natDegree v.natDegree ∧
    max (u / GCDMonoid.gcd u v).natDegree (v / GCDMonoid.gcd u v).natDegree =
      max u.natDegree v.natDegree-(GCDMonoid.gcd u v).natDegree := by
  let J := GCDMonoid.gcd u v
  have hJ : J≠0 := gcd_ne_zero_of_right hv
  have ha := left_div_gcd_ne_zero hu (q := v)
  have hb := right_div_gcd_ne_zero hv (p := u)
  have hua : J*(u/J)=u := EuclideanDomain.mul_div_cancel' hJ (gcd_dvd_left u v)
  have hvb : J*(v/J)=v := EuclideanDomain.mul_div_cancel' hJ (gcd_dvd_right u v)
  have hda := natDegree_mul hJ ha
  have hdb := natDegree_mul hJ hb
  rw [hua] at hda
  rw [hvb] at hdb
  change J.natDegree≤max u.natDegree v.natDegree ∧
    max (u/J).natDegree (v/J).natDegree=max u.natDegree v.natDegree-J.natDegree
  have huD : u.natDegree=J.natDegree+(u/J).natDegree := hda
  have hvD : v.natDegree=J.natDegree+(v/J).natDegree := hdb
  rw [huD,hvD,Nat.add_max_add_left]
  constructor <;> omega

/-- The complete two-generator bounded span, including a nontrivial gcd.
Only Euclidean division and bounded Bezout decomposition are used. -/
theorem gcd_span_iff (u v P : F[X]) (L : ℕ) (hu : u≠0) (hv : v≠0)
    (hL : max u.natDegree v.natDegree-(GCDMonoid.gcd u v).natDegree≤L) :
    (∃ A B : F[X], A.degree<L ∧ B.degree<L ∧ P=u*A+v*B) ↔
      ∃ W : F[X], W.degree < (L+(max u.natDegree v.natDegree-
        (GCDMonoid.gcd u v).natDegree) : ℕ) ∧ P=GCDMonoid.gcd u v*W := by
  let J := GCDMonoid.gcd u v
  let d := max u.natDegree v.natDegree
  have hJ : J≠0 := gcd_ne_zero_of_right hv
  have ha := left_div_gcd_ne_zero hu (q := v)
  have hb := right_div_gcd_ne_zero hv (p := u)
  have hua : J*(u/J)=u := EuclideanDomain.mul_div_cancel' hJ (gcd_dvd_left u v)
  have hvb : J*(v/J)=v := EuclideanDomain.mul_div_cancel' hJ (gcd_dvd_right u v)
  obtain ⟨hj,hd⟩ := gcd_reduction_degrees u v hu hv
  change J.natDegree≤d at hj
  change max (u/J).natDegree (v/J).natDegree=d-J.natDegree at hd
  constructor
  · rintro ⟨A,B,hA,hB,hP⟩
    have hdvd : J∣P := by
      rw [hP]
      exact dvd_add ((gcd_dvd_left u v).mul_right A) ((gcd_dvd_right u v).mul_right B)
    obtain ⟨W,hW⟩ := hdvd
    refine ⟨W,?_,hW⟩
    by_cases hw0 : W=0
    · simp [hw0]
    have hp0 : P≠0 := by rw [hW]; exact mul_ne_zero hJ hw0
    have hpdeg : P.degree<(L+d : ℕ) := by
      rw [hP]
      exact (degree_add_le _ _).trans_lt
        (max_lt (degree_mul_lt_add u A d L (by dsimp [d]; omega) hA)
          (degree_mul_lt_add v B d L (by dsimp [d]; omega) hB))
    have hn := (natDegree_lt_iff_degree_lt hp0).mpr hpdeg
    rw [hW,natDegree_mul hJ hw0] at hn
    exact degree_le_natDegree.trans_lt (by exact_mod_cast
      (show W.natDegree<L+(d-J.natDegree) by omega))
  · rintro ⟨W,hW,rfl⟩
    obtain ⟨A,B,hA,hB,heq⟩ := coprime_bounded_decomposition (u/J) (v/J) W
      (d-J.natDegree) L ha hb hd (isCoprime_div_gcd_div_gcd hv) hL hW
    refine ⟨A,B,hA,hB,?_⟩
    calc
      J*W = J*((u/J)*A+(v/J)*B) := by rw [heq]
      _ = u*A+v*B := by rw [mul_add,← mul_assoc,← mul_assoc,hua,hvb]

end
end FrobeniusLocator.Strata
end PackSource_GcdSpan

section PackSource_EvaluationRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι]

/-- Evaluation of the full bounded polynomial space. -/
def boundedEvaluation (x : ι → F) (N : ℕ) : Polynomial.degreeLT F N →ₗ[F] (ι → F) where
  toFun P i := (P : F[X]).eval (x i)
  map_add' P Q := by ext i; exact eval_add
  map_smul' c P := by ext i; simp

theorem boundedEvaluation_injective (x : ι → F) (hx : Function.Injective x) (N : ℕ)
    (hN : N≤Fintype.card ι) : Function.Injective (boundedEvaluation x N) := by
  classical
  intro P Q hPQ
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hne
  have hdeg : ((P : F[X])-(Q : F[X])).degree<N :=
    (degree_sub_le _ _).trans_lt
      (max_lt (Polynomial.mem_degreeLT.mp P.property) (Polynomial.mem_degreeLT.mp Q.property))
  have hn : ((P : F[X])-(Q : F[X])).natDegree<N :=
    (natDegree_lt_iff_degree_lt hne).mpr hdeg
  have hz : ∀ i, ((P : F[X])-(Q : F[X])).eval (x i)=0 := by
    intro i
    rw [eval_sub,sub_eq_zero]
    exact congrFun hPQ i
  exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx hz (by omega))

theorem boundedEvaluation_surjective (x : ι → F) (hx : Function.Injective x) (N : ℕ)
    (hN : Fintype.card ι≤N) : Function.Surjective (boundedEvaluation x N) := by
  classical
  intro w
  let P := Lagrange.interpolate (Finset.univ : Finset ι) x w
  have hP : P.degree<N := by
    exact (Lagrange.degree_interpolate_lt w hx.injOn).trans_le (by
      simpa only [Finset.card_univ] using (show (Fintype.card ι : WithBot ℕ)≤N by exact_mod_cast hN))
  refine ⟨⟨P,Polynomial.mem_degreeLT.mpr hP⟩,?_⟩
  funext i
  exact Lagrange.eval_interpolate_at_node w hx.injOn (Finset.mem_univ i)

/-- The Vandermonde rank formula, including zero nodes/zero bound. -/
theorem boundedEvaluation_rank (x : ι → F) (hx : Function.Injective x) (N : ℕ) :
    Module.finrank F (LinearMap.range (boundedEvaluation x N))=min (Fintype.card ι) N := by
  by_cases hN : N≤Fintype.card ι
  · rw [LinearMap.finrank_range_of_inj (boundedEvaluation_injective x hx N hN)]
    have hd := (Polynomial.degreeLTEquiv F N).finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,min_eq_right hN] using hd
  · have hc : Fintype.card ι≤N := by omega
    rw [LinearMap.range_eq_top.mpr (boundedEvaluation_surjective x hx N hc),finrank_top,
      Module.finrank_fintype_fun_eq_card,min_eq_left hc]

end
end FrobeniusLocator.Strata
end PackSource_EvaluationRank

section PackSource_TripleSpan
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]

/-- The exact three-numerator polynomial-span theorem, proved by TWO
ordinary bounded Bezout decompositions. This replaces the written
Hilbert--Burch/syzygy argument for this particular span. -/
theorem triple_span_iff (σ : F →+* F) (u v P : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) :
    (∃ A B C : F[X], A.degree<L ∧ B.degree<L ∧ C.degree<L ∧
      P=(v*v.map σ)*A+(u*v.map σ)*B+(u*u.map σ)*C) ↔
      ∃ W : F[X], W.degree < (L+2*d-(GCDMonoid.gcd u (v.map σ)).natDegree : ℕ) ∧
        P=GCDMonoid.gcd u (v.map σ)*W := by
  have huσ : u.map σ≠0 := by simpa using hu
  have hvσ : v.map σ≠0 := by simpa using hv
  have hdu : (u.map σ).natDegree=u.natDegree := natDegree_map_eq_of_injective σ.injective u
  have hdv : (v.map σ).natDegree=v.natDegree := natDegree_map_eq_of_injective σ.injective v
  have hdσ : max (u.map σ).natDegree (v.map σ).natDegree=d := by rw [hdu,hdv,hd]
  have hcopσ : IsCoprime (u.map σ) (v.map σ) := hcop.map (Polynomial.mapRingHom σ)
  have hcross : max u.natDegree (v.map σ).natDegree=d := by rw [hdv,hd]
  have hj := (gcd_reduction_degrees u (v.map σ) hu hvσ).1
  rw [hcross] at hj
  have hnum : (L+d)+(d-(GCDMonoid.gcd u (v.map σ)).natDegree) =
      L+2*d-(GCDMonoid.gcd u (v.map σ)).natDegree := by omega
  have hspan := gcd_span_iff u (v.map σ) P (L+d) hu hvσ
    (by rw [hcross]; omega)
  rw [hcross,hnum] at hspan
  constructor
  · rintro ⟨A,B,C,hA,hB,hC,hP⟩
    apply hspan.mp
    refine ⟨v.map σ*B+u.map σ*C,v*A,?_,?_,?_⟩
    · exact (degree_add_le _ _).trans_lt
        (max_lt (degree_mul_lt_add (v.map σ) B d L (by omega) hB)
          (degree_mul_lt_add (u.map σ) C d L (by omega) hC))
    · exact degree_mul_lt_add v A d L (by omega) hA
    · rw [hP]; ring
  · intro hW
    obtain ⟨Q,R,hQ,hR,hP⟩ := hspan.mpr hW
    obtain ⟨C,B1,hC,hB1,hQeq⟩ := coprime_bounded_decomposition (u.map σ) (v.map σ)
      Q d L huσ hvσ hdσ hcopσ hdL hQ
    obtain ⟨B2,A,hB2,hA,hReq⟩ := coprime_bounded_decomposition u v R d L
      hu hv hd hcop hdL hR
    refine ⟨A,B1+B2,C,hA,(degree_add_le _ _).trans_lt (max_lt hB1 hB2),hC,?_⟩
    rw [hP,hQeq,hReq]
    ring

end
end FrobeniusLocator.Strata
end PackSource_TripleSpan

section PackSource_SpanMatrices
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [Fintype ι] [Fintype β]

/-- Coefficients indexed by Fin L, including L=0. -/
def coefficientPolynomial {L : ℕ} (a : Fin L → F) : F[X] :=
  ∑ j, Polynomial.monomial j.val (a j)

theorem coefficientPolynomial_degree {L : ℕ} (a : Fin L → F) :
    (coefficientPolynomial a).degree<L := by
  apply Polynomial.mem_degreeLT.mp
  apply (Polynomial.degreeLT F L).sum_mem
  intro j _
  exact Polynomial.mem_degreeLT.mpr
    ((Polynomial.degree_monomial_le _ _).trans_lt (by exact_mod_cast j.isLt))

theorem coefficientPolynomial_eval {L : ℕ} (a : Fin L → F) (x : F) :
    (coefficientPolynomial a).eval x=∑ j, a j*x^j.val := by
  simp only [coefficientPolynomial,eval_finsetSum,eval_monomial]

theorem eval_degreeLT_sum (L : ℕ) (P : Polynomial.degreeLT F L) (x : F) :
    (P : F[X]).eval x=∑ j : Fin L, (P : F[X]).coeff j.val*x^j.val := by
  by_cases hp : (P : F[X])=0
  · simp [hp]
  rw [Fin.sum_univ_eq_sum_range (fun j => (P : F[X]).coeff j*x^j) L]
  exact Polynomial.eval_eq_sum_range'
    ((natDegree_lt_iff_degree_lt hp).mpr (Polynomial.mem_degreeLT.mp P.property)) x

/-- Bounded polynomial combinations of a finite numerator family. -/
def polynomialCombination (g : β → F[X]) (L : ℕ) :
    (β → Polynomial.degreeLT F L) →ₗ[F] F[X] where
  toFun Q := ∑ b, g b*(Q b : F[X])
  map_add' Q R := by simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' c Q := by simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

def allEvaluation (x : ι → F) : F[X] →ₗ[F] (ι → F) where
  toFun P i := P.eval (x i)
  map_add' P Q := by ext i; exact eval_add
  map_smul' c P := by ext i; simp

/-- Polynomial numerator blocks evaluated at the nodes. -/
def numeratorMatrix (x : ι → F) (g : β → F[X]) (L : ℕ) :
    Matrix (β × Fin L) ι F := fun b i => (g b.1).eval (x i)*x i^b.2.val

/-- Matrix row combinations and bounded polynomial combinations have
exactly the same evaluated image. -/
theorem numerator_range (x : ι → F) (g : β → F[X]) (L : ℕ) :
    LinearMap.range (numeratorMatrix x g L).transpose.mulVecLin =
      (LinearMap.range (polynomialCombination g L)).map (allEvaluation x) := by
  classical
  rw [← LinearMap.range_comp]
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    let Q : β → Polynomial.degreeLT F L := fun b =>
      ⟨coefficientPolynomial (fun j => a (b,j)),Polynomial.mem_degreeLT.mpr (coefficientPolynomial_degree _)⟩
    refine ⟨Q,?_⟩
    funext i
    simp only [LinearMap.comp_apply,allEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
      polynomialCombination,eval_finsetSum,eval_mul,Q,coefficientPolynomial_eval,
      Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,numeratorMatrix,Matrix.transpose_apply,
      Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rintro _ ⟨Q,rfl⟩
    refine ⟨fun b => (Q b.1 : F[X]).coeff b.2.val,?_⟩
    funext i
    simp only [LinearMap.comp_apply,allEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
      polynomialCombination,eval_finsetSum,eval_mul,Matrix.mulVecLin_apply,
      Matrix.mulVec,dotProduct,numeratorMatrix,Matrix.transpose_apply,Fintype.sum_prod_type]
    simp_rw [eval_degreeLT_sum L (Q _) (x i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Rank is now the dimension of an evaluated POLYNOMIAL subspace. -/
theorem numerator_rank (x : ι → F) (g : β → F[X]) (L : ℕ) :
    (numeratorMatrix x g L).rank = Module.finrank F
      ((LinearMap.range (polynomialCombination g L)).map (allEvaluation x)) := by
  rw [← numerator_range]
  exact (Matrix.rank_transpose _).symm

end
end FrobeniusLocator.Strata
end PackSource_SpanMatrices

section PackSource_PolynomialRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

def polynomialMul (J : F[X]) : F[X] →ₗ[F] F[X] where
  toFun P := J*P
  map_add' P Q := mul_add _ _ _
  map_smul' c P := mul_smul_comm _ _ _

/-- Invertible coordinate scaling at a finite collection of nodes. -/
def coordinateScale (c : ι → F) (hc : ∀ i, c i≠0) : (ι → F) ≃ₗ[F] (ι → F) where
  toFun v i := c i*v i
  invFun v i := (c i)⁻¹*v i
  left_inv v := by funext i; simp only [← mul_assoc,inv_mul_cancel₀ (hc i),one_mul]
  right_inv v := by funext i; simp only [← mul_assoc,mul_inv_cancel₀ (hc i),one_mul]
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' a v := by funext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- Evaluating a polynomial multiple by a unit at every node preserves
Vandermonde rank exactly. -/
theorem multiple_evaluation_rank (x : ι → F) (hx : Function.Injective x)
    (J : F[X]) (hJ : ∀ i, J.eval (x i)≠0) (N : ℕ) :
    Module.finrank F (((Polynomial.degreeLT F N).map (polynomialMul J)).map (allEvaluation x)) =
      min (Fintype.card ι) N := by
  let e := coordinateScale (fun i => J.eval (x i)) hJ
  have heval : LinearMap.range (boundedEvaluation x N) =
      (Polynomial.degreeLT F N).map (allEvaluation x) := by
    ext v
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have heq : ((Polynomial.degreeLT F N).map (polynomialMul J)).map (allEvaluation x) =
      (LinearMap.range (boundedEvaluation x N)).map e.toLinearMap := by
    rw [heval,← Submodule.map_comp,← Submodule.map_comp]
    congr 1
    ext P i
    exact eval_mul
  rw [heq,LinearEquiv.finrank_map_eq,boundedEvaluation_rank x hx N]

/-- The three numerator blocks as a literal Fin3 family. -/
def tripleNumerators (σ : F →+* F) (u v : F[X]) : Fin 3 → F[X] :=
  ![v*v.map σ,u*v.map σ,u*u.map σ]

theorem triple_polynomial_range (σ : F →+* F) (u v : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) :
    LinearMap.range (polynomialCombination (tripleNumerators σ u v) L)=
      (Polynomial.degreeLT F (L+2*d-(GCDMonoid.gcd u (v.map σ)).natDegree)).map
        (polynomialMul (GCDMonoid.gcd u (v.map σ))) := by
  apply le_antisymm
  · rintro _ ⟨Q,rfl⟩
    have he : ∃ A B C : F[X], A.degree<L ∧ B.degree<L ∧ C.degree<L ∧
        polynomialCombination (tripleNumerators σ u v) L Q=
          (v*v.map σ)*A+(u*v.map σ)*B+(u*u.map σ)*C := by
      refine ⟨Q 0,Q 1,Q 2,Polynomial.mem_degreeLT.mp (Q 0).property,
        Polynomial.mem_degreeLT.mp (Q 1).property,Polynomial.mem_degreeLT.mp (Q 2).property,?_⟩
      simp only [polynomialCombination,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_three,tripleNumerators,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    obtain ⟨W,hW,hP⟩ := (triple_span_iff σ u v _ d L hu hv hd hcop hdL).mp he
    exact ⟨W,Polynomial.mem_degreeLT.mpr hW,hP.symm⟩
  · rintro _ ⟨W,hW,rfl⟩
    obtain ⟨A,B,C,hA,hB,hC,hP⟩ :=
      (triple_span_iff σ u v ((GCDMonoid.gcd u (v.map σ))*W) d L hu hv hd hcop hdL).mpr
        ⟨W,Polynomial.mem_degreeLT.mp hW,rfl⟩
    let Q : Fin 3 → Polynomial.degreeLT F L :=
      ![⟨A,Polynomial.mem_degreeLT.mpr hA⟩,⟨B,Polynomial.mem_degreeLT.mpr hB⟩,⟨C,Polynomial.mem_degreeLT.mpr hC⟩]
    refine ⟨Q,?_⟩
    change (∑ b : Fin 3, tripleNumerators σ u v b*(Q b : F[X]))=_
    simp only [Fin.sum_univ_three,tripleNumerators,Q,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    exact hP.symm

/-- Exact evaluated three-block numerator rank. This is a matrix theorem,
not only an equality of formal polynomial spans. -/
theorem triple_numerator_rank (σ : F →+* F) (x : ι → F) (hx : Function.Injective x)
    (u v : F[X]) (d L : ℕ) (hu : u≠0) (hv : v≠0)
    (hd : max u.natDegree v.natDegree=d) (hcop : IsCoprime u v) (hdL : d≤L)
    (hJ : ∀ i, (GCDMonoid.gcd u (v.map σ)).eval (x i)≠0) :
    (numeratorMatrix x (tripleNumerators σ u v) L).rank =
      min (Fintype.card ι) (L+2*d-(GCDMonoid.gcd u (v.map σ)).natDegree) := by
  rw [numerator_rank,triple_polynomial_range σ u v d L hu hv hd hcop hdL]
  exact multiple_evaluation_rank x hx _ hJ _

end
end FrobeniusLocator.Strata
end PackSource_PolynomialRank

section PackSource_PairRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι]

def pairNumerators (u v : F[X]) : Fin 2 → F[X] := ![v,u]

theorem pair_polynomial_range (u v : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) :
    LinearMap.range (polynomialCombination (pairNumerators u v) L)=Polynomial.degreeLT F (L+d) := by
  apply le_antisymm
  · rintro _ ⟨Q,rfl⟩
    apply Polynomial.mem_degreeLT.mpr
    have hQ := (coprime_span_iff u v
      (v*(Q 0 : F[X])+u*(Q 1 : F[X])) d L hu hv hd hcop hdL).mpr
      ⟨Q 1,Q 0,Polynomial.mem_degreeLT.mp (Q 1).property,
        Polynomial.mem_degreeLT.mp (Q 0).property,add_comm _ _⟩
    simpa [polynomialCombination,pairNumerators,Fin.sum_univ_two] using hQ
  · intro P hP
    obtain ⟨A,B,hA,hB,hP⟩ := coprime_bounded_decomposition u v P d L hu hv hd hcop hdL
      (Polynomial.mem_degreeLT.mp hP)
    let Q : Fin 2 → Polynomial.degreeLT F L :=
      ![⟨B,Polynomial.mem_degreeLT.mpr hB⟩,⟨A,Polynomial.mem_degreeLT.mpr hA⟩]
    refine ⟨Q,?_⟩
    change (∑ b : Fin 2, pairNumerators u v b*(Q b : F[X]))=P
    simpa [Fin.sum_univ_two,pairNumerators,Q,add_comm] using hP.symm

theorem degreeLT_evaluation_range (x : ι → F) (N : ℕ) :
    (Polynomial.degreeLT F N).map (allEvaluation x)=LinearMap.range (boundedEvaluation x N) := by
  ext v
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact ⟨⟨P,hP⟩,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨P,P.property,rfl⟩

theorem pair_numerator_rank (x : ι → F) (hx : Function.Injective x)
    (u v : F[X]) (d L : ℕ) (hu : u≠0) (hv : v≠0)
    (hd : max u.natDegree v.natDegree=d) (hcop : IsCoprime u v) (hdL : d≤L) :
    (numeratorMatrix x (pairNumerators u v) L).rank=min (Fintype.card ι) (L+d) := by
  rw [numerator_rank,pair_polynomial_range u v d L hu hv hd hcop hdL,degreeLT_evaluation_range]
  exact boundedEvaluation_rank x hx (L+d)

end
end FrobeniusLocator.Strata
end PackSource_PairRank

section PackSource_MatrixScaling
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Matrix Polynomial Finset
open scoped BigOperators
variable {F row col : Type} [Field F] [Fintype row] [Fintype col]

/-- Nonzero independent row and column scalings preserve rank. -/
theorem rank_scale (M : Matrix row col F) (a : row → F) (b : col → F)
    (ha : ∀ i, a i≠0) (hb : ∀ j, b j≠0) :
    (Matrix.of (fun i j => a i*M i j*b j)).rank=M.rank := by
  classical
  have heq : (Matrix.of (fun i j => a i*M i j*b j))=
      Matrix.diagonal a*M*Matrix.diagonal b := by
    ext i j
    simp only [Matrix.of_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]
  rw [heq,Matrix.rank_mul_eq_left_of_det_ne_zero _ _
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))]

end
end FrobeniusLocator.Strata
end PackSource_MatrixScaling

section PackSource_ErrorRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- Error blocks with the dual nonzero column weights removed. -/
def errorTwoMatrix (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Matrix (Fin 2 × Fin L) ι F := fun b i => ![e i,σ (e i)] b.1*x i^b.2.val

def errorThreeMatrix (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Matrix (Fin 3 × Fin L) ι F := fun b i => ![e i,σ (e i),σ (σ (e i))] b.1*x i^b.2.val

/-- First and second Frobenius ratios on nodes with nonzero denominator. -/
theorem error_ratios (σ : F →+* F) (u v e : F) (hv : v≠0)
    (hrel : u*e+v*σ e=0) :
    σ e=-(u/v)*e ∧ σ (σ e)=(u*σ u/(v*σ v))*e := by
  have hs : σ e=-(u/v)*e := by
    calc
      σ e=(-u*e)/v := (eq_div_iff hv).mpr (by linear_combination hrel)
      _ = _ := by ring
  refine ⟨hs,?_⟩
  calc
    σ (σ e)=σ (-(u/v)*e) := congrArg σ hs
    _ = _ := by rw [map_mul,map_neg,map_div₀,hs]; field_simp

theorem eval_ne_zero_of_dvd {A B : F[X]} (hAB : A∣B) (x : F) (hB : B.eval x≠0) :
    A.eval x≠0 := by
  obtain ⟨Q,hQ⟩ := hAB
  rw [hQ,eval_mul] at hB
  exact (mul_ne_zero_iff.mp hB).1

/-- With no common coefficient zeros, the two-block rank is exactly the
ordinary Vandermonde rank L+d. -/
theorem error_two_rank_no_common (σ : F →+* F) (x e : ι → F)
    (hx : Function.Injective x) (u v : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) (he : ∀ i, e i≠0)
    (hvx : ∀ i, v.eval (x i)≠0)
    (hrel : ∀ i, u.eval (x i)*e i+v.eval (x i)*σ (e i)=0) :
    (errorTwoMatrix σ x e L).rank=min (Fintype.card ι) (L+d) := by
  classical
  let N := numeratorMatrix x (pairNumerators u v) L
  let a : Fin 2 × Fin L → F := fun b => if b.1=1 then -1 else 1
  let b : ι → F := fun i => e i/v.eval (x i)
  have hb : ∀ i, b i≠0 := fun i => div_ne_zero (he i) (hvx i)
  have ha : ∀ j, a j≠0 := by intro j; dsimp [a]; split_ifs <;> simp
  have heq : errorTwoMatrix σ x e L=Matrix.of (fun j i => a j*N j i*b i) := by
    ext ⟨j,l⟩ i
    have hs := (error_ratios σ (u.eval (x i)) (v.eval (x i)) (e i) (hvx i) (hrel i)).1
    fin_cases j
    · simp [errorTwoMatrix,a,b,N,numeratorMatrix,pairNumerators]
      field_simp [hvx i]
    · simp [errorTwoMatrix,a,b,N,numeratorMatrix,pairNumerators,hs]
      field_simp [hvx i]
  rw [heq,rank_scale N a b ha hb]
  exact pair_numerator_rank x hx u v d L hu hv hd hcop hdL

/-- The full three-block error-rank theorem off common coefficient roots.
The sign in the middle block is explicitly absorbed by invertible scaling. -/
theorem error_three_rank_no_common (σ : F →+* F) (x e : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (u v : F[X]) (d L : ℕ)
    (hu : u≠0) (hv : v≠0) (hd : max u.natDegree v.natDegree=d)
    (hcop : IsCoprime u v) (hdL : d≤L) (he : ∀ i, e i≠0)
    (hux : ∀ i, u.eval (x i)≠0) (hvx : ∀ i, v.eval (x i)≠0)
    (hrel : ∀ i, u.eval (x i)*e i+v.eval (x i)*σ (e i)=0) :
    (errorThreeMatrix σ x e L).rank=
      min (Fintype.card ι) (L+2*d-(GCDMonoid.gcd u (v.map σ)).natDegree) := by
  classical
  let N := numeratorMatrix x (tripleNumerators σ u v) L
  let a : Fin 3 × Fin L → F := fun b => if b.1=1 then -1 else 1
  let b : ι → F := fun i => e i/(v.eval (x i)*σ (v.eval (x i)))
  have hvσ : ∀ i, σ (v.eval (x i))≠0 := fun i => (_root_.map_ne_zero σ).mpr (hvx i)
  have hb : ∀ i, b i≠0 := fun i => div_ne_zero (he i) (mul_ne_zero (hvx i) (hvσ i))
  have ha : ∀ j, a j≠0 := by intro j; dsimp [a]; split_ifs <;> simp
  have heq : errorThreeMatrix σ x e L=Matrix.of (fun j i => a j*N j i*b i) := by
    ext ⟨j,l⟩ i
    obtain ⟨hs,ht⟩ := error_ratios σ (u.eval (x i)) (v.eval (x i)) (e i) (hvx i) (hrel i)
    fin_cases j
    · simp [errorThreeMatrix,a,b,N,numeratorMatrix,tripleNumerators,
        eval_coefficient_map σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
    · simp [errorThreeMatrix,a,b,N,numeratorMatrix,tripleNumerators,hs,
        eval_coefficient_map σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
      <;> ring
    · simp [errorThreeMatrix,a,b,N,numeratorMatrix,tripleNumerators,ht,
        eval_coefficient_map σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
      <;> ring
  rw [heq,rank_scale N a b ha hb]
  apply triple_numerator_rank σ x hx u v d L hu hv hd hcop hdL
  intro i
  exact eval_ne_zero_of_dvd (gcd_dvd_left u (v.map σ)) (x i) (hux i)

end
end FrobeniusLocator.Strata
end PackSource_ErrorRank

section PackSource_RankSaturation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V]

/-- Rank-nullity for a subspace and an ambient projection. -/
theorem subspace_map_add_inf (f : V →ₗ[F] W) (S : Submodule F V) :
    Module.finrank F (S.map f)+Module.finrank F (S ⊓ LinearMap.ker f : Submodule F V)=Module.finrank F S := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  rw [LinearMap.range_domRestrict,LinearMap.ker_domRestrict] at h
  have hk := Submodule.finrank_map_subtype_eq S ((LinearMap.ker f).comap S.subtype)
  rw [Submodule.map_comap_subtype] at hk
  rw [← hk] at h
  exact h

theorem subspace_projection_bound (f : V →ₗ[F] W) (S : Submodule F V) :
    Module.finrank F S≤Module.finrank F (S.map f)+Module.finrank F (LinearMap.ker f) := by
  have h := subspace_map_add_inf f S
  have hi := Submodule.finrank_mono (show S ⊓ LinearMap.ker f≤LinearMap.ker f from inf_le_right)
  omega

/-- Saturating the maximum projection loss forces the entire missing
coordinate space into the original row span. -/
theorem projection_kernel_le_of_saturation (f : V →ₗ[F] W) (S : Submodule F V)
    (hsat : Module.finrank F S=Module.finrank F (S.map f)+Module.finrank F (LinearMap.ker f)) :
    LinearMap.ker f≤S := by
  have h := subspace_map_add_inf f S
  have heq : S ⊓ LinearMap.ker f=LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  rw [← heq]
  exact inf_le_left

/-- Once a smaller row space saturates, the same missing coordinates
contribute their full dimension to every larger row space. -/
theorem saturation_lifts (f : V →ₗ[F] W) (S T : Submodule F V) (hST : S≤T)
    (hsat : Module.finrank F S=Module.finrank F (S.map f)+Module.finrank F (LinearMap.ker f)) :
    Module.finrank F T=Module.finrank F (T.map f)+Module.finrank F (LinearMap.ker f) := by
  have hker : LinearMap.ker f≤T := (projection_kernel_le_of_saturation f S hsat).trans hST
  have h := subspace_map_add_inf f T
  rw [inf_eq_right.mpr hker] at h
  exact h.symm

section Coordinates
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def forgetCoordinates (C : Finset ι) : (ι → F) →ₗ[F] ({i // i∉C} → F) where
  toFun v i := v i.val
  map_add' v w := rfl
  map_smul' c v := rfl

theorem forgetCoordinates_surjective (C : Finset ι) : Function.Surjective (forgetCoordinates (F := F) C) := by
  intro w
  refine ⟨fun i => if h : i∉C then w ⟨i,h⟩ else 0,?_⟩
  funext i
  simp [forgetCoordinates,i.property]

theorem forgetCoordinates_nullity (C : Finset ι) :
    Module.finrank F (LinearMap.ker (forgetCoordinates (F := F) C))=C.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (forgetCoordinates (F := F) C)
  rw [LinearMap.range_eq_top.mpr (forgetCoordinates_surjective C),finrank_top,
    Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype_compl, Fintype.card_coe] at h
  have hc := Finset.card_le_univ C
  omega

/-- Restriction to the complement is exactly the map of row spaces. -/
theorem rowspace_forget {row : Type} (M : Matrix row ι F) (C : Finset ι) :
    (Submodule.span F (Set.range M.row)).map (forgetCoordinates C)=
      Submodule.span F (Set.range (M.submatrix id Subtype.val).row) := by
  rw [Submodule.map_span,← Set.range_comp]
  rfl

end Coordinates

end
end FrobeniusLocator.Strata
end PackSource_RankSaturation

section PackSource_RootSaturation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

theorem root_nodes_card_le (x : ι → F) (hx : Function.Injective x) (P : F[X]) (hP : P≠0)
    (S : Finset ι) (hS : ∀ i∈S, P.eval (x i)=0) : S.card≤P.natDegree := by
  have h : (S.image x).card≤P.natDegree := Polynomial.card_le_degree_of_subset_roots
    (fun a ha => (Polynomial.mem_roots hP).mpr (by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hS i hi))
  simpa only [Finset.card_image_of_injective S hx] using h

/-- A saturated normal error matrix forces BOTH relation coefficients
nonzero, not merely a jointly nonzero pair. -/
theorem saturated_coefficients_nonzero (σ : F →+* F) (x e : ι → F)
    (hx : Function.Injective x) (U V : F[X]) (h L : ℕ)
    (hU : U.natDegree≤h) (hV : V.natDegree≤h) (hpair : U≠0 ∨ V≠0)
    (hsmall : h<L) (he : ∀ i, e i≠0)
    (hrel : ∀ i, U.eval (x i)*e i+V.eval (x i)*σ (e i)=0)
    (hrank : (errorTwoMatrix σ x e L).rank=L+h) : U≠0 ∧ V≠0 := by
  have hn : L+h≤Fintype.card ι := by
    simpa only [hrank] using Matrix.rank_le_card_width (errorTwoMatrix σ x e L)
  constructor
  · intro hzero
    have hv := hpair.resolve_left (by simpa using hzero)
    have hz : ∀ i∈(Finset.univ : Finset ι), V.eval (x i)=0 := by
      intro i _
      have hh := hrel i
      rw [hzero,eval_zero,zero_mul,zero_add] at hh
      exact (mul_eq_zero.mp hh).resolve_right ((_root_.map_ne_zero σ).mpr (he i))
    have hc := root_nodes_card_le x hx V hv Finset.univ hz
    rw [Finset.card_univ] at hc
    omega
  · intro hzero
    have hu := hpair.resolve_right (by simpa using hzero)
    have hz : ∀ i∈(Finset.univ : Finset ι), U.eval (x i)=0 := by
      intro i _
      have hh := hrel i
      rw [hzero,eval_zero,zero_mul,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right (he i)
    have hc := root_nodes_card_le x hx U hu Finset.univ hz
    rw [Finset.card_univ] at hc
    omega

/-- Coprimality and a nonzero error force both reduced coefficients to
be units at that node. -/
theorem coprime_relation_units (σ : F →+* F) (u v : F[X]) (a e : F)
    (hcop : IsCoprime u v) (he : e≠0)
    (hrel : u.eval a*e+v.eval a*σ e=0) : u.eval a≠0 ∧ v.eval a≠0 := by
  have hne := (hcop.map (Polynomial.evalRingHom a)).ne_zero_or_ne_zero
  constructor
  · intro hu
    have hv := hne.resolve_left (by simpa using hu)
    rw [hu,zero_mul,zero_add] at hrel
    exact (mul_ne_zero hv ((_root_.map_ne_zero σ).mpr he)) hrel
  · intro hv
    have hu := hne.resolve_right (by simpa using hv)
    rw [hv,zero_mul,add_zero] at hrel
    exact (mul_ne_zero hu he) hrel

/-- The two error blocks occur among the three error blocks. -/
theorem error_rowspace_le (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Submodule.span F (Set.range (errorTwoMatrix σ x e L).row)≤
      Submodule.span F (Set.range (errorThreeMatrix σ x e L).row) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨b,j⟩,rfl⟩
  apply Submodule.subset_span
  refine ⟨(Fin.castLE (by decide : 2≤3) b,j),?_⟩
  funext i
  fin_cases b <;> simp [errorTwoMatrix,errorThreeMatrix,Matrix.row]

/-- Common-root saturation and the exact third Frobenius rank. This is
R3 for ACTUAL error columns, with all common-zero contributions proved. -/
theorem normal_error_three_rank (σ : F →+* F) (x e : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (U V : F[X]) (h L : ℕ) (hU : U.natDegree≤h) (hV : V.natDegree≤h)
    (hpair : U≠0 ∨ V≠0) (hsmall : h<L) (he : ∀ i, e i≠0)
    (hrel : ∀ i, U.eval (x i)*e i+V.eval (x i)*σ (e i)=0)
    (hrank : (errorTwoMatrix σ x e L).rank=L+h) :
    let G := GCDMonoid.gcd U V
    let u := U/G
    let v := V/G
    let d := max u.natDegree v.natDegree
    let j := (GCDMonoid.gcd u (v.map σ)).natDegree
    (Finset.univ.filter (fun i => G.eval (x i)=0)).card=G.natDegree ∧
      d+G.natDegree=h ∧
      (errorThreeMatrix σ x e L).rank=min (Fintype.card ι) (L+h+(d-j)) := by
  obtain ⟨hU0,hV0⟩ := saturated_coefficients_nonzero σ x e hx U V h L hU hV hpair hsmall he hrel hrank
  let G := GCDMonoid.gcd U V
  let u := U/G
  let v := V/G
  let g := G.natDegree
  let d := max u.natDegree v.natDegree
  let j := (GCDMonoid.gcd u (v.map σ)).natDegree
  let C : Finset ι := Finset.univ.filter (fun i => G.eval (x i)=0)
  let D := {i // i∉C}
  have hG : G≠0 := gcd_ne_zero_of_right hV0
  have hu : u≠0 := left_div_gcd_ne_zero hU0
  have hv : v≠0 := right_div_gcd_ne_zero hV0
  have hcop : IsCoprime u v := isCoprime_div_gcd_div_gcd hV0
  have hGu : G*u=U := EuclideanDomain.mul_div_cancel' hG (gcd_dvd_left U V)
  have hGv : G*v=V := EuclideanDomain.mul_div_cancel' hG (gcd_dvd_right U V)
  have hdg : d+g≤h := by
    have hd := (gcd_reduction_degrees U V hU0 hV0).2
    have hg := (gcd_reduction_degrees U V hU0 hV0).1
    change d=max U.natDegree V.natDegree-g at hd
    change g≤max U.natDegree V.natDegree at hg
    omega
  have hc : C.card≤g := root_nodes_card_le x hx G hG C (by intro i hi; exact (Finset.mem_filter.mp hi).2)
  have hDn : Fintype.card D=Fintype.card ι-C.card := by
    simp only [D,Fintype.card_subtype_compl,Fintype.card_coe]
  have hnormal : L+h≤Fintype.card ι := by
    simpa only [hrank] using Matrix.rank_le_card_width (errorTwoMatrix σ x e L)
  have hdL : d≤L := by omega
  have hGD : ∀ i : D, G.eval (x i.val)≠0 := by
    intro i hz
    exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
  have hrelD : ∀ i : D, u.eval (x i.val)*e i.val+v.eval (x i.val)*σ (e i.val)=0 := by
    intro i
    apply (mul_eq_zero.mp (show G.eval (x i.val)*
      (u.eval (x i.val)*e i.val+v.eval (x i.val)*σ (e i.val))=0 from ?_)).resolve_left (hGD i)
    have hh := hrel i.val
    rw [← hGu,← hGv,eval_mul,eval_mul] at hh
    linear_combination hh
  have hunitD : ∀ i : D, u.eval (x i.val)≠0 ∧ v.eval (x i.val)≠0 :=
    fun i => coprime_relation_units σ u v (x i.val) (e i.val) hcop (he i.val) (hrelD i)
  have hdimD : L+d≤Fintype.card D := by omega
  have hr2D : ((errorTwoMatrix σ x e L).submatrix id (Subtype.val : D → ι)).rank=L+d := by
    have hh := error_two_rank_no_common σ (fun i : D => x i.val) (fun i : D => e i.val)
      (hx.comp Subtype.val_injective) u v d L hu hv rfl hcop hdL
      (fun i => he i.val) (fun i => (hunitD i).2) hrelD
    have heqD : (errorTwoMatrix σ x e L).submatrix id (Subtype.val : D → ι) =
        errorTwoMatrix σ (fun i : D => x i.val) (fun i : D => e i.val) L := by
      ext b i
      rfl
    rw [heqD]
    exact hh.trans (min_eq_right hdimD)
  let S := Submodule.span F (Set.range (errorTwoMatrix σ x e L).row)
  let T := Submodule.span F (Set.range (errorThreeMatrix σ x e L).row)
  let π := forgetCoordinates (F := F) C
  have hS : Module.finrank F S=L+h := by rw [← Matrix.rank_eq_finrank_span_row]; exact hrank
  have hSP : Module.finrank F (S.map π)=L+d := by
    change Module.finrank F ((Submodule.span F (Set.range (errorTwoMatrix σ x e L).row)).map (forgetCoordinates C))=_
    rw [rowspace_forget,← Matrix.rank_eq_finrank_span_row]
    exact hr2D
  have hπ : Module.finrank F (LinearMap.ker π)=C.card := forgetCoordinates_nullity C
  have hproj := subspace_projection_bound π S
  rw [hS,hSP,hπ] at hproj
  have hsat : d+C.card=h := by omega
  have hcg : C.card=g := by omega
  have hsum : d+g=h := by omega
  have hT := saturation_lifts π S T (error_rowspace_le σ x e L)
    (by rw [hS,hSP,hπ]; omega)
  have hj : j≤d := by
    have hj' := (gcd_reduction_degrees u (v.map σ) hu (by simpa using hv)).1
    have hm : (v.map σ).natDegree=v.natDegree := natDegree_map_eq_of_injective σ.injective v
    simpa only [hm] using hj'
  have hr3D : ((errorThreeMatrix σ x e L).submatrix id (Subtype.val : D → ι)).rank=
      min (Fintype.card D) (L+2*d-j) :=
    error_three_rank_no_common σ (fun i : D => x i.val) (fun i : D => e i.val)
      (hx.comp Subtype.val_injective) (fun i => hfixed i.val) u v d L hu hv rfl hcop hdL
      (fun i => he i.val) (fun i => (hunitD i).1) (fun i => (hunitD i).2) hrelD
  have hTP : Module.finrank F (T.map π)=min (Fintype.card D) (L+2*d-j) := by
    change Module.finrank F ((Submodule.span F (Set.range (errorThreeMatrix σ x e L).row)).map (forgetCoordinates C))=_
    rw [rowspace_forget,← Matrix.rank_eq_finrank_span_row]
    exact hr3D
  rw [hTP,hπ,← Matrix.rank_eq_finrank_span_row] at hT
  change C.card=g ∧ d+g=h ∧
    (errorThreeMatrix σ x e L).rank=min (Fintype.card ι) (L+h+(d-j))
  refine ⟨hcg,hsum,?_⟩
  omega

end
end FrobeniusLocator.Strata
end PackSource_RootSaturation

section PackSource_RelationExtraction
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Multiplication of a word by a bounded polynomial is contraction of
its syndrome sequence. All coefficients and indices are literal. -/
theorem syndrome_polynomial_multiple (x w : ι → F) (U : F[X]) (H j : ℕ)
    (hU : U.natDegree≤H) :
    syndrome x (fun i => U.eval (x i)*w i) j =
      ∑ l : Fin (H+1), U.coeff l.val*syndrome x w (l.val+j) := by
  simp only [syndrome,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_coeff_eval U H hU (x i)]
  simp only [Finset.sum_mul,Finset.mul_sum,pow_add]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Every vector in the ACTUAL complementary Hankel kernel supplies the
polynomial twisted relation, via completeness of the RS dual checks. -/
theorem relation_of_kernel (σ : F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (k m H : ℕ) (hkm : k+m=Fintype.card ι)
    (hH : H≤m) (a : Fin 2 × Fin (H+1) → F)
    (ha : (relationMatrix (fun b j => syndrome x
      (if b=0 then w else fun i => σ (w i)) j) m H).mulVec a=0) :
    ∃ R : F[X], TwistedRelation σ x w k H
      (Principal.assemble (fun i => a (0,i)))
      (Principal.assemble (fun i => a (1,i))) R := by
  let U := Principal.assemble (fun i => a (0,i))
  let V := Principal.assemble (fun i => a (1,i))
  let z := fun i => U.eval (x i)*w i+V.eval (x i)*σ (w i)
  have hU := Principal.assemble_natDegree_le (fun i => a (0,i))
  have hV := Principal.assemble_natDegree_le (fun i => a (1,i))
  have hzero : ∀ j<Fintype.card ι-(k+H), syndrome x z j=0 := by
    intro j hj
    have hj' : j<m-H := by omega
    have he := (relation_equations _ m H a).mp ha ⟨j,hj'⟩
    rw [Fin.sum_univ_two] at he
    simp only [Fin.isValue,ite_true,ite_false,zero_ne_one,one_ne_zero] at he
    have hs : syndrome x z j =
        (∑ l : Fin (H+1), a (0,l)*syndrome x w (l.val+j))+
        ∑ l : Fin (H+1), a (1,l)*syndrome x (fun i => σ (w i)) (l.val+j) := by
      change syndrome x (fun i => U.eval (x i)*w i+V.eval (x i)*σ (w i)) j = _
      have hlin := Principal.syndrome_linear x
        (fun i => U.eval (x i)*w i) (fun i => V.eval (x i)*σ (w i)) 1 1 j
      simp only [one_mul] at hlin
      rw [hlin,syndrome_polynomial_multiple x w U H j hU,
        syndrome_polynomial_multiple x (fun i => σ (w i)) V H j hV]
      simp only [U,V,Principal.assemble_coeff]
    exact hs.trans he
  obtain ⟨R,hR,hRv⟩ := Principal.extendsOn_of_syndrome_zero x hx z (k+H) (by omega) hzero
  refine ⟨R,hU,hV,hR,?_⟩
  intro i
  exact (hRv i (Finset.mem_univ i)).symm

/-- A nonzero relation coefficient vector gives a nonzero polynomial
pair. This is the finite-specialization nonvanishing condition. -/
theorem assembled_pair_ne_zero (H : ℕ) (a : Fin 2 × Fin (H+1) → F) (ha : a≠0) :
    Principal.assemble (fun i => a (0,i))≠0 ∨
      Principal.assemble (fun i => a (1,i))≠0 := by
  by_contra h
  push Not at h
  have hcoeff (b : Fin 2) (hb : Principal.assemble (fun i => a (b,i))=0)
      (i : Fin (H+1)) : a (b,i)=0 := by
    have he := congrArg (fun P : F[X] => P.coeff i.val) hb
    simpa only [Principal.assemble_coeff,coeff_zero] using he
  apply ha
  funext z
  rcases z with ⟨b,i⟩
  have hb : b=0 ∨ b=1 := by omega
  rcases hb with rfl | rfl
  · exact hcoeff 0 h.1 i
  · exact hcoeff 1 h.2 i

end
end FrobeniusLocator.Strata
end PackSource_RelationExtraction

section PackSource_TwistedSection
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- The actual polynomial-in-slope relation matrix. -/
def parameterRelation (p : ℕ) (x u v : ι → F) (m H : ℕ) :
    Matrix (Fin (m-H)) (Fin 2 × Fin (H+1)) F[X] :=
  fun j b => Principal.parameterSyndromes p x u v b.1 (b.2.val+j.val)

theorem parameterRelation_map (φ : F[X] →+* GenericLayer.GenericField F)
    (p : ℕ) (x u v : ι → F) (m H : ℕ) :
    (parameterRelation p x u v m H).map φ =
      relationMatrix (fun b j => φ (Principal.parameterSyndromes p x u v b j)) m H := rfl

theorem parameterSyndromes_eval (p : ℕ) [ExpChar F p]
    (x u v : ι → F) (hfixed : ∀ i, x i^p=x i) (γ : F) (b : Fin 2) (j : ℕ) :
    (Principal.parameterSyndromes p x u v b j).eval γ =
      syndrome x (if b=0 then fun i => u i+γ*v i else fun i => (u i+γ*v i)^p) j := by
  have hs : syndrome x (fun i => u i+γ*v i) j=syndrome x u j+γ*syndrome x v j := by
    simpa only [one_mul] using Principal.syndrome_linear x u v 1 γ j
  by_cases hb : b=0
  · simpa only [Principal.parameterSyndromes,hb,ite_true,eval_add,eval_mul,eval_C,eval_X] using hs.symm
  · simp only [Principal.parameterSyndromes,hb,ite_false,
      eval_add,eval_mul,eval_C,eval_pow,eval_X]
    rw [syndrome_frobenius p x hfixed,hs]
    exact (map_add (frobenius F p) _ _).trans (by rw [map_mul]; rfl) |>.symm

/-- A primitive polynomial section of a one-dimensional generic relation
kernel. No finite slope makes all relation coefficients vanish. -/
theorem primitive_relation_section (p : ℕ) [ExpChar F p] (hp : 1≤p)
    (x u v : ι → F) (m H : ℕ)
    (hnull : GenericLayer.genericNullity (parameterRelation p x u v m H)=1) :
    ∃ Q : Fin 2 × Fin (H+1) → F[X], PrimitiveVector.IsPrimitive Q ∧
      (parameterRelation p x u v m H).mulVec Q=0 ∧
      (∀ b, (Q b).natDegree≤(2*H+1)*p) ∧
      ∀ γ : F, (fun b => (Q b).eval γ)≠0 := by
  let N := parameterRelation p x u v m H
  have hr : GenericLayer.genericRank N=2*H+1 := by
    have h := GenericLayer.rank_add_nullity N
    rw [hnull,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin] at h
    omega
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis
    (algebraMap F[X] (GenericLayer.GenericField F)) N (2*H+1) hr
  have hdeg : ∀ j b, (N j b).natDegree≤p := by
    intro j b
    have hh := stacked_entry_natDegree p x u v (m-H) H (b.1,j) b.2
    have hh' : (N j b).natDegree ≤ (if b.1=0 then 1 else p) := by
      simpa only [N,parameterRelation,Principal.parameterSyndromes,stacked,hankel,Nat.add_comm] using hh
    exact hh'.trans (by split_ifs <;> omega)
  obtain ⟨Q,hprim,hQ,hdegQ,_⟩ := GenericCofactor.exists_primitive_line B
    (IsFractionRing.injective F[X] (GenericLayer.GenericField F))
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega) (fun _ => p) hdeg
  refine ⟨Q,hprim,hQ,?_,?_⟩
  · intro b
    simpa using hdegQ b
  · intro γ
    exact PrimitiveVector.eval_ne_zero Q hprim γ

/-- Literal Lemma-T specialization from a generic relation line: a
nonzero specialized coefficient pair and an RS[k+H] output at EVERY
finite slope. The generic nullity-one premise is explicit. -/
theorem twisted_relation_at_every_slope (p : ℕ) [ExpChar F p] (hp : 1≤p)
    (x u v : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (k m H : ℕ) (hkm : k+m=Fintype.card ι) (hH : H≤m)
    (hnull : GenericLayer.genericNullity (parameterRelation p x u v m H)=1) :
    ∃ Q : Fin 2 × Fin (H+1) → F[X], PrimitiveVector.IsPrimitive Q ∧
      (parameterRelation p x u v m H).mulVec Q=0 ∧
      (∀ b, (Q b).natDegree≤(2*H+1)*p) ∧
      ∀ γ : F, ∃ R : F[X],
        (Principal.assemble (fun i => (Q (0,i)).eval γ)≠0 ∨
          Principal.assemble (fun i => (Q (1,i)).eval γ)≠0) ∧
        TwistedRelation (frobenius F p) x (fun i => u i+γ*v i) k H
          (Principal.assemble (fun i => (Q (0,i)).eval γ))
          (Principal.assemble (fun i => (Q (1,i)).eval γ)) R := by
  obtain ⟨Q,hprim,hQ,hdeg,hne⟩ := primitive_relation_section p hp x u v m H hnull
  refine ⟨Q,hprim,hQ,hdeg,?_⟩
  intro γ
  let a := fun b => (Q b).eval γ
  have hk : (relationMatrix (fun b j => syndrome x
      (if b=0 then fun i => u i+γ*v i else fun i => (u i+γ*v i)^p) j) m H).mulVec a=0 := by
    funext j
    have he := congrArg (Polynomial.evalRingHom γ) (congrFun hQ j)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,parameterRelation,
      Polynomial.coe_evalRingHom,parameterSyndromes_eval p x u v hfixed γ,
      relationMatrix,hankelWindow,Matrix.transpose_apply,a,Pi.zero_apply] using he
  obtain ⟨R,hR⟩ := relation_of_kernel (frobenius F p) x (fun i => u i+γ*v i)
    hx k m H hkm hH a hk
  exact ⟨R,assembled_pair_ne_zero H a (hne γ),hR⟩

end
end FrobeniusLocator.Strata
end PackSource_TwistedSection

section PackSource_LocatorFactorization
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]

theorem weight_ne_zero (x : ι → F) (hx : Function.Injective x) (i : ι) : weight x i≠0 := by
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hx hij).symm

theorem weight_map (σ : F →+* F) (x : ι → F) (hfixed : ∀ i, σ (x i)=x i) (i : ι) :
    σ (weight x i)=weight x i := by
  simp only [weight,map_inv₀,map_prod,map_sub,hfixed]

/-- Codewords have zero syndrome throughout the exact dual range. -/
theorem syndrome_eval_zero (x : ι → F) (hx : Function.Injective x) (P : F[X])
    (k j : ℕ) (hP : P.degree<k) (hj : k+j<Fintype.card ι) :
    syndrome x (fun i => P.eval (x i)) j=0 := by
  by_cases hp : P=0
  · simp [syndrome,hp]
  have hpn := (natDegree_lt_iff_degree_lt hp).mpr hP
  have hdeg : (P*(Polynomial.X : F[X])^j).degree<(Fintype.card ι-1 : ℕ) := by
    apply degree_le_natDegree.trans_lt
    have hd := natDegree_mul_le (p := P) (q := ((Polynomial.X : F[X])^j))
    simp only [natDegree_X_pow] at hd
    exact_mod_cast (show (P*(Polynomial.X : F[X])^j).natDegree<Fintype.card ι-1 by omega)
  simpa only [syndrome,eval_mul,eval_pow,eval_X,mul_assoc] using weighted_eval_sum_zero x hx (P*(Polynomial.X : F[X])^j) hdeg

theorem syndrome_sub_decoder (x w : ι → F) (hx : Function.Injective x) (P : F[X])
    (k j : ℕ) (hP : P.degree<k) (hj : k+j<Fintype.card ι) :
    syndrome x w j=syndrome x (fun i => w i-P.eval (x i)) j := by
  have hz := syndrome_eval_zero x hx P k j hP hj
  have hl := Principal.syndrome_linear x w (fun i => P.eval (x i)) 1 (-1) j
  simpa only [one_mul,neg_one_mul,sub_eq_add_neg,hz,neg_zero,add_zero] using hl.symm

/-- Arbitrarily many coefficient-conjugate Hankel blocks. -/
def conjugateHankel (σ : β → F →+* F) (x w : ι → F) (L t : ℕ) :
    Matrix (β × Fin L) (Fin (t+1)) F :=
  fun b j => σ b.1 (syndrome x w (b.2.val+j.val))

def conjugateErrors (σ : β → F →+* F) (x e : ι → F) (L : ℕ) : Matrix (β × Fin L) ι F :=
  fun b i => σ b.1 (e i)*x i^b.2.val

def nodeVandermonde (x : ι → F) (t : ℕ) : Matrix ι (Fin (t+1)) F := fun i j => x i^j.val

theorem nodeVandermonde_surjective (x : ι → F) (hx : Function.Injective x)
    (t : ℕ) (hcard : Fintype.card ι≤t+1) : Function.Surjective (nodeVandermonde x t).mulVecLin := by
  intro w
  obtain ⟨P,hPw⟩ := boundedEvaluation_surjective x hx (t+1) hcard w
  refine ⟨fun j => (P : F[X]).coeff j.val,?_⟩
  funext i
  change (∑ j : Fin (t+1), x i^j.val*(P : F[X]).coeff j.val)=w i
  rw [show (∑ j : Fin (t+1), x i^j.val*(P : F[X]).coeff j.val)=
      ∑ j : Fin (t+1), (P : F[X]).coeff j.val*x i^j.val by apply Finset.sum_congr rfl; intro j _; ring]
  rw [sum_coeff_eval _ t (Principal.degreeLT_natDegree_le P)]
  exact congrFun hPw i

theorem rank_mul_of_surjective {row mid col : Type} [Fintype row] [Fintype mid] [Fintype col]
    (A : Matrix row mid F) (B : Matrix mid col F) (hB : Function.Surjective B.mulVecLin) :
    (A*B).rank=A.rank := by
  rw [Matrix.rank,Matrix.rank,Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hB)]

/-- Literal factorization through the ACTUAL error set; a padded witness
set is never identified with it. The error values may be zero inside S. -/
theorem conjugateHankel_factorization (σ : β → F →+* F)
    (x w : ι → F) (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (P : F[X]) (k L t : ℕ) (hP : P.degree<k) (hsize : k+L+t≤Fintype.card ι)
    (S : Finset ι) (hagree : ∀ i, i∉S → w i=P.eval (x i)) :
    conjugateHankel σ x w L t=
      Matrix.of (fun b (i : S) => weight x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)*
        nodeVandermonde (fun i : S => x i.val) t := by
  ext b j
  change σ b.1 (syndrome x w (b.2.val+j.val))=∑ i : S,
    (weight x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)*x i.val^j.val
  rw [syndrome_sub_decoder x w hx P k _ hP (by have := b.2.isLt; have := j.isLt; omega)]
  simp only [syndrome,map_sum,map_mul,map_pow,weight_map _ x (hfixed b.1),hfixed]
  rw [Finset.sum_coe_sort S (fun i =>
    weight x i*σ b.1 (w i-P.eval (x i))*x i^b.2.val*x i^j.val)]
  have hs : (∑ i : ι, weight x i*σ b.1 (w i-P.eval (x i))*x i^(b.2.val+j.val))=
      ∑ i∈S, weight x i*σ b.1 (w i-P.eval (x i))*x i^(b.2.val+j.val) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [hagree i hi]
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

/-- Exact rank equality after stripping the Vandermonde and dual weights. -/
theorem conjugateHankel_error_rank (σ : β → F →+* F)
    (x w : ι → F) (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (P : F[X]) (k L t : ℕ) (hP : P.degree<k) (hsize : k+L+t≤Fintype.card ι)
    (S : Finset ι) (hS : S.card≤t+1) (hagree : ∀ i, i∉S → w i=P.eval (x i)) :
    (conjugateHankel σ x w L t).rank=
      (conjugateErrors σ (fun i : S => x i.val) (fun i : S => w i.val-P.eval (x i.val)) L).rank := by
  rw [conjugateHankel_factorization σ x w hx hfixed P k L t hP hsize S hagree]
  have hB : Function.Surjective (nodeVandermonde (fun i : S => x i.val) t).mulVecLin :=
    nodeVandermonde_surjective (fun i : S => x i.val)
      (fun i j hij => Subtype.ext (hx hij)) t (by simpa only [Fintype.card_coe] using hS)
  rw [rank_mul_of_surjective _ _ hB]
  let N := conjugateErrors σ (fun i : S => x i.val) (fun i : S => w i.val-P.eval (x i.val)) L
  have heq : Matrix.of (fun b (i : S) => weight x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)=
      Matrix.of (fun b (i : S) => (1:F)*N b i*weight x i.val) := by
    ext b i
    simp only [N,conjugateErrors,Matrix.of_apply,one_mul]
    ring
  rw [heq,rank_scale N (fun _ => 1) (fun i => weight x i.val) (by simp)
    (fun i => weight_ne_zero x hx i.val)]

end
end FrobeniusLocator.Strata
end PackSource_LocatorFactorization

section PackSource_KernelTwoGcd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F]

/-- Common truncated apolar kernel for ANY family of syndrome functionals. -/
def recurrenceSpace (s : β → ℕ → F) (m t : ℕ) : Submodule F F[X] :=
  Polynomial.degreeLT F (t+1) ⊓ ⨅ b, ⨅ j : Fin (m-t),
    LinearMap.ker (Principal.recurrenceEval (s b) j.val)

theorem mem_recurrenceSpace (s : β → ℕ → F) (m t : ℕ) (P : F[X]) :
    P∈recurrenceSpace s m t ↔ P.degree<(t+1 : ℕ) ∧
      ∀ b j, j<m-t → Principal.recurrenceEval (s b) j P=0 := by
  simp only [recurrenceSpace,Submodule.mem_inf,Polynomial.mem_degreeLT,Submodule.mem_iInf,
    LinearMap.mem_ker,Fin.forall_iff]

/-- A bounded multiplier uses only the listed shifted recurrence checks. -/
theorem recurrence_product_zero (s : ℕ → F) (f Q : F[X]) (j N : ℕ)
    (hQ : Q.degree<N) (hrec : ∀ l<N, Principal.recurrenceEval s (j+l) f=0) :
    Principal.recurrenceEval s j (f*Q)=0 := by
  by_cases hq : Q=0
  · simp [hq]
  have hn := (natDegree_lt_iff_degree_lt hq).mpr hQ
  conv_lhs => rw [Q.as_sum_range' N hn,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro l hl
  have hpoly : f*Polynomial.monomial l (Q.coeff l)=Q.coeff l • (f*(Polynomial.X : F[X])^l) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly,map_smul,Principal.recurrenceEval_shift,hrec l (Finset.mem_range.mp hl),smul_zero]

/-- Ordinary polynomial multiple spaces. A top-degree split locator in
our applications removes the possible common root at infinity. -/
def NonprincipalSpace (K : Submodule F F[X]) (t : ℕ) : Prop :=
  ¬ ∃ G : F[X], G≠0 ∧ G.natDegree≤t ∧
    K=(Polynomial.degreeLT F (t-G.natDegree+1)).map (polynomialMul G)

/-- Elementary dimension-two gcd bound. No level resolution is used:
if the gcd were larger, bounded Bezout would put it in the smaller apolar
kernel and force the whole two-generator space to be principal. -/
theorem nonprincipal_two_generator_gcd_bound (s : β → ℕ → F) (m t : ℕ)
    (htm : t≤m) (f g : F[X]) (hf : f≠0) (hg : g≠0)
    (hfd : f.natDegree=t) (hgd : g.natDegree≤t)
    (hspan : recurrenceSpace s m t=Submodule.span F ({f,g} : Set F[X]))
    (hnon : NonprincipalSpace (recurrenceSpace s m t) t) :
    (GCDMonoid.gcd f g).natDegree+m+1≤2*t := by
  let G := GCDMonoid.gcd f g
  let d := G.natDegree
  have hG : G≠0 := gcd_ne_zero_of_right hg
  have hd : d≤t := by
    have hh := (gcd_reduction_degrees f g hf hg).1
    simpa only [hfd,max_eq_left hgd] using hh
  have hfK : f∈recurrenceSpace s m t := by rw [hspan]; exact Submodule.subset_span (by simp)
  have hgK : g∈recurrenceSpace s m t := by rw [hspan]; exact Submodule.subset_span (by simp)
  have hfm := (mem_recurrenceSpace s m t f).mp hfK
  have hgm := (mem_recurrenceSpace s m t g).mp hgK
  change d+m+1≤2*t
  by_contra hbound
  have hlen : t-d≤m-t := by omega
  have hGsmall : ∀ b j, j<m-d → Principal.recurrenceEval (s b) j G=0 := by
    intro b j hj
    have hrep : ∃ A B : F[X], A.degree<m-t ∧ B.degree<m-t ∧
        G*(Polynomial.X : F[X])^j=f*A+g*B := by
      apply (gcd_span_iff f g _ (m-t) hf hg (by simpa only [hfd,max_eq_left hgd] using hlen)).mpr
      refine ⟨(Polynomial.X : F[X])^j,?_,rfl⟩
      have he : (m-t)+(max f.natDegree g.natDegree-G.natDegree)=m-d := by rw [hfd,max_eq_left hgd]; omega
      rw [he]
      exact (degree_X_pow_le j).trans_lt (by exact_mod_cast hj)
    obtain ⟨A,B,hA,hB,heq⟩ := hrep
    have hzA := recurrence_product_zero (s b) f A 0 (m-t) hA (by simpa using hfm.2 b)
    have hzB := recurrence_product_zero (s b) g B 0 (m-t) hB (by simpa using hgm.2 b)
    have hz : Principal.recurrenceEval (s b) 0 (G*(Polynomial.X : F[X])^j)=0 := by
      rw [heq,map_add,hzA,hzB,add_zero]
    simpa only [Principal.recurrenceEval_shift,zero_add] using hz
  apply hnon
  refine ⟨G,hG,hd,le_antisymm ?_ ?_⟩
  · rw [hspan]
    apply Submodule.span_le.mpr
    intro P hP
    have hPcase : P=f ∨ P=g := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hP
    rcases hPcase with hPf | hPg
    · subst P
      refine ⟨f/G,?_,(EuclideanDomain.mul_div_cancel' hG (gcd_dvd_left f g))⟩
      have hfn := natDegree_mul hG (left_div_gcd_ne_zero hf (q := g))
      rw [EuclideanDomain.mul_div_cancel' hG (gcd_dvd_left f g),hfd] at hfn
      change t=d+(f/G).natDegree at hfn
      exact Polynomial.mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast (show (f/G).natDegree<t-d+1 by omega)))
    · subst P
      refine ⟨g/G,?_,(EuclideanDomain.mul_div_cancel' hG (gcd_dvd_right f g))⟩
      have hgn := natDegree_mul hG (right_div_gcd_ne_zero hg (p := f))
      rw [EuclideanDomain.mul_div_cancel' hG (gcd_dvd_right f g)] at hgn
      change g.natDegree=d+(g/G).natDegree at hgn
      exact Polynomial.mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast (show (g/G).natDegree<t-d+1 by omega)))
  · rintro _ ⟨Q,hQ,rfl⟩
    apply (mem_recurrenceSpace s m t _).mpr
    refine ⟨?_,?_⟩
    · have hmul := degree_mul_lt_add G Q d (t-d+1) (by rfl) (Polynomial.mem_degreeLT.mp hQ)
      have hcast : ((t-d+1 : ℕ) : WithBot ℕ)+(d : WithBot ℕ)=((t+1 : ℕ) : WithBot ℕ) := by
        norm_cast
        omega
      rw [hcast] at hmul
      exact hmul
    · intro b j hj
      apply recurrence_product_zero (s b) G Q j (t-d+1) (Polynomial.mem_degreeLT.mp hQ)
      intro l hl
      exact hGsmall b (j+l) (by omega)

end
end FrobeniusLocator.Strata
end PackSource_KernelTwoGcd

section PackSource_KernelTwoSpace
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]

def recurrenceMatrixAll (s : β → ℕ → F) (m t : ℕ) :
    Matrix (β × Fin (m-t)) (Fin (t+1)) F := fun b j => s b.1 (j.val+b.2.val)

theorem recurrenceSpace_matrix (s : β → ℕ → F) (m t : ℕ) (P : F[X]) :
    P∈recurrenceSpace s m t ↔ P.natDegree≤t ∧
      (recurrenceMatrixAll s m t).mulVec (fun j => P.coeff j.val)=0 := by
  rw [mem_recurrenceSpace]
  constructor
  · rintro ⟨hP,hrec⟩
    have hn : P.natDegree≤t := Principal.degreeLT_natDegree_le ⟨P,Polynomial.mem_degreeLT.mpr hP⟩
    refine ⟨hn,?_⟩
    funext b
    have hh := hrec b.1 b.2.val b.2.isLt
    rw [Principal.recurrenceEval_eq_sum _ _ t P hn] at hh
    simpa only [recurrenceMatrixAll,Matrix.mulVec,dotProduct,Pi.zero_apply,mul_comm] using hh
  · rintro ⟨hn,hker⟩
    refine ⟨degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree<t+1 by omega)),?_⟩
    intro b j hj
    rw [Principal.recurrenceEval_eq_sum _ _ t P hn]
    have hh := congrFun hker (b,⟨j,hj⟩)
    simpa only [recurrenceMatrixAll,Matrix.mulVec,dotProduct,Pi.zero_apply,mul_comm] using hh

/-- Exact polynomial/coefficient equivalence, with no kernel dimension
or principality hypothesis. -/
def kernelPolynomialEquiv (s : β → ℕ → F) (m t : ℕ) :
    (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin) ≃ₗ[F] recurrenceSpace s m t where
  toFun a := ⟨Principal.assemble a.val,(recurrenceSpace_matrix s m t _).mpr
    ⟨Principal.assemble_natDegree_le _,by
      have ha : (recurrenceMatrixAll s m t).mulVec a.val=0 := a.property
      simpa only [Principal.assemble_coeff] using ha⟩⟩
  invFun P := ⟨fun j => (P.val).coeff j.val,((recurrenceSpace_matrix s m t _).mp P.property).2⟩
  left_inv a := by apply Subtype.ext; funext j; exact Principal.assemble_coeff a.val j
  right_inv P := by
    apply Subtype.ext
    exact Principal.assemble_coefficients t P.val ((recurrenceSpace_matrix s m t _).mp P.property).1
  map_add' a b := by
    apply Subtype.ext
    simp only [Principal.assemble,Submodule.coe_add,Pi.add_apply,map_add,
      Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp only [Principal.assemble,Submodule.coe_smul,Pi.smul_apply,← Polynomial.smul_monomial,
      Finset.smul_sum,RingHom.id_apply]

theorem recurrenceSpace_finrank (s : β → ℕ → F) (m t : ℕ) :
    Module.finrank F (recurrenceSpace s m t)=
      Module.finrank F (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin) :=
  (kernelPolynomialEquiv s m t).finrank_eq.symm

/-- In a two-dimensional space, every nonzero member extends to a basis. -/
theorem dimension_two_basis (K : Submodule F F[X])
    (hK : Module.finrank F K=2) (f : F[X]) (hfK : f∈K) (hf : f≠0) :
    ∃ g : F[X], g∈K ∧ g≠0 ∧ K=Submodule.span F ({f,g} : Set F[X]) := by
  letI : FiniteDimensional F K := FiniteDimensional.of_finrank_pos (by omega)
  let fK : K := ⟨f,hfK⟩
  have hfK0 : fK≠0 := by intro hz; exact hf (congrArg Subtype.val hz)
  have hline : Module.finrank F (F ∙ fK)=1 := finrank_span_singleton hfK0
  obtain ⟨gK,hgK⟩ : ∃ gK : K, gK∉F ∙ fK := by
    by_contra h
    push Not at h
    have heq : (F ∙ fK : Submodule F K)=⊤ := by
      exact top_unique (fun v _ => h v)
    rw [heq,finrank_top,hK] at hline
    omega
  have hgK0 : gK≠0 := by intro hz; exact hgK (hz ▸ Submodule.zero_mem _)
  have hdim : Module.finrank F ((F ∙ fK) ⊔ F ∙ gK : Submodule F K)=2 := by
    rw [Submodule.finrank_sup_span_singleton hgK,hline]
  have htop : ((F ∙ fK) ⊔ F ∙ gK : Submodule F K)=⊤ :=
    Submodule.eq_top_of_finrank_eq (hdim.trans hK.symm)
  refine ⟨gK.val,gK.property,?_,?_⟩
  · intro hz
    apply hgK0
    exact Subtype.ext hz
  · have hm := congrArg (Submodule.map K.subtype) htop
    rw [Submodule.map_sup,Submodule.map_span,Submodule.map_span,Submodule.map_top,
      Submodule.range_subtype] at hm
    have hsetf : K.subtype '' ({fK} : Set K)=({f} : Set F[X]) := by ext P; simp [fK]
    have hsetg : K.subtype '' ({gK} : Set K)=({gK.val} : Set F[X]) := by ext P; simp
    rw [hsetf,hsetg,← Submodule.span_union] at hm
    simpa only [Set.singleton_union] using hm.symm

/-- Actual evaluated nullity two plus nonprincipality supplies the sharp
gcd bound for any full-degree witness locator. -/
theorem dimension_two_gcd_bound (s : β → ℕ → F) (m t : ℕ) (htm : t≤m)
    (hnull : Module.finrank F (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin)=2)
    (hnon : NonprincipalSpace (recurrenceSpace s m t) t)
    (f : F[X]) (hf : f∈recurrenceSpace s m t) (hf0 : f≠0) (hfd : f.natDegree=t) :
    ∃ g : F[X], g∈recurrenceSpace s m t ∧ g≠0 ∧
      recurrenceSpace s m t=Submodule.span F ({f,g} : Set F[X]) ∧
      (GCDMonoid.gcd f g).natDegree+m+1≤2*t := by
  obtain ⟨g,hg,hg0,hspan⟩ := dimension_two_basis (recurrenceSpace s m t)
    ((recurrenceSpace_finrank s m t).trans hnull) f hf hf0
  have hgd := ((recurrenceSpace_matrix s m t g).mp hg).1
  exact ⟨g,hg,hg0,hspan,nonprincipal_two_generator_gcd_bound s m t htm f g hf0 hg0 hfd hgd hspan hnon⟩

end
end FrobeniusLocator.Strata
end PackSource_KernelTwoSpace

section PackSource_PunctureWeights
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- Removing one node changes the dual weight by exactly its locator
factor. This is the puncturing identity used by the K2 count. -/
theorem punctured_weight (x : ι → F) (hx : Function.Injective x) (a : ι)
    (i : {i // i≠a}) :
    weight x i.val*(x i.val-x a)=weight (fun j : {j // j≠a} => x j.val) i := by
  let T := ((Finset.univ : Finset ι).erase i.val).erase a
  have hprod : (∏ j∈((Finset.univ : Finset {j // j≠a}).erase i), (x i.val-x j.val))=
      ∏ j∈T, (x i.val-x j) := by
    apply Finset.prod_bij (fun j _ => j.val)
    · intro j hj
      simp only [T,Finset.mem_erase,Finset.mem_univ,true_and]
      exact ⟨j.property,⟨by intro heq; exact (Finset.mem_erase.mp hj).1 (Subtype.ext heq),trivial⟩⟩
    · intro j hj k hk heq
      exact Subtype.ext heq
    · intro j hj
      have hja : j≠a := (Finset.mem_erase.mp hj).1
      have hji : j≠i.val := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      refine ⟨⟨j,hja⟩,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,rfl⟩
      intro heq
      exact hji (congrArg Subtype.val heq)
    · intro j hj
      rfl
  have ha : a∈(Finset.univ : Finset ι).erase i.val :=
    Finset.mem_erase.mpr ⟨Ne.symm i.property,Finset.mem_univ _⟩
  have horig : (∏ j∈((Finset.univ : Finset ι).erase i.val), (x i.val-x j))=
      (x i.val-x a)*(∏ j∈T, (x i.val-x j)) :=
    (Finset.mul_prod_erase _ _ ha).symm
  have hxa : x i.val-x a≠0 := sub_ne_zero.mpr (fun h => i.property (hx h))
  dsimp [weight]
  rw [horig,hprod]
  rw [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ hxa,mul_one]

/-- The punctured syndrome is the original syndrome contracted against
X-a. The node at a vanishes automatically. -/
theorem punctured_syndrome (x w : ι → F) (hx : Function.Injective x) (a : ι) (j : ℕ) :
    syndrome (fun i : {i // i≠a} => x i.val) (fun i => w i.val) j =
      syndrome x w (j+1)-x a*syndrome x w j := by
  have hsum : (∑ i : {i // i≠a}, weight x i.val*(x i.val-x a)*w i.val*x i.val^j)=
      ∑ i∈(Finset.univ : Finset ι).erase a, weight x i*(x i-x a)*w i*x i^j := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_erase.mpr ⟨i.property,Finset.mem_univ _⟩
    · intro i hi k hk heq; exact Subtype.ext heq
    · intro i hi
      exact ⟨⟨i,(Finset.mem_erase.mp hi).1⟩,Finset.mem_univ _,rfl⟩
    · intro i _; rfl
  simp only [syndrome,← punctured_weight x hx a]
  rw [hsum]
  have hz : weight x a*(x a-x a)*w a*x a^j=0 := by simp
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a),hz,sub_zero]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

end
end FrobeniusLocator.Strata
end PackSource_PunctureWeights

section PackSource_SlopeRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

def twoConjugations (σ : F →+* F) : Fin 2 → F →+* F := ![RingHom.id F,σ]
def threeConjugations (σ : F →+* F) : Fin 3 → F →+* F := ![RingHom.id F,σ,σ.comp σ]

theorem conjugateErrors_two (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    conjugateErrors (twoConjugations σ) x e L=errorTwoMatrix σ x e L := by
  ext ⟨b,j⟩ i
  fin_cases b <;> simp [conjugateErrors,twoConjugations,errorTwoMatrix]

theorem conjugateErrors_three (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    conjugateErrors (threeConjugations σ) x e L=errorThreeMatrix σ x e L := by
  ext ⟨b,j⟩ i
  fin_cases b <;> simp [conjugateErrors,threeConjugations,errorThreeMatrix,RingHom.comp_apply]

/-- R3 stated on evaluated syndrome matrices, for ANY decoder and its
EXACT support. All bridges to the error-column theorem are proved. -/
theorem normal_slope_three_rank (σ : F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (k L t H : ℕ) (hsize : k+L+t≤Fintype.card ι) (hH : H<L)
    (U V R : F[X]) (hpair : U≠0 ∨ V≠0)
    (rel : TwistedRelation σ x w k H U V R)
    (P : F[X]) (hP : P.degree<k) (S : Finset ι) (hS : S.card≤t)
    (hagree : ∀ i, i∉S → w i=P.eval (x i))
    (hexact : ∀ i∈S, w i≠P.eval (x i))
    (hnormal : (conjugateHankel (twoConjugations σ) x w L t).rank=L+H) :
    let G := GCDMonoid.gcd U V
    let u := U/G
    let v := V/G
    let d := max u.natDegree v.natDegree
    let q := d-(GCDMonoid.gcd u (v.map σ)).natDegree
    (conjugateHankel (threeConjugations σ) x w L t).rank=min S.card (L+H+q) := by
  have hfix2 : ∀ b i, twoConjugations σ b (x i)=x i := by
    intro b i
    fin_cases b <;> simp [twoConjugations,hfixed]
  have hfix3 : ∀ b i, threeConjugations σ b (x i)=x i := by
    intro b i
    fin_cases b <;> simp [threeConjugations,hfixed,RingHom.comp_apply]
  have h2 := conjugateHankel_error_rank (twoConjugations σ) x w hx hfix2 P k L t hP hsize S
    (by omega) hagree
  have h3 := conjugateHankel_error_rank (threeConjugations σ) x w hx hfix3 P k L t hP hsize S
    (by omega) hagree
  rw [conjugateErrors_two] at h2
  rw [conjugateErrors_three] at h3
  have he : ∀ i : S, w i.val-P.eval (x i.val)≠0 :=
    fun i => sub_ne_zero.mpr (hexact i.val i.property)
  have hr : ∀ i : S, U.eval (x i.val)*(w i.val-P.eval (x i.val))+
      V.eval (x i.val)*σ (w i.val-P.eval (x i.val))=0 := by
    intro i
    apply decoder_error_identity σ x w hx hfixed k H U V R rel (Finset.univ\S)
      (by rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]; omega) P hP
      (fun j hj => (hagree j (Finset.mem_sdiff.mp hj).2).symm) i.val
  have hn : (errorTwoMatrix σ (fun i : S => x i.val) (fun i : S => w i.val-P.eval (x i.val)) L).rank=L+H := by
    rw [h2] at hnormal
    exact hnormal
  have hR3 := (normal_error_three_rank σ (fun i : S => x i.val)
    (fun i : S => w i.val-P.eval (x i.val)) (hx.comp Subtype.val_injective)
    (fun i => hfixed i.val) U V H L rel.degree_U rel.degree_V hpair hH he hr hn).2.2
  rw [h3]
  simpa only [Fintype.card_coe] using hR3

/-- Literal m-block polynomial matrix used for Frobenius slope evaluation. -/
def frobeniusStacked (p blocks : ℕ) (x u v : ι → F) (L t : ℕ) :
    Matrix (Fin blocks × Fin L) (Fin (t+1)) F[X] := fun b j =>
  C (syndrome x u (b.2.val+j.val)^(p^b.1.val))+
    (Polynomial.X : F[X])^(p^b.1.val)*C (syndrome x v (b.2.val+j.val)^(p^b.1.val))

theorem stacked_eq_frobeniusStacked (p : ℕ) [ExpChar F p] (x u v : ι → F) (L t : ℕ) :
    stacked p x u v L t=frobeniusStacked p 2 x u v L t := by
  ext ⟨b,i⟩ j
  fin_cases b <;> simp [stacked,hankel,frobeniusStacked]

theorem frobeniusStacked_eval (p : ℕ) [ExpChar F p] (blocks : ℕ)
    (x u v : ι → F) (L t : ℕ) (γ : F) :
    (frobeniusStacked p blocks x u v L t).map (Polynomial.evalRingHom γ)=
      conjugateHankel (fun b : Fin blocks => iterateFrobenius F p b.val)
        x (fun i => u i+γ*v i) L t := by
  ext b j
  have hs := Principal.syndrome_linear x u v 1 γ (b.2.val+j.val)
  simp only [one_mul] at hs
  simp only [frobeniusStacked,Matrix.map_apply,Polynomial.coe_evalRingHom,eval_add,
    eval_mul,eval_C,eval_pow,eval_X]
  change (syndrome x u (b.2.val+j.val))^(p^b.1.val)+
    γ^(p^b.1.val)*(syndrome x v (b.2.val+j.val))^(p^b.1.val)=_
  rw [conjugateHankel,hs,map_add,map_mul]
  rfl

end
end FrobeniusLocator.Strata
end PackSource_SlopeRank

section PackSource_PunctureKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]

def contractSequence (s : β → ℕ → F) (a : F) : β → ℕ → F :=
  fun b j => s b (j+1)-a*s b j

def evalFunctional (a : F) : F[X] →ₗ[F] F where
  toFun P := P.eval a
  map_add' P Q := eval_add
  map_smul' c P := by simp

theorem recurrenceEval_contract (s : ℕ → F) (a : F) (j : ℕ) (Q : F[X]) :
    Principal.recurrenceEval (fun i => s (i+1)-a*s i) j Q=
      Principal.recurrenceEval s (j+1) Q-a*Principal.recurrenceEval s j Q := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR => simp only [map_add,hQ,hR]; ring
  | monomial i c => simp only [Principal.recurrenceEval_monomial]; ring

theorem recurrenceEval_X_sub_C (s : ℕ → F) (a : F) (j : ℕ) (Q : F[X]) :
    Principal.recurrenceEval s j (((Polynomial.X : F[X])-C a)*Q)=
      Principal.recurrenceEval (fun i => s (i+1)-a*s i) j Q := by
  rw [recurrenceEval_contract]
  have heq : ((Polynomial.X : F[X])-C a)*Q=Q*(Polynomial.X : F[X])^1-a • Q := by
    simp only [pow_one,Polynomial.smul_eq_C_mul]
    ring
  rw [heq,map_sub,map_smul,Principal.recurrenceEval_shift]
  simp only [smul_eq_mul,RingHom.id_apply]

/-- Multiplication by X-a identifies the punctured recurrence kernel
with the old kernel restricted by evaluation at a. -/
theorem contracted_recurrence_membership (s : β → ℕ → F) (a : F) (m t : ℕ)
    (ht : 1≤t) (htm : t≤m) (Q : F[X]) :
    Q∈recurrenceSpace (contractSequence s a) (m-1) (t-1) ↔
      ((Polynomial.X : F[X])-C a)*Q∈recurrenceSpace s m t := by
  rw [mem_recurrenceSpace,mem_recurrenceSpace]
  have hlen : (m-1)-(t-1)=m-t := by omega
  have hbound : (t-1)+1=t := by omega
  rw [hlen,hbound]
  have hdegree : Q.degree<t ↔ ((((Polynomial.X : F[X])-C a)*Q).degree<(t+1 : ℕ)) := by
    by_cases hq : Q=0
    · simp [hq]
    have hp : (Polynomial.X : F[X])-C a≠0 := (Polynomial.monic_X_sub_C a).ne_zero
    rw [← natDegree_lt_iff_degree_lt hq,← natDegree_lt_iff_degree_lt (mul_ne_zero hp hq),
      natDegree_mul hp hq,Polynomial.natDegree_X_sub_C]
    omega
  rw [hdegree]
  constructor
  · rintro ⟨hQ,hrec⟩
    refine ⟨hQ,?_⟩
    intro b j hj
    rw [recurrenceEval_X_sub_C]
    exact hrec b j hj
  · rintro ⟨hQ,hrec⟩
    refine ⟨hQ,?_⟩
    intro b j hj
    change Principal.recurrenceEval (fun i => s b (i+1)-a*s b i) j Q=0
    rw [← recurrenceEval_X_sub_C]
    exact hrec b j hj

/-- The actual polynomial linear equivalence at one puncture. -/
def puncturedKernelEquiv (s : β → ℕ → F) (a : F) (m t : ℕ) (ht : 1≤t) (htm : t≤m) :
    recurrenceSpace (contractSequence s a) (m-1) (t-1) ≃ₗ[F]
      (recurrenceSpace s m t ⊓ LinearMap.ker (evalFunctional a) : Submodule F F[X]) := by
  let f : recurrenceSpace (contractSequence s a) (m-1) (t-1) →ₗ[F]
      (recurrenceSpace s m t ⊓ LinearMap.ker (evalFunctional a) : Submodule F F[X]) :=
    { toFun := fun Q => ⟨((Polynomial.X : F[X])-C a)*Q.val,
        ⟨(contracted_recurrence_membership s a m t ht htm Q.val).mp Q.property,by simp [evalFunctional]⟩⟩
      map_add' := by intro Q R; apply Subtype.ext; simp only [Submodule.coe_add,mul_add]
      map_smul' := by intro c Q; apply Subtype.ext; simp only [Submodule.coe_smul,mul_smul_comm,RingHom.id_apply] }
  apply LinearEquiv.ofBijective f
  constructor
  · intro Q R hQR
    apply Subtype.ext
    exact mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero (congrArg Subtype.val hQR)
  · intro P
    have hz : P.val.eval a=0 := P.property.2
    obtain ⟨Q,hQ⟩ := (Polynomial.dvd_iff_isRoot.mpr hz)
    refine ⟨⟨Q,(contracted_recurrence_membership s a m t ht htm Q).mpr ?_⟩,?_⟩
    · rw [← hQ]
      exact P.property.1
    · apply Subtype.ext
      exact hQ.symm

end
end FrobeniusLocator.Strata
end PackSource_PunctureKernel

section PackSource_KernelTwoRoots
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance strataDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]

theorem gcd_eval_zero_iff (f g : F[X]) (a : F) :
    (GCDMonoid.gcd f g).eval a=0 ↔ f.eval a=0 ∧ g.eval a=0 := by
  change (GCDMonoid.gcd f g).IsRoot a ↔ f.IsRoot a ∧ g.IsRoot a
  simp only [← Polynomial.dvd_iff_isRoot,_root_.dvd_gcd_iff]

/-- Common witness zeros are at most the gcd degree. This is all the
incidence argument needs, and follows directly from univariate root counting. -/
theorem locator_common_roots_card_le (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (g : F[X]) :
    (S.filter (fun i => g.eval (x i)=0)).card≤(GCDMonoid.gcd (locator x S) g).natDegree := by
  classical
  have hdiv : GCDMonoid.gcd (locator x S) g∣locator x S := gcd_dvd_left _ _
  have hG0 : GCDMonoid.gcd (locator x S) g≠0 := ne_zero_of_dvd_ne_zero (locator_monic x S).ne_zero hdiv
  apply root_nodes_card_le x hx _ hG0
  intro i hi
  exact (gcd_eval_zero_iff _ _ _).mpr
    ⟨locator_eval_zero x S i (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩

/-- Each usable witness root is an active evaluation functional and hence
reduces actual evaluated nullity two to one. -/
theorem active_root_nullity_one (s : β → ℕ → F) (m t : ℕ)
    (hnull : Module.finrank F (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin)=2)
    (g : F[X]) (hg : g∈recurrenceSpace s m t) (a : F) (hga : g.eval a≠0) :
    Module.finrank F (LinearMap.ker (AppendConstants.appendOne (recurrenceMatrixAll s m t)
      (fun j => a^j.val)).mulVecLin)=1 := by
  have hm := (recurrenceSpace_matrix s m t g).mp hg
  have hactive : ∃ v : Fin (t+1) → F, (recurrenceMatrixAll s m t).mulVec v=0 ∧
      AppendConstants.functional (fun j => a^j.val) v≠0 := by
    refine ⟨fun j => g.coeff j.val,hm.2,?_⟩
    change (∑ j : Fin (t+1), a^j.val*g.coeff j.val)≠0
    have heq : (∑ j : Fin (t+1), a^j.val*g.coeff j.val)=g.eval a := by
      rw [← sum_coeff_eval g t hm.1 a]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rwa [heq]
  have hh := AppendConstants.nullity_drop_one (recurrenceMatrixAll s m t) (fun j => a^j.val) hactive
  rw [hnull] at hh
  omega

/-- The complete elementary K2 root supply: at least L+1 distinct domain
roots kill one kernel dimension. No generic-rank or gcd premise. -/
theorem nonprincipal_two_kernel_usable_roots (s : β → ℕ → F) (m t L : ℕ)
    (hm : m=L+t) (x : ι → F) (hx : Function.Injective x)
    (hnull : Module.finrank F (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin)=2)
    (hnon : NonprincipalSpace (recurrenceSpace s m t) t)
    (S : Finset ι) (hS : S.card=t) (hf : locator x S∈recurrenceSpace s m t) :
    ∃ T : Finset ι, T⊆S ∧ L+1≤T.card ∧
      ∀ i∈T, Module.finrank F
        (LinearMap.ker (AppendConstants.appendOne (recurrenceMatrixAll s m t)
          (fun j => x i^j.val)).mulVecLin)=1 := by
  classical
  have hf0 := (locator_monic x S).ne_zero
  have hfd : (locator x S).natDegree=t := (locator_natDegree x S).trans hS
  obtain ⟨g,hg,hg0,hspan,hbound⟩ := dimension_two_gcd_bound s m t (by omega)
    hnull hnon (locator x S) hf hf0 hfd
  let T := S.filter (fun i => g.eval (x i)≠0)
  have hzero : (S.filter (fun i => g.eval (x i)=0)).card≤
      (GCDMonoid.gcd (locator x S) g).natDegree := locator_common_roots_card_le x hx S g
  have hTcard : T.card=t-(S.filter (fun i => g.eval (x i)=0)).card := by
    have heq : T=S\S.filter (fun i => g.eval (x i)=0) := by
      ext i
      simp only [T,Finset.mem_filter,Finset.mem_sdiff]
      tauto
    rw [heq,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),hS]
  refine ⟨T,Finset.filter_subset _ _,by omega,?_⟩
  intro i hi
  exact active_root_nullity_one s m t hnull g hg (x i) (Finset.mem_filter.mp hi).2

end
end FrobeniusLocator.Strata
end PackSource_KernelTwoRoots

section PackSource_FullErrorPrincipal
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]

theorem matrix_injective_of_full_column_rank {row col : Type} [Fintype row] [Fintype col]
    (M : Matrix row col F) (hr : M.rank=Fintype.card col) : Function.Injective M.mulVecLin := by
  have hn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank+Module.finrank F (LinearMap.ker M.mulVecLin)=_ at hn
  rw [Module.finrank_fintype_fun_eq_card,hr] at hn
  have hk : Module.finrank F (LinearMap.ker M.mulVecLin)=0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem locator_dvd_of_eval_zero (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (P : F[X]) (hz : ∀ i∈S, P.eval (x i)=0) : locator x S∣P := by
  classical
  by_cases hP : P=0
  · simp [hP]
  have hroots : (locator x S).roots≤P.roots := by
    rw [Principal.locator_roots]
    apply (Multiset.le_iff_subset (S.nodup.map hx)).mpr
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp ha
    exact (Polynomial.mem_roots hP).mpr (hz i hi)
  exact (Principal.locator_splits x S).dvd_of_roots_le_roots (locator_monic x S).ne_zero hroots

theorem bounded_locator_quotient (x : ι → F) (S : Finset ι) (P : F[X]) (t : ℕ)
    (hS : S.card≤t) (hP : P.natDegree≤t) (hdiv : locator x S∣P) :
    ∃ Q : F[X], Q.degree<(t-S.card+1 : ℕ) ∧ P=locator x S*Q := by
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨Q,?_,hQ⟩
  by_cases hq : Q=0
  · simp [hq]
  have hd := natDegree_mul (locator_monic x S).ne_zero hq
  rw [← hQ,locator_natDegree] at hd
  exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<t-S.card+1 by omega))

theorem recurrenceMatrixAll_conjugate (σ : β → F →+* F) (x w : ι → F) (m t : ℕ) :
    recurrenceMatrixAll (fun b j => σ b (syndrome x w j)) m t=
      conjugateHankel σ x w (m-t) t := by
  ext b j
  simp only [recurrenceMatrixAll,conjugateHankel,Nat.add_comm]

/-- Full third-error rank forces an evaluated principal locator kernel
at the TARGET padded degree t, even when actual error weight is smaller.
This is the bridge needed to interpret the residual q cut correctly. -/
theorem full_error_rank_principal (σ : β → F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (k m t : ℕ) (hkm : k+m=Fintype.card ι) (htm : t≤m)
    (P : F[X]) (hP : P.degree<k) (E : Finset ι) (hE : E.card≤t)
    (hagree : ∀ i, i∉E → w i=P.eval (x i))
    (hfull : (conjugateErrors σ (fun i : E => x i.val)
      (fun i : E => w i.val-P.eval (x i.val)) (m-t)).rank=E.card) :
    recurrenceSpace (fun b j => σ b (syndrome x w j)) m t=
      (Polynomial.degreeLT F (t-E.card+1)).map (polynomialMul (locator x E)) := by
  let M := conjugateHankel σ x w (m-t) t
  let A : Matrix (β × Fin (m-t)) E F := Matrix.of (fun b i =>
    weight x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)
  let B := nodeVandermonde (fun i : E => x i.val) t
  have hfactor : M=A*B := conjugateHankel_factorization σ x w hx hfixed P k (m-t) t hP
    (by omega) E hagree
  have hB : Function.Surjective B.mulVecLin := nodeVandermonde_surjective (fun i : E => x i.val)
    (fun i j hij => Subtype.ext (hx hij)) t (by rw [Fintype.card_coe]; omega)
  have hM : M.rank=E.card := (conjugateHankel_error_rank σ x w hx hfixed P k (m-t) t hP
    (by omega) E (by omega) hagree).trans hfull
  have hA : A.rank=Fintype.card E := by rw [hfactor,rank_mul_of_surjective A B hB] at hM; simpa using hM
  have hinj := matrix_injective_of_full_column_rank A hA
  have hcoeff (Q : F[X]) (hQ : Q.natDegree≤t) :
      B.mulVec (fun j : Fin (t+1) => Q.coeff j.val) = fun i : E => Q.eval (x i.val) := by
    funext i
    change (∑ j : Fin (t+1), x i.val^j.val*Q.coeff j.val)=Q.eval (x i.val)
    rw [← sum_coeff_eval Q t hQ (x i.val)]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hker_iff (Q : F[X]) (hQ : Q.natDegree≤t) :
      M.mulVec (fun j : Fin (t+1) => Q.coeff j.val)=0 ↔ ∀ i∈E, Q.eval (x i)=0 := by
    rw [hfactor,← Matrix.mulVec_mulVec,hcoeff Q hQ]
    constructor
    · intro hz i hi
      have hvec : (fun i : E => Q.eval (x i.val))=0 := hinj (hz.trans (map_zero A.mulVecLin).symm)
      exact congrFun hvec ⟨i,hi⟩
    · intro hz
      have hvec : (fun i : E => Q.eval (x i.val))=0 := funext (fun i => hz i.val i.property)
      rw [hvec,Matrix.mulVec_zero]
  apply le_antisymm
  · intro Q hQ
    have hm := (recurrenceSpace_matrix _ m t Q).mp hQ
    rw [recurrenceMatrixAll_conjugate] at hm
    have hz := (hker_iff Q hm.1).mp hm.2
    obtain ⟨R,hR,hQR⟩ := bounded_locator_quotient x E Q t hE hm.1 (locator_dvd_of_eval_zero x hx E Q hz)
    exact ⟨R,Polynomial.mem_degreeLT.mpr hR,hQR.symm⟩
  · rintro _ ⟨R,hR,rfl⟩
    have hRn := Principal.degreeLT_natDegree_le (q := t-E.card) ⟨R,hR⟩
    change R.natDegree≤t-E.card at hRn
    have hdeg : (locator x E*R).natDegree≤t := natDegree_mul_le.trans (by rw [locator_natDegree]; omega)
    apply (recurrenceSpace_matrix _ m t _).mpr
    refine ⟨hdeg,?_⟩
    rw [recurrenceMatrixAll_conjugate]
    apply (hker_iff _ hdeg).mpr
    intro i hi
    simp only [eval_mul,locator_eval_zero x E i hi,zero_mul]

end
end FrobeniusLocator.Strata
end PackSource_FullErrorPrincipal

section PackSource_PunctureNullity
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]

theorem functional_coefficients_eval (t : ℕ) (P : F[X]) (hP : P.natDegree≤t) (a : F) :
    AppendConstants.functional (fun j : Fin (t+1) => a^j.val) (fun j => P.coeff j.val)=P.eval a := by
  change (∑ j : Fin (t+1), a^j.val*P.coeff j.val)=P.eval a
  rw [← sum_coeff_eval P t hP a]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Coefficient encoding of the old polynomial kernel restricted at a. -/
def appendedPolynomialEquiv (s : β → ℕ → F) (m t : ℕ) (a : F) :
    (recurrenceSpace s m t ⊓ LinearMap.ker (evalFunctional a) : Submodule F F[X]) ≃ₗ[F]
      LinearMap.ker (AppendConstants.appendOne (recurrenceMatrixAll s m t)
        (fun j => a^j.val)).mulVecLin := by
  let f : (recurrenceSpace s m t ⊓ LinearMap.ker (evalFunctional a) : Submodule F F[X]) →ₗ[F]
      LinearMap.ker (AppendConstants.appendOne (recurrenceMatrixAll s m t) (fun j => a^j.val)).mulVecLin :=
    { toFun := fun P => ⟨fun j => P.val.coeff j.val,by
        change (AppendConstants.appendOne (recurrenceMatrixAll s m t) (fun j => a^j.val)).mulVec
          (fun j => P.val.coeff j.val)=0
        apply (AppendConstants.appendOne_kernel _ _ _).mpr
        have hmem := (recurrenceSpace_matrix s m t P.val).mp P.property.1
        refine ⟨hmem.2,?_⟩
        rw [functional_coefficients_eval t P.val hmem.1 a]
        exact P.property.2⟩
      map_add' := by
        intro P Q
        apply Subtype.ext
        funext j
        change (P.val+Q.val).coeff j.val=P.val.coeff j.val+Q.val.coeff j.val
        simp only [Polynomial.coeff_add]
      map_smul' := by intro c P; apply Subtype.ext; funext j; simp only [Submodule.coe_smul,Polynomial.coeff_smul,Pi.smul_apply,RingHom.id_apply] }
  apply LinearEquiv.ofBijective f
  constructor
  · intro P Q hPQ
    apply Subtype.ext
    apply Principal.coefficients_injective_bounded t P.val Q.val
      ((recurrenceSpace_matrix s m t _).mp P.property.1).1
      ((recurrenceSpace_matrix s m t _).mp Q.property.1).1
    exact congrFun (congrArg Subtype.val hPQ)
  · intro c
    have hcp : (AppendConstants.appendOne (recurrenceMatrixAll s m t) (fun j => a^j.val)).mulVec c.val=0 := c.property
    have hc := (AppendConstants.appendOne_kernel _ _ _).mp hcp
    let P := Principal.assemble c.val
    have hp : P∈recurrenceSpace s m t := (recurrenceSpace_matrix s m t P).mpr
      ⟨Principal.assemble_natDegree_le _,by simpa only [P,Principal.assemble_coeff] using hc.1⟩
    have hPa : P.eval a=0 := by
      rw [← functional_coefficients_eval t P (Principal.assemble_natDegree_le _) a]
      simpa only [P,Principal.assemble_coeff] using hc.2
    refine ⟨⟨P,hp,hPa⟩,?_⟩
    apply Subtype.ext
    funext j
    exact Principal.assemble_coeff c.val j

/-- Appending one evaluation and puncturing one node have identical
kernel dimensions. This is a theorem, not an incidence premise. -/
theorem punctured_nullity_eq_appended (s : β → ℕ → F) (m t : ℕ) (a : F)
    (ht : 1≤t) (htm : t≤m) :
    Module.finrank F (LinearMap.ker
      (recurrenceMatrixAll (contractSequence s a) (m-1) (t-1)).mulVecLin)=
    Module.finrank F (LinearMap.ker (AppendConstants.appendOne (recurrenceMatrixAll s m t)
      (fun j => a^j.val)).mulVecLin) := by
  rw [← recurrenceSpace_finrank]
  exact (puncturedKernelEquiv s a m t ht htm).finrank_eq.trans (appendedPolynomialEquiv s m t a).finrank_eq

section Domain
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem punctured_conjugate_sequence (σ : β → F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i) (a : ι) :
    (fun b j => σ b (syndrome (fun i : {i // i≠a} => x i.val) (fun i => w i.val) j))=
      contractSequence (fun b j => σ b (syndrome x w j)) (x a) := by
  funext b j
  rw [punctured_syndrome x w hx a j,map_sub,map_mul,hfixed]
  rfl

theorem actual_punctured_nullity_eq_appended (σ : β → F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i) (m t : ℕ) (a : ι)
    (ht : 1≤t) (htm : t≤m) :
    Module.finrank F (LinearMap.ker (recurrenceMatrixAll
      (fun b j => σ b (syndrome (fun i : {i // i≠a} => x i.val) (fun i => w i.val) j))
      (m-1) (t-1)).mulVecLin)=
    Module.finrank F (LinearMap.ker (AppendConstants.appendOne
      (recurrenceMatrixAll (fun b j => σ b (syndrome x w j)) m t)
      (fun j => x a^j.val)).mulVecLin) := by
  rw [punctured_conjugate_sequence σ x w hx hfixed a]
  exact punctured_nullity_eq_appended _ m t (x a) ht htm
end Domain

end
end FrobeniusLocator.Strata
end PackSource_PunctureNullity

section PackSource_StrataCounting
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset
open scoped BigOperators
variable {F ι : Type} [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- Finite incidence arithmetic underlying the one-root K2 charge.
The per-node regular bound is a named input; no geometry is encoded as
an axiom or silently inferred from this double count. -/
theorem one_root_incidence_count (Γ : Finset F) (usable : F → Finset ι)
    (L M : ℕ) (hroots : ∀ γ∈Γ, L+1≤(usable γ).card)
    (hnode : ∀ i, (Γ.filter (fun γ => i∈usable γ)).card≤M) :
    Γ.card≤Fintype.card ι*M/(L+1) := by
  classical
  have hlow : Γ.card*(L+1)≤∑ γ∈Γ, (usable γ).card := by
    calc
      _ = ∑ γ∈Γ, (L+1) := by simp
      _ ≤ _ := Finset.sum_le_sum hroots
  have hswap : (∑ γ∈Γ, (usable γ).card)=
      ∑ i : ι, (Γ.filter (fun γ => i∈usable γ)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    have hgamma (γ : F) : (∑ i∈usable γ, (1 : ℕ))=
        ∑ i : ι, if i∈usable γ then 1 else 0 := by simp
    simp_rw [hgamma]
    exact Finset.sum_comm
  have hhigh : (∑ i : ι, (Γ.filter (fun γ => i∈usable γ)).card)≤Fintype.card ι*M :=
    (Finset.sum_le_sum (fun i _ => hnode i)).trans_eq (by simp)
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (hlow.trans (hswap.trans_le hhigh))

def principalThreePrice (n t : ℕ) : ℕ := n^3+(t+1)*n^2+(t+1)^2*n+(t+1)^3

def kernelTwoPrice (n L : ℕ) : ℕ := n*(n-1)^3/(L+1)

theorem native_principal_three_price : principalThreePrice 262144 81908=25951422703581901 := by
  norm_num [principalThreePrice]

theorem native_kernel_two_price : kernelTwoPrice 262144 49164=96050288617518050 := by
  norm_num [kernelTwoPrice]

theorem native_booked_total : 69755067252718+principalThreePrice 262144 81908+
    kernelTwoPrice 262144 49164=122071466388352669 := by
  norm_num [principalThreePrice,kernelTwoPrice]

theorem native_residual_ledger : 69755067252718+principalThreePrice 262144 81908+
    kernelTwoPrice 262144 49164+122925228561990328=244996694950342997 := by
  norm_num [principalThreePrice,kernelTwoPrice]

theorem native_joint_ledger : 29984033161052090+69755067252718+
    principalThreePrice 262144 81908+kernelTwoPrice 262144 49164+
    122925228561990328=274980728111395087 := by
  norm_num [principalThreePrice,kernelTwoPrice]

/-- Exact one-root count at the first benchmark cell, conditional ONLY
on the two finite incidence inputs. The regular (n-1)^3 node bound remains
visible in the theorem signature. -/
theorem native_kernel_two_incidence_count (Γ : Finset F) (usable : F → Finset ι)
    (hn : Fintype.card ι=262144)
    (hroots : ∀ γ∈Γ, 49165≤(usable γ).card)
    (hnode : ∀ i, (Γ.filter (fun γ => i∈usable γ)).card≤262143^3) :
    Γ.card≤96050288617518050 := by
  have h := one_root_incidence_count Γ usable 49164 (262143^3) hroots hnode
  rw [hn] at h
  exact h.trans_eq (by norm_num)

/-- Four DISJOINT slope strata add. A principal bound or regular bound
is still a hypothesis here until its geometric theorem has been proved. -/
theorem four_strata_count (Γ : Finset F) (drop principal two : F → Prop)
    [DecidablePred drop] [DecidablePred principal] [DecidablePred two]
    (D P J R : ℕ)
    (hD : (Γ.filter drop).card≤D)
    (hP : (Γ.filter (fun γ => ¬drop γ ∧ principal γ)).card≤P)
    (hJ : (Γ.filter (fun γ => ¬drop γ ∧ ¬principal γ ∧ two γ)).card≤J)
    (hR : (Γ.filter (fun γ => ¬drop γ ∧ ¬principal γ ∧ ¬two γ)).card≤R) :
    Γ.card≤D+P+J+R := by
  classical
  have hpart : Γ.card=(Γ.filter drop).card+
      (Γ.filter (fun γ => ¬drop γ ∧ principal γ)).card+
      (Γ.filter (fun γ => ¬drop γ ∧ ¬principal γ ∧ two γ)).card+
      (Γ.filter (fun γ => ¬drop γ ∧ ¬principal γ ∧ ¬two γ)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    by_cases hd : drop γ <;> by_cases hp : principal γ <;> by_cases ht : two γ <;> simp [hd,hp,ht]
  omega

end
end FrobeniusLocator.Strata
end PackSource_StrataCounting

section PackSource_PunctureBadSlope
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Lift a support avoiding the punctured node without changing its size. -/
def liftPuncturedSet (a : ι) (S : Finset ι) : Finset {i // i≠a} :=
  Finset.univ.filter (fun i => i.val∈S)

theorem liftPuncturedSet_image (a : ι) (S : Finset ι) (ha : a∉S) :
    (liftPuncturedSet a S).image Subtype.val=S := by
  ext i
  simp only [liftPuncturedSet,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i,by intro h; exact ha (h ▸ hi)⟩,hi,rfl⟩

theorem liftPuncturedSet_card (a : ι) (S : Finset ι) (ha : a∉S) :
    (liftPuncturedSet a S).card=S.card := by
  exact (Finset.card_image_of_injective (liftPuncturedSet a S) Subtype.val_injective).symm.trans
    (congrArg Finset.card (liftPuncturedSet_image a S ha))

/-- Puncturing an ERROR-WITNESS node preserves SAME-SUPPORT MCA badness.
This does not assert preservation when the removed node lies in the
agreement witness. -/
theorem puncture_bad_witness (x u v : ι → F) (k A : ℕ) (γ : F)
    (S : Finset ι) (hS : A≤S.card)
    (hdec : ExtendsOn x (fun i => u i+γ*v i) k S)
    (hbad : ¬(ExtendsOn x u k S ∧ ExtendsOn x v k S)) (a : ι) (ha : a∉S) :
    Principal.BadSlope (fun i : {i // i≠a} => x i.val) (fun i => u i.val) (fun i => v i.val) k A γ := by
  let T := liftPuncturedSet a S
  have hTS : T.card=S.card := liftPuncturedSet_card a S ha
  refine ⟨T,by omega,?_,?_⟩
  · obtain ⟨P,hP,hPv⟩ := hdec
    refine ⟨P,hP,?_⟩
    intro i hi
    exact hPv i.val (Finset.mem_filter.mp hi).2
  · rintro ⟨⟨P,hP,hPv⟩,⟨Q,hQ,hQv⟩⟩
    apply hbad
    have hne (i : ι) (hi : i∈S) : i≠a := by intro h; exact ha (h ▸ hi)
    refine ⟨⟨P,hP,?_⟩,⟨Q,hQ,?_⟩⟩
    · intro i hi
      exact hPv ⟨i,hne i hi⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    · intro i hi
      exact hQv ⟨i,hne i hi⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

end
end FrobeniusLocator.Strata
end PackSource_PunctureBadSlope

section PackSource_ConjugateLocator
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]

theorem locator_coefficient_fixed (σ : F →+* F) (x : ι → F)
    (hfixed : ∀ i, σ (x i)=x i) (E : Finset ι) (j : ℕ) :
    σ ((locator x E).coeff j)=(locator x E).coeff j := by
  have hm : (locator x E).map σ=locator x E := by simp [locator,Polynomial.map_prod,hfixed]
  have hc := congrArg (fun Q : F[X] => Q.coeff j) hm
  simpa only [Polynomial.coeff_map] using hc

/-- All conjugate blocks annihilate the same BASE-NODE locator. -/
theorem conjugate_locator_annihilates (σ : β → F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (k L t : ℕ) (hsize : k+L+t≤Fintype.card ι)
    (P : F[X]) (hP : P.degree<k) (E : Finset ι) (hE : E.card≤t)
    (hagree : ∀ i, i∉E → w i=P.eval (x i)) :
    (conjugateHankel σ x w L t).mulVec
      (fun j : Fin (t+1) => (locator x E).coeff j.val)=0 := by
  have hloc : (locator x E).natDegree≤t := (locator_natDegree x E).trans_le hE
  have hpoint : ∀ i, (locator x E).eval (x i)*(w i+(0:F)*(0:F))=
      (locator x E).eval (x i)*P.eval (x i) := by
    intro i
    by_cases hi : i∈E
    · simp [locator_eval_zero x E i hi]
    · simp [hagree i hi]
  have hfirst := hankel_annihilates x hx w (fun _ => 0) 0 k L t hsize P (locator x E) hP hloc hpoint
  funext b
  have hh := congrArg (σ b.1) (congrFun hfirst b.2)
  have hcoef : ∀ j, σ b.1 ((locator x E).coeff j)=(locator x E).coeff j :=
    locator_coefficient_fixed (σ b.1) x (hfixed b.1) E
  simpa only [Matrix.mulVec,dotProduct,hankel,eval_add,eval_mul,eval_C,eval_X,zero_mul,
    add_zero,Pi.zero_apply,map_sum,map_mul,map_zero,hcoef,conjugateHankel] using hh

theorem locator_in_conjugate_space (σ : β → F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (k m t : ℕ) (hsize : k+m≤Fintype.card ι) (htm : t≤m)
    (P : F[X]) (hP : P.degree<k) (E : Finset ι) (hE : E.card≤t)
    (hagree : ∀ i, i∉E → w i=P.eval (x i)) :
    locator x E∈recurrenceSpace (fun b j => σ b (syndrome x w j)) m t := by
  apply (recurrenceSpace_matrix _ m t _).mpr
  refine ⟨(locator_natDegree x E).trans_le hE,?_⟩
  rw [recurrenceMatrixAll_conjugate]
  exact conjugate_locator_annihilates σ x w hx hfixed k (m-t) t (by omega) P hP E hE hagree

end
end FrobeniusLocator.Strata
end PackSource_ConjugateLocator

section PackSource_KernelTwoCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
local instance countDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The exact remaining geometric input to the one-root K2 consumer.
It counts actual SAME-SUPPORT bad slopes with a unique evaluated locator
on each punctured domain. No assertion of this property is made here. -/
def PuncturedRegularCap (σ : β → F →+* F) (x u v : ι → F) (k A m t : ℕ) : Prop :=
  ∀ (a : ι) (Γ : Finset F),
    (∀ γ∈Γ, Principal.BadSlope (fun i : {i // i≠a} => x i.val)
      (fun i => u i.val) (fun i => v i.val) k A γ) →
    (∀ γ∈Γ, Module.finrank F (LinearMap.ker (recurrenceMatrixAll
      (fun b j => σ b (syndrome (fun i : {i // i≠a} => x i.val)
        (fun i => u i.val+γ*v i.val) j)) (m-1) (t-1)).mulVecLin)=1) →
    Γ.card≤(Fintype.card ι-1)^3

/-- Complete elementary K2 consumer on literal bad slopes and evaluated
kernels. Its ONLY counting input is the explicitly named punctured
regular-slope cap. Gcd, usable roots, puncturing, same-support badness,
and the incidence division are all proved here. -/
theorem nonprincipal_two_kernel_count (σ : β → F →+* F) (x u v : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (k A m L t : ℕ) (hkm : k+m=Fintype.card ι) (hm : m=L+t)
    (hA : A=k+L) (hkA : k<A) (ht : 1≤t)
    (hregular : PuncturedRegularCap σ x u v k A m t)
    (Γ : Finset F) (hbad : ∀ γ∈Γ, Principal.BadSlope x u v k A γ)
    (hnull : ∀ γ∈Γ, Module.finrank F (LinearMap.ker
      (recurrenceMatrixAll (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) m t).mulVecLin)=2)
    (hnon : ∀ γ∈Γ, NonprincipalSpace
      (recurrenceSpace (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) m t) t) :
    Γ.card≤kernelTwoPrice (Fintype.card ι) L := by
  let G := {γ // γ∈Γ}
  have hwitness : ∀ γ : G, ∃ S : Finset ι, S.card=A ∧
      ExtendsOn x (fun i => u i+γ.val*v i) k S ∧
      ¬(ExtendsOn x u k S ∧ ExtendsOn x v k S) := by
    intro γ
    exact Principal.bad_slope_exact x hx u v k A hkA γ.val (hbad γ.val γ.property)
  choose W hWcard hWdec hWbad using hwitness
  have hPexists : ∀ γ : G, ∃ P : F[X], P.degree<k ∧
      ∀ i∈W γ, P.eval (x i)=u i+γ.val*v i := hWdec
  choose P hPdeg hPval using hPexists
  let E : G → Finset ι := fun γ => Finset.univ\W γ
  have hEcard (γ : G) : (E γ).card=t := by
    simp only [E,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hWcard]
    omega
  have hloc (γ : G) : locator x (E γ)∈recurrenceSpace
      (fun b j => σ b (syndrome x (fun i => u i+γ.val*v i) j)) m t := by
    apply locator_in_conjugate_space σ x _ hx hfixed k m t hkm.le (by omega) (P γ) (hPdeg γ)
      (E γ) (hEcard γ).le
    intro i hi
    have hiW : i∈W γ := by simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hi
    exact (hPval γ i hiW).symm
  have husable : ∀ γ : G, ∃ T : Finset ι, T⊆E γ ∧ L+1≤T.card ∧
      ∀ i∈T, Module.finrank F (LinearMap.ker (AppendConstants.appendOne
        (recurrenceMatrixAll (fun b j => σ b (syndrome x (fun i => u i+γ.val*v i) j)) m t)
        (fun j => x i^j.val)).mulVecLin)=1 := by
    intro γ
    exact nonprincipal_two_kernel_usable_roots _ m t L hm x hx
      (hnull γ.val γ.property) (hnon γ.val γ.property) (E γ) (hEcard γ) (hloc γ)
  choose T hTE hTcard hTnull using husable
  let usable : F → Finset ι := fun γ => if h : γ∈Γ then T ⟨γ,h⟩ else ∅
  have hroots : ∀ γ∈Γ, L+1≤(usable γ).card := by
    intro γ hγ
    simpa only [usable,dif_pos hγ] using hTcard ⟨γ,hγ⟩
  have hnode (a : ι) : (Γ.filter (fun γ => a∈usable γ)).card≤(Fintype.card ι-1)^3 := by
    apply hregular a
    · intro γ hγ
      obtain ⟨hγΓ,ha⟩ := Finset.mem_filter.mp hγ
      let g : G := ⟨γ,hγΓ⟩
      have haT : a∈T g := by simpa only [usable,dif_pos hγΓ] using ha
      have haE : a∈E g := hTE g haT
      have haW : a∉W g := (Finset.mem_sdiff.mp haE).2
      exact puncture_bad_witness x u v k A γ (W g) (hWcard g).ge (hWdec g) (hWbad g) a haW
    · intro γ hγ
      obtain ⟨hγΓ,ha⟩ := Finset.mem_filter.mp hγ
      let g : G := ⟨γ,hγΓ⟩
      have haT : a∈T g := by simpa only [usable,dif_pos hγΓ] using ha
      rw [actual_punctured_nullity_eq_appended σ x (fun i => u i+γ*v i) hx hfixed m t a ht (by omega)]
      exact hTnull g a haT
  exact one_root_incidence_count Γ usable L ((Fintype.card ι-1)^3) hroots hnode

/-- Exact native integer, still explicitly conditional on the geometric
PuncturedRegularCap. -/
theorem native_nonprincipal_two_kernel_count (σ : β → F →+* F) (x u v : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (hn : Fintype.card ι=262144)
    (hregular : PuncturedRegularCap σ x u v 131072 180236 131072 81908)
    (Γ : Finset F) (hbad : ∀ γ∈Γ, Principal.BadSlope x u v 131072 180236 γ)
    (hnull : ∀ γ∈Γ, Module.finrank F (LinearMap.ker
      (recurrenceMatrixAll (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) 131072 81908).mulVecLin)=2)
    (hnon : ∀ γ∈Γ, NonprincipalSpace
      (recurrenceSpace (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) 131072 81908) 81908) :
    Γ.card≤96050288617518050 := by
  have h := nonprincipal_two_kernel_count σ x u v hx hfixed 131072 180236 131072 49164 81908
    (by omega) (by decide) (by decide) (by decide) (by decide) hregular Γ hbad hnull hnon
  rw [hn,native_kernel_two_price] at h
  exact h

end
end FrobeniusLocator.Strata
end PackSource_KernelTwoCount

section PackSource_PolynomialFamilyOutput
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Interpolate node values that are themselves polynomials in a separate
parameter. Inner X is the slope parameter, outer X is the RS coordinate. -/
def interpolationFamily (x : ι → F) (w : ι → F[X]) : Polynomial (Polynomial F) :=
  ∑ i, Polynomial.C (w i)*(Lagrange.basis Finset.univ x i).map (Polynomial.C : F →+* F[X])

theorem interpolationFamily_map_eval (x : ι → F) (w : ι → F[X]) (γ : F) :
    (interpolationFamily x w).map (Polynomial.evalRingHom γ)=
      Lagrange.interpolate Finset.univ x (fun i => (w i).eval γ) := by
  have hcomp : (Polynomial.evalRingHom γ).comp (Polynomial.C : F →+* F[X])=RingHom.id F := by ext c; simp
  simp only [interpolationFamily,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_map,hcomp,Polynomial.map_id,Lagrange.interpolate_apply,Polynomial.coe_evalRingHom]

theorem interpolationFamily_node (x : ι → F) (hx : Function.Injective x)
    (w : ι → F[X]) (a : ι) :
    (interpolationFamily x w).eval (Polynomial.C (x a))=w a := by
  classical
  simp only [interpolationFamily,eval_finsetSum,eval_mul,eval_C,Polynomial.eval_map_apply]
  rw [Finset.sum_eq_single a]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ a)]
    simp
  · intro b hb hba
    rw [Lagrange.eval_basis_of_ne hba (Finset.mem_univ a)]
    simp
  · simp

theorem interpolationFamily_coefficient_degree (x : ι → F) (w : ι → F[X]) (B : ℕ)
    (hw : ∀ i, (w i).natDegree≤B) (j : ℕ) :
    ((interpolationFamily x w).coeff j).natDegree≤B := by
  simp only [interpolationFamily,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C,add_zero] using hw i)

/-- Bounded parameter degree upgrades the pointwise RS outputs to ONE
polynomial family of the same strict X-degree. The field-size condition
is explicit and will be checked at the native sextic field. -/
theorem interpolationFamily_degree_lt [Fintype F] (x : ι → F) (hx : Function.Injective x)
    (w : ι → F[X]) (D B : ℕ) (hD : D≤Fintype.card ι)
    (hw : ∀ i, (w i).natDegree≤B) (hB : B<Fintype.card F)
    (houtput : ∀ γ : F, ∃ R : F[X], R.degree<D ∧ ∀ i, R.eval (x i)=(w i).eval γ) :
    (interpolationFamily x w).degree<D := by
  classical
  apply (Polynomial.degree_lt_iff_coeff_zero _ D).mpr
  intro j hj
  have hzero : ∀ γ : F, ((interpolationFamily x w).coeff j).eval γ=0 := by
    intro γ
    obtain ⟨R,hR,hRv⟩ := houtput γ
    have hRlt : R.degree<(Fintype.card ι : ℕ) := hR.trans_le (by exact_mod_cast hD)
    have heq : R=(interpolationFamily x w).map (Polynomial.evalRingHom γ) := by
      rw [interpolationFamily_map_eval]
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hx.injOn
        (by simpa only [Finset.card_univ] using hRlt)
        (Lagrange.degree_interpolate_lt _ hx.injOn)
      intro i hi
      rw [Lagrange.eval_interpolate_at_node _ hx.injOn hi,hRv i]
    have hc := congrArg (fun Q : F[X] => Q.coeff j) heq
    rw [Polynomial.coeff_map] at hc
    have hrzero : R.coeff j=0 := Polynomial.coeff_eq_zero_of_degree_lt
      (hR.trans_le (by exact_mod_cast hj))
    exact (hc.symm.trans hrzero)
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id hzero
    ((interpolationFamily_coefficient_degree x w B hw j).trans_lt hB)

end
end FrobeniusLocator.Strata
end PackSource_PolynomialFamilyOutput

section PackSource_ResidualRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- After principal and nullity-two fibers have been removed, EVERY
remaining normal decoder has the advertised q<=r-3 and actual-error lower
bound. This is an implication of actual kernel predicates, not a new
residual-count hypothesis. -/
theorem normal_nonprincipal_residual_rank (σ : F →+* F) (x w : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ i, σ (x i)=x i)
    (k L t H r : ℕ) (hsize : k+L+t=Fintype.card ι) (hH : H<L)
    (hbalance : L+H+r=t+1) (U V R : F[X]) (hpair : U≠0 ∨ V≠0)
    (rel : TwistedRelation σ x w k H U V R)
    (P : F[X]) (hP : P.degree<k) (E : Finset ι) (hE : E.card≤t)
    (hagree : ∀ i, i∉E → w i=P.eval (x i))
    (hexact : ∀ i∈E, w i≠P.eval (x i))
    (hnormal : (conjugateHankel (twoConjugations σ) x w L t).rank=L+H)
    (hnon : NonprincipalSpace (recurrenceSpace
      (fun b j => threeConjugations σ b (syndrome x w j)) (L+t) t) t)
    (hdim : 3≤Module.finrank F (LinearMap.ker
      (conjugateHankel (threeConjugations σ) x w L t).mulVecLin)) :
    let G := GCDMonoid.gcd U V
    let u := U/G
    let v := V/G
    let d := max u.natDegree v.natDegree
    let q := d-(GCDMonoid.gcd u (v.map σ)).natDegree
    q≤r-3 ∧ L+H+q+1≤E.card := by
  let G := GCDMonoid.gcd U V
  let u := U/G
  let v := V/G
  let d := max u.natDegree v.natDegree
  let q := d-(GCDMonoid.gcd u (v.map σ)).natDegree
  let M := conjugateHankel (threeConjugations σ) x w L t
  have hrank : M.rank=min E.card (L+H+q) := normal_slope_three_rank σ x w hx hfixed k L t H
    hsize.le hH U V R hpair rel P hP E hE hagree hexact hnormal
  have hfix3 : ∀ b i, threeConjugations σ b (x i)=x i := by
    intro b i
    fin_cases b <;> simp [threeConjugations,hfixed,RingHom.comp_apply]
  have hnotfull : M.rank≠E.card := by
    intro hfull
    have hfactor := conjugateHankel_error_rank (threeConjugations σ) x w hx hfix3
      P k L t hP hsize.le E (by omega) hagree
    have herr : (conjugateErrors (threeConjugations σ) (fun i : E => x i.val)
      (fun i : E => w i.val-P.eval (x i.val)) L).rank=E.card := hfactor.symm.trans hfull
    have hp := full_error_rank_principal (threeConjugations σ) x w hx hfix3 k (L+t) t
      (by omega) (by omega) P hP E hE hagree (by rw [show L+t-t=L by omega]; exact herr)
    apply hnon
    refine ⟨locator x E,(locator_monic x E).ne_zero,?_,?_⟩
    · rw [locator_natDegree]
      exact hE
    · simpa only [locator_natDegree] using hp
  change 3≤Module.finrank F (LinearMap.ker M.mulVecLin) at hdim
  have hn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank+Module.finrank F (LinearMap.ker M.mulVecLin)=_ at hn
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hn
  change q≤r-3 ∧ L+H+q+1≤E.card
  omega

end
end FrobeniusLocator.Strata
end PackSource_ResidualRank

section PackSource_FiberPrincipal
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]

theorem constant_multiple_space (f : F[X]) :
    (Polynomial.degreeLT F 1).map (polynomialMul f)=F ∙ f := by
  apply le_antisymm
  · rintro _ ⟨Q,hQ,rfl⟩
    have hn := Principal.degreeLT_natDegree_le (q := 0) ⟨Q,hQ⟩
    have hQC : Q=C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by change Q.natDegree≤0 at hn; omega)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨Q.coeff 0,?_⟩
    change (Q.coeff 0) • f=f*Q
    calc
      (Q.coeff 0) • f=f*C (Q.coeff 0) := by simp only [Polynomial.smul_eq_C_mul,mul_comm]
      _ = f*Q := congrArg (fun R : F[X] => f*R) hQC.symm
  · intro P hP
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hP
    refine ⟨C c,?_,?_⟩
    · exact Polynomial.mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by simp))
    · change f*C c=P
      rw [← hc,Polynomial.smul_eq_C_mul]
      ring

/-- An evaluated kernel line containing a full-degree witness is principal. -/
theorem line_is_principal (K : Submodule F F[X]) (t : ℕ)
    (hK : Module.finrank F K=1) (f : F[X]) (hf : f∈K) (hf0 : f≠0) (hfd : f.natDegree=t) :
    ¬NonprincipalSpace K t := by
  letI : FiniteDimensional F K := FiniteDimensional.of_finrank_pos (by omega)
  have hline : F ∙ f≤K := Submodule.span_le.mpr (by intro P hP; rw [Set.mem_singleton_iff] at hP; exact hP ▸ hf)
  have heq : F ∙ f=K := Submodule.eq_of_le_of_finrank_eq hline ((finrank_span_singleton hf0).trans hK.symm)
  intro hn
  apply hn
  refine ⟨f,hf0,hfd.le,?_⟩
  rw [hfd,Nat.sub_self,zero_add,constant_multiple_space]
  exact heq.symm

/-- A nonzero full-degree witness and nonprincipality exclude nullities
zero and one; no dimension-two classification theorem is assumed. -/
theorem nonprincipal_nullity_ge_two (s : β → ℕ → F) (m t : ℕ)
    (hnon : NonprincipalSpace (recurrenceSpace s m t) t)
    (f : F[X]) (hf : f∈recurrenceSpace s m t) (hf0 : f≠0) (hfd : f.natDegree=t) :
    2≤Module.finrank F (LinearMap.ker (recurrenceMatrixAll s m t).mulVecLin) := by
  let K := recurrenceSpace s m t
  letI : FiniteDimensional F K := Module.Finite.equiv (kernelPolynomialEquiv s m t)
  have hpos : 0<Module.finrank F K := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨f,hf⟩,by intro hz; exact hf0 (congrArg Subtype.val hz)⟩
  have hne : Module.finrank F K≠1 := by
    intro hone
    exact line_is_principal K t hone f hf hf0 hfd hnon
  have heq := recurrenceSpace_finrank s m t
  change Module.finrank F K=_ at heq
  omega

end
end FrobeniusLocator.Strata
end PackSource_FiberPrincipal

section PackSource_LemmaTProfile
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Literal connection from the two-active level Hilbert function to the
polynomial relation matrix's actual generic nullity. -/
theorem generic_relation_line_of_level (p : ℕ) (x u v : ι → F)
    (m a b c : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b<c) (hc2 : 1<c)
    (hHF : HasLevelHilbertFunction
      (fun b j => algebraMap F[X] (GenericLayer.GenericField F)
        (Principal.parameterSyndromes p x u v b j)) m a b c) :
    GenericLayer.genericNullity (parameterRelation p x u v m (m+1-c))=1 := by
  change Module.finrank (GenericLayer.GenericField F) (LinearMap.ker
    ((parameterRelation p x u v m (m+1-c)).map (algebraMap F[X] (GenericLayer.GenericField F))).mulVecLin)=1
  rw [parameterRelation_map]
  exact minimal_relation_line _ m a b c hc hsum ha hb hc2 hHF

/-- The exact relation-degree/nullity balance at an arbitrary two-active
profile. No existence of the binary level resolution is asserted. -/
theorem relation_degree_nullity_balance (m L t r a b c : ℕ)
    (hm : m=L+t) (hc : c≤m) (hsum : a+b+c=2*m+2) (hr : r+a+b=2*t+2) :
    L+(m+1-c)+r=t+1 := by omega

theorem native_minimal_relation_degree (r a b c : ℕ) (hc : c≤131072)
    (hsum : a+b+c=262146) (hr : r+a+b=163818) (hr7 : 7≤r) :
    49164+(131073-c)+r=81909 ∧ 131073-c≤32738 ∧ 131073-c<49164 := by omega

/-- The complementary transpose is injective BELOW the minimum relation
index. Thus the native relation factory uses the true minimum degree,
conditional on the stated level Hilbert function. -/
theorem no_relation_below_minimal {K : Type} [Field K] (s : Fin 2 → ℕ → K)
    (m a b c H : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b≤c) (hH : H<m+1-c)
    (hHF : HasLevelHilbertFunction s m a b c) :
    Module.finrank K (LinearMap.ker (relationMatrix s m H).mulVecLin)=0 := by
  have hHm : H<m := by omega
  have hd := complementary_nullities s m H
  rw [hHF H hHm] at hd
  omega

end
end FrobeniusLocator.Strata
end PackSource_LemmaTProfile

section PackSource_TwistedPolynomialFamily
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]

theorem assemble_nodePolynomial (H : ℕ) (q : Fin (H+1) → F[X]) (a : F) :
    (Principal.assemble q).eval (Polynomial.C a)=Principal.nodePolynomial q a := by
  simp only [Principal.assemble,eval_finsetSum,eval_monomial,Principal.nodePolynomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.C_pow]
  ring

/-- The polynomial-parameter form of Lemma T, including ONE common
output polynomial R_Z(X). The finite-field size guard is explicit. -/
theorem polynomial_twisted_output_of_section (p : ℕ) [ExpChar F p] (hp : 1≤p)
    (x u v : ι → F) (hx : Function.Injective x) (k H δ : ℕ)
    (hsize : k+H≤Fintype.card ι) (hcard : δ+p<Fintype.card F)
    (Q : Fin 2 × Fin (H+1) → F[X]) (hQdeg : ∀ b, (Q b).natDegree≤δ)
    (hsection : ∀ γ : F, ∃ R : F[X], TwistedRelation (frobenius F p) x (fun i => u i+γ*v i) k H
      (Principal.assemble (fun j => (Q (0,j)).eval γ))
      (Principal.assemble (fun j => (Q (1,j)).eval γ)) R) :
    ∃ R : Polynomial (Polynomial F), R.degree<(k+H : ℕ) ∧ ∀ i,
      (Principal.assemble (fun j => Q (0,j))).eval (Polynomial.C (x i))*
        (Polynomial.C (u i)+(Polynomial.X : F[X])*Polynomial.C (v i))+
      (Principal.assemble (fun j => Q (1,j))).eval (Polynomial.C (x i))*
        (Polynomial.C (u i^p)+(Polynomial.X : F[X])^p*Polynomial.C (v i^p))=
      R.eval (Polynomial.C (x i)) := by
  let word : ι → F[X] := fun i =>
    Principal.nodePolynomial (fun j => Q (0,j)) (x i)*(C (u i)+(Polynomial.X : F[X])*C (v i))+
    Principal.nodePolynomial (fun j => Q (1,j)) (x i)*(C (u i^p)+(Polynomial.X : F[X])^p*C (v i^p))
  have hword : ∀ i, (word i).natDegree≤δ+p := by
    intro i
    have h0 : (C (u i)+(Polynomial.X : F[X])*C (v i)).natDegree≤1 := by compute_degree
    have h1 : (C (u i^p)+(Polynomial.X : F[X])^p*C (v i^p)).natDegree≤p := by compute_degree
    have hU := Principal.nodePolynomial_natDegree_le (fun j => Q (0,j)) (fun j => hQdeg (0,j)) (x i)
    have hV := Principal.nodePolynomial_natDegree_le (fun j => Q (1,j)) (fun j => hQdeg (1,j)) (x i)
    exact (Polynomial.natDegree_add_le _ _).trans (max_le
      (Polynomial.natDegree_mul_le.trans (by omega)) (Polynomial.natDegree_mul_le.trans (by omega)))
  have houtput : ∀ γ : F, ∃ R : F[X], R.degree<(k+H : ℕ) ∧ ∀ i, R.eval (x i)=(word i).eval γ := by
    intro γ
    obtain ⟨R,hR⟩ := hsection γ
    refine ⟨R,hR.degree_R,?_⟩
    intro i
    have hU := Principal.nodePolynomial_eval (fun j => Q (0,j)) (x i) γ
    have hV := Principal.nodePolynomial_eval (fun j => Q (1,j)) (x i) γ
    rw [Principal.specialize_eq_assemble] at hU hV
    have hpower : (u i+γ*v i)^p=u i^p+γ^p*v i^p := by
      have hh := map_add (frobenius F p) (u i) (γ*v i)
      rw [map_mul] at hh
      simpa only [frobenius_def] using hh
    dsimp only [word]
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_pow]
    rw [hU,hV,← hpower]
    exact (hR.nodes i).symm
  refine ⟨interpolationFamily x word,interpolationFamily_degree_lt x hx word (k+H) (δ+p)
    hsize hword hcard houtput,?_⟩
  intro i
  rw [assemble_nodePolynomial,assemble_nodePolynomial,interpolationFamily_node x hx word i]

/-- Full primitive polynomial Lemma-T section from the ACTUAL generic
relation-line hypothesis. Minimality/uniqueness may be supplied by
`generic_relation_line_of_level`; its Hilbert function is still explicit. -/
theorem lemmaT_polynomial_family (p : ℕ) [ExpChar F p] (hp : 1≤p)
    (x u v : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (k m H : ℕ) (hkm : k+m=Fintype.card ι) (hH : H≤m)
    (hcard : (2*H+2)*p<Fintype.card F)
    (hnull : GenericLayer.genericNullity (parameterRelation p x u v m H)=1) :
    ∃ (Q : Fin 2 × Fin (H+1) → F[X]) (R : Polynomial (Polynomial F)),
      PrimitiveVector.IsPrimitive Q ∧ (parameterRelation p x u v m H).mulVec Q=0 ∧
      (∀ b, (Q b).natDegree≤(2*H+1)*p) ∧ R.degree<(k+H : ℕ) ∧
      ∀ i,
        (Principal.assemble (fun j => Q (0,j))).eval (Polynomial.C (x i))*
          (Polynomial.C (u i)+(Polynomial.X : F[X])*Polynomial.C (v i))+
        (Principal.assemble (fun j => Q (1,j))).eval (Polynomial.C (x i))*
          (Polynomial.C (u i^p)+(Polynomial.X : F[X])^p*Polynomial.C (v i^p))=
        R.eval (Polynomial.C (x i)) := by
  obtain ⟨Q,hprim,hQ,hdeg,hsection⟩ := twisted_relation_at_every_slope p hp x u v hx hfixed k m H hkm hH hnull
  have hcard' : (2*H+1)*p+p<Fintype.card F := by nlinarith [hcard]
  obtain ⟨R,hR,hRv⟩ := polynomial_twisted_output_of_section p hp x u v hx k H ((2*H+1)*p)
    (by omega) hcard' Q hdeg (by intro γ; obtain ⟨R,_,hR⟩ := hsection γ; exact ⟨R,hR⟩)
  exact ⟨Q,R,hprim,hQ,hdeg,hR,hRv⟩

end
end FrobeniusLocator.Strata
end PackSource_TwistedPolynomialFamily

section PackSource_BookedLedger
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
local instance ledgerDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def fiberSequence (σ : β → F →+* F) (x u v : ι → F) (γ : F) : β → ℕ → F :=
  fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)

def principalFiber (σ : β → F →+* F) (x u v : ι → F) (m t : ℕ) (γ : F) : Prop :=
  ¬NonprincipalSpace (recurrenceSpace (fiberSequence σ x u v γ) m t) t

def fiberNullity (σ : β → F →+* F) (x u v : ι → F) (m t : ℕ) (γ : F) : ℕ :=
  Module.finrank F (LinearMap.ker (recurrenceMatrixAll (fiberSequence σ x u v γ) m t).mulVecLin)

/-- Exact principal three-block count still owed by the geometric theorem.
This is an explicit predicate, NOT a theorem or new axiom. -/
def EvaluatedPrincipalCap (σ : β → F →+* F) (x u v : ι → F) (k A m t : ℕ) : Prop :=
  ∀ Γ : Finset F, (∀ γ∈Γ, Principal.BadSlope x u v k A γ) →
    (∀ γ∈Γ, principalFiber σ x u v m t γ) → Γ.card≤principalThreePrice (Fintype.card ι) t

/-- Badness supplies a full-degree split locator, so every nonprincipal
fiber has nullity at least two. -/
theorem bad_nonprincipal_nullity_ge_two (σ : β → F →+* F) (x u v : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ b i, σ b (x i)=x i)
    (k A m L t : ℕ) (hkm : k+m=Fintype.card ι) (hm : m=L+t) (hA : A=k+L)
    (hkA : k<A) (γ : F) (hbad : Principal.BadSlope x u v k A γ)
    (hnon : NonprincipalSpace (recurrenceSpace (fiberSequence σ x u v γ) m t) t) :
    2≤fiberNullity σ x u v m t γ := by
  obtain ⟨S,hS,⟨P,hP,hPv⟩,_⟩ := Principal.bad_slope_exact x hx u v k A hkA γ hbad
  let E := Finset.univ\S
  have hE : E.card=t := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ,hS]
    omega
  have hloc : locator x E∈recurrenceSpace (fiberSequence σ x u v γ) m t := by
    apply locator_in_conjugate_space σ x _ hx hfixed k m t hkm.le (by omega) P hP E hE.le
    intro i hi
    have hiS : i∈S := by simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hi
    exact (hPv i hiS).symm
  exact nonprincipal_nullity_ge_two _ m t hnon (locator x E) hloc (locator_monic x E).ne_zero
    ((locator_natDegree x E).trans hE)

/-- The exact requested residual count, after the two BOOKED geometric
predicates have been imported. Normality refers to the actual old K2. -/
def NormalResidualCap6917 (p : ℕ) [ExpChar F p] (x u v : ι → F) (r : ℕ) : Prop :=
  ∀ Γ : Finset F, (∀ γ∈Γ, Principal.BadSlope x u v 131072 180236 γ) →
    (∀ γ∈Γ, ((stacked p x u v 49164 81908).map (evalRingHom γ)).rank=81909-r) →
    (∀ γ∈Γ, NonprincipalSpace (recurrenceSpace
      (fiberSequence (threeConjugations (frobenius F p)) x u v γ) 131072 81908) 81908) →
    (∀ γ∈Γ, 3≤fiberNullity (threeConjugations (frobenius F p)) x u v 131072 81908 γ) →
    Γ.card≤122925228561990328

/-- Native additive ledger on actual bad slopes. PrincipalCap and
PuncturedRegularCap remain EXPLICIT geometric hypotheses. Thus this
statement does not claim the residual is the only remaining formal gap. -/
theorem native_booked_strata_count [ExpChar F 2130706433]
    (x u v : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^2130706433=x i)
    (hn : Fintype.card ι=262144) (r : ℕ) (hr7 : 7≤r)
    (hr : GenericLayer.genericRank (stacked 2130706433 x u v 49164 81908)=81909-r)
    (hfirst : GenericLayer.genericRank (hankel x u v 49164 81908)=49164)
    (hprincipal : EvaluatedPrincipalCap (threeConjugations (frobenius F 2130706433)) x u v
      131072 180236 131072 81908)
    (hregular : PuncturedRegularCap (threeConjugations (frobenius F 2130706433)) x u v
      131072 180236 131072 81908)
    (hres : NormalResidualCap6917 2130706433 x u v r)
    (Γ : Finset F) (hbad : ∀ γ∈Γ, Principal.BadSlope x u v 131072 180236 γ) :
    Γ.card≤244996694950342997 := by
  let σ := threeConjugations (frobenius F 2130706433)
  let drop : F → Prop := fun γ => ((stacked 2130706433 x u v 49164 81908).map (evalRingHom γ)).rank≠81909-r
  let princ := principalFiber σ x u v 131072 81908
  let two : F → Prop := fun γ => fiberNullity σ x u v 131072 81908 γ=2
  have hfix : ∀ b i, σ b (x i)=x i := by
    intro b i
    fin_cases b <;> simp [σ,threeConjugations,RingHom.comp_apply,frobenius_def,hfixed]
  have hD : (Γ.filter drop).card≤69755067252718 :=
    native_rank_exception_count x u v r hr7 hr hfirst _ (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hP : (Γ.filter (fun γ => ¬drop γ ∧ princ γ)).card≤25951422703581901 := by
    have hh := hprincipal (Γ.filter (fun γ => ¬drop γ ∧ princ γ))
      (fun γ hγ => hbad γ (Finset.mem_filter.mp hγ).1)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2.2)
    rw [hn,native_principal_three_price] at hh
    exact hh
  have hJ : (Γ.filter (fun γ => ¬drop γ ∧ ¬princ γ ∧ two γ)).card≤96050288617518050 := by
    apply native_nonprincipal_two_kernel_count σ x u v hx hfix hn hregular
    · intro γ hγ; exact hbad γ (Finset.mem_filter.mp hγ).1
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2.2.2
    · intro γ hγ
      exact Classical.not_not.mp (Finset.mem_filter.mp hγ).2.2.1
  have hR : (Γ.filter (fun γ => ¬drop γ ∧ ¬princ γ ∧ ¬two γ)).card≤122925228561990328 := by
    apply hres
    · intro γ hγ; exact hbad γ (Finset.mem_filter.mp hγ).1
    · intro γ hγ; exact Classical.not_not.mp (Finset.mem_filter.mp hγ).2.1
    · intro γ hγ; exact Classical.not_not.mp (Finset.mem_filter.mp hγ).2.2.1
    · intro γ hγ
      obtain ⟨hγΓ,hd,hp,ht⟩ := Finset.mem_filter.mp hγ
      have hnong := Classical.not_not.mp hp
      have htwo := bad_nonprincipal_nullity_ge_two σ x u v hx hfix 131072 180236 131072 49164 81908
        (by omega) (by decide) (by decide) (by decide) γ (hbad γ hγΓ) hnong
      change ¬fiberNullity σ x u v 131072 81908 γ=2 at ht
      change 3≤fiberNullity σ x u v 131072 81908 γ
      omega
  exact (four_strata_count Γ drop princ two 69755067252718 25951422703581901 96050288617518050
    122925228561990328 hD hP hJ hR).trans_eq (by norm_num)

end
end FrobeniusLocator.Strata
end PackSource_BookedLedger

section PackSource_PrincipalKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance decidablePrincipalKernel (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Principal homogeneous module data after removing the fixed domain
factor. Nullity and primitive/cofactor bounds are explicit inputs. -/
structure MovingPrincipalCertificate (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (Δ : F[X]) where
  fixedRoots : Finset ι
  movingDegree : ℕ
  quotientDegree : ℕ
  moving_pos : 0 < movingDegree
  degree_sum : fixedRoots.card + movingDegree + quotientDegree = t
  coefficients : Fin (movingDegree+1) → F[X]
  coefficient_degree : ∀ j, (coefficients j).natDegree ≤ p*movingDegree
  primitive_specialization : ∀ γ, specialize coefficients γ ≠ 0
  no_additional_fixed_root : ∀ i, i ∉ fixedRoots → nodePolynomial coefficients (x i) ≠ 0
  normal_nullity : ∀ γ, Δ.eval γ ≠ 0 →
    Module.finrank F (LinearMap.ker
      ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVecLin) = quotientDegree+1
  multiples_annihilate : ∀ γ (Q : Polynomial.degreeLT F (quotientDegree+1)),
    ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVec
      (multipleCoefficients (locator x fixedRoots * specialize coefficients γ)
        quotientDegree t Q) = 0

/-- Principal generic kernels are cheap at arbitrary nullity. The
certificate states the module, cofactor, primitive, and normal-rank data;
the split-locator/root-incidence conclusion is fully proved here. -/
theorem principal_bad_count (p : ℕ) [ExpChar F p]
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (u v : ι → F) (k A L t δ : ℕ) (hkA : k < A)
    (hL : k+L=A) (ht : A+t=Fintype.card ι)
    (Δ : F[X]) (hΔ : Δ ≠ 0) (hΔdeg : Δ.natDegree ≤ δ)
    (cert : MovingPrincipalCertificate p x u v L t Δ)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) :
    Γ.card ≤ δ+p*(Fintype.card ι-cert.fixedRoots.card) := by
  classical
  let H := cert.fixedRoots
  let d := cert.movingDegree
  let q := cert.quotientDegree
  let vcoeff := cert.coefficients
  let V := specialize vcoeff
  have hroots (γ : F) (hγΓ : γ ∈ Γ) (hγΔ : Δ.eval γ ≠ 0) :
      d ≤ (Finset.univ.filter
        (fun i : {i // i ∉ H} => (V γ).eval (x i.val) = 0)).card := by
    obtain ⟨T,hT,⟨P,hP,hPv⟩,hnonjoint⟩ :=
      bad_slope_exact x hx u v k A hkA γ (hΓ γ hγΓ)
    let S := Finset.univ \ T
    have hScard : S.card = t := by
      dsimp [S]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, hT]
      omega
    have hagree : ∀ i, i ∉ S → u i+γ*v i=P.eval (x i) := by
      intro i hi
      have hiT : i ∈ T := by simpa only [S, Finset.mem_sdiff, Finset.mem_univ,
        true_and, not_not] using hi
      exact (hPv i hiT).symm
    have hker := locator_annihilates_stacked p x hx hfixed u v γ k L t (by omega)
      P hP S (by omega) hagree
    let g := locator x H * V γ
    have hg : g ≠ 0 := mul_ne_zero (locator_monic x H).ne_zero
      (cert.primitive_specialization γ)
    have hga : g.natDegree ≤ H.card+d := by
      exact Polynomial.natDegree_mul_le.trans
        (by rw [locator_natDegree]; exact Nat.add_le_add_left (specialize_natDegree_le _ _) _)
    have hsize : H.card+d+q=t := cert.degree_sum
    obtain ⟨Q,hQ,hfactor⟩ := normal_kernel_factorization (H.card+d) q t
      ((stacked p x u v L t).map (Polynomial.evalRingHom γ)) g hg hga
      (by omega) (cert.normal_nullity γ hγΔ) (cert.multiples_annihilate γ)
      (locator x S) (by rw [locator_natDegree,hScard]) hker
    have hVdegree : (V γ).natDegree = d := by
      apply full_degree_of_factorization (locator x H) (V γ) Q H.card d q
        (locator_natDegree x H) (specialize_natDegree_le _ _) hQ
      rw [← hfactor, locator_natDegree, hScard, hsize]
    obtain ⟨hdiv,havoid⟩ := remove_fixed_factor x hx H S (V γ) Q hfactor
    rw [roots_outside_fixed_card x H (V γ) havoid,
      ← divisor_domain_roots x hx (S \ H) (V γ) hdiv, hVdegree]
  have hcount := principal_kernel_count
    (fun i : {i // i ∉ H} => x i.val) V
    (fun i : {i // i ∉ H} => nodePolynomial vcoeff (x i.val)) p d δ
    cert.moving_pos
    (fun i => cert.no_additional_fixed_root i.val i.property)
    (fun i => nodePolynomial_natDegree_le vcoeff cert.coefficient_degree (x i.val))
    (fun i γ => nodePolynomial_eval vcoeff (x i.val) γ)
    Δ hΔ hΔdeg Γ hroots
  have hcard : Fintype.card {i // i ∉ H} = Fintype.card ι-H.card := by simp
  simpa only [hcard] using hcount

end
end FrobeniusLocator.Principal
end PackSource_PrincipalKernel

section PackSource_ConstantKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance decidableConstant (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- A constant polynomial kernel vector separates the ordinary u,v rows. -/
theorem constant_vector_separates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t+1) → F)
    (hc : (stacked p x u v L t).mulVec (fun j => C (c j)) = 0) :
    (∀ i : Fin L, ∑ j : Fin (t+1), syndrome x u (i.val+j.val) * c j = 0) ∧
    (∀ i : Fin L, ∑ j : Fin (t+1), syndrome x v (i.val+j.val) * c j = 0) := by
  have hrow (i : Fin L) :
      ∑ j : Fin (t+1), (hankel x u v L t i j) * C (c j) = 0 := by
    have hi := congrFun hc (0,i)
    simpa [stacked, Matrix.mulVec, dotProduct] using hi
  have hu (i : Fin L) : ∑ j : Fin (t+1),
      syndrome x u (i.val+j.val) * c j = 0 := by
    have h := congrArg (Polynomial.eval (0:F)) (hrow i)
    simpa [hankel, Polynomial.eval_finsetSum] using h
  refine ⟨hu, fun i => ?_⟩
  have h := congrArg (Polynomial.eval (1:F)) (hrow i)
  simp only [hankel, Polynomial.eval_finsetSum, eval_mul, eval_add,
    eval_C, eval_X, one_mul, eval_zero] at h
  simp_rw [add_mul] at h
  rw [Finset.sum_add_distrib, hu i, zero_add] at h
  exact h

/-- The precise fixed-subspace normal-fiber contract. It is a mathematical
certificate, not an assertion that every polynomial matrix has one. -/
structure ConstantKernelCertificate (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (Δ : F[X]) where
  space : Submodule F (Fin (t+1) → F)
  generic_annihilates : ∀ c ∈ space,
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0
  normal_inclusion : ∀ γ, Δ.eval γ ≠ 0 → ∀ c,
    ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVec c = 0 → c ∈ space

/-- Fixed generic coefficient kernels have no normal MCA-bad slope. -/
theorem constant_kernel_no_normal_bad (p : ℕ) [ExpChar F p]
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A)
    (hL : k+L=A) (ht : A+t=Fintype.card ι)
    (Δ : F[X]) (hcert : ConstantKernelCertificate p x u v L t Δ)
    (γ : F) (hγ : Δ.eval γ ≠ 0) : ¬ BadSlope x u v k A γ := by
  intro hbad
  obtain ⟨T,hT,⟨P,hP,hPv⟩,hnonjoint⟩ := bad_slope_exact x hx u v k A hkA γ hbad
  let S := Finset.univ \ T
  have hScard : S.card = t := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, hT]
    omega
  have hagree : ∀ i, i ∉ S → u i+γ*v i=P.eval (x i) := by
    intro i hi
    have hiT : i ∈ T := by simpa only [S, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not] using hi
    exact (hPv i hiT).symm
  have hker := locator_annihilates_stacked p x hx hfixed u v γ k L t (by omega)
    P hP S (by omega) hagree
  have hmem := hcert.normal_inclusion γ hγ
    (fun j : Fin (t+1) => (locator x S).coeff j.val) hker
  obtain ⟨hu,hv⟩ := constant_vector_separates p x u v L t _
    (hcert.generic_annihilates _ hmem)
  have hEu := hankel_word_moments x u (locator x S) L t
    (by rw [locator_natDegree, hScard]) hu
  have hEv := hankel_word_moments x v (locator x S) L t
    (by rw [locator_natDegree, hScard]) hv
  have hU := extendsOn_of_locator_moments x hx u k L S (by omega) hEu
  have hV := extendsOn_of_locator_moments x hx v k L S (by omega) hEv
  have hcomp : Finset.univ \ S = T := by simp [S]
  rw [hcomp] at hU hV
  exact hnonjoint ⟨hU,hV⟩

theorem constant_kernel_count (p : ℕ) [ExpChar F p]
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t δ : ℕ) (hkA : k < A)
    (hL : k+L=A) (ht : A+t=Fintype.card ι)
    (Δ : F[X]) (hΔ : Δ ≠ 0) (hΔdeg : Δ.natDegree ≤ δ)
    (hcert : ConstantKernelCertificate p x u v L t Δ)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) : Γ.card ≤ δ := by
  apply le_trans (b := Δ.natDegree)
  · apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hΔ).mpr
    by_contra hn
    exact constant_kernel_no_normal_bad p x hx hfixed u v k A L t hkA hL ht
      Δ hcert γ hn (hΓ γ hγ)
  · exact hΔdeg

end
end FrobeniusLocator.Principal
end PackSource_ConstantKernel

section PackSource_TypeOne
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F J : Type*} [Field F]

/-- Type-one polynomial minors force proportional original syndrome rows. -/
theorem type_one_proportional (a b : J → F) (p : ℕ) (hp : 1 < p)
    (hminor : ∀ i j,
      ((C (a i) + (Polynomial.X : F[X]) * C (b i)) : F[X]) * (C (a j ^ p) + (Polynomial.X : F[X]) ^ p * C (b j ^ p)) =
      (C (a j) + (Polynomial.X : F[X]) * C (b j)) * (C (a i ^ p) + (Polynomial.X : F[X]) ^ p * C (b i ^ p))) :
    a = 0 ∨ ∃ c : F, ∀ i, b i = c * a i := by
  classical
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have han : ∃ j, a j ≠ 0 := by
    by_contra h
    apply ha
    funext j
    simpa using not_exists.mp h j
  obtain ⟨j, hj⟩ := han
  have hjp : a j ^ p ≠ 0 := pow_ne_zero _ hj
  refine ⟨b j / a j, fun i => ?_⟩
  have h0 := congrArg (fun q : F[X] => q.coeff 0) (hminor i j)
  have h1 := congrArg (fun q : F[X] => q.coeff 1) (hminor i j)
  have hpoly (i j : J) :
      ((C (a i) + (Polynomial.X : F[X]) * C (b i)) : F[X]) * (C (a j ^ p) + (Polynomial.X : F[X]) ^ p * C (b j ^ p)) =
      C (a i * a j ^ p) + C (b i * a j ^ p) * (Polynomial.X : F[X]) +
      C (a i * b j ^ p) * (Polynomial.X : F[X]) ^ p + C (b i * b j ^ p) * (Polynomial.X : F[X]) ^ (p+1) := by
    simp only [map_mul]
    ring
  rw [hpoly, hpoly] at h0 h1
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow] at h0 h1
  simp [show 0 ≠ p by omega] at h0
  simp [show 1 ≠ p by omega, show p ≠ 0 by omega] at h1
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hj).mpr
  apply (mul_right_inj' hjp).mp
  linear_combination (a j) * h1 - (b j) * h0

end
end FrobeniusLocator.Principal
end PackSource_TypeOne

section PackSource_TypeOneCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

def TypeOneSyndromes (x u v : ι → F) (k p : ℕ) : Prop :=
  ∀ i j : Fin (Fintype.card ι-k),
    ((C (syndrome x u i.val) + (Polynomial.X : F[X])*C (syndrome x v i.val)) *
      (C (syndrome x u j.val ^ p) + (Polynomial.X : F[X])^p*C (syndrome x v j.val ^ p))) =
    ((C (syndrome x u j.val) + (Polynomial.X : F[X])*C (syndrome x v j.val)) *
      (C (syndrome x u i.val ^ p) + (Polynomial.X : F[X])^p*C (syndrome x v i.val ^ p)))

/-- Type one of the two full syndrome functionals costs at most one
MCA-bad slope. No generic-rank or primitive-vector hypothesis remains. -/
theorem type_one_bad_count (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k A p : ℕ) (hk : k ≤ Fintype.card ι) (hp : 1 < p)
    (hminor : ∀ i j : Fin (Fintype.card ι-k),
      ((C (syndrome x u i.val) + (Polynomial.X : F[X])*C (syndrome x v i.val)) *
        (C (syndrome x u j.val ^ p) + (Polynomial.X : F[X])^p*C (syndrome x v j.val ^ p))) =
      ((C (syndrome x u j.val) + (Polynomial.X : F[X])*C (syndrome x v j.val)) *
        (C (syndrome x u i.val ^ p) + (Polynomial.X : F[X])^p*C (syndrome x v i.val ^ p))))
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) : Γ.card ≤ 1 := by
  have hprop := type_one_proportional
    (fun i : Fin (Fintype.card ι-k) => syndrome x u i.val)
    (fun i : Fin (Fintype.card ι-k) => syndrome x v i.val) p hp hminor
  rcases hprop with ha | ⟨c,hc⟩
  · have hu : ExtendsOn x u k Finset.univ := by
      apply extendsOn_of_syndrome_zero x hx u k hk
      intro j hj
      exact congrFun ha ⟨j,hj⟩
    apply bad_slope_card_le_one_of_relation x u v k A 1 0 (Or.inl one_ne_zero) _ Γ hΓ
    simpa using hu
  · have hrel : ExtendsOn x (fun i => (-c)*u i+v i) k Finset.univ := by
      apply extendsOn_of_syndrome_zero x hx _ k hk
      intro j hj
      have h := hc ⟨j,hj⟩
      have hl := syndrome_linear x u v (-c) 1 j
      simp only [one_mul] at hl
      rw [hl, h]
      ring
    apply bad_slope_card_le_one_of_relation x u v k A (-c) 1 (Or.inr one_ne_zero) _ Γ hΓ
    simpa only [one_mul] using hrel

end
end FrobeniusLocator.Principal
end PackSource_TypeOneCount

section PackSource_BadSlopeBridge
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]

theorem projected_mem_iff_extendsOn (x : ι ↪ F) (w : ι → F)
    (k : ℕ) [NeZero k] (T : Finset ι) :
    projectedWord w T ∈ projectedCodeSubmod (ReedSolomon.code x k) T ↔
      ExtendsOn x w k T := by
  classical
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  constructor
  · rintro ⟨c,hc,hproj⟩
    obtain ⟨P,hP,heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
    refine ⟨P,Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hP),?_⟩
    intro i hi
    have h := congrFun hproj ⟨i,hi⟩
    change w i = c i at h
    exact (heval i).trans h.symm
  · rintro ⟨P,hP,hPv⟩
    have hPn : P.natDegree < k := by
      by_cases h0 : P = 0
      · simpa [h0] using NeZero.pos k
      · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hP
    refine ⟨fun i => P.eval (x i), ?_, ?_⟩
    · exact ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨P,hPn,fun _ => rfl⟩
    · funext i
      exact (hPv i.val i.property).symm

/-- Preserve native nonjointness, not just native A-closeness. -/
theorem isMCA_implies_badSlope (x : ι ↪ F) (U : Fin 2 → ι → F)
    (k A : ℕ) [NeZero k] (δ : ℝ)
    (hthreshold : ∀ T : Finset ι,
      (Fintype.card ι : ℝ)*(1-δ) ≤ T.card → A ≤ T.card)
    (γ : F) (hmca : IsMCA (AffineLineGenerator F) (ReedSolomon.code x k) γ U δ) :
    BadSlope x (U 0) (U 1) k A γ := by
  classical
  obtain ⟨T,hT,hcomb,j,hj⟩ := hmca
  refine ⟨T,hthreshold T hT,?_,?_⟩
  · apply (projected_mem_iff_extendsOn x _ k T).mp
    simpa [AffineLineGenerator, Fin.sum_univ_two, smul_eq_mul, mul_comm] using hcomb
  · intro h
    fin_cases j
    · exact hj ((projected_mem_iff_extendsOn x _ k T).mpr h.1)
    · exact hj ((projected_mem_iff_extendsOn x _ k T).mpr h.2)

end
end FrobeniusLocator.Principal
end PackSource_BadSlopeBridge

section PackSource_PolynomialRelationCertificate
set_option autoImplicit true
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Matrix
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- A literal finite-parameter primitive Lemma-T witness, with both
polynomial variables and both degree conventions recorded. -/
structure PolynomialRelationCertificate (p : ℕ) (x u v : ι → F) (k H : ℕ) where
  coefficients : Fin 2 × Fin (H+1) → F[X]
  output : Polynomial (Polynomial F)
  primitive : PrimitiveVector.IsPrimitive coefficients
  coefficient_height : ∀ b, (coefficients b).natDegree≤(2*H+1)*p
  x_degree : ∀ b : Fin 2, (Principal.assemble (fun j => coefficients (b,j))).natDegree≤H
  output_degree : output.degree<(k+H : ℕ)
  nodes : ∀ i,
    (Principal.assemble (fun j => coefficients (0,j))).eval (Polynomial.C (x i))*
      (Polynomial.C (u i)+(Polynomial.X : F[X])*Polynomial.C (v i))+
    (Principal.assemble (fun j => coefficients (1,j))).eval (Polynomial.C (x i))*
      (Polynomial.C (u i^p)+(Polynomial.X : F[X])^p*Polynomial.C (v i^p))=
    output.eval (Polynomial.C (x i))

def polynomialRelationCertificate_of_nullity_one [Fintype F]
    (p : ℕ) [ExpChar F p] (hp : 1≤p) (x u v : ι → F)
    (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (k m H : ℕ) (hkm : k+m=Fintype.card ι) (hH : H≤m)
    (hcard : (2*H+2)*p<Fintype.card F)
    (hnull : GenericLayer.genericNullity (parameterRelation p x u v m H)=1) :
    PolynomialRelationCertificate p x u v k H := by
  apply Classical.choice
  obtain ⟨Q,R,hprim,hQ,hdeg,hR,hRv⟩ := lemmaT_polynomial_family p hp x u v hx hfixed k m H hkm hH hcard hnull
  exact ⟨⟨Q,R,hprim,hdeg,fun b => Principal.assemble_natDegree_le _,hR,hRv⟩⟩

end
end FrobeniusLocator.Strata
end PackSource_PolynomialRelationCertificate

section PackSource_K1_2BadDeletion
set_option autoImplicit true
set_option autoImplicit false

/-! Good-node deletions of the SAME nonjoint support. The lower bound is
sharp; it does not choose an unrelated decoder after puncturing. -/
namespace K1_2.Mixed
open FrobeniusLocator
open FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
variable {F ι : Type} [Field F] [DecidableEq ι]
local instance decProp (P : Prop) : Decidable P := Classical.propDecidable P

def JointOn (x u v : ι → F) (k : ℕ) (S : Finset ι) : Prop :=
  ExtendsOn x u k S ∧ ExtendsOn x v k S

theorem deletion_intersection_large (S J J' : Finset ι) (k j : ℕ)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j) :
    k ≤ ((S\J) ∩ (S\J')).card := by
  have hcover : S ⊆ ((S\J) ∩ (S\J')) ∪ J ∪ J' := by
    intro i hi
    by_cases h : i∈J
    · exact mem_union_left _ (mem_union_right _ h)
    · by_cases h' : i∈J'
      · exact mem_union_right _ h'
      · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr
          ⟨mem_sdiff.mpr ⟨hi,h⟩,mem_sdiff.mpr ⟨hi,h'⟩⟩))
  have hc := card_le_card hcover
  have h1 := card_union_le (((S\J) ∩ (S\J')) ∪ J) J'
  have h2 := card_union_le ((S\J) ∩ (S\J')) J
  omega

theorem polynomial_unique_on_deletions (x : ι → F) (hx : Function.Injective x)
    (u : ι → F) (k j : ℕ) (S J J' : Finset ι)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j)
    (P Q : F[X]) (hP : P.degree<k) (hQ : Q.degree<k)
    (hPv : ∀ i∈S\J,P.eval (x i)=u i)
    (hQv : ∀ i∈S\J',Q.eval (x i)=u i) : P=Q := by
  have hcard := deletion_intersection_large S J J' k j hsize hJ hJ'
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq ((S\J) ∩ (S\J'))
    (fun a _ b _ hab => hx hab)
    (hP.trans_le (by exact_mod_cast hcard))
    (hQ.trans_le (by exact_mod_cast hcard))
  intro i hi
  exact (hPv i (mem_inter.mp hi).1).trans (hQv i (mem_inter.mp hi).2).symm

/-- If one retained set is jointly explained, every other such set has
the SAME explaining polynomial pair. -/
theorem joint_deletions_same_pair (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k j : ℕ) (S J J' : Finset ι)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j)
    (P0 P1 Q0 Q1 : F[X])
    (hP0 : P0.degree<k) (hP1 : P1.degree<k)
    (hQ0 : Q0.degree<k) (hQ1 : Q1.degree<k)
    (hPv0 : ∀ i∈S\J,P0.eval (x i)=u i)
    (hPv1 : ∀ i∈S\J,P1.eval (x i)=v i)
    (hQv0 : ∀ i∈S\J',Q0.eval (x i)=u i)
    (hQv1 : ∀ i∈S\J',Q1.eval (x i)=v i) : P0=Q0 ∧ P1=Q1 :=
  ⟨polynomial_unique_on_deletions x hx u k j S J J' hsize hJ hJ' P0 Q0 hP0 hQ0 hPv0 hQv0,
   polynomial_unique_on_deletions x hx v k j S J J' hsize hJ hJ' P1 Q1 hP1 hQ1 hPv1 hQv1⟩

/-- At least choose(B-1,j) agreement-node deletions retain nonjointness,
provided B-2j>=k. Both polynomial degrees remain <k. -/
theorem bad_good_deletion_count (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k j : ℕ) (S : Finset ι)
    (hsize : k+2*j ≤ S.card) (hbad : ¬JointOn x u v k S) :
    (S.card-1).choose j ≤
      ((S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J))).card := by
  classical
  by_cases hex : ∃ J∈S.powersetCard j,JointOn x u v k (S\J)
  · obtain ⟨J0,hJ0,⟨P0,hP0,hPv0⟩,⟨P1,hP1,hPv1⟩⟩ := hex
    obtain ⟨i,hi,hfail⟩ : ∃ i∈S,P0.eval (x i)≠u i ∨ P1.eval (x i)≠v i := by
      by_contra hn
      push Not at hn
      exact hbad ⟨⟨P0,hP0,fun i hi => (hn i hi).1⟩,
        ⟨P1,hP1,fun i hi => (hn i hi).2⟩⟩
    have hsub : (S.erase i).powersetCard j ⊆
        (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J)) := by
      intro J hJ
      obtain ⟨hJS,hJcard⟩ := mem_powersetCard.mp hJ
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨hJS.trans (erase_subset _ _),hJcard⟩,?_⟩
      rintro ⟨⟨Q0,hQ0,hQv0⟩,⟨Q1,hQ1,hQv1⟩⟩
      obtain ⟨h0,h1⟩ := joint_deletions_same_pair x hx u v k j S J0 J
        hsize (mem_powersetCard.mp hJ0).2 hJcard P0 P1 Q0 Q1
        hP0 hP1 hQ0 hQ1 hPv0 hPv1 hQv0 hQv1
      have hiJ : i∉J := fun h => (notMem_erase i S) (hJS h)
      have hi' : i∈S\J := mem_sdiff.mpr ⟨hi,hiJ⟩
      rcases hfail with h | h
      · exact h (h0 ▸ hQv0 i hi')
      · exact h (h1 ▸ hQv1 i hi')
    have hc := card_le_card hsub
    simpa only [card_powersetCard,card_erase_of_mem hi] using hc
  · have heq : (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J)) =
        S.powersetCard j := by
      apply filter_eq_self.mpr
      intro J hJ hj
      exact hex ⟨J,hJ,hj⟩
    rw [heq,card_powersetCard]
    exact Nat.choose_le_choose j (Nat.sub_le _ _)

end
end K1_2.Mixed
end PackSource_K1_2BadDeletion

section PackSource_CommonCompression
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F row τ : Type} [Field F] [Fintype row] [DecidableEq row]

/-- Universal constant row-compression coefficients as independent variables. -/
def universalCompression (r : ℕ) : Matrix (Fin r) row (MvPolynomial (Fin r × row) F) :=
  fun i j => MvPolynomial.X (i,j)

def compressionMinor {r : ℕ} (A : Matrix row (Fin r) F) : MvPolynomial (Fin r × row) F :=
  (universalCompression r*A.map MvPolynomial.C).det

theorem compressionMinor_eval {r : ℕ} (A : Matrix row (Fin r) F) (x : Fin r × row → F) :
    MvPolynomial.eval x (compressionMinor A)=(Matrix.of (fun i j => x (i,j))*A).det := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id F) x
  have hd := φ.map_det (universalCompression r*A.map MvPolynomial.C)
  rw [RingHom.mapMatrix_apply] at hd
  change φ (universalCompression r*A.map MvPolynomial.C).det=_
  rw [hd]
  congr 1
  ext i j
  simp only [Matrix.map_apply,Matrix.mul_apply,map_sum,map_mul,universalCompression,
    Matrix.of_apply,φ,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval₂_C,RingHom.id_apply]

theorem compressionMinor_degree {r : ℕ} (A : Matrix row (Fin r) F) :
    (compressionMinor A).totalDegree≤r := by
  let N : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × row) F) := universalCompression r*A.map MvPolynomial.C
  have hentry : ∀ i j, (N i j).totalDegree≤1 := by
    intro i j
    change (∑ k : row, (universalCompression r i k)*MvPolynomial.C (A k j)).totalDegree≤1
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [universalCompression])
  have hh := totalDegree_det_le_row_sum N (fun _ => 1) hentry
  simpa [N,compressionMinor] using hh

theorem compressionMinor_ne_zero {r : ℕ} (A : Matrix row (Fin r) F)
    (hA : A.rank=r) : compressionMinor A≠0 := by
  classical
  have hinj := matrix_injective_of_full_column_rank A (by simpa only [Fintype.card_fin] using hA)
  obtain ⟨rows,hrows⟩ := GenericRank.exists_rows_det_ne_zero A (fun v hv => hinj (hv.trans (map_zero A.mulVecLin).symm))
  let x : Fin r × row → F := fun b => if b.2=rows b.1 then 1 else 0
  have hselector : Matrix.of (fun i j => x (i,j))*A=A.submatrix rows id := by
    ext i j
    simp [Matrix.mul_apply,x]
  have heval : MvPolynomial.eval x (compressionMinor A)≠0 := by
    rw [compressionMinor_eval,hselector]
    exact hrows
  intro hz
  exact heval (by rw [hz]; simp)

/-- A SINGLE constant row compression avoids the first-column minor at
all selected points. Native F is finite; the explicit degree/cardinality
guard replaces an unnecessary algebraic-closure/infinite-field detour. -/
theorem exists_common_row_compression [Fintype F] [DecidableEq F]
    (S : Finset τ) (r : ℕ) (A : τ → Matrix row (Fin r) F)
    (hA : ∀ z∈S, (A z).rank=r) (hcard : S.card*r<Fintype.card F) :
    ∃ C : Matrix (Fin r) row F, ∀ z∈S, (C*A z).det≠0 := by
  classical
  let p := ∏ z∈S, compressionMinor (A z)
  have hp : p≠0 := Finset.prod_ne_zero_iff.mpr (fun z hz => compressionMinor_ne_zero (A z) (hA z hz))
  have hdeg : p.totalDegree<Fintype.card F := by
    have hh := MvPolynomial.totalDegree_finsetProd S (fun z => compressionMinor (A z))
    have hs : (∑ z∈S, (compressionMinor (A z)).totalDegree)≤S.card*r :=
      (Finset.sum_le_sum (fun z _ => compressionMinor_degree (A z))).trans_eq (by simp)
    exact (hh.trans hs).trans_lt hcard
  obtain ⟨x,hx⟩ := exists_nonzero_evaluation_finite_variables p hp hdeg
  refine ⟨Matrix.of (fun i j => x (i,j)),?_⟩
  intro z hz
  have hprod : (∏ z∈S, MvPolynomial.eval x (compressionMinor (A z)))≠0 := by
    simpa only [p,map_prod] using hx
  have hn := Finset.prod_ne_zero_iff.mp hprod z hz
  rwa [compressionMinor_eval] at hn

end
end FrobeniusLocator.Strata
end PackSource_CommonCompression

section PackSource_K1_2MixedDeletions
set_option autoImplicit true
set_option autoImplicit false

namespace K1_2.Mixed
noncomputable section
open Finset
variable {F ι : Type} [Field F] [DecidableEq ι]
local instance decMixed (P : Prop) : Decidable P := Classical.propDecidable P

theorem disjoint_union_pair_injective (E S : Finset ι) (hES : Disjoint E S)
    (p q : Finset ι × Finset ι)
    (hpE : p.1⊆E) (hpS : p.2⊆S) (hqE : q.1⊆E) (hqS : q.2⊆S)
    (heq : p.1∪p.2=q.1∪q.2) : p=q := by
  have hd : ∀ i∈E,i∉S := fun i hi => (disjoint_left.mp hES hi)
  have hfirst : p.1=q.1 := by
    ext i
    constructor
    · intro hi
      have hm : i∈q.1∪q.2 := heq ▸ mem_union_left _ hi
      exact (mem_union.mp hm).resolve_right (fun h => hd i (hpE hi) (hqS h))
    · intro hi
      have hm : i∈p.1∪p.2 := heq.symm ▸ mem_union_left _ hi
      exact (mem_union.mp hm).resolve_right (fun h => hd i (hqE hi) (hpS h))
  have hsecond : p.2=q.2 := by
    ext i
    constructor
    · intro hi
      have hm : i∈q.1∪q.2 := heq ▸ mem_union_right _ hi
      exact (mem_union.mp hm).resolve_left (fun h => hd i (hqE h) (hpS hi))
    · intro hi
      have hm : i∈p.1∪p.2 := heq.symm ▸ mem_union_right _ hi
      exact (mem_union.mp hm).resolve_left (fun h => hd i (hpE h) (hqS hi))
  exact Prod.ext hfirst hsecond

def goodDeletions (x u v : ι→F) (k j : ℕ) (S : Finset ι) : Finset (Finset ι) :=
  (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J))

def mixedDeletions (x u v : ι→F) (k b j : ℕ) (E S : Finset ι) : Finset (Finset ι) :=
  ((E.powersetCard b).product (goodDeletions x u v k j S)).image (fun p => p.1∪p.2)

theorem mixedDeletions_card (x u v : ι→F) (k b j : ℕ) (E S : Finset ι)
    (hES : Disjoint E S) :
    (mixedDeletions x u v k b j E S).card =
      E.card.choose b*(goodDeletions x u v k j S).card := by
  unfold mixedDeletions
  rw [card_image_of_injOn]
  · simp only [Finset.product_eq_sprod,Finset.card_product,card_powersetCard]
  intro p hp q hq heq
  obtain ⟨hpE,hpS⟩ := mem_product.mp hp
  obtain ⟨hqE,hqS⟩ := mem_product.mp hq
  apply disjoint_union_pair_injective E S hES p q
    (mem_powersetCard.mp hpE).1
    (mem_powersetCard.mp (mem_filter.mp hpS).1).1
    (mem_powersetCard.mp hqE).1
    (mem_powersetCard.mp (mem_filter.mp hqS).1).1 heq

theorem mixedDeletions_lower_bound (x u v : ι→F) (hx : Function.Injective x)
    (k b j : ℕ) (E S : Finset ι) (hES : Disjoint E S)
    (hsize : k+2*j≤S.card) (hbad : ¬JointOn x u v k S) :
    E.card.choose b*(S.card-1).choose j ≤
      (mixedDeletions x u v k b j E S).card := by
  rw [mixedDeletions_card x u v k b j E S hES]
  exact Nat.mul_le_mul_left _ (bad_good_deletion_count x hx u v k j S hsize hbad)

theorem mixedDeletions_spec (x u v : ι→F) (k b j : ℕ) (E S I : Finset ι)
    (hES : Disjoint E S) (hI : I∈mixedDeletions x u v k b j E S) :
    I⊆E∪S ∧ I.card=b+j ∧ (S\I).card=S.card-j ∧
      ¬JointOn x u v k (S\I) := by
  obtain ⟨⟨B,J⟩,hmem,rfl⟩ := mem_image.mp hI
  obtain ⟨hB,hJ⟩ := mem_product.mp hmem
  obtain ⟨hBE,hBc⟩ := mem_powersetCard.mp hB
  obtain ⟨hJS,hJc⟩ := mem_powersetCard.mp (mem_filter.mp hJ).1
  have hd : Disjoint B J := hES.mono hBE hJS
  have hremain : S\(B∪J)=S\J := by
    ext i
    simp only [mem_sdiff,mem_union,not_or]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,fun hi => disjoint_left.mp hES (hBE hi) h.1,h.2⟩
  refine ⟨union_subset_union hBE hJS,?_,?_,?_⟩
  · rw [card_union_of_disjoint hd,hBc,hJc]
  · rw [hremain,card_sdiff_of_subset hJS,hJc]
  · rw [hremain]
    exact (mem_filter.mp hJ).2

end
end K1_2.Mixed
end PackSource_K1_2MixedDeletions

section PackSource_K1_2SharedMixedCount
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! This is the complete finite shared-deletion argument. Its remaining
child-price premise is explicit, and is not a native geometric theorem. -/
namespace K1_2.Mixed
noncomputable section
open Finset
variable {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
local instance decSharedMixed (P : Prop) : Decidable P := Classical.propDecidable P

theorem shared_mixed_rational_count (x u v : ι→F) (hx : Function.Injective x)
    (nodes : Finset ι) (Γ : Finset F) (k A T vcount c numerator denominator : ℕ)
    (S E : F→Finset ι) (U : F→ℕ)
    (hAT : T≤A) (hfit : vcount+c≤T) (hguard : k+vcount+2*c≤A)
    (hwitness : ∀ γ∈Γ, U γ≤vcount ∧ (S γ).card=A+U γ ∧
      (E γ).card=T-U γ ∧ Disjoint (E γ) (S γ) ∧ E γ∪S γ⊆nodes ∧
      ¬JointOn x u v k (S γ))
    (hchild : ∀ I∈nodes.powersetCard (vcount+2*c),
      denominator*(Γ.filter (fun γ =>
        I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ))).card≤numerator) :
    denominator*(T.choose (vcount+c)*(A-1).choose c)*Γ.card ≤
      nodes.card.choose (vcount+2*c)*numerator := by
  classical
  let incident : Finset ι→F→Prop := fun I γ =>
    I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ)
  have hparent : ∀ γ∈Γ,T.choose (vcount+c)*(A-1).choose c≤
      ((nodes.powersetCard (vcount+2*c)).filter (fun I => incident I γ)).card := by
    intro γ hγ
    obtain ⟨hU,hS,hE,hES,hsub,hbad⟩ := hwitness γ hγ
    have hsize : k+2*(U γ+c)≤(S γ).card := by rw [hS]; omega
    have hlow := mixedDeletions_lower_bound x u v hx k (vcount-U γ+c) (U γ+c)
      (E γ) (S γ) hES hsize hbad
    rw [hS,hE] at hlow
    have hbeta := deletionBeta_zero_le T A vcount c (U γ) hAT hU hfit
    have hlow' : T.choose (vcount+c)*(A-1).choose c≤
        (mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ)).card := by
      have hbeta' : T.choose (vcount+c)*(A-1).choose c≤
          (T-U γ).choose (vcount-U γ+c)*(A+U γ-1).choose (U γ+c) := by
        simpa only [deletionBeta,Nat.sub_zero,Nat.add_zero,Nat.zero_add] using hbeta
      exact hbeta'.trans hlow
    apply hlow'.trans
    apply card_le_card
    intro I hI
    obtain ⟨hIS,hIc,hremain,hbad'⟩ := mixedDeletions_spec x u v k
      (vcount-U γ+c) (U γ+c) (E γ) (S γ) I hES hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIS.trans hsub,by omega⟩,hI⟩
  have hh := shared_child_rational_incidence
    (nodes.powersetCard (vcount+2*c)) Γ incident
    (T.choose (vcount+c)*(A-1).choose c) numerator denominator
    (by
      intro γ hγ
      convert hparent γ hγ using 1 <;> congr 2)
    (by
      intro I hI
      convert hchild I hI using 1
      congr 2
      ext γ
      simp only [mem_filter,incident])
  simpa only [card_powersetCard] using hh

theorem shared_mixed_count_floor (x u v : ι→F) (hx : Function.Injective x)
    (nodes : Finset ι) (Γ : Finset F) (k A T vcount c numerator denominator : ℕ)
    (S E : F→Finset ι) (U : F→ℕ)
    (hAT : T≤A) (hfit : vcount+c≤T) (hguard : k+vcount+2*c≤A)
    (hpositive : 0<denominator*(T.choose (vcount+c)*(A-1).choose c))
    (hwitness : ∀ γ∈Γ, U γ≤vcount ∧ (S γ).card=A+U γ ∧
      (E γ).card=T-U γ ∧ Disjoint (E γ) (S γ) ∧ E γ∪S γ⊆nodes ∧
      ¬JointOn x u v k (S γ))
    (hchild : ∀ I∈nodes.powersetCard (vcount+2*c),
      denominator*(Γ.filter (fun γ =>
        I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ))).card≤numerator) :
    Γ.card≤(nodes.card.choose (vcount+2*c)*numerator)/
      (denominator*(T.choose (vcount+c)*(A-1).choose c)) := by
  apply (Nat.le_div_iff_mul_le hpositive).mpr
  simpa only [Nat.mul_comm Γ.card] using shared_mixed_rational_count x u v hx
    nodes Γ k A T vcount c numerator denominator S E U hAT hfit hguard hwitness hchild

end
end K1_2.Mixed
end PackSource_K1_2SharedMixedCount

section PackSource_CompressedKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix
open scoped BigOperators
variable {F row col : Type} [Field F] [Fintype row] [Fintype col] [DecidableEq col]

theorem kernel_eq_compressed_of_equal_rank (M : Matrix row col F) (r : ℕ)
    (C : Matrix (Fin r) row F) (hMrank : M.rank=(C*M).rank) :
    LinearMap.ker M.mulVecLin=LinearMap.ker (C*M).mulVecLin := by
  have hle : LinearMap.ker M.mulVecLin≤LinearMap.ker (C*M).mulVecLin := by
    intro v hv
    change (C*M).mulVec v=0
    rw [← Matrix.mulVec_mulVec,show M.mulVec v=0 from hv,Matrix.mulVec_zero]
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hN := LinearMap.finrank_range_add_finrank_ker (C*M).mulVecLin
  change M.rank+_= _ at hM
  change (C*M).rank+_= _ at hN
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hMrank] at hM
  omega

theorem compressed_rank_eq_of_pivot (M : Matrix row col F) (r : ℕ)
    (C : Matrix (Fin r) row F) (cols : Fin r → col)
    (hdet : ((C*M).submatrix id cols).det≠0) (hrank : M.rank≤r) :
    M.rank=r ∧ (C*M).rank=r := by
  have hlo := Matrix.rank_submatrix_le (C*M) id cols
  rw [Matrix.rank_of_det_ne_zero hdet,Fintype.card_fin] at hlo
  have hhi := Matrix.rank_le_card_height (C*M)
  rw [Fintype.card_fin] at hhi
  have hmul := Matrix.rank_mul_le_right C M
  omega

section Ring
variable {R : Type} [CommRing R] {r : ℕ}

def lastCofactor (N : Matrix (Fin r) (Fin (r+1)) R) : Fin (r+1) → R :=
  GenericCofactor.rawVector N id Fin.castSucc (Fin.last r)

theorem lastCofactor_annihilates (N : Matrix (Fin r) (Fin (r+1)) R) :
    N.mulVec (lastCofactor N)=0 := by
  exact GenericCofactor.selected_annihilates N id Fin.castSucc (Fin.last r)

theorem lastCofactor_last (N : Matrix (Fin r) (Fin (r+1)) R) :
    lastCofactor N (Fin.last r)=(N.submatrix id Fin.castSucc).det := by
  have hne (j : Fin r) : j.castSucc≠Fin.last r := by intro h; have hh := congrArg Fin.val h; have := j.isLt; simp only [Fin.val_castSucc,Fin.val_last] at hh; omega
  have hne' (j : Fin r) : Fin.last r≠j.castSucc := (hne j).symm
  rw [lastCofactor,GenericCofactor.rawVector_apply]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one,Matrix.mulVec,dotProduct,
    GenericCofactor.inclusion,Pi.single_apply,hne',ite_false,zero_mul,Finset.sum_const_zero,sub_zero]
end Ring

theorem compressed_lastCofactor_kernel {r : ℕ} (M : Matrix row (Fin (r+1)) F)
    (C : Matrix (Fin r) row F)
    (hdet : ((C*M).submatrix id Fin.castSucc).det≠0) (hrank : M.rank≤r) :
    M.mulVec (lastCofactor (C*M))=0 ∧ lastCofactor (C*M) (Fin.last r)≠0 := by
  obtain ⟨hM,hN⟩ := compressed_rank_eq_of_pivot M r C Fin.castSucc hdet hrank
  have heq := kernel_eq_compressed_of_equal_rank M r C (hM.trans hN.symm)
  have hker : lastCofactor (C*M)∈LinearMap.ker (C*M).mulVecLin := lastCofactor_annihilates _
  rw [← heq] at hker
  exact ⟨hker,by rw [lastCofactor_last]; exact hdet⟩

end
end FrobeniusLocator.Strata
end PackSource_CompressedKernel

section PackSource_K1_3Moments
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace K1_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open scoped BigOperators

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Power evaluation on the actual error nodes. -/
def powers (x : ι → F) (b : ℕ) : Matrix ι (Fin b) F :=
  fun i j => x i ^ j.val

omit [DecidableEq ι] in
theorem powers_rank (x : ι → F) (hx : Function.Injective x) (b : ℕ) :
    (powers x b).rank = min (Fintype.card ι) b := by
  let e := Polynomial.degreeLTEquiv F b
  have he : (powers x b).mulVecLin.comp e.toLinearMap = Strata.boundedEvaluation x b := by
    ext P i
    change (∑ j : Fin b, x i ^ j.val * e P j) = (P : F[X]).eval (x i)
    rw [Polynomial.eval_eq_sum_degreeLTEquiv P.property]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [← Strata.boundedEvaluation_rank x hx b, ← he,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.surjective)]
  rfl

/-- Every moment in the dual range is contributed by the errors. -/
theorem error_moment (x w : ι → F) (hx : Function.Injective x) (P : F[X])
    (k j : ℕ) (hP : P.degree < k) (hj : k + j < Fintype.card ι)
    (E : Finset ι) (hout : ∀ i, i ∉ E → w i = P.eval (x i)) :
    syndrome x w j = ∑ i ∈ E, (weight x i * (w i - P.eval (x i))) * x i ^ j := by
  classical
  rw [Strata.syndrome_sub_decoder x w hx P k j hP hj]
  symm
  apply Finset.sum_subset (Finset.subset_univ E)
  intro i _ hi
  simp [hout i hi]

/-- The moment matrix factors through the error set, with one diagonal of errors. -/
theorem moment_factor (x w : ι → F) (hx : Function.Injective x) (P : F[X])
    (k l b : ℕ) (hP : P.degree < k) (hsize : k + l + b ≤ Fintype.card ι + 1)
    (E : Finset ι) (hout : ∀ i, i ∉ E → w i = P.eval (x i)) :
    (Matrix.of (fun (i : Fin l) (j : Fin b) => syndrome x w (i.val + j.val))) =
      (powers (fun i : E => x i.val) l).transpose *
      diagonal (fun i : E => weight x i.val * (w i.val - P.eval (x i.val))) *
      powers (fun i : E => x i.val) b := by
  ext i j
  rw [Matrix.of_apply, error_moment x w hx P k _ hP (by have := i.isLt; have := j.isLt; omega)
    E hout, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, powers]
  rw [Finset.sum_coe_sort E (fun a =>
    x a ^ i.val * (weight x a * (w a - P.eval (x a))) * x a ^ j.val)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pow_add]
  ring

theorem evaluated_hankel (x u v : ι → F) (γ : F) (l t : ℕ) :
    (hankel x u v l t).map (evalRingHom γ) =
      Matrix.of (fun (i : Fin l) (j : Fin (t + 1)) =>
        syndrome x (fun a => u a + γ * v a) (i.val + j.val)) := by
  ext i j
  simpa only [Matrix.of_apply, Matrix.map_apply, coe_evalRingHom, hankel,
    eval_add, eval_mul, eval_C, eval_X, one_mul] using
      (Principal.syndrome_linear x u v 1 γ (i.val + j.val)).symm

/-- When all error columns fit in the right Vandermonde, the ordinary rank
is the minimum of the number of rows and the number of nonzero errors. -/
theorem evaluated_hankel_rank (x u v : ι → F) (hx : Function.Injective x) (γ : F)
    (P : F[X]) (k l t : ℕ) (hP : P.degree < k) (hsize : k + l + t ≤ Fintype.card ι)
    (E : Finset ι) (hE : E.card ≤ t + 1)
    (hout : ∀ i, i ∉ E → u i + γ * v i = P.eval (x i))
    (hin : ∀ i ∈ E, u i + γ * v i ≠ P.eval (x i)) :
    ((hankel x u v l t).map (evalRingHom γ)).rank = min E.card l := by
  classical
  let z : E → F := fun i => x i.val
  have hz : Function.Injective z := hx.comp Subtype.val_injective
  have hs : Function.Surjective (powers z (t + 1)).mulVecLin :=
    Strata.nodeVandermonde_surjective z hz t (by simpa only [Fintype.card_coe] using hE)
  rw [evaluated_hankel, moment_factor x _ hx P k l (t + 1) hP (by omega) E hout,
    Strata.rank_mul_of_surjective _ _ hs]
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ ?_, Matrix.rank_transpose,
    powers_rank z hz, Fintype.card_coe]
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    mul_ne_zero (Strata.weight_ne_zero x hx _) (sub_ne_zero.mpr (hin i.val i.property)))

/-- A square moment matrix on exactly as many distinct nonzero errors as rows
has nonzero determinant, including the empty square matrix. -/
theorem moment_det_ne_zero (x w : ι → F) (hx : Function.Injective x) (P : F[X])
    (k d : ℕ) (hP : P.degree < k) (hsize : k + d + d ≤ Fintype.card ι + 1)
    (E : Finset ι) (hE : E.card = d)
    (hout : ∀ i, i ∉ E → w i = P.eval (x i))
    (hin : ∀ i ∈ E, w i ≠ P.eval (x i)) :
    (Matrix.of (fun (i j : Fin d) => syndrome x w (i.val + j.val))).det ≠ 0 := by
  classical
  let e : Fin d ≃ E := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hE)).symm
  let z := fun i : Fin d => x (e i).val
  let a := fun i : Fin d => weight x (e i).val * (w (e i).val - P.eval (z i))
  let V := Matrix.vandermonde z
  have hfactor : (Matrix.of (fun (i j : Fin d) => syndrome x w (i.val + j.val))) =
      V.transpose * diagonal a * V := by
    ext i j
    rw [Matrix.of_apply, error_moment x w hx P k _ hP (by have := i.isLt; have := j.isLt; omega)
      E hout, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply, V]
    rw [← Finset.sum_coe_sort]
    symm
    apply Fintype.sum_equiv e
    intro b
    simp only [z, a, pow_add]
    ring
  have hV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr
    (hx.comp (Subtype.val_injective.comp e.injective))
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero (mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr fun i _ =>
    mul_ne_zero (Strata.weight_ne_zero x hx _) (sub_ne_zero.mpr (hin _ (e i).property)))) hV

/-- For a monic locator on the errors, the evaluated cofactor vector is that
locator's coefficient vector multiplied by the pivot determinant. -/
theorem cofactor_at_nodes (x u v : ι → F) (hx : Function.Injective x) (γ : F)
    (P : F[X]) (k d : ℕ) (hP : P.degree < k) (hsize : k + d + d ≤ Fintype.card ι)
    (E : Finset ι) (hE : E.card = d)
    (hout : ∀ i, i ∉ E → u i + γ * v i = P.eval (x i))
    (hin : ∀ i ∈ E, u i + γ * v i ≠ P.eval (x i)) :
    let M := hankel x u v d d
    let A := M.submatrix id Fin.castSucc
    let b := fun i => M i (Fin.last d)
    let c := CofactorLine.vector A b
    let q := fun i => ∑ j : Option (Fin d), C (x i ^ (j.elim d Fin.val)) * c j
    ∀ i, (q i).eval γ = A.det.eval γ * (locator x E).eval (x i) ∧ A.det.eval γ ≠ 0 := by
  classical
  dsimp only
  let M := hankel x u v d d
  let A := M.submatrix id Fin.castSucc
  let b := fun i => M i (Fin.last d)
  let D := locator x E
  let f := fun (j : Option (Fin d)) => D.coeff (j.elim d Fin.val)
  let Aγ := A.map (evalRingHom γ)
  let bγ := evalRingHom γ ∘ b
  have hAγ : Aγ = Matrix.of (fun (i j : Fin d) =>
      syndrome x (fun a => u a + γ * v a) (i.val + j.val)) := by
    ext i j
    exact congrFun (congrFun (evaluated_hankel x u v γ d d) i) (Fin.castSucc j)
  have hdet : Aγ.det ≠ 0 := by
    rw [hAγ]
    exact moment_det_ne_zero x _ hx P k d hP (by omega) E hE hout hin
  have hpoint (i : ι) : D.eval (x i) * (u i + γ * v i) = D.eval (x i) * P.eval (x i) := by
    by_cases hi : i ∈ E
    · simp [D, locator_eval_zero x E i hi]
    · rw [hout i hi]
  have hd : D.natDegree = d := (locator_natDegree x E).trans hE
  have hker := hankel_annihilates x hx u v γ k d d hsize P D hP hd.le hpoint
  have hf : f none = 1 := by
    change D.coeff d = 1
    rw [← hd]
    exact (locator_monic x E).coeff_natDegree
  have hborder : (CofactorLine.bordered Aγ bγ).mulVec f = 0 := by
    funext i
    have hh := congrFun hker i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc] at hh
    simpa only [Matrix.mulVec, dotProduct, Fintype.sum_option, CofactorLine.bordered, f,
      Option.elim_none, Option.elim_some, Aγ, A, bγ, b, Matrix.map_apply, Matrix.submatrix_apply,
      Function.comp_apply, id_eq, coe_evalRingHom, Fin.val_castSucc, Fin.val_last, add_comm] using hh
  have hline := CofactorLine.kernel_line Aγ bγ hdet f hborder
  have hmapdet : Aγ.det = A.det.eval γ := ((evalRingHom γ).map_det A).symm
  have hcoeff (j : Option (Fin d)) :
      (CofactorLine.vector A b j).eval γ = A.det.eval γ * f j := by
    rw [← hmapdet]
    have he := congrFun hline j
    rw [hf] at he
    change f j = (1 / Aγ.det) * CofactorLine.vector Aγ bγ j at he
    rw [CofactorLine.map_vector] at he
    rw [he, ← mul_assoc, one_div, mul_inv_cancel₀ hdet, one_mul]
    rfl
  intro i
  change (∑ j : Option (Fin d), C (x i ^ j.elim d Fin.val) * CofactorLine.vector A b j).eval γ =
    A.det.eval γ * D.eval (x i) ∧ A.det.eval γ ≠ 0
  refine ⟨?_, hmapdet ▸ hdet⟩
  simp only [eval_finsetSum, eval_mul, eval_C, hcoeff]
  rw [← sum_coeff_eval D d hd.le, Fin.sum_univ_castSucc, Fintype.sum_option, mul_add,
    Finset.mul_sum, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp only [f, Option.elim_some, Fin.val_castSucc]
    ring
  · simp only [f, Option.elim_none, Fin.val_last]
    ring

end
end K1_3
end PackSource_K1_3Moments

section PackSource_PrincipalRowBasis
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι K : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- A row-basis certificate supplies exactly the normal nullity used by
the principal specialization theorem. No per-slope rank assumption. -/
theorem principal_normal_nullity (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) (x u v : ι → F) (L t a q : ℕ) (haq : a+q=t)
    (B : NormalFiber.RowBasis φ (stacked p x u v L t) a)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) :
    Module.finrank F (LinearMap.ker
      ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVecLin) = q+1 := by
  have hrank := NormalFiber.rank_specializes φ hφ (stacked p x u v L t) a B γ hγ
  have hn := LinearMap.finrank_range_add_finrank_ker
    ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVecLin
  change ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).rank + _ = _ at hn
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hn
  omega

/-- The constant-kernel certificate is automatic from a fixed polynomial
kernel subspace of the correct generic dimension and a row basis. -/
def constantCertificateOfRowBasis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) (x u v : ι → F) (L t r : ℕ)
    (B : NormalFiber.RowBasis φ (stacked p x u v L t) r)
    (W : Submodule F (Fin (t+1) → F))
    (hWdim : Module.finrank F W = t+1-r)
    (hW : ∀ c ∈ W, (stacked p x u v L t).mulVec (fun j => C (c j)) = 0) :
    ConstantKernelCertificate p x u v L t (NormalFiber.pivot B).det where
  space := W
  generic_annihilates := hW
  normal_inclusion := by
    intro γ hγ c hc
    have heval (β : F) (c' : Fin (t+1) → F) (hv : c' ∈ W) :
        ((stacked p x u v L t).map (Polynomial.evalRingHom β)).mulVec c' = 0 := by
      have h := congrArg (fun w => fun i => (w i).eval β) (hW c' hv)
      funext i
      have hi := congrFun h i
      simpa [Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum] using hi
    have heq := NormalFiber.constant_kernel_eq_normal φ hφ
      (stacked p x u v L t) r B W (by simpa using hWdim) heval γ hγ
    rw [← heq]
    exact hc

def movingCertificateOfRowBasis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) (x u v : ι → F) (L t : ℕ) (H : Finset ι) (d q : ℕ)
    (hd : 0 < d) (hsize : H.card+d+q=t)
    (B : NormalFiber.RowBasis φ (stacked p x u v L t) (H.card+d))
    (coeffs : Fin (d+1) → F[X])
    (hdeg : ∀ j, (coeffs j).natDegree ≤ p*d)
    (hprimitive : ∀ γ, specialize coeffs γ ≠ 0)
    (hfixed : ∀ i, i ∉ H → nodePolynomial coeffs (x i) ≠ 0)
    (hshift : ∀ γ (Q : Polynomial.degreeLT F (q+1)),
      ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVec
        (multipleCoefficients (locator x H * specialize coeffs γ) q t Q)=0) :
    MovingPrincipalCertificate p x u v L t (NormalFiber.pivot B).det where
  fixedRoots := H
  movingDegree := d
  quotientDegree := q
  moving_pos := hd
  degree_sum := hsize
  coefficients := coeffs
  coefficient_degree := hdeg
  primitive_specialization := hprimitive
  no_additional_fixed_root := hfixed
  normal_nullity := principal_normal_nullity φ hφ p x u v L t (H.card+d) q hsize B
  multiples_annihilate := hshift

/-- The principal theorem with the actual generic row-basis degree sum.
No rank-specialization hypothesis remains in this form. -/
theorem principal_bad_count_row_sum (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (x : ι → F) (hx : Function.Injective x)
    (hfixedNodes : ∀ i, x i^p=x i) (u v : ι → F)
    (k A L t : ℕ) (hkA : k < A) (hL : k+L=A) (ht : A+t=Fintype.card ι)
    (H : Finset ι) (d q : ℕ) (hd : 0 < d) (hsize : H.card+d+q=t)
    (B : NormalFiber.RowBasis φ (stacked p x u v L t) (H.card+d))
    (coeffs : Fin (d+1) → F[X])
    (hdeg : ∀ j, (coeffs j).natDegree ≤ p*d)
    (hprimitive : ∀ γ, specialize coeffs γ ≠ 0)
    (hfixed : ∀ i, i ∉ H → nodePolynomial coeffs (x i) ≠ 0)
    (hshift : ∀ γ (Q : Polynomial.degreeLT F (q+1)),
      ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVec
        (multipleCoefficients (locator x H * specialize coeffs γ) q t Q)=0)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) :
    Γ.card ≤ (∑ i, if (B.rows i).1=0 then 1 else p)+p*(Fintype.card ι-H.card) := by
  apply principal_bad_count p x hx hfixedNodes u v k A L t _ hkA hL ht
    (NormalFiber.pivot B).det B.minor_ne
    (NormalFiber.minor_degree_le φ _ _ B _ (stacked_entry_natDegree p x u v L t))
    (movingCertificateOfRowBasis φ hφ p x u v L t H d q hd hsize B coeffs
      hdeg hprimitive hfixed hshift) Γ hΓ

theorem constant_kernel_count_row_sum (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (x : ι → F) (hx : Function.Injective x)
    (hfixedNodes : ∀ i, x i^p=x i) (u v : ι → F)
    (k A L t r : ℕ) (hkA : k < A) (hL : k+L=A) (ht : A+t=Fintype.card ι)
    (B : NormalFiber.RowBasis φ (stacked p x u v L t) r)
    (W : Submodule F (Fin (t+1) → F)) (hWdim : Module.finrank F W=t+1-r)
    (hW : ∀ c ∈ W, (stacked p x u v L t).mulVec (fun j => C (c j))=0)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k A γ) :
    Γ.card ≤ ∑ i, if (B.rows i).1=0 then 1 else p := by
  apply constant_kernel_count p x hx hfixedNodes u v k A L t _ hkA hL ht
    (NormalFiber.pivot B).det B.minor_ne
    (NormalFiber.minor_degree_le φ _ _ B _ (stacked_entry_natDegree p x u v L t))
    (constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW) Γ hΓ

end
end FrobeniusLocator.Principal
end PackSource_PrincipalRowBasis

section PackSource_IndependentLocator
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

def independentLocator (p blocks : ℕ) (x u v : ι → F) (L t : ℕ) :
    Matrix (Fin blocks × Fin L) (Fin (t+1)) (MvPolynomial (Fin blocks) F) := fun b j =>
  MvPolynomial.C (syndrome x u (b.2.val+j.val)^(p^b.1.val))+
    MvPolynomial.X b.1*MvPolynomial.C (syndrome x v (b.2.val+j.val)^(p^b.1.val))

def independentPoint (p blocks : ℕ) (γ : F) : Fin blocks → F := fun b => γ^(p^b.val)

theorem independentLocator_eval (p blocks : ℕ) (x u v : ι → F) (L t : ℕ) (γ : F) :
    (independentLocator p blocks x u v L t).map
      (MvPolynomial.eval₂Hom (RingHom.id F) (independentPoint p blocks γ))=
      (frobeniusStacked p blocks x u v L t).map (Polynomial.evalRingHom γ) := by
  ext b j
  simp only [Matrix.map_apply,independentLocator,frobeniusStacked,independentPoint,map_add,map_mul,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply,
    Polynomial.coe_evalRingHom,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]

theorem independentLocator_entry_degree (p blocks : ℕ) (x u v : ι → F) (L t : ℕ)
    (b : Fin blocks × Fin L) (j : Fin (t+1)) :
    (independentLocator p blocks x u v L t b j).totalDegree≤1 := by
  unfold independentLocator
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C]
    omega
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_X,MvPolynomial.totalDegree_C,add_zero]
      omega)

def maximalMinorList {row ν : Type} [Fintype row] [DecidableEq row] (t : ℕ)
    (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) : List (MvPolynomial ν F) :=
  Finset.univ.toList.map (fun rows : Fin (t+1) → row => (M.submatrix rows id).det)

theorem mem_maximalMinorList {row ν : Type} [Fintype row] [DecidableEq row] (t : ℕ)
    (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) (f : MvPolynomial ν F) :
    f∈maximalMinorList t M ↔ ∃ rows : Fin (t+1) → row, (M.submatrix rows id).det=f := by
  simp only [maximalMinorList,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]

theorem maximalMinorList_degree {row ν : Type} [Fintype row] [DecidableEq row] (t : ℕ)
    (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) (hM : ∀ i j, (M i j).totalDegree≤1) :
    ∀ f∈maximalMinorList t M, f.totalDegree≤t+1 := by
  intro f hf
  obtain ⟨rows,rfl⟩ := (mem_maximalMinorList t M f).mp hf
  have hh := totalDegree_det_le_row_sum (M.submatrix rows id) (fun _ => 1) (fun i j => hM (rows i) j)
  simpa using hh

theorem maximalMinorList_eval_zero_of_top_kernel {row ν : Type} [Fintype row] [DecidableEq row]
    (t : ℕ) (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) (z : ν → F)
    (v : Fin (t+1) → F)
    (hMv : (M.map (MvPolynomial.eval₂Hom (RingHom.id F) z)).mulVec v=0)
    (htop : v (Fin.last t)≠0) :
    ∀ f∈maximalMinorList t M, MvPolynomial.aeval z f=0 := by
  intro f hf
  obtain ⟨rows,rfl⟩ := (mem_maximalMinorList t M f).mp hf
  let φ := MvPolynomial.eval₂Hom (RingHom.id F) z
  have hsel : ((M.submatrix rows id).map φ).mulVec v=0 := by
    funext i
    exact congrFun hMv (rows i)
  have hd : ((M.submatrix rows id).map φ).det=0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hsel
      (i := Fin.last t) (mem_nonZeroDivisors_of_ne_zero htop)
  have hm := φ.map_det (M.submatrix rows id)
  rw [RingHom.mapMatrix_apply] at hm
  change MvPolynomial.aeval z (M.submatrix rows id).det=0
  simpa only [φ, MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.coe_eval₂Hom] using hm.trans hd

theorem independentPoint_injective (p blocks : ℕ) (hblocks : 0<blocks) :
    Function.Injective (independentPoint (F := F) p blocks) := by
  intro γ δ h
  have hh := congrFun h ⟨0,hblocks⟩
  simpa only [independentPoint,pow_zero,pow_one] using hh

theorem frobenius_iterate_fixed (p : ℕ) (a : F) (ha : a^p=a) (b : ℕ) : a^(p^b)=a := by
  induction b with
  | zero => simp
  | succ b hb => rw [pow_succ,pow_mul,hb,ha]

end
end FrobeniusLocator.Strata
end PackSource_IndependentLocator

section PackSource_TopKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix
open scoped BigOperators
variable {F row : Type} [Field F] [Fintype row]

theorem first_columns_injective_of_kernel_line {r : ℕ} (M : Matrix row (Fin (r+1)) F)
    (q : Fin (r+1) → F) (hq : q (Fin.last r)≠0)
    (hline : ∀ v, M.mulVec v=0 → ∃ a : F, v=a • q) :
    Function.Injective (M.submatrix id Fin.castSucc).mulVecLin := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let w : Fin (r+1) → F := Fin.lastCases 0 v
  have hM : M.mulVec w=0 := by
    funext i
    change (∑ j : Fin (r+1), M i j*w j)=0
    rw [Fin.sum_univ_castSucc]
    simpa only [w,Fin.lastCases_castSucc,Fin.lastCases_last,mul_zero,add_zero,Matrix.mulVec,
      dotProduct,Matrix.submatrix_apply,id_eq,Matrix.mulVecLin_apply,Pi.zero_apply] using congrFun hv i
  obtain ⟨a,ha⟩ := hline w hM
  have hlast := congrFun ha (Fin.last r)
  have ha0 : a=0 := by
    have hz : a*q (Fin.last r)=0 := by simpa only [w,Fin.lastCases_last,Pi.smul_apply,smul_eq_mul] using hlast.symm
    exact (mul_eq_zero.mp hz).resolve_right hq
  funext j
  have hh := congrFun ha j.castSucc
  simpa only [w,Fin.lastCases_castSucc,ha0,zero_smul,Pi.zero_apply] using hh

theorem first_columns_rank_of_nullity_one {r : ℕ} (M : Matrix row (Fin (r+1)) F)
    (hnull : Module.finrank F (LinearMap.ker M.mulVecLin)=1)
    (q : Fin (r+1) → F) (hMq : M.mulVec q=0) (hq : q (Fin.last r)≠0) :
    (M.submatrix id Fin.castSucc).rank=r := by
  have hq0 : q≠0 := by intro hz; exact hq (congrFun hz (Fin.last r))
  have hline := GenericRank.kernel_line_of_finrank M hnull q hq0 hMq
  have hinj := first_columns_injective_of_kernel_line M q hq hline
  change Module.finrank F (LinearMap.range (M.submatrix id Fin.castSucc).mulVecLin)=r
  rw [LinearMap.finrank_range_of_inj hinj,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]

theorem rank_le_of_all_maximal_minors_zero {r : ℕ} (M : Matrix row (Fin (r+1)) F)
    (hminor : ∀ rows : Fin (r+1) → row, (M.submatrix rows id).det=0) : M.rank≤r := by
  classical
  by_contra hn
  have hr : M.rank=r+1 := by have hh := Matrix.rank_le_card_width M; rw [Fintype.card_fin] at hh; omega
  have hinj := matrix_injective_of_full_column_rank M (by simpa only [Fintype.card_fin] using hr)
  obtain ⟨rows,hrows⟩ := GenericRank.exists_rows_det_ne_zero M (fun v hv => hinj (hv.trans (map_zero M.mulVecLin).symm))
  exact hrows (hminor rows)

end
end FrobeniusLocator.Strata
end PackSource_TopKernel

section PackSource_MultivariateCofactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν : Type} [Field F]

theorem totalDegree_neg_le (p : MvPolynomial ν F) : (-p).totalDegree≤p.totalDegree := by
  have hh := MvPolynomial.totalDegree_smul_le (-1 : F) p
  simpa only [neg_one_smul] using hh

theorem totalDegree_sub_le (p q : MvPolynomial ν F) :
    (p-q).totalDegree≤max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl (totalDegree_neg_le q))

theorem lastCofactor_degree {r : ℕ} (N : Matrix (Fin r) (Fin (r+1)) (MvPolynomial ν F))
    (hN : ∀ i j, (N i j).totalDegree≤1) (c : Fin (r+1)) :
    (lastCofactor N c).totalDegree≤r := by
  classical
  have hsum : (∑ _i : Fin r, (1 : ℕ))=r := by simp
  rw [lastCofactor,GenericCofactor.rawVector_apply]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  apply (totalDegree_sub_le _ _).trans
  apply max_le
  · by_cases hc : Fin.last r=c
    · subst c
      simp only [Pi.single_eq_same,mul_one]
      exact (totalDegree_det_le_row_sum _ (fun _ => 1) (fun i j => hN i j.castSucc)).trans_eq hsum
    · simp [Pi.single_apply,hc,Ne.symm hc]
  · change (∑ q, GenericCofactor.inclusion Fin.castSucc c q*
      (N.submatrix id Fin.castSucc).cramer (fun q => N q (Fin.last r)) q).totalDegree≤r
    apply MvPolynomial.totalDegree_finsetSum_le
    intro q _
    by_cases hq : q.castSucc=c
    · simp only [GenericCofactor.inclusion,hq,Pi.single_eq_same,one_mul,Matrix.cramer_apply]
      apply (totalDegree_det_le_row_sum _ (fun _ => 1) ?_).trans_eq hsum
      intro i j
      by_cases hj : j=q
      · subst j
        simpa only [Matrix.updateCol_self] using hN i (Fin.last r)
      · simpa only [Matrix.updateCol_ne hj,Matrix.submatrix_apply,id_eq] using hN i j.castSucc
    · simp [GenericCofactor.inclusion,Pi.single_apply,hq,Ne.symm hq]

theorem lastCofactor_map {R S : Type} [CommRing R] [CommRing S] {r : ℕ}
    (φ : R →+* S) (N : Matrix (Fin r) (Fin (r+1)) R) (c : Fin (r+1)) :
    lastCofactor (N.map φ) c=φ (lastCofactor N c) :=
  GenericCofactor.map_rawVector φ N id Fin.castSucc (Fin.last r) c

/-- Evaluate the RS coordinate, retaining all independent slope parameters. -/
def multivariateNodeCut {r : ℕ} (Q : Fin (r+1) → MvPolynomial ν F) (a : F) : MvPolynomial ν F :=
  ∑ j, MvPolynomial.C (a^j.val)*Q j

theorem multivariateNodeCut_degree {r D : ℕ} (Q : Fin (r+1) → MvPolynomial ν F)
    (hQ : ∀ j, (Q j).totalDegree≤D) (a : F) : (multivariateNodeCut Q a).totalDegree≤D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C,zero_add] using hQ j)

theorem multivariateNodeCut_map {K : Type} [Field K] {r : ℕ}
    (φ : MvPolynomial ν F →+* K) (Q : Fin (r+1) → MvPolynomial ν F) (a : F) :
    φ (multivariateNodeCut Q a)=(Principal.assemble (fun j => φ (Q j))).eval (φ (MvPolynomial.C a)) := by
  simp only [multivariateNodeCut,map_sum,map_mul,Principal.assemble,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  have hp : φ (MvPolynomial.C (a^j.val))=(φ (MvPolynomial.C a))^j.val := by rw [← map_pow,← map_pow]
  rw [hp]
  ring

end
end FrobeniusLocator.Strata
end PackSource_MultivariateCofactor

section PackSource_PrincipalExtraction
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- Extract the counting certificate from generic homogeneous principality.
The fixed squarefree domain factor is supplied explicitly; it need not
include multiplicities. No per-slope or root-count premise is assumed. -/
theorem extract_moving_certificate_for_basis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (hp : 1 ≤ p) (x u v : ι → F)
    (m d q : ℕ) (H : Finset ι) (hd : 0 < d) (hL : H.card+d+q < m)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m (H.card+d) q)
    (f : K[X]) (hfd : f.natDegree ≤ d)
    (hfactor : P.generator=(locator x H).map (φ.comp (Polynomial.C : F →+* F[X]))*f)
    (hnode : ∀ i, i ∉ H → f.eval (φ (C (x i))) ≠ 0)
    (B : NormalFiber.RowBasis φ (stacked p x u v (m-(H.card+d+q)) (H.card+d+q)) (H.card+d)) :
    Nonempty (MovingPrincipalCertificate p x u v (m-(H.card+d+q)) (H.card+d+q)
      (NormalFiber.pivot B).det) := by
  classical
  let a := H.card+d
  let M := stacked p x u v (m-(a+q)) (a+q)
  let N := stacked p x u v (m-a) a
  let Hp := (locator x H).map (Polynomial.C : F →+* F[X])
  let Hk := Hp.map φ
  let R := restrictByFamily a d N Hp
  have hHp : Hp.natDegree ≤ H.card := Polynomial.natDegree_map_le.trans (by rw [locator_natDegree])
  have hHk : Hk.natDegree ≤ H.card := Polynomial.natDegree_map_le.trans hHp
  have hHk0 : Hk ≠ 0 := ((locator_monic x H).map (Polynomial.C : F →+* F[X])).map φ |>.ne_zero
  have hfac : P.generator=Hk*f := by simpa only [Hk,Hp,Polynomial.map_map] using hfactor
  have hf0 : f ≠ 0 := by intro hf; apply P.nonzero; rw [hfac,hf,mul_zero]
  have hsmallLine := P.small_kernel_line hL
  rw [recurrenceMatrix_parameter] at hsmallLine
  rw [hfac] at hsmallLine
  have hRmap : R.map φ=restrictByFamily a d (N.map φ) Hk :=
    restrictByFamily_map a d φ N Hp
  have hRline : LinearMap.ker (R.map φ).mulVecLin =
      K ∙ (fun j : Fin (d+1) => f.coeff j.val) := by
    rw [hRmap]
    exact restricted_kernel_line a H.card d rfl (N.map φ) Hk f hHk0 hHk hfd hsmallLine
  have hfv : (fun j : Fin (d+1) => f.coeff j.val) ≠ 0 := by
    intro hz
    apply hf0
    apply coefficients_injective_bounded d f 0 hfd (by simp)
    intro j
    simpa using congrFun hz j
  have hRnull : Module.finrank K (LinearMap.ker (R.map φ).mulVecLin)=1 := by
    rw [hRline,finrank_span_singleton hfv]
  have hRrank : (R.map φ).rank=d := by
    have hn := LinearMap.finrank_range_add_finrank_ker (R.map φ).mulVecLin
    change (R.map φ).rank+_= _ at hn
    rw [hRnull,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hn
    omega
  obtain ⟨Bsmall⟩ := NormalFiber.exists_rowBasis φ R d hRrank
  have hFE : (R.map φ).mulVec (fun j : Fin (d+1) => f.coeff j.val)=0 := by
    change (fun j : Fin (d+1) => f.coeff j.val) ∈ LinearMap.ker (R.map φ).mulVecLin
    rw [hRline]
    exact Submodule.mem_span_singleton_self _
  have hRdeg : ∀ i j, (R i j).natDegree ≤ p := by
    intro i j
    apply restricted_natDegree_le a d N (locator x H) (fun _ => p) _ i j
    intro l k
    exact (stacked_entry_natDegree p x u v (m-a) a l k).trans (by split_ifs <;> omega)
  obtain ⟨coeffs,hprimitive,hRcoeff,hdegree,heval⟩ := exists_primitive_kernel_vector
    φ hφ R d Bsmall (fun _ => p) hRdeg _ hfv hFE
  have hdegree' : ∀ j, (coeffs j).natDegree ≤ p*d := by
    intro j
    simpa [Nat.mul_comm] using hdegree j
  have hspec : ∀ γ, specialize coeffs γ ≠ 0 := by
    intro γ
    rw [specialize_eq_assemble]
    apply assemble_ne_zero
    intro hz
    obtain ⟨j,hj⟩ := heval γ
    exact hj (congrFun hz j)
  have hgeneric : (R.map φ).mulVec (fun j => φ (coeffs j))=0 := by
    funext i
    have hi := congrArg φ (congrFun hRcoeff i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,Matrix.map_apply,Pi.zero_apply] using hi
  have hmem : (fun j => φ (coeffs j)) ∈ LinearMap.ker (R.map φ).mulVecLin := hgeneric
  rw [hRline] at hmem
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hgpoly : assemble (fun j => φ (coeffs j))=c • f := by
    apply coefficients_injective_bounded d
    · exact assemble_natDegree_le _
    · exact (Polynomial.natDegree_smul_le _ _).trans hfd
    · intro j
      have hj := congrFun hc j
      simpa only [assemble_coeff,Polynomial.coeff_smul,Pi.smul_apply,smul_eq_mul] using hj.symm
  have hc0 : c ≠ 0 := by
    intro hz
    have hzero : assemble (fun j => φ (coeffs j))=0 := by simpa [hz] using hgpoly
    obtain ⟨j,hj⟩ := heval 0
    have hj0 := congrArg (fun Q : K[X] => Q.coeff j.val) hzero
    have hcz : coeffs j=0 := hφ (by simpa only [assemble_coeff,coeff_zero,map_zero] using hj0)
    simp [hcz] at hj
  have hnofixed : ∀ i, i ∉ H → nodePolynomial coeffs (x i) ≠ 0 := by
    intro i hi hz
    have he := nodePolynomial_generic_eval φ coeffs (x i)
    rw [hz,map_zero,hgpoly,Polynomial.eval_smul,smul_eq_mul] at he
    exact (mul_ne_zero hc0 (hnode i hi)) he.symm
  let G := Hp*assemble coeffs
  have hGdegree : G.natDegree ≤ a :=
    Polynomial.natDegree_mul_le.trans (by have := assemble_natDegree_le coeffs; omega)
  have hGker : N.mulVec (fun j : Fin (a+1) => G.coeff j.val)=0 := by
    rw [← restrictByFamily_mulVec a d N Hp coeffs]
    exact hRcoeff
  have hGmap (γ : F) : G.map (Polynomial.evalRingHom γ)=locator x H*specialize coeffs γ := by
    rw [Polynomial.map_mul,assemble_map_eval]
    have hHpEval : Hp.map (Polynomial.evalRingHom γ)=locator x H := by
      ext j
      simp only [Hp,Polynomial.coeff_map,Polynomial.coe_evalRingHom,eval_C]
    rw [hHpEval]
  have hshift : ∀ γ (Q : Polynomial.degreeLT F (q+1)),
      (M.map (Polynomial.evalRingHom γ)).mulVec
        (multipleCoefficients (locator x H*specialize coeffs γ) q (a+q) Q)=0 := by
    intro γ Q
    have hh := family_multiples_annihilate p x u v m a q (by omega) G hGdegree hGker γ Q
    rw [hGmap] at hh
    exact hh
  refine ⟨?_⟩
  exact movingCertificateOfRowBasis φ hφ p x u v (m-(a+q)) (a+q)
    H d q hd rfl B coeffs hdegree' hspec hnofixed hshift

end
end FrobeniusLocator.Principal
end PackSource_PrincipalExtraction

section PackSource_PrimeGeneric
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν : Type} [Field F]

abbrev PrimeGenericField (P : Ideal (MvPolynomial ν F)) [P.IsPrime] :=
  FractionRing (MvPolynomial ν F ⧸ P)

def primeGenericMap (P : Ideal (MvPolynomial ν F)) [P.IsPrime] :
    MvPolynomial ν F →+* PrimeGenericField P :=
  (algebraMap (MvPolynomial ν F ⧸ P) (PrimeGenericField P)).comp (Ideal.Quotient.mk P)

theorem primeGenericMap_zero_iff (P : Ideal (MvPolynomial ν F)) [P.IsPrime] (f : MvPolynomial ν F) :
    primeGenericMap P f=0 ↔ f∈P := by
  constructor
  · intro hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (MvPolynomial ν F ⧸ P) (PrimeGenericField P)
    exact hz.trans (map_zero _).symm
  · intro hf
    change algebraMap (MvPolynomial ν F ⧸ P) (PrimeGenericField P) (Ideal.Quotient.mk P f)=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf,map_zero]

theorem primeGenericMap_nonzero_of_point (P : Ideal (MvPolynomial ν F)) [P.IsPrime]
    (z : ν → F) (hz : z∈zeroLocus F P) (f : MvPolynomial ν F) (hf : aeval z f≠0) :
    primeGenericMap P f≠0 := by
  intro hzero
  exact hf (hz f ((primeGenericMap_zero_iff P f).mp hzero))

theorem generic_rank_le_of_maximal_minors {row : Type} [Fintype row] {r : ℕ}
    (P : Ideal (MvPolynomial ν F)) [P.IsPrime]
    (M : Matrix row (Fin (r+1)) (MvPolynomial ν F))
    (hminor : ∀ rows : Fin (r+1) → row, (M.submatrix rows id).det∈P) :
    (M.map (primeGenericMap P)).rank≤r := by
  classical
  apply rank_le_of_all_maximal_minors_zero
  intro rows
  have hh := (primeGenericMap P).map_det (M.submatrix rows id)
  rw [RingHom.mapMatrix_apply] at hh
  have heq : (M.map (primeGenericMap P)).submatrix rows id=
      (M.submatrix rows id).map (primeGenericMap P) := rfl
  rw [heq,← hh]
  exact (primeGenericMap_zero_iff P _).mpr (hminor rows)

end
end FrobeniusLocator.Strata
end PackSource_PrimeGeneric

section PackSource_ComponentCofactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν row : Type} [Field F] [Fintype row] [DecidableEq row]

theorem aeval_self_eq_evalHom (z : ν → F) (f : MvPolynomial ν F) :
    MvPolynomial.aeval z f=MvPolynomial.eval₂Hom (RingHom.id F) z f := by
  simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.coe_eval₂Hom]

/-- Bounded compressed cofactors annihilate the full matrix modulo a
prime whenever the generic rank is at most the compressed row count. -/
theorem compressed_cofactor_mod_prime {r : ℕ}
    (P : Ideal (MvPolynomial ν F)) [P.IsPrime]
    (M : Matrix row (Fin (r+1)) (MvPolynomial ν F)) (C : Matrix (Fin r) row F)
    (hM : ∀ i j, (M i j).totalDegree≤1)
    (hrank : (M.map (primeGenericMap P)).rank≤r)
    (hdet : (((C.map MvPolynomial.C*M).submatrix id Fin.castSucc).det)∉P) :
    let N := C.map MvPolynomial.C*M
    (∀ j, (lastCofactor N j).totalDegree≤r) ∧
      (∀ i, M.mulVec (lastCofactor N) i∈P) := by
  classical
  let N := C.map MvPolynomial.C*M
  let φ := primeGenericMap P
  let C' := C.map (φ.comp MvPolynomial.C)
  have hNmap : N.map φ=C'*(M.map φ) := by
    ext i j
    simp only [N,C',Matrix.map_apply,Matrix.mul_apply,map_sum,map_mul,RingHom.comp_apply]
  have hmap := φ.map_det (N.submatrix id Fin.castSucc)
  rw [RingHom.mapMatrix_apply] at hmap
  have hdetK : ((C'*(M.map φ)).submatrix id Fin.castSucc).det≠0 := by
    rw [← hNmap]
    change ((N.submatrix id Fin.castSucc).map φ).det≠0
    rw [← hmap]
    exact fun hz => hdet ((primeGenericMap_zero_iff P _).mp hz)
  have hk := (compressed_lastCofactor_kernel (M.map φ) C' hdetK hrank).1
  have hqmap : lastCofactor (C'*(M.map φ))=fun j => φ (lastCofactor N j) := by
    rw [← hNmap]
    funext j
    exact lastCofactor_map φ N j
  rw [hqmap] at hk
  refine ⟨?_,?_⟩
  · have hN : ∀ i j, (N i j).totalDegree≤1 := by
      intro i j
      change (∑ k : row, MvPolynomial.C (C i k)*M k j).totalDegree≤1
      apply MvPolynomial.totalDegree_finsetSum_le
      intro k _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C,zero_add] using hM k j)
    exact lastCofactor_degree N hN
  · intro i
    apply (primeGenericMap_zero_iff P _).mp
    have hh := congrFun hk i
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,map_mul,Pi.zero_apply] using hh

/-- One bounded cofactor section is valid at ALL selected regular points
of a component. The chosen compression is common to the whole finite
selected set; the generic kernel and top coordinate are certified. -/
theorem exists_component_cofactor [Fintype F] [DecidableEq F] {r : ℕ}
    (P : Ideal (MvPolynomial ν F)) [P.IsPrime]
    (M : Matrix row (Fin (r+1)) (MvPolynomial ν F)) (hM : ∀ i j, (M i j).totalDegree≤1)
    (hrank : (M.map (primeGenericMap P)).rank≤r)
    (S : Finset (ν → F)) (hSne : S.Nonempty) (hSP : ∀ z∈S, z∈zeroLocus F P)
    (hfirst : ∀ z∈S, ((M.map (MvPolynomial.eval₂Hom (RingHom.id F) z)).submatrix id Fin.castSucc).rank=r)
    (hcard : S.card*r<Fintype.card F) :
    ∃ Q : Fin (r+1) → MvPolynomial ν F,
      (∀ j, (Q j).totalDegree≤r) ∧ (∀ i, M.mulVec Q i∈P) ∧ Q (Fin.last r)∉P ∧
      ∀ z∈S, MvPolynomial.aeval z (Q (Fin.last r))≠0 := by
  classical
  let A : (ν → F) → Matrix row (Fin r) F := fun z =>
    (M.map (MvPolynomial.eval₂Hom (RingHom.id F) z)).submatrix id Fin.castSucc
  obtain ⟨C,hC⟩ := exists_common_row_compression S r A hfirst hcard
  let N := C.map MvPolynomial.C*M
  let Δ := (N.submatrix id Fin.castSucc).det
  have heval (z : ν → F) : MvPolynomial.aeval z Δ=(C*A z).det := by
    rw [aeval_self_eq_evalHom]
    let ψ := MvPolynomial.eval₂Hom (RingHom.id F) z
    have hh := ψ.map_det (N.submatrix id Fin.castSucc)
    rw [RingHom.mapMatrix_apply] at hh
    change ψ Δ=(C*A z).det
    rw [hh]
    congr 1
    ext i j
    simp only [N,A,Matrix.map_apply,Matrix.submatrix_apply,id_eq,Matrix.mul_apply,map_sum,map_mul,
      ψ,MvPolynomial.eval₂Hom_C,RingHom.id_apply]
  have hΔ (z : ν → F) (hz : z∈S) : MvPolynomial.aeval z Δ≠0 := by rw [heval]; exact hC z hz
  have hΔP : Δ∉P := by
    obtain ⟨z,hz⟩ := hSne
    intro hmem
    exact hΔ z hz (hSP z hz Δ hmem)
  obtain ⟨hdeg,hkernel⟩ := compressed_cofactor_mod_prime P M C hM hrank hΔP
  refine ⟨lastCofactor N,hdeg,hkernel,?_,?_⟩
  · rwa [lastCofactor_last]
  · intro z hz
    rw [lastCofactor_last]
    exact hΔ z hz

end
end FrobeniusLocator.Strata
end PackSource_ComponentCofactor

section PackSource_RestrictionKernel
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F row : Type} [Field F] [Fintype row]

/-- Multiplication by a fixed nonzero polynomial transports a kernel
LINE to its deflated line, with nominal degree budgets retained. -/
theorem restriction_kernel_line (t b d : ℕ) (M : Matrix row (Fin (t+1)) F)
    (g q : F[X]) (hg : g≠0) (hgd : g.natDegree≤b) (hqd : q.natDegree≤d) (hsize : b+d≤t)
    (hline : ∀ v, M.mulVec v=0 → ∃ a : F, v=a • (fun j : Fin (t+1) => (g*q).coeff j.val))
    (v : Fin (d+1) → F) (hv : (Principal.restrictByFamily t d M g).mulVec v=0) :
    ∃ a : F, v=a • (fun j : Fin (d+1) => q.coeff j.val) := by
  let f := Principal.assemble v
  have hfd : f.natDegree≤d := Principal.assemble_natDegree_le v
  rw [Principal.restrictByFamily_mulVec] at hv
  obtain ⟨a,ha⟩ := hline _ hv
  have hgf : (g*f).natDegree≤t := Polynomial.natDegree_mul_le.trans (by omega)
  have hgq : (a • (g*q)).natDegree≤t := (Polynomial.natDegree_smul_le a (g*q)).trans
    (Polynomial.natDegree_mul_le.trans (by omega))
  have hpoly : g*f=a • (g*q) := Principal.coefficients_injective_bounded t _ _ hgf hgq (by
    intro j
    have hh := congrFun ha j
    simpa only [Polynomial.coeff_smul,Pi.smul_apply] using hh)
  have hfq : f=a • q := by
    apply mul_left_cancel₀ hg
    rw [hpoly,mul_smul_comm]
  refine ⟨a,?_⟩
  funext j
  have hc := congrArg (fun P : F[X] => P.coeff j.val) hfq
  simpa only [f,Principal.assemble_coeff,Polynomial.coeff_smul,Pi.smul_apply] using hc

/-- Deflation preserves one-dimensionality of a kernel generated by g*q. -/
theorem restriction_nullity_one (t b d : ℕ) (M : Matrix row (Fin (t+1)) F)
    (g q : F[X]) (hg : g≠0) (hq : q≠0) (hgd : g.natDegree≤b) (hqd : q.natDegree≤d) (hsize : b+d≤t)
    (hgen : M.mulVec (fun j : Fin (t+1) => (g*q).coeff j.val)=0)
    (hline : ∀ v, M.mulVec v=0 → ∃ a : F, v=a • (fun j : Fin (t+1) => (g*q).coeff j.val)) :
    Module.finrank F (LinearMap.ker (Principal.restrictByFamily t d M g).mulVecLin)=1 := by
  classical
  let qv := fun j : Fin (d+1) => q.coeff j.val
  have hqv : qv≠0 := by
    intro hz
    apply hq
    apply Principal.coefficients_injective_bounded d q 0 hqd (by simp)
    intro j
    exact congrFun hz j
  have hqker : (Principal.restrictByFamily t d M g).mulVec qv=0 := by
    rw [Principal.restrictByFamily_mulVec,Principal.assemble_coefficients d q hqd]
    exact hgen
  have heq : LinearMap.ker (Principal.restrictByFamily t d M g).mulVecLin=F ∙ qv := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a,ha⟩ := restriction_kernel_line t b d M g q hg hgd hqd hsize hline v hv
      exact Submodule.mem_span_singleton.mpr ⟨a,ha.symm⟩
    · apply Submodule.span_le.mpr
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      exact hv ▸ hqker
  rw [heq]
  exact finrank_span_singleton hqv

/-- A fixed F[X] multiplier leaves every independent-parameter row-degree
budget unchanged. -/
theorem multivariate_restriction_degree {ν : Type} (t d : ℕ)
    (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) (g : F[X]) (D : row → ℕ)
    (hM : ∀ i j, (M i j).totalDegree≤D i) :
    ∀ i j, (Principal.restrictByFamily t d M (g.map (MvPolynomial.C : F →+* MvPolynomial ν F)) i j).totalDegree≤D i := by
  intro i j
  simp only [Principal.restrictByFamily,Matrix.mul_apply,Principal.multiplicationMatrix]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l _
  have hc : ((g.map MvPolynomial.C)*(Polynomial.X : Polynomial (MvPolynomial ν F))^j.val).coeff l.val=
      MvPolynomial.C ((g*(Polynomial.X : F[X])^j.val).coeff l.val) := by
    rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  rw [hc]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C,add_zero] using hM i l)

end
end FrobeniusLocator.Strata
end PackSource_RestrictionKernel

section PackSource_PrincipalConstantExtraction
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

theorem principal_rowBasis (φ : F[X] →+* K) (p : ℕ) (x u v : ι → F)
    (m a q : ℕ)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m a q) :
    Nonempty (NormalFiber.RowBasis φ (stacked p x u v (m-(a+q)) (a+q)) a) := by
  let M := stacked p x u v (m-(a+q)) (a+q)
  have hnull := P.big_nullity
  rw [recurrenceMatrix_parameter] at hnull
  have hrank : (M.map φ).rank=a := by
    have hn := LinearMap.finrank_range_add_finrank_ker (M.map φ).mulVecLin
    change (M.map φ).rank+_= _ at hn
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hn
    change Module.finrank K (LinearMap.ker (M.map φ).mulVecLin)=q+1 at hnull
    omega
  exact NormalFiber.exists_rowBasis φ M a hrank

/-- A generic fixed generator gives a genuine fixed coefficient kernel;
the generic scalar is cancelled before specialization, not evaluated. -/
theorem extract_constant_certificate_for_basis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) (x u v : ι → F) (m a q : ℕ) (H : Finset ι) (hHa : H.card=a)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m a q)
    (c : K) (hc : c ≠ 0)
    (hgen : P.generator=c • ((locator x H).map (φ.comp (Polynomial.C : F →+* F[X]))))
    (B : NormalFiber.RowBasis φ (stacked p x u v (m-(a+q)) (a+q)) a) :
    Nonempty (ConstantKernelCertificate p x u v (m-(a+q)) (a+q)
      (NormalFiber.pivot B).det) := by
  classical
  let M := stacked p x u v (m-(a+q)) (a+q)
  let ρ := φ.comp (Polynomial.C : F →+* F[X])
  let HK := (locator x H).map ρ
  let W := LinearMap.range (multipleCoefficients (locator x H) q (a+q))
  have hHdeg : (locator x H).natDegree ≤ a := by rw [locator_natDegree,hHa]
  have hinj := multipleCoefficients_injective (locator x H) a q (a+q)
    (locator_monic x H).ne_zero hHdeg (by omega)
  have hWdim : Module.finrank F W=a+q+1-a := by
    have hh := LinearMap.finrank_range_of_inj hinj
    change Module.finrank F W=Module.finrank F (Polynomial.degreeLT F (q+1)) at hh
    rw [hh,(Polynomial.degreeLTEquiv F (q+1)).finrank_eq,Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
    omega
  have hW : ∀ w ∈ W, M.mulVec (fun j => C (w j))=0 := by
    rintro _ ⟨Q,rfl⟩
    let QK := (Q : F[X]).map ρ
    have hQK : QK.natDegree ≤ q := Polynomial.natDegree_map_le.trans (degreeLT_natDegree_le Q)
    have hproduct : P.generator*(c⁻¹ • QK)=HK*QK := by
      rw [hgen]
      change (c • HK)*(c⁻¹ • QK)=HK*QK
      calc
        _ = (c*c⁻¹) • (HK*QK) := by simp only [Polynomial.smul_eq_C_mul,map_mul]; ring
        _ = _ := by rw [mul_inv_cancel₀ hc,one_smul]
    have hrec : InRecurrenceKernel
        (fun b j => φ (parameterSyndromes p x u v b j)) m (a+q) (HK*QK) := by
      apply (P.kernel_eq _).mpr
      exact ⟨c⁻¹ • QK,(Polynomial.natDegree_smul_le _ _).trans hQK,hproduct.symm⟩
    have hgeneric := ((recurrence_kernel_iff_matrix _ m (a+q) _).mp hrec).2
    rw [recurrenceMatrix_parameter] at hgeneric
    let E := (locator x H*(Q:F[X])).map (Polynomial.C : F →+* F[X])
    have hEmap : E.map φ=HK*QK := by simp only [E,HK,QK,Polynomial.map_map,Polynomial.map_mul,ρ]
    have hgenericE : (M.map φ).mulVec
        (fun j : Fin (a+q+1) => (E.map φ).coeff j.val)=0 := by rw [hEmap]; exact hgeneric
    have hpoly := family_kernel_of_map φ hφ M E (fun j : Fin (a+q+1) => j.val) hgenericE
    change M.mulVec (fun j : Fin (a+q+1) => C ((locator x H*(Q:F[X])).coeff j.val))=0
    simpa only [E,Polynomial.coeff_map] using hpoly
  exact ⟨constantCertificateOfRowBasis φ hφ p x u v (m-(a+q)) (a+q) a B W hWdim hW⟩

end
end FrobeniusLocator.Principal
end PackSource_PrincipalConstantExtraction

section PackSource_GenericFixedRoots
set_option autoImplicit true
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- Remove all generic fixed domain roots, with the squarefree factor
and the remaining nominal homogeneous degree recorded exactly. -/
theorem generic_fixed_root_factor (ρ : F →+* K) (x : ι → F)
    (hx : Function.Injective x) (g : K[X]) (hg : g ≠ 0) (a : ℕ)
    (hga : g.natDegree ≤ a) :
    ∃ (H : Finset ι) (d : ℕ) (f : K[X]), H.card+d=a ∧ f.natDegree ≤ d ∧
      g=(locator x H).map ρ*f ∧ (∀ i, i ∉ H → f.eval (ρ (x i)) ≠ 0) := by
  classical
  let xK := fun i => ρ (x i)
  have hxK : Function.Injective xK := ρ.injective.comp hx
  let H := Finset.univ.filter (fun i => g.eval (xK i)=0)
  have hle : (locator xK H).roots ≤ g.roots := by
    rw [locator_roots]
    apply (Multiset.le_iff_subset (H.nodup.map hxK)).mpr
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hz
    exact (Polynomial.mem_roots hg).mpr ((Finset.mem_filter.mp hi).2)
  have hdiv : locator xK H ∣ g := (locator_splits xK H).dvd_of_roots_le_roots
    (locator_monic xK H).ne_zero hle
  obtain ⟨f,hf⟩ := hdiv
  have hf0 : f ≠ 0 := by intro hz; apply hg; rw [hf,hz,mul_zero]
  have hdegree : H.card+f.natDegree=g.natDegree := by
    rw [hf,Polynomial.natDegree_mul (locator_monic xK H).ne_zero hf0,locator_natDegree]
  have hHa : H.card ≤ a := by omega
  refine ⟨H,a-H.card,f,by omega,by omega,?_,?_⟩
  · rw [locator_map]
    exact hf
  · intro i hi hzero
    have hgi : g.eval (xK i) ≠ 0 := by
      simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    apply hgi
    rw [hf,eval_mul]
    change (locator xK H).eval (xK i)*f.eval (ρ (x i))=0
    rw [hzero,mul_zero]

end
end FrobeniusLocator.Principal
end PackSource_GenericFixedRoots

section PackSource_GenericPrincipalCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- Bare generic principality suffices at every nullity. All fixed roots,
primitive normalization, cofactor heights, and normal-fiber multiplicities
are derived, including the constant-generator and infinity cases. -/
theorem generic_principal_bad_count_for_basis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (hp : 1 ≤ p) (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i^p=x i) (u v : ι → F) (k m a q : ℕ)
    (hkm : k+m=Fintype.card ι) (hL : a+q < m)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m a q)
    (B : NormalFiber.RowBasis φ (stacked p x u v (m-(a+q)) (a+q)) a)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k (k+(m-(a+q))) γ) :
    Γ.card ≤ (∑ i, if (B.rows i).1=0 then 1 else p)+p*Fintype.card ι := by
  classical
  obtain ⟨H,d,f,ha,hfd,hfactor,hnode⟩ := generic_fixed_root_factor
    (φ.comp (Polynomial.C : F →+* F[X])) x hx P.generator P.nonzero a P.degree_bound
  subst a
  by_cases hd : d=0
  · subst d
    simp only [Nat.add_zero] at *
    have hfC : f=C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hc : f.coeff 0 ≠ 0 := by
      intro hz
      apply P.nonzero
      rw [hfactor,hfC,hz,C_0,mul_zero]
    have hgen : P.generator=f.coeff 0 •
        ((locator x H).map (φ.comp (Polynomial.C : F →+* F[X]))) := by
      rw [hfactor,hfC,Polynomial.smul_eq_C_mul]
      simp only [coeff_C_zero]
      ring
    obtain ⟨cert⟩ := extract_constant_certificate_for_basis φ hφ p x u v m H.card q H rfl P _ hc hgen B
    have hh := constant_kernel_count p x hx hfixed u v k (k+(m-(H.card+q)))
      (m-(H.card+q)) (H.card+q) _ (by omega) rfl (by omega)
      (NormalFiber.pivot B).det B.minor_ne
      (NormalFiber.minor_degree_le φ _ _ B _ (stacked_entry_natDegree p x u v _ _)) cert Γ hΓ
    exact hh.trans (Nat.le_add_right _ _)
  · have hdpos : 0 < d := by omega
    obtain ⟨cert⟩ := extract_moving_certificate_for_basis φ hφ p hp x u v m d q H hdpos hL
      P f hfd hfactor hnode B
    have hh := principal_bad_count p x hx hfixed u v k (k+(m-(H.card+d+q)))
      (m-(H.card+d+q)) (H.card+d+q) _ (by omega) rfl (by omega)
      (NormalFiber.pivot B).det B.minor_ne
      (NormalFiber.minor_degree_le φ _ _ B _ (stacked_entry_natDegree p x u v _ _)) cert Γ hΓ
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_left p (Nat.sub_le _ _)) _)

theorem generic_principal_bad_count (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (hp : 1 ≤ p) (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i^p=x i) (u v : ι → F) (k m a q : ℕ)
    (hkm : k+m=Fintype.card ι) (hL : a+q < m)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m a q)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k (k+(m-(a+q))) γ) :
    ∃ B : NormalFiber.RowBasis φ (stacked p x u v (m-(a+q)) (a+q)) a,
      Γ.card ≤ (∑ i, if (B.rows i).1=0 then 1 else p)+p*Fintype.card ι := by
  obtain ⟨B⟩ := principal_rowBasis φ p x u v m a q P
  exact ⟨B,generic_principal_bad_count_for_basis φ hφ p hp x hx hfixed u v k m a q hkm hL P B Γ hΓ⟩

theorem generic_principal_bad_count_coarse (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (p : ℕ) [ExpChar F p] (hp : 1 ≤ p) (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i^p=x i) (u v : ι → F) (k m a q : ℕ)
    (hkm : k+m=Fintype.card ι) (hL : a+q < m)
    (P : PrincipalAt (fun b j => φ (parameterSyndromes p x u v b j)) m a q)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, BadSlope x u v k (k+(m-(a+q))) γ) :
    Γ.card ≤ p*(Fintype.card ι+a) := by
  obtain ⟨B,hcount⟩ := generic_principal_bad_count φ hφ p hp x hx hfixed u v k m a q hkm hL P Γ hΓ
  have hdegree : (∑ i, if (B.rows i).1=0 then 1 else p) ≤ p*a := by
    calc
      _ ≤ ∑ _i : Fin a, p := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ p*a+p*Fintype.card ι := hcount.trans (Nat.add_le_add_right hdegree _)
    _ = _ := by ring

end
end FrobeniusLocator.Principal
end PackSource_GenericPrincipalCount

section PackSource_PolynomialKernelLine
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F row : Type} [Field F] [Fintype row]

theorem assemble_smul_vector {R : Type} [CommRing R] {t : ℕ} (a : R) (v : Fin (t+1) → R) :
    Principal.assemble (a • v)=a • Principal.assemble v := by
  simp only [Principal.assemble,Pi.smul_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.smul_monomial]

theorem polynomial_from_kernel_line {t : ℕ} (M : Matrix row (Fin (t+1)) F)
    (hnull : Module.finrank F (LinearMap.ker M.mulVecLin)=1)
    (g : F[X]) (hg : g≠0) (hgd : g.natDegree≤t)
    (hMg : M.mulVec (fun j : Fin (t+1) => g.coeff j.val)=0)
    (q : Fin (t+1) → F) (hMq : M.mulVec q=0) (hqtop : q (Fin.last t)≠0) :
    ∃ a : F, a≠0 ∧ Principal.assemble q=a • g := by
  classical
  have hgv : (fun j : Fin (t+1) => g.coeff j.val)≠0 := by
    intro hz
    apply hg
    apply Principal.coefficients_injective_bounded t g 0 hgd (by simp)
    exact fun j => congrFun hz j
  obtain ⟨a,ha⟩ := GenericRank.kernel_line_of_finrank M hnull _ hgv hMg q hMq
  have ha0 : a≠0 := by
    intro hz
    exact hqtop (by rw [ha,hz,zero_smul]; rfl)
  refine ⟨a,ha0,?_⟩
  rw [ha,assemble_smul_vector,Principal.assemble_coefficients t g hgd]

section Parameter
variable {ν : Type} {t : ℕ}

theorem component_kernel_specializes (P : Ideal (MvPolynomial ν F))
    (M : Matrix row (Fin (t+1)) (MvPolynomial ν F)) (Q : Fin (t+1) → MvPolynomial ν F)
    (hkernel : ∀ i, M.mulVec Q i∈P) (z : ν → F) (hz : z∈MvPolynomial.zeroLocus F P) :
    (M.map (MvPolynomial.eval₂Hom (RingHom.id F) z)).mulVec
      (fun j => MvPolynomial.eval₂Hom (RingHom.id F) z (Q j))=0 := by
  funext i
  have hh := hz (M.mulVec Q i) (hkernel i)
  rw [aeval_self_eq_evalHom] at hh
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,map_mul,Pi.zero_apply] using hh

theorem multivariateNodeCut_eval (Q : Fin (t+1) → MvPolynomial ν F) (z : ν → F) (a : F) :
    MvPolynomial.aeval z (multivariateNodeCut Q a)=
      (Principal.assemble (fun j => MvPolynomial.eval₂Hom (RingHom.id F) z (Q j))).eval a := by
  rw [aeval_self_eq_evalHom,multivariateNodeCut_map]
  simp only [MvPolynomial.eval₂Hom_C,RingHom.id_apply]
end Parameter

end
end FrobeniusLocator.Strata
end PackSource_PolynomialKernelLine

section PackSource_CertificateSpecialization
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- The primitive GLOBAL polynomial relation specializes nontrivially at
EVERY finite slope, with the same strict output-degree guard. -/
theorem certificate_specializes (p : ℕ) [ExpChar F p] (x u v : ι → F) (k H : ℕ)
    (Crt : PolynomialRelationCertificate p x u v k H) (γ : F) :
    let U := (Principal.assemble (fun j => Crt.coefficients (0,j))).map (Polynomial.evalRingHom γ)
    let V := (Principal.assemble (fun j => Crt.coefficients (1,j))).map (Polynomial.evalRingHom γ)
    let R := Crt.output.map (Polynomial.evalRingHom γ)
    (U≠0 ∨ V≠0) ∧ TwistedRelation (frobenius F p) x (fun i => u i+γ*v i) k H U V R := by
  let φ := Polynomial.evalRingHom γ
  have hne := assembled_pair_ne_zero H (fun b => (Crt.coefficients b).eval γ)
    (PrimitiveVector.eval_ne_zero _ Crt.primitive γ)
  have hu (b : Fin 2) : (Principal.assemble (fun j => Crt.coefficients (b,j))).map φ=
      Principal.assemble (fun j => (Crt.coefficients (b,j)).eval γ) := by
    rw [Principal.assemble_map_eval,Principal.specialize_eq_assemble]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [Principal.assemble_map_eval,Principal.specialize_eq_assemble] using hne
  · exact Polynomial.natDegree_map_le.trans (Crt.x_degree 0)
  · exact Polynomial.natDegree_map_le.trans (Crt.x_degree 1)
  · exact Polynomial.degree_map_le.trans_lt Crt.output_degree
  · intro i
    have hA (P : Polynomial (Polynomial F)) : (P.map φ).eval (x i)=φ (P.eval (Polynomial.C (x i))) := by
      simpa only [φ,Polynomial.coe_evalRingHom,Polynomial.eval_C] using
        (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (Polynomial.C (x i)) (p := P))
    have hh := congrArg φ (Crt.nodes i)
    simp only [map_add,map_mul,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow] at hh
    rw [← hA,← hA,← hA] at hh
    have hp : (u i+γ*v i)^p=u i^p+γ^p*v i^p := by
      have hp := map_add (frobenius F p) (u i) (γ*v i)
      rw [map_mul] at hp
      exact hp
    simpa only [φ,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow,frobenius_def,← hp] using hh

/-- The requested all-node error equation, now directly from a primitive
polynomial-family certificate rather than a supplied specialized relation. -/
theorem certificate_error_identity (p : ℕ) [ExpChar F p]
    (x u v : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i^p=x i)
    (k H : ℕ) (Crt : PolynomialRelationCertificate p x u v k H) (γ : F)
    (S : Finset ι) (hS : k+H≤S.card) (P : F[X]) (hP : P.degree<k)
    (hagree : ∀ i∈S, P.eval (x i)=u i+γ*v i) (i : ι) :
    ((Principal.assemble (fun j => Crt.coefficients (0,j))).map (Polynomial.evalRingHom γ)).eval (x i)*
      (u i+γ*v i-P.eval (x i))+
    ((Principal.assemble (fun j => Crt.coefficients (1,j))).map (Polynomial.evalRingHom γ)).eval (x i)*
      (u i+γ*v i-P.eval (x i))^p=0 := by
  have hrel := (certificate_specializes p x u v k H Crt γ).2
  exact frobenius_error_identity p x _ hx hfixed k H _ _ _ hrel S hS P hP hagree i

end
end FrobeniusLocator.Strata
end PackSource_CertificateSpecialization

section PackSource_AffineLocator
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι ν : Type} [Field F] [Fintype ι] [DecidableEq ι]

def affineLocator (σ : ν → F →+* F) (x u v : ι → F) (L t : ℕ) :
    Matrix (ν × Fin L) (Fin (t+1)) (MvPolynomial ν F) := fun b j =>
  MvPolynomial.C (σ b.1 (syndrome x u (b.2.val+j.val)))+
    MvPolynomial.X b.1*MvPolynomial.C (σ b.1 (syndrome x v (b.2.val+j.val)))

theorem affineLocator_entry_degree (σ : ν → F →+* F) (x u v : ι → F) (L t : ℕ)
    (b : ν × Fin L) (j : Fin (t+1)) : (affineLocator σ x u v L t b j).totalDegree≤1 := by
  unfold affineLocator
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C]; omega
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_X,MvPolynomial.totalDegree_C,add_zero]; omega)

theorem affineLocator_eval_slope (σ : ν → F →+* F) (x u v : ι → F) (L t : ℕ) (γ : F) :
    (affineLocator σ x u v L t).map (MvPolynomial.eval₂Hom (RingHom.id F) (fun b => σ b γ))=
      conjugateHankel σ x (fun i => u i+γ*v i) L t := by
  ext b j
  have hs := Principal.syndrome_linear x u v 1 γ (b.2.val+j.val)
  simp only [one_mul] at hs
  simp only [Matrix.map_apply,affineLocator,map_add,map_mul,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',RingHom.id_apply,conjugateHankel,hs]

theorem independentLocator_eq_affine (p blocks : ℕ) [ExpChar F p] (x u v : ι → F) (L t : ℕ) :
    independentLocator p blocks x u v L t=
      affineLocator (fun b : Fin blocks => iterateFrobenius F p b.val) x u v L t := rfl

/-- Fixed-locator row relations are EXACTLY the constant linear equations
used by FixedLocatorStopping. -/
theorem affineLocator_fixed_multiplier (σ : ν → F →+* F) (x u v : ι → F) (L t : ℕ)
    (g : F[X]) (hg : g.natDegree≤t) (hfixed : ∀ b j, σ b (g.coeff j)=g.coeff j)
    (b : ν × Fin L) :
    (affineLocator σ x u v L t).mulVec (fun j => MvPolynomial.C (g.coeff j.val)) b=
      MvPolynomial.C (σ b.1 (Principal.recurrenceEval (syndrome x u) b.2.val g))+
      MvPolynomial.X b.1*MvPolynomial.C (σ b.1 (Principal.recurrenceEval (syndrome x v) b.2.val g)) := by
  rw [Principal.recurrenceEval_eq_sum _ _ t g hg,Principal.recurrenceEval_eq_sum _ _ t g hg]
  simp only [map_sum,map_mul,hfixed,Matrix.mulVec,dotProduct,affineLocator,Nat.add_comm,
    add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

end
end FrobeniusLocator.Strata
end PackSource_AffineLocator

section PackSource_SplitDivisorLocator
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- A nonzero divisor of a squarefree domain locator IS a scalar domain
locator. All roots are retained exactly; there is no implicit root field. -/
theorem split_divisor_locator_factor (x : ι → F) (hx : Function.Injective x)
    (E : Finset ι) (g : F[X]) (hg : g≠0) (hdiv : g∣locator x E) :
    ∃ B : Finset ι, B⊆E ∧ B.card=g.natDegree ∧ ∃ c : F, c≠0 ∧ g=c • locator x B := by
  classical
  let B := Finset.univ.filter (fun i => g.eval (x i)=0)
  have hE0 := (locator_monic x E).ne_zero
  have hsplits := (Principal.locator_splits x E).of_dvd hE0 hdiv
  have hle := Polynomial.roots.le_of_dvd hE0 hdiv
  rw [Principal.locator_roots] at hle
  have hnodup : g.roots.Nodup := Multiset.nodup_of_le hle (E.nodup.map hx)
  have hBE : B⊆E := by
    intro i hi
    have hgx : g.eval (x i)=0 := (Finset.mem_filter.mp hi).2
    obtain ⟨Q,hQ⟩ := hdiv
    apply (Principal.locator_eval_zero_iff x hx E i).mp
    rw [hQ,Polynomial.eval_mul,hgx,zero_mul]
  have himage : B.image x=g.roots.toFinset := by
    ext a
    simp only [Finset.mem_image,Multiset.mem_toFinset]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (Polynomial.mem_roots hg).mpr (Finset.mem_filter.mp hi).2
    · intro ha
      have hEa := Multiset.mem_of_le hle ha
      obtain ⟨i,hiE,hia⟩ := Multiset.mem_map.mp hEa
      refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hia⟩
      rw [hia]
      exact (Polynomial.mem_roots hg).mp ha
  have hBcard : B.card=g.natDegree := by
    calc
      B.card = (B.image x).card := (Finset.card_image_of_injective B hx).symm
      _ = g.roots.toFinset.card := congrArg Finset.card himage
      _ = g.roots.card := Multiset.toFinset_card_of_nodup hnodup
      _ = g.natDegree := hsplits.natDegree_eq_card_roots.symm
  have hBg : locator x B∣g := locator_dvd_of_eval_zero x hx B g (fun i hi => (Finset.mem_filter.mp hi).2)
  obtain ⟨Q,hQ⟩ := hBg
  have hQ0 : Q≠0 := by intro hz; exact hg (by rw [hQ,hz,mul_zero])
  have hQd : Q.natDegree=0 := by
    have hh := Polynomial.natDegree_mul (locator_monic x B).ne_zero hQ0
    rw [← hQ,locator_natDegree,hBcard] at hh
    omega
  have hQC := Polynomial.eq_C_of_natDegree_eq_zero hQd
  have hc : Q.coeff 0≠0 := by intro hz; exact hQ0 (hQC.trans (by rw [hz,Polynomial.C_0]))
  refine ⟨B,hBE,hBcard,Q.coeff 0,hc,?_⟩
  calc
    g=locator x B*Q := hQ
    _ = locator x B*C (Q.coeff 0) := congrArg (fun R : F[X] => locator x B*R) hQC
    _ = Q.coeff 0 • locator x B := by rw [Polynomial.smul_eq_C_mul]; ring

end
end FrobeniusLocator.Strata
end PackSource_SplitDivisorLocator

section PackSource_C50DependentMCA
set_option autoImplicit true
/-!
Actual same-support MCA for globally quotient-dependent input pairs.
No interpolation or geometry, and no restriction on the radius is needed.
-/
namespace Sol1.C50

noncomputable section
open Code LinearCode CoreDefinitions

variable {K I A : Type} [Field K] [Fintype K] [Fintype I]
  [AddCommGroup A] [Module K A]

def badSet (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ) : Set K :=
  {gamma | IsMCA (AffineLineGenerator K) C gamma W delta}

/-- A concrete nontrivial linear relation between the two classes in the
quotient by the GLOBAL code. -/
def DependentModulo (C : ModuleCode I K A) (W : Fin 2 → I → A) : Prop :=
  ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ a • W 0 + b • W 1 ∈ C

omit [Fintype K] [Fintype I] in
theorem projected_mem_of_global_mem (C : ModuleCode I K A) (T : Finset I)
    (w : I → A) (hw : w ∈ C) : projectedWord w T ∈ projectedCodeSubmod C T := by
  exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩

/-- A global codeword direction creates no actual MCA event, for ANY radius.
Both codeword extensions are recovered on the exact candidate witness T. -/
theorem not_isMCA_of_direction_mem
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (hV : W 1 ∈ C)
    (gamma : K) (delta : ℝ) : ¬ IsMCA (AffineLineGenerator K) C gamma W delta := by
  classical
  rintro ⟨T, _hsize, hcombo, j, hj⟩
  have hVproj := projected_mem_of_global_mem C T (W 1) hV
  have hcombo' : projectedWord (W 0 + gamma • W 1) T ∈ projectedCodeSubmod C T := by
    simpa only [AffineMCALemmas.affineLineGenerator_sum_smul] using hcombo
  have heq : projectedWord (W 0) T = projectedWord (W 0 + gamma • W 1) T -
      gamma • projectedWord (W 1) T := by
    funext i
    change W 0 i.val = (W 0 i.val + gamma • W 1 i.val) - gamma • W 1 i.val
    abel
  have hUproj : projectedWord (W 0) T ∈ projectedCodeSubmod C T := by
    rw [heq]
    exact (projectedCodeSubmod C T).sub_mem hcombo'
      ((projectedCodeSubmod C T).smul_mem gamma hVproj)
  fin_cases j
  · exact hj hUproj
  · exact hj hVproj

/-- A normalized quotient relation leaves at most the exceptional seed -c. -/
theorem isMCA_eq_neg_of_relation
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (c : K)
    (hrelation : W 0 - c • W 1 ∈ C)
    (gamma : K) (delta : ℝ) (hbad : IsMCA (AffineLineGenerator K) C gamma W delta) :
    gamma = -c := by
  classical
  by_contra hne
  obtain ⟨T, _hsize, hcombo, j, hj⟩ := hbad
  have hWproj := projected_mem_of_global_mem C T (W 0 - c • W 1) hrelation
  have hcombo' : projectedWord (W 0 + gamma • W 1) T ∈ projectedCodeSubmod C T := by
    simpa only [AffineMCALemmas.affineLineGenerator_sum_smul] using hcombo
  have hscalar : gamma + c ≠ 0 := by
    intro hz
    apply hne
    calc gamma = (gamma + c) - c := by abel
         _ = -c := by rw [hz]; simp
  have hdiff : projectedWord (W 0 + gamma • W 1) T - projectedWord (W 0 - c • W 1) T =
      (gamma + c) • projectedWord (W 1) T := by
    funext i
    change (W 0 i.val + gamma • W 1 i.val) - (W 0 i.val - c • W 1 i.val) =
      (gamma + c) • W 1 i.val
    rw [add_smul]
    abel
  have hscaled : (gamma + c) • projectedWord (W 1) T ∈ projectedCodeSubmod C T := by
    rw [← hdiff]
    exact (projectedCodeSubmod C T).sub_mem hcombo' hWproj
  have hVproj : projectedWord (W 1) T ∈ projectedCodeSubmod C T :=
    ((projectedCodeSubmod C T).smul_mem_iff hscalar).mp hscaled
  have hUeq : projectedWord (W 0) T = projectedWord (W 0 - c • W 1) T +
      c • projectedWord (W 1) T := by
    funext i
    change W 0 i.val = (W 0 i.val - c • W 1 i.val) + c • W 1 i.val
    abel
  have hUproj : projectedWord (W 0) T ∈ projectedCodeSubmod C T := by
    rw [hUeq]
    exact (projectedCodeSubmod C T).add_mem hWproj
      ((projectedCodeSubmod C T).smul_mem c hVproj)
  fin_cases j
  · exact hj hUproj
  · exact hj hVproj

theorem badSet_eq_empty_of_direction_mem
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ) (hV : W 1 ∈ C) :
    badSet C W delta = ∅ := by
  ext gamma
  exact ⟨fun h ↦ (not_isMCA_of_direction_mem C W hV gamma delta h).elim, False.elim⟩

theorem badSet_subset_singleton_of_relation
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ)
    (c : K) (hrelation : W 0 - c • W 1 ∈ C) : badSet C W delta ⊆ {-c} := by
  intro gamma hgamma
  exact Set.mem_singleton_iff.mpr (isMCA_eq_neg_of_relation C W c hrelation gamma delta hgamma)

omit [Fintype K] [Fintype I] in
/-- Nontrivial quotient dependence normalizes unless the direction is global. -/
theorem dependentModulo_normal_form
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (hdependent : DependentModulo C W) :
    W 1 ∈ C ∨ ∃ c : K, W 0 - c • W 1 ∈ C := by
  classical
  by_cases hV : W 1 ∈ C
  · exact Or.inl hV
  · right
    obtain ⟨a,b,hnonzero,hrelation⟩ := hdependent
    have ha : a ≠ 0 := by
      intro ha0
      have hb : b ≠ 0 := hnonzero.resolve_left (not_not.mpr ha0)
      have hscaled : b • W 1 ∈ C := by simpa only [ha0, zero_smul, zero_add] using hrelation
      exact hV ((C.smul_mem_iff hb).mp hscaled)
    refine ⟨-(a⁻¹ * b), ?_⟩
    have hscaled := C.smul_mem a⁻¹ hrelation
    simpa [smul_add, smul_smul, inv_mul_cancel₀ ha, neg_smul, sub_neg_eq_add] using hscaled

theorem badSet_subset_singleton_of_dependentModulo
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ)
    (hdependent : DependentModulo C W) : ∃ gamma0 : K, badSet C W delta ⊆ {gamma0} := by
  rcases dependentModulo_normal_form C W hdependent with hV | ⟨c,hrelation⟩
  · exact ⟨0, by rw [badSet_eq_empty_of_direction_mem C W delta hV]; exact Set.empty_subset _⟩
  · exact ⟨-c, badSet_subset_singleton_of_relation C W delta c hrelation⟩

theorem badSet_finite_ncard_le_one_of_dependentModulo
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ)
    (hdependent : DependentModulo C W) : (badSet C W delta).Finite ∧ (badSet C W delta).ncard ≤ 1 := by
  obtain ⟨gamma0,hsub⟩ := badSet_subset_singleton_of_dependentModulo C W delta hdependent
  refine ⟨(Set.finite_singleton gamma0).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub).trans (by simp)

omit [Fintype K] [Fintype I] in
/-- The concrete relation predicate is EXACTLY failure of linear independence
of the two actual classes in the global-code quotient. -/
theorem dependentModulo_iff_not_quotient_independent
    (C : ModuleCode I K A) (W : Fin 2 → I → A) :
    DependentModulo C W ↔ ¬ LinearIndependent K
      ![(Submodule.Quotient.mk (W 0) : (I → A) ⧸ C), Submodule.Quotient.mk (W 1)] := by
  classical
  rw [LinearIndependent.pair_iff]
  constructor
  · rintro ⟨a,b,hnonzero,hrelation⟩ hindependent
    have hq : a • (Submodule.Quotient.mk (W 0) : (I → A) ⧸ C) +
        b • Submodule.Quotient.mk (W 1) = 0 := by
      have hz := (Submodule.Quotient.mk_eq_zero C).mpr hrelation
      simpa only [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] using hz
    obtain ⟨ha,hb⟩ := hindependent a b hq
    exact hnonzero.elim (fun h ↦ h ha) (fun h ↦ h hb)
  · intro hnot
    by_contra hnodep
    apply hnot
    intro a b hq
    by_contra hnonzero
    apply hnodep
    refine ⟨a,b,by tauto,?_⟩
    apply (Submodule.Quotient.mk_eq_zero C).mp
    simpa only [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] using hq

theorem badSet_finite_ncard_le_one_of_quotient_dependent
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ)
    (hdependent : ¬ LinearIndependent K
      ![(Submodule.Quotient.mk (W 0) : (I → A) ⧸ C), Submodule.Quotient.mk (W 1)]) :
    (badSet C W delta).Finite ∧ (badSet C W delta).ncard ≤ 1 :=
  badSet_finite_ncard_le_one_of_dependentModulo C W delta
    ((dependentModulo_iff_not_quotient_independent C W).mpr hdependent)

open Classical in
theorem bad_filter_card_le_one_of_dependentModulo
    (C : ModuleCode I K A) (W : Fin 2 → I → A) (delta : ℝ)
    (hdependent : DependentModulo C W) :
    (Finset.univ.filter fun gamma ↦ IsMCA (AffineLineGenerator K) C gamma W delta).card ≤ 1 := by
  classical
  obtain ⟨gamma0,hsubset⟩ := badSet_subset_singleton_of_dependentModulo C W delta hdependent
  have hfinset : (Finset.univ.filter fun gamma ↦
      IsMCA (AffineLineGenerator K) C gamma W delta) ⊆ {gamma0} := by
    intro gamma hgamma
    apply Finset.mem_singleton.mpr
    have hbad : gamma ∈ badSet C W delta := (Finset.mem_filter.mp hgamma).2
    exact Set.mem_singleton_iff.mp (hsubset hbad)
  exact (Finset.card_le_card hfinset).trans (by simp)

/-- The input strata combine by MAX. In particular, a bound B>=1 on the
quotient-independent pairs is already the same bound on every input pair. -/
theorem all_pairs_cap_of_independent_pairs
    (C : ModuleCode I K A) (delta : ℝ) (B : ℕ)
    (hindependent : ∀ W : Fin 2 → I → A,
      LinearIndependent K
        ![(Submodule.Quotient.mk (W 0) : (I → A) ⧸ C), Submodule.Quotient.mk (W 1)] →
      (badSet C W delta).ncard ≤ B) :
    ∀ W : Fin 2 → I → A, (badSet C W delta).ncard ≤ max B 1 := by
  classical
  intro W
  by_cases h : LinearIndependent K
      ![(Submodule.Quotient.mk (W 0) : (I → A) ⧸ C), Submodule.Quotient.mk (W 1)]
  · exact (hindependent W h).trans (Nat.le_max_left _ _)
  · exact (badSet_finite_ncard_le_one_of_quotient_dependent C W delta h).2.trans
      (Nat.le_max_right _ _)


end
end Sol1.C50
end PackSource_C50DependentMCA

section PackSource_C64ScalarMCA
set_option autoImplicit true
namespace Sol1.C64
open Polynomial Code LinearCode CoreDefinitions
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {F K I : Type} [Field F] [Field K]

def liftedNodes (phi : F →+* K) (nodes : I ↪ F) : I ↪ K :=
  ⟨fun i ↦ phi (nodes i),phi.injective.comp nodes.injective⟩
def evalWord (phi : F →+* K) (nodes : I ↪ F) (P : K[X]) : I → K :=
  fun i ↦ P.eval (phi (nodes i))
def evalPair (phi : F →+* K) (nodes : I ↪ F) (P : Fin 2 → K[X]) : Fin 2 → I → K :=
  fun j ↦ evalWord phi nodes (P j)

theorem evalWord_add_smul (phi : F →+* K) (nodes : I ↪ F) (P Q : K[X]) (gamma : K) :
    evalWord phi nodes (P+gamma • Q) = evalWord phi nodes P + gamma • evalWord phi nodes Q := by
  ext i
  simp [evalWord,eval_add,eval_smul]

theorem evalWord_mem_code (phi : F →+* K) (nodes : I ↪ F) (k : ℕ) [NeZero k]
    (P : K[X]) (hdegree : P.natDegree < k) :
    evalWord phi nodes P ∈ ReedSolomon.code (liftedNodes phi nodes) k := by
  apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
  exact ⟨P,hdegree,fun _ ↦ rfl⟩

theorem natDegree_lt_of_tail_zero (k : ℕ) (hk : 0 < k) (P : K[X])
    (hcoeff : ∀ i, k ≤ i → P.coeff i = 0) : P.natDegree < k := by
  by_cases hz : P = 0
  · simpa [hz] using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
      ((Polynomial.degree_lt_iff_coeff_zero P k).mpr hcoeff)

variable [Fintype I]

/-- Extract the ACTUAL MCA witness support and scalar RS polynomial, keeping the same T. -/
theorem exists_witness_polynomial [Fintype K]
    (phi : F →+* K) (nodes : I ↪ F) (k A : ℕ) [NeZero k]
    (delta : ℝ)
    (hthreshold : ∀ t : ℕ, (Fintype.card I : ℝ)*(1-delta) ≤ t → A ≤ t)
    (P : Fin 2 → K[X]) (gamma : K)
    (hbad : IsMCA (AffineLineGenerator K) (ReedSolomon.code (liftedNodes phi nodes) k)
      gamma (evalPair phi nodes P) delta) :
    ∃ T : Finset I, ∃ H : K[X], A ≤ T.card ∧ H.natDegree < k ∧
      ∀ i ∈ T, ((P 0+gamma • P 1)-H).eval (phi (nodes i)) = 0 := by
  classical
  obtain ⟨T,hT,hcombo,_hfail⟩ := hbad
  have hc : projectedWord (evalWord phi nodes (P 0)+gamma • evalWord phi nodes (P 1)) T ∈
      projectedCodeSubmod (ReedSolomon.code (liftedNodes phi nodes) k) T := by
    simpa only [AffineMCALemmas.affineLineGenerator_sum_smul,evalPair] using hcombo
  rw [← evalWord_add_smul] at hc
  obtain ⟨w,hw,heq⟩ := (LinearCode.mem_projectedCodeSubmod_iff _ T _).mp hc
  obtain ⟨H,hH,heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  refine ⟨T,H,hthreshold T.card hT,hH,?_⟩
  intro i hi
  have hnode := congrFun heq ⟨i,hi⟩
  change (P 0+gamma • P 1).eval (phi (nodes i)) = w i at hnode
  have heval' : H.eval (phi (nodes i)) = w i := heval i
  rw [eval_sub,hnode,heval',sub_self]

theorem residual_degree (P : Fin 2 → K[X]) (H : K[X]) (gamma : K) (k A : ℕ)
    (hkA : k ≤ A) (hP : ∀ j, (P j).natDegree ≤ A) (hH : H.natDegree < k) :
    ((P 0+gamma • P 1)-H).natDegree ≤ A := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_add_le _ _).trans (max_le (hP 0) ((natDegree_smul_le _ _).trans (hP 1)))
  · omega

theorem residual_tail_coeff (P : Fin 2 → K[X]) (H : K[X]) (gamma : K) (k : ℕ)
    (hH : H.natDegree < k) (i : ℕ) (hi : k ≤ i) :
    ((P 0+gamma • P 1)-H).coeff i = (P 0).coeff i+gamma*(P 1).coeff i := by
  have hz : H.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_sub,coeff_add,coeff_smul,smul_eq_mul,hz]

/-- A single nonzero top-tail minor controls arbitrary extension-valued inputs. -/
theorem scalar_minor_card_le [Fintype F] [Fintype K]
    (phi : F →+* K) (nodes : I ↪ F) (k A : ℕ) [NeZero k] (hkA : k ≤ A)
    (delta : ℝ) (hthreshold : ∀ t : ℕ, (Fintype.card I : ℝ)*(1-delta) ≤ t → A ≤ t)
    (P : Fin 2 → K[X]) (hP : ∀ j, (P j).natDegree ≤ A)
    (i : ℕ) (hi : k ≤ i)
    (hminor : (P 0).coeff i*(P 1).coeff A-(P 1).coeff i*(P 0).coeff A ≠ 0)
    (S : Finset K)
    (hS : ∀ gamma ∈ S, IsMCA (AffineLineGenerator K)
      (ReedSolomon.code (liftedNodes phi nodes) k) gamma (evalPair phi nodes P) delta) :
    S.card ≤ Fintype.card F := by
  classical
  have hdata (gamma : K) (hg : gamma ∈ S) :
      (P 0).coeff A+gamma*(P 1).coeff A ≠ 0 ∧
      ∃ c : F, phi c = tailRatio ((P 0).coeff i) ((P 1).coeff i)
        ((P 0).coeff A) ((P 1).coeff A) gamma := by
    obtain ⟨T,H,hT,hH,hroot⟩ := exists_witness_polynomial phi nodes k A delta hthreshold P gamma (hS gamma hg)
    let R := (P 0+gamma • P 1)-H
    have hdeg : R.natDegree ≤ A := residual_degree P H gamma k A hkA hP hH
    have hr : R ≠ 0 := by
      intro hz
      have hzi : (P 0).coeff i+gamma*(P 1).coeff i = 0 := by
        rw [← residual_tail_coeff P H gamma k hH i hi]
        change R.coeff i = 0
        rw [hz,coeff_zero]
      have hzA : (P 0).coeff A+gamma*(P 1).coeff A = 0 := by
        rw [← residual_tail_coeff P H gamma k hH A hkA]
        change R.coeff A = 0
        rw [hz,coeff_zero]
      apply hminor
      linear_combination (P 1).coeff A*hzi-(P 1).coeff i*hzA
    obtain ⟨hnad,hcard⟩ := root_saturation phi nodes T R hr A hdeg hT hroot
    have hcoeff : R.coeff A ≠ 0 := by rw [← hnad,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hr
    have hden : (P 0).coeff A+gamma*(P 1).coeff A ≠ 0 := by
      rwa [residual_tail_coeff P H gamma k hH A hkA] at hcoeff
    refine ⟨hden,?_⟩
    obtain ⟨c,hc⟩ := locator_tail_ratio phi nodes T R hr (hdeg.trans hT) hroot i
    refine ⟨c,?_⟩
    rw [hcard,residual_tail_coeff P H gamma k hH i hi,
      residual_tail_coeff P H gamma k hH A hkA] at hc
    exact hc
  apply tailRatio_card_le phi _ _ _ _ hminor S
  · exact fun gamma hg ↦ (hdata gamma hg).1
  · exact fun gamma hg ↦ (hdata gamma hg).2

end
end Sol1.C64
end PackSource_C64ScalarMCA

section PackSource_C64NativeSetup
set_option autoImplicit true
namespace Sol1.C64
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev Base := KoalaBear.Field
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev NativePair := Fin 2 → I → Fin IRSProfile.interleaving → K
local instance : DecidableEq K := Classical.decEq K

def nativePhi : Base →+* K := algebraMap Base K
def nativeNodes : I ↪ Base where
  toFun i := IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j h
    apply IRSProfile.domain.injective
    change CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) =
      CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node j)
    exact congrArg CompPoly.Extension.Ext.ofBase h

def NativeDegreeStratum (A : ℕ) (U : NativePair) : Prop :=
  ∀ j r, (fun i ↦ U j i r) ∈ ReedSolomon.code IRSProfile.domain (A+1)

theorem nativeDegreeStratum_iff_polynomials (A : ℕ) (U : NativePair) :
    NativeDegreeStratum A U ↔ ∀ j r, ∃ P : K[X], P.natDegree ≤ A ∧
      ∀ i, P.eval (IRSProfile.domain i) = U j i r := by
  classical
  let : NeZero (A+1) := ⟨by omega⟩
  constructor
  · intro h j r
    obtain ⟨P,hP,heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (h j r)
    exact ⟨P,by omega,heval⟩
  · intro h j r
    obtain ⟨P,hP,heval⟩ := h j r
    apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
    exact ⟨P,by omega,heval⟩


theorem native_base_card : Fintype.card Base = 2130706433 := by
  change Fintype.card (ZMod KoalaBear.fieldSize) = 2130706433
  rw [ZMod.card]
  rfl


theorem native_field_card : Fintype.card K = (2130706433 : ℕ)^6 := by
  rw [KoalaBear.card_ext6]
  rfl


theorem native_projection_room : Fintype.card Base+1 ≤ Fintype.card K := by
  rw [native_base_card,native_field_card]
  norm_num


theorem native_lifted_domain : liftedNodes nativePhi nativeNodes =
    IRSProfile.domain := by
  ext i
  rfl


theorem native_code_eq : IRSProfile.code =
    ((ReedSolomon.code IRSProfile.domain 131072)^⋈(Fin IRSProfile.interleaving)) := by
  unfold IRSProfile.code ReedSolomon.Interleaved.irsCode
  rfl



end
end Sol1.C64
end PackSource_C64NativeSetup

section PackSource_C42QueryScore
set_option autoImplicit true
/-! Exact native grid-radius/score arithmetic only. This is not a ProtocolClaim. -/
namespace Sol1.C42

noncomputable section
open ProximityPrize.Benchmark
open scoped NNReal
def queryRadius : ℝ≥0 := claimedRadius 81908 262144

theorem query_complement : (1 - queryRadius : ℝ≥0) = 180236 / 262144 := by
  apply NNReal.coe_injective
  have hr : queryRadius ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num [queryRadius, claimedRadius]
  rw [NNReal.coe_sub hr]
  norm_num [queryRadius, claimedRadius]

theorem claimedError_pow_100 (s : ℕ) :
    (claimedError s) ^ 100 = 1 / (2 : ℝ≥0) ^ s := by
  unfold claimedError
  rw [← NNReal.rpow_mul_natCast]
  have hex : -((s : ℝ) / 100) * ((100 : ℕ) : ℝ) = -(s : ℝ) := by norm_num
  rw [hex, NNReal.rpow_neg, NNReal.rpow_natCast]
  simp only [one_div]

theorem score_lower_integer_cross :
    (180236 : ℕ) ^ 12800 * 2 ^ 6918 ≤ 262144 ^ 12800 := by
  calc
    _ ≤ 2 ^ 223482 * 2 ^ 6918 := Nat.mul_le_mul_right _ score_6917_integer
    _ = 262144 ^ 12800 := by
      rw [show (262144 : ℕ) = 2 ^ 18 by norm_num, ← pow_mul, ← pow_add]

theorem score_upper_integer_cross :
    (262144 : ℕ) ^ 12800 < 180236 ^ 12800 * 2 ^ 6919 := by
  calc
    _ = 2 ^ 223481 * 2 ^ 6919 := by
      rw [show (262144 : ℕ) = 2 ^ 18 by norm_num, ← pow_mul, ← pow_add]
    _ < 180236 ^ 12800 * 2 ^ 6919 :=
      Nat.mul_lt_mul_of_pos_right score_not_6918_integer (by positivity)

theorem query_score_6917 :
    (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6918 := by
  change (1 - queryRadius) ^ 128 ≤ claimedError 6918
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : ℕ) ≠ 0)).mp
  rw [← pow_mul, claimedError_pow_100, query_complement]
  change ((180236 : ℝ≥0) / 262144) ^ 12800 ≤ 1 / (2 : ℝ≥0) ^ 6918
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast score_lower_integer_cross

theorem query_score_below_6918 :
    claimedError 6919 < (1 - queryRadius) ^ IRSProfile.repetitions := by
  change claimedError 6919 < (1 - queryRadius) ^ 128
  apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : ℕ) ≠ 0)).mp
  rw [claimedError_pow_100, ← pow_mul, query_complement]
  change 1 / (2 : ℝ≥0) ^ 6919 < ((180236 : ℝ≥0) / 262144) ^ 12800
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast score_upper_integer_cross

theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [queryRadius, claimedRadius, IRSProfile.minRelativeDistance]


end
end Sol1.C42
end PackSource_C42QueryScore

section PackSource_NativeFullRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open scoped BigOperators

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev p : ℕ := 2130706433
local instance decidableNativeFullRank (P : Prop) : Decidable P := Classical.propDecidable P

/-- CompPoly's extension has the base characteristic; this is not a registered instance. -/
instance nativeCharP : CharP K p :=
  charP_of_injective_algebraMap
    (R := KoalaBear.Field) (A := K) (algebraMap KoalaBear.Field K).injective p

theorem native_domain_fixed (i : I) : IRSProfile.domain i ^ p = IRSProfile.domain i := by
  change (CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params
    (IRSProfile.baseNttDomain.node i)) ^ p =
    CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params (IRSProfile.baseNttDomain.node i)
  rw [← map_pow]
  exact congrArg (CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
    (ZMod.pow_card (IRSProfile.baseNttDomain.node i))

/-- A maximal minor certificate for one actual benchmark input. -/
def FullRankCertificate (u v : I → K) : Prop :=
  ∃ rows : Fin 81909 → Fin 2 × Fin 49164,
    minorPolynomial (stacked p IRSProfile.domain u v 49164 81908) rows ≠ 0

theorem native_full_rank_close_count (u v : I → K) (hfull : FullRankCertificate u v) :
    (Finset.univ.filter (fun γ => Decodable IRSProfile.domain u v 131072 81908 γ)).card ≤
      174524033220597 := by
  obtain ⟨rows, hrows⟩ := hfull
  have hh := decodable_finset_card_le_minor_degree p IRSProfile.domain
    IRSProfile.domain.injective native_domain_fixed u v 131072 49164 81908
    (by norm_num only [IRSProfile.card_index]) rows hrows
    (Finset.univ.filter (fun γ => Decodable IRSProfile.domain u v 131072 81908 γ))
    (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hd := minor_natDegree_le p (by norm_num [p]) IRSProfile.domain u v 49164 81908 rows
  exact hh.trans (hd.trans (by norm_num [p]))

end
end FrobeniusLocator.Native
end PackSource_NativeFullRank

section PackSource_NativeMCA
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
local instance decidableNativeMCA (P : Prop) : Decidable P := Classical.propDecidable P
local instance nonzeroNativeMCA : NeZero (131072 : ℕ) := ⟨by norm_num⟩

def radius : ℝ := (claimedRadius 81908 262144 : ℝ)

theorem native_IsMCA_decodable (u : Fin 2 → I → K) (γ : K)
    (hmca : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Decodable IRSProfile.domain (u 0) (u 1) 131072 81908 γ := by
  change IsMCA (AffineLineGenerator K) (ReedSolomon.code IRSProfile.domain 131072)
    γ u radius at hmca
  apply isMCA_implies_decodable IRSProfile.domain u 131072 81908 radius ?_ γ hmca
  intro T hT
  norm_num [IRSProfile.card_index, radius, claimedRadius] at hT ⊢
  exact hT

theorem native_full_rank_MCA_count (u : Fin 2 → I → K)
    (hfull : FullRankCertificate (u 0) (u 1)) :
    (Finset.univ.filter (fun γ => IsMCA (AffineLineGenerator K)
      IRSProfile.baseCode γ u radius)).card ≤ 174524033220597 := by
  apply (Finset.card_le_card (t := Finset.univ.filter
    (fun γ => Decodable IRSProfile.domain (u 0) (u 1) 131072 81908 γ)) ?_).trans
    (native_full_rank_close_count (u 0) (u 1) hfull)
  intro γ hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
  exact native_IsMCA_decodable u γ hγ

end
end FrobeniusLocator.Native
end PackSource_NativeMCA

section PackSource_NativePrincipal
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open FrobeniusLocator.Principal
local instance decidableNativePrincipal (P : Prop) : Decidable P := Classical.propDecidable P
local instance nonzeroNativePrincipal : NeZero (131072 : ℕ) := ⟨by norm_num⟩

theorem native_IsMCA_badSlope (U : Fin 2 → I → K) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U radius) :
    BadSlope IRSProfile.domain (U 0) (U 1) 131072 180236 γ := by
  change IsMCA (AffineLineGenerator K) (ReedSolomon.code IRSProfile.domain 131072)
    γ U radius at hγ
  apply isMCA_implies_badSlope IRSProfile.domain U 131072 180236 radius ?_ γ hγ
  intro T hT
  norm_num [IRSProfile.card_index, radius, claimedRadius] at hT ⊢
  exact hT

def PrincipalCertificate (u v : I → K) : Prop :=
  ∃ (Δ : K[X]) (δ : ℕ), Δ ≠ 0 ∧ Δ.natDegree ≤ δ ∧ δ ≤ p*81909 ∧
    (Nonempty (MovingPrincipalCertificate p IRSProfile.domain u v 49164 81908 Δ) ∨
      Nonempty (ConstantKernelCertificate p IRSProfile.domain u v 49164 81908 Δ))

theorem native_principal_MCA_count (U : Fin 2 → I → K)
    (hcert : PrincipalCertificate (U 0) (U 1))
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U radius) :
    Γ.card ≤ 733075940392949 := by
  obtain ⟨Δ,δ,hΔ,hΔdeg,hδ,hcert⟩ := hcert
  have hbad : ∀ γ ∈ Γ, BadSlope IRSProfile.domain (U 0) (U 1) 131072 180236 γ :=
    fun γ hγ => native_IsMCA_badSlope U γ (hΓ γ hγ)
  rcases hcert with hmoving | hconstant
  · obtain ⟨cert⟩ := hmoving
    have hh := principal_bad_count p IRSProfile.domain IRSProfile.domain.injective
      native_domain_fixed (U 0) (U 1) 131072 180236 49164 81908 δ
      (by norm_num) (by norm_num) (by norm_num only [IRSProfile.card_index])
      Δ hΔ hΔdeg cert Γ hbad
    rw [IRSProfile.card_index] at hh
    exact hh.trans (calc
      _ ≤ p*81909+p*262144 := Nat.add_le_add hδ (Nat.mul_le_mul_left p (Nat.sub_le _ _))
      _ = _ := by norm_num [p])
  · obtain ⟨cert⟩ := hconstant
    have hh := constant_kernel_count p IRSProfile.domain IRSProfile.domain.injective
      native_domain_fixed (U 0) (U 1) 131072 180236 49164 81908 δ
      (by norm_num) (by norm_num) (by norm_num only [IRSProfile.card_index])
      Δ hΔ hΔdeg cert Γ hbad
    norm_num [p] at hδ
    omega

theorem native_type_one_MCA_count (U : Fin 2 → I → K)
    (htype : TypeOneSyndromes IRSProfile.domain (U 0) (U 1) 131072 p)
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U radius) : Γ.card ≤ 1 := by
  apply type_one_bad_count IRSProfile.domain IRSProfile.domain.injective
    (U 0) (U 1) 131072 180236 p
    (by norm_num only [IRSProfile.card_index]) (by norm_num [p]) htype Γ
  intro γ hγ
  exact native_IsMCA_badSlope U γ (hΓ γ hγ)

theorem native_principal_budget : 733075940392949 ≤ 244996694950342997 := by norm_num

end
end FrobeniusLocator.Native
end PackSource_NativePrincipal

section PackSource_NativeStrataMCA
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
local instance nativeStrataDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance nativeStrataNonzero : NeZero (131072 : ℕ) := ⟨by norm_num⟩

theorem native_IsMCA_badSlope (U : Fin 2 → Native.I → Native.K) (γ : Native.K)
    (hmca : IsMCA (AffineLineGenerator Native.K) IRSProfile.baseCode γ U Native.radius) :
    Principal.BadSlope IRSProfile.domain (U 0) (U 1) 131072 180236 γ := by
  change IsMCA (AffineLineGenerator Native.K) (ReedSolomon.code IRSProfile.domain 131072)
    γ U Native.radius at hmca
  apply Principal.isMCA_implies_badSlope IRSProfile.domain U 131072 180236 Native.radius ?_ γ hmca
  intro T hT
  norm_num [IRSProfile.card_index,Native.radius,claimedRadius] at hT ⊢
  exact hT

/-- Benchmark-native MCA endpoint. The two geometric counts and the
normal residual cap are shown verbatim in the signature. This is NOT
an unconditional MCA cap or ProtocolClaim. -/
theorem native_MCA_count_of_booked_geometry_and_residual (U : Fin 2 → Native.I → Native.K)
    (r : ℕ) (hr7 : 7≤r)
    (hr : GenericLayer.genericRank (stacked Native.p IRSProfile.domain (U 0) (U 1) 49164 81908)=81909-r)
    (hfirst : GenericLayer.genericRank (hankel IRSProfile.domain (U 0) (U 1) 49164 81908)=49164)
    (hprincipal : EvaluatedPrincipalCap (threeConjugations (frobenius Native.K Native.p)) IRSProfile.domain
      (U 0) (U 1) 131072 180236 131072 81908)
    (hregular : PuncturedRegularCap (threeConjugations (frobenius Native.K Native.p)) IRSProfile.domain
      (U 0) (U 1) 131072 180236 131072 81908)
    (hres : NormalResidualCap6917 Native.p IRSProfile.domain (U 0) (U 1) r)
    (Γ : Finset Native.K) (hΓ : ∀ γ∈Γ, IsMCA (AffineLineGenerator Native.K) IRSProfile.baseCode γ U Native.radius) :
    Γ.card≤244996694950342997 := by
  apply native_booked_strata_count IRSProfile.domain (U 0) (U 1) IRSProfile.domain.injective
    Native.native_domain_fixed IRSProfile.card_index r hr7 hr hfirst hprincipal hregular hres Γ
  intro γ hγ
  exact native_IsMCA_badSlope U γ (hΓ γ hγ)

end
end FrobeniusLocator.Strata
end PackSource_NativeStrataMCA

section PackSource_NativeLemmaT
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Matrix
open ProximityPrize.Benchmark

/-- The field-size guard in the global polynomial output construction
is discharged at the actual native sextic field for every open H. -/
theorem native_relation_height_fits_field (H : ℕ) (hH : H≤32738) :
    (2*H+2)*Native.p<Fintype.card Native.K := by
  change (2*H+2)*2130706433<Fintype.card KoalaBear.Ext6
  rw [KoalaBear.card_ext6]
  have hle := Nat.mul_le_mul_right 2130706433 (show 2*H+2≤2*32738+2 by omega)
  exact hle.trans_lt (by norm_num)

/-- Native primitive polynomial Lemma T with all size/degree guards
proved. The binary level Hilbert function remains an EXPLICIT premise. -/
def native_lemmaT_of_two_active_level (U : Fin 2 → Native.I → Native.K)
    (r a b c : ℕ) (hr7 : 7≤r) (ha : a≤b) (hb : b≤81908) (hc : 81908<c)
    (hcm : c≤131072) (hsum : a+b+c=262146) (hr : r+a+b=163818)
    (hHF : HasLevelHilbertFunction
      (fun b j => algebraMap Native.K[X] (GenericLayer.GenericField Native.K)
        (Principal.parameterSyndromes Native.p IRSProfile.domain (U 0) (U 1) b j)) 131072 a b c) :
    PolynomialRelationCertificate Native.p IRSProfile.domain (U 0) (U 1) 131072 (131073-c) := by
  have hH := (native_minimal_relation_degree r a b c hcm hsum hr hr7).2.1
  have hline := generic_relation_line_of_level Native.p IRSProfile.domain (U 0) (U 1)
    131072 a b c hcm hsum ha (by omega) (by omega) hHF
  exact polynomialRelationCertificate_of_nullity_one Native.p (by norm_num [Native.p])
    IRSProfile.domain (U 0) (U 1) IRSProfile.domain.injective Native.native_domain_fixed
    131072 131072 (131073-c) (by rw [IRSProfile.card_index]) (by omega)
    (native_relation_height_fits_field _ hH) hline

end
end FrobeniusLocator.Strata
end PackSource_NativeLemmaT

section PackSource_NativeGenericPrincipal
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open FrobeniusLocator.Principal

abbrev GenericSlopeField := FractionRing K[X]
def genericSlopeEmbedding : K[X] →+* GenericSlopeField := algebraMap K[X] GenericSlopeField

def GenericPrincipalCertificate (u v : I → K) : Prop :=
  ∃ a q : ℕ, a+q=81908 ∧ Nonempty (PrincipalAt
    (fun b j => genericSlopeEmbedding (parameterSyndromes p IRSProfile.domain u v b j))
    131072 a q)

/-- Native any-nullity principal-kernel theorem from bare principality
over K(Z), without a separately supplied cofactor or normal-fiber package. -/
theorem native_generic_principal_MCA_count (U : Fin 2 → I → K)
    (hprincipal : GenericPrincipalCertificate (U 0) (U 1))
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U radius) :
    Γ.card ≤ 733075940392949 := by
  obtain ⟨a,q,hsum,⟨P⟩⟩ := hprincipal
  have hbad : ∀ γ ∈ Γ,
      BadSlope IRSProfile.domain (U 0) (U 1) 131072 (131072+(131072-(a+q))) γ := by
    intro γ hγ
    rw [hsum]
    exact native_IsMCA_badSlope U γ (hΓ γ hγ)
  have hh := generic_principal_bad_count_coarse genericSlopeEmbedding
    (IsFractionRing.injective K[X] GenericSlopeField) p (by norm_num [p])
    IRSProfile.domain IRSProfile.domain.injective native_domain_fixed (U 0) (U 1)
    131072 131072 a q (by norm_num only [IRSProfile.card_index]) (by omega) P Γ hbad
  rw [IRSProfile.card_index] at hh
  exact hh.trans (calc
    _ ≤ p*(262144+81909) := Nat.mul_le_mul_left p (by omega)
    _ = _ := by norm_num [p])

end
end FrobeniusLocator.Native
end PackSource_NativeGenericPrincipal
