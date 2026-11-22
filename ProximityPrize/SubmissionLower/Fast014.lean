import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fast012
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
local instance decidableMCABridge (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
end
end FrobeniusLocator
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
local instance decidableBadSlope (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
def BadSlope (x : ι → F) (u v : ι → F) (k A : ℕ) (γ : F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧
    ExtendsOn x (fun i => u i + γ * v i) k S ∧
    ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)
theorem degree_smul_lt (a : F) {P : F[X]} {k : ℕ} (hP : P.degree < k) :
    (a • P).degree < k := (Polynomial.degree_smul_le a P).trans_lt hP
theorem degree_sub_lt {P Q : F[X]} {k : ℕ}
    (hP : P.degree < k) (hQ : Q.degree < k) : (P-Q).degree < k :=
  (Polynomial.degree_sub_le P Q).trans_lt (max_lt hP hQ)
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
theorem eval_coefficient_map (σ : F →+* F) (P : F[X]) (a : F)
    (ha : σ a = a) : (P.map σ).eval a = σ (P.eval a) := by
  simpa only [ha] using (Polynomial.eval_map_apply σ a (p := P))
theorem degree_mul_lt_add (U P : F[X]) (h k : ℕ)
    (hU : U.natDegree ≤ h) (hP : P.degree < k) :
    (U*P).degree < k+h := by
  by_cases hp : P=0
  · simp [hp]
  have hpn : P.natDegree < k := (natDegree_lt_iff_degree_lt hp).mpr hP
  have hb : (U*P).natDegree < k+h :=
    natDegree_mul_le.trans_lt (by omega)
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hb)
structure TwistedRelation (σ : F →+* F) (x w : ι → F)
    (k h : ℕ) (U V R : F[X]) : Prop where
  degree_U : U.natDegree ≤ h
  degree_V : V.natDegree ≤ h
  degree_R : R.degree < k+h
  nodes : ∀ i, U.eval (x i)*w i + V.eval (x i)*σ (w i) = R.eval (x i)
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [Fintype ι] [Fintype β]
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
def polynomialCombination (g : β → F[X]) (L : ℕ) :
    (β → Polynomial.degreeLT F L) →ₗ[F] F[X] where
  toFun Q := ∑ b, g b*(Q b : F[X])
  map_add' Q R := by simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' c Q := by simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]
def allEvaluation (x : ι → F) : F[X] →ₗ[F] (ι → F) where
  toFun P i := P.eval (x i)
  map_add' P Q := by ext i; exact eval_add
  map_smul' c P := by ext i; simp
def numeratorMatrix (x : ι → F) (g : β → F[X]) (L : ℕ) :
    Matrix (β × Fin L) ι F := fun b i => (g b.1).eval (x i)*x i^b.2.val
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
theorem numerator_rank (x : ι → F) (g : β → F[X]) (L : ℕ) :
    (numeratorMatrix x g L).rank = Module.finrank F
      ((LinearMap.range (polynomialCombination g L)).map (allEvaluation x)) := by
  rw [← numerator_range]
  exact (Matrix.rank_transpose _).symm
end
end FrobeniusLocator.Strata
end
section
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
def coordinateScale (c : ι → F) (hc : ∀ i, c i≠0) : (ι → F) ≃ₗ[F] (ι → F) where
  toFun v i := c i*v i
  invFun v i := (c i)⁻¹*v i
  left_inv v := by funext i; simp only [← mul_assoc,inv_mul_cancel₀ (hc i),one_mul]
  right_inv v := by funext i; simp only [← mul_assoc,mul_inv_cancel₀ (hc i),one_mul]
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' a v := by funext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
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
end
section
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Matrix Polynomial Finset
open scoped BigOperators
variable {F row col : Type} [Field F] [Fintype row] [Fintype col]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]
def errorTwoMatrix (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Matrix (Fin 2 × Fin L) ι F := fun b i => ![e i,σ (e i)] b.1*x i^b.2.val
def errorThreeMatrix (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Matrix (Fin 3 × Fin L) ι F := fun b i => ![e i,σ (e i),σ (σ (e i))] b.1*x i^b.2.val
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V]
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
theorem projection_kernel_le_of_saturation (f : V →ₗ[F] W) (S : Submodule F V)
    (hsat : Module.finrank F S=Module.finrank F (S.map f)+Module.finrank F (LinearMap.ker f)) :
    LinearMap.ker f≤S := by
  have h := subspace_map_add_inf f S
  have heq : S ⊓ LinearMap.ker f=LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  rw [← heq]
  exact inf_le_left
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
theorem rowspace_forget {row : Type} (M : Matrix row ι F) (C : Finset ι) :
    (Submodule.span F (Set.range M.row)).map (forgetCoordinates C)=
      Submodule.span F (Set.range (M.submatrix id Subtype.val).row) := by
  rw [Submodule.map_span,← Set.range_comp]
  rfl
end Coordinates
end
end FrobeniusLocator.Strata
end
section
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
theorem error_rowspace_le (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    Submodule.span F (Set.range (errorTwoMatrix σ x e L).row)≤
      Submodule.span F (Set.range (errorThreeMatrix σ x e L).row) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨b,j⟩,rfl⟩
  apply Submodule.subset_span
  refine ⟨(Fin.castLE (by decide : 2≤3) b,j),?_⟩
  funext i
  fin_cases b <;> simp [errorTwoMatrix,errorThreeMatrix,Matrix.row]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F]
def recurrenceSpace (s : β → ℕ → F) (m t : ℕ) : Submodule F F[X] :=
  Polynomial.degreeLT F (t+1) ⊓ ⨅ b, ⨅ j : Fin (m-t),
    LinearMap.ker (Principal.recurrenceEval (s b) j.val)
theorem mem_recurrenceSpace (s : β → ℕ → F) (m t : ℕ) (P : F[X]) :
    P∈recurrenceSpace s m t ↔ P.degree<(t+1 : ℕ) ∧
      ∀ b j, j<m-t → Principal.recurrenceEval (s b) j P=0 := by
  simp only [recurrenceSpace,Submodule.mem_inf,Polynomial.mem_degreeLT,Submodule.mem_iInf,
    LinearMap.mem_ker,Fin.forall_iff]
end
end FrobeniusLocator.Strata
end
section
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
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
def twoConjugations (σ : F →+* F) : Fin 2 → F →+* F := ![RingHom.id F,σ]
theorem conjugateErrors_two (σ : F →+* F) (x e : ι → F) (L : ℕ) :
    conjugateErrors (twoConjugations σ) x e L=errorTwoMatrix σ x e L := by
  ext ⟨b,j⟩ i
  fin_cases b <;> simp [conjugateErrors,twoConjugations,errorTwoMatrix]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance strataDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
end
end FrobeniusLocator.Strata
end
section
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
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β : Type} [Field F] [DecidableEq F] [Fintype β]
section Domain
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Domain
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset
open scoped BigOperators
variable {F ι : Type} [DecidableEq F] [Fintype ι] [DecidableEq ι]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
local instance countDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
theorem relation_degree_nullity_balance (m L t r a b c : ℕ)
    (hm : m=L+t) (hc : c≤m) (hsum : a+b+c=2*m+2) (hr : r+a+b=2*t+2) :
    L+(m+1-c)+r=t+1 := by omega
end
end FrobeniusLocator.Strata
end
section
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype β]
local instance ledgerDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance decidablePrincipalKernel (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance decidableConstant (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
structure ConstantKernelCertificate (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (Δ : F[X]) where
  space : Submodule F (Fin (t+1) → F)
  generic_annihilates : ∀ c ∈ space,
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0
  normal_inclusion : ∀ γ, Δ.eval γ ≠ 0 → ∀ c,
    ((stacked p x u v L t).map (Polynomial.evalRingHom γ)).mulVec c = 0 → c ∈ space
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F J : Type*} [Field F]
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
end
section
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
end
section
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
end
section
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Matrix
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_3
noncomputable section
open Polynomial Matrix Finset FrobeniusLocator
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι K : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]
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
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]
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
end
section
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
end
section
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι ν : Type} [Field F] [Fintype ι] [DecidableEq ι]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
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
end
section
namespace Sol1.C64
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev NativePair := Fin 2 → I → Fin IRSProfile.interleaving → K
local instance : DecidableEq K := Classical.decEq K
theorem native_field_card : Fintype.card K = (2130706433 : ℕ)^6 := by
  rw [KoalaBear.card_ext6]
  rfl
theorem native_code_eq : IRSProfile.code =
    ((ReedSolomon.code IRSProfile.domain 131072)^⋈(Fin IRSProfile.interleaving)) := by
  unfold IRSProfile.code ReedSolomon.Interleaved.irsCode
  rfl
end
end Sol1.C64
end
section
namespace Sol1.C42
noncomputable section
open ProximityPrize.Benchmark
open scoped NNReal
theorem claimedError_pow_100 (s : ℕ) :
    (claimedError s) ^ 100 = 1 / (2 : ℝ≥0) ^ s := by
  unfold claimedError
  rw [← NNReal.rpow_mul_natCast]
  have hex : -((s : ℝ) / 100) * ((100 : ℕ) : ℝ) = -(s : ℝ) := by norm_num
  rw [hex, NNReal.rpow_neg, NNReal.rpow_natCast]
  simp only [one_div]
end
end Sol1.C42
end
section
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
end
end FrobeniusLocator.Native
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
local instance decidableNativeMCA (P : Prop) : Decidable P := Classical.propDecidable P
local instance nonzeroNativeMCA : NeZero (131072 : ℕ) := ⟨by norm_num⟩
end
end FrobeniusLocator.Native
end
section
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
theorem native_principal_budget : 733014149906392 ≤ 243069641737383864 := by norm_num
end
end FrobeniusLocator.Native
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
local instance nativeStrataDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance nativeStrataNonzero : NeZero (131072 : ℕ) := ⟨by norm_num⟩
end
end FrobeniusLocator.Strata
end
