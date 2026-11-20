/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833TripleIncidence
import ProximityPrize.SubmissionLower.Mid6833ResidueAnchors
namespace Genuine.OrbitLines
open Polynomial Finset Frontier.ResidueOrbit
open scoped Polynomial BigOperators Classical
noncomputable section
variable {F K I G J : Type*} [Field F] [Field K] [Algebra F K] [Fintype I] [Fintype G] [Fintype J]
local instance mid6833Local_OrbitLines_8  : DecidableEq K := Classical.decEq _

/-- A small list on an affine polynomial pencil. Every position where the
slope has nonzero value can be charged at most once. -/
theorem pencil_count (x : I ↪ K) (w : I → K) (S : Finset G) (c : G ↪ F)
    (P Q : K[X]) (nz : Q ≠ 0) (W A : ℕ) (deg : Q.natDegree ≤ W)
    (ag : ∀g∈S, A ≤ (univ.filter (fun i => (P+c g • Q).eval (x i)=w i)).card) :
    S.card * A ≤ (S.card-1) * W + (Fintype.card I) := by
  classical
  let Z := univ.filter (fun i => Q.eval (x i)=0)
  have hz : Z.card ≤ W := by
    by_contra! h
    apply nz
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f:=fun i:Z => x i.val) (x.injective.comp Subtype.val_injective)
      (fun i => (mem_filter.mp i.property).2) (by simpa only [Fintype.card_coe] using deg.trans_lt h)
  let T (i:I) := S.filter (fun g => (P+c g • Q).eval (x i)=w i)
  have term (i:I) : (T i).card ≤ (if i ∈ Z then S.card-1 else 0)+1 := by
    by_cases hi : i∈Z
    · rw [if_pos hi]; exact (card_le_card (filter_subset _ _)).trans (by omega)
    · rw [if_neg hi,zero_add]; apply card_le_one.mpr
      intro g hg h hh
      apply c.injective
      have eq := ((mem_filter.mp hg).2).trans ((mem_filter.mp hh).2).symm
      have nv : Q.eval (x i)≠0 := by simpa [Z] using hi
      have sml (a:F) : a • Q = C (algebraMap F K a)*Q := by rw [← Polynomial.smul_eq_C_mul,algebraMap_smul]
      simp only [sml,eval_add,eval_mul,eval_C,add_right_inj] at eq
      exact (FaithfulSMul.algebraMap_injective F K) (mul_right_cancel₀ nv eq)
  have sum := sum_le_sum (s:=univ) (fun i _ => term i)
  have mass : S.card*A ≤ ∑ i, (T i).card := by
    have h := sum_le_sum (s:=S) (fun g hg => ag g hg)
    simp only [sum_const,nsmul_eq_mul,card_filter,T] at *
    exact h.trans_eq sum_comm
  apply mass.trans (sum.trans _)
  simp only [sum_add_distrib]
  simpa [Nat.mul_comm] using Nat.add_le_add_right (Nat.mul_le_mul_left (S.card-1) hz) (Fintype.card I)

def ratio (c : G ↪ F) (g h k:G) : F := (c k-c g)/(c h-c g)

omit [Fintype G] in
private theorem ratio_seed (c : G ↪ F) {g h:G} (ne : g≠h) (k : G) (origin v:K) :
    ((origin + c k • v)-(origin+c g • v))-
      ratio c g h k • ((origin+c h • v)-(origin+c g • v))=0 := by
  have nv : c h-c g≠0 := sub_ne_zero.mpr (fun e => ne (c.injective e).symm)
  simp only [add_sub_add_left_eq_sub,←sub_smul,smul_smul,ratio,div_mul_cancel₀ _ nv,sub_self]

/-- A non-pencil triple on a base-field seed line has a nonzero seed-zero
difference which vanishes both at all virtual poles and at every joint agreement. -/
theorem triple_nodes (x : I ↪ K) (w : I → K) (θ : J → K →ₐ[F] K)
    (D D' H L : K[X]) (W d : ℕ) (part : D'∣D) (cop : IsCoprime D' H)
    (regular : ∀ i, (univ.lcm (fun j => D'.map (θ j).toRingHom)).eval (x i)≠0)
    (spanD : W ≤ (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree+d)
    (c : G ↪ F) (origin v : K) (T : G → K[X])
    (valid : ∀g, (origin+c g • v,T g)∈pairs θ D H L W)
    (g h k : G) (ne : g≠h)
    (off : T k-T g ≠ ratio c g h k • (T h-T g)) :
    (univ.filter (fun i => (T g).eval (x i)=w i ∧ (T h).eval (x i)=w i ∧
       (T k).eval (x i)=w i)).card ≤ d := by
  classical
  let M := pairs θ D H L W
  let z (j:G) : K × K[X] := (origin+c j • v,T j)
  let u := (z k-z g)-ratio c g h k • (z h-z g)
  let A := univ.filter (fun i => (T g).eval (x i)=w i ∧ (T h).eval (x i)=w i ∧ (T k).eval (x i)=w i)
  have pure : u∈M := M.sub_mem (M.sub_mem (valid k) (valid g))
    (M.smul_mem _ (M.sub_mem (valid h) (valid g)))
  have zero : u.1=0 := ratio_seed c ne k origin v
  by_contra! large
  have card : d<A.card := large
  have mem : u ∈ anchored θ D H L W x A := by
    refine ⟨pure,?_⟩
    intro i hi
    obtain ⟨hg,hh,hk⟩ := (mem_filter.mp hi).2
    change (((T k-T g)-ratio c g h k • (T h-T g))).eval (x i)=0
    simp only [eval_sub,eval_smul,hg,hh,hk,sub_self,smul_zero]
  have inj := anchored_kernel θ D D' H L W part cop x A (fun i _ => regular i) (by omega)
  have sharp : (⟨u,mem⟩ : anchored θ D H L W x A) = 0 := inj (by exact zero)
  have vz : u.2=0 := congrArg (fun q : anchored θ D H L W x A => q.val.2) sharp
  exact off (sub_eq_zero.mp vz)

/-- Joint polynomial and support bound for a whole base-field affine seed line.
The parameters admit a direct exact check for a proposed list length m. -/
theorem line_cap (x : I ↪ K) (w : I → K) (θ : J → K →ₐ[F] K)
    (D D' H L : K[X]) (W d a m B u : ℕ) (part : D'∣D) (cop : IsCoprime D' H)
    (regular : ∀ i, (univ.lcm (fun j => D'.map (θ j).toRingHom)).eval (x i)≠0)
    (spanD : W ≤ (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree+d)
    (hd : d ≤ Fintype.card I) (pbound : ∀s:ℕ, s*a ≤ (s-1)*W+Fintype.card I → s≤B)
    (num : 2*u^3*Fintype.card I + m^3*d+(B+1)*m^2*(Fintype.card I-d) < 3*u^2*(m*a))
    (c : G ↪ F) (origin v : K) (T : G ↪ K[X])
    (valid : ∀g, (origin+c g • v,T g)∈pairs θ D H L W)
    (ag : ∀g, a≤(univ.filter (fun i => (T g).eval (x i)=w i)).card) :
    Fintype.card G<m := by
  classical
  by_contra! hm
  obtain ⟨S,_,sz⟩ := Finset.exists_subset_card_eq (s:=(univ:Finset G)) (n:=m) (by simpa using hm)
  let e : S ↪ G := ⟨Subtype.val,Subtype.val_injective⟩
  let V := e.trans T
  let f := e.trans c
  let fit (g:S) (i:I) := (V g).eval (x i)=w i
  let b (g:S) (i:I) : ℕ := if fit g i then 1 else 0
  let exc (g h k:S) := V k-V g = ratio f g h k • (V h-V g)
  have triple_eq (g h k:S) : ∑ i, b g i*b h i*b k i =
      (univ.filter (fun i => fit g i ∧ fit h i ∧ fit k i)).card := by
    rw [card_filter]
    apply sum_congr rfl
    intro i _
    by_cases hg : fit g i <;> by_cases hh : fit h i <;> by_cases hk : fit k i <;> simp [b,hg,hh,hk]
  have ac (g:S) : a≤∑ i, b g i := by
    change a ≤ ∑ i, (if (T (e g)).eval (x i)=w i then 1 else 0)
    simpa only [card_filter] using ag (e g)
  have pc (g h:S) (ne:g≠h) : (univ.filter (fun k => exc g h k)).card≤B := by
    let C := univ.filter (fun k => exc g h k)
    let Q := V h - V g
    have dQ : Q.natDegree ≤ W := (natDegree_sub_le _ _).trans
      (max_le (valid (e h)).1 (valid (e g)).1)
    have nz : Q≠0 := sub_ne_zero.mpr (fun eq => ne (V.injective eq).symm)
    have hden : f h-f g≠0 := sub_ne_zero.mpr (fun eq => ne (f.injective eq).symm)
    let t : S ↪ F := ⟨ratio f g h, by
      intro j k hk
      change (f j-f g)/(f h-f g) = (f k-f g)/(f h-f g) at hk
      exact f.injective (sub_left_inj.mp ((div_left_inj' hden).mp hk))⟩
    have cg (k:S) (hk : k∈C) : V k = V g+t k • Q := by
      have hh : V k-V g=t k • Q := (mem_filter.mp hk).2
      rw [sub_eq_iff_eq_add] at hh
      simpa [add_comm] using hh
    apply pbound
    exact pencil_count x w C t (V g) Q nz W a dQ (fun k hk => by
      rw [←cg k hk]; exact ag (e k))
  have real := Genuine.Triple.cubic b a d B u ac exc (by
    intro g h ne
    convert! pc g h ne using 2
    ext k; simp) (by
    intro g h k ne hoff
    rw [triple_eq]
    exact triple_nodes x w θ D D' H L W d part cop regular spanD f origin v V
        (fun g => valid (e g)) g h k ne hoff) (fun g h k => by
      rw [triple_eq]; exact card_le_univ _) hd
  rw [Fintype.card_coe,sz] at real
  exact num.not_ge real

end
#print axioms pencil_count
#print axioms triple_nodes
#print axioms line_cap
end Genuine.OrbitLines
