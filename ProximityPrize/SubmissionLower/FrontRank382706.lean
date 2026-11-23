import ProximityPrize.SubmissionLower.FrontRank482706
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.FrontCases82706
set_option Elab.async false
set_option autoImplicit true
section
namespace Front82706_3
noncomputable section
open Front82706 Polynomial
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a*(B.β l).map twist
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b*B.α j)
end
end Front82706_3
end
section
namespace Front82706_3
noncomputable section
open Front82706 Polynomial ProximityPrize.Benchmark FrobeniusLocator
open P1_3 (Adjugate Plane)
open private amp_le primitive_lift contraction_degree from ProximityPrize.SubmissionLower.PortFrontB
theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B:RankThree u T R D) (hnp:Nonparallel B)
    (W:Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom:k+3*D.height+(fixedNodes R).card≤blockLength) :
    Nonempty (Adjugate u (fixedNodes R) D.height):=by
  change 131072+3*D.height+(fixedNodes R).card≤262144 at hroom
  let A:=B.α
  let V:=fun j => (B.β j).map twist
  let s:=amplitudeDegree (A 0) (A 1)
  let t:=amplitudeDegree (V 0) (V 1)
  have htw (P : K[X]) : (P.map twist).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht:t=amplitudeDegree (B.β 0) (B.β 1):=by simp only [t,V,amplitudeDegree,htw]
  have ha:B.a.natDegree+t≤D.height:=ht ▸ B.first_degree
  have hb:B.b.natDegree+s≤D.height:=B.second_degree
  have hv:IsCoprime (V 0) (V 1):=B.β_primitive.map (mapRingHom twist)
  have hout (j l : Fin 2) : (W.output j l).natDegree < 131072 + D.height := by
    by_cases hz:W.output j l=0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L:=fun l => A 0*W.output 1 l - A 1*W.output 0 l
  let N:=fun j => V 1*W.output j 0 - V 0*W.output j 1
  let w:=fun i => B.a.eval (node i)*((A 0).eval (node i)*u 1 i - (A 1).eval (node i)*u 0 i)
  let z:=fun i => B.b.eval (node i)*((V 0).eval (node i)*(u 1 i)^p - (V 1).eval (node i)*(u 0 i)^p)
  have hn (i : I) (hi : i ∉ fixedNodes R) (j l : Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i)*(V l).eval (node i)*u j i -
        B.b.eval (node i)*(A j).eval (node i)*(u l i)^p:=by
    rw [← W.nodes i hi]
    simp only [leftCoeff,rightCoeff,eval_mul,eval_neg,A,V]
    ring
  obtain ⟨P, hP, heP⟩ := primitive_lift (fixedNodes R) V L w (131072 + D.height + s) hv
    (fun l => contraction_degree (amp_le A 0) (amp_le A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L,w,eval_sub,eval_mul,hn i hi]; ring)
    (by change t < _; omega) (by change _+t+_≤_; omega)
  obtain ⟨Q, hQ, heQ⟩ := primitive_lift (fixedNodes R) A N z (131072 + D.height + t) B.α_primitive
    (fun j => contraction_degree (amp_le V 1) (amp_le V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N,z,eval_sub,eval_mul,hn i hi]; ring)
    (by change s < _; omega) (by change _+s+_≤_; omega)
  change P.natDegree+t < 131072+D.height+s at hP
  change Q.natDegree+s < 131072+D.height+t at hQ
  let σ:=RingEquiv.ofBijective twist ⟨twist.injective,Finite.surjective_of_injective twist.injective⟩
  let τ:=σ.symm.toRingHom
  have hundo (x:K):τ (twist x)=x:=σ.symm_apply_apply x
  have hfixed (i : I) : τ (node i) = node i := by
    have hh:twist (node i)=node i:=Native.native_domain_fixed i
    simpa only [hh] using hundo (node i)
  have hmap (F : K[X]) (i : I) : (F.map τ).eval (node i) = τ (F.eval (node i)) :=
    Strata.eval_coefficient_map τ _ _ (hfixed i)
  have hβ (l : Fin 2) (i : I) : (V l).eval (node i) = twist ((B.β l).eval (node i)) :=
    Strata.eval_coefficient_map twist _ _ (Native.native_domain_fixed i)
  let b:=B.b.map τ
  let Q' := Q.map τ
  have heQ' (i : I) (hi : i ∉ fixedNodes R) : Q'.eval (node i) = b.eval (node i) *
      ((B.β 0).eval (node i)*u 1 i - (B.β 1).eval (node i)*u 0 i):=by
    rw [show Q'.eval (node i)=τ (Q.eval (node i)) from hmap Q i,heQ i hi]
    change τ (B.b.eval (node i) * ((V 0).eval (node i) * twist (u 1 i) -
      (V 1).eval (node i)*twist (u 0 i)))=_
    simp only [b,hmap,hβ,map_mul,map_sub,hundo]
  let det:=A 0*B.β 1 - A 1*B.β 0
  let denom:=B.a*b*det
  let num:=fun j => b*B.β j*P - B.a*A j*Q'
  have hb' : b.natDegree=B.b.natDegree:=natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree=Q.natDegree:=natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j:Fin 2):(B.β j).natDegree≤t:=ht ▸ amp_le B.β j
  have hadeg (j:Fin 2):(A j).natDegree≤s:=amp_le A j
  have ddet : det.natDegree ≤ s + t := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom, mul_ne_zero (mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff τ.injective).mpr B.b_ne)) hnp,
    ?_,num, ?_, ?_⟩⟩
  · calc
      denom.natDegree ≤ B.a.natDegree + b.natDegree + det.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _≤2*D.height:=by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree < 131072 + 2 * D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have := hvdeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega)
      · have := hadeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i) * u 0 i = (num 0).eval (node i)
      simp only [denom,num,det,eval_mul,eval_sub,heP i hi,heQ' i hi,w]
      ring
    · change denom.eval (node i) * u 1 i = (num 1).eval (node i)
      simp only [denom,num,det,eval_mul,eval_sub,heP i hi,heQ' i hi,w]
      ring
end
end Front82706_3
end
section
namespace Front82706_3
noncomputable section
open Front82706 FrobeniusLocator ProximityPrize.Benchmark Polynomial
open P1_3 (Adjugate)
open private natDegree_lt_of_degree_lt_pos from ProximityPrize.SubmissionLower.PortFrontB
theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ:K} (hn:Normal u γ) (M:BadMark u γ) :
    Disjoint M.support (fixedNodes R):=by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D:Reduction u T R) (J:Adjugate u (fixedNodes R) D.height)
    (hsmall:2*D.height < Front82706.L) {γ:K} (hn:Normal u γ) (M:BadMark u γ):False:=by
  classical
  let F:=J.numer 0+C γ*J.numer 1 - J.denom*M.decoder
  have hfit : Front82706.k + 2 * D.height < Front82706.agreement := by
    have hsum:Front82706.k+Front82706.L=Front82706.agreement:=by decide
    omega
  have hdeg : F.natDegree < Front82706.agreement := by
    have hj (j : Fin 2) : (J.numer j).natDegree < Front82706.k + 2 * D.height :=
      natDegree_lt_of_degree_lt_pos (by
        have hk:0 < Front82706.k:=by decide
        omega) (J.numer_degree j)
    have hP:M.decoder.natDegree < Front82706.k:=natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod:=natDegree_mul_le (p:=J.denom) (q:=M.decoder)
    have hsub:=natDegree_sub_le (J.numer 0+C γ*J.numer 1) (J.denom*M.decoder)
    change (J.numer 0+C γ*J.numer 1 - J.denom*M.decoder).natDegree < Front82706.agreement
    have:=J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have:=hj 0; omega) (by have:=hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF : F = 0 := by
    by_contra hf
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd:i ∉ fixedNodes R:=fun h => (Finset.disjoint_left.mp (mark_disjoint D hn M)) hi h
        simp only [F,eval_sub,eval_add,eval_mul,eval_C, ← J.nodes i hd,M.hits i hi]
        ring)
    have:=M.agreement
    omega
  let zeros:=Finset.univ.filter (fun i:I => J.denom.eval (node i)=0)
  let E:=fixedNodes R ∪ zeros
  have hZ : zeros.card ≤ J.denom.natDegree := Strata.root_nodes_card_le node
    IRSProfile.domain.injective _ J.nonzero zeros (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hE : E.card ≤ (fixedNodes R).card + 2 * D.height := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    have hd:i ∉ fixedNodes R:=fun h => hi (Finset.mem_union_left _ h)
    have hz : J.denom.eval (node i) ≠ 0 :=
      fun h => hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    have hf:F.eval (node i)=0:=by rw [hF,eval_zero]
    simp only [F,eval_sub,eval_add,eval_mul,eval_C, ← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal:=relation_height_balance T
  have hheight:=D.height_eq
  have hs:=actual_stackRank u
  have hcard : Front82706.k + Front82706.L + Front82706.t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) Front82706.L Front82706.t).map (evalRingHom γ)).rank=stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      Front82706.k Front82706.L Front82706.t M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b:Fin 2 => iterateFrobenius K p b.val) (fun i:E => node i.val)
    (fun i:E => u 0 i.val+γ*u 1 i.val - M.decoder.eval (node i.val)) Front82706.L)
  rw [Fintype.card_coe,hn] at hr
  have hsize : 2 * D.height + (fixedNodes R).card < stackRank u := by
    omega
  omega
end
end Front82706_3
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front82706_3
noncomputable section
open Front82706 Polynomial FrobeniusLocator
open P1_3 (Plane)
open private column column_ne column_bound column_dvd firstColumn_normal threeU_fun
  tight_pair outputs slice_bound nodes_of_columns relationOn_fun from ProximityPrize.SubmissionLower.PortFrontB
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β=column p (leftCoeff B):=by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a*(B.β j).map twist)=leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α=column 1 (rightCoeff B):=by
  simp only [threeV,rightCoeff,column,liftX,seed,Polynomial.map_mul,Polynomial.map_neg,pow_one]
  ring
theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D:Reduction u T R} (B:RankThree u T R D) :
    Nonempty (Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)):=by
  let U:=leftCoeff B
  let V:=rightCoeff B
  have amp_ne (v : Fin 2 → K[X]) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩:=hv
    simp [hz] at hab
  obtain ⟨l,hl⟩:=amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩:=amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l,mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j,V j≠0:=⟨j,neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V,rightCoeff,natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ:=algebraMap K[X] Frac
  have hinj:Function.Injective φ:=IsFractionRing.injective K[X] Frac
  have hd (P:Bivar):(extendSeed P).natDegree=P.natDegree:=natDegree_map_eq_of_injective hinj _
  have hn {P:Bivar} (hp:P≠0):extendSeed P≠0:=(Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir:=B.same_direction
  rw [sameDirection,left_eq,right_eq] at hdir
  have he:=congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom:=max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide:p≠0) hU)) D.coprime he
    (by simp only [hd,D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd,D.max_degree] at htight
  refine ⟨⟨outputs p B.output,hU,hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < P0.k + D.height := by
      by_cases hz:B.output=0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h:=B.nodes
    rwa [relationOn_fun,left_eq,right_eq] at h
end
end Front82706_3
end

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace Front82706_3
noncomputable section
open Front82706 Front82706_4 Polynomial MvPolynomial
open P2_4 (Puncture)
open K1_10 (Plane)
open K1_10_1 (planeRelation planeRelation_view numerator denominator relationBounds)
open K1_11 (sourceWeights sourceBounds filtered mem_filtered polynomialView)
open private coeff_bounds denominator_ne from ProximityPrize.SubmissionLower.PortFrontB

private def plane_contact {u : Words} {deleted : Finset I} {h : ℕ}
    {U V:Fin 2→Polynomial K} (W:Plane u deleted h U V) (P:Puncture deleted) :
    ContactInput u P .w11 h:=by
  let L:=planeRelation U V W.output
  let a:=numerator U W.output
  let b:=denominator V
  have hb:b≠0:=denominator_ne W.V_ne
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j :=
    K1_10_1_1.proof u deleted h U V W
  have hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a :=
    planeRelation_view U V W.output
  have hfit : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071 + h) 1 1 1) :=
    (mem_filtered _ _ _).mpr fun j => (hdeg j).le
  have hn : L ≠ 0 := by
    intro hz
    have hp:=hdeg 1
    simp [hz,relationBounds,weightedTotalDegree] at hp
  obtain ⟨haY,hbY,haS,hbS,haT,hbT⟩:=coeff_bounds L a b _ hfit hview hb
  refine ⟨L,hn,hdeg, ?_,a,b,hb,hview, ?_,haY,hbY,haS,hbS,haT,hbT⟩
  · intro i
    exact K1_10_1_2.proof u deleted h U V W (P.index i) ((P.retained _).mp ⟨i,rfl⟩)
  · exact K1_10_1_3.proof u deleted h U V W

theorem proof : Front82706.c3 := by
  intro u front T R D B _ hnp Γ hΓ hn
  classical
  obtain ⟨W⟩:=plane_of_rankThree B
  have hheight:=relation_height_le front T
  by_cases hsmall:2*D.height < L
  · have hshort := (shortened_guards D front).1
    have hbudget : D.height + (fixedNodes R).card ≤ heightCap :=
      D.height_eq ▸ hheight
    have hcap:heightCap≤blockLength:=by decide
    have hroom:k+3*D.height+(fixedNodes R).card≤blockLength:=by omega
    obtain ⟨J⟩:=adjugate_of_plane B hnp W hroom
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩:=bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hfloor : EnoughHeight .w11 T.height D.height := by
    change ¬ 2*D.height < 48366 at hsmall
    change 24183≤D.height
    omega
  let P:=K1_11.nativePuncture (fixedNodes R)
  let F:=selectMarks D hΓ hn
  let C:=plane_contact W P
  obtain ⟨Q⟩:=exists_annihilator C T.height hfloor hheight D.height_eq F.val F.property
  exact count_of_annihilator P Q F.property

#print axioms proof
end
end Front82706_3
