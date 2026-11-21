import ProximityPrize.SubmissionLower.FrontDirection82219
import ProximityPrize.SubmissionLower.FrontCases82219
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Front82219_5
noncomputable section
open Polynomial Front82219 FrobeniusLocator
open Front82219Direction (Direction)
open private column column_ne column_bound column_dvd firstColumn_normal threeU_fun tight_pair
  slice_bound relationOn_fun outputs nodes_of_columns from ProximityPrize.SubmissionLower.PortFrontB
private def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist
private def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
private theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → K[X]) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
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
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap K[X] Frac
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
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
    have ht : B.output.natDegree < k + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h
private theorem coprime_contents {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) :
    IsCoprime B.a B.b := by
  apply (gcd_isUnit_iff _ _).mp
  apply P.primitive
  · intro i
    exact (gcd_dvd_left B.a B.b).trans (dvd_mul_right _ _)
  · intro j
    rw [rightCoeff, dvd_neg]
    exact (gcd_dvd_right B.a B.b).trans (dvd_mul_right _ _)
private theorem plane_height {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (par : Parallel B) (hdeg : B.b.natDegree = B.a.natDegree) :
    D.height = B.a.natDegree + amplitudeDegree (B.α 0) (B.α 1) := by
  let s := amplitudeDegree (B.α 0) (B.α 1)
  have hA (i : Fin 2) : (B.α i).natDegree ≤ s := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hL (i : Fin 2) : (leftCoeff B i).natDegree ≤ B.a.natDegree + s := by
    change B.α = B.β at par
    unfold leftCoeff
    rw [← par]
    exact natDegree_mul_le_of_le le_rfl (natDegree_map_le.trans (hA i))
  have hR (j : Fin 2) : (rightCoeff B j).natDegree ≤ B.a.natDegree + s := by
    rw [rightCoeff, natDegree_neg, ← hdeg]
    exact natDegree_mul_le_of_le le_rfl (hA j)
  have hmax := max_le (max_le (hL 0) (hL 1)) (max_le (hR 0) (hR 1))
  exact le_antisymm (P.height_eq ▸ hmax) (hdeg ▸ B.second_degree)
private theorem plane_nodes {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (par : Parallel B) (x : I) (hx : x ∉ fixedNodes R) (i j : Fin 2) :
    (P.output j i).eval (node x) =
      B.a.eval (node x) * ((B.α i).map twist).eval (node x) * u j x -
      B.b.eval (node x) * (B.α j).eval (node x) * twist (u i x) := by
  change B.α = B.β at par
  simpa only [leftCoeff, rightCoeff, eval_mul, eval_neg, neg_mul,
    ← sub_eq_add_neg, ← par, twist, frobenius_def] using (P.nodes x hx j i).symm
theorem direction_of_rankThree {u T R D} (hu : FrontRemainder u)
    (B : RankThree u T R D) (par : Parallel B) (hnorm : UnitNorm B) :
    ∃ F : Direction u (fixedNodes R),
      F.U.natDegree + F.s + (fixedNodes R).card ≤ heightCap := by
  obtain ⟨P⟩ := plane_of_rankThree B
  change K1.sixNorm B.a = K1.sixNorm B.b at hnorm
  obtain ⟨den, hden, hphase, hnodes⟩ := K1_12_1.denominator B.b_ne hnorm
  have hden' : den.map twist ≠ 0 := (Polynomial.map_ne_zero_iff twist.injective).mpr hden
  have hdeg := congrArg (fun Q : K[X] => Q.natDegree) hphase
  change (B.a * den.map twist).natDegree = (B.b * den).natDegree at hdeg
  rw [natDegree_mul B.a_ne hden', natDegree_mul B.b_ne hden,
    natDegree_map_eq_of_injective twist.injective] at hdeg
  have hdeg' : B.b.natDegree = B.a.natDegree := by omega
  have hcop := coprime_contents B P
  have hheight := plane_height B P par hdeg'
  have hdvd : B.a ∣ den := hcop.dvd_of_dvd_mul_left
    (hphase ▸ dvd_mul_right B.a (den.map twist))
  have hheight' : B.a.natDegree + amplitudeDegree (B.α 0) (B.α 1) +
      (fixedNodes R).card ≤ heightCap := by
    rw [← hheight, D.height_eq]
    exact relation_height_le hu T
  refine ⟨{
    den := den
    U := B.a
    V := B.b
    A := B.α
    out := fun i j => P.output j i
    den_nodes := hnodes
    U_ne := B.a_ne
    V_ne := B.b_ne
    U_dvd := hdvd
    coprime := hcop
    phase := hphase
    degrees_eq := hdeg'
    primitive := B.α_primitive
    height := hheight'
    out_degree := by
      intro i j
      simpa only [hheight, ← Nat.add_assoc] using P.output_degree j i
    nodes := plane_nodes B P par
  }, hheight'⟩
end
end Front82219_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Front82219_5
noncomputable section
open Polynomial Front82219 FrobeniusLocator
open Front82219Direction (Direction Regular Offset eval_twist)
open K1_12 (eval_unit_of_dvd invariant_multiple)
open private coprime_factor_of_label from ProximityPrize.SubmissionLower.Fast068
open Front82219Direction (E_nodes numerator numerator_degree fixed_numerator hits)
theorem normalize {u : Words} {deleted : Finset I} (F : Direction u deleted)
    (height : F.U.natDegree + F.s + deleted.card ≤ heightCap) (Γ : Finset K)
    (reg : ∀ γ ∈ Γ, Regular F γ) (original : ∀ g : Γ, BadMark u g.val)
    (avoid : ∀ g, Disjoint (original g).support deleted) (η ζ : Γ) (hne : ζ.val ≠ η.val)
    (O : Offset F (original η)) :
    ∃ M : AnchorModel u deleted, ∃ S : Γ → K[X],
      ∃ marks : ∀ g : Γ, AnchorMark M g.val (S g), ∀ g, (marks g).bad = original g := by
  classical
  let m (g : Γ) := original g
  obtain ⟨W,hW⟩ := O.left.trans F.U_dvd
  have hWn (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  obtain ⟨L,c,hL,hLf,hLn,hsplit⟩ := invariant_multiple W hWn
  change L.map twist = L at hLf
  have hcn (i : I) : c.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hL ▸ dvd_mul_left c W) (hLn i)
  have hscalar (g : Γ) : ∃ S : K[X], S.map twist = S ∧
      numerator O (m g) = c * F.amp g.val * S := by
    obtain ⟨N, hN, hfix⟩ := fixed_numerator O W hW (m g) (avoid g) (reg g.val g.property)
    obtain ⟨S,hS,hNS⟩ := hsplit N hfix
    exact ⟨S,hS,by rw [hN,hNS]; ring⟩
  choose S hS ident using hscalar
  let word (i : I) := if i ∈ deleted then 0 else O.raw i / L.eval (node i)
  have hword (i : I) (hi : i ∉ deleted) : word i = O.raw i / L.eval (node i) := by simp [word, hi]
  have hden (i : I) : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by
    rw [hW, eval_mul]
  have hLval (i : I) : L.eval (node i) = W.eval (node i) * c.eval (node i) := by rw [hL, eval_mul]
  have hs : amplitudeDegree (F.amp η.val) (F.A 1) = F.s := by
    unfold amplitudeDegree
    rw [(reg η.val η.property).degree_eq]
    exact max_eq_left (le_max_right _ _)
  have hcop : IsCoprime O.E c := coprime_factor_of_label (sub_ne_zero.mpr hne) O.reduced (ident ζ)
  let M : AnchorModel u deleted := {
    shift := η.val
    pencil₀ := (m η).decoder
    pencil₁ := O.pencil
    pencil₀_degree := (m η).degree
    pencil₁_degree := O.pencil_degree
    E := O.E
    factor := c
    Q := O.Q
    A₀ := F.amp η.val
    A₁ := F.A 1
    word := word
    word_fixed := by
      intro i
      by_cases hi : i ∈ deleted
      · simp [word,hi]
      · rw [hword i hi, map_div₀, O.raw_fixed i hi, ← eval_twist L i, hLf]
    word_deleted := fun i hi => by simp [word, hi]
    E_monic := O.E_monic
    E_nodes := E_nodes O
    factor_nodes := fun i _ => hcn i
    coprime_factor := hcop
    offset_proper := O.proper
    offset_reduced := O.reduced
    adjacent_coprime := F.coprime.mono O.left O.right
    amplitudes_primitive := by
      obtain ⟨x,y,hxy⟩ := F.primitive
      exact ⟨x,y - x*C η.val,by unfold Direction.amp; linear_combination hxy⟩
    first_amplitude_unit := (reg η.val η.property).content_unit.of_isCoprime_of_dvd_right O.left
    height_bound := by
      rw [hs]
      have hd := natDegree_le_of_dvd O.left F.U_ne
      change O.E.natDegree + F.s ≤ heightCap
      omega
    first_word := by
      intro i hi
      rw [O.first i hi, hword i hi]
      field_simp [F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring
    second_word := by
      intro i hi
      rw [O.second i hi, hword i hi]
      field_simp [E_nodes O i, F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring }
  have amp_eq (g : Γ) : P1.ModelAt.amplitude M g.val = F.amp g.val := by
    change F.amp η.val + C (g.val-η.val) * F.A 1 = F.amp g.val
    simp only [Direction.amp, map_sub]
    ring
  let marks (g : Γ) : AnchorMark M g.val (S g) := by
    have hreg := reg g.val g.property
    refine {
      bad := original g
      avoids_deleted := avoid g
      scalar_fixed := hS g
      scalar_degree := ?_
      scalar_hits := ?_
      pole_unit := ?_
      identity := ?_ }
    · by_cases hz : S g = 0
      · exact Or.inl hz
      right
      have hc : c ≠ 0 := fun h => hcn 0 (by rw [h, eval_zero])
      have hd := numerator_degree O (m g)
      rw [ident g, natDegree_mul (mul_ne_zero hc hreg.amp_ne) hz,
        natDegree_mul hc hreg.amp_ne, hreg.degree_eq] at hd
      change (S g).natDegree ≤ (k : ℤ) - 1 + (O.E.natDegree - c.natDegree -
        (amplitudeDegree (F.amp η.val) (F.A 1) : ℤ))
      rw [hs]
      omega
    · intro i hi
      have hits := hits O W hW (m g) (avoid g) i hi
      rw [ident g, eval_mul, eval_mul] at hits
      change (S g).eval (node i) = word i
      have hd := Finset.disjoint_left.mp (avoid g) hi
      rw [hword i hd, eq_div_iff (hLn i), hLval]
      apply mul_left_cancel₀ (hreg.node_unit i hd)
      linear_combination hits
    · rw [amp_eq g]
      exact hreg.content_unit.of_isCoprime_of_dvd_right O.left
    · rw [amp_eq g]
      exact ident g
  exact ⟨M, S, marks, fun g => rfl⟩
end
end Front82219_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Front82219_5
noncomputable section
open Polynomial Front82219 FrobeniusLocator
open Front82219Direction (Regular excluded excluded_card_le cross_lift)
private theorem other_hits {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) (i : I) (hi : i ∈ m.bad.support) :
    n.bad.decoder.eval (node i) = u 0 i + δ * u 1 i := by
  have hd := Finset.disjoint_left.mp m.avoids_deleted hi
  have h0 := M.first_word i hd
  have h1 := M.second_word i hd
  have h := congrArg (eval (node i)) n.identity
  simp only [P1.ModelAt.decoder, P1.ModelAt.amplitude, P1.ModelAt.label, eval_sub,
    eval_mul, eval_C, eval_add, m.scalar_hits i hi] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show M.E.eval (node i) * _ = 0 from ?_)).resolve_left (M.E_nodes i)
  linear_combination h - h0 - (δ - M.shift) * h1
private theorem same_scalar_label {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) : γ = δ := by
  by_contra hne
  let V := (δ-γ)⁻¹ • (n.bad.decoder - m.bad.decoder)
  have hd : δ-γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hV : V.degree < k := Principal.degree_smul_lt _
    (Principal.degree_sub_lt n.bad.degree m.bad.degree)
  have hv (i : I) (hi : i ∈ m.bad.support) : V.eval (node i) = u 1 i := by
    simp only [V, eval_smul, eval_sub, smul_eq_mul, other_hits m n i hi, m.bad.hits i hi]
    field_simp [hd]
    ring
  apply m.bad.nonjoint
  refine ⟨⟨m.bad.decoder - γ • V, Principal.degree_sub_lt m.bad.degree
    (Principal.degree_smul_lt _ hV), ?_⟩, ⟨V, hV, hv⟩⟩
  intro i hi
  simp only [eval_sub, eval_smul, smul_eq_mul, m.bad.hits i hi, hv i hi]
  ring
theorem proof : Front82219.c5 := by
  classical
  intro u hu T R D B _ par unit Γ bad normal
  by_cases hsmall : Γ.card ≤ anchorFee
  · exact Or.inl hsmall
  right
  obtain ⟨F, height⟩ := direction_of_rankThree hu B par unit
  let book := excluded F Γ
  have hbook : book ⊆ Γ := Finset.filter_subset _ _
  have hcard : book.card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 :=
    excluded_card_le F Γ
  have hbudget : book.card + 1 ≤ anchorFee := by
    have hprod := Nat.mul_le_mul_left p (show F.s ≤ heightCap by omega)
    rw [Nat.add_mul, one_mul] at hcard
    rw [← anchor_fee_exact]
    omega
  let Δ := Γ \ book
  have hbig : 1 < Δ.card := by
    have hpart := Finset.card_sdiff_add_card_eq_card hbook
    change Δ.card + book.card = Γ.card at hpart
    omega
  have regular (δ : K) (hd : δ ∈ Δ) : Regular F δ := by
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hd
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hin, h⟩)
  let m (g : Δ) := Classical.choice (bad_mark u Γ bad g.val (Finset.mem_sdiff.mp g.property).1)
  have avoid (g : Δ) : Disjoint (m g).support (fixedNodes R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (Finset.mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).hits i hi)
  obtain ⟨η, hη, ζ, hζ, hne⟩ := Finset.one_lt_card.mp hbig
  let a : Δ := ⟨η, hη⟩
  let b : Δ := ⟨ζ, hζ⟩
  obtain ⟨lift⟩ := cross_lift F
  obtain ⟨O⟩ := Front82219Direction.offset_of_anchor F lift (m a) (avoid a) (regular η hη)
  obtain ⟨M, S, marks, _⟩ := normalize F height Δ regular m avoid a b hne.symm O
  let scalar (γ : K) : K[X] := if h : γ ∈ Δ then S ⟨γ, h⟩ else 0
  have hmarked (γ : K) (hγ : γ ∈ Δ) : AnchorMark M γ (scalar γ) := by
    simpa only [scalar, dite_eq_left hγ] using marks ⟨γ, hγ⟩
  refine ⟨book, hbook, by omega, M, ⟨⟨scalar, hmarked, ?_⟩⟩⟩
  intro γ hγ δ hδ he
  exact same_scalar_label (hmarked γ hγ) (he ▸ hmarked δ hδ)
end
end Front82219_5
end
