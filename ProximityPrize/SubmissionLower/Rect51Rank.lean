import ProximityPrize.SubmissionLower.UpperBranch5

/-! The rectangular terminal idea follows the public kaankolcu 69.50 note,
submission f9161583-1b70-4048-8a65-bae6ee236fe4. -/

set_option Elab.async false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false
namespace Rect51Rank
noncomputable section

open K1_14 (FX Equation Jet)
open MvPolynomial Finset
open scoped BigOperators
open private flatten flatten_mem_bidegree from ProximityPrize.SubmissionLower.Fast069

abbrev Exp := Option (Fin 2) →₀ ℕ

def coordDegree (c : Equation) (i : Option (Fin 2)) : ℕ :=
  (flatten c).weightedTotalDegree (Pi.single i 1)

theorem coordDegree_mul {c d : Equation} (hc : c ≠ 0) (hd : d ≠ 0) (i) :
    coordDegree (c*d) i = coordDegree c i + coordDegree d i := by
  unfold coordDegree
  rw [map_mul,weightedTotalDegree_mul]
  · exact fun hn => hc (flatten.injective (hn.trans (map_zero flatten).symm))
  · exact fun hn => hd (flatten.injective (hn.trans (map_zero flatten).symm))

theorem coordDegree_pow {c : Equation} (hc : c ≠ 0) (i) (n : ℕ) :
    coordDegree (c^n) i = n*coordDegree c i := by
  induction n with
  | zero => rw [pow_zero,zero_mul,coordDegree,map_one,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ n ih => rw [pow_succ,coordDegree_mul (pow_ne_zero n hc) hc,ih,Nat.succ_mul]

def slots (U0 U1 t0 t1 : ℕ) : ℕ :=
  if t0≤U0 ∧ t1≤U1 then (U0-t0+1)*(U1-t1+1) else 0

private def boxExponent {a b c : ℕ} (x : Fin a × Fin b × Fin c) : Exp :=
  Finsupp.equivFunOnFinite.symm fun k =>
    k.elim x.1.val (fun i => if i=0 then x.2.1.val else x.2.2.val)

private theorem boxExponent_injective (a b c : ℕ) :
    Function.Injective (@boxExponent a b c) := by
  intro x y he
  have eq (k) := congrArg (fun e : Exp => e k) he
  have h0 := eq none
  have h1 := eq (some 0)
  have h2 := eq (some 1)
  simp only [boxExponent,Finsupp.coe_equivFunOnFinite_symm,Option.elim,ite_true,
    show (1 : Fin 2) ≠ 0 by decide,ite_false] at h0 h1 h2
  exact Prod.ext (Fin.ext h0) (Prod.ext (Fin.ext h1) (Fin.ext h2))

private def box (a u0 u1 : ℕ) : Finset Exp :=
  Finset.univ.map ⟨@boxExponent a (u0+1) (u1+1), boxExponent_injective a (u0+1) (u1+1)⟩

private theorem mem_box_of {a u0 u1} (m : Exp)
    (ha : m none<a) (h0 : m (some 0)≤u0) (h1 : m (some 1)≤u1) : m∈box a u0 u1 := by
  refine Finset.mem_map.mpr ⟨⟨⟨m none,ha⟩,⟨m (some 0),by omega⟩,⟨m (some 1),by omega⟩⟩,
    Finset.mem_univ _,?_⟩
  ext k
  cases k with
  | none => simp [boxExponent]
  | some k => fin_cases k <;> simp [boxExponent]

private theorem card_box (a u0 u1) : (box a u0 u1).card = a*((u0+1)*(u1+1)) := by
  simp [box,Fintype.card_prod]

private theorem exponent_le (c : Equation) (i : Option (Fin 2)) {m : Exp}
    (hm : m∈(flatten c).support) : m i≤coordDegree c i := by
  rw [coordDegree,weightedTotalDegree_piSingle]
  exact monomial_le_degreeOf i hm

theorem rank_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g≠0)
    {a u0 u1 yspent t0 t1 : ℕ} (hy : yspent≤g.natDegree)
    (h0 : t0≤coordDegree g (some 0)) (h1 : t1≤coordDegree g (some 1))
    (hC : ∀ c∈C, c≠0 → c.natDegree<a ∧ coordDegree c (some 0)≤u0 ∧
      coordDegree c (some 1)≤u1 ∧ g∣c) :
    Module.rank FX C≤(↑((a-yspent)*slots u0 u1 t0 t1) : Cardinal) := by
  have hquot (c : Equation) (hc : c∈C) (hn : c≠0) : ∃ q : Equation,
      c=g*q ∧ q.natDegree<a-yspent ∧ t0+coordDegree q (some 0)≤u0 ∧
      t1+coordDegree q (some 1)≤u1 := by
    obtain ⟨hY,hu0,hu1,q,rfl⟩ := hC c hc hn
    have hq : q≠0 := right_ne_zero_of_mul hn
    rw [Polynomial.natDegree_mul hg hq] at hY
    rw [coordDegree_mul hg hq] at hu0 hu1
    exact ⟨q,rfl,by omega,by omega,by omega⟩
  by_cases hh : t0≤u0 ∧ t1≤u1
  · let E := box (a-yspent) (u0-t0) (u1-t1)
    let V := restrictSupport FX (↑E : Set Exp)
    letI : Module.Finite FX V := restrictSupport_finite E.finite_toSet
    let m : V→ₗ[FX] Equation :=
      (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp V.subtype)
    have hle : C≤LinearMap.range m := by
      intro c hc
      by_cases hn : c=0
      · rw [hn]
        exact Submodule.zero_mem _
      obtain ⟨q,rfl,hq,hu0,hu1⟩ := hquot c hc hn
      have hqV : flatten q∈V := by
        apply (mem_restrictSupport_iff FX).mpr
        intro x hx
        apply mem_box_of
        · have hmem := flatten_mem_bidegree (u := K1_14_4.seedDegree q) (a := q.natDegree) le_rfl le_rfl
          rw [mem_restrictBidegree] at hmem
          exact (hmem x hx).1.trans_lt hq
        · exact (exponent_le _ _ hx).trans (Nat.le_sub_of_add_le (by omega))
        · exact (exponent_le _ _ hx).trans (Nat.le_sub_of_add_le (by omega))
      refine ⟨⟨flatten q,hqV⟩,?_⟩
      change g*flatten.symm (flatten q) = g*q
      rw [AlgEquiv.symm_apply_apply]
    have hv : Module.finrank FX V=(a-yspent)*slots u0 u1 t0 t1 := by
      rw [finrank_restrictSupport_finset,card_box,slots,if_pos hh]
    calc
      _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hle
      _ ≤ Module.rank FX V := rank_range_le m
      _ = _ := by rw [← Module.finrank_eq_rank,hv]
  · have hbot : C=⊥ := by
      apply bot_unique
      intro c hc
      rw [Submodule.mem_bot]
      by_contra hn
      obtain ⟨q,_,_,h0',h1'⟩ := hquot c hc hn
      exact hh ⟨by omega,by omega⟩
    rw [hbot]
    simp


theorem slots_symm (U x y : ℕ) : slots U U x y = slots U U y x := by
  by_cases hx : x≤U <;> by_cases hy : y≤U <;> simp [slots,hx,hy,Nat.mul_comm]

theorem slots_le_balanced (U r V x y : ℕ) (hV : V≤x+y) :
    slots U U (r*x) (r*y) ≤ slots U U (r*(V/2)) (r*((V+1)/2)) := by
  wlog hxy : x≤y generalizing x y
  · rw [slots_symm]
    exact this _ _ (by omega) (by omega)
  by_cases hU : r*x≤U ∧ r*y≤U
  · let a := V/2
    let b := (V+1)/2
    have hab : a≤b := by dsimp [a,b]; omega
    have hby : b≤y := by dsimp [b]; omega
    have hb := (Nat.mul_le_mul_left r hby).trans hU.2
    have ha := (Nat.mul_le_mul_left r hab).trans hb
    have htarget : r*a≤U ∧ r*b≤U := ⟨ha,hb⟩
    change slots U U (r*x) (r*y) ≤ slots U U (r*a) (r*b)
    unfold slots
    rw [if_pos hU,if_pos htarget]
    by_cases hx : a≤x
    · exact Nat.mul_le_mul (by have h := Nat.mul_le_mul_left r hx; omega)
        (by have h := Nat.mul_le_mul_left r hby; omega)
    · let aWidth := U-r*a+1
      let bWidth := U-r*b+1
      let xWidth := U-r*x+1
      let yWidth := U-r*y+1
      let shift := xWidth-aWidth
      have hAX : aWidth≤xWidth := by
        dsimp only [aWidth,xWidth]
        have h := Nat.mul_le_mul_left r (show x≤a by omega)
        omega
      have hYA : yWidth≤aWidth := by
        dsimp only [aWidth,yWidth]
        have h := Nat.mul_le_mul_left r (hab.trans hby)
        omega
      have hYD : yWidth+shift≤bWidth := by
        dsimp only [aWidth,bWidth,xWidth,yWidth,shift]
        have h := Nat.mul_le_mul_left r hV
        have hv : a+b=V := by dsimp [a,b]; omega
        simp only [Nat.mul_add] at h
        have hv' := congrArg (r*·) hv
        rw [Nat.mul_add] at hv'
        omega
      change xWidth*yWidth≤aWidth*bWidth
      calc
        xWidth*yWidth = aWidth*yWidth+shift*yWidth := by rw [← Nat.add_mul]; congr 1; dsimp only [shift]; omega
        _ ≤ aWidth*yWidth+shift*aWidth := Nat.add_le_add_left (Nat.mul_le_mul_left _ hYA) _
        _ = aWidth*(yWidth+shift) := by ring
        _ ≤ aWidth*bWidth := Nat.mul_le_mul_left _ hYD
  · unfold slots
    rw [if_neg hU]
    exact Nat.zero_le _


open Polynomial
open K1_14 (Shape)
open K1_14_4 (gradeWidth)
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069

def gradeCapacity (h : ℕ) (s : Shape) (U E V W order j : ℕ) : ℕ :=
  let r := order - j
  (gradeWidth (131071-h) s.B W j - r*E) * slots U U (r*(V/2)) (r*((V+1)/2))

/-- Rectangular rank bound on rows retained by a factor family. -/
theorem cutoff_finrank_le (h : ℕ) (s : Shape) (U E V W order : ℕ) (C : Submodule FX Jet)
    {f : Equation} (hf : f≠0) (hE : E≤f.natDegree)
    (hV : V≤coordDegree f (some 0)+coordDegree f (some 1)) (hk : 0<131071-h)
    (hshape : ∀ P∈C, P≠0 → P.leadingCoeff.natDegree+P.natDegree≤s.B∧P.natDegree≤s.J)
    (hbox : ∀ P∈C, ∀ i : Fin 2, coordDegree P.leadingCoeff (some i)≤U)
    (hlead : ∀ P∈C, P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈C, P≠0 → f^(order-P.natDegree)∣P.leadingCoeff) :
    Module.finrank FX C≤∑ j∈range (s.J+1),gradeCapacity h s U E V W order j := by
  refine finrank_le_grades (F := FX) (A := Equation) C (gradeCapacity h s U E V W order)
    (s.J+1) ?_ ?_
  · intro j
    let r := order - j
    let a := gradeWidth (131071-h) s.B W j
    let x := coordDegree f (some 0)
    let y := coordDegree f (some 1)
    have hy := Nat.mul_le_mul_left r hE
    have hfPow : f^r≠0 := pow_ne_zero _ hf
    have hwn := show r*E ≤ (f^r).natDegree by rwa [natDegree_pow]
    have h0 := show r*x ≤ coordDegree (f^r) (some 0) by rw [coordDegree_pow hf]
    have h1 := show r*y ≤ coordDegree (f^r) (some 1) by rw [coordDegree_pow hf]
    refine (rank_multiples_le _ hfPow (a := a) (u0 := U) (u1 := U) hwn h0 h1 ?_).trans ?_
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := fun hz => hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      have hB := (hshape P hpV hn).1
      have hW := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hW hdiv
      change (P.coeff j).natDegree < a ∧ coordDegree (P.coeff j) (some 0)≤U ∧
        coordDegree (P.coeff j) (some 1)≤U ∧ f^r ∣ P.coeff j
      rw [← hj,coeff_natDegree]
      refine ⟨?_,hbox P hpV 0,hbox P hpV 1,hdiv⟩
      have hq := (Nat.le_div_iff_mul_le hk).2 hW
      unfold a gradeWidth
      omega
    · exact_mod_cast Nat.mul_le_mul_left (a-r*E) (slots_le_balanced U r V x y hV)
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hshape P hp hn).2)

#print axioms rank_multiples_le
#print axioms slots_le_balanced
#print axioms cutoff_finrank_le
end
end Rect51Rank
