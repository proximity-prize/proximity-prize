import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false

-- merged module R6960HelperSource6960
section Merged_R6960HelperSource6960
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
def helperBank : Bank := ⟨⟨294,408,89,7376⟩,777085255680,779461982⟩
theorem helper_bank_checked : P3_7_1.BankOK helperBank := by
  have moment : P1_7_1_3.momentEstimate 408 89 = 779461982 := by
    refine P1_7_1_3_2.moment_from_blocks
      [(128,109021770),(128,353396160),(128,272672821),(113,44371231)] ?_ rfl rfl
    exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
  exact P3_7_1.checked helperBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment
inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary
def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1
def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0
def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 86
  | .mixedBoundary => 79
  | _ => 1
private def compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  (compressedPhase helperBank.shape 179818 h 10 test.slope test.excess test.seed 0 -
    compressedPhase helperBank.shape 179818 h 10 test.slope test.excess test.seed 1 : ℕ) - (debit h helperBank : ℤ)
private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) :
    compressedSurplus h test = surplus helperBank 179818 h 10 test.slope test.excess test.seed := by
  unfold compressedSurplus surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ (by cases test <;> decide)]
private theorem twoSlopes_first :
    compressedSurplus 2359 .twoSlopes = 1315756893570 := by rfl
private theorem twoSlopes_next :
    compressedSurplus 2360 .twoSlopes = 135642678453300 := by rfl
private theorem seedBoundary_first :
    compressedSurplus 2359 .seedBoundary = 951451442183972 := by rfl
private theorem seedBoundary_next :
    compressedSurplus 2360 .seedBoundary = 1086170799811930 := by rfl
private theorem mixedBoundary_first :
    compressedSurplus 2359 .mixedBoundary = 765760703428686 := by rfl
private theorem mixedBoundary_next :
    compressedSurplus 2360 .mixedBoundary = 900411679649940 := by rfl
private theorem jetBoundary_first :
    compressedSurplus 2359 .jetBoundary = 6850472265407568 := by rfl
private theorem jetBoundary_next :
    compressedSurplus 2360 .jetBoundary = 6987702602189220 := by rfl
theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2359≤h) (hi : h≤33579) :
    debit h helperBank < gain helperBank.shape 179818 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2359 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus helperBank 179818 2359 10 test.slope test.excess test.seed ≤
      surplus helperBank 179818 2360 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq, ← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2359≤h) (hi : h≤33579) :
    WidthGuard helperBank 179818 h 10 :=
  width_at_height _ _ 2359 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179818 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q :=
  crt_avoiding_row Crt word helperBank 179818 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (by decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179818 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤85 ∧ (2≤jetDegree G → seedDegree G≤78) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 86≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 79≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179818 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179818 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.HelperSource

end Merged_R6960HelperSource6960

-- merged module R6960PrefixReceipt
section Merged_R6960PrefixReceipt

-- merged module R6960DifferentialContact
section Merged_R6960DifferentialContact
noncomputable section
namespace Lower6960.DifferentialContact
open MvPolynomial K1_14_2_2_3
open K1_14_2_2_3_1 (partial_append)
variable {K : Type*} [CommRing K]
abbrev A (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
def Contact (I : Ideal (A K)) (n : ℕ) (f : A K) : Prop :=
  ∀ w : List (Fin 2),w.length<n → partialWord f w∈I
theorem zero_order (I : Ideal (A K)) (f : A K) : Contact I 0 f := by
  intro w h; omega
theorem succ_iff (I : Ideal (A K)) (n : ℕ) (f : A K) :
    Contact I (n+1) f ↔ f∈I ∧ ∀ i, Contact I n (pderiv i f) := by
  constructor
  · intro h; refine ⟨h [] (by simp),?_⟩
    intro i w hw
    rw [←partial_append]
    exact h _ (by simp; omega)
  · rintro ⟨hf,hd⟩ w hw
    induction w using List.reverseRecOn with
    | nil => exact hf
    | append_singleton ws i _ =>
      rw [partial_append]
      apply hd i ws
      simpa using hw
theorem weaken {I : Ideal (A K)} {n m : ℕ} {f : A K} (h : Contact I n f) (le : m≤n) :
    Contact I m f := fun w hw => h w (hw.trans_le le)
def testIdeal (I : Ideal (A K)) (n : ℕ) : Ideal (A K) where
  carrier := {f | Contact I n f}
  zero_mem' := by
    change Contact I n 0
    induction n with
    | zero => exact zero_order I _
    | succ n ih => exact (succ_iff I n 0).2 ⟨I.zero_mem, fun i=>by simpa using ih⟩
  add_mem' := by
    intro f g hf hg
    change Contact I n f at hf
    change Contact I n g at hg
    change Contact I n (f+g)
    induction n generalizing f g with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      obtain ⟨g0,dg⟩ := (succ_iff ..).1 hg
      exact (succ_iff ..).2 ⟨I.add_mem f0 g0, fun i=>by rw [map_add];exact ih (df i) (dg i)⟩
  smul_mem' := by
    intro a f hf
    change Contact I n f at hf
    change Contact I n (a*f)
    induction n generalizing a f with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      refine (succ_iff ..).2 ⟨I.mul_mem_left _ f0,?_⟩
      intro i; rw [pderiv_mul]
      have h1:=ih (pderiv i a) (weaken (m:=n) hf (by omega))
      have h2:=ih a (df i)
      intro w hw
      have distrib (g h : A K) : partialWord (g+h) w=partialWord g w+partialWord h w := by
        clear hw
        induction w with
        | nil => rfl
        | cons j w ih => simp only [partialWord,ih,map_add]
      rw [distrib]
      exact I.add_mem (h1 _ hw) (h2 _ hw)
theorem product {I : Ideal (A K)} (n m : ℕ) (f g : A K)
    (hf : Contact I n f) (hg : Contact I m g) : Contact I (n+m) (f*g) := by
  induction n generalizing m f g with
  | zero =>
    rw [Nat.zero_add]
    exact (testIdeal I m).mul_mem_left f hg
  | succ n ih =>
    induction m generalizing g with
    | zero =>
      rw [Nat.add_zero,mul_comm];exact (testIdeal I (n+1)).mul_mem_left g hf
    | succ m jh =>
      have df := ((succ_iff ..).1 hf).2
      have dg := ((succ_iff ..).1 hg).2
      refine (succ_iff ..).2 ⟨I.mul_mem_left f ((succ_iff ..).1 hg).1,?_⟩
      intro i; rw [pderiv_mul]
      apply (testIdeal I (n+1+m)).add_mem
      · change Contact I (n+1+m) ((pderiv i f)*g)
        simpa only [Nat.succ_add,Nat.add_succ] using ih (m+1) (pderiv i f) g (df i) hg
      · change Contact I (n+1+m) (f*(pderiv i g))
        exact jh (pderiv i g) (dg i)
theorem row_power {I : Ideal (A K)} {f : A K} {n : ℕ} (hf : Contact I n f) (k : ℕ) :
    Contact I (k*n) (f^k) := by
  induction k with
  | zero => rw [Nat.zero_mul]; exact zero_order I _
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact product _ _ _ _ ih hf
theorem row_strip {I : Ideal (A K)} (prime : I.IsPrime) (n : ℕ) (g f : A K)
    (unit : g∉I) (h : Contact I n (g*f)) : Contact I n f := by
  induction n generalizing f with
  | zero => exact zero_order I _
  | succ n ih =>
    obtain ⟨prod0,dprod⟩ := (succ_iff ..).1 h
    refine (succ_iff ..).2 ⟨(prime.mem_or_mem prod0).resolve_left unit,?_⟩
    have low := ih f (weaken h (by omega))
    intro i
    apply ih
    have data:=dprod i
    rw [pderiv_mul] at data
    have first := (testIdeal I n).mul_mem_left (pderiv i g) low
    have diff := (testIdeal I n).sub_mem data first
    change g*(pderiv i f) ∈ testIdeal I n
    simpa only [add_sub_cancel_left] using diff
open K1_14 (Jet Seeds)
open K1_14_2 (Ambient toJet)
open K1_14_2_2_3 (shiftedWord specialize_shiftedWord)
def Native (J : Ideal Ambient) (n : ℕ) (P : Jet) : Prop :=
  ∀ w : List (Fin 2),w.length<n → toJet (shiftedWord P w)∈J
private def coords : Jet →+* A Seeds := seedPresentation.toRingHom.comp toJet
private theorem native_iff (J : Ideal Ambient) (n : ℕ) (P : Jet) :
    Native J n P ↔ Contact (J.comap seedPresentation.symm.toRingHom) n (coords P) := by
  have commute (w : List (Fin 2)) : partialWord (coords P) w=coords (shiftedWord P w) := by
    have hh:=specialize_shiftedWord (RingHom.id Seeds) P w
    simpa [coords,specializeJets,MvPolynomial.map_id] using hh.symm
  constructor
  · intro h w hw
    rw [commute]
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J
    simpa using h w hw
  · intro h w hw
    have mem:=h w hw
    rw [commute] at mem
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J at mem
    simpa using mem
theorem native_power {J : Ideal Ambient} {n k r : ℕ} {P : Jet} (h : Native J n P)
    (fit : r≤k*n) : Native J r (P^k) := by
  apply (native_iff ..).2
  rw [map_pow]
  exact weaken (row_power ((native_iff ..).1 h) k) fit
theorem native_strip {J : Ideal Ambient} (hJ : J.IsPrime) {G P : Jet} (n : ℕ)
    (outside : toJet G∉J) (h : Native J n (G*P)) : Native J n P := by
  let I := J.comap seedPresentation.symm.toRingHom
  let _ : J.IsPrime := hJ
  have mem := (native_iff ..).1 h
  rw [map_mul] at mem
  apply (native_iff ..).2
  apply row_strip (I:=I) (Ideal.IsPrime.comap seedPresentation.symm.toRingHom) n (coords G) (coords P) _ mem
  change seedPresentation.symm (seedPresentation (toJet G))∉J
  simpa using outside
end Lower6960.DifferentialContact

end
end Merged_R6960DifferentialContact

-- merged module R6960PrefixRows
section Merged_R6960PrefixRows
noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1 (I K)
open K1_14 (Shape Jet FX Seeds Equation L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (Ambient toJet UsesSeed jetMarkHom)
open Lower6960.DifferentialContact (Native native_strip native_power weaken)
open Lower6960.HelperPrefix (one_helper timesShape)
open K1_14_2_2_3 (shiftedWord shift_word)
open K1_14_2_2_2_1 (divisor_caps)
open scoped Classical
theorem contact_of_crt {h agreement W reserve : ℕ} {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (P : Jet)
    (inside : P ∈ evaluated Crt word s W) (width : W + 2*h*reserve < s.m*agreement)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K) (S : (Polynomial K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (many : agreement ≤ hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i) :
    Native (RingHom.ker (jetMarkHom z S)) (reserve+1) P := by
  intro w hw
  have shift : K1_14_3.SeedShift h (evaluated Crt word) s :=
    fun _ _ hin i r => P0_10_1.evaluated_shift Crt word hin i r
  have mem := shift_word shift inside w
  have fit : W+2*h*w.length<s.m*agreement :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : w.length≤reserve)) _) width
  apply RingHom.mem_ker.mpr
  rw [K1_14_2.eval_toJet]
  exact P0_10_1.contact_vanish Crt word noPole z S residues degree hits many agree _ _ fit _ mem
def Common (V : Submodule FX Jet) (G : Jet) : Prop :=
  Irreducible G ∧ 0<G.natDegree ∧ UsesSeed G ∧ ∀ H∈V, G∣H
structure Prepared {ι : Type*} (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape) where
  exception : Jet
  kind : exception=1 ∨ Common V exception
  free : ι→Jet
  helper : Jet
  helper_mem : helper∈V
  helper_ne : helper≠0
  free_ne : ∀ i,free i≠0
  stripped : ∀ i,∃ k : ℕ, P i=exception^k*free i
  free_caps : ∀ i,K1_14_2_2.RowCaps (free i) (s i)
  moving_caps : ∀ i,K1_14_2_2.RowCaps (helper^(ks i)) (timesShape (ks i) hs)
  no_moving : ∀ i,K1_14_3.NoMovingCommon (free i) (helper^(ks i))
  contacts : ∀ i (J : Ideal Ambient),J.IsPrime → toJet exception∉J →
    ∀ r a : ℕ, r≤ks i*a → Native J r (P i) → (∀ H∈V,Native J a H) →
      Native J r (free i) ∧ Native J r (helper^(ks i))
theorem power_caps {H : Jet} {hs : Shape} (hn : H≠0)
    (cap : K1_14_2_2.RowCaps H hs) (k : ℕ) :
    K1_14_2_2.RowCaps (H^k) (timesShape k hs) := by
  open K1_14_2_2_2_1 in
    obtain ⟨hb,hj,hu⟩ := (rowCaps_iff H hs).mp cap
    apply (rowCaps_iff ..).mpr
    have b : jetDegree (H^k)=k*jetDegree H := P1_7_4_1.factorDegree_pow hn k 0
    have u : seedDegree (H^k)=k*seedDegree H := P1_7_4_1.factorDegree_pow hn k 2
    rw [b,u,natDegree_pow]
    exact ⟨Nat.mul_le_mul_left k hb,Nat.mul_le_mul_left k hj,Nat.mul_le_mul_left k hu⟩
theorem prepare {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    (nonzero : ∃ H∈V,H≠0) (vcaps : ∀ H∈V,K1_14_2_2.RowCaps H hs)
    (unique : ∀ G H,Common V G → Common V H → IsRelPrime G H → False) :
    Nonempty (Prepared P s ks V hs) := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have select (G : Jet) (kind : G=1 ∨ Common V G) (F : ι→Jet)
      (fac : ∀ i,∃ n : ℕ,P i=G^n*F i) (none : ∀ i Q,Common V Q → ¬ Q∣F i) :
      Nonempty (Prepared P s ks V hs) := by
    have nf (i) : F i≠0 := by
      obtain ⟨n,e⟩ := fac i
      exact right_ne_zero_of_mul (e ▸ proper i)
    obtain ⟨H,mem,nh,avoid⟩ := one_helper F ks V nonzero nf (by
      intro i Q irr div pos useed
      by_contra! all
      exact none i Q ⟨irr,pos,useed,all⟩ div)
    refine ⟨⟨G,kind,F,H,mem,nh,nf,fac,?_,fun i=>power_caps nh (vcaps H mem) _,avoid,?_⟩⟩
    · intro i
      obtain ⟨n,e⟩ := fac i
      exact divisor_caps (proper i) (caps i) (dvd_trans (dvd_mul_left (F i) (G^n)) (dvd_of_eq e.symm))
    · intro i J prime regular r a fit hp hc
      obtain ⟨n,e⟩ := fac i
      rw [e] at hp
      have unit : toJet (G^n)∉J := by
        rw [map_pow]
        exact fun bad => regular (prime.mem_of_pow_mem _ bad)
      exact ⟨native_strip prime r unit hp,native_power (hc H mem) fit⟩
  by_cases ex : ∃ G,Common V G
  · obtain ⟨G,g⟩ := ex
    choose F eq avoid using fun i => (FiniteMultiplicity.of_prime_left g.1.prime (proper i)).exists_eq_pow_mul_and_not_dvd
    apply select G (Or.inr g) F (fun i=>⟨_,eq i⟩)
    intro i Q q div
    by_cases same : G∣Q
    · exact avoid i (same.trans div)
    · exact unique G Q g q (g.1.isRelPrime_iff_not_dvd.mpr same)
  · apply select 1 (Or.inl rfl) P (fun i=>⟨0,by simp⟩)
    exact fun _ Q q _ => ex ⟨Q,q⟩
end Lower6960.PrefixRows

end
end Merged_R6960PrefixRows

-- merged module R6960PrefixReceipt
section Merged_R6960PrefixReceipt
noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1_14 (Shape Jet L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (jetMarkHom toJet)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Lower6960.HelperSource
open Lower6960.DifferentialContact (Native)
def rescueDegrees (G : Jet) : Prop :=
  G.natDegree=1 ∧
    ((jetDegree G=1 ∧ seedDegree G=1) ∨
     (jetDegree G=1 ∧ 2≤seedDegree G ∧ seedDegree G≤6) ∨
     (jetDegree G=1 ∧ 7≤seedDegree G ∧ seedDegree G≤85) ∨
     (2≤jetDegree G ∧ jetDegree G≤7 ∧ 1≤seedDegree G ∧ seedDegree G≤78))
theorem prepare_6960 {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2359≤h) (hi : h≤33579) :
    let V := evaluated Crt word helperBank.shape (helperCutoff h)
    ∃ out : Prepared P s ks V helperBank.shape, out.exception=1 ∨ rescueDegrees out.exception := by
  obtain ⟨out⟩ := prepare P s ks _ helperBank.shape proper caps
    (helper_nonzero Crt word lo hi) (fun _ inside=>evaluated_shape Crt word inside)
    (fun _ _ g i cop=>helper_not_two Crt word lo hi g.1 i.1 cop g.2.1 i.2.1 g.2.2.1
      i.2.2.1 g.2.2.2 i.2.2.2)
  refine ⟨out,out.kind.imp_right ?_⟩
  intro g
  obtain ⟨slope,b0,b1,u0,u1,mixed⟩ :=
    helper_common_caps Crt word lo hi g.1 g.2.2.1 g.2.1 g.2.2.2
  unfold rescueDegrees
  omega
theorem native_at_6960 {ι : Type*} {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2359≤h) (hi : h≤33579) {P : ι→Jet} {s : ι→Shape} {ks : ι→ℕ}
    (out : Prepared P s ks (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape)
    (i : ι) (W r : ℕ) (inside : P i∈evaluated Crt word (s i) W)
    (width : W+2*h*r<(s i).m*179818) (power : r+1≤ks i*11)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K1.K) (S : (Polynomial K1.K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset K1.I) (many : 179818≤hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i)
    (regular : toJet out.exception∉RingHom.ker (jetMarkHom z S)) :
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.helper^(ks i)) := by
  apply out.contacts i _ (RingHom.ker_isPrime _) regular (r+1) 11 power
  · exact contact_of_crt Crt word (s i) _ inside width noPole z S residues degree hits many agree
  · intro H member
    have wh := helper_width lo hi
    unfold WidthGuard cutoffCount at wh
    have fit : helperCutoff h + 2*h*10 < helperBank.shape.m*179818 := by
      unfold helperCutoff cutoffCount
      omega
    exact contact_of_crt Crt word helperBank.shape H member fit noPole z S residues degree hits many agree
end Lower6960.PrefixRows

end
end Merged_R6960PrefixReceipt

end Merged_R6960PrefixReceipt
