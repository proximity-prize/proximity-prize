import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import ProximityPrize.SubmissionLower.Fast023
set_option autoImplicit true
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
structure Stage where
  reserve : ℕ
  cheap : Shape
  layered : Shape
def stages : List Stage :=
  [⟨0, ⟨59,82,18,1899⟩, ⟨136,190,40,8441⟩⟩,
   ⟨1, ⟨66,92,21,2076⟩, ⟨150,210,44,9356⟩⟩,
   ⟨2, ⟨73,102,23,2261⟩, ⟨164,229,48,10272⟩⟩,
   ⟨3, ⟨80,112,25,2455⟩, ⟨178,249,52,11191⟩⟩,
   ⟨5, ⟨94,131,30,2824⟩, ⟨213,298,62,12959⟩⟩,
   ⟨8, ⟨115,160,36,3401⟩, ⟨262,366,77,15611⟩⟩,
   ⟨12, ⟨136,190,43,4204⟩, ⟨325,454,96,19187⟩⟩,
   ⟨18, ⟨178,248,56,5332⟩, ⟨409,572,121,24615⟩⟩,
   ⟨28, ⟨241,336,78,7235⟩, ⟨570,797,169,33523⟩⟩,
   ⟨42, ⟨325,453,104,9976⟩, ⟨759,1061,224,46271⟩⟩]
def full : Shape := ⟨836,1164,247,273617⟩
def shapes : List Shape := full :: stages.flatMap (fun s => [s.cheap, s.layered])
def bufferedAt (w : ℤ) (r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 1 - 2 * w.toNat * r
def UsesSeed (G : Jet) : Prop :=
  ∃ j i, 0 < ((G.coeff j).coeff i).totalDegree
def BufferedPairs (w : ℤ) (rows : Banks) : Prop :=
  ∀ s ∈ stages,
    ∃ P ∈ rows s.cheap (bufferedAt w s.reserve s.cheap),
    ∃ Q ∈ rows s.layered (bufferedAt w s.reserve s.layered),
      P ≠ 0 ∧ Q ≠ 0 ∧
        ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G → ¬ G ∣ Q
abbrev ODE := Polynomial (Polynomial FX)
def fixedAt (G : ODE) (S : K[X]) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def FixedEquation {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) (B J : ℕ) : Prop :=
  ∃ G : ODE, G ≠ 0 ∧ G.natDegree ≤ J ∧
    (∀ j i, ((G.coeff j).coeff i) ≠ 0 → i+j ≤ B) ∧
    ∀ γ ∈ T, fixedAt G (F.scalar γ) = 0
def fixedKeys : List (ℕ × ℕ) := (507836, 93976) :: shapes.map (fun s => (s.B, s.J))
def endpointDegree : ℕ := 134625
def fixedPrice (B J : ℕ) : ℕ :=
  let d := endpointDegree
  let t := 2*d-3
  let a := 1+t*(B-1)
  let v := min a (t*(J-1)+d)
  let gap := 180265-d
  (81879*((B-J)*v+J*a)+gap-1)/gap+B^2
def fixedTotal : ℕ := (fixedKeys.map fun k => fixedPrice k.1 k.2).sum
def directPrice : ℕ :=
  5980 + ((p+1)*1052972+19635660) + (p+1)*(shapes.map Shape.U).sum + 310966947964
def lossSeedCap : ℕ := 220891211
def lossYCap : ℕ := 4783514411
def movingPrice : ℕ := 86954269798767161
abbrev Ambient := MvPolynomial (Fin 4) FX
abbrev RootAmbient := MvPolynomial (Fin 3) FX
def rootSeeds : Seeds →+* RootAmbient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3))).toRingHom
def rootIncl : RootAmbient →+* Ambient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))).toRingHom
def toRoot : Equation →+* RootAmbient := eval₂RingHom rootSeeds (MvPolynomial.X 2)
def toJet : Jet →+* Ambient := eval₂RingHom (rootIncl.comp toRoot) (MvPolynomial.X 3)
def rootMarkHom (z : K) (S : K[X]) : RootAmbient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S]
def jetMarkHom (z : K) (S : K[X]) : Ambient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S, atX S.derivative]
theorem eval_root (a b y : FX) (f : Equation) :
    MvPolynomial.eval ![a,b,y] (toRoot f) = f.eval₂ (MvPolynomial.eval ![a,b]) y := by
  have hseed : (MvPolynomial.eval ![a,b,y]).comp rootSeeds = MvPolynomial.eval ![a,b] := by
    apply RingHom.ext
    intro g
    change MvPolynomial.eval ![a,b,y] (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) g) = _
    rw [MvPolynomial.eval_rename]
    have hvec : ![a,b,y] ∘ Fin.castLE (by decide : 2 ≤ 3) = ![a,b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
  change MvPolynomial.eval ![a,b,y] (f.eval₂ rootSeeds (MvPolynomial.X 2)) = _
  rw [Polynomial.hom_eval₂, hseed, MvPolynomial.eval_X]
  rfl
private theorem eval_incl (a b y v : FX) (f : RootAmbient) :
    MvPolynomial.eval ![a,b,y,v] (rootIncl f) = MvPolynomial.eval ![a,b,y] f := by
  change MvPolynomial.eval ![a,b,y,v] (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4)) f) = _
  rw [MvPolynomial.eval_rename]
  have hvec : ![a,b,y,v] ∘ Fin.castLE (by decide : 3 ≤ 4) = ![a,b,y] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
theorem eval_rootIncl_toRoot (z : K) (S : K[X]) (f : Equation) :
    jetMarkHom z S (rootIncl (toRoot f)) = atMark f z S :=
  (eval_incl (seedEmbedding z) _ _ _ (toRoot f)).trans (eval_root (seedEmbedding z) _ _ f)
theorem eval_toJet (z : K) (S : K[X]) (P : Jet) :
    jetMarkHom z S (toJet P) = jetAt P z S := by
  have h : (jetMarkHom z S).comp (rootIncl.comp toRoot) =
      eval₂RingHom (graphEval z) (atX S) := by
    exact RingHom.ext (eval_rootIncl_toRoot z S)
  have hv : jetMarkHom z S (MvPolynomial.X 3) = atX S.derivative := by
    simp [jetMarkHom]
  change jetMarkHom z S (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3)) = _
  rw [Polynomial.hom_eval₂, h, hv]
  rfl
def OnJet (I : Ideal Ambient) (z : K) (S : K[X]) : Prop :=
  I ≤ RingHom.ker (jetMarkHom z S)
def OnRoot (I : Ideal RootAmbient) (z : K) (S : K[X]) : Prop :=
  I ≤ RingHom.ker (rootMarkHom z S)
abbrev SeedField := FractionRing Seeds
def generic (i : Fin 2) : SeedField :=
  algebraMap Seeds SeedField (MvPolynomial.X i)
def seedLine {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i + MvPolynomial.C (generic 0) * MvPolynomial.X j -
    MvPolynomial.C (generic 1)
def ySection {n : ℕ} (i : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i - MvPolynomial.C (generic 1)
abbrev CoordinateRing {R : Type} [CommRing R] (I : Ideal R) := R ⧸ I
abbrev JetSeedSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev JetYSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
abbrev RootSeedSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev RootYSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
def LossCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) : Prop :=
  ∃ cs : Finset (Ideal Ambient),
    (∀ I ∈ cs, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
      Module.Finite SeedField (JetSeedSection I) ∧
      0 < Module.finrank SeedField (JetSeedSection I) ∧
      Module.Finite SeedField (JetYSection I)) ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetSeedSection I)) ≤ lossSeedCap ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetYSection I)) ≤ lossYCap ∧
    ∀ γ ∈ T, ∃ I ∈ cs, OnJet I (M.label γ) (F.scalar γ)
def SmallRootCurve (I : Ideal RootAmbient) (g H : ℕ) : Prop :=
  I.IsPrime ∧
    ∃ C₀ : MvPolynomial (Fin 2) L, Irreducible C₀ ∧
      I.comap rootSeeds =
        Ideal.span {MvPolynomial.map
          ((algebraMap L[X] FX).comp (Polynomial.C : L →+* L[X])) C₀} ∧
      Module.Finite SeedField (RootSeedSection I) ∧
      Module.finrank SeedField (RootSeedSection I) = C₀.totalDegree * g ∧
      Module.Finite SeedField (RootYSection I) ∧
      Module.finrank SeedField (RootYSection I) ≤ H
def rootPrice (g H : ℕ) : ℚ :=
  let t : ℚ := 2 * (g : ℚ) - 1
  (t + (11697/6520 : ℚ) * (((2 * endpointDegree - 1 : ℕ) : ℚ)*t+1)) * H + g
def RootTariff : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    M.overhead ≤ 3554 → ∀ T ⊆ Γ, ∀ I g H, 0 < g → g ≤ 8 →
    SmallRootCurve I g H →
    (∀ γ ∈ T, OnRoot I (M.label γ) (F.scalar γ)) →
    (T.card : ℚ) ≤ rootPrice g H
abbrev FibreRing := MvPolynomial (Fin 2) SeedField
def mapGenericSeed : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.C (generic 0), MvPolynomial.C (generic 1), MvPolynomial.X 0, MvPolynomial.X 1]
abbrev OverSeeds (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericSeed)
def mapGenericJets : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (generic 0), MvPolynomial.C (generic 1)]
abbrev OverJets (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericJets)
structure RetainedParents (rows : Banks) where
  ideals : Finset (Ideal Ambient)
  prime : ∀ I ∈ ideals, I.IsPrime
  seed_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverSeeds I)
  seed_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  jet_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverJets I)
  jet_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverJets I) ∧
    Module.finrank SeedField (OverJets I) < p
  terminal : ∀ I ∈ ideals, ∀ P ∈ rows full (full.m * 180265 - 1), toJet P ∈ I
def FullDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < full.m * 180265, ∀ P ∈ rows full W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff
def ProjectedProduct (w : ℤ) (rows : Banks) (parents : RetainedParents rows)
    (f : Equation) : Prop :=
  0 < f.natDegree ∧ f.IsPrimitive ∧
    (f.map (algebraMap Seeds SeedField)).Separable ∧
    (∀ I ∈ parents.ideals, rootIncl (toRoot f) ∈ I) ∧
    FullDivisibility w rows f ∧ TerminalDivisibility w rows f
structure Geometry {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) where
  direct : Finset K
  lost : Finset K
  kept : Finset K
  fixedGroups : (ℕ × ℕ) → Finset K
  parents : RetainedParents rows
  direct_card : direct.card ≤ directPrice
  fixed_eq : ∀ k ∈ fixedKeys, fixedGroups k ⊆ Γ ∧ FixedEquation F (fixedGroups k) k.1 k.2
  lost_subset : lost ⊆ Γ
  loss_cover : LossCover M F lost
  kept_subset : kept ⊆ Γ
  kept_cover : ∀ γ ∈ kept, ∃ I ∈ parents.ideals, OnJet I (M.label γ) (F.scalar γ)
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ (∃ k ∈ fixedKeys, γ ∈ fixedGroups k) ∨ γ ∈ lost ∨ γ ∈ kept
end
end K1_14_2
end
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → BufferedPairs M.overhead rows
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → BufferedPairs M.overhead rows →
    Nonempty (Geometry M F rows)
def c3 : Prop :=
  RootTariff →
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    M.overhead ≤ 3554 → ∀ T ⊆ Γ, LossCover M F T → T.card ≤ movingPrice
def c4 : Prop := RootTariff
def c5 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    M.overhead ≤ 3554 → ∀ T ⊆ Γ, ∀ B J, (B,J) ∈ fixedKeys →
    FixedEquation F T B J → T.card ≤ fixedPrice B J
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → ∀ parents : RetainedParents rows,
    parents.ideals.Nonempty → ∃ f : Equation, ProjectedProduct M.overhead rows parents f
def c7 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → ∀ f : Equation, f ≠ 0 →
    FullDivisibility M.overhead rows f → f.natDegree ≤ 5
def unionOf (groups : (ℕ × ℕ) → Finset K) (keys : List (ℕ × ℕ)) : Finset K := by
  classical
  exact keys.foldr (fun k acc => groups k ∪ acc) ∅
theorem mem_unionOf (groups : (ℕ × ℕ) → Finset K)
    {keys : List (ℕ × ℕ)} {k : ℕ × ℕ} {γ : K}
    (hk : k ∈ keys) (hγ : γ ∈ groups k) : γ ∈ unionOf groups keys := by
  classical
  induction keys with
  | nil => simp at hk
  | cons a keys ih =>
    simp only [List.mem_cons] at hk
    change γ ∈ groups a ∪ unionOf groups keys
    rcases hk with rfl | hk
    · exact Finset.mem_union_left _ hγ
    · exact Finset.mem_union_right _ (ih hk)
theorem card_unionOf_le (groups : (ℕ × ℕ) → Finset K)
    (keys : List (ℕ × ℕ)) (h : ∀ k ∈ keys, (groups k).card ≤ fixedPrice k.1 k.2) :
    (unionOf groups keys).card ≤ (keys.map fun k => fixedPrice k.1 k.2).sum := by
  classical
  induction keys with
  | nil => simp [unionOf]
  | cons k keys ih =>
    change (groups k ∪ unionOf groups keys).card ≤
      fixedPrice k.1 k.2 + (keys.map fun k => fixedPrice k.1 k.2).sum
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (h k (List.mem_cons_self ..))
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha))))
set_option maxRecDepth 12000 in
private theorem ledger (w : ℤ) (hw : w ≤ 3554) :
    directPrice + fixedTotal + movingPrice ≤ highPrefix w := by
  have he : highPrefix w = 132117856182247703 := by simp [highPrefix, hw]
  rw [he]
  decide +kernel
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6)
    (h7 : c7) : K1_14.c2 := by
  classical
  intro u del M Γ F hlo hhi H hH rows hrows
  obtain ⟨g⟩ := h2 u del M Γ F hlo hhi rows hrows (h1 u del M Γ F hlo hhi rows hrows)
  let fixed := unionOf g.fixedGroups fixedKeys
  have hfixed : fixed.card ≤ fixedTotal := by
    apply card_unionOf_le
    rintro ⟨B, J⟩ hk
    obtain ⟨hsub, hG⟩ := g.fixed_eq (B,J) hk
    exact h5 u del M Γ F hhi _ hsub B J hk hG
  have hlost := h3 h4 u del M Γ F hhi g.lost g.lost_subset g.loss_cover
  have hsubset : Γ \ g.kept ⊆ (g.direct ∪ fixed) ∪ g.lost := by
    intro γ hγ
    obtain ⟨hΓ, hnot⟩ := Finset.mem_sdiff.mp hγ
    rcases g.cover γ hΓ with hd | ⟨k, hk, hf⟩ | hl | hs
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_unionOf _ hk hf))
    · exact Finset.mem_union_right _ hl
    · exact (hnot hs).elim
  have hprefix : (Γ \ g.kept).card ≤ highPrefix M.overhead := by
    calc
      _ ≤ ((g.direct ∪ fixed) ∪ g.lost).card := Finset.card_le_card hsubset
      _ ≤ g.direct.card + fixed.card + g.lost.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ directPrice + fixedTotal + movingPrice :=
        Nat.add_le_add (Nat.add_le_add g.direct_card hfixed) hlost
      _ ≤ _ := ledger M.overhead hhi
  by_cases he : g.kept = ∅
  · exact Or.inl (by simpa [he] using hprefix)
  have hparents : g.parents.ideals.Nonempty := by
    obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨I, hI, _⟩ := g.kept_cover γ hγ
    exact ⟨I, hI⟩
  obtain ⟨f, hpos, hprim, hsep, hmem, hfull, hterm⟩ :=
    h6 u del M Γ F hlo hhi rows hrows g.parents hparents
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hpos
  have hdeg := h7 u del M Γ F hlo hhi rows hrows f hf hfull
  refine Or.inr ⟨g.kept, g.kept_subset, hprefix, f, ⟨hpos, ?_, hprim, hsep⟩, hterm, ?_⟩
  · simpa [band, hhi] using hdeg
  · intro γ hγ
    obtain ⟨I, hi, hI⟩ := g.kept_cover γ hγ
    have hz := RingHom.mem_ker.mp (hI (hmem I hi))
    simpa only [eval_rootIncl_toRoot] using hz
end
end K1_14_2
end
section
namespace K1_14_2_1
open K1_14 K1_14_2
def RowCaps (s : Shape) (P : Jet) : Prop :=
  ∀ j i, ((P.coeff j).coeff i) ≠ 0 →
    i + j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
def rawVolume (h r : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (rawWidth h r s)
def movingCeiling (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (fun _ j => 2 * h * j)
end K1_14_2_1
end
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1_14 K1_14_2 Polynomial UniqueFactorizationMonoid
def divisible (V : Submodule FX Jet) (G : Jet) : Submodule FX V where
  carrier := {Q | G ∣ (Q : Jet)}
  zero_mem' := dvd_zero G
  add_mem' := fun hP hQ => dvd_add hP hQ
  smul_mem' a := by
    rintro Q ⟨R, hR⟩
    exact ⟨a • R, by
      change a • (Q : Jet) = G * (a • R)
      rw [hR, mul_smul_comm]⟩
theorem exists_layered (P : Jet) (hP : P ≠ 0) (V : Submodule FX Jet)
    (hn : ∃ Q ∈ V, Q ≠ 0)
    (hproper : ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G →
      ∃ Q ∈ V, ¬ G ∣ Q) :
    ∃ Q ∈ V, Q ≠ 0 ∧
      ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G → ¬ G ∣ Q := by
  classical
  let : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
  let I := {H : Jet // H ∈ factors P}
  let : Finite I := Set.finite_coe_iff.mpr (factors P).finite_toSet
  let tests : Option I → Submodule FX V := fun k =>
    match k with
    | none => ⊥
    | some H =>
      if ∃ G : Jet, Irreducible G ∧ G ∣ P ∧ 0 < G.natDegree ∧ UsesSeed G ∧
          Associated G H.val then divisible V H.val else ⊥
  have bot_proper : (⊥ : Submodule FX V) ≠ ⊤ := by
    obtain ⟨Q, hQ, hnQ⟩ := hn
    intro heq
    have hmem : (⟨Q, hQ⟩ : V) ∈ (⊥ : Submodule FX V) := heq ▸ Submodule.mem_top
    exact hnQ (congrArg Subtype.val ((Submodule.mem_bot FX).mp hmem))
  have ht : ∀ k, tests k ≠ ⊤ := by
    intro k
    cases k with
    | none => exact bot_proper
    | some H =>
      change (if _ then divisible V H.val else ⊥) ≠ ⊤
      split_ifs with h
      · obtain ⟨G, hi, hd, hv, hs, ha⟩ := h
        obtain ⟨Q, hQ, hnQ⟩ := hproper G hi hd hv hs
        intro heq
        have hmem : (⟨Q, hQ⟩ : V) ∈ divisible V H.val := heq ▸ Submodule.mem_top
        exact hnQ (ha.dvd.trans (show H.val ∣ Q from hmem))
      · exact bot_proper
  obtain ⟨Q, hQ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (K := FX) (M := V) tests ht
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · intro hz
    exact hQ none ((Submodule.mem_bot FX).mpr (Subtype.ext hz))
  · intro G hi hd hv hs hdiv
    obtain ⟨H, hH, ha⟩ := exists_mem_factors_of_dvd hP hi hd
    let k : I := ⟨H, hH⟩
    apply hQ (some k)
    change Q ∈ (if _ then divisible V H else ⊥)
    rw [ite_eq_left ⟨G, hi, hd, hv, hs, ha⟩]
    exact ha.symm.dvd.trans hdiv
end
end K1_14_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
abbrev JetPlane := Polynomial (Polynomial FX)
abbrev Surface := PrimeSpectrum Jet
def fixedEmbedding : JetPlane →+* Jet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom MvPolynomial.C)
def fixedAt (G : JetPlane) (S : K[X]) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def JetCaps {R : Type*} [Semiring R] (G : Polynomial (Polynomial R)) (b j : ℕ) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 → y + v ≤ b ∧ v ≤ j
def RowCaps (G : Jet) (s : Shape) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 →
    y + v ≤ s.B ∧ v ≤ s.J ∧ ((G.coeff v).coeff y).totalDegree ≤ s.U
def cheapShape (i : Fin 4) : Shape :=
  ![⟨45,63,14,812⟩, ⟨57,80,18,1041⟩, ⟨81,114,26,1383⟩, ⟨123,173,40,2173⟩] i
def layeredShape (i : Fin 4) : Shape :=
  ![⟨84,118,24,2907⟩, ⟨114,160,33,3775⟩, ⟨144,203,42,5064⟩, ⟨231,325,67,8061⟩] i
def reserve (i : Fin 4) : ℕ := ![0,2,5,12] i
def fullShape : Shape := ⟨358,500,105,66251⟩
def reserveCutoff (h : ℕ) (s : Shape) (i : Fin 4) : ℕ :=
  s.m * 180265 - 1 - 2*h*reserve i
def contactPower (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (s.m * 180265 - 1 - W) / (2*h)
def SeedShift (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, ∀ i r, seedHasse i r P ∈ rows s (W + 2*h*r)
def LeadingFilter (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree
def RankFloor (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W < s.m*180265,
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-h) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-h)) ≤
      sourceDebit h s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)
def NoMovingCommon (P Q : Jet) : Prop :=
  ∀ D : Jet, Irreducible D → D ∣ P → D ∣ Q → 0 < D.natDegree →
    D ∈ Set.range fixedEmbedding
structure BufferedPair (h : ℕ) (rows : Banks) (i : Fin 4) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (cheapShape i) (reserveCutoff h (cheapShape i) i)
  layered_mem : layered ∈ rows (layeredShape i) (reserveCutoff h (layeredShape i) i)
  cheap_caps : RowCaps cheap (cheapShape i)
  layered_caps : RowCaps layered (layeredShape i)
  no_moving : NoMovingCommon cheap layered
abbrev SeedField := FractionRing Seeds
abbrev SeedClosure := AlgebraicClosure SeedField
abbrev JetField := FractionRing JetPlane
abbrev JetClosure := AlgebraicClosure JetField
abbrev FibreJet := Polynomial (Polynomial SeedClosure)
def seedGeneric : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def jetGeneric : JetPlane →+* JetClosure :=
  let first : JetPlane →+* JetField := algebraMap JetPlane JetField
  let second : JetField →+* JetClosure := algebraMap JetField JetClosure
  second.comp first
def seedFibreEval (y v : SeedClosure) : Jet →+* SeedClosure :=
  eval₂RingHom (eval₂RingHom seedGeneric y) v
def OnSeedFibre (q : Surface) (y v : SeedClosure) : Prop :=
  RingHom.ker (seedFibreEval y v) = q.asIdeal
structure Parent (q : Surface) : Prop where
  height_two : q.asIdeal.height = 2
  seed_side : ∃ y v, OnSeedFibre q y v ∧ IsSeparable SeedField y ∧ IsSeparable SeedField v
  jet_side : ∃ g : Jet →+* JetClosure,
    g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = q.asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i))))
def fibreRow (P : Jet) : FibreJet := P.map (Polynomial.mapRingHom seedGeneric)
def fibrePoint (y v : SeedClosure) : Ideal FibreJet :=
  Ideal.span {C (R := Polynomial SeedClosure) (Polynomial.X (R := SeedClosure) - C y),
    Polynomial.X (R := Polynomial SeedClosure) - C (C v)}
def OrderAt (q : Surface) (P : Jet) (m : ℕ) : Prop :=
  ∀ y v, OnSeedFibre q y v → fibreRow P ∈ fibrePoint y v ^ m
def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (s.m*180265 - 1), P ∈ q.asIdeal
abbrev ClearedSeeds := MvPolynomial (Fin 2) L[X]
abbrev ClearedEquation := Polynomial ClearedSeeds
def liftEquation : ClearedEquation →+* Equation :=
  Polynomial.mapRingHom (MvPolynomial.map (algebraMap L[X] FX))
def clearedDx (g : ClearedEquation) : ClearedEquation :=
  g.sum fun j a => monomial j (∑ e ∈ MvPolynomial.support a, MvPolynomial.monomial e (AddMonoidAlgebra.coeff a e).derivative)
def ordinaryCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) + X * C (liftEquation g.derivative)
def IsClearing (f : Equation) (g : ClearedEquation) (a : L[X]) : Prop :=
  a ≠ 0 ∧ liftEquation g = C (MvPolynomial.C (algebraMap L[X] FX a)) * f
def Compatible (P Q : Jet) (q : Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    C f ∈ q.asIdeal → ∀ g a, IsClearing f g a → ordinaryCutter g ∈ q.asIdeal
def PassStage {h : ℕ} (rows : Banks) (pairs : ∀ i : Fin 4, BufferedPair h rows i)
    (i : Fin 5) (q : Surface) : Prop :=
  if hi : i.val < 4 then
    let j : Fin 4 := ⟨i.val, hi⟩
    BankVanishes rows (cheapShape j) q ∧ BankVanishes rows (layeredShape j) q ∧
      Compatible (pairs j).cheap (pairs j).layered q
  else BankVanishes rows fullShape q
def cutShape (i : Fin 5) : Shape :=
  if hi : i.val < 4 then layeredShape ⟨i.val, hi⟩ else fullShape
inductive Slice where
  | seed | ordinate | mixed | jets
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionSeeds := MvPolynomial (Fin 2) SectionField
abbrev SectionJet := Polynomial (Polynomial SectionSeeds)
def sectionMap : Jet →+* SectionJet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom
    (MvPolynomial.map (algebraMap FX SectionField)))
def sectionScalar (i : Fin 4) : SectionJet :=
  C (C (MvPolynomial.C (algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i))))
def sectionEquations (slice : Slice) : Set SectionJet :=
  let t₀ : SectionJet := C (C (MvPolynomial.X 0))
  let t₁ : SectionJet := C (C (MvPolynomial.X 1))
  let y : SectionJet := C (R := Polynomial SectionSeeds) (Polynomial.X (R := SectionSeeds))
  let v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
  let seedLine := t₀ + sectionScalar 0 * t₁
  let jetLine := y + sectionScalar 1 * v
  let a := sectionScalar 2
  let b := sectionScalar 3
  match slice with
  | .seed => {t₀ - a, t₁ - b}
  | .ordinate => {seedLine - a, y - b}
  | .mixed => {seedLine - a, jetLine - b}
  | .jets => {y - a, v - b}
def sectionDegree (q : Surface) (slice : Slice) : ℕ :=
  let J := q.asIdeal.map sectionMap ⊔ Ideal.span (sectionEquations slice)
  Module.finrank SectionField (SectionJet ⧸ J)
def mass (qs : Finset Surface) (s : Slice) : ℚ :=
  ∑ q ∈ qs, (sectionDegree q s : ℚ)
structure MassCap (qs : Finset Surface) (a c z : ℚ) : Prop where
  seed : mass qs .seed ≤ a
  ordinate : mass qs .ordinate ≤ c
  mixed : mass qs .mixed ≤ z
def seedMassCap (i : Fin 4) : ℚ :=
  ![2891,1882/3,6539/18,34367/144] i
def ordinateMassCap (i : Fin 4) : ℚ :=
  ![60998,12408,39923/6,624487/144] i
def mixedMassCap (i : Fin 4) : ℚ :=
  ![381269,158780,1418621/16,15468365/288] i
def cutDegree (s : Shape) (qs : Finset Surface) : ℚ :=
  (s.U : ℚ) * mass qs .seed + ((s.B - s.J : ℕ) : ℚ) * mass qs .ordinate +
    (s.J : ℚ) * mass qs .mixed
def constantDegree (s : Shape) (qs : Finset Surface) : ℚ :=
  (s.U : ℚ) * mass qs .mixed + (s.B : ℚ) * mass qs .jets
structure SeedCover where
  curve : Seeds
  curve_ne : curve ≠ 0
  points : Finset (FX × FX)
def SeedCover.Covers (C : SeedCover) (z : K) : Prop :=
  graphEval z C.curve = 0 ∨ (seedEmbedding z, seedEmbedding z ^ p) ∈ C.points
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  masses : MassCap parents 2891 60998 381269
  jetMass : mass parents .jets ≤ 3019828
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 381269 + 812 + 2907
  seedPoints : seeds.points.card ≤ 3019828
  ordinates : Finset FX
  ordinateCount : ordinates.card ≤ 2891
  lowJet : JetPlane
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  lowJet_caps : JetCaps lowJet 381269 60998
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cover : ∀ γ ∈ Γ,
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    fixedAt lowJet (F.scalar γ) = 0 ∨ fixedAt fixedCheap (F.scalar γ) = 0 ∨
    fixedAt fixedLayered (F.scalar γ) = 0 ∨ ∃ q ∈ parents, MarkOn M F q γ
def odePrice (d b j : ℕ) : ℕ :=
  let T := 2*d - 3
  let a := 1 + T*(b-1)
  let v := min a (T*(j-1)+d)
  let gap := 180265-d
  ((262144-d)*((b-j)*v+j*a) + (gap-1))/gap + b*(b-1)+b
structure ProjectedProduct (qs : Finset Surface) (f : Equation) : Prop where
  positive : 0 < f.natDegree
  primitive : f.IsPrimitive
  separable : (f.map (algebraMap Seeds SeedField)).Separable
  vanishes : ∀ q ∈ qs, C f ∈ q.asIdeal
  divides_leading : ∀ (P : Jet) (k : ℕ), P ≠ 0 →
    (∀ q ∈ qs, OrderAt q P k) → f ^ (k - P.natDegree) ∣ P.leadingCoeff
end
end K1_14_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def stageAt (i : Fin 10) : Stage :=
  stages.get ⟨i.val, by simp [stages]⟩
def stagePair (i : Fin 10) : List Shape :=
  [(stageAt i).cheap, (stageAt i).layered]
def key (s : Shape) : ℕ × ℕ := (s.B, s.J)
def fullCutoff (s : Shape) : ℕ := s.m * 180265 - 1
def RowCaps (P : Jet) (s : Shape) : Prop :=
  ∀ j i, (P.coeff j).coeff i ≠ 0 →
    i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
def ODECaps (G : ODE) (B J : ℕ) : Prop :=
  G ≠ 0 ∧ G.natDegree ≤ J ∧ ∀ j i, (G.coeff j).coeff i ≠ 0 → i+j ≤ B
structure RowPair (w : ℤ) (rows : Banks) (i : Fin 10) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (stageAt i).cheap (bufferedAt w (stageAt i).reserve (stageAt i).cheap)
  layered_mem : layered ∈ rows (stageAt i).layered (bufferedAt w (stageAt i).reserve (stageAt i).layered)
  cheap_caps : RowCaps cheap (stageAt i).cheap
  layered_caps : RowCaps layered (stageAt i).layered
  no_moving : ∀ G : Jet, Irreducible G → G ∣ cheap → 0 < G.natDegree →
    UsesSeed G → ¬ G ∣ layered
def fixedIncl : ODE →+* Jet := K1_14_3.fixedEmbedding
structure FixedPart (P : Jet) (s : Shape) where
  equation : ODE
  equation_caps : ODECaps equation s.B s.J
  residual : Jet
  factorization : P = fixedIncl equation * residual
  stripped : ∀ G : ODE, Irreducible (fixedIncl G) → ¬ fixedIncl G ∣ residual
structure FixedPair {w rows i} (B : RowPair w rows i) where
  cheap : FixedPart B.cheap (stageAt i).cheap
  layered : FixedPart B.layered (stageAt i).layered
def bankVanishes (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), toJet P ∈ I
def compatible (P Q : Jet) (I : Ideal Ambient) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    rootIncl (toRoot f) ∈ I →
    ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3.ordinaryCutter g) ∈ I
def pairTest {w rows i} (B : RowPair w rows i) (I : Ideal Ambient) : Prop :=
  bankVanishes rows (stageAt i).cheap I ∧ bankVanishes rows (stageAt i).layered I ∧
    compatible B.cheap B.layered I
def fixedOn (G : ODE) (I : Ideal Ambient) : Prop :=
  toJet (fixedIncl G) ∈ I
def pairGood {w rows i} {B : RowPair w rows i} (A : FixedPair B) (I : Ideal Ambient) : Prop :=
  pairTest B I ∧ ¬ fixedOn A.cheap.equation I ∧ ¬ fixedOn A.layered.equation I
def stageTest {w rows} (pairs : ∀ i : Fin 10, RowPair w rows i)
    (n : ℕ) (I : Ideal Ambient) : Prop :=
  if hn : n < 10 then pairTest (pairs ⟨n, hn⟩) I else bankVanishes rows full I
def cutShape (n : ℕ) : Shape :=
  if hn : n < 10 then (stageAt ⟨n, hn⟩).layered else full
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionAmbient := MvPolynomial (Fin 4) SectionField
def sliceParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def sectionBase : Ambient →+* SectionAmbient := MvPolynomial.map (algebraMap FX SectionField)
def sectionSeedLine : SectionAmbient :=
  MvPolynomial.X 0 + MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sliceParameter 2)
def sectionJetLine : SectionAmbient :=
  MvPolynomial.X 2 + MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 3 -
    MvPolynomial.C (sliceParameter 3)
abbrev OverOrdinate (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, MvPolynomial.X 2 -
    MvPolynomial.C (sliceParameter 3)})
abbrev OverMixed (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine})
def ordinateIncl : Polynomial FX →+* Ambient :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 2)
def jetPlaneIncl : ODE →+* Ambient := toJet.comp fixedIncl
structure Active (I : Ideal Ambient) : Prop where
  prime : I.IsPrime
  dimension : ringKrullDim (CoordinateRing I) = 2
  seed_finite : Module.Finite SeedField (OverSeeds I)
  ordinate_finite : Module.Finite SectionField (OverOrdinate I)
  mixed_finite : Module.Finite SectionField (OverMixed I)
  jet_finite : Module.Finite SeedField (OverJets I)
  seed_size : 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  mixed_lt : Module.finrank SectionField (OverMixed I) < p
  jet_lt : Module.finrank SeedField (OverJets I) < p
  ordinate_dominant : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
def dual (I : Ideal Ambient) : Prop := 0 < Module.finrank SeedField (OverJets I)
def sectionDegree (I : Ideal Ambient) : Fin 4 → ℕ :=
  ![Module.finrank SeedField (OverSeeds I), Module.finrank SectionField (OverOrdinate I),
    Module.finrank SectionField (OverMixed I), Module.finrank SeedField (OverJets I)]
def mass (S : Finset (Ideal Ambient)) (k : Fin 4) : ℕ :=
  ∑ I ∈ S, sectionDegree I k
def Fits (S : Finset (Ideal Ambient)) (cap : Fin 4 → ℕ) : Prop :=
  ∀ k, mass S k ≤ cap k
def orderOn (I : Ideal Ambient) (P : Jet) (m : ℕ) : Prop :=
  let imageIdeal := if dual I then ⊥ else (I.comap jetPlaneIncl).map jetPlaneIncl
  ∃ a : Ambient, a ∉ I ∧ a * toJet P ∈ I^m ⊔ imageIdeal
def budget (n : ℕ) : Fin 4 → ℕ :=
  match n with
  | 0 => ![5980,227898,1052972,16029459]
  | 1 => ![3767,143910,648356,4855764]
  | 2 => ![3019,114928,521837,4855764]
  | 3 => ![2687,101858,521837,3052656]
  | 4 => ![422,15662,158698,1993744]
  | 5 => ![280,10171,103959,1285200]
  | 6 => ![225,8016,68569,995828]
  | 7 => ![170,6245,54168,776610]
  | 8 => ![145,5264,47174,606347]
  | _ => ![123,4633,40170,512888]
def exitBudget (i : Fin 10) : Fin 4 → ℕ :=
  if i.val = 4 then ![2533,93976,507836,1993744] else budget i.val
def weight (s : Shape) (fee : Fin 3) : Fin 4 → ℕ :=
  ![![s.U, s.B-s.J, s.J, 0],
    ![0, s.U, 0, s.J],
    ![0,0, s.U, s.B]] fee
def dot (weight values : Fin 4 → ℕ) : ℕ := ∑ k, weight k * values k
def initialPrice : ℕ := 5980 + ((p+1)*1052972+19635660) + (p+1)*(1899+8441)
def OnParent {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop :=
  OnJet I (M.label γ) (F.scalar γ)
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (cheapFixed layeredFixed : ODE) where
  parents : Finset (Ideal Ambient)
  geometric : ∀ I ∈ parents, Active I
  initial_mass : Fits parents (budget 0)
  direct : Finset K
  direct_card : direct.card ≤ initialPrice
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ fixedAt cheapFixed (F.scalar γ) = 0 ∨
    fixedAt layeredFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent M F I γ
def CurveGeometry (I : Ideal Ambient) : Prop :=
  I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
    Module.Finite SeedField (JetSeedSection I) ∧
    0 < Module.finrank SeedField (JetSeedSection I) ∧
    Module.Finite SeedField (JetYSection I)
structure CutCover where
  direct : Finset K
  curves : Finset (Ideal Ambient)
  geometric : ∀ I ∈ curves, CurveGeometry I
def curveSeedMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetSeedSection I)
def curveYMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetYSection I)
def CutCover.cost (C : CutCover) (fee : Fin 3) : ℕ :=
  ![curveSeedMass C.curves, curveYMass C.curves, C.direct.card] fee
def CutCover.covers {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (C : CutCover) (γ : K) : Prop :=
  γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent M F I γ
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
theorem stage_mem (i : Fin 10) : stageAt i ∈ stages :=
  List.get_mem ..
theorem pair_scheduled {w : ℤ} (hw : w ≤ 3554) (i : Fin 10) {s : Shape}
    (hs : s ∈ stagePair i) : s ∈ scheduled w := by
  have he : scheduled w = stages.flatMap (fun t => [t.cheap, t.layered]) ++
      [full, terminalShape w] := by
    simp [scheduled, hw, stages, full]
  rw [he]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, stage_mem i, hs⟩)
theorem positive_m (i : Fin 10) :
    0 < (stageAt i).cheap.m ∧ 0 < (stageAt i).layered.m := by
  fin_cases i <;> decide
theorem buffer_lt (i : Fin 10) {s : Shape} (hs : s ∈ stagePair i) (w : ℤ) :
    bufferedAt w (stageAt i).reserve s < s.m * 180265 := by
  have hm : 0 < s.m := by
    simp [stagePair] at hs
    rcases hs with rfl | rfl
    · exact (positive_m i).1
    · exact (positive_m i).2
  unfold bufferedAt
  omega
theorem buffered_fits {w : ℤ} (hw : w ≤ 3554) (i : Fin 10) {s : Shape}
    (hs : s ∈ stagePair i) : 2 * w.toNat * (stageAt i).reserve ≤ fullCutoff s := by
  have hnat : w.toNat ≤ 3554 := by omega
  have hcalc (k : Fin 10) :
      2 * 3554 * (stageAt k).reserve ≤ fullCutoff (stageAt k).cheap ∧
      2 * 3554 * (stageAt k).reserve ≤ fullCutoff (stageAt k).layered := by
    fin_cases k <;> decide
  apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hnat)).trans
  simp [stagePair] at hs
  rcases hs with rfl | rfl
  · exact (hcalc i).1
  · exact (hcalc i).2
theorem eval_fixed (z : K) (S : K[X]) (G : ODE) :
    jetMarkHom z S (toJet (fixedIncl G)) = fixedAt G S := by
  rw [eval_toJet]
  change (G.map (Polynomial.mapRingHom MvPolynomial.C)).eval₂
      (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative) =
    G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
  rw [eval₂_map]
  have h : (eval₂RingHom (graphEval z) (atX S)).comp (Polynomial.mapRingHom MvPolynomial.C) =
      evalRingHom (atX S) := by
    apply RingHom.ext
    intro f
    change (f.map MvPolynomial.C).eval₂ (graphEval z) (atX S) = f.eval (atX S)
    rw [eval₂_map, ← eval₂_id]
    have hc : (graphEval z).comp MvPolynomial.C = RingHom.id FX := by
      ext c
      simp [graphEval]
    rw [hc]
  rw [h]
theorem fixed_on_mark {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (h : OnParent M F I γ) (hf : fixedOn G I) :
    fixedAt G (F.scalar γ) = 0 := by
  have hz := RingHom.mem_ker.mp (h hf)
  simpa only [eval_fixed] using hz
def price (fee : Fin 3) (n : ℕ) : Fin 4 → ℕ :=
  if n = 0 then fun _ => 0 else weight (cutShape n) fee
def jump (fee : Fin 3) (n : ℕ) (k : Fin 4) : ℕ :=
  price fee (n+1) k - price fee n k
def ledger (fee : Fin 3) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, dot (jump fee i) (budget i)
theorem price_step : ∀ (i : Fin 10) (fee : Fin 3) (k : Fin 4),
    price fee i.val k ≤ price fee (i.val+1) k := by
  decide +kernel
theorem dot_mono (w a b : Fin 4 → ℕ) (h : ∀ k, a k ≤ b k) : dot w a ≤ dot w b :=
  Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_left _ (h k))
theorem mass_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    mass S k ≤ mass T k :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
theorem dot_mass_sdiff {S T : Finset (Ideal Ambient)} (h : T ⊆ S) (w : Fin 4 → ℕ) :
    dot w (mass (S \ T)) + dot w (mass T) = dot w (mass S) := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Nat.mul_add]
  congr 1
  exact Finset.sum_sdiff h
theorem price_jump (fee : Fin 3) {n : ℕ} (hn : n < 10) (a : Fin 4 → ℕ) :
    dot (price fee (n+1)) a = dot (price fee n) a + dot (jump fee n) a := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Nat.add_mul]
  congr 1
  exact (Nat.add_sub_of_le (price_step ⟨n, hn⟩ fee k)).symm
theorem loss_ledger (S : ℕ → Finset (Ideal Ambient)) (fee : Fin 3) {n : ℕ} (hn : n ≤ 10)
    (sub : ∀ i < n, S (i+1) ⊆ S i) (hcap : ∀ i < n, Fits (S i) (budget i)) :
    (∑ i ∈ Finset.range n, dot (price fee (i+1)) (mass (S i \ S (i+1)))) +
      dot (price fee n) (mass (S n)) ≤ ledger fee n := by
  induction n with
  | zero => simp [price, dot, ledger]
  | succ n ih =>
    have hprev := ih (by omega) (fun i hi => sub i (by omega))
      (fun i hi => hcap i (by omega))
    have hdis := dot_mass_sdiff (sub n (by omega)) (price fee (n+1))
    have hj := price_jump fee (show n < 10 by omega) (mass (S n))
    have hc := dot_mono (jump fee n) _ _ (hcap n (by omega))
    unfold ledger at hprev ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega
def feeCap (fee : Fin 3) : ℕ := ![lossSeedCap, lossYCap, 310966947964] fee
theorem ledger_cap : ∀ fee : Fin 3, ledger fee 10 ≤ feeCap fee := by
  decide +kernel
theorem direct_cap : initialPrice + feeCap 2 ≤ directPrice := by
  decide +kernel
theorem sum_union_le {α : Type*} (f : α → ℕ) (A B : Finset α) :
    (∑ a ∈ A ∪ B, f a) ≤ (∑ a ∈ A, f a) + ∑ a ∈ B, f a := by
  have h := Finset.sum_union_inter (f := f) (s₁ := A) (s₂ := B)
  omega
theorem sum_biUnion_le {α β : Type*} (A : Finset α) (B : α → Finset β) (f : β → ℕ) :
    (∑ x ∈ A.biUnion B, f x) ≤ ∑ i ∈ A, ∑ x ∈ B i, f x := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le f _ _).trans (Nat.add_le_add_left ih _)
def joinCuts {α : Type*} (A : Finset α) (B : α → CutCover) : CutCover where
  direct := A.biUnion (fun i => (B i).direct)
  curves := A.biUnion (fun i => (B i).curves)
  geometric := fun I hI => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hI
    exact (B i).geometric I hi
theorem joinCuts_cost {α : Type*} (A : Finset α) (B : α → CutCover) (fee : Fin 3) :
    (joinCuts A B).cost fee ≤ ∑ i ∈ A, (B i).cost fee := by
  fin_cases fee
  · exact sum_biUnion_le _ _ _
  · exact sum_biUnion_le _ _ _
  · exact Finset.card_biUnion_le
theorem joinCuts_covers {α : Type*} {A : Finset α} {B : α → CutCover} {i : α}
    (hi : i ∈ A) {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {γ : K}
    (h : (B i).covers M F γ) : (joinCuts A B).covers M F γ := by
  rcases h with h | ⟨I, hI, hγ⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
  · exact Or.inr ⟨I, Finset.mem_biUnion.mpr ⟨i, hi, hI⟩, hγ⟩
theorem sum_dot (A : Finset (Ideal Ambient)) (w : Fin 4 → ℕ) :
    (∑ I ∈ A, dot w (sectionDegree I)) = dot w (mass A) := by
  simp only [dot, mass, Finset.mul_sum]
  exact Finset.sum_comm
def emptyCut : CutCover :=
  ⟨∅, ∅, by simp⟩
theorem combineCuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape)
    (hcut : ∀ I ∈ A, ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent M F I γ → C.covers M F γ) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent M F I γ) → C.covers M F γ := by
  let C (I : Ideal Ambient) : CutCover :=
    if hI : I ∈ A then Classical.choose (hcut I hI) else emptyCut
  have hC (I : Ideal Ambient) (hI : I ∈ A) :
      (∀ fee, (C I).cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent M F I γ → (C I).covers M F γ := by
    simpa only [C, dite_eq_left hI] using Classical.choose_spec (hcut I hI)
  refine ⟨joinCuts A C, ?_, ?_⟩
  · intro fee
    calc
      _ ≤ ∑ I ∈ A, (C I).cost fee := joinCuts_cost A C fee
      _ ≤ ∑ I ∈ A, dot (weight s fee) (sectionDegree I) :=
        Finset.sum_le_sum (fun I hI => (hC I hI).1 fee)
      _ = _ := sum_dot _ _
  · rintro γ hγ ⟨I, hI, hmark⟩
    exact joinCuts_covers hI ((hC I hI).2 γ hγ hmark)
def timeline (start : Finset (Ideal Ambient)) (stay : ℕ → Ideal Ambient → Prop) :
    ℕ → Finset (Ideal Ambient)
  | 0 => start
  | n+1 => (timeline start stay n).filter (stay (n+1))
theorem timeline_succ (start : Finset (Ideal Ambient)) (stay : ℕ → Ideal Ambient → Prop)
    (n : ℕ) : timeline start stay (n+1) ⊆ timeline start stay n :=
  Finset.filter_subset _ _
theorem timeline_antitone (start : Finset (Ideal Ambient)) (stay : ℕ → Ideal Ambient → Prop) :
    Antitone (timeline start stay) :=
  antitone_nat_of_succ_le (timeline_succ start stay)
theorem fits_mono {S T : Finset (Ideal Ambient)} {cap : Fin 4 → ℕ} (hs : S ⊆ T)
    (ht : Fits T cap) : Fits S cap :=
  fun k => (mass_mono hs k).trans (ht k)
abbrev FixedTag := Fin 2 ⊕ (Fin 10 × Bool)
def cheapTag (i : Fin 10) : FixedTag := .inr (i, false)
def layeredTag (i : Fin 10) : FixedTag := .inr (i, true)
def rankTag : FixedTag := .inl 0
def tagKey : FixedTag → ℕ × ℕ
  | .inl t => if t = 0 then (507836, 93976) else key full
  | .inr (i, b) => key (if b then (stageAt i).layered else (stageAt i).cheap)
theorem tagKey_injective : Function.Injective tagKey := by
  change ∀ a b : FixedTag, tagKey a = tagKey b → a = b
  decide +kernel
theorem tagKey_range : Finset.univ.image tagKey = fixedKeys.toFinset := by
  decide +kernel
theorem tagKey_mem (t : FixedTag) : tagKey t ∈ fixedKeys := by
  apply List.mem_toFinset.mp
  rw [← tagKey_range]
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
theorem tagKey_exists {k : ℕ × ℕ} (hk : k ∈ fixedKeys) : ∃ t, tagKey t = k := by
  have hk' := List.mem_toFinset.mpr hk
  rw [← tagKey_range] at hk'
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk'
  exact ⟨t, ht⟩
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
def ordinarySeedDegree (f : Equation) : ℕ :=
  f.support.sup fun y => (f.coeff y).totalDegree
structure ProperPair (P Q : Jet) : Prop where
  left_ne : P ≠ 0
  right_ne : Q ≠ 0
  no_common : ∀ D : Jet, Irreducible D → D ∣ P → ¬ D ∣ Q
def markEval (z : K) (S : K[X]) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def AtSurface (q : Surface) (z : K) (S : K[X]) : Prop :=
  q.asIdeal ≤ RingHom.ker (markEval z S)
def TwoDimensional (qs : Finset Surface) : Prop :=
  ∀ q ∈ qs, q.asIdeal.height = 2
def ComponentsOn (P Q : Jet) (qs : Finset Surface) : Prop :=
  ∀ q ∈ qs, q.asIdeal.height = 2 ∧ P ∈ q.asIdeal ∧ Q ∈ q.asIdeal
structure PreparedPair (P Q : Jet) where
  seedContent : Seeds
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  cheap : Jet
  layered : Jet
  ordinary : Finset Equation
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 812 + 2907
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cheap_caps : RowCaps cheap (cheapShape 0)
  layered_caps : RowCaps layered (layeredShape 0)
  proper : ProperPair cheap layered
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ 812
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ 63
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    graphEval z seedContent = 0 ∨ fixedAt fixedCheap S = 0 ∨ fixedAt fixedLayered S = 0 ∨
      (jetAt cheap z S = 0 ∧ jetAt layered z S = 0) ∨
      ∃ f ∈ ordinary, atMark f z S = 0
structure FourMassCap (qs : Finset Surface) (a c z e : ℚ) : Prop where
  seed : mass qs .seed ≤ a
  ordinate : mass qs .ordinate ≤ c
  mixed : mass qs .mixed ≤ z
  jets : mass qs .jets ≤ e
def SeedDominant (q : Surface) : Prop :=
  Ideal.comap (C.comp C : Seeds →+* Jet) q.asIdeal = ⊥
def JetDominant (q : Surface) : Prop :=
  Ideal.comap fixedEmbedding q.asIdeal = ⊥
def totalSectionDegree (qs : Finset Surface) (s : Slice) : ℕ :=
  ∑ q ∈ qs, sectionDegree q s
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
theorem seed_count {T : Finset K} {label : K → K} (hinj : Set.InjOn label (T : Set K))
    (C : SeedCover) (hdeg : C.curve.totalDegree < p)
    (hcover : ∀ γ ∈ T, C.Covers (label γ)) :
    T.card ≤ (p+1)*C.curve.totalDegree + C.points.card := by
  classical
  let zero := T.filter (fun γ => graphEval (label γ) C.curve = 0)
  let other := T.filter (fun γ => graphEval (label γ) C.curve ≠ 0)
  have inj : Set.InjOn (fun γ => seedEmbedding (label γ)) (T : Set K) :=
    fun _ ha _ hb h => hinj ha hb (seedEmbedding.injective h)
  have hzero : zero.card ≤ (p+1)*C.curve.totalDegree := by
    have hcard : (zero.image (fun γ => seedEmbedding (label γ))).card = zero.card :=
      Finset.card_image_iff.mpr (inj.mono (by exact Finset.filter_subset _ _))
    have hb := frobenius_coefficient_exception_count p
      C.curve.totalDegree C.curve.totalDegree (by decide) C.curve C.curve_ne
      (C.curve.degreeOf_le_totalDegree 0) hdeg (C.curve.degreeOf_le_totalDegree 1)
      (zero.image (fun γ => seedEmbedding (label γ))) (by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hγ).2)
    simpa only [hcard, Nat.add_mul, Nat.one_mul, Nat.add_comm (C.curve.totalDegree)] using hb
  have hother : other.card ≤ C.points.card := by
    apply Finset.card_le_card_of_injOn
      (fun γ => (seedEmbedding (label γ), seedEmbedding (label γ)^p))
    · intro γ hγ
      have hm := Finset.mem_filter.mp (show γ ∈ other from hγ)
      exact (hcover γ hm.1).resolve_left hm.2
    · intro x hx y hy h
      exact inj (Finset.mem_filter.mp (show x ∈ other from hx)).1
        (Finset.mem_filter.mp (show y ∈ other from hy)).1 (congrArg Prod.fst h)
  rw [← Finset.card_filter_add_card_filter_not (s := T)
    (p := fun γ => graphEval (label γ) C.curve = 0)]
  exact Nat.add_le_add hzero hother
theorem scalar_atX_injective : Function.Injective atX :=
  (IsFractionRing.injective L[X] FX).comp
    (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective)
theorem label_injective {u del} (M : AnchorModel u del) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def joinCovers {ι : Type*} (I : Finset ι) (C : ι → SeedCover) : SeedCover := by
  classical
  exact ⟨∏ i ∈ I, (C i).curve,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (C i).curve_ne),
    I.biUnion (fun i => (C i).points)⟩
theorem joinCovers_degree {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).curve.totalDegree ≤ ∑ i ∈ I, (C i).curve.totalDegree :=
  MvPolynomial.totalDegree_finsetProd I _
theorem joinCovers_points {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).points.card ≤ ∑ i ∈ I, (C i).points.card :=
  Finset.card_biUnion_le
theorem joinCovers_covers {ι : Type*} {I : Finset ι} {C : ι → SeedCover} {i : ι}
    (hi : i ∈ I) {z : K} (hz : (C i).Covers z) :
    (joinCovers I C).Covers z := by
  classical
  rcases hz with h | h
  · left
    change graphEval z (∏ j ∈ I, (C j).curve) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hi h
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
theorem combine_cut_covers {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) (lost : Finset Surface)
    (hcut : ∀ q ∈ lost, ∃ C : SeedCover,
      (C.curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      (C.points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → C.Covers (M.label γ)) :
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree s lost ∧
      (C.points.card : ℚ) ≤ constantDegree s lost ∧
      ∀ γ ∈ Γ, (∃ q ∈ lost, MarkOn M F q γ) → C.Covers (M.label γ) := by
  classical
  let C (q : Surface) : SeedCover :=
    if hq : q ∈ lost then Classical.choose (hcut q hq) else ⟨1, one_ne_zero, ∅⟩
  have hC (q) (hq : q ∈ lost) :
      ((C q).curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      ((C q).points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → (C q).Covers (M.label γ) := by
    simpa only [C, dite_eq_left hq] using Classical.choose_spec (hcut q hq)
  refine ⟨joinCovers lost C, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).curve.totalDegree : ℚ) := by
        exact_mod_cast joinCovers_degree lost C
      _ ≤ ∑ q ∈ lost, cutDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).1)
      _ = _ := by simp [cutDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).points.card : ℚ) := by
        exact_mod_cast joinCovers_points lost C
      _ ≤ ∑ q ∈ lost, constantDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).2.1)
      _ = _ := by simp [constantDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · rintro γ hγ ⟨q, hq, hqγ⟩
    exact joinCovers_covers hq ((hC q hq).2.2 γ hγ hqγ)
theorem mass_sdiff {S T : Finset Surface} (h : T ⊆ S) (s : Slice) :
    mass (S \ T) s = mass S s - mass T s := by
  classical
  apply eq_sub_of_add_eq
  exact Finset.sum_sdiff h
theorem mass_nonneg (S : Finset Surface) (s : Slice) : 0 ≤ mass S s :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
theorem moving_loss_bound {S₀ S₁ S₂ S₃ S₄ : Finset Surface}
    (h₁ : S₁ ⊆ S₀) (h₂ : S₂ ⊆ S₁) (h₃ : S₃ ⊆ S₂) (h₄ : S₄ ⊆ S₃)
    (m₀ : MassCap S₀ 2891 60998 381269)
    (m₁ : MassCap S₁ (seedMassCap 1) (ordinateMassCap 1) (mixedMassCap 1))
    (m₂ : MassCap S₂ (seedMassCap 2) (ordinateMassCap 2) (mixedMassCap 2))
    (m₃ : MassCap S₃ (seedMassCap 3) (ordinateMassCap 3) (mixedMassCap 3)) :
    cutDegree (cutShape 1) (S₀ \ S₁) + cutDegree (cutShape 2) (S₁ \ S₂) +
      cutDegree (cutShape 3) (S₂ \ S₃) + cutDegree (cutShape 4) (S₃ \ S₄)
      ≤ 7830019781/144 := by
  rcases m₀ with ⟨a₀,c₀,z₀⟩
  rcases m₁ with ⟨a₁,c₁,z₁⟩
  rcases m₂ with ⟨a₂,c₂,z₂⟩
  rcases m₃ with ⟨a₃,c₃,z₃⟩
  have a₄ := mass_nonneg S₄ .seed
  have c₄ := mass_nonneg S₄ .ordinate
  have z₄ := mass_nonneg S₄ .mixed
  norm_num [seedMassCap, ordinateMassCap, mixedMassCap] at a₁ c₁ z₁ a₂ c₂ z₂ a₃ c₃ z₃
  norm_num [cutDegree, cutShape, layeredShape, fullShape, mass_sdiff h₁, mass_sdiff h₂,
    mass_sdiff h₃, mass_sdiff h₄]
  linarith only [a₀,c₀,z₀,a₁,c₁,z₁,a₂,c₂,z₂,a₃,c₃,z₃,a₄,c₄,z₄]
theorem constant_loss_bound {S₀ S₁ S₂ S₃ S₄ : Finset Surface}
    (h₁ : S₁ ⊆ S₀) (h₂ : S₂ ⊆ S₁) (h₃ : S₃ ⊆ S₂) (h₄ : S₄ ⊆ S₃)
    (z₀ : mass S₀ .mixed ≤ 381269) (e₀ : mass S₀ .jets ≤ 3019828) :
    constantDegree (cutShape 1) (S₀ \ S₁) + constantDegree (cutShape 2) (S₁ \ S₂) +
      constantDegree (cutShape 3) (S₂ \ S₃) + constantDegree (cutShape 4) (S₃ \ S₄)
      ≤ 26769366519 := by
  have z₁ := mass_nonneg (S₀ \ S₁) .mixed
  have z₂ := mass_nonneg (S₁ \ S₂) .mixed
  have z₃ := mass_nonneg (S₂ \ S₃) .mixed
  have z₄ := mass_nonneg S₄ .mixed
  have e₁ := mass_nonneg (S₀ \ S₁) .jets
  have e₂ := mass_nonneg (S₁ \ S₂) .jets
  have e₃ := mass_nonneg (S₂ \ S₃) .jets
  have e₄ := mass_nonneg S₄ .jets
  norm_num [cutShape, layeredShape, fullShape, constantDegree, mass_sdiff h₁, mass_sdiff h₂,
    mass_sdiff h₃, mass_sdiff h₄] at z₁ z₂ z₃ e₁ e₂ e₃ ⊢
  linarith only [z₀,z₁,z₂,z₃,z₄,e₀,e₁,e₂,e₃,e₄]
theorem endpoint_fees (w : ℤ) (hlo : 3555 ≤ w) :
    (p+1)*(381269+812+2907) + 3019828 + 2891 +
      odePrice (131071 + (band w).endpoint) 381269 60998 +
      odePrice (131071 + (band w).endpoint) 63 14 +
      odePrice (131071 + (band w).endpoint) 118 24 +
      ((p+1)*54375137 + 26769366519) ≤ highPrefix w := by
  have hnot : ¬ w ≤ 3554 := by omega
  unfold band highPrefix
  simp only [hnot, ite_false]
  split_ifs <;> decide
theorem endpoint_range (w : ℤ) (hlo : 3555 ≤ w) (hhi : w ≤ 32680) :
    w ≤ (band w).endpoint ∧ 8249 ≤ (band w).endpoint ∧ (band w).endpoint ≤ 32680 := by
  unfold band
  split_ifs <;> norm_num at * <;> omega
end
end K1_14_3
end
