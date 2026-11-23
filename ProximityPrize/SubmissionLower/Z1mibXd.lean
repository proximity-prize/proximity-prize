import ProximityPrize.SubmissionLower.ZJObpKc
set_option Elab.async false
set_option autoImplicit true
namespace qe9q5Za
noncomputable section
open aR (af)
open oR (separant D3)
open we (eT cH fW vY D7 graph JZ)
open yz (oe S3 F3 ahz bpz)
open qSCPCwb (BW)
open qeu0RUc (yD avw Wa aIn afR
  i9 aFK)
open MvPolynomial
open private yz.three_ne_zero from ProximityPrize.SubmissionLower.BG
open private bHx from ProximityPrize.SubmissionLower.BG
abbrev aRt (v :ℕ) :=Wa v→cH
def ave {v :ℕ} (z :aRt v) :oe :=
  fun i=>z ⟨Finsupp.single i 1,aIn v i⟩
private theorem epO (v :ℕ) (y :oe) :
    ave (monomialPoint (Wa v) y)=y :=
  funext fun i=>monomialPoint_single y (aIn v i)
theorem bsL {v :ℕ} {f :af 3} {P:Ideal (eT 3)} {z :aRt v}
    (hz :z∈zeroLocus cH (i9 v f P)) :
    monomialPoint (Wa v) (ave z)=z := by
  obtain ⟨y,hy⟩:=exists_monomialPoint_eq_of_mem_zeroLocus_ker (aIn v)
    (zeroLocus_anti_mono (Ideal.ker_le_comap (afR v)) hz)
  rw [← hy,epO]
private theorem epN {v :ℕ} {f :af 3} {P:Ideal (eT 3)} {z :aRt v}
    (hz :z∈zeroLocus cH (i9 v f P)) :
    ave z∈zeroLocus cH (F3 f P) := by
  apply (monomialPoint_mem_zeroLocus_comap_iff (aIn v) _ _).mp
  rw [bsL hz]
  exact hz
private theorem Z1 {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) :
    P∈(BW f).minimalPrimes∧fW (separant f)∉P :=
  Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
private theorem b7F {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (g:eT 3) :
    vY g∈F3 f P↔g∈P:= by
  let:P.IsPrime :=(Z1 hP).1.isPrime
  change g∈(F3 f P).comap (rename Fin.castSucc).toRingHom↔g∈P
  rw [bHx (Z1 hP).2]
private theorem ez4 {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) {y :oe}
    (hy :y∈zeroLocus cH (F3 f P))
    (hs :eval y (vY (fW (separant f)))≠0) :
    y∈S3 f P:= by
  let x :Fin 3→cH :=y ∘ Fin.castSucc
  have hs' : eval x (fW (separant f))≠0:= by
    simpa only [vY,eval_rename,x] using hs
  have hx :x∈D7 f P:= by
    refine ⟨fun g hg => ?_,hs'⟩
    have h:=hy (vY g) ((b7F hP g).mpr hg)
    simpa only [aeval_eq_eval,vY,eval_rename,x] using h
  have hvan:graph f∈F3 f P:= by
    rintro _ ⟨w,hw,rfl⟩
    exact bpz hw.2
  have h:=hy (graph f) hvan
  simp only [aeval_eq_eval,graph,map_add,map_mul,map_ofNat,eval_X,vY,
    eval_rename] at h
  change eval x (fW (D3 f)) +
    3*y 3*eval x (fW (separant f))=0 at h
  refine ⟨x,hx,?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j=>Fin.snoc_castSucc _ _ j) i
  rw [JZ,Fin.snoc_last,div_eq_iff (mul_ne_zero yz.three_ne_zero hs')]
  change -eval x (fW (D3 f)) =
    y 3*(3*eval x (fW (separant f)))
  linear_combination -h
private theorem bqb {v :ℕ} {f :af 3} {P:Ideal (eT 3)}
    (hP:aFK v f P) {g:eT 4} (hg:g∉F3 f P) :
    {z | z∈zeroLocus cH (i9 v f P) ∧
      eval (ave z) g=0}.Finite := by
  obtain ⟨G,hG⟩:=monomialMap_surjective (aIn v) g
  have hnot:G∉i9 v f P:= by
    change afR v G∉F3 f P
    rwa [hG]
  obtain ⟨hdim,_⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP.1 hnot (b:=G.totalDegree) le_rfl
  rw [hP.2] at hdim
  refine ((finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) _
    (Nat.eq_zero_of_le_zero hdim)).1).subset ?_
  intro z hz
  apply mem_zeroLocus_sup_span_singleton_iff.mpr
  refine ⟨hz.1,?_⟩
  rw [← bsL hz.1,aeval_monomialPoint,hG,aeval_eq_eval]
  exact hz.2
private theorem eaO {v :ℕ} {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (hC:aFK v f P) :
    {z | z∈zeroLocus cH (i9 v f P) ∧
      ave z∉S3 f P}.Finite := by
  have hsep:vY (fW (separant f))∉F3 f P :=
    fun h=>(Z1 hP).2 ((b7F hP _).mp h)
  refine (bqb hC hsep).subset ?_
  intro z hz
  exact ⟨hz.1,not_ne_iff.mp fun hs =>
    hz.2 (ez4 hP (epN hz.1) hs)⟩
private theorem eaX {v :ℕ} {f :af 3} {P Q:Ideal (eT 3)}
    (hP:P∈yD f) (hQ:Q∈yD f) (hne :P≠Q)
    (hC:aFK v f P) :
    {z | z∈zeroLocus cH (i9 v f P) ∧
      ave z∈S3 f Q}.Finite := by
  have h : ¬ Q≤P:=Ideal.not_le_of_mem_minimalPrimes (Z1 hQ).1 (Z1 hP).1 hne.symm
  obtain ⟨g,hgQ,hgP⟩ : ∃ g,g∈Q∧g∉P:= by
    by_contra! hbad
    exact h hbad
  refine (bqb hC (fun hg=>hgP ((b7F hP _).mp hg))).subset ?_
  intro z hz
  refine ⟨hz.1,?_⟩
  obtain ⟨x,hx,he⟩:=hz.2
  rw [← he,ahz]
  exact hx.1 g hgQ
theorem d4a {v :ℕ} {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (hC:aFK v f P) :
    ∃ B:Finset (aRt v),
      ∀ z∈zeroLocus cH (i9 v f P),z∉B →
        ave z∈S3 f P ∧
        ∀ Q∈yD f,P≠Q→ave z∉S3 f Q:= by
  classical
  let overlap (Q:Ideal (eT 3)) :=
    {z | z∈zeroLocus cH (i9 v f P)∧ave z∈S3 f Q}
  have h:=(eaO hP hC).union
    (((yD f).erase P).finite_toSet.biUnion (t:=overlap) fun Q hQ =>
      eaX hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm hC)
  refine ⟨h.toFinset,fun z hz hB => ?_⟩
  have hn:=mt (h.mem_toFinset.mpr :_→z∈h.toFinset) hB
  exact ⟨Classical.byContradiction fun hb=>hn (Or.inl ⟨hz,hb⟩),
    fun Q hQ hne hmeet=>hn (Or.inr (Set.mem_iUnion₂.mpr
      ⟨Q,Finset.mem_erase.mpr ⟨hne.symm,hQ⟩,hz,hmeet⟩))⟩
end
end qe9q5Za
