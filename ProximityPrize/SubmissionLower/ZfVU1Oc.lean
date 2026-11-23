import ProximityPrize.SubmissionLower.ZedfuCc
set_option Elab.async false
section
set_option autoImplicit true
namespace P6_6_7
noncomputable section
open Polynomial P6_6
open aR (ao af shape cK extend wU ceilDiv)
open dN (GeoJets kC Ch bC An)
open BO (bfW Ue)
open agL (BV EY duA)
open scoped BigOperators
theorem ord_le (C:Context) (R:af 4) (γ:P6.K) :ord C R γ≤(shape R).b:= by
  classical
  exact Nat.findGreatest_le _
private theorem orderAt_ord (C:Context) (R:af 4) (γ:P6.K) :
    wU R (extend (C.s γ)) (ord C R γ) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (fun _ _=>Nat.zero_le _)
theorem assignSurfaces {C:Context} {R G:af 4} {ell:ℕ} {cs :ChartCase C.n}
    (h:PairInput C R G ell cs) :Nonempty (SurfaceAssignment C R G) := by
  classical
  have hex (γ) (hγ:γ∈C.Δ∧0<ord C R γ) :
      ∃ assigned,(kC R G).IsMinimalPrime assigned∧assigned≤Ch (extend (C.s γ)) := by
    have hle :kC R G≤Ch (extend (C.s γ)) := by
      apply Ideal.span_le.mpr
      intro P hP
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl
      · exact Ue.mpr (bfW hγ.2 (orderAt_ord C R γ))
      · exact Ue.mpr (bfW h.positive (h.order γ hγ.1))
    let: (Ch (extend (C.s γ))).IsPrime :=RingHom.ker_isPrime (An _)
    exact Ideal.exists_minimalPrimes_le hle
  refine ⟨⟨fun γ=>if hγ:γ∈C.Δ∧0<ord C R γ then (hex γ hγ).choose else ⊥,?_⟩⟩
  intro γ hγ ho
  simpa only [dite_eq_left (And.intro hγ ho)] using (hex γ ⟨hγ,ho⟩).choose_spec
private theorem genericOrder_le_ord {C:Context} {R:af 4} {assigned:Ideal GeoJets} {γ:P6.K}
    (hZ:assigned≤Ch (extend (C.s γ))) :genericOrder R assigned≤ord C R γ:= by
  classical
  have hg:genericOrder R assigned≤(shape R).b:=Nat.findGreatest_le _
  have hs : ∀ a,EY a<genericOrder R assigned→bC (BV a R)∈assigned :=
    Nat.findGreatest_spec (P:= fun d => ∀ a,EY a<d→bC (BV a R)∈assigned)
      (Nat.zero_le _) (fun _ hx=>(Nat.not_lt_zero _ hx).elim)
  apply Nat.le_findGreatest hg
  intro a ha
  by_contra! he
  have hz :=Ue.mp (hZ (hs a he))
  rw [duA] at hz
  exact (MvPolynomial.mem_support_iff.mp ha) hz
theorem dfk (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n)
    (assigned:SurfaceAssignment C R G) :
    markedWeight C.Δ C.s R=DG C R G assigned+lowGeneric C R G ell assigned +
      highAux C R G ell cs assigned+highInv C R G ell cs assigned:= by
  classical
  unfold markedWeight DG lowGeneric highAux highInv
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hb:surfaceOrder C R G assigned γ≤ord C R γ:= by
    unfold surfaceOrder
    split
    · rename_i ho
      exact genericOrder_le_ord (assigned.valid γ hγ ho).2
    · exact Nat.zero_le _
  change ord C R γ= _
  by_cases hl:genericOrder G (assigned.aI γ)<ell
  · simp [hl,Nat.not_le_of_gt hl,Nat.sub_add_cancel hb]
  · by_cases hr :RegularInvariant C cs (assigned.aI γ) γ
    · simp [hl,Nat.le_of_not_gt hl,hr,Nat.sub_add_cancel hb]
    · simp [hl,Nat.le_of_not_gt hl,hr,Nat.sub_add_cancel hb]
theorem split_small (C:Context) (R:af 4) :
    markedWeight C.Δ C.s R=smallMarks C R false+smallMarks C R true := by
  classical
  unfold markedWeight smallMarks
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  change ord C R γ= _
  by_cases h:thirdFiber R (extend (C.s γ))=0 <;> simp [h]
theorem fee_of_scaled {n d:ℕ} {a :ℤ} (hd:0<d) (h: (d:ℤ)*n≤a) :
    n≤ ceilDiv a.toNat d:= by
  have hnat :d*n≤a.toNat := by
    exact_mod_cast h.trans (Int.self_le_toNat a)
  unfold ceilDiv
  apply (Nat.le_div_iff_mul_le hd).mpr
  rw [Nat.mul_comm]
  omega
theorem jU (C:Context) {R:af 4} (hR:Irreducible R) (hj: (shape R).j=0) :
    markedWeight C.Δ C.s R≤(shape R).b:= by
  classical
  let incl:Unit→Fin 4 := fun _=>0
  have hincl:Function.Injective incl:= fun _ _ _=>Subsingleton.elim _ _
  have hvars : (R.vars :Set (Fin 4))⊆Set.range incl:= by
    intro i hi
    obtain ⟨m,hm,hi⟩:=(MvPolynomial.mem_vars_iff_mem_support i).mp hi
    have hidx :m.sum (fun j a=>j.val*a)≤(shape R).j :=
      Finset.le_sup (f := fun m=>m.sum (fun j a=>j.val*a)) hm
    have hterm :i.val*m i≤ m.sum (fun j a=>j.val*a) :=
      Finset.single_le_sum (f := fun j:Fin 4=>j.val*m j) (fun _ _=>Nat.zero_le _) hi
    have hi0:i.val=0 :=
      (Nat.mul_eq_zero.mp (Nat.le_zero.mp ((hterm.trans hidx).trans_eq hj))).resolve_right
        (Finsupp.mem_support_iff.mp hi)
    exact ⟨(),Fin.ext hi0.symm⟩
  obtain ⟨r,hr⟩:=MvPolynomial.exists_rename_eq_of_vars_subset_range R incl hincl hvars
  let e :=MvPolynomial.uniqueAlgEquiv (ao[X]) Unit
  let lift:=(MvPolynomial.rename incl).comp e.symm.toAlgHom
  have hev (T:ao[X]) :cK R T=(e r).eval T:= by
    rw [← hr,cK,MvPolynomial.eval_rename]
    change MvPolynomial.eval₂ (RingHom.id (ao[X])) (aR.jet T ∘ incl) r= _
    simpa [e,incl,aR.jet] using
      (MvPolynomial.eval₂_uniqueAlgEquiv (f :=r) (φ:=RingHom.id (ao[X]))
        (a :=aR.jet T ∘ incl)).symm
  have ha (γ:P6.K) (hγ:0<ord C R γ) :
      Associated R (MvPolynomial.X 0-MvPolynomial.C (extend (C.s γ))) := by
    let T:=extend (C.s γ)
    have hroot :Polynomial.IsRoot (e r) T:= by
      change (e r).eval T=0
      rw [← hev T]
      exact bfW hγ (orderAt_ord C R γ)
    have hdiv :=map_dvd lift (Polynomial.dvd_iff_isRoot.mpr hroot)
    have hlift:lift (e r)=R:= by simpa [lift] using hr
    have hlin:lift (Polynomial.X-Polynomial.C T)=MvPolynomial.X 0-MvPolynomial.C T:= by
      rw [map_sub]
      change MvPolynomial.rename incl (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X ()) Polynomial.X) -
          MvPolynomial.rename incl (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X ()) (Polynomial.C T))= _
      simp [incl]
    rw [hlift,hlin] at hdiv
    have hnot : ¬ IsUnit (MvPolynomial.X 0-MvPolynomial.C T:af 4) := by
      intro hunit
      have hm:=hunit.map (MvPolynomial.eval (aR.jet T))
      simp [aR.jet] at hm
    by_contra h
    exact hnot ((hR.isUnit_iff_not_associated_of_dvd hdiv).mpr h)
  by_cases h : ∃ γ∈C.Δ,0<ord C R γ
  · obtain ⟨γ,hγ,ho⟩:=h
    have hz (δ) (hδ:δ∈C.Δ) (hne :δ≠γ) :ord C R δ=0:= by
      by_contra hne0
      have hdvd:=(ha γ ho).dvd'.trans (ha δ (Nat.pos_of_ne_zero hne0)).dvd
      have he :=map_dvd (MvPolynomial.eval (aR.jet (extend (C.s γ)))) hdvd
      have hzero : (extend (C.s γ))-extend (C.s δ)=0:= by
        simpa [aR.jet] using he
      have hsame :=Polynomial.map_injective aR.embed aR.embed.injective (sub_eq_zero.mp hzero)
      exact hne ((C.messages.distinct hγ hδ hsame).symm)
    change (∑ i∈C.Δ,ord C R i)≤_
    rw [Finset.sum_eq_single_of_mem γ hγ hz]
    exact ord_le C R γ
  · change (∑ i∈C.Δ,ord C R i)≤_
    have hz : (∑ i∈C.Δ,ord C R i)=0 :=
      Finset.sum_eq_zero fun i hi=>Nat.eq_zero_of_not_pos fun hp=>h ⟨i,hi,hp⟩
    rw [hz]
    exact Nat.zero_le _
end
end P6_6_7
end
section
set_option autoImplicit true
namespace q8NBBre
noncomputable section
open P6_6_7
open aR (af extend)
open dN (GeoJets bC Ch AX)
open agL (BV EY)
open Dr (tW)
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev Branch:=Ideal GeoJets×Ideal GeoJets
def excessAt {C:Context} {R G:af 4}
    (assigned:SurfaceAssignment C R G) (γ:P6.K) :ℕ :=
  ord C R γ - surfaceOrder C R G assigned γ
def active {C:Context} {R G:af 4} (assigned:SurfaceAssignment C R G) :Finset P6.K :=
  C.Δ.filter (fun γ=>0<excessAt assigned γ)
structure Cuts {C:Context} {R G:af 4} (assigned:SurfaceAssignment C R G) where
  first:Ideal GeoJets→Exponent
  curve :P6.K→ Ideal GeoJets
  valid : ∀ γ∈active assigned,
    let z₀:=assigned.aI γ
    let u₀:=BV (first z₀) R
    EY (first z₀)=genericOrder R z₀∧bC u₀∉z₀ ∧
      (AX z₀ u₀).IsMinimalPrime (curve γ)∧curve γ≤Ch (extend (C.s γ))
variable {C:Context} {R G:af 4} {assigned:SurfaceAssignment C R G}
def Cuts.tag (A:Cuts assigned) (γ:P6.K) :Branch:=(assigned.aI γ,A.curve γ)
def Cuts.branches (A:Cuts assigned) :Finset Branch:= by
  classical exact (active assigned).image A.tag
def Cuts.marks (A:Cuts assigned) (B:Branch) :Finset P6.K:= by
  classical exact (active assigned).filter (fun γ=>A.tag γ=B)
def Cuts.polynomial (A:Cuts assigned) (B:Branch) :af 4 :=
  BV (A.first B.1) R
def Cuts.order (A:Cuts assigned) (B:Branch) :ℕ:=genericOrder (A.polynomial B) B.2
def Cuts.a4Q (A:Cuts assigned) (B:Branch) (γ:P6.K) :ℕ :=
  excessAt assigned γ - A.order B
def Cuts.degree (A:Cuts assigned) (h:aR.Shape) :ℚ :=
  ∑ B∈A.branches,(A.order B:ℚ)*tW B.2 [h]
end
end q8NBBre
end
