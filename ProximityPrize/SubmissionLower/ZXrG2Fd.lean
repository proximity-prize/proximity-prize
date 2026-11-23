import ProximityPrize.SubmissionLower.E1
import ProximityPrize.SubmissionLower.P6Split
import ProximityPrize.SubmissionLower.Zb3VwYd
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.card_union_le → z2s, Finset.filter_subset → zT0, Finset.mem_union_left → zDk, Finset.mem_union_right → zMj, Finset.single_le_sum → zfK, Finset.sum_le_sum → zQk, Finset.univ → zdB, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.mul_le_mul_left → zBI, Nat.zero_le → zD0
set_option autoImplicit true
namespace P6_6
noncomputable section
open Polynomial
open P6 (K)
open aR (af Shape shape aO extend cK Dd jF)
open scoped BigOperators
def c1 :Prop :=
  ∀ w Γ s,Messages w Γ s →
    ∃ P:af 4,P≠0∧aO (shape P) m6∧tB P M8 ∧
      ∀ γ∈Γ,cK P (extend (s γ))=0
def c2 :Prop := ∀ w,(∀ i,P6.twist (w i)=w i)→aJ5 w
def c3:Prop :=
  ∀ w Δ s,Messages w Δ s→aJ5 w →
    ∀ n (f :Fin n→af 4),(∀ i,wm (f i)) →
      (∀ i j,i≠j → ¬ Associated (f i) (f j)) →
      let zo:=EarlyIndices w f
      (∀ γ∈Δ,∀ i∈zo,cK (f i) (extend (s γ))≠0) →
      RetainedSource Δ s f zo
def c4 :Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ P:jF Γ s,P.H.natDegree≤P6.ajO.toNat →
    ∃ (book :zJe K) (E :aw1),book.card≤80000 ∧
      ∀ γ∈Γ,γ∉book→E.bqU (extend (s γ))
def c5:Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ v,v≤ m6.t → ∀ g,axx v g →
    (∀ γ∈Γ,cK g (extend (s γ))=0)→Γ.card≤aIx v
def c6:Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ f,wm f →
    (∀ γ∈Γ,Dd f (extend (s γ)))→acX (shape f) →
    ∀ E :aw1,(∀ γ∈Γ,E.bqU (extend (s γ)))→Γ.card≤lY (shape f)
def c7:Prop :=
  ∀ w Δ s,Messages w Δ s → ∀ n (f :Fin n→af 4) S v,
    ChartMarks Δ s f S→aO (v.plus (wD (shape ∘ f) S)) m6 →
    ∀ R,JetFactor R →
      (∀ l ell dR,0<ell→ell≤l→aO (v.scale l) Wk →
        aO (shape R) (firstCaps v l)→ProperCutter Δ s R (physicalBody v ell) ell →
        markedWeight Δ s R≤largeFee v (shape R) l ell dR) ∧
      (∀ l ell,0<ell→ell≤l→aO (shape R) (firstCaps v l) →
        ¬ CompanionTest v (shape R) ell→(¬ R∣factorProd f S) →
        markedWeight Δ s R≤ smallFee (remainingChart v) (shape R)) ∧
      (∀ i∈S,Associated R (f i) → ∀ ell dR,0<ell →
        aO (v.scale ell) Wk→ProperCutter Δ s R (physicalBody v ell) ell →
        markedWeight Δ s R≤ selfFee v (shape R) ell dR)
def c8:Prop :=
  ∀ n (a :Fin n→Shape) (zo:zJe (Fin n)),
    (∀ i,Valid (a i))→aO (wD a zdB) m6 →
    let v :=wD a zo
    AdmissibleEarly v →
    ∃ jX,((wD a (zdB \ zo)).t=0∧jX=0∨LaterQuote v jX) ∧
      (∑ i∈zo,lY (a i))+aIx (wD a zdB).t+aPd+jX≤gV
private theorem in_spend {n:ℕ} (a :Fin n→Shape) {S:zJe (Fin n)} {i:Fin n}
    (hi:i∈S) :aO (a i) (wD a S) :=
  ⟨zfK (f := fun i=>(a i).b) (fun _ _=>zD0 _) hi,
    zfK (f := fun i=>(a i).j) (fun _ _=>zD0 _) hi,
    zfK (f := fun i=>(a i).t) (fun _ _=>zD0 _) hi⟩
private theorem remaining_fits {v a r :Shape} (h:aO (v.plus a) m6)
    (hr :aO r a) (hd:JetShape r) :aO r (remainingLiteral v) := by
  obtain ⟨hb,hj,ht⟩:=h
  obtain ⟨hrb,hrj,hrt⟩:=hr
  obtain ⟨_,hmin,hmax⟩:=hd
  change v.b+a.b≤ m6.b at hb
  change v.j+a.j≤ m6.j at hj
  change v.t+a.t≤ m6.t at ht
  have B:r.b≤ m6.b - v.b:= by omega
  have J:r.j≤ min (m6.j - v.j) (3*(m6.b - v.b)) :=le_min (by omega) (by omega)
  refine ⟨B,J,?_⟩
  change r.t≤ min (m6.t - v.t) (min (m6.b - v.b)
    (min (m6.j - v.j) (3*(m6.b - v.b))/3))
  exact le_min (by omega) (le_min (by omega)
    ((Nat.le_div_iff_mul_le (by decide :0<3)).mpr (by
      rw [Nat.mul_comm]
      exact hmin.trans J)))
private theorem dot_le {c a b:Shape} (h:aO a b) :dot c a≤dot c b :=
  z9f (z9f (zBI _ h.1) (zBI _ h.2.1))
    (zBI _ h.2.2)
private theorem weighted_dot {n:ℕ} (c:Shape) (a :Fin n→Shape) (e :Fin n→ℕ) :
    (∑ i,e i*dot c (a i))=dot c (wD (fun i=>(a i).scale (e i)) zdB) := by
  simp only [dot,wD,Shape.scale,Finset.mul_sum,mul_add,Finset.sum_add_distrib,Nat.mul_left_comm]
private theorem sum_marked_weight {n:ℕ} (Δ:zJe K) (s :K→K[X])
    (R:Fin n→af 4) (e :Fin n→ℕ) :
    (∑ γ∈Δ,∑ i,e i*ambientOrder (R i) (extend (s γ))) = ∑ i,e i*markedWeight Δ s (R i) := by
  rw [Finset.sum_comm]
  simp only [markedWeight,Finset.mul_sum]
private theorem later_count (geo:c7) {w Δ s n} {f :Fin n→af 4} {zo:zJe (Fin n)}
    {jX:ℕ} (hm:Messages w Δ s) (source :RetainedSource Δ s f zo)
    (bY:ChartMarks Δ s f (zdB \ zo))
    (fits :aO ((wD (shape ∘ f) zo).plus (wD (shape ∘ f) (zdB \ zo))) m6)
    (quote :LaterQuote (wD (shape ∘ f) zo) jX) :Δ.card≤jX:= by
  let v :=wD (shape ∘ f) zo
  let S:=zdB \ zo
  obtain ⟨l,ell,dR,coeff,hfirst,hell,hle,hbudget,htotal,htests⟩:=quote
  obtain ⟨r,R,e,first⟩:=source.first l hfirst
  have hweight (i:Fin r) :markedWeight Δ s (R i)≤dot coeff (shape (R i)) := by
    let x :=shape (R i)
    obtain ⟨large,small,self⟩:=geo w Δ s hm n f S v bY fits (R i) (first.factors i)
    obtain ⟨hlarge,hsmall⟩:=htests x (first.factors i).2.1 (first.each i)
    by_cases hc:CompanionTest v x ell
    · exact (large l ell dR hell hle hfirst.2.2.1 (first.each i)
        (source.companion _ (first.factors i) (first.newFactors i) ell hell hbudget (.inl hc))).trans
        (hlarge hc)
    by_cases hd:R i∣factorProd f S
    · obtain ⟨j,hj,hdiv⟩:=((first.factors i).1.prime.dvd_finsetProd_iff f).mp hd
      have he :=(first.factors i).1.associated_of_dvd (bY.factors j hj).1 hdiv
      have hbox :=anm.bNR (bY.factors j hj).1.ne_zero hdiv
      have hsame :=anm.bNR (first.factors i).1.ne_zero he.dvd'
      have ht:0<x.t:=(bY.factors j hj).2.1.trans_le hsame.2.2
      have hs :=in_spend (shape ∘ f) hj
      have hin:aO x (wD (shape ∘ f) S) :=
        ⟨hbox.1.trans hs.1,hbox.2.1.trans hs.2.1,hbox.2.2.trans hs.2.2⟩
      obtain ⟨k,lift,hk,hb,htst,hp⟩:=(hsmall hc).2 ht (remaining_fits fits hin (first.factors i).2.1)
      have hcut:ProperCutter Δ s (R i) (physicalBody v k) k :=
        source.companion _ (first.factors i) (first.newFactors i) k hk hb
          (htst.imp_right fun heq=>⟨heq,j,(Finset.mem_sdiff.mp hj).2,he⟩)
      exact (self j hj he k lift hk hb hcut).trans hp
    · exact (small l ell hell hle (first.each i) hc hd).trans (hsmall hc).1
  apply Nat.le_of_mul_le_mul_left _ hfirst.1
  calc
    l*Δ.card = ∑ _γ∈Δ,l:= by simp [Nat.mul_comm]
    _ ≤ ∑ γ∈Δ,∑ i,e i*ambientOrder (R i) (extend (s γ)) :=zQk first.order
    _ = ∑ i,e i*markedWeight Δ s (R i) :=sum_marked_weight Δ s R e
    _ ≤ ∑ i,e i*dot coeff (shape (R i)) :=zQk fun i _=>zBI _ (hweight i)
    _=dot coeff (wD (fun i=>(shape (R i)).scale (e i)) zdB) :=weighted_dot coeff _ e
    _≤dot coeff (firstCaps v l) :=dot_le first.total
    _≤l*jX:=htotal
private theorem fat_eligible {a :Shape} (h:aO a m6) :acX a := by
  have hm:max a.b a.j≤133:=max_le h.1 (h.2.1.trans (by decide))
  apply (Nat.mul_le_mul_right _ hm).trans_lt
  change 0x2f5825<P6.p
  decide
private theorem spend_partition {n:ℕ} (a :Fin n→Shape) (S:zJe (Fin n)) :
    (wD a S).plus (wD a (zdB \ S))=wD a Finset.univ := by
  simp only [wD,Shape.plus,Nat.add_comm (∑ i∈S,_),Finset.sum_sdiff (Finset.subset_univ S)]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) (h8:c8) :P6.c6:= by
  classical
  intro u D M Γ F _ lo hi
  let s :=F.scalar
  have hm:Messages M.word Γ s :=eAk M F hi
  obtain ⟨P,hP,hbox,hw,hz⟩:=h1 _ _ _ hm
  obtain ⟨n,g,f,cover⟩:=dRc P hP hbox hw hz
  obtain ⟨pole,hsmall⟩:=eMO M F lo hi
  obtain ⟨book,E,booked,hE⟩:=h4 _ _ _ hm pole hsmall
  let a :=shape ∘ f
  let zo:=EarlyIndices M.word f
  let rest:=zdB \ zo
  let low:=Γ.filter (fun γ=>cK g (extend (s γ))=0)
  let gH (i:Fin n) :=Γ.filter (fun γ =>
    γ∉book∧cK g (extend (s γ))≠0∧cK (f i) (extend (s γ))=0 ∧
      ∀ j∈zo,j< i→cK (f j) (extend (s γ))≠0)
  let left:=Γ.filter (fun γ=>γ∉book∧cK g (extend (s γ))≠0 ∧
    ∀ i∈zo,cK (f i) (extend (s γ))≠0)
  have lowerPaid :low.card≤aIx (wD a zdB).t :=
    h5 _ _ _ (hm.mono (zT0 _ _)) _ cover.fits.2.2 _ cover.lower
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have paidCap (i:Fin n) : (gH i).card≤lY (a i) := by
    have hs :gH i⊆Γ:=zT0 _ _
    refine h6 _ _ _ (hm.mono hs) _ (cover.factors i) ?_ (fat_eligible (cover.factors i).2.2.1) E ?_
    · intro γ hγ
      have hp:=(Finset.mem_filter.mp hγ).2
      exact ⟨hp.2.2.1,cover.regular γ (hs hγ) hp.2.1 i⟩
    · exact fun γ hγ=>hE γ (hs hγ) (Finset.mem_filter.mp hγ).2.1
  have hml:Messages M.word left s :=hm.mono (zT0 _ _)
  have units : ∀ γ∈left,∀ i∈zo,cK (f i) (extend (s γ))≠0 :=
    fun _ hγ=>(Finset.mem_filter.mp hγ).2.2.2
  have bY:ChartMarks left s f rest:= by
    refine ⟨fun i _=>cover.factors i,fun i _ j _=>cover.different i j,?_,?_⟩
    · intro γ hγ
      obtain ⟨hγΓ,_,hg,hfree⟩:=Finset.mem_filter.mp hγ
      obtain ⟨i,hi⟩:=(cover.Eh γ hγΓ).resolve_left hg
      exact ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun he=>hfree i he hi.1⟩,hi.1⟩
    · intro γ hγ i _
      obtain ⟨hγΓ,_,hg,_⟩:=Finset.mem_filter.mp hγ
      exact cover.regular γ hγΓ hg i
  have source :=h3 _ _ _ hml (h2 _ hml.word_fixed) n f cover.factors cover.different units
  obtain ⟨jX,hcase,hcap⟩:=h8 n a zo cover.valid cover.fits source.possible
  have leftCap:left.card≤jX:= by
    rcases hcase with ⟨hz,rfl⟩ | hq
    · have he :left = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro γ hγ
        obtain ⟨i,hi,_⟩:=bY.Eh γ hγ
        have h:=(cover.valid i).1.trans (in_spend a hi).2.2
        change (wD a rest).t=0 at hz
        rw [hz] at h
        exact (Nat.not_succ_le_zero 0) h)
      simp [he]
    · exact later_count h7 hml source bY ((spend_partition a zo).symm ▸ cover.fits) hq
  have Eh:Γ⊆book∪low∪zo.biUnion gH∪left:= by
    intro γ hγ
    by_cases hb:γ∈book
    · exact zDk _ (zDk _ (zDk _ hb))
    by_cases hg:cK g (extend (s γ))=0
    · exact zDk _ (zDk _
        (zMj _ (Finset.mem_filter.mpr ⟨hγ,hg⟩)))
    by_cases hu : ∀ i∈zo,cK (f i) (extend (s γ))≠0
    · exact zMj _ (Finset.mem_filter.mpr ⟨hγ,hb,hg,hu⟩)
    push Not at hu
    obtain ⟨i,hi,hzero⟩:=hu
    let T:=zo.filter (fun j=>cK (f j) (extend (s γ))=0)
    have he :T.Nonempty :=⟨i,Finset.mem_filter.mpr ⟨hi,hzero⟩⟩
    obtain ⟨hfirst,hvan⟩:=Finset.mem_filter.mp (T.min'_mem he)
    have hn (j:Fin n) (hj:j∈zo) (hlt:j<T.min' he) :
        cK (f j) (extend (s γ))≠0 :=
      fun hz=>(not_le_of_gt hlt) (T.min'_le j (Finset.mem_filter.mpr ⟨hj,hz⟩))
    exact zDk _ (zMj _ (Finset.mem_biUnion.mpr
      ⟨T.min' he,hfirst,Finset.mem_filter.mpr ⟨hγ,hb,hg,hvan,hn⟩⟩))
  have hearly : (zo.biUnion gH).card ≤ ∑ i∈zo,lY (a i) :=
    Finset.card_biUnion_le.trans (zQk fun i _=>paidCap i)
  have hb:book.card≤aPd:=booked.trans (by decide)
  calc
    Γ.card≤_:=Finset.card_le_card Eh
    _≤((book.card+low.card)+(zo.biUnion gH).card)+left.card :=
      (z2s _ _).trans (zlr ((z2s _ _).trans
        (zlr (z2s _ _) _)) _)
    _≤((aPd+aIx (wD a zdB).t) + ∑ i∈zo,lY (a i))+jX :=
      z9f (z9f (z9f hb lowerPaid) hearly) leftCap
    _≤gV:= by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hcap
end
end P6_6
