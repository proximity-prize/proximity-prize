import ProximityPrize.SubmissionLower.Zo0SdJd
set_option Elab.async false
open _root_ renaming Fin.cases→lJ,P5_7.FarBand→aU,P5_7.WitnessOK→c9,P5_7.farAgreement→lz,P5_7.terminal→cy
section
set_option autoImplicit true
namespace P5_7
open P5 (gJ k p blockLength)
theorem far_coverage {w:ℤ} (hl:3600≤w) (hh:w≤33463) :
   ∃ b:aU,InFar b w:= by
 by_cases dbl:w≤3999
 · exact ⟨.dbl,show (3600:ℤ)≤w∧w≤3999 from ⟨by omega,dbl⟩⟩
 by_cases lZ:w≤4799
 · exact ⟨.lZ,show (4000:ℤ)≤w∧w≤4799 from ⟨by omega,lZ⟩⟩
 by_cases om:w≤7744
 · exact ⟨.om,show (4800:ℤ)≤w∧w≤7744 from ⟨by omega,om⟩⟩
 by_cases wS:w≤7999
 · exact ⟨.wS,show (7745:ℤ)≤w∧w≤7999 from ⟨by omega,wS⟩⟩
 by_cases vX:w≤14499
 · exact ⟨.vX,show (8000:ℤ)≤w∧w≤14499 from ⟨by omega,vX⟩⟩
 by_cases vg:w≤21447
 · exact ⟨.vg,show (14500:ℤ)≤w∧w≤21447 from ⟨by omega,vg⟩⟩
 by_cases wI:w≤23999
 · exact ⟨.wI,show (21448:ℤ)≤w∧w≤23999 from ⟨by omega,wI⟩⟩
 by_cases vW:w≤28299
 · exact ⟨.vW,show (24000:ℤ)≤w∧w≤28299 from ⟨by omega,vW⟩⟩
 by_cases wO:w≤32410
 · exact ⟨.wO,show (28300:ℤ)≤w∧w≤32410 from ⟨by omega,wO⟩⟩
 exact ⟨.wQ,show (32411 :ℤ)≤w∧w≤33657 from by omega⟩
theorem far_guards (b:aU) :
  0<b.row.lo∧b.row.hi<131071 ∧
  0<(cy b).shape.m*lz∧(cy b).shape.m*lz<p ∧
  (cy b).shape.B*(131071-b.row.lo)≤(cy b).shape.m*lz ∧
  b.row.prefixFee≤gJ.far.regular := by
 cases b <;> decide
abbrev wX (b:aU) :=k-1+b.row.hi
private structure aYP (D U bw e :ℕ) (g:jJ) :Prop where
 slots :g.slots≤U
 seed :g.seedCap<p
 witness :c9 D e g.witness
 rate :numerator D e g.witness≤g.rate
 gap:gap D ≤g.rate
 gH :bw + nativeFee D e ((p+1)*g.seedCap) g.rate≤gJ.far.regular
private theorem check_grade {D U bw e g}
 (q:g.slots≤U∧g.seedCap<p∧c9 D e g.witness ∧
   numerator D e g.witness≤g.rate∧gap D ≤g.rate ∧
   bw + nativeFee D e ((p+1)*g.seedCap) g.rate≤gJ.far.regular) :
 aYP D U bw e g:=⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2⟩
private def CheckedGrades (D U bw:ℕ) :ℕ→ℕ→List jJ→Prop
 | _,_,[]=>True
 | e,prev,g :: gs =>
   (prev≤g.rate∧aYP D U bw e g)∧CheckedGrades D U bw (e+1) g.rate gs
private instance witnessDecidable (D l:ℕ) (x :NativeWitness) :
  Decidable (c9 D l x) := by
 unfold c9
 infer_instance
private theorem grade_cons {D U bw e prev g gs}
 (h:prev≤g.rate)
 (q:g.slots≤U∧g.seedCap<p∧c9 D e g.witness ∧
   numerator D e g.witness≤g.rate∧gap D ≤g.rate ∧
   bw + nativeFee D e ((p+1)*g.seedCap) g.rate≤gJ.far.regular)
 (rest:CheckedGrades D U bw (e+1) g.rate gs) :
 CheckedGrades D U bw e prev (g :: gs) :=⟨⟨h,check_grade q⟩,rest⟩
private theorem grade_rows (b:aU) :
  CheckedGrades (wX b) (cy b).shape.U b.row.prefixFee 1 0 b.row.gw:= by
 cases b <;>
  repeat' first | exact True.intro | (apply grade_cons <;> try decide)
private theorem grade_get {D U bw e prev :ℕ} {xs :List jJ}
    (checked :CheckedGrades D U bw e prev xs) (i:Fin xs.length) :
    prev≤(xs.get i).rate∧aYP D U bw (e+i.val) (xs.get i) := by
  induction xs generalizing e prev with
  | nil=>exact i.elim0
  | cons g gs ih =>
    refine lJ ?_ (fun j => ?_) i
    · exact checked.1
    · obtain ⟨hr,h⟩:=ih checked.2 j
      exact ⟨checked.1.1.trans hr,by
        change aYP D U bw (e+(j.val+1)) (gs.get j)
        rw [← Nat.add_assoc,Nat.add_right_comm]
        exact h⟩
private theorem grade_mono {D U bw e prev :ℕ} {xs :List jJ}
    (checked :CheckedGrades D U bw e prev xs) (i j:Fin xs.length) (h:i.val≤j.val) :
    (xs.get i).rate≤(xs.get j).rate := by
  induction xs generalizing e prev with
  | nil=>exact i.elim0
  | cons g gs ih =>
    revert h
    refine lJ ?_ (fun i' => ?_) i
    · refine lJ ?_ (fun j' => ?_) j
      · exact fun _=>le_rfl
      · exact fun _=>(grade_get checked.2 j').1
    · refine lJ ?_ (fun j' => ?_) j
      · intro h
        simp only [Fin.val_succ,Fin.val_zero] at h
        omega
      · exact fun h=>ih checked.2 i' j' (Nat.le_of_succ_le_succ h)
private theorem checked (b:aU) (i:aKj b) :
  aYP (wX b) (cy b).shape.U b.row.prefixFee (i.val+1) (cV b i) := by
 simpa only [Nat.add_comm 1] using (grade_get (grade_rows b) i).2
theorem grade_slots (b:aU) (i:aKj b) :
 (cV b i).slots≤(cy b).shape.U:=(checked b i).slots
theorem grade_seed (b:aU) (i:aKj b) :
 (cV b i).seedCap<p:=(checked b i).seed
theorem grade_paid (b:aU) (i:aKj b) :
 b.row.prefixFee + nativeFee (wX b) (i.val+1) ((p+1)*(cV b i).seedCap)
  (cV b i).rate≤gJ.far.regular :=(checked b i).gH
private theorem degree_guards (b:aU) :
  k≤wX b∧wX b<lz∧lz<blockLength ∧
  0< normalWidth (wX b)∧b.row.gw.length<p:= by
 cases b <;> decide
theorem grade_guard (b:aU) (i:aKj b) :
  NativeGuard (wX b) (i.val+1) (cV b i).rate := by
 obtain ⟨hD,hA,hN,hL,hp⟩:=degree_guards b
 refine ⟨hD,hA,hN,hL,i.val.succ_pos,(Nat.succ_le_of_lt i.isLt).trans_lt hp,(checked b i).gap,?_⟩
 intro l hl hli
 let j:aKj b:=⟨l-1,by have :=i.isLt; omega⟩
 have hj:l=j.val+1 := by dsimp [j]; omega
 have hji:j.val≤ i.val := by omega
 rw [hj]
 exact ⟨(cV b j).witness,(checked b j).witness,
  (checked b j).rate.trans (grade_mono (grade_rows b) j i hji)⟩
end P5_7
end
section
set_option autoImplicit true
namespace P5_7
noncomputable section
open Polynomial
open P5 (K p)
open cu (FX Equation yq jz qD Vg vm)
private def nativeEquation (f :Equation) :OneSeedEquation :=
 f.map (Vg p).toRingHom
private theorem graph_specialize (z :K) :
   (evalRingHom (jz z)).comp (Vg (F:=FX) p).toRingHom =
     qD z := by
 apply MvPolynomial.ringHom_ext
 · intro c
   simp [Vg,qD]
 · intro i
   fin_cases i <;> simp [Vg,qD]
theorem native_restriction {f :Equation} (hn:f≠0) {v :ℕ}
   (hv :v<p) (hs :vm f v) :
   ∃ g:OneSeedEquation,g≠0∧g.natDegree≤f.natDegree ∧
     NativeSeedBound g ((p+1)*v) ∧ ∀ z S,atNative g z S=yq f z S:= by
 have hp:0<p:= by decide
 refine ⟨nativeEquation f,?_,natDegree_map_le,?_,?_⟩
 · have hl:=cu.bG0 p hp (f.coeff f.natDegree)
     (by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hn)
     (((f.coeff f.natDegree).degreeOf_le_totalDegree 0).trans_lt ((hs _).trans_lt hv))
   intro hz
   apply hl
   have h:=congrArg (fun g:OneSeedEquation=>g.coeff f.natDegree) hz
   rw [nativeEquation,coeff_map,coeff_zero] at h
   exact h
 · intro l
   rw [nativeEquation,coeff_map]
   change ((Vg p) (f.coeff l)).natDegree≤(p+1)*v
   have h0:=((f.coeff l).degreeOf_le_totalDegree 0).trans (hs l)
   have h1 :=((f.coeff l).degreeOf_le_totalDegree 1).trans (hs l)
   simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm v] using
     cu.b33 p v v (f.coeff l) h0 h1
 · intro z S
   rw [atNative,nativeEquation,eval₂_map,graph_specialize,yq]
end
end P5_7
end
