module

public import OverfullWork.KuhnOsthusRemainingParityReserves

@[expose] public section


/-! Align the literal cluster positions of Lemma 10.5 with
the construction for two nonwrapping exceptional covers. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V Z : Type*}

def ParityTripleSwitch.castClusters {G : Digraph V} {S T S' T' : Finset V}
    (K : ParityTripleSwitch G S T) (hS : S = S') (hT : T = T') :
    ParityTripleSwitch G S' T' :=
  hT ▸ hS ▸ K

@[simp] theorem ParityTripleSwitch.castClusters_source {G : Digraph V} {S T S' T' : Finset V}
    (K : ParityTripleSwitch G S T) (hS : S = S') (hT : T = T') (l : Bool) :
    ((K.castClusters hS hT).source l).val = (K.source l).val := by
  subst S'
  subst T'
  rfl

@[simp] theorem ParityTripleSwitch.castClusters_matching_target
    {G : Digraph V} {S T S' T' : Finset V}
    (K : ParityTripleSwitch G S T) (hS : S = S') (hT : T = T') (i : Fin 3) (l : Bool) :
    (((K.castClusters hS hT).matching i).target l).val = ((K.matching i).target l).val := by
  subst S'
  subst T'
  rfl

/-- On a translated interval, the path cover has the same arcs
and paths in the two sets of cluster coordinates. -/
theorem IntervalPathCover.exists_translated {H : Digraph V} {A B : ℕ → Finset V}
    {l r s t : ℕ} (E : IntervalPathCover H (clusterIntervalVertices A s t) (A s) (A t))
    (hs : s ≤ t) (hl : l ≤ r) (hLen : r-l = t-s)
    (hAt : ∀ i, l ≤ i → i ≤ r → B i = A (s+(i-l))) :
    ∃ E' : IntervalPathCover H (clusterIntervalVertices B l r) (B l) (B r),
      E'.digraph = E.digraph := by
  have hLeft : B l = A s := by simpa using hAt l le_rfl hl
  have hRight : B r = A t := by rw [hAt r hl le_rfl,show s+(r-l) = t by omega]
  let E₀ := E.castSupport (clusterIntervalVertices_translate A B hs hLen hl hAt).symm
  let E' := E₀.castBoundaries hLeft.symm hRight.symm
  exact ⟨E',(IntervalPathCover.castBoundaries_digraph _ _ _).trans
    (IntervalPathCover.castSupport_digraph _ _)⟩

private theorem rotateClusterArray_succ {k : ℕ} (X : Fin k → Finset V) (hk : 0 < k)
    (o : ℕ) (i : Fin k) :
    rotateClusterArray X hk o (finRotate k i) =
      X (finRotate k ⟨(o+i.val)%k,Nat.mod_lt _ hk⟩) := by
  apply congrArg X
  apply Fin.ext
  change (o+(finRotate k i).val)%k = (finRotate k ⟨(o+i.val)%k,Nat.mod_lt _ hk⟩).val
  rw [finRotate_val_modulo,finRotate_val_modulo]
  change (o+(i.val+1)%k)%k = ((o+i.val)%k+1)%k
  rw [Nat.add_mod_mod,Nat.mod_add_mod,Nat.add_assoc]

variable [Fintype V]

/-- The canonical continuation after B₁. It retains the original
K₂,₃ and selects the C₄ at the pair from V_(k/2+20) to V_(k/2+21).
The covers of I₇ and I₁ are supplied in their original coordinates. -/
theorem FirstParityReserve.exists_canonical_remaining_reserves
    {G E₆ H H' : Digraph V} {D R : Digraph (V ⊕ Z)} {q m r : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m) (hRD : R ≤ D)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε η d z : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (hz : 0 ≤ z)
    (hGapε : 2*ε < d) (hGapη : 2*η < d) (hd : d ≤ 1)
    (hTol : 2*(ε+z) ≤ η) (hLoss : 1 ≤ z*(((2*m:ℕ):ℝ)*η))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε d (X i) (X (finRotate (14*q) i)))
    (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ)) (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
    (hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    ∀ (Q : FirstParityReserve G E₆ (A (7*q+15)) (A (7*q+16)))
      (E₇ : IntervalPathCover H (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q)))
      (E₁ : IntervalPathCover H' (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q)))
      (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z)),
      (∀ i : Fin 3, i ≠ 0 → ∀ l, R.Adj (.inl (Q.triple.source l).val)
        (.inl ((Q.triple.matching i).target l).val)) →
      Disjoint R P₁.original →
      Nonempty (RemainingParityReserves Q.triple R (A (7*q+19)) (A (7*q+20)) P₇ P₁) := by
  intro hk A Q E₇ E₁ P₇ P₁ hKeep hReserved
  let Y := rotateClusterArray X hk (3*q)
  let B := cyclicCluster Y hk
  have hB (i : ℕ) : B i = A (3*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have hCover' (v : V) : ∃ i, v ∈ Y i := by
    obtain ⟨i,hi⟩ := hCover v
    let j : Fin (14*q) := ⟨(11*q+i.val)%(14*q),Nat.mod_lt _ hk⟩
    have he : (3*q+j.val)%(14*q) = i.val := by
      change (3*q+(11*q+i.val)%(14*q))%(14*q) = i.val
      rw [Nat.add_mod_mod,show 3*q+(11*q+i.val) = 14*q+i.val by omega,
        Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]
    refine ⟨j,?_⟩
    change v ∈ X ⟨(3*q+j.val)%(14*q),Nat.mod_lt _ hk⟩
    have hj : (⟨(3*q+j.val)%(14*q),Nat.mod_lt _ hk⟩ : Fin (14*q)) = i := Fin.ext he
    rwa [hj]
  have hDis' (i j : Fin (14*q)) (hne : i ≠ j) : Disjoint (Y i) (Y j) := by
    apply cyclicCluster_distinct hk hDis
    intro h
    have hh := congrArg (fun n : ℕ => (11*q+n)%(14*q)) h
    rw [Nat.add_mod_mod,Nat.add_mod_mod,show 11*q+(3*q+i.val) = 14*q+i.val by omega,
      show 11*q+(3*q+j.val) = 14*q+j.val by omega,Nat.add_mod_left,Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hh
    exact hne (Fin.ext hh)
  have hSize' (i : Fin (14*q)) : (Y i).card = 2*m := hSize _
  have hPair' (i : Fin (14*q)) :
      IsLowerSuperregularPair (ordinaryCycleHost R) ε d (Y i) (Y (finRotate (14*q) i)) := by
    change IsLowerSuperregularPair _ _ _ (Y i) (rotateClusterArray X hk (3*q) (finRotate (14*q) i))
    rw [rotateClusterArray_succ]
    exact hPair _
  have h₇ (i : ℕ) (hi : 9*q ≤ i) (_ : i ≤ 11*q) : B i = A (12*q+(i-9*q)) := by
    rw [hB,show 3*q+i = 12*q+(i-9*q) by omega]
  have h₁ (i : ℕ) (hi : 11*q ≤ i) (_ : i ≤ 13*q) : B i = A (0+(i-11*q)) := by
    rw [hB]
    apply congrArg X
    apply Fin.ext
    change (3*q+i)%(14*q) = (0+(i-11*q))%(14*q)
    rw [show 3*q+i = 14*q+(0+(i-11*q)) by omega,Nat.add_mod_left]
  obtain ⟨E₇',hE₇'⟩ := E₇.exists_translated (by omega) (by omega) (by omega) h₇
  obtain ⟨E₁',hE₁'⟩ := E₁.exists_translated (by omega) (by omega) (by omega) h₁
  have hS : B (4*q+15) = A (7*q+15) := by rw [hB]; congr 1; omega
  have hT : B (4*q+15+1) = A (7*q+16) := by rw [hB]; congr 1; omega
  have hU : B (4*q+19) = A (7*q+19) := by rw [hB]; congr 1; omega
  have hW : B (4*q+19+1) = A (7*q+20) := by rw [hB]; congr 1; omega
  let K := Q.triple.castClusters hS.symm hT.symm
  have hK (i : Fin 3) (hi : i ≠ 0) (l : Bool) :
      R.Adj (.inl (K.source l).val) (.inl ((K.matching i).target l).val) := by
    simpa only [K,ParityTripleSwitch.castClusters_source,ParityTripleSwitch.castClusters_matching_target]
      using hKeep i hi l
  let P₇' : ProjectedExceptionalArcs D E₇'.digraph (id : Z → Z) := hE₇'.symm ▸ P₇
  let P₁' : ProjectedExceptionalArcs D E₁'.digraph (id : Z → Z) := hE₁'.symm ▸ P₁
  have hP₁' : P₁'.original = P₁.original := by
    dsimp only [P₁']
    generalize E₁'.digraph = L at hE₁' ⊢
    subst L
    rfl
  have hP : Disjoint R P₁'.original := by rwa [hP₁']
  obtain ⟨T⟩ := ParityTripleSwitch.exists_remaining_parity_reserves Y hk hm hRD
    (r := r) (s := 4*q+15) (a := 4*q+19) (c := 9*q) (t := 11*q) (c' := 11*q) (t' := 13*q)
    (by omega) (by omega) (by omega) le_rfl (by omega) (by omega) (by omega)
    hCover' hDis' hSize' ε η d z hε hη hη₁ hz hGapε hGapη hd hTol hLoss hPair'
    hr hCutε hCutη hRouteε hRouteη K E₇' E₁' P₇' P₁' hK hP
  have hCast {S U T W : Finset V} {P Q : Digraph V} (K : ParityTripleSwitch G S T)
      (hS : S = U) (hT : T = W) {J L J' L' : Finset V}
      (hJ : J = J') (hL : L = L') {E F : Digraph V} (hE : E = P) (hF : F = Q)
      (P₇ : ProjectedExceptionalArcs D P (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D Q (id : Z → Z))
      (M : RemainingParityReserves (K.castClusters hS hT) R J L
        (hE.symm ▸ P₇) (hF.symm ▸ P₁)) :
      Nonempty (RemainingParityReserves K R J' L' P₇ P₁) := by
    subst U; subst W; subst J'; subst L'; subst E; subst F
    exact ⟨M⟩
  exact hCast Q.triple hS.symm hT.symm hU hW hE₇' hE₁' P₇ P₁ T

end OverfullWork.DirectedRobustExpansion
