module

public import OverfullWork.KuhnOsthusParityCanonicalIntervals
public import OverfullWork.KuhnOsthusCycleParityAssembly

@[expose] public section


/-! Connect the physically constructed reserves to the exchange
configuration used for Lemma 10.4. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical
variable {V Z : Type*}

/-- The three matches of the same physical K₂,₃ and the two matches
of the auxiliary C₄ furnish the parity repair configuration. The
first two factors can be either of the main half splicings. -/
def RemainingParityReserves.repairConfiguration
    {G E₆ E₇ E₁ : Digraph V} {D R : Digraph (V ⊕ Z)} {S T U W : Finset V}
    (B₁ : FirstParityReserve G E₆ S T)
    {P₇ : ProjectedExceptionalArcs D E₇ (id : Z → Z)}
    {P₁ : ProjectedExceptionalArcs D E₁ (id : Z → Z)}
    (B : RemainingParityReserves B₁.triple R U W P₇ P₁)
    (T₀ T₁ S₀ S₁ : Equiv.Perm V)
    (h₀ : ∀ l, B₁.factor.permutation (B₁.factor.mark (l,0)) = S₀ (B₁.factor.mark (!l,0)))
    (h₁ : ∀ l, B₁.factor.permutation (B₁.factor.mark (l,1)) = S₁ (B₁.factor.mark (!l,1))) :
    ParityRepairConfiguration
      ![T₀,T₁,S₀,S₁,B₁.factor.permutation,B.second.permutation,B.third.permutation] := by
  refine {
    mark := B₁.factor.mark
    order := B₁.factor.order
    auxLeft := (B.auxiliary.diagonal.source false).val
    auxRight := (B.auxiliary.diagonal.source true).val
    crossFirst := ⟨(h₀ true).symm,(h₀ false).symm⟩
    crossSecond := ⟨(h₁ true).symm,(h₁ false).symm⟩
    crossAux := ⟨(B.auxiliary_arcs false).1.trans (B.auxiliary_arcs true).2.symm,
      (B.auxiliary_arcs true).1.trans (B.auxiliary_arcs false).2.symm⟩
    crossTriple := ?_
    auxBicycles := B.auxiliary_bicycles
    tripleBicycles := ?_ }
  · change
      B₁.factor.permutation (B₁.factor.mark (true,2)) =
        B.second.permutation (B₁.factor.mark (false,2)) ∧
      B.second.permutation (B₁.factor.mark (true,2)) =
        B.third.permutation (B₁.factor.mark (false,2)) ∧
      B.third.permutation (B₁.factor.mark (true,2)) =
        B₁.factor.permutation (B₁.factor.mark (false,2))
    constructor
    · rw [(B₁.triple_arcs true).2,(B₁.triple_arcs false).1,(B.triple_arcs false).1]
      rfl
    constructor
    · rw [(B₁.triple_arcs true).1,(B₁.triple_arcs false).1,
        (B.triple_arcs true).1,(B.triple_arcs false).2]
      rfl
    · rw [(B₁.triple_arcs true).1,(B₁.triple_arcs false).2,(B.triple_arcs true).2]
      rfl
  · change
      MarkedBicycle B.second.permutation (B₁.factor.mark (false,2)) (B₁.factor.mark (true,2)) ∧
      MarkedBicycle B.third.permutation (B₁.factor.mark (false,2)) (B₁.factor.mark (true,2))
    rw [(B₁.triple_arcs false).1,(B₁.triple_arcs true).1]
    exact B.triple_bicycles

/-- Existential form of the repair configuration used in the iteration. -/
theorem RemainingParityReserves.parity_repair_configuration
    {G E₆ E₇ E₁ : Digraph V} {D R : Digraph (V ⊕ Z)} {S T U W : Finset V}
    (B₁ : FirstParityReserve G E₆ S T)
    {P₇ : ProjectedExceptionalArcs D E₇ (id : Z → Z)}
    {P₁ : ProjectedExceptionalArcs D E₁ (id : Z → Z)}
    (B : RemainingParityReserves B₁.triple R U W P₇ P₁)
    (T₀ T₁ S₀ S₁ : Equiv.Perm V)
    (h₀ : ∀ l, B₁.factor.permutation (B₁.factor.mark (l,0)) = S₀ (B₁.factor.mark (!l,0)))
    (h₁ : ∀ l, B₁.factor.permutation (B₁.factor.mark (l,1)) = S₁ (B₁.factor.mark (!l,1))) :
    Nonempty (ParityRepairConfiguration
      ![T₀,T₁,S₀,S₁,B₁.factor.permutation,B.second.permutation,B.third.permutation]) :=
  ⟨B.repairConfiguration B₁ T₀ T₁ S₀ S₁ h₀ h₁⟩

/-- The two original arc sets also avoid previously used arcs if the
routing host and the two reserved original covers avoid them. -/
theorem RemainingParityReserves.disjoint_used {G E₇ E₁ : Digraph V}
    {D R L : Digraph (V ⊕ Z)} {S T U W : Finset V} {K : ParityTripleSwitch G S T}
    {P₇ : ProjectedExceptionalArcs D E₇ (id : Z → Z)}
    {P₁ : ProjectedExceptionalArcs D E₁ (id : Z → Z)}
    (B : RemainingParityReserves K R U W P₇ P₁)
    (hR : Disjoint R L) (h₇ : Disjoint P₇.original L) (h₁ : Disjoint P₁.original L) :
    Disjoint ((liftOrdinaryCycleArcs Z B.second.ordinary ⊔ P₇.original) ⊔
      (liftOrdinaryCycleArcs Z B.third.ordinary ⊔ P₁.original)) L := by
  have ordinary_le {P : Digraph V} (hP : P ≤ ordinaryCycleHost R) :
      liftOrdinaryCycleArcs Z P ≤ R := by
    rintro (x | x) (y | y) he
    · exact hP he
    · exact he.elim
    · exact he.elim
    · exact he.elim
  have h₀ := ordinary_le B.second.ordinary_le
  have h₀' := ordinary_le (B.third.ordinary_le.trans (fun _ _ he => he.1))
  exact disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hR.mono_left h₀,h₇⟩,
    disjoint_sup_left.mpr ⟨hR.mono_left h₀',h₁⟩⟩

/-- Construct the two remaining original reserves directly after
deleting the constructed B₁. Their ordinary routes and prescribed
exceptional systems are disjoint from B₁. -/
theorem FirstParityReserve.exists_remaining_after_original
    {H₆ H H' : Digraph V} {D R : Digraph (V ⊕ Z)} [Fintype V] {q m r : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m) (hRD : R ≤ D)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε₀ ε η d z : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η) (hη₁ : η ≤ 1) (hz : 0 ≤ z)
    (hGapε : 2*ε < d) (hGapη : 2*η < d) (hd : d ≤ 1)
    (hTol₀ : 2*(ε₀+z) ≤ ε) (hLoss₀ : 1 ≤ z*(((2*m:ℕ):ℝ)*ε))
    (hTol : 2*(ε+z) ≤ η) (hLoss : 1 ≤ z*(((2*m:ℕ):ℝ)*η))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε₀ d (X i) (X (finRotate (14*q) i)))
    (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ)) (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
    (hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    ∀ (E₆ : IntervalPathCover H₆ (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q)))
      (Q : FirstParityReserve (ordinaryCycleHost R) E₆.digraph (A (7*q+15)) (A (7*q+16)))
      (E₇ : IntervalPathCover H (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q)))
      (E₁ : IntervalPathCover H' (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q)))
      (P₆ : ProjectedExceptionalArcs D E₆.digraph (id : Z → Z))
      (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z)),
      Disjoint R P₇.original → Disjoint R P₁.original →
      let B₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
      ∃ B : RemainingParityReserves Q.triple (R \ B₁) (A (7*q+19)) (A (7*q+20)) P₇ P₁,
        Disjoint ((liftOrdinaryCycleArcs Z B.second.ordinary ⊔ P₇.original) ⊔
          (liftOrdinaryCycleArcs Z B.third.ordinary ⊔ P₁.original)) B₁ := by
  intro hk A E₆ Q E₇ E₁ P₆ P₇ P₁ hR₇ hR₁ B₁
  let R' := R \ B₁
  have hPair' (i : Fin (14*q)) :
      IsLowerSuperregularPair (ordinaryCycleHost R') ε d (X i) (X (finRotate (14*q) i)) :=
    Q.factor.residual_pair_after_restore P₆ R _ _ hm (hSize _) (hSize _) ε₀ ε d z
      hε hε₁ hz (by linarith) hTol₀ hLoss₀ (hPair i)
  have hExact : restoreExceptionalFactor Q.factor.permutation P₆.source id = B₁ :=
    P₆.restore_exact _ Q.factor.exact_factor Q.factor.ordinary_separate
  have hKeep (i : Fin 3) (hi : i ≠ 0) (l : Bool) :
      R'.Adj (.inl (Q.triple.source l).val) (.inl ((Q.triple.matching i).target l).val) := by
    have h := Q.unused i hi l
    refine ⟨h.1,?_⟩
    intro he
    change B₁.Adj (.inl (Q.triple.source l).val) (.inl ((Q.triple.matching i).target l).val) at he
    rw [←hExact] at he
    exact h.2 ((Q.factor.exact_factor _ _).mpr he.1)
  have hR' : R' ≤ R := fun _ _ h => h.1
  obtain ⟨B⟩ := FirstParityReserve.exists_canonical_remaining_reserves X hq hm (hR'.trans hRD)
    hCover hDis hSize ε η d z hε.le hη hη₁ hz hGapε hGapη hd hTol hLoss hPair'
    hr hCutε hCutη hRouteε hRouteη Q E₇ E₁ P₇ P₁ hKeep (hR₁.mono_left hR')
  have hOrd : liftOrdinaryCycleArcs Z Q.factor.ordinary ≤ R := by
    rintro (x | x) (y | y) he
    · exact Q.factor.ordinary_le he
    · exact he.elim
    · exact he.elim
    · exact he.elim
  obtain ⟨h₆₇O,h₆₇I⟩ := E₆.disjoint_cyclic_slots_at_wrap hk hDis (by omega) le_rfl le_rfl E₇
  obtain ⟨h₁₆O,h₁₆I⟩ := E₁.disjoint_cyclic_slots hk hDis (by omega) (by omega) (by omega) E₆
  have hB₇ : Disjoint P₇.original B₁ := (disjoint_sup_left.mpr
    ⟨hR₇.mono_left hOrd,P₆.original_disjoint_of_slots P₇ h₆₇O h₆₇I⟩).symm
  have hB₁ : Disjoint P₁.original B₁ := (disjoint_sup_left.mpr
    ⟨hR₁.mono_left hOrd,(P₁.original_disjoint_of_slots P₆ h₁₆O h₁₆I).symm⟩).symm
  have hRB : Disjoint R' B₁ := by
    rw [disjoint_iff_inf_le]
    intro x y h
    exact h.1.2 h.2
  exact ⟨B,B.disjoint_used hRB hB₇ hB₁⟩

end OverfullWork.DirectedRobustExpansion
