module

public import OverfullWork.KuhnOsthusPhysicalCyA3

@[expose] public section


/-! Construct a marked reserve in a common residual host. The
ordinary paths and the given exceptional path system are recorded
separately, so an arc removed for one factor cannot be reused by the next. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

structure CycleAbsorberResidualFactor {G H : Digraph V} {A : ℕ → Finset V}
    {m p b c : ℕ} (C : CycleAbsorberClaimOne G A m p) (B : ℕ → Finset V)
    (E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
    (D : Digraph V) (n : ℕ) where
  ordinary : Digraph V
  permutation : Equiv.Perm V
  rows : CycleAbsorberMarkedRows permutation m
  exact_factor : ∀ x y, (ordinary ⊔ E.digraph).Adj x y ↔ permutation x = y
  ordinary_le : ordinary ≤ D
  ordinary_slots : ∀ x y, ordinary.Adj x y →
    (∃ i, 3 ≤ i ∧ i < b ∧ x ∈ A i ∧ y ∈ A (i+1)) ∨
    (∃ i, i < n ∧ x ∈ B i ∧ y ∈ B (i+1))
  first : ∀ i l, rows.mark (l,cycleAbsorberColumn i 0) =
    (C.first.source (cycleAbsorberSwitchSlot m (i,cycleAbsorberLane l))).val ∧
    permutation (rows.mark (l,cycleAbsorberColumn i 0)) =
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 (cycleAbsorberLane l)))).val
  second : ∀ i l, rows.mark (l,cycleAbsorberColumn i 1) =
    (C.second.source (alternateCycleAbsorberSwitchSlot m (i,cycleAbsorberLane l))).val ∧
    permutation (rows.mark (l,cycleAbsorberColumn i 1)) =
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 (cycleAbsorberLane l)))).val
  repair_start : ∀ l, rows.mark (l,Fin.last (2*m)) ∈ A 11
  repair_end : ∀ l, permutation (rows.mark (l,Fin.last (2*m))) ∈ A 12
  repair : ∀ l, (D \ (ordinary ⊔ E.digraph)).Adj
    (rows.mark (l,Fin.last (2*m))) (permutation (rows.mark (!l,Fin.last (2*m))))

/-- All ordinary arcs, including the unused repair matching, are
chosen in the supplied residual. The exceptional paths may use
their own shortcuts. -/
theorem CycleAbsorberClaimOne.exists_residual_factor {G H D : Digraph V} {A : ℕ → Finset V}
    {m p b c n : ℕ} (C : CycleAbsorberClaimOne G A m p) (hm : 0 < m)
    (B : ℕ → Finset V) (hb : 15 ≤ b) (hc : b ≤ c) (hn : 3 ≤ n)
    (hB₀ : B 0 = A c) (hBn : B n = A 3)
    (E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
    (hAll : clusterIntervalVertices A 3 c ∪ clusterIntervalVertices B 0 n = univ)
    (hMeet : clusterIntervalVertices A 3 c ∩ clusterIntervalVertices B 0 n = B n ∪ B 0)
    (hSizeA : ∀ i, 3 ≤ i → i ≤ b → (A i).card = 2*m)
    (hDisA : ∀ i j, 3 ≤ i → i ≤ c → 3 ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hSizeB : ∀ i ≤ n, (B i).card = 2*m)
    (hDisB : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (B i) (B j))
    (hFirst : ∀ i l, D.Adj (C.first.source (cycleAbsorberSwitchSlot m (i,l)))
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 l))))
    (hSecond : ∀ i l, D.Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,l)))
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 l))))
    (η d : ℝ) (hη : 0 ≤ η) (hGap : 2*η < d) (hd : d ≤ 1)
    (hPairsA : ∀ i, 4 ≤ i → i < b → IsLowerSuperregularPair D η d (A i) (A (i+1)))
    (hPairsB : ∀ i < n, IsLowerSuperregularPair D η d (B i) (B (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    Nonempty (CycleAbsorberResidualFactor C B E D n) := by
  obtain ⟨S,h₃,h₄,h₇,h₈,hRepair⟩ := C.exists_open_reserve_in (cycleAbsorberLastCopy m hm)
    (fun i hi hi' => hSizeA i hi (by omega))
    (fun i j hi hi' hj hj' h => hDisA i j hi (by omega) hj (by omega) h)
    hFirst hSecond η d hη hGap hd (fun i hi hi' => hPairsA i hi (by omega)) r hr hCut hRoute
  obtain ⟨P,R,σ,hArc,hTrace,T,hSpan⟩ := S.exists_closed_reserve_tour_in B n b c hb hc hn
    hB₀ hBn E hAll hMeet (fun i hi => hSizeA i (by omega)) hDisA hSizeB hDisB
    η d hη hGap hd (fun i hi => hPairsA i (by omega)) hPairsB r hr hCut hRoute
  obtain ⟨M,h₁,h₂,hLast⟩ := S.exists_marked_rows hm σ T hSpan hTrace
  let O := (S.unionPaths ⊔ P.unionPaths) ⊔ R.unionPaths
  have hO : ∀ x y, (O ⊔ E.digraph).Adj x y ↔ σ x = y := by
    intro x y
    rw [←hArc x y]
    simp only [O,Digraph.sup_adj]
    tauto
  refine ⟨⟨O,σ,M,hO,sup_le (sup_le S.unionPaths_le P.unionPaths_le) R.unionPaths_le,
    ?_,?_,?_,?_,?_,?_⟩⟩
  · intro x y h
    rcases h with (h | h) | h
    · obtain ⟨j,i,hi,hir,rfl,rfl⟩ := Digraph.iSup_adj.mp h
      exact .inl ⟨i,hi,by omega,S.part i hi hir.le j,S.part _ (by omega) (by omega) j⟩
    · obtain ⟨j,i,hi,hir,rfl,rfl⟩ := Digraph.iSup_adj.mp h
      exact .inl ⟨i,by omega,hir,P.part i hi hir.le j,P.part _ (by omega) (by omega) j⟩
    · obtain ⟨j,i,hi,hir,rfl,rfl⟩ := Digraph.iSup_adj.mp h
      exact .inr ⟨i,hir,R.part i hi hir.le j,R.part _ (by omega) (by omega) j⟩
  · intro i l
    exact ⟨(h₁ i l).1.trans (h₃ ..),(h₁ i l).2.trans (h₄ ..)⟩
  · intro i l
    exact ⟨(h₂ i l).1.trans (h₇ ..),(h₂ i l).2.trans (h₈ ..)⟩
  · intro l
    rw [(hLast l).1]
    exact S.part 11 (by decide) (by decide) _
  · intro l
    rw [(hLast l).2]
    exact S.part 12 (by decide) le_rfl _
  · intro l
    constructor
    · rw [(hLast l).1,(hLast (!l)).2]
      exact hRepair _ _
    · intro h
      have he := M.mark.injective (σ.injective ((hO _ _).mp h))
      have hb := congrArg Prod.fst he
      cases l <;> cases hb

/-- Apply the residual construction through a full traversal of
the cluster cycle, with the exceptional interval at `b .. c`. -/
theorem CycleAbsorberClaimOne.exists_cyclic_residual_factor {G H D : Digraph V}
    {m p k b c : ℕ} (X : Fin k → Finset V) (hk : 0 < k)
    (hb : 15 ≤ b) (hc : b ≤ c) (hck : c < k)
    (C : CycleAbsorberClaimOne G (cyclicCluster X hk) m p) (hm : 0 < m)
    (E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (hFirst : ∀ i l, D.Adj (C.first.source (cycleAbsorberSwitchSlot m (i,l)))
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 l))))
    (hSecond : ∀ i l, D.Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,l)))
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 l))))
    (η d : ℝ) (hη : 0 ≤ η) (hGap : 2*η < d) (hd : d ≤ 1)
    (hPairs : ∀ i, IsLowerSuperregularPair D η d (cyclicCluster X hk i) (cyclicCluster X hk (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    Nonempty (CycleAbsorberResidualFactor C (fun i => cyclicCluster X hk (c+i)) E D (k+3-c)) := by
  obtain ⟨hB₀,hBn,hAll,hMeet,hDisA,hDisB⟩ :=
    cyclicCluster_reserve_intervals X (by omega : 3 < c) hck hCover hDis
  exact C.exists_residual_factor hm (fun i => cyclicCluster X hk (c+i)) hb hc
    (by omega : 3 ≤ k+3-c) hB₀ hBn E hAll hMeet
    (fun i _ _ => hSize _) hDisA (fun i _ => hSize _) hDisB hFirst hSecond
    η d hη hGap hd (fun i _ _ => hPairs i)
    (fun i _ => by simpa only [Nat.add_assoc] using hPairs (c+i)) r hr hCut hRoute

omit [Fintype V] in
/-- At each cluster whose successor pair is owned by the exceptional
interval, the reserve consumes no ordinary outgoing arcs. -/
theorem CycleAbsorberResidualFactor.ordinary_avoids_exceptional_slots {G H D : Digraph V}
    {m p k b c : ℕ} {X : Fin k → Finset V} (hk : 0 < k) (hb : 3 ≤ b) (hck : c < k)
    {C : CycleAbsorberClaimOne G (cyclicCluster X hk) m p}
    {E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c)}
    (T : CycleAbsorberResidualFactor C (fun i => cyclicCluster X hk (c+i)) E D (k+3-c))
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    {i : ℕ} (hi : b ≤ i) (hic : i < c) {x y : V}
    (hx : x ∈ cyclicCluster X hk i) : ¬ T.ordinary.Adj x y := by
  intro h
  rcases T.ordinary_slots x y h with ⟨j,_,hj,hjv,_⟩ | ⟨j,hj,hjv,_⟩
  · exact disjoint_left.mp (cyclicCluster_distinct hk hDis (i := i) (j := j)
      (by rw [Nat.mod_eq_of_lt (by omega : i < k),Nat.mod_eq_of_lt (by omega : j < k)]; omega))
      hx hjv
  · have hj' : c+j < k+3 := by omega
    apply disjoint_left.mp (cyclicCluster_distinct hk hDis (i := i) (j := c+j) ?_) hx hjv
    rw [Nat.mod_eq_of_lt (by omega : i < k)]
    by_cases hlt : c+j < k
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [show c+j = k+(c+j-k) by omega,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
      omega

end OverfullWork.DirectedRobustExpansion
