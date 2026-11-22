module

public import OverfullWork.KuhnOsthusCycleAbsorberCyA3
public import OverfullWork.KuhnOsthusReserveIntervalGeometry

@[expose] public section


/-! Connect the physical switch matchings of Claim 1 to the two
rows of (CyA3) after insertion of the exceptional interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Starting with the primary bundle, build the spanning reserve,
identify every marked arc with its prescribed switch, and retain
the two alternate repair arcs in the residual digraph. The same
construction applies with the cluster origin moved to the other half. -/
theorem CycleAbsorberClaimOne.exists_closed_reserve_with_order
    {G : Digraph V} {m p k b c : ℕ} (X : Fin k → Finset V)
    (hk : 0 < k) (hb : 15 ≤ b) (hbc : b ≤ c) (hck : c < k)
    (C : CycleAbsorberClaimOne G (cyclicCluster X hk) m p) (hm : 0 < m) (hp : 12 ≤ p)
    (hpk : p < k)
    (E : IntervalPathCover (G \ C.paths.unionPaths)
      (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    (hCover : ∀ x : V, ∃ i, x ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε η d a : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hGap : 2*η < d) (hd : d ≤ 1) (hTol : 2*(ε+a) ≤ η)
    (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, IsLowerSuperregularPair G ε d (X i) (X (finRotate k i)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let A := cyclicCluster X hk
    let B := fun i => A (c+i)
    let n := k+3-c
    let D := G \ C.paths.unionPaths
    ∃ (S : OrderedClusterPaths D A (Fin m × Fin 2) 3 12)
      (P : OrderedClusterPaths D A (Fin m × Fin 2) 12 b)
      (R : OrderedClusterPaths D B (Fin m × Fin 2) 0 n)
      (σ : Equiv.Perm V) (M : CycleAbsorberMarkedRows σ m),
      (∀ x y, (((S.unionPaths ⊔ P.unionPaths) ⊔ E.digraph) ⊔ R.unionPaths).Adj x y ↔ σ x = y) ∧
      (((S.unionPaths ⊔ P.unionPaths) ⊔ E.digraph) ⊔ R.unionPaths) ≤ D ∧
      (∀ i l, M.mark (l,cycleAbsorberColumn i 0) =
        (C.first.source (cycleAbsorberSwitchSlot m (i,cycleAbsorberLane l))).val ∧
        σ (M.mark (l,cycleAbsorberColumn i 0)) =
          (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 (cycleAbsorberLane l)))).val) ∧
      (∀ i l, M.mark (l,cycleAbsorberColumn i 1) =
        (C.second.source (alternateCycleAbsorberSwitchSlot m (i,cycleAbsorberLane l))).val ∧
        σ (M.mark (l,cycleAbsorberColumn i 1)) =
          (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 (cycleAbsorberLane l)))).val) ∧
      ∀ l, D.Adj (M.mark (l,Fin.last (2*m))) (σ (M.mark (!l,Fin.last (2*m)))) ∧
        σ (M.mark (l,Fin.last (2*m))) ≠ σ (M.mark (!l,Fin.last (2*m))) := by
  intro A B n D
  obtain ⟨hB₀,hBn,hAll,hMeet,hDisA,hDisB⟩ :=
    cyclicCluster_reserve_intervals X (by omega : 3 < c) hck hCover hDis
  have hCard (i : ℕ) : (A i).card = 2*m := hSize _
  have hPos (i : ℕ) : (A i).Nonempty := card_pos.mp (by rw [hCard]; omega)
  have hDisP (i j : ℕ) (hi : i ≤ p) (hj : j ≤ p) (h : i ≠ j) : Disjoint (A i) (A j) := by
    apply hDis
    intro he
    apply h
    have he' := congrArg Fin.val he
    change i % k = j % k at he'
    rwa [Nat.mod_eq_of_lt (hi.trans_lt hpk),Nat.mod_eq_of_lt (hj.trans_lt hpk)] at he'
  have hCycle (i : ℕ) : IsLowerSuperregularPair G ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair G ε d (A i) (cyclicCluster X hk (i+1))
    rw [cyclicCluster_successor]
    exact hPairs _
  have hResidual (i : ℕ) : IsLowerSuperregularPair D η d (A i) (A (i+1)) :=
    IsLowerSuperregularPair.after_path_bundle C.paths (fun i j _ hi _ hj h => hDisP i j hi hj h)
      (A i) (A (i+1)) (hPos _) (hPos _) (2*m) (hCard _) (hCard _)
      ε η d a hε hη hη₁ ha (by linarith) hTol hBudget (hCycle i)
  obtain ⟨S,h₃,h₄,h₇,h₈,hRepair⟩ := C.exists_open_reserve hp
    (cycleAbsorberLastCopy m hm) (fun i _ => hCard i) hDisP ε η d a hε hη hη₁ ha hGap hd hTol hBudget
    (fun i _ _ => hCycle i) r hr hCut hRoute
  obtain ⟨P,R,σ,hArc,hTrace,H,hSpan⟩ := S.exists_closed_reserve_tour B n b c hb hbc
    (by dsimp [n]; omega) hB₀ hBn E hAll hMeet (fun i _ _ => hCard i) hDisA
    (fun i _ => hCard (c+i)) hDisB η d hη.le hGap hd
    (fun i _ _ => hResidual i)
    (fun i _ => by simpa only [B,Nat.add_assoc] using hResidual (c+i)) r hr hCut hRoute
  obtain ⟨M,hFirst,hSecond,hLast⟩ := S.exists_marked_rows hm σ H hSpan hTrace
  refine ⟨S,P,R,σ,M,hArc,?_,?_,?_,?_⟩
  · exact sup_le (sup_le (sup_le S.unionPaths_le P.unionPaths_le) E.digraph_le) R.unionPaths_le
  · intro i l
    exact ⟨(hFirst i l).1.trans (h₃ ..), (hFirst i l).2.trans (h₄ ..)⟩
  · intro i l
    exact ⟨(hSecond i l).1.trans (h₇ ..), (hSecond i l).2.trans (h₈ ..)⟩
  · intro l
    constructor
    · rw [(hLast l).1,(hLast (!l)).2]
      exact hRepair _ _
    · intro h
      have hEq := congrArg Prod.fst (M.mark.injective (σ.injective h))
      cases l <;> cases hEq

end OverfullWork.DirectedRobustExpansion
