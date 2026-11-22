module

public import OverfullWork.KuhnOsthusClosedCycleReserve
public import OverfullWork.KuhnOsthusReserveIntervalGeometry

@[expose] public section


/-! Assemble the two halves of the primary factor of Lemma 10.3.
Only the two prescribed complete exceptional systems are taken
from outside the ordinary routing host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The two halves of (F) stitch to a spanning permutation factor,
with the two primary switch path bundles and both complete exceptional
path systems preserved as exact summands. Indices here are zero-based
and the length of the cluster cycle is `14*q`. -/
theorem kuhn_osthus_lemma_10_3_primary_factor {G H : Digraph V} {m q : ℕ} (hq : 15 ≤ q)
    (X : Fin (14*q) → Finset V)
    (hCover : ∀ v, ∃ i, v ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i, IsLowerSuperregularPair G ε d (X i) (X (finRotate (14*q) i)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let A := cyclicCluster X (by omega)
    let B := cyclicCluster (rotateClusterArray X (by omega) (7*q)) (by omega)
    ∀ (C : CycleAbsorberClaimOne G A m (4*q)) (C' : CycleAbsorberClaimOne G B m q)
      (E₃ : IntervalPathCover H (clusterIntervalVertices A (4*q) (6*q)) (A (4*q)) (A (6*q)))
      (E₅ : IntervalPathCover H (clusterIntervalVertices B q (3*q)) (B q) (B (3*q))),
    ∃ (P : OrderedClusterPaths G A (Fin (2*m)) (6*q) (7*q))
      (Q : OrderedClusterPaths G B (Fin (2*m)) (3*q) (7*q))
      (σ : Equiv.Perm V),
      let F := ((C.paths.unionPaths ⊔ E₃.digraph) ⊔ P.unionPaths) ⊔
        ((C'.paths.unionPaths ⊔ E₅.digraph) ⊔ Q.unionPaths)
      ∀ x y, F.Adj x y ↔ σ x = y := by
  intro A B C C' E₃ E₅
  obtain ⟨hB₀,hBn,hAll,hMeet,hDisA,hDisB⟩ :=
    cyclicCluster_complementary_intervals X (by omega : 0 < 7*q) (by omega : 7*q < 14*q)
      hCover hDis
  have hn : 14*q+0-7*q = 7*q := by omega
  rw [hn] at hBn hAll hMeet hDisB
  have hB (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X _ _ _
  have hB' : B = fun i => A (7*q+i) := funext hB
  rw [←hB'] at hB₀ hBn hAll hMeet hDisB
  have hCard (i : ℕ) : (A i).card = 2*m := hSize _
  let label (i : ℕ) : Fin (2*m) ≃ A i :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hCard i)).symm
  have hPair (i : ℕ) : IsLowerSuperregularPair G ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair G ε d (A i) (cyclicCluster X _ (i+1))
    rw [cyclicCluster_successor]
    exact hPairs _
  obtain ⟨P,U,hU,_,_⟩ := C.exists_half_path_cover_in (by omega) (by omega) E₃
    (label (6*q)) (label (7*q)) (fun i j hi hj h => hDisA i j (Nat.zero_le _) hi (Nat.zero_le _) hj h)
    (fun i _ _ => hCard i) ε d hε hGap hd (fun i _ _ => hPair i) r hr hCut hRoute
  let labelB (i : ℕ) : Fin (2*m) ≃ B i :=
    (label (7*q+i)).trans (Equiv.subtypeEquivRight (fun v => by rw [hB]))
  obtain ⟨Q,W,hW,_,_⟩ := C'.exists_half_path_cover_in (by omega) (by omega) E₅
    (labelB (3*q)) (labelB (7*q)) hDisB
    (fun i _ _ => by rw [hB]; exact hCard _) ε d hε hGap hd
    (fun i _ _ => by simpa only [hB,Nat.add_assoc] using hPair (7*q+i)) r hr hCut hRoute
  let U' := U.castBoundaries hBn.symm hB₀.symm
  have hU' : U'.digraph = U.digraph := IntervalPathCover.castBoundaries_digraph _ _ _
  obtain ⟨σ,hσ⟩ := U'.exists_winding_factor W hAll hMeet
    (hDisB (7*q) 0 le_rfl (Nat.zero_le _) (by omega))
  rw [hU',hU,hW] at hσ
  exact ⟨P,Q,σ,hσ⟩

end OverfullWork.DirectedRobustExpansion
