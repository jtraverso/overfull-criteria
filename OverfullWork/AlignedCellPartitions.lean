module

public import OverfullWork.ChunkedCellPartitions
public import Mathlib.Data.Fin.Embedding

@[expose] public section


/-! Align the number of equal-size source and target cells without
identifying their vertex sets. The final exceptional size is exactly
the larger of the two original exceptional sizes. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]
set_option maxHeartbeats 18000000

theorem exists_selected_cells (f : V → Option I) (m k : ℕ)
    (hSize : ∀ i,(cluster f i).card=m) (hk : k ≤ Fintype.card I) :
    ∃ (π : Fin k ↪ I) (g : V → Option (Fin k)),
      (∀ i,cluster g i=cluster f (π i)) ∧ (∀ i,(cluster g i).card=m) := by
  let π : Fin k ↪ I := (Fin.castLEEmb hk).trans (Fintype.equivFin I).symm.toEmbedding
  let C := fun i : Fin k => cluster f (π i)
  have hDis : ∀ i j,i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    exact clusters_disjoint f (fun hh => hij (π.injective hh))
  refine ⟨π,mapCells C,?_,?_⟩
  · intro i;exact cluster_mapCells C hDis i
  · intro i;rw [cluster_mapCells C hDis];exact hSize _

theorem exists_aligned_cells (f : V → Option I) (g : V → Option J) (m : ℕ)
    (hF : ∀ i,(cluster f i).card=m) (hG : ∀ j,(cluster g j).card=m) :
    let k := min (Fintype.card I) (Fintype.card J)
    ∃ (π : Fin k ↪ I) (σ : Fin k ↪ J) (f' g' : V → Option (Fin k)),
      (∀ i,cluster f' i=cluster f (π i)) ∧ (∀ i,cluster g' i=cluster g (σ i)) ∧
      (∀ i,(cluster f' i).card=m) ∧ (∀ i,(cluster g' i).card=m) ∧
      (exceptional f').card=(exceptional g').card ∧
      (exceptional f').card ≤ max (exceptional f).card (exceptional g).card := by
  dsimp only
  let k := min (Fintype.card I) (Fintype.card J)
  obtain ⟨π,f',hπ,hF'⟩ := exists_selected_cells f m k hF (min_le_left _ _)
  obtain ⟨σ,g',hσ,hG'⟩ := exists_selected_cells g m k hG (min_le_right _ _)
  have hOrderF := order_eq f m hF
  have hOrderG := order_eq g m hG
  have hOrderF' := order_eq f' m hF'
  have hOrderG' := order_eq g' m hG'
  simp only [Fintype.card_fin] at hOrderF' hOrderG'
  have hSame : (exceptional f').card=(exceptional g').card := by omega
  refine ⟨π,σ,f',g',hπ,hσ,hF',hG',hSame,?_⟩
  rcases le_total (Fintype.card I) (Fintype.card J) with hLeft|hRight
  · have hk : k=Fintype.card I := min_eq_left hLeft
    have hMul := congrArg (fun z : ℕ => m*z) hk
    have hh : (exceptional f').card=(exceptional f).card := by omega
    exact hh.le.trans (le_max_left _ _)
  · have hk : k=Fintype.card J := min_eq_right hRight
    have hMul := congrArg (fun z : ℕ => m*z) hk
    have hh : (exceptional g').card=(exceptional g).card := by omega
    rw [hSame]
    exact hh.le.trans (le_max_right _ _)

end OverfullWork.DirectedClusterQuotient
