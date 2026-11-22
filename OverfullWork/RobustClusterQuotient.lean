module

public import OverfullWork.DirectedClusterQuotient

@[expose] public section


/-! The finite counting core of Kühn--Osthus--Treglown Lemma 14:
lift a set of clusters, apply robust expansion in the host, pay the
per-vertex neighbour loss, and project robust neighbours to clusters.
The quotient is constructed from the actual pure digraph. Constructing
the directed regularity partition and pure digraph is a separate task. -/
namespace OverfullWork.RobustClusterQuotient
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem inNeighbours_mono (D : Digraph V) {A B : Finset V} (hSub : A ⊆ B) (v : V) :
    inNeighbours D A v ≤ inNeighbours D B v :=
  card_le_card (filter_subset_filter _ hSub)

theorem neighbour_loss_of_deleted_indegree (D H : Digraph V) (hLe : H ≤ D)
    (L : ℕ) (hLoss : ∀ v,inDegree (D\H) v ≤ L) (A : Finset V) (v : V) :
    inNeighbours D A v ≤ inNeighbours H A v+L := by
  have hPart := DirectedArcSelection.incidence_partition D H hLe A {v}
  simp only [incidences,sum_singleton] at hPart
  have hBound := (inNeighbours_mono (D\H) (subset_univ A) v).trans (hLoss v)
  change inNeighbours (D\H) A v ≤ L at hBound
  omega

theorem robust_of_neighbour_loss (D H : Digraph V) (f : V → Option I) (m : ℕ)
    (hm : 0 < m) (hSize : ∀ i,(cluster f i).card=m) (r t s T L : ℕ)
    (hRobust : IsRobustAt D r t)
    (hLoss : ∀ A v,inNeighbours D A v ≤ inNeighbours H A v+L)
    (hInterval : t ≤ m*T) (hBudget : (exceptional f).card+L+m*s ≤ r) :
    IsRobustAt (quotient H f) s T := by
  intro S hLo hHi
  have hLiftLo : t ≤ (lift f S).card := by
    rw [lift_card f m hSize]
    exact hInterval.trans (Nat.mul_le_mul_left m hLo)
  have hLiftHi : (lift f S).card+t ≤ Fintype.card V := by
    have hMul := Nat.mul_le_mul_left m hHi
    have hOrder := order_eq f m hSize
    rw [lift_card f m hSize]
    nlinarith only [hMul,hOrder,hInterval]
  have hGrow := hRobust (lift f S) hLiftLo hLiftHi
  rw [lift_card f m hSize] at hGrow
  have hMap : ∀ v ∈ neighbourhood D r (lift f S),∀ i,f v=some i →
      i ∈ neighbourhood (quotient H f) s S := by
    intro v hv i hfi
    have hSource : r ≤ inNeighbours D (lift f S) v := (mem_filter.mp hv).2
    have hPay := hLoss (lift f S) v
    have hUpper := inNeighbours_lift_le H f m hSize S v i hfi
    have hMul : m*s ≤ m*inNeighbours (quotient H f) S i := by omega
    have hCount : s ≤ inNeighbours (quotient H f) S i := (mul_le_mul_iff_right₀ hm).mp hMul
    exact mem_filter.mpr ⟨mem_univ _,hCount⟩
  have hUpper := card_le_exceptional_add_lift f m hSize
    (neighbourhood D r (lift f S)) (neighbourhood (quotient H f) s S) hMap
  have hMul : m*(S.card+s) ≤ m*(neighbourhood (quotient H f) s S).card := by
    nlinarith only [hGrow,hUpper,hBudget]
  exact (mul_le_mul_iff_right₀ hm).mp hMul

theorem robust_of_deleted_indegree (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (m : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (r t s T L : ℕ)
    (hRobust : IsRobustAt D r t) (hLoss : ∀ v,inDegree (D\H) v ≤ L)
    (hInterval : t ≤ m*T) (hBudget : (exceptional f).card+L+m*s ≤ r) :
    IsRobustAt (quotient H f) s T :=
  robust_of_neighbour_loss D H f m hm hSize r t s T L hRobust
    (neighbour_loss_of_deleted_indegree D H hLe L hLoss) hInterval hBudget

end OverfullWork.RobustClusterQuotient
