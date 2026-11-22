module

public import OverfullWork.DirectedDegreeTrimming
public import OverfullWork.DirectedClusterQuotient

@[expose] public section


/-! Restore all arcs incident with exceptional vertices and remove
arcs inside each ordinary cell. The actual resulting graph has global
incoming/outgoing loss bounds and preserves every off-diagonal host
pair. No regular partition or Hamilton cycle is inferred to exist. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 12000000

def exceptionalPure (D H : Digraph V) (f : V → Option I) : Digraph V where
  Adj u v := D.Adj u v ∧ (f u=none ∨ f v=none ∨ (f u≠f v ∧ H.Adj u v))

theorem exceptionalPure_le (D H : Digraph V) (f : V → Option I) : exceptionalPure D H f≤D :=
  fun _ _ h => h.1

theorem exceptionalPure_incident (D H : Digraph V) (f : V → Option I) (u v : V)
    (h : f u=none ∨ f v=none) : (exceptionalPure D H f).Adj u v ↔ D.Adj u v := by
  constructor
  · exact fun hh => hh.1
  · intro hh
    exact ⟨hh,h.elim Or.inl (fun hv => Or.inr (Or.inl hv))⟩

theorem exceptionalPure_diagonal (D H : Digraph V) (f : V → Option I) (i : I)
    (u v : V) (hu : u∈cluster f i) (hv : v∈cluster f i) :
    ¬(exceptionalPure D H f).Adj u v := by
  intro hh
  have hU := (mem_cluster f i u).mp hu
  have hV := (mem_cluster f i v).mp hv
  rcases hh.2 with h|h|⟨h,_⟩
  · rw [hU] at h;simp at h
  · rw [hV] at h;simp at h
  · exact h (hU.trans hV.symm)

theorem exceptionalPure_between (D H : Digraph V) (hLe : H≤D) (f : V → Option I)
    (i j : I) (hij : i≠j) (u v : V) (hu : u∈cluster f i) (hv : v∈cluster f j) :
    (exceptionalPure D H f).Adj u v ↔ H.Adj u v := by
  have hU := (mem_cluster f i u).mp hu
  have hV := (mem_cluster f j v).mp hv
  constructor
  · intro hh
    rcases hh.2 with h|h|⟨_,h⟩
    · rw [hU] at h;simp at h
    · rw [hV] at h;simp at h
    · exact h
  · intro hh
    refine ⟨hLe hh,Or.inr (Or.inr ⟨?_,hh⟩)⟩
    intro he
    exact hij (Option.some.inj (hU.symm.trans (he.trans hV)))

theorem exceptionalPure_indegree_loss (D H : Digraph V) (f : V → Option I)
    (m L : ℕ) (hSize : ∀ i,(cluster f i).card≤m)
    (hLoss : ∀ v,f v≠none → inDegree (D\H) v≤L) (v : V) :
    inDegree (D\exceptionalPure D H f) v≤L+m := by
  letI : DecidableRel (D\H).Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (D\exceptionalPure D H f).Adj := fun _ _ => Classical.propDecidable _
  cases hV : f v with
  | none =>
    have hz : inDegree (D\exceptionalPure D H f) v=0 := by
      unfold inDegree inNeighbours
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro u hu
      obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
      exact hNot ⟨hD,Or.inr (Or.inl hV)⟩
    omega
  | some i =>
    have hSub : univ.filter (fun u => (D\exceptionalPure D H f).Adj u v)⊆
        (univ.filter fun u => (D\H).Adj u v)∪cluster f i := by
      intro u hu
      obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
      by_cases hU : f u=some i
      · exact mem_union_right _ ((mem_cluster f i u).mpr hU)
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨mem_univ _,hD,?_⟩
        intro hH
        exact hNot ⟨hD,Or.inr (Or.inr ⟨fun he => hU (he.trans hV),hH⟩)⟩
    have hCard := (card_le_card hSub).trans (card_union_le _ _)
    have hOld := hLoss v (by rw [hV];simp)
    have hCell := hSize i
    change inDegree (D\exceptionalPure D H f) v ≤ inDegree (D\H) v+(cluster f i).card at hCard
    omega

theorem exceptionalPure_outdegree_loss (D H : Digraph V) (f : V → Option I)
    (m L : ℕ) (hSize : ∀ i,(cluster f i).card≤m)
    (hLoss : ∀ v,f v≠none → outDegree (D\H) v≤L) (v : V) :
    outDegree (D\exceptionalPure D H f) v≤L+m := by
  letI : DecidableRel (D\H).Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (D\exceptionalPure D H f).Adj := fun _ _ => Classical.propDecidable _
  cases hV : f v with
  | none =>
    have hz : outDegree (D\exceptionalPure D H f) v=0 := by
      unfold outDegree
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro u hu
      obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
      exact hNot ⟨hD,Or.inl hV⟩
    omega
  | some i =>
    have hSub : univ.filter (fun u => (D\exceptionalPure D H f).Adj v u)⊆
        (univ.filter fun u => (D\H).Adj v u)∪cluster f i := by
      intro u hu
      obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
      by_cases hU : f u=some i
      · exact mem_union_right _ ((mem_cluster f i u).mpr hU)
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨mem_univ _,hD,?_⟩
        intro hH
        exact hNot ⟨hD,Or.inr (Or.inr ⟨fun he => hU (he.symm.trans hV),hH⟩)⟩
    have hCard := (card_le_card hSub).trans (card_union_le _ _)
    have hOld := hLoss v (by rw [hV];simp)
    have hCell := hSize i
    change outDegree (D\exceptionalPure D H f) v ≤ outDegree (D\H) v+(cluster f i).card at hCard
    omega

end OverfullWork.DirectedClusterQuotient
