module

public import OverfullWork.OsthusStadenUsefulPrimaryBridges

@[expose] public section


/-! Route the choices of all bridges and the equalizing deletions
through the corresponding disjoint base p-cells. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Choose one distinct vertex from each p-cell in every layer.
At a prescribed bridge source the vertex belongs to the useful set;
all choices also lie in the corresponding base cell. -/
theorem exists_globally_distinct_bridge_and_trim_vertices
    {L U I V : Type*} [Fintype L] [Fintype U]
    (base : U → Finset V) (cell : L → U → Finset V)
    (source : L → I → U) (useful : L → I → Finset V) (loss : ℕ)
    (hBase : ∀ a b, a ≠ b → Disjoint (base a) (base b))
    (hSource : ∀ j, Function.Injective (source j))
    (hNear : ∀ j a, (cell j a \ base a).card ≤ loss)
    (hCell : ∀ j a, Fintype.card L+loss ≤ (cell j a).card)
    (hUseful : ∀ j i, useful j i ⊆ cell j (source j i) ∧
      Fintype.card L+loss ≤ (useful j i).card) :
    ∃ chosen : L → U → V,
      Function.Injective (fun q : L × U => chosen q.1 q.2) ∧
      (∀ j a, chosen j a ∈ cell j a ∧ chosen j a ∈ base a) ∧
      ∀ j i, chosen j (source j i) ∈ useful j i := by
  let candidate (j : L) (a : U) :=
    if h : ∃ i, source j i = a then useful j h.choose else cell j a
  have hSubset (j : L) (a : U) : candidate j a ⊆ cell j a := by
    dsimp only [candidate]
    split_ifs with h
    · have hEq := congrArg (cell j) h.choose_spec
      exact fun x hx => hEq ▸ (hUseful j h.choose).1 hx
    · exact Subset.rfl
  have hSize (j : L) (a : U) : Fintype.card L+loss ≤ (candidate j a).card := by
    dsimp only [candidate]
    split_ifs with h
    · exact (hUseful j h.choose).2
    · exact hCell j a
  have hOverlap (j : L) (a : U) : Fintype.card L ≤ (candidate j a ∩ base a).card := by
    have hAway : (candidate j a \ base a).card ≤ loss :=
      (card_le_card (sdiff_subset_sdiff (hSubset j a) Subset.rfl)).trans (hNear j a)
    have hSplit := card_sdiff_add_card_inter (candidate j a) (base a)
    have hEnough := hSize j a
    omega
  have hRequests (a : U) :
      (((univ : Finset (L × U)).filter (fun q => q.2 = a)).card) ≤ Fintype.card L := by
    rw [←card_univ]
    refine card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_
    rintro ⟨j,u⟩ hu ⟨k,v⟩ hv hjk
    exact Prod.ext hjk ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
  obtain ⟨pick,hPick,hMember⟩ := exists_distinct_aligned_vertices base (Prod.snd : L × U → U)
    (fun q => candidate q.1 q.2) hBase (fun q => (hRequests q.2).trans (hOverlap q.1 q.2))
  refine ⟨fun j a => pick (j,a),hPick,
    fun j a => ⟨hSubset j a (hMember (j,a)).1,(hMember (j,a)).2⟩,?_⟩
  intro j i
  have h : ∃ k, source j k = source j i := ⟨i,rfl⟩
  have he := hSource j h.choose_spec
  have hChoose := (hMember (j,source j i)).1
  change pick (j,source j i) ∈ candidate j (source j i) at hChoose
  simpa only [candidate,dif_pos h,he] using hChoose

end OverfullWork.DirectedRobustExpansion
