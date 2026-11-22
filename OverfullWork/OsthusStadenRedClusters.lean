module

public import OverfullWork.OsthusStadenLayerUnwinding

@[expose] public section


/-! The separation and size bound in Osthus–Staden §5.4 (Red4 and Red5),
given the prescribed clean clusters and the halving of the refined cells. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The original factor type fixes both the label modulo `p` and which
half of that cell is eligible. -/
def redPhase (p t : ℕ) : ZMod p × Bool :=
  (t, decide (p ≤ t % (2*p)))

/-- The rule in §5.4 selects exactly one half-cell in each non-clean
intermediate cluster. The first coordinate also fixes its refined cell. -/
def redHalfEligible {I : Type*} (p t : ℕ) (Clean : I → Prop)
    (i : I) (a : ZMod p × Bool) : Prop :=
  ¬ Clean i ∧ a = redPhase p t

theorem existsUnique_redHalf {I : Type*} {p t : ℕ} {Clean : I → Prop} {i : I}
    (hi : ¬ Clean i) : ∃! a, redHalfEligible p t Clean i a :=
  ⟨redPhase p t, ⟨hi, rfl⟩, fun _ h => h.2⟩

/-- Both orientations of exceptional adjacency are confined to the same
half of each refined cell when the exceptional edges obey the red rule. -/
theorem red_exceptional_neighbors_le_half {I W : Type*} {p t m : ℕ}
    {Clean : I → Prop} (i : I) (d : ZMod p)
    (half : Bool → Finset W) (neighbors : Finset W)
    (hHalf : ∀ b, (half b).card ≤ m/2)
    (hRed : ∀ v ∈ neighbors, ∃ b, v ∈ half b ∧ redHalfEligible p t Clean i (d,b)) :
    neighbors.card ≤ m/2 := by
  refine (Finset.card_le_card (t := half (redPhase p t).2) ?_).trans (hHalf _)
  intro v hv
  obtain ⟨b, hMem, hEligible⟩ := hRed v hv
  have hb : b = (redPhase p t).2 := congrArg Prod.snd hEligible.2
  simpa only [hb] using hMem

/-- Clean final positions and the common label imposed by the red rule
give (Red5) along every second-level unwound cycle. -/
theorem red_clusters_distance {A : Type*} {n p t : ℕ}
    (F : Equiv.Perm A) (order : Fin n × ZMod p → A) (Clean : Fin n → Prop)
    (hClean : ∀ i : Fin n, n-2 ≤ i.val → Clean i)
    (hDist : ∀ (x y : Fin n × ZMod p) k, 0 < k →
      x.1.val < n-2 → y.1.val < n-2 → x.2 = y.2 →
      (F^k) (order x) = order y → p ≤ k)
    {x y : Fin n × ZMod p} {b c : Bool}
    (hx : redHalfEligible p t Clean x.1 (x.2,b))
    (hy : redHalfEligible p t Clean y.1 (y.2,c))
    {k : ℕ} (hk : 0 < k) (hPath : (F^k) (order x) = order y) : p ≤ k := by
  apply hDist x y k hk
  · exact lt_of_not_ge (fun h => hx.1 (hClean _ h))
  · exact lt_of_not_ge (fun h => hy.1 (hClean _ h))
  · exact (congrArg Prod.fst hx.2).trans (congrArg Prod.fst hy.2).symm
  · exact hPath

/-- In an adapted primary cluster, choose `m−1` non-clean cells in
each half of a `2m`-cell refinement, as in equation (21). Assigning the
two sets opposite orientations gives disjoint in-red and out-red cells. -/
theorem exists_directional_red_cells {I : Type*} [DecidableEq I]
    (upper lower : Finset I) (clean : I) (m : ℕ)
    (hUpper : upper.card = m) (hLower : lower.card = m) (hDis : Disjoint upper lower) :
    ∃ inRed outRed : Finset I,
      inRed ⊆ upper.erase clean ∧ outRed ⊆ lower.erase clean ∧
      inRed.card = m-1 ∧ outRed.card = m-1 ∧ Disjoint inRed outRed := by
  have hCard (cells : Finset I) (h : cells.card = m) : m-1 ≤ (cells.erase clean).card := by
    by_cases hMem : clean ∈ cells
    · rw [Finset.card_erase_of_mem hMem,h]
    · rw [Finset.erase_eq_of_notMem hMem,h]
      exact Nat.sub_le _ _
  obtain ⟨inRed,hin,hinCard⟩ := Finset.exists_subset_card_eq (hCard upper hUpper)
  obtain ⟨outRed,hout,houtCard⟩ := Finset.exists_subset_card_eq (hCard lower hLower)
  exact ⟨inRed,outRed,hin,hout,hinCard,houtCard,
    hDis.mono (hin.trans (Finset.erase_subset _ _)) (hout.trans (Finset.erase_subset _ _))⟩

end OverfullWork.DirectedRobustExpansion
