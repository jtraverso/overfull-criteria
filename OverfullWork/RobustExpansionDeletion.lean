module

public import OverfullWork.SparseDeficitExpansion
public import OverfullWork.TwoColourTrimming

@[expose] public section


/-! # Robust expansion after actual edge deletions

Deleting a graph of maximum degree at most `d` lowers the robust-neighbour
threshold by at most `d`, while preserving the original expansion gain.
Finite unions of two-degree layers pay at most twice their number. These
estimates authorize only the displayed finite degree budget, not arbitrarily
many trimming rounds. A reserved subgraph interface requires that actual
subgraph and never asserts its existence.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Every neighbour removed from `S` was incident with a deleted edge. -/
theorem neighboursIn_le_sdiff_add_degree (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (S : Finset V) (v : V) :
    neighboursIn G S v≤neighboursIn (G\F) S v+F.degree v := by
  have hs : G.neighborFinset v∩S⊆((G\F).neighborFinset v∩S)∪F.neighborFinset v := by
    intro x hx
    obtain ⟨hxG,hxS⟩:=mem_inter.mp hx
    have hG:=(mem_neighborFinset G v x).mp hxG
    by_cases hF:F.Adj v x
    · exact mem_union_right _ ((mem_neighborFinset F v x).mpr hF)
    · exact mem_union_left _ (mem_inter.mpr
        ⟨(mem_neighborFinset (G\F) v x).mpr ⟨hG,hF⟩,hxS⟩)
  have hh:=(card_le_card hs).trans (card_union_le _ _)
  simpa only [neighboursIn,filter_mem_eq_inter,card_neighborFinset_eq_degree] using hh

/-- An actual robust neighbour survives at the reduced threshold. -/
theorem neighbourhood_subset_sdiff (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (r d : ℕ)
    (hF : ∀v,F.degree v≤d) (S : Finset V) :
    neighbourhood G r S⊆neighbourhood (G\F) (r-d) S := by
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh:=(mem_filter.mp hv).2
  have hl:=neighboursIn_le_sdiff_add_degree G F S v
  have hd:=hF v
  omega

/-- The expansion gain remains `r`; only the neighbour threshold pays
for the deleted degree. This is stronger than conventional robustness. -/
theorem robust_gain_after_deletion (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (r d t : ℕ)
    (hrobust : IsRobustAt G r t) (hF : ∀v,F.degree v≤d) :
    ∀S : Finset V,t≤S.card → S.card+t≤Fintype.card V →
      S.card+r≤(neighbourhood (G\F) (r-d) S).card := by
  intro S hlo hhi
  exact (hrobust S hlo hhi).trans (card_le_card (neighbourhood_subset_sdiff G F r d hF S))

theorem isRobustAt_sdiff (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (r d t : ℕ)
    (hrobust : IsRobustAt G r t) (hF : ∀v,F.degree v≤d) :
    IsRobustAt (G\F) (r-d) t := by
  intro S hlo hhi
  have hh:=robust_gain_after_deletion G F r d t hrobust hF S hlo hhi
  omega

/-- The nontrivial deletion range has a genuinely positive threshold. -/
theorem positive_threshold_after_deletion (r d : ℕ) (hd : d<r) : 0<r-d := by omega

/-- Adding edges preserves the robust-neighbour sets at the same threshold. -/
theorem neighbourhood_mono_graph (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G≤H) (r : ℕ) (S : Finset V) :
    neighbourhood G r S⊆neighbourhood H r S := by
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hs : G.neighborFinset v∩S⊆H.neighborFinset v∩S := by
    intro x hx
    exact mem_inter.mpr ⟨(mem_neighborFinset H v x).mpr
      (hGH ((mem_neighborFinset G v x).mp (mem_inter.mp hx).1)),(mem_inter.mp hx).2⟩
  exact (mem_filter.mp hv).2.trans (card_le_card hs)

theorem isRobustAt_mono_graph (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G≤H) (r t : ℕ)
    (hrobust : IsRobustAt G r t) : IsRobustAt H r t := by
  intro S hlo hhi
  exact (hrobust S hlo hhi).trans (card_le_card (neighbourhood_mono_graph G H hGH r S))

/-- A supplied actual reserve remains robust in the remaining graph.
Existence of a suitable reserve is a separate construction problem. -/
theorem isRobustAt_of_reserved_subgraph (G F Γ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] [DecidableRel Γ.Adj] (r t : ℕ)
    (hΓ : Γ≤G\F) (hrobust : IsRobustAt Γ r t) : IsRobustAt (G\F) r t :=
  isRobustAt_mono_graph Γ (G\F) hΓ r t hrobust

/-- The actual union of the first `m` layers. -/
def layerUnion (L : ℕ→SimpleGraph V) : ℕ→SimpleGraph V
  | 0 => ⊥
  | m+1 => layerUnion L m⊔L m

omit [Fintype V] [DecidableEq V] in
@[simp] theorem layerUnion_zero (L : ℕ→SimpleGraph V) : layerUnion L 0=⊥ := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem layerUnion_succ (L : ℕ→SimpleGraph V) (m : ℕ) :
    layerUnion L (m+1)=layerUnion L m⊔L m := rfl

/-- Overlapping layers only improve this bound; disjointness is unnecessary. -/
theorem degree_layerUnion_le (L : ℕ→SimpleGraph V) (m : ℕ)
    (hL : ∀i<m,∀v,(L i).degree v≤2) : ∀v,(layerUnion L m).degree v≤2*m := by
  classical
  induction m with
  | zero =>
    intro v
    have he : (layerUnion L 0).neighborFinset v=∅ := by
      ext w
      rw [(layerUnion L 0).mem_neighborFinset v w]
      change False ↔ w∈(∅:Finset V)
      simp only [notMem_empty]
    rw [←card_neighborFinset_eq_degree,he,card_empty]
  | succ m ih =>
    intro v
    have hh:=ih (fun i hi=>hL i (by omega) ) v
    have hs : (layerUnion L (m+1)).degree v≤(layerUnion L m).degree v+(L m).degree v := by
      rw [layerUnion_succ,←card_neighborFinset_eq_degree,neighborFinset_sup]
      exact card_union_le _ _
    have hd:=hL m (by omega) v
    omega

omit [Fintype V] [DecidableEq V] in
theorem layerUnion_le (G : SimpleGraph V) (L : ℕ→SimpleGraph V) (m : ℕ)
    (hL : ∀i<m,L i≤G) : layerUnion L m≤G := by
  induction m with
  | zero => exact bot_le
  | succ m ih => exact sup_le (ih (fun i hi=>hL i (by omega))) (hL m (by omega))

/-- At most `2m` robust neighbours are lost after `m` actual two-degree layers. -/
theorem isRobustAt_after_layers (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ℕ→SimpleGraph V) (m r t : ℕ)
    (hrobust : IsRobustAt G r t) (hL : ∀i<m,∀v,(L i).degree v≤2) :
    IsRobustAt (G\layerUnion L m) (r-2*m) t := by
  classical
  exact isRobustAt_sdiff G (layerUnion L m) r (2*m) t hrobust (degree_layerUnion_le L m hL)

/-- The precise positive-threshold range of this finite deletion argument. -/
theorem isRobustAt_after_layers_positive (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ℕ→SimpleGraph V) (m r t : ℕ)
    (hrobust : IsRobustAt G r t) (hL : ∀i<m,∀v,(L i).degree v≤2)
    (hbudget : 2*m<r) :
    0<r-2*m ∧ IsRobustAt (G\layerUnion L m) (r-2*m) t :=
  ⟨by omega,isRobustAt_after_layers G L m r t hrobust hL⟩

omit [Fintype V] [DecidableEq V] in
/-- Exact deletion bookkeeping for the actual finite union. -/
theorem sdiff_layerUnion_succ (G : SimpleGraph V) (L : ℕ→SimpleGraph V) (m : ℕ) :
    G\layerUnion L (m+1)=(G\layerUnion L m)\L m := by
  ext x y
  simp only [layerUnion_succ,sdiff_adj,sup_adj]
  tauto

/-- When each actual layer satisfies the full degree demands in its
current residue, the maximum-degree drift telescopes exactly. These
finite hypotheses do not supply any next layer or preserve no-overfullness. -/
theorem maxDegree_after_layers (G : SimpleGraph V) (L : ℕ→SimpleGraph V) (m : ℕ)
    (hstage : ∀i<m,
      2≤(G\layerUnion L i).maxDegree ∧ L i≤G\layerUnion L i ∧
      (∀v,(L i).degree v≤2) ∧
      (∀v,(G\layerUnion L i).degree v+2≤(G\layerUnion L i).maxDegree+(L i).degree v)) :
    (G\layerUnion L m).maxDegree=G.maxDegree-2*m := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hD,hle,hdeg,hdemand⟩:=hstage m (by omega)
    have hstep:=TwoColourTrimming.maxDegree_sdiff_of_degree_demands _ _ hD hle hdeg hdemand
    have hi:=ih (fun i hi=>hstage i (by omega))
    have heq : (G\layerUnion L (m+1)).maxDegree=((G\layerUnion L m)\L m).maxDegree := by
      simp only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
        ←Nat.card_eq_fintype_card,sdiff_layerUnion_succ]
    omega

/-- Exact maximum-degree loss and the same per-vertex deletion budget
make every degree deficit nonincreasing. -/
theorem deficit_sdiff_le_of_exact_drop (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (d : ℕ)
    (hFG : F≤G)
    (hF : ∀v,F.degree v≤d) (hdrop : (G\F).maxDegree=G.maxDegree-d) (v : V) :
    (G\F).maxDegree-(G\F).degree v≤G.maxDegree-G.degree v := by
  have hs:=MaximumMatching.degree_sdiff_add_of_le G F hFG v
  have hh:=hF v
  have hg:=G.degree_le_maxDegree v
  rw [hdrop]
  omega

theorem totalDeficit_sdiff_le_of_exact_drop (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (d : ℕ)
    (hFG : F≤G)
    (hF : ∀v,F.degree v≤d) (hdrop : (G\F).maxDegree=G.maxDegree-d) :
    SparseDeficitCore.totalDeficit (G\F) (G\F).maxDegree≤
      SparseDeficitCore.totalDeficit G G.maxDegree := by
  apply sum_le_sum
  intro v _
  exact deficit_sdiff_le_of_exact_drop G F d hFG hF hdrop v

end OverfullWork.RobustExpansion
