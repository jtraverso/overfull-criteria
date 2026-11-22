module

public import OverfullWork.MatchingTutte
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section


/-! # The one low-clique component and the exact Tutte parity correction -/
namespace OverfullWork.MaximumMatching
open SimpleGraph Finset
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 2000000

/-- Deleting vertices in exactly the representation used by Mathlib's Tutte theorem. -/
noncomputable def residual (G : SimpleGraph W) (U : Set W) :
    SimpleGraph ((⊤ : G.Subgraph).deleteVerts U).verts :=
  ((⊤ : G.Subgraph).deleteVerts U).coe

noncomputable def residualLow (G : SimpleGraph W) (L U : Set W) :
    Set ((⊤ : G.Subgraph).deleteVerts U).verts := {x | x.val∈L}

/-- Odd components containing no surviving low vertex. -/
noncomputable def highOddComponents (G : SimpleGraph W) (L U : Set W) :
    Finset (residual G U).ConnectedComponent :=
  (residual G U).oddComponents.toFinset.filter fun C => Disjoint C.supp (residualLow G L U)

omit [Fintype W] in
private theorem clique_components_subsingleton (H : SimpleGraph W) (L : Set W)
    (hL : H.IsClique L) :
    Set.Subsingleton {C : H.ConnectedComponent | ¬Disjoint C.supp L} := by
  intro C hC D hD
  obtain ⟨x,hxC,hxL⟩:=Set.not_disjoint_iff.mp hC
  obtain ⟨y,hyD,hyL⟩:=Set.not_disjoint_iff.mp hD
  by_cases hxy : x=y
  · subst y
    exact ConnectedComponent.eq_of_common_vertex hxC hyD
  · have hyC:=C.mem_supp_of_adj_mem_supp hxC (hL hxL hyL hxy)
    exact ConnectedComponent.eq_of_common_vertex hyC hyD

/-- A clique can meet at most one connected component, including odd components. -/
theorem odd_components_le_high_add_one (H : SimpleGraph W) (L : Set W)
    (hL : H.IsClique L) :
    H.oddComponents.ncard≤
      (H.oddComponents.toFinset.filter fun C => Disjoint C.supp L).card+1 := by
  classical
  let O:=H.oddComponents.toFinset
  have hsmall : (O.filter fun C => ¬Disjoint C.supp L).card≤1 := by
    apply Finset.card_le_one.mpr
    intro C hC D hD
    exact clique_components_subsingleton H L hL (mem_filter.mp hC).2 (mem_filter.mp hD).2
  have hsum:=Finset.card_filter_add_card_filter_not (s:=O) (fun C => Disjoint C.supp L)
  have hcard : O.card=H.oddComponents.ncard := (Set.ncard_eq_toFinset_card' _).symm
  change _≤(O.filter fun C => Disjoint C.supp L).card+1
  omega

private def residualVertexEquiv (G : SimpleGraph W) (U : Set W) :
    ((⊤ : G.Subgraph).deleteVerts U).verts ≃ ↥Uᶜ where
  toFun x:=⟨x.val,x.property.2⟩
  invFun x:=⟨x.val,⟨by trivial,x.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [DecidableEq W] in
theorem residual_odd_components_parity (G : SimpleGraph W) (U : Set W)
    (heven : Even (Fintype.card W)) :
    Odd (residual G U).oddComponents.ncard ↔ Odd U.ncard := by
  have hc : Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts=Uᶜ.ncard := by
    rw [←Nat.card_coe_set_eq]
    exact Nat.card_congr (residualVertexEquiv G U)
  rw [SimpleGraph.odd_ncard_oddComponents,hc]
  exact Set.odd_ncard_compl_iff (by simpa only [Nat.card_eq_fintype_card] using heven) U

omit [Fintype W] [DecidableEq W] in
theorem residualLow_isClique (G : SimpleGraph W) (L U : Set W) (hL : G.IsClique L) :
    (residual G U).IsClique (residualLow G L U) := by
  intro x hx y hy hne
  apply Subgraph.Adj.coe
  apply Subgraph.deleteVerts_adj.mpr
  refine ⟨by trivial,x.property.2,by trivial,y.property.2,?_⟩
  exact hL hx hy (fun he => hne (Subtype.ext he))

/-- The potential extra odd low component is excluded by parity, not assumed away. -/
theorem tutte_component_bound (G : SimpleGraph W) (L U : Set W)
    (heven : Even (Fintype.card W)) (hL : G.IsClique L)
    (hhigh : (highOddComponents G L U).card≤U.ncard) :
    (residual G U).oddComponents.ncard≤U.ncard := by
  have htotal:=odd_components_le_high_add_one (residual G U) (residualLow G L U)
    (residualLow_isClique G L U hL)
  have hpar:=residual_odd_components_parity G U heven
  change (residual G U).oddComponents.ncard≤(highOddComponents G L U).card+1 at htotal
  simp only [Nat.odd_iff] at hpar
  omega

/-- Only the high-component cut estimate remains to apply Tutte. -/
theorem exists_perfectMatching_of_high_components_bound (G : SimpleGraph W) (L : Set W)
    (heven : Even (Fintype.card W)) (hL : G.IsClique L)
    (hhigh : ∀U : Set W,(highOddComponents G L U).card≤U.ncard) :
    ∃P : G.Subgraph,P.IsPerfectMatching := by
  apply SimpleGraph.tutte.mpr
  intro U
  exact not_lt_of_ge (tutte_component_bound G L U heven hL (hhigh U))

end OverfullWork.MaximumMatching
