module

public import OverfullWork.KuhnOsthusPrescribedMatchings
public import OverfullWork.KuhnOsthusCycleAbsorberReserveMiddle
public import OverfullWork.DirectedConfigurationDegrees
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset DirectedRobustExpansion
open scoped Classical

variable {V : Type*}

/-- The real arcs of a filling bijection between free endpoint sets. -/
def fillingMatchingDigraph {S T : Finset V} (f : S ≃ T) : Digraph V :=
  ⟨fun x y => ∃ a : S, a.val = x ∧ (f a).val = y⟩

theorem fillingMatchingDigraph_semidegrees [Fintype V] {S T : Finset V} (f : S ≃ T) (v : V) :
    inDegree (fillingMatchingDigraph f) v ≤ 1 ∧ outDegree (fillingMatchingDigraph f) v ≤ 1 := by
  constructor
  · apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨a, ha, hav⟩ := (mem_filter.mp hx).2
    obtain ⟨b, hb, hbv⟩ := (mem_filter.mp hy).2
    have h := f.injective (Subtype.ext (hav.trans hbv.symm))
    exact ha.symm.trans (h ▸ hb)
  · apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨a, hav, ha⟩ := (mem_filter.mp hx).2
    obtain ⟨b, hbv, hb⟩ := (mem_filter.mp hy).2
    have h : a = b := Subtype.ext (hav.trans hbv.symm)
    exact ha.symm.trans (h ▸ hb)

/-- Repeatedly fill a fixed pair in §5.1.5. The occupied vertex sets
may change in every round. The earlier filling matchings cost at
most one edge per vertex per round, and all later edges are taken
from the remaining reserve. -/
theorem exists_edge_disjoint_filling_matchings [Fintype V]
    {s : ℕ} (G : Digraph V) (A B : Finset V)
    (U W : Fin s → Finset V) (m r : ℕ) (ε η d a : ℝ)
    (hm : 0 < m) (hA : A.card = m) (hB : B.card = m)
    (hU : ∀ i, U i ⊆ A) (hW : ∀ i, W i ⊆ B) (hCards : ∀ i, (U i).card = (W i).card)
    (hPair : IsLowerSuperregularPair G ε d A B)
    (hη : 0 < η) (hηOne : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (s:ℝ) ≤ a*((m:ℝ)*η))
    (hGap : 2*η < d) (hr : 0 < r) (hCut : (m:ℝ)*η ≤ (r:ℝ))
    (hMargin : ∀ i, (r:ℝ)+((U i).card:ℝ) ≤ (d-η)*(m:ℝ)) :
    ∃ F : Fin s → Digraph V,
      (∀ i, (F i ≤ G) ∧ ∃ f : ↥(A \ U i) ≃ ↥(B \ W i), F i = fillingMatchingDigraph f) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) := by
  classical
  have hPrefix (t : ℕ) (ht : t ≤ s) :
      ∃ F : Fin t → Digraph V,
        (∀ i, (F i ≤ G) ∧ ∃ f : ↥(A \ U (Fin.castLE ht i)) ≃ ↥(B \ W (Fin.castLE ht i)),
          F i = fillingMatchingDigraph f) ∧
        Pairwise (fun i j => Disjoint (F i) (F j)) := by
    induction t with
    | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ t ih =>
      have ht' : t ≤ s := by omega
      obtain ⟨F, hOld, hDisj⟩ := ih ht'
      let H : Digraph V := ⨆ j, F j
      have hLe : H ≤ G := iSup_le fun j => (hOld j).1
      have hDeg (v : V) : inDegree H v ≤ t ∧ outDegree H v ≤ t := by
        have hOne (j : Fin t) : inDegree (F j) v ≤ 1 ∧ outDegree (F j) v ≤ 1 := by
          obtain ⟨f, hf⟩ := (hOld j).2
          rw [hf]
          exact fillingMatchingDigraph_semidegrees f v
        change inDegree (⨆ j, F j) v ≤ t ∧ outDegree (⨆ j, F j) v ≤ t
        rw [DirectedSpanningConfiguration.inDegree_iSup_of_disjoint F hDisj,
          DirectedSpanningConfiguration.outDegree_iSup_of_disjoint F hDisj]
        exact ⟨(sum_le_sum fun j _ => (hOne j).1).trans_eq (by simp),
          (sum_le_sum fun j _ => (hOne j).2).trans_eq (by simp)⟩
      have hRes := IsLowerSuperregularPair.after_bounded_arc_deletion hLe t hDeg A B
        (card_pos.mp (hA ▸ hm)) (card_pos.mp (hB ▸ hm)) m hA hB ε η d a hη hηOne ha hd hTol
        ((by exact_mod_cast ht' : (t:ℝ) ≤ s).trans hBudget) hPair
      let i := Fin.castLE ht (Fin.last t)
      obtain ⟨f, hf⟩ := IsLowerSuperregularPair.exists_matching_on_free_vertices
        (G \ H) A B (U i) (W i) d η r hRes (hU i) (hW i) (hA.trans hB.symm)
        (hCards i) hGap hr (by rw [hA]; exact hCut) (by rw [hA]; exact hMargin i)
      let new := fillingMatchingDigraph f
      have hNew : new ≤ G \ H := by
        intro x y h
        obtain ⟨a, rfl, rfl⟩ := h
        exact hf a
      have hFresh (j : Fin t) : Disjoint (F j) new := by
        apply disjoint_iff_inf_le.mpr
        intro x y h
        exact (hNew h.2).2 (Digraph.iSup_adj.mpr ⟨j, h.1⟩)
      refine ⟨Fin.snoc F new, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_last] using
            (show new ≤ G ∧ ∃ e : ↥(A \ U i) ≃ ↥(B \ W i), new = fillingMatchingDigraph e from
              ⟨fun _ _ h => (hNew h).1, f, rfl⟩)
        · rw [Fin.snoc_castSucc]
          exact hOld j
      · intro j k
        refine Fin.lastCases ?_ (fun j => ?_) j
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun k _ => ?_) k
          simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hFresh k).symm
        · refine Fin.lastCases (fun _ => ?_) (fun k h => ?_) k
          · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hFresh j
          · simpa only [Fin.snoc_castSucc] using hDisj (fun e => h (congrArg Fin.castSucc e))
  obtain ⟨F, hF, hDisj⟩ := hPrefix s le_rfl
  exact ⟨F, fun i => by simpa using hF i, hDisj⟩

/-- Pack the filling matchings across all consecutive pairs in a
family of blocks. Distinct ordered pairs are separated on at least
one endpoint side, as happens for disjoint subclusters. -/
theorem exists_edge_disjoint_filling_matchings_on_pairs [Fintype V]
    {I : Type*} {s : ℕ} (G : Digraph V) (A B : I → Finset V)
    (U W : I → Fin s → Finset V) (m r : ℕ) (ε η d a : ℝ)
    (hm : 0 < m) (hA : ∀ p, (A p).card = m) (hB : ∀ p, (B p).card = m)
    (hApart : ∀ p q, p ≠ q → Disjoint (A p) (A q) ∨ Disjoint (B p) (B q))
    (hU : ∀ p i, U p i ⊆ A p) (hW : ∀ p i, W p i ⊆ B p)
    (hCards : ∀ p i, (U p i).card = (W p i).card)
    (hPair : ∀ p, IsLowerSuperregularPair G ε d (A p) (B p))
    (hη : 0 < η) (hηOne : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (s:ℝ) ≤ a*((m:ℝ)*η))
    (hGap : 2*η < d) (hr : 0 < r) (hCut : (m:ℝ)*η ≤ (r:ℝ))
    (hMargin : ∀ p i, (r:ℝ)+((U p i).card:ℝ) ≤ (d-η)*(m:ℝ)) :
    ∃ F : I → Fin s → Digraph V,
      (∀ p i, F p i ≤ G ∧ ∃ f : ↥(A p \ U p i) ≃ ↥(B p \ W p i),
        F p i = fillingMatchingDigraph f) ∧
      Pairwise (fun i j : I × Fin s => Disjoint (F i.1 i.2) (F j.1 j.2)) := by
  classical
  have hEach (p : I) := exists_edge_disjoint_filling_matchings G (A p) (B p) (U p) (W p)
    m r ε η d a hm (hA p) (hB p) (hU p) (hW p) (hCards p) (hPair p)
    hη hηOne ha hd hTol hBudget hGap hr hCut (hMargin p)
  choose F hF hDis using hEach
  refine ⟨F, hF, ?_⟩
  rintro ⟨p, i⟩ ⟨q, j⟩ hNe
  by_cases he : p = q
  · subst q
    exact hDis p (fun h => hNe (Prod.ext rfl h))
  · obtain ⟨f, hf⟩ := (hF p i).2
    obtain ⟨g, hg⟩ := (hF q j).2
    change Disjoint (F p i) (F q j)
    rw [hf, hg, disjoint_iff_inf_le]
    intro x y h
    obtain ⟨u, hu, hv⟩ := h.1
    obtain ⟨w, hw, hz⟩ := h.2
    rcases hApart p q he with hA' | hB'
    · exact disjoint_left.mp hA' (hu ▸ sdiff_subset u.prop) (hw ▸ sdiff_subset w.prop)
    · exact disjoint_left.mp hB' (hv ▸ sdiff_subset (f u).prop) (hz ▸ sdiff_subset (g w).prop)

end OverfullWork.ChenShan
