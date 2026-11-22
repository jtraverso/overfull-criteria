module

public import OverfullWork.KuhnOsthusPathFactorCompletion
public import OverfullWork.SequentialFactorMerges

@[expose] public section


/-! The all-successor-pair case of Kühn–Osthus Lemma 6.4 used
in §8.2. A vertex free in both directions joins the two consecutive
pairs. Each replacement is made on free sources only. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

def successorReserve (R : Digraph V) (σ : Equiv.Perm V) (S : Finset V) : Digraph S :=
  ⟨fun x y => R.Adj x (σ y)⟩

theorem successor_target_is_free_source (D R : Digraph V) {I : Type*}
    (cluster : V → I) (s : Equiv.Perm I) (σ : Equiv.Perm V)
    (hKeep : ∀ x y, D.Adj x y → σ x = y)
    (hNew : ∀ x, (∃ y, D.Adj x y) ∨ (R.Adj x (σ x) ∧ cluster (σ x) = s (cluster x)))
    (i : I) {v : V} (hv : v ∈ freeIn D cluster (s i)) :
    σ.symm v ∈ freeOut D cluster i := by
  have hTarget := mem_freeIn.mp hv
  have hEmpty : ¬ ∃ w, D.Adj (σ.symm v) w := by
    rintro ⟨w,hw⟩
    have he := hKeep (σ.symm v) w hw
    rw [σ.apply_symm_apply] at he
    exact hTarget.2 ⟨σ.symm v,he.symm ▸ hw⟩
  have hRoute := (hNew (σ.symm v)).resolve_left hEmpty
  rw [σ.apply_symm_apply] at hRoute
  exact mem_freeOut.mpr ⟨s.injective (hRoute.2.symm.trans hTarget.1),hEmpty⟩

/-- Replace the cut matchings independently. A vertex free in both
directions witnesses the connection between consecutive cuts, and
acyclicity makes every old orbit meet at least one cut. -/
theorem hamilton_completion_of_successor_cut_merges {n : ℕ} (D R : Digraph V)
    (cluster : V → Fin (n+1)) (σ : Equiv.Perm V)
    (hAcyclic : NoDirectedCycle D)
    (hKeep : ∀ x y, D.Adj x y → σ x = y)
    (hNew : ∀ x, (∃ y, D.Adj x y) ∨
      (R.Adj x (σ x) ∧ cluster (σ x) = finRotate (n+1) (cluster x)))
    (hOverlap : ∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ freeOut D cluster i)
    (hStep : ∀ i (ρ : Equiv.Perm V),
      let S := freeOut D cluster i
      let B := successorReserve R σ S
      ∃ M : Equiv.Perm (↑S), (∀ x, B.Adj x (M x)) ∧
        (∀ x y, ρ.SameCycle x y → (replacedSuccessor ρ S M).SameCycle x y) ∧
        ∀ x y, touchesCut ρ S x → touchesCut ρ S y →
          (replacedSuccessor ρ S M).SameCycle x y) :
    ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
      (∀ x y, D.Adj x y → ρ x = y) ∧ (∀ x, (D ⊔ R).Adj x (ρ x)) := by
  let s := finRotate (n+1)
  let S := freeOut D cluster
  let B i := successorReserve R σ (S i)
  let r (i j : Fin (n+1)) : Prop := i.val+1 = j.val
  have hDis (i j : Fin (n+1)) (hne : i ≠ j) : Disjoint (S i) (S j) := by
    rw [disjoint_left]
    intro v hi hj
    exact hne ((mem_freeOut.mp hi).1.symm.trans (mem_freeOut.mp hj).1)
  have hCover (v : V) : ∃ i, touchesCut σ (S i) v := by
    obtain ⟨w,hw,he⟩ := every_completed_orbit_uses_a_free_source D hAcyclic σ hKeep v
    exact ⟨cluster w,w,mem_freeOut.mpr ⟨rfl,he⟩,hw⟩
  have hBridge (i j : Fin (n+1)) (hij : r i j) :
      ∃ x y, touchesCut σ (S i) x ∧ touchesCut σ (S j) y ∧
        ∃ l : List V, x ∈ l ∧ y ∈ l ∧ l.IsChain (fun a b => (∀ l, a ∉ S l) ∧ σ a = b) := by
    change i.val+1 = j.val at hij
    have hNotLast : i ≠ Fin.last n := by
      intro h
      subst i
      have hlt := j.isLt
      simp only [Fin.val_last] at hij
      omega
    have he : s i = j := Fin.ext ((coe_finRotate_of_ne_last hNotLast).trans hij)
    obtain ⟨v,hvIn,hvOut⟩ := hOverlap j
    have hv : v ∈ freeIn D cluster (s i) := he.symm ▸ hvIn
    have hSource := successor_target_is_free_source D R cluster s σ hKeep hNew i hv
    have hSame : σ.SameCycle v (σ.symm v) :=
      Equiv.Perm.sameCycle_symm_apply_right.mpr (Equiv.Perm.SameCycle.refl σ v)
    exact ⟨v,v,⟨σ.symm v,hSource,hSame⟩,touchesCut_of_mem σ hvOut,
      [v],by simp,by simp,by simp⟩
  have hNonempty (i : Fin (n+1)) : (S i).Nonempty := by
    obtain ⟨v,_,hv⟩ := hOverlap i
    exact ⟨v,hv⟩
  obtain ⟨ρ,hOld,hMerged,hPreserve,hUse⟩ := exists_sequential_cut_merges σ (n+1) S B hDis
    (fun i ρ => by
      obtain ⟨M,hM,hOld,hTouch⟩ := hStep i ρ
      exact ⟨M,hM,hOld,fun x hx y hy =>
        hTouch x y (touchesCut_of_mem ρ hx) (touchesCut_of_mem ρ hy)⟩)
  have hCycle := spanning_cycle_of_cut_merge_bridges σ ρ S r 0 hNonempty
    (cutOrder_connected n) hCover hOld hMerged hPreserve hBridge
  have hPreserve' (x y : V) (h : D.Adj x y) : ρ x = y := by
    refine (hPreserve x (fun i hi => (mem_freeOut.mp hi).2 ⟨y,h⟩)).trans (hKeep x y h)
  refine ⟨ρ,hCycle,hPreserve',?_⟩
  intro x
  by_cases hx : ∃ y, D.Adj x y
  · obtain ⟨y,hy⟩ := hx
    exact (Digraph.sup_adj _ _ _ _).mpr (Or.inl ((hPreserve' x y hy).symm ▸ hy))
  · have hs : x ∈ S (cluster x) := mem_freeOut.mpr ⟨rfl,hx⟩
    obtain ⟨M,hM,hArc⟩ := hUse (cluster x)
    have he := hArc ⟨x,hs⟩
    refine (Digraph.sup_adj _ _ _ _).mpr (Or.inr ?_)
    rw [he]
    exact hM ⟨x,hs⟩

/-- Given the numeric reserve conditions for the free successor pairs,
turn the factor into one cycle without changing its prescribed arcs. -/
theorem exists_hamilton_completion_of_successor_reserves
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (D R : Digraph W)
      (cluster : W → Fin (n+1)) (σ : Equiv.Perm W),
      NoDirectedCycle D →
      (∀ x y, D.Adj x y → σ x = y) →
      (∀ x, (∃ y, D.Adj x y) ∨
        (R.Adj x (σ x) ∧ cluster (σ x) = finRotate (n+1) (cluster x))) →
      (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ freeOut D cluster i) →
      (∀ i, N ≤ (freeOut D cluster i).card) →
      ν ≤ d*τ → γ ≤ d →
      (∀ i, ∀ A B : Finset (freeOut D cluster i),
        ε*((freeOut D cluster i).card:ℝ) ≤ (A.card:ℝ) →
        ε*((freeOut D cluster i).card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences (successorReserve R σ (freeOut D cluster i)) A B:ℝ)) →
      (∀ i v, d*((freeOut D cluster i).card:ℝ) ≤
        (inDegree (successorReserve R σ (freeOut D cluster i)) v:ℝ)) →
      (∀ i v, d*((freeOut D cluster i).card:ℝ) ≤
        (outDegree (successorReserve R σ (freeOut D cluster i)) v:ℝ)) →
      ∃ ρ : Equiv.Perm W, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, D.Adj x y → ρ x = y) ∧ (∀ x, (D ⊔ R).Adj x (ρ x)) := by
  obtain ⟨N,hN⟩ := exists_touched_cycle_merge.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ n D R cluster σ hAcyclic hKeep hNew hOverlap hSize hCost hDegrees hRect hIn hOut
  apply hamilton_completion_of_successor_cut_merges D R cluster σ hAcyclic hKeep hNew hOverlap
  intro i ρ
  let S := freeOut D cluster i
  let B := successorReserve R σ S
  obtain ⟨M,hM,T,z,_,_,hChain,hSupport⟩ := hN ρ S B ⊥ 0 (hSize i) bot_le
    (by simpa using mul_le_mul_of_nonneg_right hCost (show 0 ≤ (S.card:ℝ) by positivity))
    (by simpa using mul_le_mul_of_nonneg_right hDegrees (show 0 ≤ (S.card:ℝ) by positivity))
    (hRect i) (hIn i) (hOut i) (fun _ => by simp [inDegree,inNeighbours,outDegree,Digraph.bot_adj])
  exact ⟨M,fun x => ((Digraph.sdiff_adj _ _ _ _).mp (hM x)).1,
    coarsening_of_touched_cycle ρ S M T z hChain hSupport⟩

end OverfullWork.DirectedRobustExpansion
