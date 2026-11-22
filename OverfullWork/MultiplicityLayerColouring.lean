module

public import OverfullWork.SimpleColouringBridge
public import OverfullWork.ColouredLayerSum

@[expose] public section


/-! # Explicit simple multiplicity layers and palette enlargement

The order bound uses one proper simple-graph coloring per copy level.
This is an actual coloring construction, with no multigraph Vizing
theorem supplied as a premise.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def zeroCopies : MultiGraph V where
  mult _ := 0
  loopless _ _ := rfl

def zeroColouring (k : ℕ) : (zeroCopies : MultiGraph V).EdgeColoring k where
  col _ _ := 0
  sum_col _ := by simp [zeroCopies]
  proper _ _ := by simp

theorem EdgeColoring.enlarge {M : MultiGraph V} {k l : ℕ} (C : M.EdgeColoring k)
    (hkl : k ≤ l) : Nonempty (M.EdgeColoring l) := by
  have hM : M.addCopies zeroCopies = M := by apply ext_mult;intro e;exact Nat.add_zero _
  have hc := C.addCopies (zeroColouring (V := V) (l-k))
  rw [hM,Nat.add_sub_of_le hkl] at hc
  exact ⟨hc⟩

def copyLevel (M : MultiGraph V) (j : ℕ) : MultiGraph V where
  mult e := if j < M.mult e then 1 else 0
  loopless e he := by rw [M.loopless e he];simp

theorem copyLevel_simple (M : MultiGraph V) (j : ℕ) : ∀ e, (M.copyLevel j).mult e ≤ 1 := by
  intro e
  dsimp only [copyLevel]
  split_ifs <;> omega

theorem copyLevel_sum (M : MultiGraph V) (μ : ℕ) (hμ : ∀ e, M.mult e ≤ μ) :
    OverfullWork.CanonicalPairTriangle.sumCopies univ (fun j : Fin μ => M.copyLevel j.val) = M := by
  apply ext_mult
  intro e
  change (∑ j : Fin μ, if j.val < M.mult e then 1 else 0) = M.mult e
  rw [←card_filter]
  have hc : (range (M.mult e)).card =
      (univ.filter (fun j : Fin μ => j.val < M.mult e)).card := by
    apply card_bij (fun j hj => (⟨j,(mem_range.mp hj).trans_le (hμ e)⟩ : Fin μ))
    · intro j hj
      exact mem_filter.mpr ⟨mem_univ _,mem_range.mp hj⟩
    · intro j hj k hk h
      exact congrArg Fin.val h
    · intro j hj
      exact ⟨j.val,mem_range.mpr (mem_filter.mp hj).2,Fin.ext rfl⟩
  simpa only [card_range] using hc.symm

theorem colourable_by_order_times_multiplicity (M : MultiGraph V) (μ : ℕ)
    (hV : 0 < Fintype.card V) (hμ : ∀ e, M.mult e ≤ μ) :
    Nonempty (M.EdgeColoring (μ*Fintype.card V)) := by
  have hcol : ∀ j : Fin μ, Nonempty ((M.copyLevel j.val).EdgeColoring (Fintype.card V)) := by
    intro j
    let L := M.copyLevel j.val
    have hs := M.copyLevel_simple j.val
    have hdeg : ∀ v, L.degree v ≤ Fintype.card V-1 := by
      intro v
      rw [←L.of_supportGraph hs,degree_ofSimpleGraph]
      have hh := L.supportGraph.degree_lt_card_verts v
      omega
    have hc := exists_edgeColoring_simple L (Fintype.card V-1) hs hdeg
    rwa [Nat.sub_add_cancel hV] at hc
  let C := fun j => Classical.choice (hcol j)
  have hc := OverfullWork.ColouredLayerSum.colouring (fun j : Fin μ => M.copyLevel j.val) C
  rw [M.copyLevel_sum μ hμ] at hc
  exact ⟨hc⟩

end SimpleGraph.MultiGraph
