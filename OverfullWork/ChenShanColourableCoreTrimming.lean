module

public import OverfullWork.ChenShanBalancedCoreDeletion
public import OverfullWork.ChenShanCriticalCore
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The divisible recut in §5.1.1, with a proper coloring of the
enlarged exterior from Lemma 3.7. -/
theorem exists_divisible_colourable_core_trimming
    (M : MultiGraph V) (H : SimpleGraph V) [DecidableRel H.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (hSize : A.card = B.card)
    (hSupport : ∀ x y, H.Adj x y → x ∈ A ∪ B ∧ y ∈ A ∪ B)
    (k a b : ℕ) (hb : 0 < b)
    (hRegular : ∀ v, (M.addCopies (MultiGraph.ofSimpleGraph H)).degree v = k)
    (hSmall : ∀ v ∈ A ∪ B, M.degree v ≤ a) (hColour : Nonempty (M.EdgeColoring k))
    (hSlack : 3*(a+2*b) ≤ k)
    {ν τ : ℝ} (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ < 1/4)
    (hRoom : ((b-1 : ℕ):ℝ) ≤ ν*A.card)
    (hExp : ExpandsAcross H ν τ A B) :
    ∃ D E : Finset V, D ⊆ A ∧ E ⊆ B ∧ (D ∪ E).card < 2*b ∧
      (A \ D).card = (B \ E).card ∧ b ∣ (A \ D).card ∧
      ExpandsAcross H (ν/2) (2*τ) (A \ D) (B \ E) ∧
      let N := M.addCopies (MultiGraph.ofSimpleGraph (restoredCoreEdges H (D ∪ E)))
      Nonempty (N.EdgeColoring k) ∧
      ∀ v ∈ (A \ D) ∪ (B \ E), N.degree v ≤ a+(D ∪ E).card := by
  obtain ⟨D,E,hD,hE,hCard,hEq,hDiv,hRob,_,_⟩ :=
    exists_divisible_robust_core_trimming H A B hAB hSize b hb hν hντ hτ hRoom hExp
  have hY : D ∪ E ⊆ A ∪ B := union_subset (hD.trans subset_union_left) (hE.trans subset_union_right)
  have hSlack' : 3*(a+(D ∪ E).card) < k := by omega
  obtain ⟨hC,hDegree⟩ := colourable_exterior_after_core_deletion M H (A ∪ B) (D ∪ E)
    hY hSupport k a hRegular hSmall hColour hSlack'
  refine ⟨D,E,hD,hE,hCard,hEq,hDiv,hRob,hC,?_⟩
  intro v hv
  have hv' : v ∈ (A ∪ B) \ (D ∪ E) := by
    rcases mem_union.mp hv with h | h
    · obtain ⟨ha,hd⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨mem_union_left _ ha,fun hy =>
        (mem_union.mp hy).elim hd (fun he => (Finset.disjoint_left.mp hAB ha) (hE he))⟩
    · obtain ⟨hb',he⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨mem_union_right _ hb',fun hy =>
        (mem_union.mp hy).elim (fun hd => (Finset.disjoint_left.mp hAB (hD hd)) hb') he⟩
  exact hDegree v hv'

end OverfullWork.ChenShan
