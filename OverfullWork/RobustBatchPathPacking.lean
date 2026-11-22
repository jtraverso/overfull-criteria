module

public import OverfullWork.DenseBatchPathPacking
public import OverfullWork.RobustRegularFactorization

@[expose] public section


/-! Spanning linkage in the successive ordinary residues of CMS §5.2. -/
namespace OverfullWork.DenseBatchPathPacking

open SimpleGraph RobustExpansion
open scoped Classical
universe u

/-- Pack disjoint rounds of prescribed spanning paths in a robust graph.
Every intermediate residue loses at most two incident edges per completed
round. Endpoints can recur in different rounds. -/
theorem exists_robust_packing (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (ℓ p : ℕ) (a b : Fin ℓ → Fin p → V),
      N ≤ Fintype.card V → IsRealRobust G (2*ν) τ →
      (∀ v, α*(Fintype.card V:ℝ)+2*(ℓ:ℝ) ≤ (G.degree v:ℝ)) →
      2*(ℓ:ℝ) ≤ ν*(Fintype.card V:ℝ) → 0 < p → (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      (∀ j, Function.Injective (a j)) → (∀ j, Function.Injective (b j)) →
      (∀ j i k, a j i ≠ b j k) → Nonempty (Packing G ℓ p a b) := by
  obtain ⟨N,hN⟩ := RobustSpanningLinkage.exists_spanning_linkage_threshold.{u} ν τ α
    hν (by linarith only [hντ,hτα,hα]) hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ ℓ p a b hSize hRob hDeg hBudget hp hCount ha hb hab
  apply exists_packing_of_residual_linkage G ℓ p a b
  intro Q t ht hQ hQDeg j
  have htR : (t:ℝ) ≤ ℓ := by exact_mod_cast ht.le
  have hTR : ((2*t:ℕ):ℝ) ≤ (2*ν-ν)*(Fintype.card V:ℝ) := by
    push_cast
    linarith only [htR,hBudget]
  have hRob' := isRealRobust_sdiff_with_loss G Q (2*ν) ν τ τ (2*t)
    (by linarith only [hν]) le_rfl hTR hQDeg hRob
  refine hN (G \ Q) hSize hRob' (fun v => ?_) hp hCount (a j) (b j) (ha j) (hb j) (hab j)
  have hAdd :
      ((G \ Q).degree v:ℝ)+(Q.degree v:ℝ) = (G.degree v:ℝ) := by
    exact_mod_cast MaximumMatching.degree_sdiff_add_of_le G Q hQ v
  have hQD : (Q.degree v:ℝ) ≤ 2*(t:ℝ) := by exact_mod_cast hQDeg v
  linarith only [hAdd,hQD,hDeg v,htR]

end OverfullWork.DenseBatchPathPacking
