module

public import OverfullWork.KuhnOsthusResidueSpacing
public import OverfullWork.KuhnOsthusPathPartition

@[expose] public section


/-! The last walk pair in Kühn–Osthus Lemma 9.5 lists its quarters
starting with the third. A common short position window then uses
disjoint quarters at the two sides of the cut. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Positions in a common window shorter than a quarter cannot
belong to the same quarter after shifting one list by two quarters. -/
theorem walk_quarter_shift_separation (m : ℕ) (hm : 0 < m) (p q : Fin (4*m))
    (hpq : p.val < q.val+m) (hqp : q.val < p.val+m) :
    p.val/m ≠ (q.val/m+2)%4 := by
  have hp := (Nat.div_lt_iff_lt_mul hm).mpr p.isLt
  have hq := (Nat.div_lt_iff_lt_mul hm).mpr q.isLt
  have h₁ := Nat.div_le_div_right (c := m) hpq.le
  have h₂ := Nat.div_le_div_right (c := m) hqp.le
  rw [Nat.add_div_right _ hm] at h₁ h₂
  omega

/-- Matched arcs following the fine successor form a path system
when at the cut no vertex is used in both directions. Split the
vertices of the first label between the start and the end of the
integer order. -/
theorem walk_arcs_path_system_of_cut {V : Type*} (D : Digraph V) {n : ℕ}
    (rank : V → Fin (n+1))
    (hStep : ∀ x y, D.Adj x y → rank y = finRotate (n+1) (rank x))
    (hCut : ∀ x, rank x = 0 → ∀ y z, D.Adj y x → ¬ D.Adj x z)
    (hOut : ∀ {x y z}, D.Adj x y → D.Adj x z → y = z)
    (hIn : ∀ {x y z}, D.Adj x z → D.Adj y z → x = y) :
    IsDirectedPathSystem D := by
  let height (x : V) :=
    if rank x = 0 ∧ ¬ ∃ y, D.Adj x y then n+1 else (rank x).val
  have hInc (x y : V) (hxy : D.Adj x y) : height x < height y := by
    have hx : ¬ (rank x = 0 ∧ ¬ ∃ y, D.Adj x y) := fun h => h.2 ⟨y,hxy⟩
    change (if rank x = 0 ∧ ¬ ∃ y, D.Adj x y then n+1 else (rank x).val) < _
    rw [if_neg hx]
    by_cases hy : rank y = 0
    · have hEnd : rank y = 0 ∧ ¬ ∃ z, D.Adj y z :=
        ⟨hy,fun ⟨z,hz⟩ => hCut y hy x z hxy hz⟩
      simpa only [height,if_pos hEnd] using (rank x).isLt
    · have hBefore : rank x ≠ Fin.last n := by
        intro hLast
        exact hy ((hStep x y hxy).trans (hLast ▸ finRotate_last))
      have hVal : (rank y).val = (rank x).val+1 :=
        (congrArg Fin.val (hStep x y hxy)).trans (coe_finRotate_of_ne_last hBefore)
      have hlt : (rank x).val < (rank y).val := by omega
      have hEnd : ¬ (rank y = 0 ∧ ¬ ∃ z, D.Adj y z) := fun h => hy h.1
      simpa only [height,if_neg hEnd] using hlt
  have hPath {x y : V} (h : Relation.TransGen D.Adj x y) : height x < height y := by
    induction h with
    | single h => exact hInc _ _ h
    | tail _ h ih => exact ih.trans (hInc _ _ h)
  exact ⟨fun v h => (Nat.lt_irrefl (height v)) (hPath h),hOut,hIn⟩

/-- The paper's common-window calculation (9.14)–(9.15).
The half-open batch ranges at the first and at the final pair
have the same quarter width and lie in this common window. -/
theorem walk_batch_positions_in_short_window (q s a p p' : ℕ)
    (ha : 10*(a+1) ≤ q) (hQ : 110 < q)
    (h₁ : 110*s*a ≤ p) (h₂ : p < 130*s*(a+1))
    (h₁' : 110*s*a ≤ p') (h₂' : p' < 130*s*(a+1)) :
    p < p'+3*s*q ∧ p' < p+3*s*q := by
  have hGap : 130*s*(a+1) ≤ 110*s*a+3*s*q := by
    have hVa : 20*(a+1)+110 ≤ 3*q := by omega
    have hMul := Nat.mul_le_mul_left s hVa
    nlinarith only [hMul]
  exact ⟨h₂.trans_le (hGap.trans (Nat.add_le_add_right h₁' _)),
    h₂'.trans_le (hGap.trans (Nat.add_le_add_right h₁ _))⟩

end OverfullWork.DirectedRobustExpansion
