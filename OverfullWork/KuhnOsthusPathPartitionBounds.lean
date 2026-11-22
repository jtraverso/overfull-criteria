module

public import OverfullWork.KuhnOsthusPathPartitionSizes
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section


/-! Evaluate the bounds used by Kühn–Osthus after the style assignment.
The exceptional budget is shared by the factor piece and the original
complete exceptional path system. -/
namespace OverfullWork.DirectedRobustExpansion

open DirectedDemandHall (Arc)
variable {V J : Type*} [Fintype V]

theorem assembled_path_piece_bounds [DecidableEq J]
    {label : V → J} {Z : Finset V} {A H C Q : Digraph V} {a h c : Finset J}
    {n s : ℝ} (hs : 1228 ≤ s) (hn : s ≤ n)
    (hz : 2 * (Z.card : ℝ) ≤ n / s)
    (hQ : Q ≤ A ⊔ H ⊔ C)
    (ha : (Fintype.card (Arc A) : ℝ) ≤ ⌈1226 * n / (s - 1)⌉₊)
    (hh : Fintype.card (Arc H) ≤ Z.card)
    (hc : (Fintype.card (Arc C) : ℝ) ≤ n / (s - 1) + Z.card)
    (hAs : SupportedByStyles label Z a A) (hHs : SupportedByStyles label Z h H)
    (hCs : SupportedByStyles label Z c C) (hNumStyles : a.card + h.card + c.card ≤ 5) :
    (Fintype.card (Arc Q) : ℝ) ≤ 1230 * n / s ∧
      ∃ S : Finset J, S.card ≤ 5 ∧ SupportedByStyles label Z S Q := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hRounding := (Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1226) hn0) hs1.le)).le
  have hFactor : 1227 * n / (s-1) ≤ 1228 * n / s := by
    rw [div_le_div_iff₀ hs1 hs0]
    have hMul := mul_nonneg hn0 (show 0 ≤ s - 1228 by linarith)
    nlinarith
  have hOne : 1 ≤ n / s := (le_div_iff₀ hs0).mpr (by simpa using hn)
  have hCard : (Fintype.card (Arc Q) : ℝ) ≤
      (Fintype.card (Arc A) : ℝ) + Fintype.card (Arc H) + Fintype.card (Arc C) := by
    exact_mod_cast card_arcs_le_of_path_piece_support hQ
  have hh' : (Fintype.card (Arc H) : ℝ) ≤ Z.card := by exact_mod_cast hh
  have hTerm : 1226 * n / (s-1) + n / (s-1) = 1227 * n / (s-1) := by ring
  have hTerm' : 1228 * n / s + n / s + n / s = 1230 * n / s := by ring
  refine ⟨by linarith,⟨a ∪ h ∪ c,?_,styles_of_path_piece_support hQ hAs hHs hCs⟩⟩
  exact ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le a h) _)).trans hNumStyles

end OverfullWork.DirectedRobustExpansion
