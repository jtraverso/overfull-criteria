module

public import OverfullWork.KuhnOsthusSmallTileFactors
public import OverfullWork.KuhnOsthusExceptionalPairStability

@[expose] public section


/-! Use one common explicit margin for the two fixed-size patterns. -/
namespace OverfullWork.DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

theorem geometric_tile_budgets (m r p h : ℕ) (η δ : ℝ) (hp : p ≤ 14) (hh : h ≤ 14)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hBudget : 28*((r:ℝ)+1) < η^14*(δ*(m:ℝ))) :
    let small := δ*(m:ℝ)/2
    0 ≤ small ∧ 0 ≤ δ*(m:ℝ)-small ∧
      ((p*r+p : ℕ):ℝ) < η^p*small ∧
      ((h*r+h : ℕ):ℝ) < η^h*(δ*(m:ℝ)-small) := by
  intro small
  have hSmall : 0 ≤ small := by dsimp [small]; positivity
  have hEq : δ*(m:ℝ)-small = small := by dsimp [small]; ring
  have hBound (a : ℕ) (ha : a ≤ 14) : ((a*r+a : ℕ):ℝ) < η^a*small := by
    have hA : (a:ℝ) ≤ 14 := by exact_mod_cast ha
    have hL : (a:ℝ)*((r:ℝ)+1) ≤ 14*((r:ℝ)+1) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    have hP := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hη hη₁ ha) hSmall
    push_cast
    rw [show (a:ℝ)*(r:ℝ)+(a:ℝ) = (a:ℝ)*((r:ℝ)+1) by ring]
    refine hL.trans_lt (?_ : 14*((r:ℝ)+1) < η^a*small)
    apply lt_of_lt_of_le _ hP
    change 14*((r:ℝ)+1) < η^14*(δ*(m:ℝ)/2)
    linarith only [hBudget]
  exact ⟨hSmall,(by rw [hEq]; exact hSmall),hBound p hp,(by rw [hEq]; exact hBound h hh)⟩

/-- Choose the rectangle threshold by rounding up εm. These
explicit inequalities make the fixed-pattern margins simultaneous. -/
theorem tile_rectangle_threshold (m : ℕ) (ε d : ℝ) (hm : 0 < m) (hε : 0 < ε)
    (hSmall : 56*ε ≤ (d-2*ε)^14*(d-ε))
    (hLarge : 112 < (d-2*ε)^14*((d-ε)*(m:ℝ))) :
    ∃ r : ℕ, 0 < r ∧ (m:ℝ)*ε ≤ (r:ℝ) ∧
      28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ)) := by
  let r := ⌈(m:ℝ)*ε⌉₊
  have hrL : (m:ℝ)*ε ≤ (r:ℝ) := Nat.le_ceil _
  have hrU : (r:ℝ) < (m:ℝ)*ε+1 := Nat.ceil_lt_add_one (by positivity)
  have hr : 0 < r := by
    exact_mod_cast (mul_pos (show (0:ℝ) < m by exact_mod_cast hm) hε).trans_le hrL
  have hGap := mul_le_mul_of_nonneg_right hSmall (Nat.cast_nonneg (α := ℝ) m)
  refine ⟨r,hr,hrL,?_⟩
  linarith only [hrU,hGap,hLarge]

/-- Convert the superregular-pair inequalities into the integer
rectangle threshold and two degree floors used by the tile factors. -/
theorem IsLowerSuperregularPair.tile_bounds (G : Digraph V) (A B : Finset V)
    (d ε : ℝ) (m r : ℕ) (H : IsLowerSuperregularPair G ε d A B)
    (hA : A.card = m) (hB : B.card = m) (hCut : (m:ℝ)*ε ≤ (r:ℝ)) :
    TileRectangleBound G A B r (d-2*ε) ∧
    (∀ v ∈ A, (d-ε)*(m:ℝ) ≤ (outTo G B v:ℝ)) ∧
    (∀ v ∈ B, (d-ε)*(m:ℝ) ≤ (inNeighbours G A v:ℝ)) := by
  obtain ⟨hOut,hIn,hRect⟩ := H.physical_lower_bounds G A B d ε
  refine ⟨?_,?_,?_⟩
  · intro S hS T hT hs ht
    exact hRect S hS T hT (by rw [hA]; exact hCut.trans (by exact_mod_cast hs))
      (by rw [hB]; exact hCut.trans (by exact_mod_cast ht))
  · intro v hv
    exact hB ▸ hOut v hv
  · intro v hv
    exact hA ▸ hIn v hv

end OverfullWork.DirectedRobustExpansion
