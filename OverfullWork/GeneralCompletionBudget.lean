module

public import OverfullWork.ScaledMargins

@[expose] public section


/-! # Numerical certificate for arbitrary multiplicity and excess

The five inequalities are the exact expansion and Hall margins used by
the completion engine. No choice of a graph or seed is hidden in them.
-/
namespace OverfullWork.BoundedMargins

structure Budget (μ b c m D t k d : ℕ) : Prop where
  first : b*ScaledMargins.badBound c m t+b+k+c*t<D
  ordinary : d+k+c*t+b≤D
  overlap : m+2*ScaledMargins.badBound c m t<2*d
  residual_hall : m+2*(3*c*t)+4*(m/(3*c)+1)+2*b+2+2*k≤2*D
  residual_centre : 3*c*t+2*μ*(m/(3*c)+1)+k<D

/-- The previous multiplicity-eight numerical certificate specializes
exactly to the new interface. -/
theorem budget_of_scaled {c m D t k : ℕ} (h : ScaledMargins.Budget c m D t k) :
    Budget 8 7 c m D t k (ScaledMargins.degreeBound c m) := by
  refine ⟨h.first,h.ordinary,h.overlap,?_,?_⟩
  · simpa only [show 2*7+2=16 by decide, Nat.add_assoc] using h.residual_hall
  · simpa using h.residual_centre

/-- Bounds can be weakened without reconstructing the combinatorial proof. -/
theorem budget_mono {μ b μ' b' c m D t k d : ℕ}
    (hμ : μ'≤μ) (hb : b'≤b) (h : Budget μ b c m D t k d) :
    Budget μ' b' c m D t k d := by
  have hB:=Nat.mul_le_mul_right (ScaledMargins.badBound c m t) hb
  have hA:=Nat.mul_le_mul_right (m/(3*c)+1) hμ
  refine ⟨by have hh:=h.first; omega,by have hh:=h.ordinary; omega,
    h.overlap,by have hh:=h.residual_hall; omega,?_⟩
  have hh:=h.residual_centre
  nlinarith only [hA,hh]

/-- A smaller seed palette only improves all completion margins. -/
theorem budget_palette_mono {μ b c m D t k k' d : ℕ}
    (hk : k'≤k) (h : Budget μ b c m D t k d) :
    Budget μ b c m D t k' d := by
  exact ⟨by have hh:=h.first; omega,by have hh:=h.ordinary; omega,
    h.overlap,by have hh:=h.residual_hall; omega,
    by have hh:=h.residual_centre; omega⟩

end OverfullWork.BoundedMargins
