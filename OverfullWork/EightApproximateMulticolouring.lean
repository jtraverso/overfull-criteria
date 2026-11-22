module

public import OverfullWork.BalancedHalves
public import OverfullWork.FourApproximateMulticolouring

@[expose] public section


/-! # A third binary split: multiplicity eight with additive palette error -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_edgeColoring_multiplicity_eight_of_moment (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤8) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d+2*r+1:ℕ)^3<(2*r:ℝ)^6) :
    Nonempty (M.EdgeColoring (8*(((d/2+r)/2+r)/2+r+1))) := by
  have hsize₁ : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6 := by
    apply lt_of_le_of_lt ?_ hsize
    gcongr
    exact_mod_cast (show d/2≤d+2*r by omega)
  have hsize₂ : 15*(Fintype.card V:ℝ)*(d/2+r+r+1:ℕ)^3<(2*r:ℝ)^6 := by
    have hq : ((d/2+r+r+1:ℕ):ℝ)≤((d+2*r+1:ℕ):ℝ):=by
      exact_mod_cast (show d/2+r+r+1≤d+2*r+1 by omega)
    have hp:=pow_le_pow_left₀ (Nat.cast_nonneg (d/2+r+r+1)) hq 3
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_lt hsize
  obtain ⟨A,B,hAB,hA,hB,hdegrees⟩:=M.exists_balanced_halves d r 4 hmu hdeg hsize₁
  obtain ⟨C⟩:=A.exists_edgeColoring_multiplicity_four_of_moment (d/2+r) r hA
    (fun v => (hdegrees v).1) hsize₂
  obtain ⟨F⟩:=B.exists_edgeColoring_multiplicity_four_of_moment (d/2+r) r hB
    (fun v => (hdegrees v).2) hsize₂
  have hh : Nonempty ((A.addCopies B).EdgeColoring
      (4*(((d/2+r)/2+r)/2+r+1)+4*(((d/2+r)/2+r)/2+r+1))) := ⟨C.addCopies F⟩
  rw [hAB] at hh
  have hk : 8*(((d/2+r)/2+r)/2+r+1)=
      4*(((d/2+r)/2+r)/2+r+1)+4*(((d/2+r)/2+r)/2+r+1):=by omega
  rwa [←hk] at hh

theorem multiplicity_eight_palette_bound (d r : ℕ) :
    8*(((d/2+r)/2+r)/2+r+1)≤d+14*r+8 := by omega

end SimpleGraph.MultiGraph
