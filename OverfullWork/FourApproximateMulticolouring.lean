module

public import OverfullWork.FourLayers

@[expose] public section


/-! # Colouring multiplicity four with small additive error

Split into two almost equal multiplicity-two layers, split each again
into simple layers, and concatenate the four Vizing palettes.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_edgeColoring_multiplicity_four_approx (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤4) (hdeg : ∀ v,M.degree v≤d)
    (hsize₁ : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6)
    (hsize₂ : 15*(Fintype.card V:ℝ)*((d/2+r)/2+1:ℕ)^3<(2*r:ℝ)^6) :
    Nonempty (M.EdgeColoring (4*((d/2+r)/2+r+1))) := by
  obtain ⟨A,B,hAB,hA,hB,hdegrees⟩:=M.exists_balanced_double_layers d r hmu hdeg hsize₁
  obtain ⟨C⟩:=A.exists_edgeColoring_multiplicity_two_approx (d/2+r) r hA
    (fun v => (hdegrees v).1) hsize₂
  obtain ⟨F⟩:=B.exists_edgeColoring_multiplicity_two_approx (d/2+r) r hB
    (fun v => (hdegrees v).2) hsize₂
  have hh : Nonempty ((A.addCopies B).EdgeColoring
      (2*((d/2+r)/2+r+1)+2*((d/2+r)/2+r+1))) := ⟨C.addCopies F⟩
  rw [hAB] at hh
  have hk : 4*((d/2+r)/2+r+1)=2*((d/2+r)/2+r+1)+2*((d/2+r)/2+r+1):=by omega
  rw [hk]
  exact hh

theorem multiplicity_four_palette_bound (d r : ℕ) :
    4*((d/2+r)/2+r+1)≤d+6*r+4 := by omega

/-- A single stronger numerical condition is convenient when d itself
comes from a balanced vertex partition. -/
theorem exists_edgeColoring_multiplicity_four_of_moment (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤4) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d+r+1:ℕ)^3<(2*r:ℝ)^6) :
    Nonempty (M.EdgeColoring (4*((d/2+r)/2+r+1))) := by
  apply M.exists_edgeColoring_multiplicity_four_approx d r hmu hdeg
  · apply lt_of_le_of_lt ?_ hsize
    gcongr
    exact_mod_cast (show d/2≤d+r by omega)
  · apply lt_of_le_of_lt ?_ hsize
    gcongr
    exact_mod_cast (show (d/2+r)/2≤d+r by omega)

end SimpleGraph.MultiGraph
