module

public import OverfullWork.DeterministicMultigraphHalves
public import OverfullWork.GeneralApproximateMulticolouring

@[expose] public section


/-! # Binary colouring with a deterministic split of every odd layer -/
namespace SimpleGraph.MultiGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deterministic_palette_bounds (j d : ℕ) :
    d+1≤binaryPalette j d 1 ∧ binaryPalette j d 1+2≤d+3*2^j := by
  refine ⟨binary_palette_ge_degree j d 1 (by omega),?_⟩
  have h := binary_palette_bound j d 1
  omega

theorem exists_deterministic_colouring_of_split
    (hsplit : ∀ (M : MultiGraph V) (d b : ℕ),
      (∀ e,M.mult e≤2*b) → (∀ v,M.degree v≤d) →
      ∃ A B : MultiGraph V,A.addCopies B=M ∧
        (∀ e,A.mult e≤b) ∧ (∀ e,B.mult e≤b) ∧
        ∀ v,A.degree v≤d/2+1 ∧ B.degree v≤d/2+1)
    (j : ℕ) (M : MultiGraph V) (d : ℕ)
    (hmu : ∀ e,M.mult e≤2^j) (hdeg : ∀ v,M.degree v≤d) :
    Nonempty (M.EdgeColoring (binaryPalette j d 1)) := by
  induction j generalizing M d with
  | zero => exact M.exists_edgeColoring_simple d (by simpa using hmu) hdeg
  | succ j ih =>
    obtain ⟨A,B,hAB,hA,hB,hdegrees⟩ := hsplit M d (2^j)
      (by simpa [pow_succ,Nat.mul_comm] using hmu) hdeg
    obtain ⟨C⟩ := ih A (d/2+1) hA (fun v => (hdegrees v).1)
    obtain ⟨F⟩ := ih B (d/2+1) hB (fun v => (hdegrees v).2)
    have hh : Nonempty ((A.addCopies B).EdgeColoring
        (binaryPalette j (d/2+1) 1+binaryPalette j (d/2+1) 1)) := ⟨C.addCopies F⟩
    rw [hAB] at hh
    simpa only [binaryPalette,two_mul] using hh

/-- A deterministic colour construction.  The only graph hypotheses are
the multiplicity and maximum-degree bounds. -/
theorem exists_deterministic_colouring (j : ℕ) (M : MultiGraph V) (d : ℕ)
    (hmu : ∀ e,M.mult e≤2^j) (hdeg : ∀ v,M.degree v≤d) :
    Nonempty (M.EdgeColoring (binaryPalette j d 1)) := by
  exact exists_deterministic_colouring_of_split
    (fun M d b hmu hdeg => M.exists_deterministic_halves d b hmu hdeg)
    j M d hmu hdeg

/-- Convenient palette interface.  The preceding bound gives the
stronger inequality `k+2 ≤ d+3*2^j`. -/
theorem exists_deterministic_palette (j : ℕ) (M : MultiGraph V) (d : ℕ)
    (hmu : ∀ e,M.mult e≤2^j) (hdeg : ∀ v,M.degree v≤d) :
    ∃ k,d+1≤k ∧ k≤d+8*(2^j) ∧ Nonempty (M.EdgeColoring k) := by
  refine ⟨binaryPalette j d 1,(deterministic_palette_bounds j d).1,?_,
    exists_deterministic_colouring j M d hmu hdeg⟩
  have h := (deterministic_palette_bounds j d).2
  omega

end SimpleGraph.MultiGraph
