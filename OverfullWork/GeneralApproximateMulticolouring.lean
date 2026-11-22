module

public import OverfullWork.BalancedHalves

@[expose] public section


/-! # Binary multicolouring for arbitrary bounded multiplicity

The recursion is proved for every depth, rather than just depths one to
three. The single moment hypothesis dominates all nodes of the recursion.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of colours after `j` balanced binary splits and simple Vizing
colourings at the leaves. -/
def binaryPalette : ℕ → ℕ → ℕ → ℕ
  | 0, d, _ => d+1
  | j+1, d, r => 2*binaryPalette j (d/2+r) r

/-- With positive slack the binary palette is never below the input
maximum-degree bound, which also controls the size of an internal seed. -/
theorem binary_palette_ge_degree (j d r : ℕ) (hr : 1≤r) :
    d+1≤binaryPalette j d r := by
  induction j generalizing d with
  | zero => simp [binaryPalette]
  | succ j ih =>
    have h:=ih (d/2+r)
    simp only [binaryPalette]
    omega

theorem binary_palette_bound (j d r : ℕ) :
    binaryPalette j d r + 2*r ≤ d + 2*r*2^j + 2^j := by
  induction j generalizing d with
  | zero => simp only [binaryPalette, pow_zero, Nat.mul_one]; omega
  | succ j ih =>
    have hh:=ih (d/2+r)
    have hd : 2*(d/2)≤d:=by omega
    simp only [binaryPalette, pow_succ]
    nlinarith

theorem binary_palette_additive_bound (j d r : ℕ) :
    binaryPalette j d r ≤ d + 2*(2^j-1)*r + 2^j := by
  have h:=binary_palette_bound j d r
  have hp : 1≤2^j:=Nat.one_le_pow j 2 (by omega)
  have he : 2^j-1+1=2^j:=by omega
  nlinarith

/-- Arbitrary depth: multiplicity at most `2^j` has a proper colouring
whose additive error is bounded independently of the maximum degree. -/
theorem exists_edgeColoring_power_two_of_moment (j : ℕ) (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤2^j) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d+j*r+1:ℕ)^3<(2*r:ℝ)^6) :
    Nonempty (M.EdgeColoring (binaryPalette j d r)) := by
  induction j generalizing M d with
  | zero =>
    exact M.exists_edgeColoring_simple d (by simpa using hmu) hdeg
  | succ j ih =>
    have houter : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6 := by
      have hq : ((d/2+1:ℕ):ℝ)≤((d+(j+1)*r+1:ℕ):ℝ):=by
        exact_mod_cast (show d/2+1≤d+(j+1)*r+1 by omega)
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 3) (by positivity)).trans_lt hsize
    have hinner : 15*(Fintype.card V:ℝ)*(d/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6 := by
      have hq : ((d/2+r+j*r+1:ℕ):ℝ)≤((d+(j+1)*r+1:ℕ):ℝ):=by
        exact_mod_cast (show d/2+r+j*r+1≤d+(j+1)*r+1 by
          have hd : d/2≤d:=by omega
          nlinarith)
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 3) (by positivity)).trans_lt hsize
    obtain ⟨A,B,hAB,hA,hB,hdegrees⟩:=M.exists_balanced_halves d r (2^j)
      (by simpa [pow_succ,Nat.mul_comm] using hmu) hdeg houter
    obtain ⟨C⟩:=ih A (d/2+r) hA (fun v => (hdegrees v).1) hinner
    obtain ⟨F⟩:=ih B (d/2+r) hB (fun v => (hdegrees v).2) hinner
    have hh : Nonempty ((A.addCopies B).EdgeColoring
        (binaryPalette j (d/2+r) r+binaryPalette j (d/2+r) r)):=⟨C.addCopies F⟩
    rw [hAB] at hh
    simpa only [binaryPalette,two_mul] using hh

/-- A convenient interface exposing only the colour count and its bound. -/
theorem exists_bounded_palette_of_power_two_moment (j : ℕ) (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤2^j) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d+j*r+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ k, k≤d+2*(2^j-1)*r+2^j ∧ Nonempty (M.EdgeColoring k) :=
  ⟨binaryPalette j d r,binary_palette_additive_bound j d r,
    exists_edgeColoring_power_two_of_moment j M d r hmu hdeg hsize⟩

/-- Every finite multiplicity bound is covered. The depth `μ` is a simple
uniform choice; callers may use a smaller depth with the previous theorem. -/
theorem exists_edgeColoring_bounded_multiplicity_of_moment (M : MultiGraph V) (μ d r : ℕ)
    (hmu : ∀ e,M.mult e≤μ) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d+μ*r+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ k, k≤d+2*(2^μ-1)*r+2^μ ∧ Nonempty (M.EdgeColoring k) := by
  apply exists_bounded_palette_of_power_two_moment μ M d r
    (fun e => (hmu e).trans (Nat.lt_two_pow_self.le)) hdeg hsize

end SimpleGraph.MultiGraph
