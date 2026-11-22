module

public import OverfullWork.CMSCrossingPairTransport
public import OverfullWork.TwoSidedNormalizedLifting

@[expose] public section


/-! Apply two-sided regular lifting to the balanced halves from the
proof of CMS Lemma 5.4. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph DirectedClusterQuotient
open scoped Classical

variable {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Fintype I]

set_option maxHeartbeats 1900000 in
/-- Each direction of a balanced cut inherits expansion from the same
robust quotient and the corresponding halves of its regular pairs. -/
theorem expands_to_of_regular_half_cells (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : X ↪ V) (A B : Finset V)
    (hA : (univ : Finset X).map a = A) (hB : (univ : Finset X).map b = B)
    (f : V → Option I) (R : Digraph I) (l : ℕ) (ρ τ ε δ : ℝ)
    (hl : 0 < l) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hτ : 0 < τ) (hρτ : ρ ≤ τ)
    (hτQ : τ ≤ 1/4) (hε : 0 < ε) (hεSmall : ε ≤ ρ/64)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hCount : 4 ≤ Fintype.card I) (hWindow : 4 ≤ τ*(Fintype.card I:ℝ))
    (hLarge : 2 ≤ δ*ρ^2*(A.card:ℝ)/128)
    (hRound : (Fintype.card I:ℝ) ≤ ρ*(A.card:ℝ)/64)
    (hExc : ((exceptional f).card:ℝ) ≤ ρ*(A.card:ℝ)/32)
    (hCellsA : ∀ i, (A ∩ cluster f i).card = l)
    (hCellsB : ∀ i, (B ∩ cluster f i).card = l)
    (hPairs : ∀ i j, R.Adj i j → G.IsUniform ε (A ∩ cluster f i) (B ∩ cluster f j))
    (hDensity : ∀ i j, R.Adj i j →
      ε+δ ≤ (G.edgeDensity (A ∩ cluster f i) (B ∩ cluster f j):ℝ))
    (hR : DirectedRobustExpansion.IsRealRobust R ρ τ) :
    BipartiteRobustMargin.ExpandsTo G A B ⌈δ*ρ^2/256*(A.card:ℝ)⌉₊ ⌈2*τ*(A.card:ℝ)⌉₊ := by
  let D := DirectedRegularPairs.pullDirectedPair a b (RobustSpanningLinkage.symmetric G)
  let f₀ := f ∘ a
  let g₀ := f ∘ b
  let n := Fintype.card X
  let k := Fintype.card I
  have hCard : A.card = n := by rw [←hA,card_map,card_univ]
  have hAcell (i : I) : (cluster f₀ i).card = l := by
    rw [←card_map a,map_cluster_of_embedding,hA,hCellsA]
  have hBcell (i : I) : (cluster g₀ i).card = l := by
    rw [←card_map b,map_cluster_of_embedding,hB,hCellsB]
  have hExc₀ : ((exceptional f₀).card:ℝ) ≤ ρ*(n:ℝ)/32 :=
    (show ((exceptional f₀).card:ℝ) ≤ ((exceptional f).card:ℝ) by exact_mod_cast exceptional_pull_le a f).trans
      (by rwa [←hCard])
  have hTotal : (n:ℝ) = ((exceptional f₀).card:ℝ)+(l:ℝ)*(k:ℝ) := by
    exact_mod_cast order_eq f₀ l hAcell
  have hNn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hLower : (n:ℝ)/2 ≤ (l:ℝ)*(k:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hρ₁ hNn
    nlinarith only [hTotal,hExc₀,h,hNn]
  have hUpper₀ : (l:ℝ)*(k:ℝ) ≤ (n:ℝ) := by
    linarith only [hTotal,Nat.cast_nonneg (α := ℝ) (exceptional f₀).card]
  have hInterval : 2*⌈τ*(k:ℝ)⌉₊ ≤ k := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ τ*(k:ℝ) by positivity)).le
    have hBound := mul_le_mul_of_nonneg_right hτQ (Nat.cast_nonneg (α := ℝ) k)
    have hk : (4:ℝ) ≤ k := by exact_mod_cast hCount
    exact_mod_cast (show (2:ℝ)*(⌈τ*(k:ℝ)⌉₊:ℝ) ≤ (k:ℝ) by linarith only [hh,hBound,hk])
  have hUniform (i j : I) (hij : R.Adj i j) :
      DirectedRegularPairs.IsUniform D ε (cluster f₀ i) (cluster g₀ j) := by
    apply uniform_pull_symmetric
    rw [map_cluster_of_embedding,map_cluster_of_embedding,hA,hB]
    exact hPairs i j hij
  have hDense (i j : I) (hij : R.Adj i j) :
      ε+δ ≤ DirectedRegularPairs.density D (cluster f₀ i) (cluster g₀ j) := by
    dsimp only [D]
    rw [DirectedRegularPairs.density_pullDirectedPair,map_cluster_of_embedding,map_cluster_of_embedding,
      hA,hB,symmetric_density]
    exact hDensity i j hij
  have hRaw : DirectedRobustExpansion.IsRealRobust D (δ*ρ^2/256) (2*τ) :=
    TwoSidedClusterQuotient.normalized_regular_lifting D R f₀ g₀ l l ρ τ ε δ
      (by omega) hl le_rfl hρ hρ₁ hτ hδ hδ₁ hε hρτ
      (fun i => (hBcell i).ge) (fun i => (hAcell i).symm ▸ hl)
      (fun i => (hAcell i).le) (fun i => (hBcell i).le)
      hUniform hDense hR hInterval (by
        exact_mod_cast (show (n:ℝ) ≤ 2*(l:ℝ)*(k:ℝ) by nlinarith only [hLower]))
      (by simp only [Nat.sub_self,Nat.cast_zero,zero_mul]; positivity) hExc₀
      (hUpper₀.trans (by nlinarith only [mul_nonneg hρ.le hNn]))
      (by simpa only [hCard] using hRound)
      (by
        have hh := mul_le_mul_of_nonneg_left hWindow (Nat.cast_nonneg (α := ℝ) l)
        have hh' := mul_le_mul_of_nonneg_left hUpper₀ hτ.le
        nlinarith only [hh,hh'])
      (by
        have hh := mul_le_mul_of_nonneg_right hεSmall (show 0 ≤ (l:ℝ)*(k:ℝ) by positivity)
        have hh' := mul_le_mul_of_nonneg_left hUpper₀ (show 0 ≤ ρ/64 by positivity)
        nlinarith only [hh,hh'])
      (by simpa only [hCard] using hLarge)
  apply expandsTo_of_pulled_robust G a b hA hB
  rw [hCard]
  exact DirectedRobustExpansion.integer_of_real D _ _ (by positivity) hRaw

end OverfullWork.CMSBalancedCut
