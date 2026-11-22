module

public import OverfullWork.RobustExpansionFinite
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

@[expose] public section


/-! # Robust-neighbour counting from Mathlib regular pairs

These are the dense-pair counting estimates used in CMS Lemma 5.4.
The regular pair is the existing `SimpleGraph.IsUniform` predicate.
No regular partition or robust bipartite expander is assumed to exist.
-/
namespace OverfullWork.RegularPairNeighbourhood
open SimpleGraph Finset PrunedCore
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Restricting a regular pair preserves regularity with the displayed
size and tolerance losses. This is the slicing estimate needed when
trimming cells to equal even size. -/
theorem uniform_on_subcells {U W U' W' : Finset V} {ε ε' : ℝ}
    (hUniform : G.IsUniform ε U W) (hU : U'⊆U) (hW : W'⊆W)
    (hUlarge : (U.card:ℝ)*ε≤U'.card) (hWlarge : (W.card:ℝ)*ε≤W'.card)
    (hUscale : (U.card:ℝ)*ε≤(U'.card:ℝ)*ε')
    (hWscale : (W.card:ℝ)*ε≤(W'.card:ℝ)*ε') (hTol : 2*ε≤ε') :
    G.IsUniform ε' U' W' := by
  intro A hAU B hBW hA hB
  have h₁:|(G.edgeDensity A B:ℝ)-(G.edgeDensity U W:ℝ)|<ε:=
    hUniform (hAU.trans hU) (hBW.trans hW) (hUscale.trans hA) (hWscale.trans hB)
  have h₂:|(G.edgeDensity U' W':ℝ)-(G.edgeDensity U W:ℝ)|<ε:=
    hUniform hU hW hUlarge hWlarge
  calc
    _ = |((G.edgeDensity A B:ℝ)-(G.edgeDensity U W:ℝ))-
      ((G.edgeDensity U' W':ℝ)-(G.edgeDensity U W:ℝ))| := by congr 1;ring
    _ ≤ |(G.edgeDensity A B:ℝ)-(G.edgeDensity U W:ℝ)|+
      |(G.edgeDensity U' W':ℝ)-(G.edgeDensity U W:ℝ)| := abs_sub _ _
    _ < ε+ε := add_lt_add h₁ h₂
    _ ≤ ε' := by linarith

/-- Keeping at least half of each cell costs at most a factor two in
the regularity tolerance, for tolerances at most one half. -/
theorem uniform_on_half_subcells {U W U' W' : Finset V} {ε : ℝ}
    (hCap : ε≤(1:ℝ)/2) (hUniform : G.IsUniform ε U W)
    (hU : U'⊆U) (hW : W'⊆W)
    (hUhalf : (U.card:ℝ)≤2*(U'.card:ℝ))
    (hWhalf : (W.card:ℝ)≤2*(W'.card:ℝ)) : G.IsUniform (2*ε) U' W' := by
  have hε:0≤ε:=hUniform.pos.le
  have hScale:∀a b : ℝ,0≤b → a≤2*b → a*ε≤b ∧ a*ε≤b*(2*ε):=by
    intro a b hb hab
    have h₁:=mul_le_mul_of_nonneg_right hab hε
    have h₂:=mul_le_mul_of_nonneg_left hCap (show 0≤2*b by positivity)
    constructor <;>nlinarith
  have h₁:=hScale _ _ (Nat.cast_nonneg _) hUhalf
  have h₂:=hScale _ _ (Nat.cast_nonneg _) hWhalf
  exact uniform_on_subcells G hUniform hU hW h₁.1 h₂.1 h₁.2 h₂.2 le_rfl

theorem interedges_eq_sum_neighbours (A B : Finset V) :
    (G.interedges A B).card=∑v∈B,neighboursIn G A v := by
  calc
    _ = ∑a∈A,∑b∈B,if G.Adj a b then 1 else 0 := by
      simp only [G.interedges_def,card_filter,sum_product]
    _ = ∑b∈B,∑a∈A,if G.Adj b a then 1 else 0 := by
      rw [sum_comm]
      simp only [G.adj_comm]
    _ = _ := by simp only [RobustExpansion.neighboursIn_eq_filter_card,card_filter]

theorem interedges_le_of_neighbour_bound (A B : Finset V) (r : ℕ)
    (h : ∀v∈B,neighboursIn G A v≤r) : (G.interedges A B).card≤r*B.card := by
  rw [interedges_eq_sum_neighbours]
  calc
    _ ≤ ∑_v∈B,r :=sum_le_sum h
    _ = _ :=by simp [Nat.mul_comm]

/-- A regular pair has the expected edge lower bound on all subsets
large enough for the exact Mathlib regularity definition. -/
theorem uniform_interedges_lower {U W A B : Finset V} {ε d : ℝ}
    (hUniform : G.IsUniform ε U W) (hDensity : d≤(G.edgeDensity U W:ℝ))
    (hAU : A⊆U) (hBW : B⊆W)
    (hA : (U.card:ℝ)*ε≤A.card) (hB : (W.card:ℝ)*ε≤B.card)
    (hApos : A.Nonempty) (hBpos : B.Nonempty) :
    (d-ε)*(A.card:ℝ)*(B.card:ℝ)<((G.interedges A B).card:ℝ) := by
  have hh:|(G.edgeDensity A B:ℝ)-(G.edgeDensity U W:ℝ)|<ε:=hUniform hAU hBW hA hB
  have hd:d-ε<(G.edgeDensity A B:ℝ):=by
    obtain ⟨hl,_⟩:=abs_lt.mp hh
    linarith
  have hden:0<(A.card:ℝ)*(B.card:ℝ):=by
    have h₁:0<(A.card:ℝ):=by exact_mod_cast hApos.card_pos
    have h₂:0<(B.card:ℝ):=by exact_mod_cast hBpos.card_pos
    positivity
  rw [G.edgeDensity_def] at hd
  push_cast at hd
  have hb: (d-ε)*((A.card:ℝ)*(B.card:ℝ))<((G.interedges A B).card:ℝ):=
    (lt_div_iff₀ hden).mp hd
  simpa only [mul_assoc] using hb

/-- Only an epsilon proportion of a regular partner cell can have too
few neighbours in a large subset of the first cell. -/
theorem few_low_neighbours {U W A : Finset V} {ε d : ℝ}
    (hε : 0<ε) (hU : U.Nonempty) (hW : W.Nonempty)
    (hUniform : G.IsUniform ε U W) (hDensity : d≤(G.edgeDensity U W:ℝ))
    (hAU : A⊆U) (hA : (U.card:ℝ)*ε≤A.card) (r : ℕ)
    (hr : (r:ℝ)≤(d-ε)*(A.card:ℝ)) :
    ((W.filter fun v=>neighboursIn G A v<r).card:ℝ)<(W.card:ℝ)*ε := by
  let B:=W.filter fun v=>neighboursIn G A v<r
  have hApos:A.Nonempty:=by
    have hu:0<(U.card:ℝ):=by exact_mod_cast hU.card_pos
    have ha:0<(A.card:ℝ):=lt_of_lt_of_le (mul_pos hu hε) hA
    exact card_pos.mp (by exact_mod_cast ha)
  by_contra hn
  have hB:(W.card:ℝ)*ε≤B.card:=by change ¬((B.card:ℝ)<_) at hn;linarith
  have hBpos:B.Nonempty:=by
    have hw:0<(W.card:ℝ):=by exact_mod_cast hW.card_pos
    have hb:0<(B.card:ℝ):=lt_of_lt_of_le (mul_pos hw hε) hB
    exact card_pos.mp (by exact_mod_cast hb)
  have hLower:=uniform_interedges_lower G hUniform hDensity hAU (filter_subset _ _)
    hA hB hApos hBpos
  have hUpper:(G.interedges A B).card≤r*B.card:=by
    apply interedges_le_of_neighbour_bound G A B r
    intro v hv
    have hh:=(mem_filter.mp hv).2
    omega
  have hUpper':((G.interedges A B).card:ℝ)≤(r:ℝ)*(B.card:ℝ):=by exact_mod_cast hUpper
  have hProduct: (r:ℝ)*(B.card:ℝ)≤((d-ε)*(A.card:ℝ))*(B.card:ℝ):=
    mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
  linarith

end OverfullWork.RegularPairNeighbourhood
