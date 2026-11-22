module

public import OverfullWork.SmallCentreCriticalExclusion
public import OverfullWork.CriticalDegreePairs

@[expose] public section


/-! Remove the proved small-centre case from the actual critical fork.

The final reduction and the large-centre branch remain explicit; this
does not identify class-two normalized states with critical graphs.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 32000000

theorem above_half_reduction_or_large_centre (ε : ℝ) (hε : 0 < ε) :
    ∃ Qs : ℕ, 8 ≤ Qs ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) → ¬G.HasOverfullSubgraph →
        let k := Fintype.card W/(4096*Qs^2)
        (∃ r : CriticalTwoColourReduction.Reduction G,
          (∑ v : W, (2-r.layer.degree v)) ≤ 2*k+2 ∧ ¬(G\r.layer).HasOverfullSubgraph) ∨
        ∃ c : Certificate G (6*k+6) (k+1),
          ∃ x ∈ c.set, G.degree x < ∑ y ∈ c.setᶜ, G.degree y := by
  obtain ⟨Qs,hQs,N₀,hExclude⟩ := above_half_small_centre_critical_exclusion.{u} ε hε
  obtain ⟨N₁,hFork⟩ := FlexibleAlmostReduction.above_half_normalized_fork_at_budget.{u} ε hε Qs (by omega)
  refine ⟨Qs,hQs,max N₀ N₁,?_⟩
  intro W _ _ G _ hn hcrit hdense hNo
  rcases hFork G (by omega) hcrit hdense hNo with hCert|hReduction
  · obtain ⟨c⟩ := hCert
    right
    refine ⟨c,?_⟩
    by_contra hNot
    push Not at hNot
    exact hExclude G c (by omega) hcrit hdense hNo (le_refl _) (le_refl _) hNot
  · exact Or.inl hReduction

theorem no_second_low_in_critical_large_centre
    {W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hcrit : Overfull.IsDeltaCritical G) (hActive : ∀ v, 0 < G.degree v)
    (hMargin : Fintype.card W+3*B ≤ 2*G.maxDegree)
    (x : W) (hx : x ∈ c.set) (hLarge : G.degree x < ∑ y ∈ c.setᶜ, G.degree y)
    (v : W) (hv : v ∈ c.set) (hvx : v ≠ x) : G.maxDegree < G.degree x+G.degree v := by
  by_contra! hLow
  have hDegree := LargeCentreCriticalGeometry.other_degree_lower G c hx hLarge hv hvx
  have hAnchor := LargeCentreCriticalGeometry.anchor_degree_add_excess_le G c hx hLarge hv hvx (by omega)
  have hPair := Gate8J2C.critical_degree_dichotomy G hcrit hActive hvx (by omega)
  omega

end OverfullWork.NormalizedCanonicalCandidate
