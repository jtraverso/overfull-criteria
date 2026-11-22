module

public import OverfullWork.FixedGapCriterion
public import OverfullWork.CriticalSpectrum

@[expose] public section


/-! # Uniform extraction of the remaining large-gap critical obstruction

For every fixed s and positive density margin, sufficiently large
counterexamples yield a critical core with gap greater than s. This is
a restriction on a hypothetical obstruction, not its exclusion.
-/
namespace OverfullWork.Gate8J
open SimpleGraph
open scoped Classical
universe u

theorem eventually_critical_gap_gt (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Overfull.IsDeltaCritical G → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      s<G.maxDegree-G.minDegree := by
  obtain ⟨N,hN⟩:=Gate8H2.eventually_above_half_fixed_gap.{u} s ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hsize hcrit hno hdense
  by_contra hn
  exact hcrit.2.1 ((hN G hsize (by omega) hdense).mpr hno)

/-- A degree threshold survives passage to an arbitrarily smaller
critical core because the maximum degree is preserved. -/
theorem eventually_exists_large_gap_critical_core (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph → N≤G.maxDegree →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∃ w : Critical.CriticalWitness G,
        N≤Fintype.card w.vertices ∧
        ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) ∧
        s<w.graph.maxDegree-w.graph.minDegree := by
  obtain ⟨N,hN⟩:=eventually_critical_gap_gt.{u} s ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hnc hno hlarge hdense
  obtain ⟨w⟩:=Critical.exists_criticalWitness G hnc hno
  haveI : Nonempty w.vertices:=w.critical.1.nonempty
  have hsize : N≤Fintype.card w.vertices := by
    have hh:=w.graph.maxDegree_lt_card_verts
    rw [w.maxDegree_eq] at hh
    omega
  have hdense' : ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) := by
    have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast w.order_le
    rw [w.maxDegree_eq]
    exact (mul_le_mul_of_nonneg_left ho (by positivity)).trans hdense
  exact ⟨w,hsize,hdense',hN w.graph hsize w.critical w.no_overfull hdense'⟩

/-- The original graph may instead satisfy an order threshold 2N:
the density margin then guarantees the required degree threshold N. -/
theorem eventually_exists_large_gap_critical_core_of_order (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      2*N≤Fintype.card W → ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∃ w : Critical.CriticalWitness G,
        N≤Fintype.card w.vertices ∧
        ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) ∧
        s<w.graph.maxDegree-w.graph.minDegree := by
  obtain ⟨N,hN⟩:=eventually_exists_large_gap_critical_core.{u} s ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hsize hnc hno hdense
  have hsizeR : 2*(N:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast hsize
  have hpositive : 0≤ε*(Fintype.card W:ℝ):=by positivity
  have hdegree : N≤G.maxDegree := by
    exact_mod_cast (show (N:ℝ)≤(G.maxDegree:ℝ) by nlinarith only [hdense,hsizeR,hpositive])
  exact hN G hnc hno hdegree hdense

/-- Full output interface: the extracted critical core has large gap,
a low/high edge, many maximum-degree neighbours, and the CCJS forbidden
interval. None of these restrictions is assumed for the original graph. -/
theorem eventually_exists_structured_critical_core (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      2*N≤Fintype.card W → ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∃ (w : Critical.CriticalWitness G) (a b : w.vertices),
        N≤Fintype.card w.vertices ∧
        ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) ∧
        s<w.graph.maxDegree-w.graph.minDegree ∧ 2≤w.graph.minDegree ∧
        w.graph.degree a=w.graph.minDegree ∧ w.graph.Adj a b ∧
        w.graph.degree b=w.graph.maxDegree ∧
        s+2≤((w.graph.neighborFinset b).filter
          fun z => z≠a ∧ w.graph.degree z=w.graph.maxDegree).card ∧
        (∀ v,v≠a → w.graph.degree v+w.graph.minDegree≤w.graph.maxDegree →
          w.graph.degree v+w.graph.maxDegree+5<Fintype.card w.vertices+2*w.graph.minDegree) ∧
        ∀ v,w.graph.degree v+w.graph.minDegree≤w.graph.maxDegree → ¬w.graph.Adj a v := by
  obtain ⟨N,hN⟩:=eventually_exists_large_gap_critical_core_of_order.{u} s ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hsize hnc hno hdense
  obtain ⟨w,horder,hden,hgap⟩:=hN G hsize hnc hno hdense
  obtain ⟨hmin,a,b,ha,hab,hb,hmax,hforbidden,hnadj⟩:=
    exists_minimum_edge_spectrum w.graph w.critical w.no_isolates
  exact ⟨w,a,b,horder,hden,hgap,hmin,ha,hab,hb,by omega,hforbidden,hnadj⟩

end OverfullWork.Gate8J
