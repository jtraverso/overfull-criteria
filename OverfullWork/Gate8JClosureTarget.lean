module

public import OverfullWork.ConflictSeedCriterion

@[expose] public section


/-! # The exact remaining above-half closure target

These are propositions describing the unresolved goal. Their equivalence
does not prove any of them. In particular, the established growing-gap
criterion retains an additional quantitative hypothesis; the target below
does not. No external theorem is imported as an axiom.
-/
namespace OverfullWork.Gate8J
open SimpleGraph
open scoped Classical
universe u

/-- The unconditional fixed-margin, sufficiently-large above-half goal. -/
def AboveHalfGoal : Prop :=
  ∀ε : ℝ,0<ε → ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    N≤Fintype.card W →
    ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
    (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph)

/-- Excluding all sufficiently large active critical counterexamples,
with the size measured on the critical graph itself. -/
def CriticalExclusion : Prop :=
  ∀ε : ℝ,0<ε → ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    N≤Fintype.card W → Overfull.IsDeltaCritical G → (∀v,0<G.degree v) →
    ¬G.HasOverfullSubgraph →
    ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) → False

/-- The exact residual task after the proved linear window. The
coefficient is fixed before the graph; the eventual threshold may depend
on it. Neither the window nor the local pruning excludes these graphs. -/
def StructuredResidualExclusion : Prop :=
  ∀ε : ℝ,0<ε → ∀A : ℕ,0<A → ∃N : ℕ,
    ∀{W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Overfull.IsDeltaCritical G → (∀v,0<G.degree v) →
      ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
      Fintype.card W<A*(min (G.maxDegree-G.minDegree+1) (EdgeKernel.seedCoreDegree G)) →
      False

theorem aboveHalfGoal_iff_criticalExclusion : AboveHalfGoal.{u} ↔ CriticalExclusion.{u} := by
  constructor
  · intro h ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,?_⟩
    intro W _ _ G _ hsize hcrit _ hno hdense
    exact hcrit.2.1 ((hN G hsize hdense).mpr hno)
  · intro h ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨2*N,?_⟩
    intro W _ _ G _ hsize hdense
    refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
    by_contra hnc
    obtain ⟨w⟩ := Critical.exists_criticalWitness G hnc hno
    have : Nonempty w.vertices := w.critical.1.nonempty
    have hn : Fintype.card W≤2*G.maxDegree := by
      have hp : 0≤ε*(Fintype.card W:ℝ) := by positivity
      exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith)
    have horder : G.maxDegree<Fintype.card w.vertices := by
      have hh := w.graph.maxDegree_lt_card_verts
      rwa [w.maxDegree_eq] at hh
    have hwsize : N≤Fintype.card w.vertices := by omega
    have hwdense : ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℝ)≤(w.graph.maxDegree:ℝ) := by
      have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card W:ℝ) := by
        exact_mod_cast w.order_le
      rw [w.maxDegree_eq]
      exact (mul_le_mul_of_nonneg_left ho (by positivity)).trans hdense
    exact hN w.graph hwsize w.critical w.no_isolates w.no_overfull hwdense

theorem criticalExclusion_iff_structuredResidualExclusion :
    CriticalExclusion.{u} ↔ StructuredResidualExclusion.{u} := by
  constructor
  · intro h ε hε A _
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,?_⟩
    intro W _ _ G _ hsize hcrit hactive hno hdense _
    exact hN G hsize hcrit hactive hno hdense
  · intro h ε hε
    obtain ⟨A,hA,hwindow⟩ := Gate8J2I.critical_order_lt_linear_min_seedCoreDegree.{u} ε hε
    obtain ⟨N,hN⟩ := h ε hε A hA
    refine ⟨N,?_⟩
    intro W _ _ G _ hsize hcrit hactive hno hdense
    exact hN G hsize hcrit hactive hno hdense (hwindow G hcrit hno hdense)

theorem aboveHalfGoal_iff_structuredResidualExclusion :
    AboveHalfGoal.{u} ↔ StructuredResidualExclusion.{u} :=
  aboveHalfGoal_iff_criticalExclusion.trans criticalExclusion_iff_structuredResidualExclusion

end OverfullWork.Gate8J
