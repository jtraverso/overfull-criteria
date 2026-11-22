module

public import OverfullWork.CombinedCoreDegree
public import OverfullWork.LinearCriterion

@[expose] public section


/-! # Linear above-half criteria for combined deficit and saturation pruning

The parameter τ measures internal maximum degree of the actual greatest
maximum-degree subset satisfying both deficit and neighbour-saturation
constraints. It is bounded above by the saturation-pruned parameter.
-/
namespace OverfullWork.Gate8J2I
open SimpleGraph DeficitCore
open scoped Classical
universe u

theorem critical_order_lt_linear_combinedCoreDegree (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      Overfull.IsDeltaCritical G → (∀ v,0<G.degree v) → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      Fintype.card W<A*(combinedCoreDegree G) := by
  obtain ⟨A,hA,hcriterion⟩:=above_half_linear_gap.{u} ε hε
  refine ⟨A,hA,?_⟩
  intro W _ _ G _ hcrit hactive hno hdense
  have hcore:=critical_gap_add_one_le_combinedCoreDegree G hcrit hactive
  have hmul:=Nat.mul_le_mul_left A hcore
  by_contra hn
  have hsize : A*(G.maxDegree-G.minDegree+1)≤Fintype.card W:=by omega
  exact hcrit.2.1 ((hcriterion G hsize hdense).mpr hno)

/-- Local sparsity of the combined kernel suffices. The parameter is
computed after both deficit and neighbour-saturation pruning. -/
theorem above_half_linear_combined_core_degree (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      A*(combinedCoreDegree G)≤Fintype.card W →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨B,hB,hcritical⟩:=critical_order_lt_linear_combinedCoreDegree.{u} ε hε
  refine ⟨2*B,by omega,?_⟩
  intro W _ _ G _ hsize hdense
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  by_contra hnc
  obtain ⟨w⟩:=Critical.exists_criticalWitness G hnc hno
  haveI : Nonempty w.vertices:=w.critical.1.nonempty
  have horder : G.maxDegree<Fintype.card w.vertices := by
    have hh:=w.graph.maxDegree_lt_card_verts
    rwa [w.maxDegree_eq] at hh
  have hn : Fintype.card W≤2*G.maxDegree := by
    have hp : 0≤ε*(Fintype.card W:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hp])
  have hden : ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) := by
    have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast w.order_le
    rw [w.maxDegree_eq]
    exact (mul_le_mul_of_nonneg_left ho (by positivity)).trans hdense
  have hbad:=hcritical w.graph w.critical w.no_isolates w.no_overfull hden
  have hcore:=combinedCoreDegree_le_of_copy w.embedding w.maxDegree_eq
  have hmul:=Nat.mul_le_mul_left B hcore
  have hsize' : 2*(B*(combinedCoreDegree G))≤Fintype.card W := by
    simpa only [Nat.mul_assoc] using hsize
  omega

/-- One coefficient covers either a small growing gap or a locally
sparse combined kernel. The coefficient depends only on the density margin. -/
theorem above_half_linear_gap_or_combined_core_degree (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      A*(min (G.maxDegree-G.minDegree+1) (combinedCoreDegree G))≤Fintype.card W →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨B,hB,hgap⟩:=above_half_linear_gap.{u} ε hε
  obtain ⟨C,_,hcore⟩:=above_half_linear_combined_core_degree.{u} ε hε
  refine ⟨max B C,lt_of_lt_of_le hB (le_max_left _ _),?_⟩
  intro W _ _ G _ hsize hdense
  by_cases hmin : G.maxDegree-G.minDegree+1≤combinedCoreDegree G
  · rw [min_eq_left hmin] at hsize
    exact hgap G ((Nat.mul_le_mul_right _ (le_max_left B C)).trans hsize) hdense
  · rw [min_eq_right (show combinedCoreDegree G≤G.maxDegree-G.minDegree+1 by omega)] at hsize
    exact hcore G ((Nat.mul_le_mul_right _ (le_max_right B C)).trans hsize) hdense

theorem critical_order_lt_linear_min_combinedCoreDegree (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      Overfull.IsDeltaCritical G → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      Fintype.card W<A*(min (G.maxDegree-G.minDegree+1) (combinedCoreDegree G)) := by
  obtain ⟨A,hA,hcriterion⟩:=above_half_linear_gap_or_combined_core_degree.{u} ε hε
  refine ⟨A,hA,?_⟩
  intro W _ _ G _ hcrit hno hdense
  by_contra hn
  exact hcrit.2.1 ((hcriterion G (by omega) hdense).mpr hno)

/-- Counterexamples extract into the combined-kernel obstruction window. -/
theorem exists_linear_combinedCoreDegree_critical_obstruction (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∃ w : Critical.CriticalWitness G,
        G.maxDegree<Fintype.card w.vertices ∧
        ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) ∧
        Fintype.card w.vertices<A*(min (w.graph.maxDegree-w.graph.minDegree+1)
          (combinedCoreDegree w.graph)) := by
  obtain ⟨A,hA,hcritical⟩:=critical_order_lt_linear_min_combinedCoreDegree.{u} ε hε
  refine ⟨A,hA,?_⟩
  intro W _ _ G _ hnc hno hdense
  obtain ⟨w⟩:=Critical.exists_criticalWitness G hnc hno
  haveI : Nonempty w.vertices:=w.critical.1.nonempty
  have horder : G.maxDegree<Fintype.card w.vertices := by
    have hh:=w.graph.maxDegree_lt_card_verts
    rwa [w.maxDegree_eq] at hh
  have hden : ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℕ)≤(w.graph.maxDegree:ℝ) := by
    have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast w.order_le
    rw [w.maxDegree_eq]
    exact (mul_le_mul_of_nonneg_left ho (by positivity)).trans hdense
  exact ⟨w,horder,hden,hcritical w.graph w.critical w.no_overfull hden⟩

end OverfullWork.Gate8J2I
