module

public import OverfullWork.RealRobustEvenOrientation

@[expose] public section


/-! Transfer of a Hamilton decomposition through an orientation,
as in the proof of Kühn–Osthus, Applications Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- A cyclic ordering visiting every vertex once and following the given adjacency. -/
def HasSpanningCycle (Adj : V → V → Prop) : Prop :=
  ∃ T : List V, ∃ x : V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some x ∧
    (T ++ [x]).IsChain Adj

structure DirectedHamiltonDecomposition (D : Digraph V) (k : ℕ) : Type u where
  factor : Fin k → Digraph V
  factor_le : ∀ i, factor i ≤ D
  partition : ∀ v w, D.Adj v w → ∃! i, (factor i).Adj v w
  degrees : ∀ i v, outDegree (factor i) v = 1 ∧ inDegree (factor i) v = 1
  spanning : ∀ i, HasSpanningCycle (factor i).Adj

structure HamiltonDecomposition (G : SimpleGraph V) (k : ℕ) : Type u where
  factor : Fin k → SimpleGraph V
  factor_le : ∀ i, factor i ≤ G
  partition : ∀ v w, G.Adj v w → ∃! i, (factor i).Adj v w
  degrees : ∀ i v, (factor i).degree v = 2
  spanning : ∀ i, HasSpanningCycle (factor i).Adj

noncomputable def DirectedHamiltonDecomposition.toUndirected {D : Digraph V} {G : SimpleGraph V}
    {k : ℕ} (hD : IsOrientationOf D G) (P : DirectedHamiltonDecomposition D k) :
    HamiltonDecomposition G k := by
  let F := fun i => (P.factor i).toSimpleGraphInclusive
  have hOr (i : Fin k) : IsOrientationOf (P.factor i) (F i) := by
    refine ⟨?_,fun _ _ h => h.2,?_⟩
    · intro v w h
      exact ⟨(hD.1 v w (P.factor_le i h)).ne,Or.inl h⟩
    · intro v w h
      exact hD.2.2 v w ⟨P.factor_le i h.1,P.factor_le i h.2⟩
  refine ⟨F,?_,?_,?_,?_⟩
  · intro i v w h
    exact h.2.elim (fun h => hD.1 v w (P.factor_le i h))
      (fun h => (hD.1 w v (P.factor_le i h)).symm)
  · have forward (v w : V) (h : D.Adj v w) : ∃! i, (F i).Adj v w := by
      obtain ⟨i,hi,hUnique⟩ := P.partition v w h
      refine ⟨i,(hOr i).1 v w hi,?_⟩
      intro j hj
      rcases hj.2 with hj | hj
      · exact hUnique j hj
      · exact (hD.2.2 v w ⟨h,P.factor_le j hj⟩).elim
    intro v w h
    rcases hD.2.1 v w h with h | h
    · exact forward v w h
    · obtain ⟨i,hi,hUnique⟩ := forward w v h
      exact ⟨i,hi.symm,fun j hj => hUnique j hj.symm⟩
  · intro i v
    letI : DecidableRel (F i).Adj := Classical.decRel _
    have h := degree_partition (P.factor i) (F i) (hOr i) v
    rw [(P.degrees i v).1,(P.degrees i v).2] at h
    exact h.symm
  · intro i
    obtain ⟨T,x,hN,hMem,hHead,hChain⟩ := P.spanning i
    exact ⟨T,x,hN,hMem,hHead,hChain.imp (fun a b h => (hOr i).1 a b h)⟩

/-- The existence assertion of Kühn–Osthus, Applications Theorem 1.2,
deduced from the directed decomposition theorem. -/
theorem robust_even_decomposition_of_loopless_directed
    (directed : ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧
      ∀ ν : ℝ, 0 < ν → ∃ N : ℕ, ∀ {W : Type u} [Fintype W]
        (D : Digraph W) (k : ℕ), N ≤ Fintype.card W →
        α*(Fintype.card W:ℝ) ≤ k → IsRealRobust D ν τ →
        (∀ v, outDegree D v = k ∧ inDegree D v = k) →
        (∀ v, ¬ D.Adj v v) → Nonempty (DirectedHamiltonDecomposition D k))
    (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] (k : ℕ),
        N ≤ Fintype.card W → α*(Fintype.card W:ℝ) ≤ 2*(k:ℝ) →
        RobustExpansion.IsRealRobust G ν τ → (∀ v, G.degree v = 2*k) →
        Nonempty (HamiltonDecomposition G k) := by
  obtain ⟨τ₀,hτ₀,hDir⟩ := directed (α/2) (by positivity)
  let τ := min τ₀ (α/64)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτle : τ ≤ τ₀ := min_le_left _ _
  have hτα : 64*τ ≤ α := by linarith only [min_le_right τ₀ (α/64)]
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  let b := min ν 1
  have hb : 0 < b := lt_min hν zero_lt_one
  have hbν : b ≤ ν := min_le_left _ _
  obtain ⟨μ,hμ,N₁,hO⟩ := exists_real_robust_even_regular_orientation.{u} b τ α
    hb (min_le_right _ _) hτ.le hτα hα
  obtain ⟨N₂,hFin⟩ := hDir μ hμ
  refine ⟨max N₁ N₂,?_⟩
  intro W _ _ G _ k hn hDeg hG hReg
  have hSmall : RobustExpansion.IsRealRobust G b τ := by
    intro S hLo hHi
    have hn0 : 0 ≤ (Fintype.card W:ℝ) := Nat.cast_nonneg _
    have hN := mul_le_mul_of_nonneg_right hbν hn0
    have hSubset : RobustExpansion.realNeighbourhood G ν S ⊆
        RobustExpansion.realNeighbourhood G b S :=
      fun v hv => mem_filter.mpr ⟨mem_univ _,hN.trans (mem_filter.mp hv).2⟩
    have hi := hG S hLo hHi
    have hc : ((RobustExpansion.realNeighbourhood G ν S).card:ℝ) ≤
        ((RobustExpansion.realNeighbourhood G b S).card:ℝ) := by
      exact_mod_cast card_le_card hSubset
    linarith only [hi,hc,hN]
  obtain ⟨D,hDG,hD,hRegD⟩ := hO G k ((le_max_left _ _).trans hn) hSmall hDeg hReg
  have hLarge : IsRealRobust D μ τ₀ := by
    intro S hLo hHi
    have hn0 : 0 ≤ (Fintype.card W:ℝ) := Nat.cast_nonneg _
    apply hD S ((mul_le_mul_of_nonneg_right hτle hn0).trans hLo)
    exact hHi.trans (mul_le_mul_of_nonneg_right (by linarith only [hτle]) hn0)
  obtain ⟨P⟩ := hFin D k ((le_max_right _ _).trans hn) (by linarith only [hDeg]) hLarge hRegD
    (fun v h => G.irrefl (hDG.1 v v h))
  exact ⟨P.toUndirected hDG⟩

/-- The orientation bridge also accepts a decomposition theorem stated for arbitrary directed hosts. -/
theorem robust_even_decomposition_of_directed
    (directed : ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧
      ∀ ν : ℝ, 0 < ν → ∃ N : ℕ, ∀ {W : Type u} [Fintype W]
        (D : Digraph W) (k : ℕ), N ≤ Fintype.card W →
        α*(Fintype.card W:ℝ) ≤ k → IsRealRobust D ν τ →
        (∀ v, outDegree D v = k ∧ inDegree D v = k) →
        Nonempty (DirectedHamiltonDecomposition D k))
    (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] (k : ℕ),
        N ≤ Fintype.card W → α*(Fintype.card W:ℝ) ≤ 2*(k:ℝ) →
        RobustExpansion.IsRealRobust G ν τ → (∀ v, G.degree v = 2*k) →
        Nonempty (HamiltonDecomposition G k) := by
  apply robust_even_decomposition_of_loopless_directed _ α hα
  intro a ha
  obtain ⟨τ,hτ,hPack⟩ := directed a ha
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  obtain ⟨N,hN⟩ := hPack ν hν
  exact ⟨N,fun D k hOrder hDense hRob hReg _ => hN D k hOrder hDense hRob hReg⟩

end OverfullWork.DirectedRobustExpansion
