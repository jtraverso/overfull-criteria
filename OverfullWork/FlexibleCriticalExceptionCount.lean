module

public import OverfullWork.SparseSmallLowLayer

@[expose] public section


/-! # Independent construction and exception-count scales

The construction threshold q and the desired counting scale Q can be
fixed independently. Apply the proved critical deficit tail estimate at
P=max(q,Q), then use the actual inclusions of exceptional sets and the
monotonicity of integer division. Its existing deficit coefficient at P
is already small enough. The order threshold precedes every graph, and
neither a density margin epsilon nor no-overfullness is required.
-/
namespace OverfullWork.FlexibleCriticalExceptionCount
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
universe u
set_option maxHeartbeats 4000000

/-- Raising the allowed deficit shrinks the actual exceptional set. -/
theorem exceptions_antitone_threshold {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D a b : ℕ) (hab : a≤b) :
    exceptions G D b⊆exceptions G D a := by
  intro v hv
  have hh:=(mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ _,by omega⟩

/-- Any two fixed scales can be used for the threshold and counting
budget. G1 supplies a common stronger scale before the graph is given. -/
theorem exception_count_at_scales (q Q : ℕ) (hq : 2≤q) (hQ : 2≤Q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      Fintype.card V≤2*G.maxDegree →
      (exceptions G G.maxDegree (Fintype.card V/(8*q))).card≤
        Fintype.card V/(4096*Q^2) := by
  let P:=max q Q
  have hP : 2≤P := hq.trans (le_max_left _ _)
  obtain ⟨N,hcount⟩:=SparseSmallLowLayer.exception_count_at_fixed_scale.{u} P hP
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hc hdense
  have hqP : q≤P := le_max_left _ _
  have hQP : Q≤P := le_max_right _ _
  have ha : Fintype.card V/(8*P)≤Fintype.card V/(8*q) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 8 hqP) (by positivity)
  have hsub:=exceptions_antitone_threshold G G.maxDegree _ _ ha
  have hQQ : Q^2≤P^2 := Nat.pow_le_pow_left hQP 2
  have hk : Fintype.card V/(4096*P^2)≤Fintype.card V/(4096*Q^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 hQQ) (by positivity)
  exact (card_le_card hsub).trans ((hcount G hn hc hdense).trans hk)

end OverfullWork.FlexibleCriticalExceptionCount
