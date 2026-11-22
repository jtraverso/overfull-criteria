module

public import OverfullWork.OsthusStadenBlackIntervals
public import OverfullWork.FactorMergeBatch

@[expose] public section


/-! Assign all factors to the disjoint cut families in §5.11 with
an exact integer capacity, including a partially filled final block. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical

theorem exists_factor_batch_schedule (k n b : ℕ) (hCapacity : k ≤ n*b) :
    ∃ batch : Fin k → Fin n, ∃ slot : Fin k → Fin b,
      Function.Injective (fun f => (batch f,slot f)) ∧
      ∀ i, ((univ : Finset (Fin k)).filter (fun f => batch f = i)).card ≤ b := by
  let e : Fin k ↪ Fin n × Fin b :=
    (Fin.castLEEmb hCapacity).trans finProdFinEquiv.symm.toEmbedding
  refine ⟨fun f => (e f).1,fun f => (e f).2,e.injective,?_⟩
  intro i
  calc
    _ ≤ (univ : Finset (Fin b)).card := by
      apply card_le_card_of_injOn (fun f => (e f).2) (fun _ _ => mem_univ _)
      intro x hx y hy h
      apply e.injective
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) h
    _ = b := by simp

/-- Integer load of the rotation families. Rounding up the divisions
suffices, without assuming that the number of factors is divisible by
the number of cut families. -/
theorem rounded_batch_capacity (k n : ℕ) (hn : 0 < n) :
    k ≤ n*((k+n-1)/n) := by
  have h := Nat.mod_add_div (k+n-1) n
  have hmod := Nat.mod_lt (k+n-1) hn
  omega

end OverfullWork.DirectedRobustExpansion
