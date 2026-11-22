module

public import OverfullWork.OffDiagonalStubPairing
public import OverfullWork.CriticalCentreTriples

@[expose] public section


/-! # The boundary pairing used in CMS Theorem 4.2, Case 1

The graph is the actual input multigraph. No matching, transport matrix,
or prescribed degree sequence is assumed. The absence of an overfull
triple supplies exactly the obstruction inequalities of Lemma 3.2.
The boundary size here is unrelated to the canonical triangle parameter.
-/
namespace OverfullWork.HeavyPairBoundary
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

def outside (a b : V) : Finset V := ({a, b} : Finset V)ᶜ

@[simp] theorem mem_outside (a b v : V) : v ∈ outside a b ↔ v ≠ a ∧ v ≠ b := by
  simp [outside]

theorem sum_outside_add (f : V → ℕ) (a b : V) (hab : a ≠ b) :
    (∑ w : outside a b, f w.val) + f a + f b = ∑ v, f v := by
  rw [sum_coe_sort]
  have hs := sum_add_sum_compl ({a, b} : Finset V) f
  simp only [sum_pair hab] at hs
  change (∑ w ∈ ({a, b} : Finset V)ᶜ, f w) + f a + f b = _
  omega

theorem left_boundary_size (M : MultiGraph V) (a b : V) (hab : a ≠ b) :
    (∑ w : outside a b, M.mult s(a, w.val)) + M.mult s(a, b) = M.degree a := by
  have hs := sum_outside_add (fun v => M.mult s(a, v)) a b hab
  rw [M.loopless s(a,a) (by simp), add_zero, ← M.degree_eq_sum_mult] at hs
  exact hs

theorem right_boundary_size (M : MultiGraph V) (a b : V) (hab : a ≠ b) :
    (∑ w : outside a b, M.mult s(b, w.val)) + M.mult s(a, b) = M.degree b := by
  have hs := sum_outside_add (fun v => M.mult s(b, v)) a b hab
  rw [M.loopless s(b,b) (by simp), add_zero, ← M.degree_eq_sum_mult] at hs
  rwa [show s(b,a) = s(a,b) from Sym2.eq_swap] at hs

theorem triple_bundle_le (M : MultiGraph V) (D : ℕ)
    (hNo : ¬ M.HasOverfullSubset D) (a b : V) (hab : a ≠ b)
    (w : outside a b) :
    M.mult s(a,b) + M.mult s(a,w.val) + M.mult s(b,w.val) ≤ D := by
  have hw := (mem_outside a b w.val).mp w.property
  have hc : ({a,b,w.val} : Finset V).card = 3 := by simp [hab, hw.1.symm, hw.2.symm]
  have hb : M.edgesWithin {a,b,w.val} ≤ D := by
    by_contra h
    apply hNo
    refine ⟨{a,b,w.val}, ?_⟩
    simpa only [hc, Nat.reduceDiv, mul_one] using Nat.lt_of_not_ge h
  have ht := CriticalCentreTriples.triple_internal M a b w.val hab hw.1.symm hw.2.symm
  rw [MultiGraph.twiceInternal_eq] at ht
  omega

/-- All copies of the two boundary stars can actually be paired so that
the ordinary endpoints differ. This includes zero boundary size. -/
theorem exists_boundary_pairing (M : MultiGraph V) (D : ℕ)
    (hreg : M.IsRegularOfDegree D) (hNo : ¬ M.HasOverfullSubset D)
    (a b : V) (hab : a ≠ b) :
    ∃ e : (Σ w : outside a b, Fin (M.mult s(a,w.val))) ≃
        (Σ w : outside a b, Fin (M.mult s(b,w.val))),
      (∀ z, z.1.val ≠ (e z).1.val) ∧
      Fintype.card (Σ w : outside a b, Fin (M.mult s(a,w.val))) =
        D - M.mult s(a,b) := by
  have hleft := left_boundary_size M a b hab
  have hright := right_boundary_size M a b hab
  rw [hreg a] at hleft
  rw [hreg b] at hright
  obtain ⟨e, he⟩ := OffDiagonalStubPairing.exists_stub_equiv
    (fun w : outside a b => M.mult s(a,w.val))
    (fun w : outside a b => M.mult s(b,w.val))
    (by omega) (by
      intro w
      have ht := triple_bundle_le M D hNo a b hab w
      omega)
  refine ⟨e, ?_, ?_⟩
  · intro z h
    exact he z (Subtype.ext h)
  · simp only [Fintype.card_sigma, Fintype.card_fin]
    omega

end OverfullWork.HeavyPairBoundary
