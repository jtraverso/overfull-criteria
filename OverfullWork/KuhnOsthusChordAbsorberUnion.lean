module

public import OverfullWork.KuhnOsthusBaseCycleBlowup
public import OverfullWork.RobustRegularFactor

@[expose] public section


/-! Arc disjointness and physical degrees of the original chord
absorber in Kühn–Osthus (CA3) and (9.1). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A reserve supported on ordinary vertices has zero semidegrees
on the exceptional set. -/
private theorem exceptional_semidegrees_zero {D : Digraph V} {Z : Finset V}
    (h : ∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) (v : V) (hv : v ∈ Z) :
    inDegree D v = 0 ∧ outDegree D v = 0 := by
  constructor
  · apply Nat.eq_zero_of_not_pos
    intro hp
    obtain ⟨x,hx⟩ := card_pos.mp hp
    exact (h x v (mem_filter.mp hx).2).2 hv
  · apply Nat.eq_zero_of_not_pos
    intro hp
    obtain ⟨x,hx⟩ := card_pos.mp hp
    exact (h v x (mem_filter.mp hx).2).1 hv

/-- The original chord absorber consists precisely of the two
physical reserves and the original exceptional factors. Taking the
successive reserves in the actual complements proves (CA3), and
their degrees give (9.1). -/
theorem chord_absorber_union_of_reserves (G E B U : Digraph V) (Z : Finset V)
    (q e b u : ℕ) (hE : E ≤ G) (hB : B ≤ G \ E) (hU : U ≤ G \ (E ⊔ B))
    (hSupportB : ∀ x y, B.Adj x y → x ∉ Z ∧ y ∉ Z)
    (hSupportU : ∀ x y, U.Adj x y → x ∉ Z ∧ y ∉ Z)
    (hEDeg : ∀ v, let k := if v ∈ Z then q*e else e
      inDegree E v = k ∧ outDegree E v = k)
    (hBDeg : ∀ v ∉ Z, inDegree B v = b ∧ outDegree B v = b)
    (hUDeg : ∀ v ∉ Z, inDegree U v = u ∧ outDegree U v = u) :
    let CA := E ⊔ B ⊔ U
    CA ≤ G ∧ Disjoint E B ∧ Disjoint E U ∧ Disjoint B U ∧
      ∀ v, let k := if v ∈ Z then q*e else b+u+e
        inDegree CA v = k ∧ outDegree CA v = k := by
  have hEB (x y : V) : ¬ (E.Adj x y ∧ B.Adj x y) := fun h => (hB h.2).2 h.1
  have hEU (x y : V) : ¬ (E.Adj x y ∧ U.Adj x y) := fun h => (hU h.2).2 (Or.inl h.1)
  have hBU (x y : V) : ¬ (B.Adj x y ∧ U.Adj x y) := fun h => (hU h.2).2 (Or.inr h.1)
  have apart {P Q : Digraph V} (h : ∀ x y, ¬ (P.Adj x y ∧ Q.Adj x y)) : Disjoint P Q :=
    disjoint_iff_inf_le.mpr (fun x y ha => (h x y ha).elim)
  refine ⟨sup_le (sup_le hE (fun _ _ h => (hB h).1)) (fun _ _ h => (hU h).1),
    apart hEB,apart hEU,apart hBU,?_⟩
  intro v
  obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint (E ⊔ B) U
    (fun x y h => (hU h.2).2 h.1) v
  obtain ⟨ho',hi'⟩ := degrees_sup_of_disjoint E B hEB v
  rw [hi,ho,hi',ho']
  by_cases hv : v ∈ Z
  · have hDeg := hEDeg v
    change inDegree E v = (if v ∈ Z then q*e else e) ∧
      outDegree E v = (if v ∈ Z then q*e else e) at hDeg
    obtain ⟨hEi,hEo⟩ := by simpa only [if_pos hv] using hDeg
    obtain ⟨hBi,hBo⟩ := exceptional_semidegrees_zero hSupportB v hv
    obtain ⟨hUi,hUo⟩ := exceptional_semidegrees_zero hSupportU v hv
    simp only [if_pos hv,hEi,hEo,hBi,hBo,hUi,hUo,add_zero,and_self]
  · have hDeg := hEDeg v
    change inDegree E v = (if v ∈ Z then q*e else e) ∧
      outDegree E v = (if v ∈ Z then q*e else e) at hDeg
    obtain ⟨hEi,hEo⟩ := by simpa only [if_neg hv] using hDeg
    obtain ⟨hBi,hBo⟩ := hBDeg v hv
    obtain ⟨hUi,hUo⟩ := hUDeg v hv
    simp only [if_neg hv,hEi,hEo,hBi,hBo,hUi,hUo,add_left_comm,add_comm,and_self]

end OverfullWork.DirectedRobustExpansion
