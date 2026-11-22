module

public import OverfullWork.KuhnOsthusChordCompletion
public import OverfullWork.KuhnOsthusExceptionalContraction

@[expose] public section


/-! Restore the exceptional vertices in the chord-completion cycles
and account for the regular residue in Kühn–Osthus Lemma 9.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Lift a whole chord-completion pack, preserving arc disjointness
and exact coverage of the original prescribed systems. -/
theorem expand_chord_cycle_pack {q : ℕ} (P : Fin q → Digraph V) (R : Digraph V) (Z : Finset V)
    (hP : ∀ i, IsDirectedPathSystem (P i)) (hZ : ∀ i, CoversExceptional (P i) Z)
    (hNo : ∀ i x y, (P i).Adj x y → x ∈ Z → y ∉ Z)
    (hDis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hReserve : ∀ i, Disjoint (P i) R)
    (hOrd : ∀ x y, R.Adj x y → x ∉ Z ∧ y ∉ Z)
    (F : Fin q → Equiv.Perm ↥Zᶜ)
    (hCycle : ∀ i, HasSpanningCycle (fun x y => F i x = y))
    (hKeep : ∀ i x y, (basicExceptionalPathSystem (P i) Z).Adj x y → F i x = y)
    (hEdge : ∀ i x, ((basicExceptionalPathSystem (P i) Z) ⊔ induced R Zᶜ).Adj x (F i x))
    (hPack : ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) :
    ∃ G : Fin q → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => G i x = y)) ∧
      (∀ i x y, (P i).Adj x y → G i x = y) ∧
      (∀ i j, i ≠ j → ∀ x, G i x ≠ G j x) ∧
      (⨆ i, P i) ≤ matchingUnion G ∧ matchingUnion G ≤ (⨆ i, P i) ⊔ R := by
  choose G hG hPreserve hSupport hProjection using fun i =>
    expand_basic_exceptional_cycle_with_projection (P i) R Z (hP i) (hZ i) (hNo i)
      (F i) (hCycle i) (hKeep i) (hEdge i)
  refine ⟨G,hG,hPreserve,?_,?_,?_⟩
  · intro i j hij x hEq
    have hi := hSupport i x
    have hj := hSupport j x
    rw [←hEq] at hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (disjoint_iff_inf_le.mp (hDis i j hij)) ⟨hi,hj⟩
    · exact (disjoint_iff_inf_le.mp (hReserve i)) ⟨hi,hj⟩
    · exact (disjoint_iff_inf_le.mp (hReserve j)) ⟨hj,hi⟩
    · obtain ⟨hx,hy⟩ := hOrd _ _ hi
      let a : ↥Zᶜ := ⟨x,mem_compl.mpr hx⟩
      let b : ↥Zᶜ := ⟨G i x,mem_compl.mpr hy⟩
      exact hPack i j hij a ((hProjection i a b rfl).trans (hProjection j a b hEq.symm).symm)
  · intro x y h
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp h
    exact ⟨i,hPreserve i x y hi⟩
  · rintro x y ⟨i,rfl⟩
    exact (hSupport i x).imp (fun h => Digraph.iSup_adj.mpr ⟨i,h⟩) id

/-- The unused arcs after a chord cycle pack lie in the base-cycle
reserve. The semidegree accounting gives a regular ordinary residue
when the union has the required degree before the cycles are removed. -/
theorem regular_chord_residue_of_cycle_pack {q : ℕ} (P R : Digraph V) (Z : Finset V)
    (F : Fin q → Equiv.Perm V) (k : ℕ)
    (hPack : ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x)
    (hCover : P ≤ matchingUnion F) (hLe : matchingUnion F ≤ P ⊔ R)
    (hDeg : ∀ v, let d := if v ∈ Z then q else q+k
      inDegree (P ⊔ R) v = d ∧ outDegree (P ⊔ R) v = d) :
    let D := (P ⊔ R) \ matchingUnion F
    D ≤ R ∧ ∀ v, let d := if v ∈ Z then 0 else k
      inDegree D v = d ∧ outDegree D v = d := by
  intro D
  refine ⟨fun _ _ h => h.1.resolve_left (fun hP => h.2 (hCover hP)),?_⟩
  intro v
  obtain ⟨hin,hout⟩ := residual_semidegrees (P ⊔ R) (matchingUnion F) hLe v
  obtain ⟨hi,ho⟩ := matchingUnion_exact_semidegrees F hPack v
  change inDegree D v + inDegree (matchingUnion F) v = inDegree (P ⊔ R) v at hin
  change outDegree D v + outDegree (matchingUnion F) v = outDegree (P ⊔ R) v at hout
  rw [hi,(hDeg v).1] at hin
  rw [ho,(hDeg v).2] at hout
  by_cases hv : v ∈ Z
  · simp only [if_pos hv] at hin hout ⊢
    omega
  · simp only [if_neg hv] at hin hout ⊢
    omega

end OverfullWork.DirectedRobustExpansion
