module

public import OverfullWork.KuhnOsthusParityReserveDegrees

@[expose] public section


/-! Extract the ordinary-only parity reserve in Kühn–Osthus
Lemma 11.2(ii)(a), keeping its prescribed exceptional factors. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

/-- Exact physical degrees identify the part of the parity absorber
outside the prescribed packets as an ordinary regular digraph. -/
theorem parity_reserve_split_of_exact_semidegrees (P E : Digraph (V ⊕ Z)) (s : ℕ)
    (hE : E ≤ P)
    (hP : ∀ v, let d := match v with | .inl _ => 6*s | .inr _ => 7*s
      inDegree P v = d ∧ outDegree P v = d)
    (hDegE : ∀ v, let d := match v with | .inl _ => s | .inr _ => 7*s
      inDegree E v = d ∧ outDegree E v = d) :
    let R := ordinaryCycleHost (P \ E)
    Disjoint (liftOrdinaryCycleArcs Z R) E ∧ P = liftOrdinaryCycleArcs Z R ⊔ E ∧
      ∀ v, inDegree R v = 5*s ∧ outDegree R v = 5*s := by
  intro R
  let D := P \ E
  have hRemaining (v : V ⊕ Z) :
      let d := match v with | .inl _ => 5*s | .inr _ => 0
      inDegree D v = d ∧ outDegree D v = d := by
    obtain ⟨hi,ho⟩ := residual_semidegrees P E hE v
    rw [(hP v).1,(hDegE v).1] at hi
    rw [(hP v).2,(hDegE v).2] at ho
    cases v <;> dsimp [D] at hi ho ⊢ <;> omega
  have hNoIn (z : Z) (v : V ⊕ Z) : ¬ D.Adj v (.inr z) := by
    intro h
    have hPos : 0 < inDegree D (.inr z) := by
      simp only [inDegree,inNeighbours,card_pos,Finset.Nonempty,mem_filter,mem_univ,true_and]
      exact ⟨v,h⟩
    exact (Nat.ne_of_gt hPos) (hRemaining (.inr z)).1
  have hNoOut (z : Z) (v : V ⊕ Z) : ¬ D.Adj (.inr z) v := by
    intro h
    have hPos : 0 < outDegree D (.inr z) := by
      simp only [outDegree,card_pos,Finset.Nonempty,mem_filter,mem_univ,true_and]
      exact ⟨v,h⟩
    exact (Nat.ne_of_gt hPos) (hRemaining (.inr z)).2
  have hLift : liftOrdinaryCycleArcs Z R = D := by
    ext x y
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y => exact (iff_false_intro (hNoIn y (.inl x))).symm
    | inr x =>
      cases y with
      | inl y => exact (iff_false_intro (hNoOut x (.inl y))).symm
      | inr y => exact (iff_false_intro (hNoOut x (.inr y))).symm
  refine ⟨?_,?_,?_⟩
  · rw [hLift,disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    exact h.2 h'
  · rw [hLift]
    ext x y
    constructor
    · intro h
      by_cases he : E.Adj x y
      · exact .inr he
      · exact .inl ⟨h,he⟩
    · rintro (h | he)
      · exact h.1
      · exact hE he
  · let e : V ↪ V ⊕ Z := ⟨Sum.inl,Sum.inl_injective⟩
    have he : liftDirectedPair e e R = D := by
      rw [←hLift]
      ext x y
      cases x <;> cases y <;> simp [e,liftOrdinaryCycleArcs,liftDirectedPair]
    intro v
    have h := hRemaining (.inl v)
    have hi := lift_pair_semidegree e e R false v
    have ho := lift_pair_semidegree e e R true v
    change inDegree (liftDirectedPair e e R) (.inl v) = inDegree R v at hi
    change outDegree (liftDirectedPair e e R) (.inl v) = outDegree R v at ho
    rw [he] at hi ho
    exact ⟨hi.symm.trans h.1,ho.symm.trans h.2⟩

end OverfullWork.DirectedRobustExpansion
