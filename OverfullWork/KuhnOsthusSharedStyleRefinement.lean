module

public import OverfullWork.OsthusStadenNestedRefinement
public import OverfullWork.OsthusStadenSliceRegularity

@[expose] public section


/-! Refine in the same physical cells for the endpoint count and
for the routing host in Kühn–Osthus Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- A simultaneous uniform refinement for both neighbourhood
directions in the original graph and in the residual graph. -/
theorem exists_shared_exceptional_style_refinement
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (K : ℕ) (hK : 0 < K) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type*}
      (G D : Digraph V) (P : I → Finset V) (m : ℕ),
      N ≤ K*m → (∀ i, (P i).card = K*m) →
      4*(Fintype.card V:ℝ) ≤ B*((K*m:ℕ):ℝ) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      ∃ C : Fin K × I → Finset V,
        (∀ j, (C j).card = m ∧ C j ⊆ P j.2) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        (∀ i, (univ : Finset (Fin K)).biUnion (fun a => C (a,i)) = P i) ∧
        ∀ j, UniformProfileCell (inProfile G) (P j.2) (C j) K ε ∧
          UniformProfileCell (outProfile G) (P j.2) (C j) K ε ∧
          UniformProfileCell (inProfile D) (P j.2) (C j) K ε ∧
          UniformProfileCell (outProfile D) (P j.2) (C j) K ε := by
  obtain ⟨N,hN⟩ := exists_ambient_uniform_refinement.{u,u} B ε hB hε K hK
  refine ⟨N,?_⟩
  intro V _ I G D P m hNmin hSize hProfiles hDis
  let profiles : (V ⊕ V) ⊕ (V ⊕ V) → Finset V :=
    Sum.elim (Sum.elim (inProfile G) (outProfile G)) (Sum.elim (inProfile D) (outProfile D))
  have hF (i : I) : Nonempty (UniformRefinementOf (I := Fin K) profiles (P i) m ε) := by
    apply hN profiles (P i) m (by rwa [hSize]) (hSize i)
    simpa only [Fintype.card_sum,Nat.cast_add,hSize] using
      (show (Fintype.card V:ℝ)+Fintype.card V+(Fintype.card V+Fintype.card V) ≤
        B*((K*m:ℕ):ℝ) by linarith only [hProfiles])
  let F (i : I) := Classical.choice (hF i)
  let C (j : Fin K × I) := (F j.2).cells j.1
  have hSub (j : Fin K × I) : C j ⊆ P j.2 := (F j.2).subset _
  refine ⟨C,fun j => ⟨(F j.2).size _,hSub j⟩,?_,fun i => (F i).cover,?_⟩
  · intro i j hne
    by_cases h : i.2 = j.2
    · have ha : i.1 ≠ j.1 := fun hh => hne (Prod.ext hh h)
      change Disjoint ((F i.2).cells i.1) ((F j.2).cells j.1)
      rw [←h]
      exact (F i.2).disjoint _ _ ha
    · exact (hDis _ _ h).mono (hSub i) (hSub j)
  · intro j
    refine ⟨?_,?_,?_,?_⟩ <;> intro v hv
    · simpa only [profiles,Sum.elim_inl,C,Fintype.card_fin] using
        (F j.2).uniform j.1 (.inl (.inl v)) hv
    · simpa only [profiles,Sum.elim_inl,Sum.elim_inr,C,Fintype.card_fin] using
        (F j.2).uniform j.1 (.inl (.inr v)) hv
    · simpa only [profiles,Sum.elim_inl,Sum.elim_inr,C,Fintype.card_fin] using
        (F j.2).uniform j.1 (.inr (.inl v)) hv
    · simpa only [profiles,Sum.elim_inr,C,Fintype.card_fin] using
        (F j.2).uniform j.1 (.inr (.inr v)) hv

end OverfullWork.DirectedRobustExpansion
