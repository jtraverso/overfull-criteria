module

public import OverfullWork.KuhnOsthusCycleParityAssembly

@[expose] public section


/-! Edge accounting for the s absorbers in Kühn–Osthus Lemma 10.4. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical
variable {V I J : Type*} [Fintype V] [Finite I] [Finite J]

/-- The two cycle sweeps and their common parity repair in one round. -/
structure PreparedParityAbsorptionRound (I J : Type*) (F : Fin 7 → Equiv.Perm V) where
  first : CycleAbsorberSweepData I F 0 2
  second : CycleAbsorberSweepData J F 1 3
  repair : ParityRepairConfiguration F
  firstMarks : ∀ b : Bool, first.mark (b,first.final) = repair.mark (b,0)
  secondMarks : ∀ b : Bool, second.mark (b,second.final) = repair.mark (b,1)

def PreparedParityAbsorptionRound.Protected {F : Fin 7 → Equiv.Perm V}
    (A : PreparedParityAbsorptionRound I J F) (a : Fin 7) (v : V) : Prop :=
  A.first.Protected a v ∧ A.second.Protected a v ∧ A.repair.Protected a v

omit [Fintype V] in
/-- Flatten disjoint permutation families while retaining the
index of every factor inside its round. -/
theorem flatten_disjoint_permutation_rounds {s t : ℕ}
    (F : Fin s → Fin t → Equiv.Perm V)
    (hDis : ∀ a i j, i ≠ j → ∀ v, F a i v ≠ F a j v)
    (hRounds : Pairwise (fun a b => Disjoint (matchingUnion (F a)) (matchingUnion (F b)))) :
    ∃ G : Fin (s*t) → Equiv.Perm V,
      matchingUnion G = ⨆ a, matchingUnion (F a) ∧
      (∀ i j, i ≠ j → ∀ v, G i v ≠ G j v) ∧
      ∀ a i, G (finProdFinEquiv (a,i)) = F a i := by
  let e : Fin s × Fin t ≃ Fin (s*t) := finProdFinEquiv
  let G (i : Fin (s*t)) : Equiv.Perm V := F (e.symm i).1 (e.symm i).2
  refine ⟨G,?_,?_,?_⟩
  · ext x y
    rw [Digraph.iSup_adj]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e.symm i).1,(e.symm i).2,hi⟩
    · rintro ⟨a,j,hj⟩
      exact ⟨e (a,j),by simpa only [G,e.symm_apply_apply] using hj⟩
  · intro i j hij v he
    let a := e.symm i
    let b := e.symm j
    by_cases hab : a.1 = b.1
    · have hOther : a.2 ≠ b.2 := fun h => hij (e.symm.injective (Prod.ext hab h))
      change F a.1 a.2 v = F b.1 b.2 v at he
      exact hDis a.1 a.2 b.2 hOther v (by simpa only [← hab] using he)
    · exact (disjoint_iff_inf_le.mp (hRounds hab)) ⟨⟨a.2,he⟩,⟨b.2,rfl⟩⟩
  · intro a i
    change G (e (a,i)) = F a i
    simp only [G,e.symm_apply_apply]

/-- The exact conclusion of the normalized folded absorption. The
(7s) spanning cycles partition all the arcs of the (s) input rounds. -/
theorem kuhn_osthus_lemma_10_4_of_prepared_absorbers {s : ℕ}
    (F : Fin s → Fin 7 → Equiv.Perm V)
    (A : ∀ a, PreparedParityAbsorptionRound I J (F a))
    (hDis : ∀ a i j, i ≠ j → ∀ v, F a i v ≠ F a j v)
    (hRounds : ∀ a b, a ≠ b → Disjoint (matchingUnion (F a)) (matchingUnion (F b))) :
    ∃ G : Fin (s*7) → Equiv.Perm V,
      matchingUnion G = ⨆ a, matchingUnion (F a) ∧
      (∀ i j, i ≠ j → ∀ v, G i v ≠ G j v) ∧
      (∀ i, HasSpanningCycle (fun v w => G i v = w)) ∧
      ∀ (a : Fin s) (i : Fin 7) v, (A a).Protected i v →
        G (finProdFinEquiv (a,i)) v = F a i v := by
  have hOne (a : Fin s) := cycle_and_parity_absorption_round (F a)
    (A a).first (A a).second (A a).repair (A a).firstMarks (A a).secondMarks (hDis a)
  choose C hUnion hPart hCycle hKeep using hOne
  have hApart : Pairwise (fun a b => Disjoint (matchingUnion (C a)) (matchingUnion (C b))) := by
    intro a b hab
    rw [hUnion a,hUnion b]
    exact hRounds a b hab
  obtain ⟨G,hG,hDisG,hIndex⟩ := flatten_disjoint_permutation_rounds C hPart hApart
  simp only [hUnion] at hG
  refine ⟨G,hG,hDisG,?_,?_⟩
  · intro i
    obtain ⟨⟨a,j⟩,rfl⟩ := (finProdFinEquiv : Fin s × Fin 7 ≃ Fin (s*7)).surjective i
    rw [hIndex]
    exact hCycle a j
  · intro a i v h
    rw [hIndex]
    exact hKeep a i v h.1 h.2.1 h.2.2

end OverfullWork.DirectedRobustExpansion
