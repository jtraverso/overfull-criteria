module

public import OverfullWork.KuhnOsthusOriginalAbsorptionRounds

@[expose] public section


/-! Compose the chord pack and the folded physical parity absorption,
as in the last part of Kühn–Osthus Lemma 11.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

/-- The exact final partition from the chord output and the physical
blocks of Lemma 10.5. The regular residue is factored inside the proof. -/
theorem kuhn_osthus_lemma_11_2_partition_of_original_blocks {k s t : ℕ}
    (X : Fin k → Finset V) (A : Digraph (V ⊕ Z))
    (C : Fin t → Equiv.Perm (V ⊕ Z)) (hC : matchingUnion C ≤ A)
    (hCycle : ∀ i, HasSpanningCycle (fun x y => C i x = y))
    (hDisC : ∀ i j, i ≠ j → ∀ x, C i x ≠ C j x)
    (R : Digraph V) (hResidue : A \ matchingUnion C = liftOrdinaryCycleArcs Z R)
    (hReg : ∀ v, inDegree R v = s ∧ outDegree R v = s)
    (hNext : ∀ i x y, x ∈ X i → R.Adj x y → y ∈ X (finRotate k i))
    (P : Fin s → Digraph (V ⊕ Z)) (E : Fin s → Fin 7 → Digraph (V ⊕ Z))
    (hAbsorb : ∀ a, AbsorbsWindingFactor X (P a) (E a))
    (hBlocks : Pairwise (fun a b => Disjoint (P a) (P b)))
    (hApart : Disjoint A (⨆ a, P a)) :
    ∃ F : Fin (t+s*7) → Equiv.Perm (V ⊕ Z),
      matchingUnion F = A ⊔ (⨆ a, P a) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      (∀ i, HasSpanningCycle (fun v w => F i v = w)) ∧
      (∀ i : Fin t, F (i.castAdd (s*7)) = C i) ∧
      ∀ a i, E a i ≤ ⟨fun v w => F ((finProdFinEquiv (a,i)).natAdd t) v = w⟩ := by
  have hOrd : liftOrdinaryCycleArcs Z R ≤ A := hResidue ▸ (fun _ _ h => h.1)
  obtain ⟨G,hG,hDisG,hHamG,hKeep⟩ :=
    kuhn_osthus_lemma_10_4_of_original_blocks X P E hAbsorb hBlocks R hReg hNext
      (hApart.mono_left hOrd)
  have hMix : Disjoint (matchingUnion C) (matchingUnion G) := by
    rw [hG,← hResidue]
    apply disjoint_sup_right.mpr
    refine ⟨?_,hApart.mono_left hC⟩
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hc,hr⟩
    exact hr.2 hc
  obtain ⟨hUnion,hDis⟩ := matchingUnion_addCases_of_disjoint C G hDisC hDisG hMix
  let F (i : Fin (t+s*7)) : Equiv.Perm (V ⊕ Z) := Fin.addCases C G i
  have hLeft (i : Fin t) : F (i.castAdd (s*7)) = C i := Fin.addCases_left i
  have hRight (i : Fin (s*7)) : F (i.natAdd t) = G i := Fin.addCases_right i
  refine ⟨F,?_,hDis,?_,hLeft,?_⟩
  · calc
      matchingUnion F = matchingUnion C ⊔ matchingUnion G := hUnion
      _ = (matchingUnion C ⊔ (A \ matchingUnion C)) ⊔ (⨆ a, P a) := by
        rw [hG,← hResidue,sup_assoc]
      _ = A ⊔ (⨆ a, P a) := by
        congr 1
        ext x y
        constructor
        · rintro (h | h)
          · exact hC h
          · exact h.1
        · intro h
          by_cases he : (matchingUnion C).Adj x y
          · exact .inl he
          · exact .inr ⟨h,he⟩
  · intro i
    cases i using Fin.addCases with
    | left j => rw [hLeft]; exact hCycle j
    | right j => rw [hRight]; exact hHamG j
  · intro a i
    rw [hRight]
    exact hKeep a i

end OverfullWork.DirectedRobustExpansion
