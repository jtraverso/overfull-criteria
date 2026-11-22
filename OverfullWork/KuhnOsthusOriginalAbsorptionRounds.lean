module

public import OverfullWork.KuhnOsthusOriginalParityRound
public import OverfullWork.KuhnOsthusParityAbsorptionRounds
public import OverfullWork.KuhnOsthusPreprocessingAssembly

@[expose] public section


/-! The folded form of Lemma 10.4 on the original graph. The entire
winding residue is factorized and assigned one factor per physical
block. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

/-- A regular blow-up residue is absorbed by the same number of
constructed blocks, with all original exceptional systems retained. -/
theorem kuhn_osthus_lemma_10_4_of_original_blocks {k s : ℕ}
    (X : Fin k → Finset V) (P : Fin s → Digraph (V ⊕ Z))
    (E : Fin s → Fin 7 → Digraph (V ⊕ Z))
    (hAbsorb : ∀ a, AbsorbsWindingFactor X (P a) (E a))
    (hBlocks : Pairwise (fun a b => Disjoint (P a) (P b)))
    (R : Digraph V) (hReg : ∀ v, inDegree R v = s ∧ outDegree R v = s)
    (hNext : ∀ i x y, x ∈ X i → R.Adj x y → y ∈ X (finRotate k i))
    (hReserved : Disjoint (liftOrdinaryCycleArcs Z R) (⨆ a, P a)) :
    ∃ F : Fin (s*7) → Equiv.Perm (V ⊕ Z),
      matchingUnion F = liftOrdinaryCycleArcs Z R ⊔ (⨆ a, P a) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      (∀ i, HasSpanningCycle (fun v w => F i v = w)) ∧
      ∀ a i, E a i ≤ ⟨fun v w => F (finProdFinEquiv (a,i)) v = w⟩ := by
  obtain ⟨M,hM,hDisM⟩ := exists_permutation_factorization_of_regular R s hReg
  let L (a : Fin s) := liftOrdinaryCycleArcs Z (⟨fun x y => M a x = y⟩ : Digraph V)
  have hLR (a : Fin s) : L a ≤ liftOrdinaryCycleArcs Z R := by
    rintro (x | z) (y | w) h
    · exact hM ▸ (show (matchingUnion M).Adj x y from ⟨a,h⟩)
    all_goals exact h
  have hOne (a : Fin s) := hAbsorb a (M a)
    (fun i x hx => hNext i x _ hx (hM ▸ (show (matchingUnion M).Adj x (M a x) from ⟨a,rfl⟩)))
    (hReserved.mono (hLR a) (le_iSup P a))
  choose C hUnion hPart hCycle hKeep using hOne
  have hApart (a b : Fin s) (hab : a ≠ b) : Disjoint (L a) (L b) := by
    rw [disjoint_iff_inf_le]
    rintro (x | z) (y | w) ⟨ha,hb⟩
    · exact hDisM a b hab x (ha.trans hb.symm)
    all_goals exact ha
  have hRound : Pairwise (fun a b => Disjoint (matchingUnion (C a)) (matchingUnion (C b))) := by
    intro a b hab
    rw [hUnion a,hUnion b]
    exact disjoint_sup_left.mpr
      ⟨disjoint_sup_right.mpr ⟨hApart a b hab,hReserved.mono (hLR a) (le_iSup P b)⟩,
        disjoint_sup_right.mpr ⟨(hReserved.mono (hLR b) (le_iSup P a)).symm,hBlocks hab⟩⟩
  obtain ⟨F,hF,hDisF,hIndex⟩ := flatten_disjoint_permutation_rounds C hPart hRound
  refine ⟨F,?_,hDisF,?_,?_⟩
  · rw [hF]
    ext x y
    rw [Digraph.iSup_adj]
    constructor
    · rintro ⟨a,ha⟩
      rcases (hUnion a ▸ ha : (L a ⊔ P a).Adj x y) with he | he
      · exact .inl (hLR a he)
      · exact .inr (Digraph.iSup_adj.mpr ⟨a,he⟩)
    · rintro (h | h)
      · rcases x with x | z <;> rcases y with y | w
        · obtain ⟨a,ha⟩ : (matchingUnion M).Adj x y := hM.symm ▸ h
          exact ⟨a,(hUnion a).symm ▸ (.inl ha : (L a ⊔ P a).Adj (.inl x) (.inl y))⟩
        all_goals exact h.elim
      · obtain ⟨a,ha⟩ := Digraph.iSup_adj.mp h
        exact ⟨a,(hUnion a).symm ▸ (.inr ha : (L a ⊔ P a).Adj x y)⟩
  · intro i
    obtain ⟨⟨a,j⟩,rfl⟩ := (finProdFinEquiv : Fin s × Fin 7 ≃ Fin (s*7)).surjective i
    rw [hIndex]
    exact hCycle a j
  · intro a i
    rw [hIndex]
    exact hKeep a i

end OverfullWork.DirectedRobustExpansion
