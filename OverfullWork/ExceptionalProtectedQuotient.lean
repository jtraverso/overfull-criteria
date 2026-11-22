module

public import OverfullWork.DirectedPurePairGraph

@[expose] public section


/-! Exceptional vertices need no small deletion bound. Restore all arcs
incident with them before applying the global-loss quotient interface.
This changes no cluster quotient, and pays no exceptional-vertex loss. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

def protectExceptionals (D H : Digraph V) (f : V → Option I) : Digraph V where
  Adj u v := D.Adj u v ∧ (H.Adj u v ∨ f u=none ∨ f v=none)

theorem protectExceptionals_le (D H : Digraph V) (f : V → Option I) :
    protectExceptionals D H f ≤ D := fun _ _ hh => hh.1

theorem quotient_protectExceptionals (D H : Digraph V) (f : V → Option I) (hLe : H ≤ D) :
    quotient (protectExceptionals D H f) f=quotient H f := by
  ext i j
  constructor
  · rintro ⟨u,v,hu,hv,hD,hH|hU|hV⟩
    · exact ⟨u,v,hu,hv,hH⟩
    · rw [hu] at hU;cases hU
    · rw [hv] at hV;cases hV
  · rintro ⟨u,v,hu,hv,hH⟩
    exact ⟨u,v,hu,hv,hLe hH,Or.inl hH⟩

theorem protected_inDegree_loss (D H : Digraph V) (f : V → Option I) (L : ℕ)
    (hLoss : ∀ v,f v ≠ none → inDegree (D\H) v ≤ L) :
    ∀ v,inDegree (D\protectExceptionals D H f) v ≤ L := by
  letI : DecidableRel (D\H).Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (D\protectExceptionals D H f).Adj := fun _ _ => Classical.propDecidable _
  intro v
  by_cases hv : f v=none
  · have hEmpty : univ.filter (fun u => (D\protectExceptionals D H f).Adj u v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro u _ hh
      exact hh.2 ⟨hh.1,Or.inr (Or.inr hv)⟩
    simp only [inDegree,inNeighbours,hEmpty,card_empty,Nat.zero_le]
  · apply le_trans (b:=inDegree (D\H) v) ?_ (hLoss v hv)
    apply card_le_card
    intro u hu
    obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_univ _,hD,fun hH => hNot ⟨hD,Or.inl hH⟩⟩

theorem protected_outDegree_loss (D H : Digraph V) (f : V → Option I) (L : ℕ)
    (hLoss : ∀ v,f v ≠ none → outDegree (D\H) v ≤ L) :
    ∀ v,outDegree (D\protectExceptionals D H f) v ≤ L := by
  letI : DecidableRel (D\H).Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (D\protectExceptionals D H f).Adj := fun _ _ => Classical.propDecidable _
  intro v
  by_cases hv : f v=none
  · have hEmpty : univ.filter (fun u => (D\protectExceptionals D H f).Adj v u)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro u _ hh
      exact hh.2 ⟨hh.1,Or.inr (Or.inl hv)⟩
    simp only [outDegree,hEmpty,card_empty,Nat.zero_le]
  · apply le_trans (b:=outDegree (D\H) v) ?_ (hLoss v hv)
    apply card_le_card
    intro u hu
    obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_univ _,hD,fun hH => hNot ⟨hD,Or.inl hH⟩⟩

theorem real_quotient_transfer_nonexceptional (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (m L : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hLossIn : ∀ v,f v ≠ none → inDegree (D\H) v ≤ L)
    (hLossOut : ∀ v,f v ≠ none → outDegree (D\H) v ≤ L)
    (hClusters : 4 ≤ ν*(Fintype.card I:ℝ))
    (hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ))
    (hException : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLossSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4)
    (hDegreeSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    IsRealRobust (quotient H f) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (inDegree (quotient H f) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (outDegree (quotient H f) j:ℝ)) := by
  have hh := RobustClusterQuotient.real_quotient_transfer D (protectExceptionals D H f)
    (protectExceptionals_le D H f) f m L hm hSize ν τ α hν hτ hα hRobust hIn hOut
    (protected_inDegree_loss D H f L hLossIn) (protected_outDegree_loss D H f L hLossOut)
    hClusters hOrderLarge hException hLossSmall hDegreeSmall
  rw [quotient_protectExceptionals D H f hLe] at hh
  exact hh

theorem regularReduced_real_transfer_nonexceptional (D : Digraph V) (f : V → Option I)
    (ε d : ℝ) (hd : 0 < d) (m L : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hLossIn : ∀ v,f v ≠ none → inDegree (D\restrictPairs D f (regularReduced D f ε d)) v ≤ L)
    (hLossOut : ∀ v,f v ≠ none → outDegree (D\restrictPairs D f (regularReduced D f ε d)) v ≤ L)
    (hClusters : 4 ≤ ν*(Fintype.card I:ℝ))
    (hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ))
    (hException : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLossSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4)
    (hDegreeSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    IsRealRobust (regularReduced D f ε d) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (inDegree (regularReduced D f ε d) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (outDegree (regularReduced D f ε d) j:ℝ)) := by
  have hh := real_quotient_transfer_nonexceptional D _ (restrictPairs_le D f _) f m L hm
    hSize ν τ α hν hτ hα hRobust hIn hOut hLossIn hLossOut hClusters hOrderLarge
    hException hLossSmall hDegreeSmall
  rw [quotient_regular_pure D f ε d hd] at hh
  exact hh

end OverfullWork.DirectedClusterQuotient
