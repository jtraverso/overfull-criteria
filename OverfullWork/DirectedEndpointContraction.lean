module

public import OverfullWork.TwoSidedRealTransfer
public import OverfullWork.ChunkedCellPartitions

@[expose] public section


/-! Directed endpoint contraction as two injective representative maps.
Outgoing and incoming representatives may differ, exactly as in KLO
Corollaries 6.8--6.9. No Hamilton cycle is assumed or constructed here. -/
namespace OverfullWork.DirectedEndpointContraction
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V W : Type*} [Fintype V] [Fintype W]
set_option maxHeartbeats 18000000

def contracted (D : Digraph V) (a b : W ↪ V) : Digraph W where
  Adj u v := D.Adj (a u) (b v)

noncomputable def partialIndex (e : W ↪ V) : V → Option W := mapCells fun w => {e w}

theorem partialIndex_cluster (e : W ↪ V) (w : W) : cluster (partialIndex e) w={e w} := by
  apply cluster_mapCells
  intro i j hij
  apply disjoint_left.mpr
  intro v hi hj
  simp only [mem_singleton] at hi hj
  exact hij (e.injective (hi.symm.trans hj))

theorem partialIndex_eq (e : W ↪ V) (v : V) (w : W) : partialIndex e v=some w ↔ v=e w := by
  rw [←mem_cluster,partialIndex_cluster,mem_singleton]

theorem partialIndex_size (e : W ↪ V) : ∀ w,(cluster (partialIndex e) w).card=1 := by
  intro w;rw [partialIndex_cluster,card_singleton]

theorem partialIndex_exceptional (e : W ↪ V) :
    (exceptional (partialIndex e)).card=Fintype.card V-Fintype.card W := by
  have hh := order_eq (partialIndex e) 1 (partialIndex_size e)
  simp only [one_mul] at hh
  omega

theorem quotient_eq_contracted (D : Digraph V) (a b : W ↪ V) :
    TwoSidedClusterQuotient.quotient D (partialIndex a) (partialIndex b)=contracted D a b := by
  ext i j
  constructor
  · rintro ⟨u,v,hu,hv,hAdj⟩
    rw [partialIndex_eq] at hu hv
    subst u;subst v;exact hAdj
  · intro hAdj
    exact ⟨a i,b j,(partialIndex_eq a _ _).mpr rfl,(partialIndex_eq b _ _).mpr rfl,hAdj⟩

theorem robust_contracted (D : Digraph V) (a b : W ↪ V) (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hRobust : IsRealRobust D ν τ)
    (hClusters : 4 ≤ ν*(Fintype.card W:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hDeficit : ((Fintype.card V-Fintype.card W:ℕ):ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLoss : ((Fintype.card V-Fintype.card W:ℕ):ℝ) ≤ ν*(Fintype.card V:ℝ)/4) :
    IsRealRobust (contracted D a b) (ν/2) (2*τ) := by
  let f := partialIndex a
  let g := partialIndex b
  have hG := partialIndex_size b
  have hException : ((exceptional g).card:ℝ) ≤ (Fintype.card V:ℝ)/4 := by
    simpa only [g,partialIndex_exceptional] using hDeficit
  have hSmall : ((exceptional g).card:ℝ)+(0:ℝ) ≤ ν*(Fintype.card V:ℝ)/4 := by
    simpa only [g,partialIndex_exceptional,add_zero] using hLoss
  obtain ⟨hPaid,hInterval⟩ := RobustClusterQuotient.paper_scale_budgets g 1 0 hG ν τ hν hτ
    hClusters hOrder hException (by simpa using hSmall)
  have hDeleted : ∀ v,g v ≠ none → inDegree (D\D) v ≤ 0 := by
    intro v _
    simp [inDegree,inNeighbours,Digraph.sdiff_adj]
  have hR := TwoSidedClusterQuotient.real_robust_from_host D D le_rfl f g 1 0 (by omega)
    (partialIndex_size a) hG ν τ hν hτ hRobust hDeleted hPaid hInterval
  rw [quotient_eq_contracted] at hR
  exact hR

theorem indegree_loss (D : Digraph V) (a b : W ↪ V) (w : W) :
    inDegree D (b w) ≤ inDegree (contracted D a b) w+(Fintype.card V-Fintype.card W) := by
  have hh := card_le_exceptional_add_lift (partialIndex a) 1 (partialIndex_size a)
    (univ.filter fun u => D.Adj u (b w))
    (univ.filter fun i => (contracted D a b).Adj i w) (by
      intro u hu i hi
      rw [partialIndex_eq] at hi
      subst u
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩)
  rw [partialIndex_exceptional,one_mul] at hh
  change inDegree D (b w) ≤ _+inDegree (contracted D a b) w at hh
  omega

theorem outdegree_loss (D : Digraph V) (a b : W ↪ V) (w : W) :
    outDegree D (a w) ≤ outDegree (contracted D a b) w+(Fintype.card V-Fintype.card W) := by
  have hh := card_le_exceptional_add_lift (partialIndex b) 1 (partialIndex_size b)
    (univ.filter fun u => D.Adj (a w) u)
    (univ.filter fun j => (contracted D a b).Adj w j) (by
      intro u hu j hj
      rw [partialIndex_eq] at hj
      subst u
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩)
  rw [partialIndex_exceptional,one_mul] at hh
  change outDegree D (a w) ≤ _+outDegree (contracted D a b) w at hh
  omega

theorem semidegrees_contracted (D : Digraph V) (a b : W ↪ V) (α : ℝ)
    (hα : 0 ≤ α) (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hSmall : ((Fintype.card V-Fintype.card W:ℕ):ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    (∀ w,(α/2)*(Fintype.card W:ℝ) ≤ (inDegree (contracted D a b) w:ℝ)) ∧
    (∀ w,(α/2)*(Fintype.card W:ℝ) ≤ (outDegree (contracted D a b) w:ℝ)) := by
  have hCard : (Fintype.card W:ℝ) ≤ (Fintype.card V:ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective a a.injective
  have hScale := mul_le_mul_of_nonneg_left hCard hα
  constructor
  · intro w
    have hh : (inDegree D (b w):ℝ) ≤ (inDegree (contracted D a b) w:ℝ)+((Fintype.card V-Fintype.card W:ℕ):ℝ) := by
      exact_mod_cast indegree_loss D a b w
    have hMin := hIn (b w)
    linarith only [hh,hMin,hSmall,hScale]
  · intro w
    have hh : (outDegree D (a w):ℝ) ≤ (outDegree (contracted D a b) w:ℝ)+((Fintype.card V-Fintype.card W:ℕ):ℝ) := by
      exact_mod_cast outdegree_loss D a b w
    have hMin := hOut (a w)
    linarith only [hh,hMin,hSmall,hScale]

end OverfullWork.DirectedEndpointContraction
