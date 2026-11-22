module

public import OverfullWork.RealDirectedOrderedPath
public import OverfullWork.SinglePathContraction

@[expose] public section


/-! End-to-end construction of the short prescribed directed path and
its actual robust loopless contraction. Prepares KLO Corollary 6.8 for
the general Hamiltonicity theorem; that theorem is not assumed here. -/
namespace OverfullWork.DirectedPrescribedVertexPath
open Finset DirectedRobustExpansion DirectedEndpointContraction
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 16000000

noncomputable def pathVertices (x : V) (l : List V) : Finset V := (x :: l).toFinset

def pathEnd (x : V) (l : List V) : V := (x :: l).getLast (by simp)

theorem path_start_mem (x : V) (l : List V) : x∈pathVertices x l := by
  simp [pathVertices]

theorem path_end_mem (x : V) (l : List V) : pathEnd x l∈pathVertices x l := by
  apply List.mem_toFinset.mpr
  have hh : (x :: l).getLast?=some (pathEnd x l) :=
    List.getLast?_eq_some_getLast (by simp)
  exact List.mem_of_mem_getLast? (by rw [hh];rfl)

noncomputable def contractedPath (D : Digraph V) (x : V) (l : List V) :
    Digraph (Outside (pathVertices x l) ⊕ Fin 1) :=
  singleContraction D (pathVertices x l) x (pathEnd x l)
    (path_start_mem x l) (path_end_mem x l)

/-- All path and contraction data are constructed from ordinary robust
expansion and linear semidegrees. No cycle or path existence premise. -/
theorem exists_contractible_ordered_path (D : Digraph V) (ν τ α : ℝ)
    (hν : 0 < ν) (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 4*τ ≤ α)
    (hLarge : 64 ≤ ν*(Fintype.card V:ℝ)) (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (x : V) (marks : List V) (hDistinct : (x :: marks).Nodup)
    (hCount : (marks.length:ℝ) ≤ ν^3*(Fintype.card V:ℝ)) :
    ∃ l,(x :: l).IsChain D.Adj ∧
      (x :: l).getLast?=(x :: marks).getLast? ∧
      (x :: l).Nodup ∧ marks.Sublist l ∧
      ((pathVertices x l).card:ℝ) ≤ ν*(Fintype.card V:ℝ)/4 ∧
      IsRealRobust (contractedPath D x l) (ν/2) (2*τ) ∧
      (∀ w,(α/2)*(Fintype.card (Outside (pathVertices x l) ⊕ Fin 1):ℝ) ≤
        (inDegree (contractedPath D x l) w:ℝ)) ∧
      (∀ w,(α/2)*(Fintype.card (Outside (pathVertices x l) ⊕ Fin 1):ℝ) ≤
        (outDegree (contractedPath D x l) w:ℝ)) := by
  obtain ⟨l,hChain,hLast,hSimple,hOrdered,hLength⟩ := exists_real_ordered_path D ν τ α
    hν hSmall hντ hτα hLarge hRobust hIn hOut x marks hDistinct hCount
  have hCard : ((pathVertices x l).card:ℝ) ≤ ν*(Fintype.card V:ℝ)/4 := by
    simpa only [pathVertices,List.toFinset_card_of_nodup hSimple] using hLength
  have hτ : 0 < τ := hν.trans_le hντ
  have hνα : ν ≤ α := by linarith only [hν,hντ,hτα]
  have hNuScale := mul_le_mul_of_nonneg_right hνα
    (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ Fintype.card V)
  have hR := single_contraction_robust D (pathVertices x l) x (pathEnd x l)
    (path_start_mem x l) (path_end_mem x l) ν τ hν (by linarith only [hSmall]) hτ
    (by linarith only [hLarge])
    (by have hh := mul_le_mul_of_nonneg_right hντ
          (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ Fintype.card V)
        linarith only [hLarge,hh]) hCard hRobust
  have hSemi := single_contraction_semidegrees D (pathVertices x l) x (pathEnd x l)
    (path_start_mem x l) (path_end_mem x l) α (hν.le.trans hνα)
    (by linarith only [hCard,hNuScale,hLarge]) hIn hOut
  exact ⟨l,hChain,hLast,hSimple,hOrdered,hCard,hR,hSemi⟩

end OverfullWork.DirectedPrescribedVertexPath
