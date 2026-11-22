module

public import OverfullWork.RealDirectedRobustHamilton
public import OverfullWork.OrderedPathCycleExpansion

@[expose] public section


/-! KLO Corollary 6.8, using the proved Lo–Patel Hamiltonicity theorem
on the contraction of the prescribed short path. -/
namespace OverfullWork.DirectedPrescribedVertexPath

open Finset DirectedRobustExpansion DirectedEndpointContraction DirectedListRoutes
open scoped Classical
universe u
set_option maxHeartbeats 5000000

/-- Reroot an actual simple directed cycle at any vertex on it. -/
theorem rotate_closed_word {V : Type*} (D : Digraph V) (T : List V) (root x : V)
    (hHead : T.head? = some root) (hClosed : (T ++ [root]).IsChain D.Adj) (hx : x ∈ T) :
    ∃ l, (x :: l).Perm T ∧ (x :: (l ++ [x])).IsChain D.Adj := by
  obtain ⟨A,B,rfl⟩ := List.mem_iff_append.mp hx
  cases A with
  | nil =>
    have hx' : x = root := Option.some.inj hHead
    exact ⟨B, .refl _, by simpa [← hx'] using hClosed⟩
  | cons y A =>
    have hy : y = root := Option.some.inj hHead
    subst root
    have hChain : ((y :: A) ++ x :: (B ++ [y])).IsChain D.Adj := by
      simpa only [List.append_assoc, List.cons_append] using hClosed
    obtain ⟨hBefore,hAfter⟩ := List.isChain_split.mp hChain
    have hR : Route D x y (B ++ [y]) :=
      ⟨hAfter, by
        change ((x :: B) ++ [y]).getLast? = _
        exact (List.getLast?_append_of_ne_nil (x :: B) (by simp)).trans rfl⟩
    have hJoin := join_chain D hR hBefore
    refine ⟨B ++ y :: A, ?_, ?_⟩
    · change ((x :: B) ++ (y :: A)).Perm ((y :: A) ++ (x :: B))
      exact List.perm_append_comm
    · change (x :: ((B ++ [y]) ++ (A ++ [x]))).IsChain D.Adj at hJoin
      have hEq : (B ++ [y]) ++ (A ++ [x]) = (B ++ y :: A) ++ [x] := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rwa [hEq] at hJoin

/-- A robust Hamilton cycle through the prescribed vertices in their given order. -/
theorem exists_ordered_hamilton_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 64*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∀ (x : V) (marks : List V), (x :: marks).Nodup →
      (marks.length:ℝ) ≤ ν^3*(Fintype.card V:ℝ) →
      ∃ T : List V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some x ∧
        (T ++ [x]).IsChain D.Adj ∧ (x :: marks).Sublist T := by
  obtain ⟨N₀,hHam⟩ := DirectedAbsorbingLadder.exists_hamilton_threshold.{u}
    (ν/2) (2*τ) (α/2) (by positivity) (by linarith)
    (by linarith only [hτα]) (by linarith)
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (64/ν)
  refine ⟨max (2*N₀) N₁,?_⟩
  intro V _ D hn hRobust hIn hOut x marks hSimple hCount
  have hLarge : 64 ≤ ν*(Fintype.card V:ℝ) := by
    have hCast : (N₁:ℝ) ≤ Fintype.card V := by exact_mod_cast (show N₁ ≤ Fintype.card V by omega)
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp (hN₁.trans hCast)
  obtain ⟨l,hPath,_,hPathSimple,hMarks,hSmallPath,hR,hdIn,hdOut⟩ :=
    exists_contractible_ordered_path D ν τ α hν hSmall hντ (by linarith)
      hLarge hRobust hIn hOut x marks hSimple hCount
  let W := Outside (pathVertices x l) ⊕ Fin 1
  have hCard : Fintype.card W+(pathVertices x l).card-1 = Fintype.card V := by
    have h := single_carrier_order (pathVertices x l) ⟨x,path_start_mem x l⟩
    change Fintype.card W+((pathVertices x l).card-1) = Fintype.card V at h
    have hp := card_pos.mpr (show (pathVertices x l).Nonempty from ⟨x,path_start_mem x l⟩)
    omega
  have hSmallNat : 2*(pathVertices x l).card ≤ Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_right (show ν ≤ 1 by linarith) (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    exact_mod_cast (show (2:ℝ)*((pathVertices x l).card:ℝ) ≤ Fintype.card V by linarith only [hh,hSmallPath])
  obtain ⟨T,y,hND,hAll,hHead,hClosed⟩ :=
    hHam (contractedPath D x l) (by change N₀ ≤ Fintype.card W; omega)
      hR hdIn hdOut
  obtain ⟨init,hPerm,hRotate⟩ := rotate_closed_word (contractedPath D x l) T y
    (Sum.inr 0) hHead hClosed (hAll _)
  have hRPerm : (init ++ [Sum.inr (0:Fin 1)]).Perm T := List.perm_append_comm.trans hPerm
  exact expand_contracted_cycle D x l marks hPath hPathSimple hMarks init
    (hRPerm.nodup_iff.mpr hND) (fun v => hRPerm.mem_iff.mpr (hAll v)) hRotate

end OverfullWork.DirectedPrescribedVertexPath
