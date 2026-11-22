module

public import OverfullWork.KuhnOsthusCycleAbsorberInput

@[expose] public section


/-! The cluster construction, starting from one scheme and its four
canonical exceptional interval systems. The two instances of Claim 1
and all subsequent routes use the same prepared residual. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u}

structure NormalizedCycleAbsorber {G H : Digraph V} {A B : ℕ → Finset V} {m q : ℕ}
    (E : CycleAbsorberExceptionalCovers H A q)
    (eTop : Fin (2*m) ≃ A 0) (eLow : Fin (2*m) ≃ B 0) where
  top : CycleAbsorberClaimOne G A m (4*q)
  low : CycleAbsorberClaimOne G B m q
  top_start : ∀ j, top.paths.vertex 0 j = (eTop j).val
  low_start : ∀ j, low.paths.vertex 0 j = (eLow j).val
  topTail : OrderedClusterPaths G A (Fin (2*m)) (6*q) (7*q)
  lowTail : OrderedClusterPaths G B (Fin (2*m)) (3*q) (7*q)
  main : Digraph V
  main_arcs : main = ((top.paths.unionPaths ⊔ E.third.digraph) ⊔ topTail.unionPaths) ⊔
    ((low.paths.unionPaths ⊔ E.fifth.digraph) ⊔ lowTail.unionPaths)
  mainPermutation : Equiv.Perm V
  exact_main : ∀ x y, main.Adj x y ↔ mainPermutation x = y
  secondRotated : IntervalPathCover H (clusterIntervalVertices B (9*q) (11*q)) (B (9*q)) (B (11*q))
  second_arcs : secondRotated.digraph = E.second.digraph
  upper : CycleAbsorberResidualFactor top (fun i => A (8*q+i)) E.fourth (G \ main) (14*q+3-8*q)
  lowerHost : Digraph V
  lower : CycleAbsorberResidualFactor low (fun i => B (11*q+i)) secondRotated lowerHost (14*q+3-11*q)
  lower_le : lower.ordinary ≤ G
  main_disjoint : ∀ x y, main.Adj x y →
    ¬ (upper.ordinary ⊔ E.fourth.digraph).Adj x y ∧ ¬ (lower.ordinary ⊔ E.second.digraph).Adj x y
  upper_disjoint : ∀ x y, (upper.ordinary ⊔ E.fourth.digraph).Adj x y →
    ¬ (lower.ordinary ⊔ E.second.digraph).Adj x y
  upper_repair : ∀ l,
    (G \ (main ⊔ (upper.ordinary ⊔ E.fourth.digraph) ⊔ (lower.ordinary ⊔ E.second.digraph))).Adj
      (upper.rows.mark (l,Fin.last (2*m))) (upper.permutation (upper.rows.mark (!l,Fin.last (2*m))))
  lower_repair : ∀ l,
    (G \ (main ⊔ (upper.ordinary ⊔ E.fourth.digraph) ⊔ (lower.ordinary ⊔ E.second.digraph))).Adj
      (lower.rows.mark (l,Fin.last (2*m))) (lower.permutation (lower.rows.mark (!l,Fin.last (2*m))))

variable [Fintype V]

private theorem partition_card_bound {k m : ℕ} (X : Fin k → Finset V)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hSize : ∀ i, (X i).card = 2*m) :
    2*(Fintype.card V:ℝ) ≤ (2*k:ℕ)*((2*m:ℕ):ℝ) := by
  have he : (Finset.univ : Finset V) = (Finset.univ : Finset (Fin k)).biUnion X := by
    ext v
    simp only [mem_univ,mem_biUnion,true_and,true_iff]
    exact hCover v
  have hn : Fintype.card V ≤ k*(2*m) := by
    calc
      Fintype.card V = ((univ : Finset (Fin k)).biUnion X).card := by
        rw [← he, card_univ]
      _ ≤ ∑ i : Fin k, (X i).card := card_biUnion_le
      _ = k*(2*m) := by simp [hSize]
  have h : 2*Fintype.card V ≤ (2*k)*(2*m) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hn
  exact_mod_cast h

/-- The normalized cycle absorber is constructed from the cyclic
cluster pairs and the four complete exceptional covers. The first
deletion pays for their ordinary arcs and coincident shortcuts. -/
theorem kuhn_osthus_lemma_10_3_from_exceptional_covers (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε η θ d a : ℝ) (_hε₀ : 0 ≤ ε₀) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hTol₀ : 2*(ε₀+a) ≤ ε) (hTol : 2*(ε+a) ≤ η)
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGapη : 2*η < d) (hd : d ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {G H : Digraph V} {m : ℕ}
      (X : Fin (14*q) → Finset V) (hm : 0 < m) (hNm : N ≤ 2*m)
      (hCover : ∀ v, ∃ i, v ∈ X i)
      (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
      (hSize : ∀ i, (X i).card = 2*m)
      (hPairs : ∀ i, IsLowerSuperregularPair G ε₀ d (X i) (X (finRotate (14*q) i)))
      (hDelete : 1 ≤ a*(((2*m:ℕ):ℝ)*ε))
      (hBudget : 3 ≤ a*(((2*m:ℕ):ℝ)*η))
      (s : ℕ) (hs : 0 < s) (hCutθ : (m:ℝ)*θ ≤ (s:ℝ))
      (hRouteθ : 28*((s:ℝ)+1) < (d-2*θ)^14*((d-θ)*(m:ℝ)))
      (r : ℕ) (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
      (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
      (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
      (_hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
      ∀ (E : CycleAbsorberExceptionalCovers H A q)
        (eTop : Fin (2*m) ≃ A 0) (eLow : Fin (2*m) ≃ B 0),
        Nonempty (NormalizedCycleAbsorber (G := G \ E.arcs) E eTop eLow) := by
  have hC : 0 < (2*(14*q):ℕ) := by omega
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_10_3_claim_one.{u} ((2*(14*q):ℕ):ℝ) ε θ d
    (by exact_mod_cast hC) hε hθ hGapθ hd
  refine ⟨N,?_⟩
  intro V _ G H m X hm hNm hCover hDis hSize hPairs hDelete hBudget s hs hCutθ hRouteθ
    r hr hCutε hCutη hRouteε hRouteη hk A B E eTop eLow
  let D := G \ E.arcs
  have hOrigin (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have hDisA {i j : ℕ} (hi : i < 14*q) (hj : j < 14*q) (he : i ≠ j) :
      Disjoint (A i) (A j) := cyclicCluster_disjoint_before_wrap hk hDis hi hj he
  have hSecure (i : Fin (14*q)) : IsLowerSuperregularPair D ε d (X i) (X (finRotate (14*q) i)) :=
    E.residual_pair (fun i j hi hj h => hDisA (by omega) (by omega) h)
      _ _ hm (hSize _) (hSize _) ε₀ ε d a hε hε₁ ha (by linarith) hTol₀ hDelete (hPairs i)
  have hPair (i : ℕ) : IsLowerSuperregularPair D ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair D ε d (A i) (cyclicCluster X hk (i+1))
    rw [cyclicCluster_successor]
    exact hSecure _
  have hProfiles := partition_card_bound X hCover hSize
  let label (S : Finset V) (hS : S.card = 2*m) : Fin (2*m) ≃ S :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hS)).symm
  have hGapε : 2*ε < d := by linarith
  obtain ⟨C,hC₀,_⟩ := hN D A m (4*q) s r (by omega) hm hNm hProfiles
    (fun _ _ => hSize _) (fun i j hi hj h => hDisA (by omega) (by omega) h)
    (fun i _ => hPair i) hs hCutθ hRouteθ hr hCutε hRouteε eTop (label _ (hSize _))
  obtain ⟨C',hC'₀,_⟩ := hN D B m q s r (by omega) hm hNm hProfiles
    (fun i _ => by rw [hOrigin]; exact hSize _)
    (fun i j hi hj h => by rw [hOrigin,hOrigin]; exact hDisA (by omega) (by omega) (by omega))
    (fun i _ => by simpa only [hOrigin,Nat.add_assoc] using hPair (7*q+i))
    hs hCutθ hRouteθ hr hCutε hRouteε eLow (label _ (by rw [hOrigin]; exact hSize _))
  obtain ⟨E₂,E₅,h₂,h₅⟩ := E.exists_rotated X hk
  have hClean (x y : V) (h : D.Adj x y) :
      ¬ (((E.third.digraph ⊔ E₅.digraph) ⊔ E.fourth.digraph) ⊔ E₂.digraph).Adj x y := by
    rw [h₂,h₅]
    exact h.2
  obtain ⟨P,Q,φ,S,D',S',hD',hF,hFS,hSS,hR,hR'⟩ :=
    kuhn_osthus_lemma_10_3_cluster_assembly X hq hm hCover hDis hSize
      ε η d a hε.le hη hη₁ ha hGapε hGapη hd hTol hBudget hSecure r hr hCutε hCutη hRouteε hRouteη
      C C' E₂ E.third E.fourth E₅ hClean
  refine ⟨{
    top := C
    low := C'
    top_start := hC₀
    low_start := hC'₀
    topTail := P
    lowTail := Q
    main := ((C.paths.unionPaths ⊔ E.third.digraph) ⊔ P.unionPaths) ⊔
      ((C'.paths.unionPaths ⊔ E₅.digraph) ⊔ Q.unionPaths)
    main_arcs := by rw [h₅]
    mainPermutation := φ
    exact_main := hF
    secondRotated := E₂
    second_arcs := h₂
    upper := S
    lowerHost := D'
    lower := S'
    lower_le := S'.ordinary_le.trans hD'
    main_disjoint := fun x y h => by rw [←h₂]; exact hFS x y h
    upper_disjoint := fun x y h => by rw [←h₂]; exact hSS x y h
    upper_repair := fun l => by rw [←h₂]; exact hR l
    lower_repair := fun l => by rw [←h₂]; exact hR' l }⟩

end OverfullWork.DirectedRobustExpansion
