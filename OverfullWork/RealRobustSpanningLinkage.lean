module

public import OverfullWork.RealRobustOrderedHamilton
public import OverfullWork.OrderedContractionBudgets
public import OverfullWork.PairedHamiltonDecode
public import OverfullWork.RealRobustExpansion

@[expose] public section


/-! KLO Corollary 6.9(ii), the robust spanning linkage used in CMS
Lemma 3.15. The symmetric digraph keeps both orientations of each host
edge, so the expansion and semidegree parameters are preserved exactly. -/
namespace OverfullWork.RobustSpanningLinkage

open Finset DirectedEndpointContraction DirectedPrescribedVertexPath OrderedCycleCutting
open scoped Classical
universe u
set_option maxHeartbeats 800000

private def symmetric {V : Type*} (G : SimpleGraph V) : Digraph V := ⟨G.Adj⟩

private theorem symmetric_robust {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν τ : ℝ)
    (h : RobustExpansion.IsRealRobust G ν τ) :
    DirectedRobustExpansion.IsRealRobust (symmetric G) ν τ := by
  intro S hlo hhi
  have hCounts (v : V) : DirectedRobustExpansion.inNeighbours (symmetric G) S v =
      PrunedCore.neighboursIn G S v := by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    change (S.filter fun u => (symmetric G).Adj u v).card = (S.filter (G.Adj v)).card
    apply congrArg Finset.card
    ext u
    rw [mem_filter, mem_filter]
    exact and_congr_right (fun _ => G.adj_comm u v)
  have hEq : DirectedRobustExpansion.realNeighbourhood (symmetric G) ν S =
      RobustExpansion.realNeighbourhood G ν S := by
    ext v
    rw [DirectedRobustExpansion.realNeighbourhood, RobustExpansion.realNeighbourhood,
      mem_filter, mem_filter, hCounts]
  rw [hEq]
  exact h S hlo hhi

private theorem symmetric_inDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DirectedRobustExpansion.inDegree (symmetric G) v = G.degree v := by
  have hEq : (univ.filter fun u => (symmetric G).Adj u v) = G.neighborFinset v := by
    ext u
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_univ, true_and]
    exact G.adj_comm u v
  exact (congrArg Finset.card hEq).trans (G.card_neighborFinset_eq_degree v)

private theorem symmetric_outDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DirectedRobustExpansion.outDegree (symmetric G) v = G.degree v := by
  have hEq : (univ.filter fun u => (symmetric G).Adj v u) = G.neighborFinset v := by
    ext u
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_univ, true_and]
    rfl
  exact (congrArg Finset.card hEq).trans (G.card_neighborFinset_eq_degree v)

private theorem markers_nodup {X I : Type*} {T : List (X ⊕ I)} (h : T.Nodup) :
    (markers T).Nodup := by
  apply h.filterMap
  intro a b i ha hb
  cases a <;> cases b <;> simp_all

private theorem marker_order {X : Type*} {k : ℕ} {T : List (X ⊕ Fin (k+1))}
    (hND : T.Nodup) (hSub : (List.ofFn (Sum.inr : Fin (k+1) → X ⊕ Fin (k+1))).Sublist T) :
    markers T = List.ofFn (id : Fin (k+1) → Fin (k+1)) := by
  have hFun : List.ofFn (Sum.inr : Fin (k+1) → X ⊕ Fin (k+1)) =
      (List.ofFn (id : Fin (k+1) → Fin (k+1))).map Sum.inr := by
    rw [List.map_ofFn]
    rfl
  have hSub' : (List.ofFn (id : Fin (k+1) → Fin (k+1))).Sublist (markers T) := by
    rw [hFun] at hSub
    let f : X ⊕ Fin (k+1) → Option (Fin (k+1)) :=
      fun w => match w with | Sum.inl _ => none | Sum.inr i => some i
    have h := hSub.filterMap f
    have hf : f ∘ Sum.inr = some := rfl
    rw [List.filterMap_map, hf, List.filterMap_some] at h
    have hFT : T.filterMap f = markers T := by
      unfold markers
      apply congrArg (fun g => T.filterMap g)
      funext w
      cases w <;> rfl
    rwa [hFT] at h
  have hCard : (markers T).length ≤ k+1 := by
    rw [← List.toFinset_card_of_nodup (markers_nodup hND)]
    exact (card_le_univ _).trans_eq (Fintype.card_fin _)
  exact (hSub'.eq_of_length_le (by simpa using hCard)).symm

/-- A cyclic contraction of distinct endpoint pairs has a Hamilton
cycle visiting the contracted markers in the specified cyclic order.
The cube bound pays for both contractions. -/
theorem exists_paired_ordered_cycle_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → DirectedRobustExpansion.IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (DirectedRobustExpansion.inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (DirectedRobustExpansion.outDegree D v:ℝ)) →
      ∀ (k : ℕ), ((k+1:ℕ):ℝ) ≤ (ν/4)^3*(Fintype.card V:ℝ) →
      ∀ (a b : Fin (k+1) → V) (ha : Function.Injective a) (hb : Function.Injective b),
        (∀ i j, a i ≠ b j) →
        ∃ init : List (Outside (pairedSet a b) ⊕ Fin (k+1)),
          (init ++ [Sum.inr 0]).Nodup ∧ (∀ w,w ∈ init ++ [Sum.inr 0]) ∧
          (0 :: markers (init ++ [Sum.inr 0])).IsChain
            (fun i j => finRotate (k+1) i = j) ∧
          (Sum.inr 0 :: (init ++ [Sum.inr 0])).IsChain
            (pairedContraction D a b ha hb (finRotate (k+1))).Adj := by
  obtain ⟨N₀,hOrdered⟩ := exists_ordered_hamilton_threshold.{u} (ν/2) (2*τ) (α/2)
    (by positivity) (by linarith only [hSmall]) (by linarith only [hντ,hν])
    (by linarith only [hτα]) (by linarith only [hα])
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (16/ν)
  refine ⟨max (2*N₀) N₁,?_⟩
  intro V _ D hN hRD hIn hOut k hpBound a b ha hb hab
  let next := finRotate (k+1)
  let H := pairedContraction D a b ha hb next
  let W := Outside (pairedSet a b) ⊕ Fin (k+1)
  have hLarge : 16 ≤ ν*(Fintype.card V:ℝ) := by
    have hCast : (N₁:ℝ) ≤ Fintype.card V := by exact_mod_cast (show N₁ ≤ Fintype.card V by omega)
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp (hN₁.trans hCast)
  have hτ : 0 < τ := hν.trans_le hντ
  have hOrder : 2 ≤ τ*(Fintype.card V:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    linarith only [h,hLarge]
  let n := Fintype.card V
  have hCarrier : Fintype.card W+(k+1) = n := paired_carrier_card a b ha hb hab
  have hDeficit : n-Fintype.card W = k+1 := by omega
  have hν1 : ν ≤ 1 := by linarith only [hSmall]
  have hν3 : ν^3 ≤ ν := by
    have hν2 := pow_le_pow_left₀ hν.le hν1 2
    have hh := mul_le_mul_of_nonneg_right hν2 hν.le
    nlinarith only [hh]
  have hν3n := mul_le_mul_of_nonneg_right hν3 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hνn := mul_le_mul_of_nonneg_right hν1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hPart : ((k+1:ℕ):ℝ) ≤ ν*(n:ℝ)/64 := by
    change ((k+1:ℕ):ℝ) ≤ (ν/4)^3*(n:ℝ) at hpBound
    nlinarith only [hpBound,hν3n]
  have hLoss : ((k+1:ℕ):ℝ)+1 ≤ ν*(n:ℝ)/4 := by linarith only [hPart,hLarge]
  have hQuarter : ((k+1:ℕ):ℝ) ≤ (n:ℝ)/4 := by linarith only [hLoss,hνn]
  have hQuarterNat : 4*(k+1) ≤ n := by
    exact_mod_cast (show (4:ℝ)*((k+1:ℕ):ℝ) ≤ n by linarith only [hQuarter])
  have hCast : (Fintype.card W:ℝ)+((k+1:ℕ):ℝ) = n := by exact_mod_cast hCarrier
  have hHalf : (n:ℝ)/2 ≤ Fintype.card W := by linarith only [hCast,hQuarter]
  have hScale := mul_le_mul_of_nonneg_left hHalf hν.le
  have hRobust := robust_loopless_contracted D (outgoingRepresentative a b ha next)
    (incomingRepresentative a b hb) ν τ hν hτ hRD
    (by linarith only [hScale,hLarge]) hOrder
    (by rwa [hDeficit]) (by rwa [hDeficit])
  have hνα : ν ≤ α := by linarith only [hν,hντ,hτα]
  have hBudget := mul_le_mul_of_nonneg_right hνα (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  obtain ⟨hdIn,hdOut⟩ := semidegrees_loopless_contracted D (outgoingRepresentative a b ha next)
    (incomingRepresentative a b hb) α (hν.le.trans hνα) hIn hOut
    (by rw [hDeficit]; linarith only [hLoss,hBudget,hLarge])
  have hN' : N₀ ≤ Fintype.card W := by omega
  let start : W := Sum.inr 0
  let marks : List W := List.ofFn (fun i : Fin k => Sum.inr i.succ)
  have hEq : (start :: marks) = List.ofFn (Sum.inr : Fin (k+1) → W) := List.ofFn_succ.symm
  have hND : (start :: marks).Nodup := by
    rw [hEq]
    exact List.nodup_ofFn.mpr Sum.inr_injective
  have hMarks : (marks.length:ℝ) ≤ (ν/2)^3*(Fintype.card W:ℝ) := by
    have hh : (marks.length:ℝ) ≤ ((k+1:ℕ):ℝ) := by simp [marks]
    have hScaled := mul_le_mul_of_nonneg_left hHalf (pow_nonneg (show 0 ≤ ν by positivity) 3)
    have hNν : 0 ≤ ν^3*(n:ℝ) := by positivity
    exact hh.trans (by nlinarith only [hpBound,hScaled,hNν])
  obtain ⟨T,hSimple,hAll,hHead,hCycle,hSub⟩ :=
    hOrdered H hN' hRobust hdIn hdOut start marks hND hMarks
  rw [hEq] at hSub
  have hMarkerEq := marker_order hSimple hSub
  cases T with
  | nil => simp at hHead
  | cons y init =>
    have hy : y = start := Option.some.inj hHead
    subst y
    have hRot : (init ++ [start]).Perm (start :: init) := by
      simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := init) (l₂ := [start]))
    refine ⟨init,hRot.nodup_iff.mpr hSimple,fun w => hRot.mem_iff.mpr (hAll w),?_,hCycle⟩
    · have hStep := DirectedRungCycle.rotate_order (R := fun i j : Fin (k+1) => next i = j)
        (fun _ => rfl)
      have hList : 0 :: markers (init ++ [Sum.inr 0]) = markers (start :: init) ++ [0] := by
        simp only [markers, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          List.cons_append, start]
      rw [hList, hMarkerEq]
      exact hStep

private theorem linkage_of_digraph (ν τ α : ℝ) (hν : 0 < ν)
    (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (G : SimpleGraph V),
      (∀ {u v}, D.Adj u v → G.Adj u v) →
      N ≤ Fintype.card V → DirectedRobustExpansion.IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (DirectedRobustExpansion.inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (DirectedRobustExpansion.outDegree D v:ℝ)) →
      ∀ {p : ℕ}, 0 < p → (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∀ (a b : Fin p → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) →
        ∃ P : ∀ i, G.Walk (a i) (b i),
          (∀ i,(P i).IsPath) ∧
          (∀ i j,i ≠ j → ∀ v,v ∈ (P i).support → v ∉ (P j).support) ∧
          ∀ v, ∃ i,v ∈ (P i).support := by
  obtain ⟨N,hN⟩ := exists_paired_ordered_cycle_threshold.{u} ν τ α hν hSmall hντ hτα hα
  refine ⟨N, ?_⟩
  intro V _ D G hDG hn hR hIn hOut p hp hpBound a b ha hb hab
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hScale := mul_le_mul_of_nonneg_right hSmall
    (mul_nonneg (pow_nonneg hν.le 3) (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _))
  have hCount : ((k+1:ℕ):ℝ) ≤ (ν/4)^3*(Fintype.card V:ℝ) := by
    change ((k+1:ℕ):ℝ) ≤ ν^4*(Fintype.card V:ℝ) at hpBound
    nlinarith only [hScale,hpBound]
  obtain ⟨init,hSimple,hCover,hOrder,hCycle⟩ :=
    hN D hn hR hIn hOut k hCount a b ha hb hab
  exact PairedHamiltonDecode.paths_of_hamilton_cycle a b ha hb (finRotate (k+1))
    D G hDG hab init 0 hSimple hCover hOrder hCycle

/-- For fixed normalized parameters there is a single order threshold.
Up to `ν^4 n` prescribed pairs of distinct endpoints can be joined by
pairwise vertex-disjoint paths that together cover every vertex. -/
theorem exists_spanning_linkage_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], N ≤ Fintype.card V → RobustExpansion.IsRealRobust G ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (G.degree v:ℝ)) →
      ∀ {p : ℕ}, 0 < p → (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∀ (a b : Fin p → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) →
        ∃ P : ∀ i, G.Walk (a i) (b i),
          (∀ i,(P i).IsPath) ∧
          (∀ i j,i ≠ j → ∀ v,v ∈ (P i).support → v ∉ (P j).support) ∧
          ∀ v, ∃ i,v ∈ (P i).support := by
  obtain ⟨N, hN⟩ := linkage_of_digraph.{u} ν τ α hν hSmall hντ hτα hα
  refine ⟨N, ?_⟩
  intro V _ _ G _ hSize hRobust hDegree
  exact hN (symmetric G) G (fun h => h) hSize (symmetric_robust G ν τ hRobust)
    (fun v => by rw [symmetric_inDegree]; exact hDegree v)
    (fun v => by rw [symmetric_outDegree]; exact hDegree v)

/-- Chen–McDonald–Shan Lemma 3.15 with the explicit hierarchy
`0 < ν ≤ τ` and `256τ ≤ α ≤ 1`. -/
theorem cms_lemma_3_15 (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], N ≤ Fintype.card V → RobustExpansion.IsRealRobust G ν τ →
      α*(Fintype.card V:ℝ) ≤ (G.minDegree:ℝ) →
      ∀ {p : ℕ}, 0 < p → (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∀ (a b : Fin p → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) →
        ∃ P : ∀ i, G.Walk (a i) (b i),
          (∀ i,(P i).IsPath) ∧
          (∀ i j,i ≠ j → ∀ v,v ∈ (P i).support → v ∉ (P j).support) ∧
          ∀ v, ∃ i,v ∈ (P i).support := by
  obtain ⟨N,hN⟩ := exists_spanning_linkage_threshold.{u} ν τ α hν
    (by linarith only [hντ,hτα,hα]) hντ hτα hα
  refine ⟨N, ?_⟩
  intro V _ _ G _ hSize hRobust hMin
  exact hN G hSize hRobust (fun v => hMin.trans (by exact_mod_cast G.minDegree_le_degree v))

end OverfullWork.RobustSpanningLinkage
