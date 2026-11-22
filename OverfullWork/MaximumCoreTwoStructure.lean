module

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
public import OverfullWork.MaximumCoreDegree
public import OverfullWork.Critical

@[expose] public section


/-!
# The structural Hilton–Zhao lemma for cores of maximum degree two

Adapted locally from `CoreDeg2/Basic.lean` in the reviewed
`hilton-zhao-cariolaro` source (commit prefix `9cc9`). The proof uses
edge-minimal extraction, Vizing's adjacency lemma, and connectivity.
This is the structural lemma, not the Hilton–Zhao classification conjecture.
The core parameters are the existing `Gate8J2C.maximumCoreDegree` and
`Gate8J2C.maximumNeighbours`.
-/
namespace OverfullWork.MaximumCoreTwo
open SimpleGraph Finset Overfull
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

omit [Fintype V] [DecidableEq V] in
theorem exists_adj_of_not_colorable (G : SimpleGraph V) {k : ℕ}
    (h : ¬ G.lineGraph.Colorable k) : ∃ u v, G.Adj u v := by
  by_contra hne
  push Not at hne
  apply h
  have : IsEmpty G.edgeSet := ⟨fun ⟨e, he⟩ => by
    induction e using Sym2.ind with
    | h x y => exact hne x y he⟩
  exact Colorable.of_isEmpty k

omit [Fintype V] [DecidableEq V] in
/-- In a connected graph with an edge, every vertex has a neighbour. -/
theorem exists_adj_of_connected {G : SimpleGraph V} (hconn : G.Connected) {u w : V}
    (huw : G.Adj u w) (v : V) : ∃ x, G.Adj v x := by
  by_cases hvu : v = u
  · exact ⟨w, hvu ▸ huw⟩
  · obtain ⟨p⟩ := hconn.preconnected v u
    cases p with
    | nil => exact absurd rfl hvu
    | cons h _ => exact ⟨_, h⟩

/-- A connected class-two graph with maximum-core degree at most two is itself critical. -/
theorem isDeltaCritical (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hcoreBound : Gate8J2C.maximumCoreDegree G ≤ 2) (hcl : ¬ G.lineGraph.Colorable G.maxDegree) : IsDeltaCritical G := by
  classical
  set Δ := G.maxDegree with hΔ
  let coreNbrs := fun v => (G.neighborFinset v).filter fun u => G.degree u = G.maxDegree
  have hcore : ∀ v, G.degree v = G.maxDegree → #(coreNbrs v) ≤ 2 := by
    intro v hv
    exact (Gate8J2C.maximumNeighbours_le_coreDegree G v hv).trans hcoreBound
  obtain ⟨H, hHG, hHcol, hHdel⟩ := Critical.exists_edgeMinimal G hcl
  have hdegH : ∀ v, H.degree v ≤ G.degree v := fun v => degree_le_of_le hHG
  have hdegG : ∀ v, G.degree v ≤ Δ := fun v => G.degree_le_maxDegree v
  have hHΔ : H.maxDegree = Δ := by
    have hle : H.maxDegree ≤ Δ :=
      maxDegree_le_of_forall_degree_le _ _ fun v => (hdegH v).trans (hdegG v)
    by_contra hne
    exact hHcol ((LeanPool.Vizing.lineGraph_colorable H).mono (by omega))
  have hclass : IsClassTwo H := by
    unfold IsClassTwo; rw [hHΔ]; exact hHcol
  -- Vizing's adjacency lemma in `H`
  have hval : ∀ x y, H.Adj x y → Δ + 1 ≤ H.degree y +
      #((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ) := by
    intro x y hxy
    have hdel : (H.deleteEdges {s(x,y)}).EdgeColorable H.maxDegree := by
      simpa only [hHΔ] using hHdel s(x,y) hxy
    obtain ⟨c, hc⟩ := exists_colMinus_of_colorable hxy hdel
    have := val hclass hc
    rw [hHΔ] at this
    exact this
  -- vertices of degree `Δ` in `H` have degree `Δ` in `G`
  have hcoreH : ∀ z, H.degree z = Δ → G.degree z = Δ := fun z hz =>
    le_antisymm (hdegG z) (hz ▸ hdegH z)
  -- the set counted by VAL in `H` sits inside `coreNbrs x` minus `y`
  have hsub : ∀ x y, ((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ) ⊆
      (coreNbrs x).erase y := by
    intro x y z hz
    simp only [mem_filter, mem_neighborFinset] at hz
    exact mem_erase.2 ⟨hz.2.1, (mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr (hHG hz.1), hcoreH z hz.2.2⟩)⟩
  -- every vertex with an `H`-neighbour `y` has an `H`-neighbour of `H`-degree `Δ` other than `y`
  have hcoreNbr : ∀ x y, H.Adj x y → ∃ z, H.Adj x z ∧ z ≠ y ∧ H.degree z = Δ := by
    intro x y hxy
    have h1 := hval x y hxy
    have h2 : H.degree y ≤ Δ := (hdegH y).trans (hdegG y)
    obtain ⟨z, hz⟩ : ((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ).Nonempty :=
      card_pos.mp (by omega)
    simp only [mem_filter, mem_neighborFinset] at hz
    exact ⟨z, hz.1, hz.2.1, hz.2.2⟩
  -- non-isolated vertices of `H` have `H`-degree at least `Δ − 1`
  have hlow : ∀ y w, H.Adj y w → Δ ≤ H.degree y + 1 := by
    intro y w hyw
    obtain ⟨z, hyz, -, hz⟩ := hcoreNbr y w hyw
    have h1 := hval z y hyz.symm
    have h2 := card_le_card (hsub z y)
    have h3 := card_erase_le (s := coreNbrs z) (a := y)
    have h4 := hcore z (hcoreH z hz)
    omega
  -- no edge of `G` leaves the non-isolated vertices of `H`
  have hclosed : ∀ u w v, H.Adj u w → G.Adj u v → H.Adj u v := by
    intro u w v huw huv
    by_contra hnot
    have hl := hlow u w huw
    -- `G.degree u ≥ H.degree u + 1`
    have hGu : H.degree u + 1 ≤ G.degree u := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      have : insert v (H.neighborFinset u) ⊆ G.neighborFinset u := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hz
        · exact (mem_neighborFinset _ _ _).2 huv
        · exact (mem_neighborFinset _ _ _).2 (hHG ((mem_neighborFinset _ _ _).1 hz))
      have h := card_le_card this
      rwa [card_insert_of_notMem (by rwa [mem_neighborFinset])] at h
    have hGuΔ : G.degree u = Δ := le_antisymm (hdegG u) (by omega)
    obtain ⟨x, hux, -, hx⟩ := hcoreNbr u w huw
    have h1 := hval x u hux.symm
    have h2 := card_le_card (hsub x u)
    have hu_mem : u ∈ coreNbrs x := mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr (hHG hux.symm), hGuΔ⟩
    have h3 := card_erase_of_mem hu_mem
    have h4 := hcore x (hcoreH x hx)
    have h5 : H.degree u + 1 ≤ Δ := by omega
    omega
  -- `H` has an edge
  obtain ⟨u₀, w₀, hu₀⟩ := exists_adj_of_not_colorable H hHcol
  -- every vertex is non-isolated in `H`
  have hall : ∀ v, ∃ w, H.Adj v w := by
    intro v
    obtain ⟨p⟩ := hconn.preconnected u₀ v
    suffices ∀ a b (q : G.Walk a b), (∃ w, H.Adj a w) → ∃ w, H.Adj b w from
      this _ _ p ⟨w₀, hu₀⟩
    intro a b q
    induction q with
    | nil => exact id
    | cons h _ ih =>
      intro ⟨w, hw⟩
      exact ih ⟨_, (hclosed _ w _ hw h).symm⟩
  have hGH : G ≤ H := by
    intro u v huv
    obtain ⟨w, hw⟩ := hall u
    exact hclosed u w v hw huv
  have hHeq : H = G := le_antisymm hHG hGH
  subst hHeq
  exact ⟨hconn, hcl, hHdel⟩

/-- Every vertex has two maximum-degree neighbours in a connected class-two
 graph with maximum-core degree at most two. -/
theorem two_le_maximumNeighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hcl : ¬G.EdgeColorable G.maxDegree) (v : V) :
    2 ≤ Gate8J2C.maximumNeighbours G v := by
  have hcrit := isDeltaCritical G hconn hcore hcl
  obtain ⟨u,w,huw⟩ := exists_adj_of_not_colorable G hcl
  apply Gate8J2C.critical_maximumNeighbours_ge_two G hcrit _ v
  intro a
  exact (G.degree_pos_iff_exists_adj a).mpr (exists_adj_of_connected hconn huw a)

/-- The maximum-degree core is two-regular, expressed in the existing
 maximum-neighbour interface. -/
theorem maximumNeighbours_eq_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hcl : ¬G.EdgeColorable G.maxDegree) {v : V} (hv : G.degree v=G.maxDegree) :
    Gate8J2C.maximumNeighbours G v = 2 :=
  le_antisymm ((Gate8J2C.maximumNeighbours_le_coreDegree G v hv).trans hcore)
    (two_le_maximumNeighbours G hconn hcore hcl v)

/-- The induced graph on all maximum-degree vertices is two-regular. -/
theorem maximum_core_two_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hcl : ¬G.EdgeColorable G.maxDegree) :
    (G.induce {v | G.degree v=G.maxDegree}).IsRegularOfDegree 2 := by
  intro v
  rw [←card_neighborSet_eq_degree]
  let e : (G.induce {w | G.degree w=G.maxDegree}).neighborSet v ≃
      ↥((G.neighborFinset v.val).filter fun w => G.degree w=G.maxDegree) :=
    { toFun := fun w => ⟨w.val.val,mem_filter.mpr
        ⟨(mem_neighborFinset _ _ _).mpr w.property,w.val.property⟩⟩
      invFun := fun w => ⟨⟨w.val,(mem_filter.mp w.property).2⟩,
        (mem_neighborFinset _ _ _).mp (mem_filter.mp w.property).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe] at hc
  exact hc.trans (maximumNeighbours_eq_two G hconn hcore hcl v.property)

/-- Every vertex has degree at least the maximum degree minus one. -/
theorem maxDegree_le_degree_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hcl : ¬G.EdgeColorable G.maxDegree) (v : V) : G.maxDegree ≤ G.degree v+1 := by
  have hcrit := isDeltaCritical G hconn hcore hcl
  obtain ⟨u,w,huw⟩ := exists_adj_of_not_colorable G hcl
  obtain ⟨a,hva⟩ := exists_adj_of_connected hconn huw v
  obtain ⟨z,hvz,_,hz⟩ := exists_maxdeg_nbr hcrit hva
  have hlo := Gate8J2C.deficit_le_maximumNeighbours G hcrit hvz.symm
  have hhi := (Gate8J2C.maximumNeighbours_le_coreDegree G z hz).trans hcore
  have hdeg := G.degree_le_maxDegree v
  omega

/-- For maximum degree at least three, some vertex has degree exactly
 the maximum degree minus one. -/
theorem exists_degree_add_one_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hcl : ¬G.EdgeColorable G.maxDegree) (hΔ : 3 ≤ G.maxDegree) :
    ∃v, G.degree v+1=G.maxDegree := by
  by_contra hne
  push Not at hne
  have hreg : ∀v, G.degree v=G.maxDegree := by
    intro v
    have := maxDegree_le_degree_add_one G hconn hcore hcl v
    have := G.degree_le_maxDegree v
    have := hne v
    omega
  obtain ⟨u,w,huw⟩ := exists_adj_of_not_colorable G hcl
  have hcount : Gate8J2C.maximumNeighbours G u = G.degree u := by
    unfold Gate8J2C.maximumNeighbours
    rw [filter_true_of_mem (fun z _ => hreg z),card_neighborFinset_eq_degree]
  have hbound := (Gate8J2C.maximumNeighbours_le_coreDegree G u (hreg u)).trans hcore
  rw [hcount,hreg u] at hbound
  omega

/-- A vertex two or more below the maximum degree excludes class two
 under the connected maximum-core-degree-two hypothesis. -/
theorem edgeColourable_of_low_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hlow : ∃v, G.degree v+2 ≤ G.maxDegree) : G.EdgeColorable G.maxDegree := by
  by_contra hcl
  obtain ⟨v,hv⟩ := hlow
  have := maxDegree_le_degree_add_one G hconn hcore hcl v
  omega

/-- A maximum-degree vertex with at most one maximum-degree neighbour
 excludes class two under the same structural hypothesis. -/
theorem edgeColourable_of_core_leaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : Gate8J2C.maximumCoreDegree G ≤ 2)
    (hleaf : ∃v, G.degree v=G.maxDegree ∧ Gate8J2C.maximumNeighbours G v ≤ 1) :
    G.EdgeColorable G.maxDegree := by
  by_contra hcl
  obtain ⟨v,_,hv⟩ := hleaf
  have := two_le_maximumNeighbours G hconn hcore hcl v
  omega

end OverfullWork.MaximumCoreTwo
