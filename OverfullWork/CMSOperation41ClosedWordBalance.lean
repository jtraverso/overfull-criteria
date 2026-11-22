module

public import OverfullWork.CMSOperation41ClosedWord
public import OverfullWork.MaximumMatchingPeeling

@[expose] public section


/-! Recover the degree of an expanded cycle by restoring its marked
edges. These edges can be absent from the source graph. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The simple graph of the marked pairs, whether or not those pairs
are edges of the source graph. -/
def trimmingGapGraph (gaps : Finset (Sym2 V)) : SimpleGraph V :=
  fromRel (fun a b => s(a,b) ∈ gaps)

omit [Fintype V] [DecidableEq V] in
theorem trimmingGapGraph_adj (gaps : Finset (Sym2 V)) (a b : V) :
    (trimmingGapGraph gaps).Adj a b ↔ a ≠ b ∧ s(a,b) ∈ gaps := by
  have hSwap : s(b,a) = s(a,b) := Sym2.eq_swap
  simp only [trimmingGapGraph,fromRel_adj,hSwap,or_self]

theorem trimming_gap_degree_eq_card_incident_pairs (gaps : Finset (Sym2 V)) (v : V) :
    (trimmingGapGraph gaps).degree v = (gaps.filter (fun edge => v ∈ edge ∧ ¬edge.IsDiag)).card := by
  let J := trimmingGapGraph gaps
  have hInj : Function.Injective (fun u : V => s(v,u)) := fun _ _ he => Sym2.congr_right.mp he
  have hEdges : (J.neighborFinset v).image (fun u => s(v,u)) =
      gaps.filter (fun edge => v ∈ edge ∧ ¬edge.IsDiag) := by
    ext edge
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := mem_image.mp h
      obtain ⟨hne,hGap⟩ := (trimmingGapGraph_adj gaps v u).mp ((mem_neighborFinset J v u).mp hu)
      exact mem_filter.mpr ⟨hGap,Sym2.mem_iff.mpr (Or.inl rfl),fun h => hne (Sym2.mk_isDiag_iff.mp h)⟩
    · intro h
      obtain ⟨hGap,hMem,hNotDiag⟩ := mem_filter.mp h
      obtain ⟨u,rfl⟩ := Sym2.mem_iff_exists.mp hMem
      exact mem_image.mpr ⟨u,(mem_neighborFinset J v u).mpr
        ((trimmingGapGraph_adj gaps v u).mpr ⟨fun he => hNotDiag (Sym2.mk_isDiag_iff.mpr he),hGap⟩),rfl⟩
  change J.degree v = _
  rw [←hEdges,card_image_of_injective _ hInj,card_neighborFinset_eq_degree]

theorem trimming_gap_degree_of_single_pair {a b : V} (hne : a ≠ b) (v : V) :
    (trimmingGapGraph ({s(a,b)} : Finset (Sym2 V))).degree v =
      if v = a ∨ v = b then 1 else 0 := by
  rw [trimming_gap_degree_eq_card_incident_pairs,filter_singleton]
  simp only [Sym2.mem_iff,Sym2.mk_isDiag_iff,hne,not_false_eq_true,and_true]
  split_ifs with h <;> simp [h]

set_option maxHeartbeats 1800000 in
/-- Every vertex of the cyclic word has exactly two incident positions.
Its physical degree plus its degree in the marked pairs is two. Outside
that word both degrees vanish. -/
theorem closed_word_degree_with_gaps {n : ℕ} (T : List V) (x : V)
    (hLength : T.length = n+3) (hNodup : T.Nodup) (hHead : T.head? = some x)
    (gaps : Finset (Sym2 V)) (Q : SimpleGraph V)
    (hGap : ∀ edge ∈ gaps, ∃ a b,edge = s(a,b) ∧ List.IsInfix [a,b] (T ++ [x]))
    (hQ : ∀ a b,Q.Adj a b ↔ s(a,b) ∉ gaps ∧
      (List.IsInfix [a,b] (T ++ [x]) ∨ List.IsInfix [b,a] (T ++ [x]))) :
    ∀ v,Q.degree v+(trimmingGapGraph gaps).degree v = if v ∈ T then 2 else 0 := by
  obtain ⟨w,hRange,hPairs⟩ := closed_word_cycle_coordinates T hLength hNodup x hHead
  let H := markedCycle (univ : Finset (Fin (n+3)))
  let C := H.map w
  let J := trimmingGapGraph gaps
  have hC (a b : V) : C.Adj a b ↔ List.IsInfix [a,b] (T ++ [x]) ∨
      List.IsInfix [b,a] (T ++ [x]) := by
    rw [hPairs,hPairs]
    constructor
    · intro h
      obtain ⟨i,j,hIJ,rfl,rfl⟩ := (map_adj w H a b).mp h
      change (i ∈ univ ∧ finRotate (n+3) i = j) ∨ (j ∈ univ ∧ finRotate (n+3) j = i) at hIJ
      rcases hIJ with ⟨_,rfl⟩|⟨_,rfl⟩
      · exact Or.inl ⟨i,rfl,rfl⟩
      · exact Or.inr ⟨j,rfl,rfl⟩
    · rintro (⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩)
      · exact (map_adj w H _ _).mpr ⟨i,finRotate (n+3) i,Or.inl ⟨mem_univ _,rfl⟩,rfl,rfl⟩
      · exact (map_adj w H _ _).mpr ⟨finRotate (n+3) i,i,Or.inr ⟨mem_univ _,rfl⟩,rfl,rfl⟩
  have hLe : J ≤ C := by
    intro a b h
    have hMem := ((trimmingGapGraph_adj gaps a b).mp h).2
    obtain ⟨u,v,hPair,hWord⟩ := hGap s(a,b) hMem
    rcases Sym2.eq_iff.mp hPair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (hC _ _).mpr (Or.inl hWord)
    · exact (hC _ _).mpr (Or.inr hWord)
  have hTrim : C \ J = Q := by
    ext a b
    rw [sdiff_adj,trimmingGapGraph_adj]
    constructor
    · rintro ⟨hEdge,hMissing⟩
      exact (hQ a b).mpr ⟨fun h => hMissing ⟨hEdge.ne,h⟩,(hC a b).mp hEdge⟩
    · intro h
      obtain ⟨hMissing,hEdge⟩ := (hQ a b).mp h
      exact ⟨(hC a b).mpr hEdge,fun h => hMissing h.2⟩
  intro v
  have hBalance := MaximumMatching.degree_sdiff_add_of_le C J hLe v
  have hBalance' : Q.degree v+J.degree v = C.degree v := by
    simpa only [hTrim,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hBalance
  rw [hBalance']
  by_cases hv : v ∈ T
  · rw [if_pos hv]
    obtain ⟨i,rfl⟩ := (hRange v).mp hv
    change (H.map w).degree (w i) = 2
    rw [map_degree_at_embedding H w,markedCycle_degree]
    simp
  · rw [if_neg hv]
    exact map_degree_outside_embedding H w v (fun h => hv ((hRange v).mpr h))

end OverfullWork.CMSTrimmingRound
