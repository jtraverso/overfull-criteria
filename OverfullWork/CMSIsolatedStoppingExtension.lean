module

public import OverfullWork.CMSOddStoppingExtension

@[expose] public section


/-! The isolated-vertex extension in CMS Case 1.1. The odd old graph
has at least two deficient vertices because it has no isolated vertex
and its total degree deficit is at least the maximum degree. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph OddCutDeficit
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isolatedStoppingExtension (G : SimpleGraph V) : SimpleGraph (Option V) :=
  G.map (⟨some,Option.some_injective V⟩ : V ↪ Option V)

theorem isolated_stopping_extension_adj_old (G : SimpleGraph V) (u v : V) :
    (isolatedStoppingExtension G).Adj (some u) (some v) ↔ G.Adj u v :=
  map_adj_apply (f := ⟨some,Option.some_injective V⟩)

theorem isolated_stopping_extension_not_adj_new (G : SimpleGraph V) (v : Option V) :
    ¬(isolatedStoppingExtension G).Adj none v := by
  rintro ⟨_,u,_,_,hu,_⟩
  change some u = none at hu
  nomatch hu

theorem isolated_stopping_extension_degree_new (G : SimpleGraph V) :
    (isolatedStoppingExtension G).degree none = 0 := by
  by_contra hn
  obtain ⟨v,hv⟩ := ((isolatedStoppingExtension G).degree_pos_iff_exists_adj none).mp
    (Nat.pos_of_ne_zero hn)
  exact isolated_stopping_extension_not_adj_new G v hv

theorem isolated_stopping_extension_degree_old (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (isolatedStoppingExtension G).degree (some u) = G.degree u := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree,
    ←card_image_of_injective _ (Option.some_injective V)]
  congr 1
  ext v
  cases v with
  | none =>
    have h : ¬(isolatedStoppingExtension G).Adj (some u) none := fun h =>
      isolated_stopping_extension_not_adj_new G (some u) h.symm
    simp [mem_neighborFinset,h]
  | some v =>
    simp only [mem_neighborFinset,isolated_stopping_extension_adj_old,mem_image,Option.some.injEq]
    exact ⟨fun h => ⟨v,h,rfl⟩,by rintro ⟨w,hw,rfl⟩; exact hw⟩

def isolatedStoppingCopy (G : SimpleGraph V) : Copy G (isolatedStoppingExtension G) where
  toHom := {toFun := some,map_rel' := fun h => (isolated_stopping_extension_adj_old _ _ _).mpr h}
  injective' := Option.some_injective V

theorem isolated_stopping_extension_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    (isolatedStoppingExtension G).maxDegree = G.maxDegree := by
  apply le_antisymm _ (isolatedStoppingCopy G).maxDegree_mono
  apply (isolatedStoppingExtension G).maxDegree_le_of_forall_degree_le
  intro v
  cases v with
  | none => rw [isolated_stopping_extension_degree_new]; exact Nat.zero_le _
  | some v => rw [isolated_stopping_extension_degree_old]; exact G.degree_le_maxDegree _

private theorem sum_over_old {M : Type*} [AddCommMonoid M]
    (S : Finset (Option V)) (f : Option V → M) (hf : f none = 0) :
    (∑ v ∈ S,f v) = ∑ v ∈ S.eraseNone,f (some v) := by
  have hMap := sum_map S.eraseNone (Function.Embedding.some : V ↪ Option V) f
  rw [map_some_eraseNone] at hMap
  change (∑ v ∈ S.erase none,f v) = ∑ v ∈ S.eraseNone,f (some v) at hMap
  rw [←hMap]
  by_cases h : none ∈ S
  · rw [←sum_erase_add S f h,hf,add_zero]
  · rw [erase_eq_of_notMem h]

private theorem twice_internal_edges_as_rows {T : Type*}
    [Fintype T] [DecidableEq T] (H : SimpleGraph T) [DecidableRel H.Adj] (U : Finset T) :
    2*internalEdges H U = ∑ v ∈ U,∑ w ∈ U,if H.Adj v w then 1 else 0 := by
  rw [internalEdges_eq_multigraph,←MultiGraph.twiceInternal_eq]
  simp only [MultiGraph.twiceInternal,MultiGraph.ofSimpleGraph,mem_edgeSet]

theorem isolated_stopping_extension_internalEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Option V)) :
    internalEdges (isolatedStoppingExtension G) S = internalEdges G S.eraseNone := by
  let H := isolatedStoppingExtension G
  have hNo (u : Option V) : ¬H.Adj u none := fun h =>
    isolated_stopping_extension_not_adj_new G u h.symm
  have h := twice_internal_edges_as_rows H S
  rw [sum_over_old S _ (by simp [H,isolated_stopping_extension_not_adj_new])] at h
  have hRow (v : V) : (∑ w ∈ S,if H.Adj (some v) w then 1 else 0) =
      ∑ w ∈ S.eraseNone,if G.Adj v w then 1 else 0 := by
    rw [sum_over_old S _ (by simp [hNo])]
    simp only [H,isolated_stopping_extension_adj_old]
  simp_rw [hRow] at h
  rw [←twice_internal_edges_as_rows G] at h
  change internalEdges H S = internalEdges G S.eraseNone
  omega

theorem isolated_stopping_extension_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNo : ¬G.HasOverfullSubgraph) : ¬(isolatedStoppingExtension G).HasOverfullSubgraph := by
  rintro ⟨S,hS⟩
  change (isolatedStoppingExtension G).maxDegree*(S.card/2) <
    internalEdges (isolatedStoppingExtension G) S at hS
  rw [isolated_stopping_extension_maxDegree,isolated_stopping_extension_internalEdges] at hS
  apply hNo
  refine ⟨S.eraseNone,?_⟩
  change G.maxDegree*(S.eraseNone.card/2) < internalEdges G S.eraseNone
  have hCard : S.eraseNone.card ≤ S.card := by
    by_cases h : none ∈ S
    · rw [card_eraseNone_of_mem h]; exact Nat.sub_le _ _
    · rw [card_eraseNone_of_not_mem h]
  exact (Nat.mul_le_mul_left _ (Nat.div_le_div_right hCard)).trans_lt hS

theorem two_deficient_of_odd_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hOdd : Odd (Fintype.card V)) (hPos : ∀ v,0 < G.degree v)
    (hNo : ¬G.HasOverfullSubgraph) :
    2 ≤ (univ.filter fun v => G.degree v < G.maxDegree).card := by
  let D : Finset V := univ.filter fun v => G.degree v < G.maxDegree
  let d := G.maxDegree
  have hn : 0 < Fintype.card V := by obtain ⟨k,hk⟩ := hOdd; omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
  have hd : 0 < d := (hPos v).trans_le (G.degree_le_maxDegree _)
  have hNo' : internalEdges G (univ : Finset V) ≤ d*((univ : Finset V).card/2) := by
    exact not_lt.mp (fun hh => hNo ⟨univ,hh⟩)
  have hOdd' : Odd (univ : Finset V).card := by rwa [card_univ]
  have hBound := (odd_internal_bound_iff_cut_deficit G d G.degree_le_maxDegree univ hOdd').mp hNo'
  have hMass : d ≤ ∑ w ∈ D,(d-G.degree w) := by
    have hSum : (∑ w ∈ D,(d-G.degree w)) = deficitMass G d univ := by
      unfold deficitMass
      rw [sum_filter]
      apply sum_congr rfl
      intro w _
      split_ifs with hw
      · rfl
      · have hEq : G.degree w = d := le_antisymm (G.degree_le_maxDegree _) (by omega)
        rw [hEq,Nat.sub_self]
    simpa [hSum,cutEdges,crossingEdges] using hBound
  change 2 ≤ D.card
  by_contra hn'
  have hC : D.card ≤ 1 := by omega
  by_cases h : D.Nonempty
  · obtain ⟨u,hu⟩ := h
    have hEq : D = {u} := eq_singleton_iff_unique_mem.mpr
      ⟨hu,fun w hw => by
        have le : ({u,w}:Finset V) ⊆ D := insert_subset_iff.mpr ⟨hu,singleton_subset_iff.mpr hw⟩
        have hLe := card_le_card le
        by_contra hn
        rw [card_pair (Ne.symm hn)] at hLe
        omega⟩
    rw [hEq,sum_singleton] at hMass
    have hp := hPos u
    omega
  · rw [not_nonempty_iff_eq_empty.mp h,sum_empty] at hMass
    omega

theorem isolated_stopping_extension_three_deficient
    (G : SimpleGraph V) [DecidableRel G.Adj] (hPos : ∀ v,0 < G.degree v)
    (hTwo : (univ.filter fun v => G.degree v < G.maxDegree).card = 2) :
    let H := isolatedStoppingExtension G
    ∀ p q : Option V,p ≠ q → (∀ v,H.degree p ≤ H.degree v) →
      (∀ v,v ≠ p → H.degree q ≤ H.degree v) →
      ∃ w : Option V,w ≠ p ∧ w ≠ q ∧ H.degree w < H.maxDegree ∧
        ∀ v,v ∉ ({p,q,w}:Finset (Option V)) → H.degree v = H.maxDegree := by
  intro H p q hpq hFirst hSecond
  have hp : p = none := by
    cases p with
    | none => rfl
    | some p =>
      have h := hFirst none
      change (isolatedStoppingExtension G).degree (some p) ≤
        (isolatedStoppingExtension G).degree none at h
      rw [isolated_stopping_extension_degree_old,isolated_stopping_extension_degree_new] at h
      exact (not_le_of_gt (hPos p) h).elim
  subst p
  cases q with
  | none => exact (hpq rfl).elim
  | some q =>
    let D : Finset V := univ.filter fun v => G.degree v < G.maxDegree
    have hCard : D.card = 2 := hTwo
    obtain ⟨a,ha⟩ := card_pos.mp (show 0 < D.card by omega)
    have hq : q ∈ D := by
      have h := hSecond (some a) (by simp)
      change (isolatedStoppingExtension G).degree (some q) ≤
        (isolatedStoppingExtension G).degree (some a) at h
      rw [isolated_stopping_extension_degree_old,isolated_stopping_extension_degree_old] at h
      exact mem_filter.mpr ⟨mem_univ _,h.trans_lt (mem_filter.mp ha).2⟩
    have hErase : (D.erase q).card = 1 := by rw [card_erase_of_mem hq,hCard]
    obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (D.erase q).card by omega)
    obtain ⟨hwq,hwD⟩ := mem_erase.mp hw
    have hPair : ({q,w}:Finset V) = D := by
      apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hq,singleton_subset_iff.mpr hwD⟩)
      rw [card_pair hwq.symm,hCard]
    refine ⟨some w,by simp,by simpa using hwq,?_,?_⟩
    · change (isolatedStoppingExtension G).degree (some w) < (isolatedStoppingExtension G).maxDegree
      rw [isolated_stopping_extension_degree_old,isolated_stopping_extension_maxDegree]
      exact (mem_filter.mp hwD).2
    · intro v hv
      cases v with
      | none => exact (hv (mem_insert_self _ _)).elim
      | some v =>
        change (isolatedStoppingExtension G).degree (some v) = (isolatedStoppingExtension G).maxDegree
        rw [isolated_stopping_extension_degree_old,isolated_stopping_extension_maxDegree]
        apply le_antisymm (G.degree_le_maxDegree _)
        by_contra h
        have hin : v ∈ D := mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge h⟩
        rw [←hPair,mem_insert,mem_singleton] at hin
        exact hv (by rcases hin with rfl | rfl <;> simp)

end OverfullWork.CanonicalRegularization
