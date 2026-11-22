module

public import OverfullWork.CMSOperation41CoreCreditMass
public import OverfullWork.CMSOperation41EvenAuxiliaryWords
public import OverfullWork.CMSOperation41OddAuxiliaryWords

@[expose] public section


/-! Put the endpoint words of S2.1 into the format consumed by the
simultaneous core packing. Only actual gap occurrences are marked. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PaperLowSkeleton LowSkeletonPreparation
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem exists_body_between_distinct_ends (L : List V) (a b : V) (hne : a ≠ b)
    (hStart : L.head? = some a) (hEnd : L.getLast? = some b) :
    ∃ T : List V,L = a :: T ++ [b] := by
  obtain ⟨first,hl⟩ := List.head?_eq_some_iff.mp hStart
  obtain ⟨last,hr⟩ := List.getLast?_eq_some_iff.mp hEnd
  cases last with
  | nil =>
    rw [hr] at hStart
    simp only [List.nil_append,List.head?_cons,Option.some.injEq] at hStart
    exact (hne hStart.symm).elim
  | cons x T =>
    refine ⟨T,?_⟩
    have he : a :: first = x :: (T++[b]) := hl.symm.trans hr
    rw [←(List.cons.inj he).1] at hr
    exact hr

namespace TrimmingReplacementWords

set_option maxHeartbeats 2000000 in
/-- Convert disjoint prescribed words with named core endpoints into
fixed layout occurrences. No choice of a flexible core path is needed. -/
theorem exists_of_full_words {I : Type*} (G : SimpleGraph V) (U : Finset V)
    (endpoint : (I × Bool) ↪ ↥(Uᶜ : Finset V)) (full : I → List V) (gaps : Finset (Sym2 V))
    (hStart : ∀ i,(full i).head? = some (endpoint (i,false)).val)
    (hEnd : ∀ i,(full i).getLast? = some (endpoint (i,true)).val)
    (hSimple : ∀ i,(full i).Nodup)
    (hChain : ∀ i,(full i).IsChain (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hWitness : ∀ e ∈ gaps,∃ i a b,e = s(a,b) ∧ List.IsInfix [a,b] (full i))
    (hCore : ∀ i v,v ∈ full i → v ∉ U →
      v = (endpoint (i,false)).val ∨ v = (endpoint (i,true)).val)
    (hDisjoint : ∀ i j,i ≠ j → List.Disjoint (full i) (full j)) :
    ∃ R : TrimmingReplacementWords G U I,R.endpoint = endpoint ∧ R.gaps = gaps ∧
      ∀ i,R.word i = full i := by
  have hNe (i : I) : (endpoint (i,false)).val ≠ (endpoint (i,true)).val := by
    intro h
    have he := endpoint.injective (Subtype.ext h)
    cases congrArg Prod.snd he
  choose body hBody using fun i =>
    exists_body_between_distinct_ends (full i) _ _ (hNe i) (hStart i) (hEnd i)
  have hFull (i : I) : ((endpoint (i,false)).val :: body i ++ [(endpoint (i,true)).val]).Nodup :=
    hBody i ▸ hSimple i
  let R : TrimmingReplacementWords G U I :=
    { endpoint := endpoint
      body := body
      gaps := gaps
      chain := fun i => hBody i ▸ hChain i
      gap_witness := by
        intro e he
        obtain ⟨i,a,b,hE,hWord⟩ := hWitness e he
        exact ⟨i,a,b,hE,hBody i ▸ hWord⟩
      simple := fun i => (List.nodup_append.mp (List.nodup_cons.mp (hFull i)).2).1
      outside := by
        intro i v hv
        by_contra! hNone
        have hIn : v ∈ full i := by rw [hBody]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
        rcases hCore i v hIn hNone with he|he
        · exact (List.nodup_cons.mp (hFull i)).1 (he ▸ List.mem_append_left _ hv)
        · exact (List.disjoint_of_nodup_append (List.nodup_cons.mp (hFull i)).2) hv (by simp [he])
      disjoint := by
        intro i j hne v hi hj
        apply hDisjoint i j hne
        · rw [hBody]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hi)
        · rw [hBody]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hj) }
  exact ⟨R,rfl,rfl,fun i => (hBody i).symm⟩

end TrimmingReplacementWords

private theorem body_ne_nil_of_exceptional_occurrence {G : SimpleGraph V} {U : Finset V}
    {I : Type*} (R : TrimmingReplacementWords G U I) (i : I) {v : V}
    (hv : v ∈ U) (hWord : v ∈ R.word i) : R.body i ≠ [] := by
  intro hEmpty
  rcases (show v = (R.endpoint (i,false)).val ∨ v = (R.endpoint (i,true)).val by
    simpa [TrimmingReplacementWords.word,hEmpty] using hWord) with h | h
  · exact mem_compl.mp (R.endpoint (i,false)).property (h ▸ hv)
  · exact mem_compl.mp (R.endpoint (i,true)).property (h ▸ hv)

private theorem prescribed_edge_at_matching_leaf {G : SimpleGraph V} {U W : Finset V} {I : Type*}
    (R : TrimmingReplacementWords G U I)
    (hMarked : ∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b))
    {w a : V} (ha : a ∉ W)
    (hWord : ∃ i,List.IsInfix [w,a] (R.word i) ∨ List.IsInfix [a,w] (R.word i)) :
    R.prescribedGraph.Adj w a := by
  apply (R.prescribedGraph_adj _ _).mpr
  refine ⟨?_,hWord⟩
  intro h
  obtain ⟨x,hx,y,hy,hEq⟩ := hMarked _ h
  rcases Sym2.eq_iff.mp hEq with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact ha hy
  · exact ha hx

private theorem preserved_matching_edges {G M : SimpleGraph V} [DecidableRel M.Adj]
    {U W : Finset V} {I : Type*} (R : TrimmingReplacementWords G U I)
    (hM : IsSkeleton G M W) (hOutside : ∀ v,v ∉ W → M.degree v ≤ 1)
    (hLeaf : ∀ a : outerLeaves M W,∃ w ∈ W,M.Adj w a.val ∧ R.prescribedGraph.Adj w a.val) :
    M ≤ R.prescribedGraph := by
  have hEdge {u v : V} (hv : v ∉ W) (h : M.Adj u v) : R.prescribedGraph.Adj u v := by
    have hPos := (M.degree_pos_iff_exists_adj v).mpr ⟨u,h.symm⟩
    have hOne : M.degree v = 1 := by have hc := hOutside v hv; omega
    let a : outerLeaves M W := ⟨v,mem_filter.mpr ⟨mem_compl.mpr hv,hOne⟩⟩
    obtain ⟨w,_,hw,hPhysical⟩ := hLeaf a
    obtain ⟨x,_,hUnique⟩ := (degree_eq_one_iff_existsUnique_adj (G := M)).mp hOne
    have hEq := (hUnique _ hw.symm).trans (hUnique _ h.symm).symm
    exact hEq ▸ hPhysical
  intro u v h
  rcases hM.crosses u v h with hu | hv
  · exact hEdge hu.2 h
  · exact (hEdge hv.2 h.symm).symm

set_option maxHeartbeats 2300000 in
theorem exists_even_skeleton_prescription {G M : SimpleGraph V} [DecidableRel M.Adj]
    {U W Z : Finset V} (hWU : W ⊆ U) (hM : IsSkeleton G M W) (hMatch : OneFactor.IsMatchingGraph M)
    (P : LowSkeletonProjection.Projection G (outerLeaves M W) U Z) :
    ∃ (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      0 < f ∧ 2*f = (outerLeaves M W).card ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      (∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b)) ∧
      (∀ i,R.body i ≠ []) ∧
      (∀ v,v ∈ Set.range R.endpoint ↔ ∃ a : outerLeaves M W,P.representative a = v) ∧
      (∀ a : outerLeaves M W,a.val ∉ U → ∃ w ∈ W,M.Adj w a.val ∧ R.prescribedGraph.Adj w a.val) ∧
      M ≤ R.prescribedGraph ∧
      (∀ i v,v ∈ R.body i → v ∉ W → ∃ w ∈ W,M.Adj w v) := by
  obtain ⟨f,e,low,word,hf,hCard,hLow,hRange,hWords,hOut,hDis,hMatching,hLeafMem⟩ :=
    exists_even_matching_auxiliary_words hWU hM hMatch P
  let gaps : Finset (Sym2 V) := univ.image (fun i : Fin f => s(low (i,false),low (i,true)))
  have hChain (i : Fin f) : (word i).IsChain (fun u v => G.Adj u v ∨ s(u,v) ∈ gaps) := by
    apply (hWords i).2.2.2.1.imp
    rintro _ _ (h|⟨rfl,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  have hGap (x : Sym2 V) (hx : x ∈ gaps) : ∃ i a b,x = s(a,b) ∧ List.IsInfix [a,b] (word i) := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ⟨i,_,_,rfl,(hWords i).2.2.2.2⟩
  obtain ⟨R,hEnd,hRGap,hFull⟩ := TrimmingReplacementWords.exists_of_full_words G U e word gaps
    (fun i => (hWords i).2.1) (fun i => (hWords i).2.2.1) (fun i => (hWords i).1)
    hChain hGap (fun i v hv => (hOut i v hv).mp) hDis
  have hMarked (edge : Sym2 V) (he : edge ∈ R.gaps) : ∃ a ∈ W,∃ b ∈ W,edge = s(a,b) := by
    rw [hRGap] at he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact ⟨low (i,false),hLow _,low (i,true),hLow _,rfl⟩
  have hLeaf (a : outerLeaves M W) : ∃ w ∈ W,M.Adj w a.val ∧ R.prescribedGraph.Adj w a.val := by
    obtain ⟨w,hw,hEdge,hWord⟩ := hMatching a
    have ha := mem_compl.mp (mem_filter.mp a.property).1
    exact ⟨w,hw,hEdge,prescribed_edge_at_matching_leaf R hMarked ha (by simpa only [hFull] using hWord)⟩
  refine ⟨f,R,hf,hCard,?_,?_,hMarked,?_,?_,fun a _ => hLeaf a,
    preserved_matching_edges R hM (fun v _ => matching_degree_le_one M hMatch v) hLeaf,?_⟩
  · let i : Fin f := ⟨0,hf⟩
    rw [hRGap]
    exact ⟨s(low (i,false),low (i,true)),mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  · apply R.core_incident_gaps_eq_empty_of_exceptional_pairs
    intro edge he
    obtain ⟨a,ha,b,hb,hEq⟩ := hMarked edge he
    exact ⟨a,hWU ha,b,hWU hb,hEq⟩
  · intro i
    apply body_ne_nil_of_exceptional_occurrence R i (hWU (hLow (i,false)))
    rw [hFull]
    exact (hWords i).2.2.2.2.subset List.mem_cons_self
  · simpa only [hEnd] using hRange
  · intro i v hv hW
    have hvWord : v ∈ word i := by
      rw [←hFull]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
    let a : outerLeaves M W := ⟨v,hLeafMem i v hvWord (R.outside i v hv) hW⟩
    obtain ⟨w,hw,he,_⟩ := hLeaf a
    exact ⟨w,hw,he⟩

set_option maxHeartbeats 2300000 in
theorem exists_odd_skeleton_prescription {G M : SimpleGraph V} [DecidableRel M.Adj]
    {U W Z : Finset V} (hWU : W ⊆ U) (hMatch : OneFactor.IsMatchingGraph M)
    {w a b : V} (hw : w ∈ W) (hwa : M.Adj w a) (hb : b ∉ W) (hab : a ≠ b)
    (hS : IsSkeleton G (M ⊔ edge w b) W)
    (haA : a ∈ outerLeaves (M ⊔ edge w b) W) (hbA : b ∈ outerLeaves (M ⊔ edge w b) W)
    (hFour : 4 ≤ (outerLeaves (M ⊔ edge w b) W).card)
    (P : LowSkeletonProjection.Projection G (outerLeaves (M ⊔ edge w b) W) U Z) :
    ∃ (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      2 ≤ f ∧ 2*f = (outerLeaves (M ⊔ edge w b) W).card ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      (∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b)) ∧
      (∀ i,R.body i ≠ []) ∧
      (∀ v,v ∈ Set.range R.endpoint ↔ ∃ a : outerLeaves (M ⊔ edge w b) W,P.representative a = v) ∧
      (∀ c : outerLeaves (M ⊔ edge w b) W,c.val ∉ U →
        ∃ x ∈ W,(M ⊔ edge w b).Adj x c.val ∧ R.prescribedGraph.Adj x c.val) ∧
      M ⊔ edge w b ≤ R.prescribedGraph ∧
      (∀ i v,v ∈ R.body i → v ∉ W → ∃ x ∈ W,(M ⊔ edge w b).Adj x v) := by
  obtain ⟨f,e,word,gap,k,hf,hCard,hRange,hNone,hWords,hGapWord,hGapLow,hOut,hDis,hOccurs,hMatching,hLeafMem⟩ :=
    exists_odd_matching_auxiliary_words hWU hMatch hw hwa hb hab hS haA hbA hFour P
  let gapAt (p : V × V) : Sym2 V := s(p.1,p.2)
  let gaps : Finset (Sym2 V) := univ.biUnion (fun i : Fin f => (gap i).toFinset.image gapAt)
  have hChain (i : Fin f) : (word i).IsChain (fun u v => G.Adj u v ∨ s(u,v) ∈ gaps) := by
    apply (hWords i).2.2.2.imp
    intro u v h
    rcases h with h|h
    · exact Or.inl h
    · exact Or.inr (mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨(u,v),by simp [h],rfl⟩⟩)
  have hGap (x : Sym2 V) (hx : x ∈ gaps) : ∃ i a b,x = s(a,b) ∧ List.IsInfix [a,b] (word i) := by
    obtain ⟨i,_,hx⟩ := mem_biUnion.mp hx
    obtain ⟨⟨u,v⟩,hi,rfl⟩ := mem_image.mp hx
    exact ⟨i,u,v,rfl,hGapWord i u v ((Option.mem_toFinset.mp hi))⟩
  obtain ⟨R,hEnd,hRGap,hFull⟩ := TrimmingReplacementWords.exists_of_full_words G U e word gaps
    (fun i => (hWords i).2.1) (fun i => (hWords i).2.2.1) (fun i => (hWords i).1)
    hChain hGap (fun i v hv => (hOut i v hv).mp) hDis
  have hMarked (edge : Sym2 V) (he : edge ∈ R.gaps) : ∃ a ∈ W,∃ b ∈ W,edge = s(a,b) := by
    rw [hRGap] at he
    obtain ⟨i,_,he⟩ := mem_biUnion.mp he
    obtain ⟨⟨x,y⟩,hMem,rfl⟩ := mem_image.mp he
    obtain ⟨hx,hy⟩ := hGapLow i x y (Option.mem_toFinset.mp hMem)
    exact ⟨x,hx,y,hy,rfl⟩
  have hLeaf (c : outerLeaves (M ⊔ edge w b) W) :
      ∃ x ∈ W,(M ⊔ edge w b).Adj x c.val ∧ R.prescribedGraph.Adj x c.val := by
    obtain ⟨x,hx,hH,hWord⟩ := hMatching c
    have hc := mem_compl.mp (mem_filter.mp c.property).1
    exact ⟨x,hx,hH,prescribed_edge_at_matching_leaf R hMarked hc (by simpa only [hFull] using hWord)⟩
  have hOutside (z : V) (hz : z ∉ W) : (M ⊔ edge w b).degree z ≤ 1 := by
    by_cases hzb : z = b
    · subst z
      exact (mem_filter.mp hbA).2.le
    have hzw : z ≠ w := fun h => hz (h.symm ▸ hw)
    have hAdj (x : V) : (M ⊔ edge w b).Adj z x ↔ M.Adj z x := by
      refine ⟨fun h => h.resolve_right ?_,Or.inl⟩
      intro h
      exact ((edge_adj w b z x).mp h).1.elim (fun h => hzw h.1) (fun h => hzb h.1)
    have hEq : (M ⊔ edge w b).neighborFinset z = M.neighborFinset z := by
      ext x
      simpa only [mem_neighborFinset] using hAdj x
    rw [←card_neighborFinset_eq_degree,hEq,card_neighborFinset_eq_degree]
    exact matching_degree_le_one M hMatch z
  refine ⟨f,R,hf,hCard,?_,?_,hMarked,?_,?_,fun c _ => hLeaf c,
    preserved_matching_edges R hS hOutside hLeaf,?_⟩
  · let i : Fin f := if k.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
    have hne : i ≠ k := by
      intro h
      have he := congrArg Fin.val h
      by_cases hk : k.val = 0
      · simp only [i,if_pos hk] at he
        omega
      · simp only [i,if_neg hk] at he
        omega
    cases he : gap i with
    | none => exact (hne ((hNone i).mp he)).elim
    | some p =>
      rw [hRGap]
      exact ⟨gapAt p,mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨p,by simp [he],rfl⟩⟩⟩
  · apply R.core_incident_gaps_eq_empty_of_exceptional_pairs
    intro edge he
    obtain ⟨a,ha,b,hb,hEq⟩ := hMarked edge he
    exact ⟨a,hWU ha,b,hWU hb,hEq⟩
  · intro i
    obtain ⟨v,hv,hMem⟩ := hOccurs i
    exact body_ne_nil_of_exceptional_occurrence R i (hWU hv) ((hFull i).symm ▸ hMem)
  · simpa only [hEnd] using hRange
  · intro i v hv hW
    have hvWord : v ∈ word i := by
      rw [←hFull]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
    let c : outerLeaves (M ⊔ edge w b) W := ⟨v,hLeafMem i v hvWord (R.outside i v hv) hW⟩
    obtain ⟨x,hx,he,_⟩ := hLeaf c
    exact ⟨x,hx,he⟩

end OverfullWork.CMSTrimmingRound
