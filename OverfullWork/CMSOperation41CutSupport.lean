module

public import OverfullWork.CMSOperation41ReplacementWords
public import OverfullWork.CMSOperation41ExactRecords

@[expose] public section


/-! The virtual deletions of Operation 4.1 preserve the ordinary
host. Every physical prescribed edge meets the initial exceptional set.
An empty word body is allowed only for a marked artificial connector. -/
namespace OverfullWork.CMSTrimmingRound.TrimmingReplacementWords

open Finset SimpleGraph DirectedSpanningConfiguration DirectedRobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sup.adjDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {U : Finset V}

private theorem word_nodup (R : TrimmingReplacementWords G U I) (i : I) :
    (R.word i).Nodup := by
  let a := (R.endpoint (i,false)).val
  let b := (R.endpoint (i,true)).val
  have hA : a ∉ U := mem_compl.mp (R.endpoint (i,false)).property
  have hB : b ∉ U := mem_compl.mp (R.endpoint (i,true)).property
  have hAB : a ≠ b := by
    intro h
    have he := R.endpoint.injective (Subtype.ext h)
    cases congrArg Prod.snd he
  apply List.nodup_cons.mpr
  refine ⟨?_,List.nodup_append.mpr ⟨R.simple i,List.nodup_singleton b,?_⟩⟩
  · rintro h
    rcases List.mem_append.mp h with h | h
    · exact hA (R.outside i a h)
    · exact hAB (List.mem_singleton.mp h)
  · intro x hx y hy hEq
    have hxb : x = b := hEq.trans (List.mem_singleton.mp hy)
    apply hB
    rw [←hxb]
    exact R.outside i x hx

set_option maxHeartbeats 1600000 in
theorem prescribedGraph_meets_exceptional_set (R : TrimmingReplacementWords G U I)
    (hEmpty : ∀ i,R.body i = [] → s((R.endpoint (i,false)).val,(R.endpoint (i,true)).val) ∈ R.gaps) :
    ∀ u v,R.prescribedGraph.Adj u v → u ∈ U ∨ v ∈ U := by
  let allowed (u v : V) := u ∈ U ∨ v ∈ U ∨ s(u,v) ∈ R.gaps
  have hWord (i : I) : (R.word i).IsChain allowed := by
    let a := (R.endpoint (i,false)).val
    let b := (R.endpoint (i,true)).val
    change (a :: R.body i ++ [b]).IsChain allowed
    by_cases h : R.body i = []
    · rw [h]
      exact .cons_cons (Or.inr (Or.inr (hEmpty i h))) (.singleton _)
    have hBody : (R.body i).IsChain allowed := by
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro x y before after he
      have hx : x ∈ R.body i := by rw [he]; simp
      exact Or.inl (R.outside i x hx)
    have hFirst : (a :: R.body i).IsChain allowed := by
      apply List.isChain_cons.mpr
      refine ⟨?_,hBody⟩
      intro x hx
      exact Or.inr (Or.inl (R.outside i x (List.mem_of_mem_head? hx)))
    apply hFirst.append (.singleton b)
    intro x hx y hy
    have hx' : x ∈ (R.body i).getLast? := by
      rwa [List.getLast?_cons_of_ne_nil h] at hx
    exact Or.inl (R.outside i x (List.mem_of_mem_getLast? hx'))
  intro u v huv
  obtain ⟨hGap,i,hPair|hPair⟩ := (R.prescribedGraph_adj u v).mp huv
  · exact ((hWord i).infix hPair).rel.elim Or.inl (fun h => h.elim Or.inr (fun hg => (hGap hg).elim))
  · have hGap' : s(v,u) ∉ R.gaps := by rwa [Sym2.eq_swap]
    exact (((hWord i).infix hPair).rel.elim Or.inl
      (fun h => h.elim Or.inr (fun hg => (hGap' hg).elim))).symm

set_option maxHeartbeats 2600000 in
private theorem degree_le_of_edges_in_words (R : TrimmingReplacementWords G U I)
    (J : SimpleGraph V) (v : V)
    (hJ : ∀ u,J.Adj v u → ∃ i,List.IsInfix [v,u] (R.word i) ∨ List.IsInfix [u,v] (R.word i)) :
    J.degree v ≤ if v ∈ U then 2 else 1 := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (fun a b => Classical.propDecidable (a = b))
  have hUnique (i j : I) (hi : v ∈ R.word i) (hj : v ∈ R.word j) : i = j := by
    have hMem (k : I) (hk : v ∈ R.word k) :
        (∃ side : Bool,(R.endpoint (k,side)).val = v) ∨ v ∈ R.body k := by
      rcases List.mem_cons.mp hk with h | h
      · exact Or.inl ⟨false,h.symm⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr h
        · exact Or.inl ⟨true,(List.mem_singleton.mp h).symm⟩
    rcases hMem i hi with ⟨s,hs⟩ | hBodyI <;> rcases hMem j hj with ⟨t,ht⟩ | hBodyJ
    · exact congrArg Prod.fst (R.endpoint.injective (Subtype.ext (hs.trans ht.symm)))
    · exact (mem_compl.mp (R.endpoint (i,s)).property (hs ▸ R.outside j v hBodyJ)).elim
    · exact (mem_compl.mp (R.endpoint (j,t)).property (ht ▸ R.outside i v hBodyI)).elim
    · by_contra hne
      exact R.disjoint i j hne hBodyI hBodyJ
  by_cases hHas : ∃ i,v ∈ R.word i
  · obtain ⟨i,hi⟩ := hHas
    let a := (R.endpoint (i,false)).val
    let b := (R.endpoint (i,true)).val
    have hAB : a ≠ b := by
      intro h
      have hEq := R.endpoint.injective (Subtype.ext h)
      cases congrArg Prod.snd hEq
    have hND := word_nodup R i
    let O := univ.filter (fun u => (wordGraph (R.word i)).Adj v u)
    let N := univ.filter (fun u => (wordGraph (R.word i)).Adj u v)
    have hSub : J.neighborFinset v ⊆ O∪N := by
      intro u hu
      obtain ⟨j,hPair|hPair⟩ := hJ u ((mem_neighborFinset J v u).mp hu)
      · have he := hUnique i j hi (hPair.mem (by simp))
        exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,he.symm ▸ hPair⟩)
      · have he := hUnique i j hi (hPair.mem (by simp))
        exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,he.symm ▸ hPair⟩)
    have hO : O.card = if v ∈ a :: R.body i then 1 else 0 := by
      change outDegree (wordGraph (R.word i)) v = _
      exact word_outDegree (a :: R.body i) b v hND
    have hN : N.card = if v ∈ R.body i ++ [b] then 1 else 0 :=
      word_inDegree (R.body i ++ [b]) a v hND
    have hSum : J.degree v ≤ O.card+N.card := by
      rw [←card_neighborFinset_eq_degree]
      exact (card_le_card hSub).trans (card_union_le _ _)
    rw [hO,hN] at hSum
    by_cases hv : v ∈ U
    · rw [if_pos hv]
      split_ifs at hSum <;> omega
    · have hn : v ∉ R.body i := fun h => hv (R.outside i v h)
      rw [if_neg hv]
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,hn,or_false,false_or] at hSum
      split_ifs at hSum with ha hb
      · exact (hAB (ha.symm.trans hb)).elim
      · omega
      · omega
      · omega
  · have hZero : J.degree v = 0 := by
      by_contra! h
      obtain ⟨u,hu⟩ := (J.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero h)
      obtain ⟨i,hPair|hPair⟩ := hJ u hu
      · exact hHas ⟨i,hPair.mem (by simp)⟩
      · exact hHas ⟨i,hPair.mem (by simp)⟩
    rw [hZero]
    exact Nat.zero_le _

theorem prescribed_graph_degree_le (R : TrimmingReplacementWords G U I) (v : V) :
    R.prescribedGraph.degree v ≤ if v ∈ U then 2 else 1 := by
  apply degree_le_of_edges_in_words R
  intro u hu
  exact ((R.prescribedGraph_adj v u).mp hu).2

private theorem gap_adjacency_in_words (R : TrimmingReplacementWords G U I) {v u : V}
    (h : (trimmingGapGraph R.gaps).Adj v u) :
    ∃ i,List.IsInfix [v,u] (R.word i) ∨ List.IsInfix [u,v] (R.word i) := by
  obtain ⟨i,a,b,hEq,hPair⟩ := R.gap_witness _ ((trimmingGapGraph_adj _ _ _).mp h).2
  rcases Sym2.eq_iff.mp hEq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨i,Or.inl hPair⟩
  · exact ⟨i,Or.inr hPair⟩

private theorem prescribed_graph_disjoint_gaps (R : TrimmingReplacementWords G U I) :
    Disjoint R.prescribedGraph (trimmingGapGraph R.gaps) := by
  rw [disjoint_iff_inf_le]
  intro x y h
  exact ((R.prescribedGraph_adj _ _).mp h.1).1 ((trimmingGapGraph_adj _ _ _).mp h.2).2

theorem degree_credit_le_two (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (v : V) : R.degreeCredit omitted v ≤ 2 := by
  have hGap := degree_le_of_edges_in_words R (trimmingGapGraph R.gaps) v
    (fun _ => gap_adjacency_in_words R)
  unfold degreeCredit
  split_ifs with h
  · exact hGap.trans (by split_ifs <;> omega)
  · exact le_rfl

set_option maxHeartbeats 3200000 in
/-- An exceptional vertex needs no packed edge to determine its debit.
Its two consecutive positions are either prescribed edges or gaps. -/
theorem prescribed_degree_add_credit_on_exceptional (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) {v : V} (hv : v ∈ U) :
    R.prescribedGraph.degree v+R.degreeCredit omitted v = 2 := by
  let K := trimmingGapGraph R.gaps
  let J := R.prescribedGraph ⊔ K
  have hFromWord (u : V) (hne : v ≠ u)
      (h : ∃ i,List.IsInfix [v,u] (R.word i) ∨ List.IsInfix [u,v] (R.word i)) : J.Adj v u := by
    by_cases hGap : s(v,u) ∈ R.gaps
    · exact Or.inr ((trimmingGapGraph_adj _ _ _).mpr ⟨hne,hGap⟩)
    · exact Or.inl ((R.prescribedGraph_adj _ _).mpr ⟨hGap,h⟩)
  have hToWord (u : V) (h : J.Adj v u) :
      ∃ i,List.IsInfix [v,u] (R.word i) ∨ List.IsInfix [u,v] (R.word i) := by
    rcases h with h | h
    · exact ((R.prescribedGraph_adj _ _).mp h).2
    · exact gap_adjacency_in_words R h
  have hAdd := degree_sup_eq_add_of_disjoint_trimming R.prescribedGraph K
    (prescribed_graph_disjoint_gaps R) v
  by_cases hBody : ∃ i,v ∈ R.body i
  · obtain ⟨i,hi⟩ := hBody
    obtain ⟨L,T,hBodyEq⟩ := List.mem_iff_append.mp hi
    let a := (R.endpoint (i,false)).val
    let b := (R.endpoint (i,true)).val
    let P := a :: L
    have hNe : P ≠ [] := by simp [P]
    let x := P.getLast hNe
    have hLeft : P.dropLast++[x] = P := List.dropLast_append_getLast hNe
    have hMiddle : R.word i = P ++ v :: (T ++ [b]) := by
      simp [TrimmingReplacementWords.word,hBodyEq,a,b,P,List.append_assoc]
    cases hRight : T++[b] with
    | nil => simp at hRight
    | cons y tail =>
      have hForm : R.word i = P.dropLast ++ [x,v,y] ++ tail := by
        rw [hMiddle,hRight,←hLeft]
        simp [List.append_assoc]
      have hInfix : List.IsInfix [x,v,y] (R.word i) := ⟨P.dropLast,tail,hForm.symm⟩
      have hND := hInfix.sublist.nodup (word_nodup R i)
      have hDistinct : x ≠ v ∧ x ≠ y ∧ v ≠ y := by simpa [and_assoc] using hND
      have hFirst : List.IsInfix [x,v] (R.word i) := by
        refine ⟨P.dropLast,y::tail,?_⟩
        simp [hForm,List.append_assoc]
      have hSecond : List.IsInfix [v,y] (R.word i) := by
        refine ⟨P.dropLast++[x],tail,?_⟩
        simp [hForm,List.append_assoc]
      have hN₁ := hFromWord x hDistinct.1.symm ⟨i,Or.inr hFirst⟩
      have hN₂ := hFromWord y hDistinct.2.2 ⟨i,Or.inl hSecond⟩
      have hLower : 2 ≤ J.degree v := by
        rw [←card_neighborFinset_eq_degree,←card_pair hDistinct.2.1]
        apply card_le_card
        intro u hu
        rcases (show u=x ∨ u=y by simpa using hu) with rfl | rfl
        · exact (mem_neighborFinset J v _).mpr hN₁
        · exact (mem_neighborFinset J v _).mpr hN₂
      have hUpper := degree_le_of_edges_in_words R J v hToWord
      rw [if_pos hv] at hUpper
      rw [degreeCredit,if_pos (Or.inr ⟨i,hi⟩)]
      change R.prescribedGraph.degree v+K.degree v = 2
      change J.degree v = R.prescribedGraph.degree v+K.degree v at hAdd
      omega
  · have hAbsent (i : I) : v ∉ R.word i := by
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact mem_compl.mp (R.endpoint (i,false)).property (h ▸ hv)
      · rcases List.mem_append.mp h with h | h
        · exact hBody ⟨i,h⟩
        · exact mem_compl.mp (R.endpoint (i,true)).property ((List.mem_singleton.mp h) ▸ hv)
    have hZero : R.prescribedGraph.degree v = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      obtain ⟨u,hu⟩ := (R.prescribedGraph.degree_pos_iff_exists_adj v).mp h
      obtain ⟨i,hPair|hPair⟩ := hToWord u (Or.inl hu)
      · exact hAbsent i (hPair.mem (by simp))
      · exact hAbsent i (hPair.mem (by simp))
    rw [hZero,degreeCredit,if_neg,zero_add]
    rintro (⟨z,_,rfl⟩|h)
    · exact mem_compl.mp z.property hv
    · exact hBody h

set_option maxHeartbeats 2100000 in
theorem prescribed_degree_one_on_active_pair (R : TrimmingReplacementWords G U I)
    (W : Finset V) (hW : W ⊆ U) (hSize : W.card = 2) (hGap : R.gaps.Nonempty)
    (hMarked : ∀ e ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,e = s(a,b)) :
    ∀ w ∈ W,R.prescribedGraph.degree w = 1 := by
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < W.card)
  have hPair : W = {a,b} := by
    apply (eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨ha,singleton_subset_iff.mpr hb⟩) ?_).symm
    rw [hSize,card_pair hab]
  have hOnly (e : Sym2 V) (he : e ∈ R.gaps) : e = s(a,b) := by
    obtain ⟨u,hu,v,hv,rfl⟩ := hMarked e he
    obtain ⟨i,x,y,heq,hi⟩ := R.gap_witness _ he
    have hND := hi.sublist.nodup (word_nodup R i)
    have hxy : x ≠ y := by simpa using hND
    have huv : u ≠ v := by
      intro h
      rcases Sym2.eq_iff.mp heq with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact hxy (h₁.symm.trans (h.trans h₂))
      · exact hxy (h₂.symm.trans (h.symm.trans h₁))
    rw [hPair] at hu hv
    have hu' : u=a ∨ u=b := by simpa using hu
    have hv' : v=a ∨ v=b := by simpa using hv
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact (huv (hu'.trans hv'.symm)).elim
    · rw [hu',hv']
    · rw [hu',hv',Sym2.eq_swap]
    · exact (huv (hu'.trans hv'.symm)).elim
  obtain ⟨e,he⟩ := hGap
  have hMem : s(a,b) ∈ R.gaps := hOnly e he ▸ he
  have hGaps : R.gaps = {s(a,b)} := by
    ext f
    exact ⟨fun h => mem_singleton.mpr (hOnly f h),fun h => (mem_singleton.mp h).symm ▸ hMem⟩
  intro w hw
  have hwU := hW hw
  have hwPair : w = a ∨ w = b := by simpa [hPair] using hw
  obtain ⟨i,x,y,heq,hInfix⟩ := R.gap_witness _ hMem
  have hIncident : w ∈ s(x,y) := by
    rw [←heq]
    exact Sym2.mem_iff.mpr hwPair
  have hWord : w ∈ R.word i := hInfix.mem (by simpa using Sym2.mem_iff.mp hIncident)
  have hBody : w ∈ R.body i := by
    rcases List.mem_cons.mp hWord with h | h
    · exact (mem_compl.mp (R.endpoint (i,false)).property (h ▸ hwU)).elim
    · rcases List.mem_append.mp h with h | h
      · exact h
      · exact (mem_compl.mp (R.endpoint (i,true)).property ((List.mem_singleton.mp h) ▸ hwU)).elim
  have hBalance := R.prescribed_degree_add_credit_on_exceptional ∅ hwU
  rw [degreeCredit,if_pos (Or.inr ⟨i,hBody⟩),hGaps,trimming_gap_degree_of_single_pair hab,if_pos hwPair] at hBalance
  omega

/-- At an ordinary vertex, the prescribed physical edges never exceed
the debit of the future layer, including at an omitted endpoint. -/
theorem prescribed_degree_le_core_debit (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (hKeep : ∀ i,R.endpoint i ∉ omitted)
    {v : V} (hv : v ∉ U) :
    R.prescribedGraph.degree v ≤ 2-R.degreeCredit omitted v := by
  let x : ↥(Uᶜ : Finset V) := ⟨v,mem_compl.mpr hv⟩
  by_cases hx : x ∈ omitted
  · have hAbsent (i : I) : v ∉ R.word i := by
      intro h
      rcases List.mem_cons.mp h with h | h
      · have he : x = R.endpoint (i,false) := Subtype.ext h
        exact hKeep (i,false) (he ▸ hx)
      · rcases List.mem_append.mp h with h | h
        · exact hv (R.outside i v h)
        · have he : x = R.endpoint (i,true) := Subtype.ext (List.mem_singleton.mp h)
          exact hKeep (i,true) (he ▸ hx)
    have hZero : R.prescribedGraph.degree v = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      obtain ⟨u,hu⟩ := (R.prescribedGraph.degree_pos_iff_exists_adj v).mp h
      obtain ⟨_,i,hPair|hPair⟩ := (R.prescribedGraph_adj v u).mp hu
      · exact hAbsent i (hPair.mem (by simp))
      · exact hAbsent i (hPair.mem (by simp))
    rw [hZero]
    exact Nat.zero_le _
  · let K := trimmingGapGraph R.gaps
    let J := R.prescribedGraph ⊔ K
    have hUpper := degree_le_of_edges_in_words R J v (fun u h => by
      rcases h with h | h
      · exact ((R.prescribedGraph_adj v u).mp h).2
      · exact gap_adjacency_in_words R h)
    have hAdd := degree_sup_eq_add_of_disjoint_trimming R.prescribedGraph K
      (prescribed_graph_disjoint_gaps R) v
    change J.degree v = R.prescribedGraph.degree v+K.degree v at hAdd
    have hCredit := R.degree_credit_eq_gaps_at_retained_core omitted x hx
    change R.degreeCredit omitted v = K.degree v at hCredit
    rw [if_neg hv,hAdd] at hUpper
    omega

theorem prescribed_degree_eq_zero_of_absent_body (R : TrimmingReplacementWords G U I)
    {v : V} (hv : v ∈ U) (hAbsent : ∀ i,v ∉ R.body i) : R.prescribedGraph.degree v = 0 := by
  have hCredit : R.degreeCredit ∅ v = 2 := by
    rw [degreeCredit,if_neg]
    rintro (⟨x,_,rfl⟩ | ⟨i,hi⟩)
    · exact (mem_compl.mp x.property) hv
    · exact hAbsent i hi
  have h := R.prescribed_degree_add_credit_on_exceptional ∅ hv
  omega

end OverfullWork.CMSTrimmingRound.TrimmingReplacementWords
