module

public import OverfullWork.CMSOperation41ClosedWordBalance
public import OverfullWork.CMSOperation41ExpandedEdges

@[expose] public section


/-! Physical projection of a realised layout. The layer consists
exactly of the prescribed consecutive pairs except at marked gaps,
and has two actual edge colours. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph DirectedSpanningConfiguration
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem physical_layer_of_cyclic_layout_words (G : SimpleGraph V) {n : ℕ}
    (w : Fin (n+1) ↪ V) (body : Fin (n+1) → List V) (gaps : Finset (Sym2 V))
    (hPaths : ∀ i,(w i :: body i ++ [w (finRotate (n+1) i)]).IsChain
      (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hSimple : ∀ i,(w i :: body i).Nodup)
    (hOutside : ∀ i v,v ∈ body i → v ∉ Set.range w)
    (hDisjoint : ∀ i j,i ≠ j → List.Disjoint (body i) (body j))
    (hLarge : 3 ≤ n+1+∑ i,(body i).length)
    (hParity : Even (n+1+∑ i,(body i).length) ∨
      ∃ i a b,s(a,b) ∈ gaps ∧ List.IsInfix [a,b] (w i :: body i ++ [w (finRotate (n+1) i)])) :
    ∃ Q : SimpleGraph V,Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v ∈ openCycleWord w body,(∀ u,s(v,u) ∉ gaps) → Q.degree v = 2) ∧
      (∀ v,v ∉ openCycleWord w body → Q.degree v = 0) ∧
      (∀ a b,Q.Adj a b ↔ s(a,b) ∉ gaps ∧
        ∃ i,List.IsInfix [a,b] (w i :: body i ++ [w (finRotate (n+1) i)]) ∨
          List.IsInfix [b,a] (w i :: body i ++ [w (finRotate (n+1) i)])) ∧
      ((∀ edge ∈ gaps,∃ i a b,edge = s(a,b) ∧
        List.IsInfix [a,b] (w i :: body i ++ [w (finRotate (n+1) i)])) →
      ∀ v,Q.degree v+(trimmingGapGraph gaps).degree v =
        if v ∈ openCycleWord w body then 2 else 0) := by
  let T := openCycleWord w body
  have hL : T.length = n+1+∑ i,(body i).length := openCycleWord_length w body
  have hLen : T.length = (T.length-3)+3 := by omega
  obtain ⟨hNode,hHead,hCycle,_⟩ := open_cycle_word_of_disjoint_interiors
    (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps) w body hPaths hSimple hOutside hDisjoint
  have hMarks : Even T.length ∨ ∃ a b,s(a,b) ∈ gaps ∧ List.IsInfix [a,b] (T ++ [w 0]) := by
    rcases hParity with hEven | ⟨i,a,b,hGap,hInfix⟩
    · exact Or.inl (hL.symm ▸ hEven)
    · exact Or.inr ⟨a,b,hGap,hInfix.trans (replacement_word_infix_expanded_cycle w body i)⟩
  obtain ⟨Q,hLe,hColour,hDegree,hTwo,hZero,hQ⟩ :=
    physical_layer_of_closed_word G T hLen hNode (w 0) hHead gaps hCycle hMarks
  have hArc (a b : V) : List.IsInfix [a,b] (T ++ [w 0]) ↔
      ∃ i,List.IsInfix [a,b] (w i :: body i ++ [w (finRotate (n+1) i)]) := by
    change (wordGraph (expandedCycleWord w body)).Adj a b ↔ _
    rw [expanded_cycle_wordGraph,Digraph.iSup_adj]
    rfl
  refine ⟨Q,hLe,hColour,hDegree,hTwo,hZero,?_,?_⟩
  · intro a b
    rw [hQ]
    constructor
    · rintro ⟨hn,hab | hba⟩
      · obtain ⟨i,hi⟩ := (hArc a b).mp hab
        exact ⟨hn,i,Or.inl hi⟩
      · obtain ⟨i,hi⟩ := (hArc b a).mp hba
        exact ⟨hn,i,Or.inr hi⟩
    · rintro ⟨hn,i,hab | hba⟩
      · exact ⟨hn,Or.inl ((hArc a b).mpr ⟨i,hab⟩)⟩
      · exact ⟨hn,Or.inr ((hArc b a).mpr ⟨i,hba⟩)⟩
  · intro hGap
    apply closed_word_degree_with_gaps T (w 0) hLen hNode hHead gaps Q ?_ hQ
    intro edge he
    obtain ⟨i,a,b,hPair,hWord⟩ := hGap edge he
    exact ⟨a,b,hPair,(hArc a b).mpr ⟨i,hWord⟩⟩

section RealizedLayout

variable {C : Type*}

/-- Realized flexible paths stay in the original core and each fixed
arc receives its original replacement. -/
def realizedReplacementInterior {n : ℕ}
    (e : C ↪ V) (fixed : Finset (Fin (n+1))) (old : Fin (n+1) → List C)
    (external : Fin (n+1) → List V) (i : Fin (n+1)) : List V :=
  if i ∈ fixed then external i else (old i).map e

theorem realized_replacement_length [Fintype C] {n : ℕ}
    (e : C ↪ V) (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ C)
    (fixed : Finset (Fin (n+1))) (isolated : Finset C) {D : Digraph C}
    (P : Realization D (cyclicLayout hn w fixed isolated)) (hIso : ∀ i,w i ∉ isolated)
    (external : Fin (n+1) → List V) :
    let body := realizedReplacementInterior e fixed P.interior external
    n+1+(∑ i,(body i).length) = Fintype.card C-isolated.card+(∑ i ∈ fixed,(external i).length) := by
  intro body
  have hPoint (i : Fin (n+1)) : (body i).length = (P.interior i).length+
      if i ∈ fixed then (external i).length else 0 := by
    by_cases hi : i ∈ fixed
    · rw [P.fixed_empty i hi]
      simp [body,realizedReplacementInterior,hi]
    · simp [body,realizedReplacementInterior,hi]
  have hSum := sum_congr (s₁ := univ) (s₂ := univ) rfl (fun i _ => hPoint i)
  rw [sum_add_distrib,←sum_filter] at hSum
  simp only [filter_mem_eq_inter,univ_inter] at hSum
  have hLength := P.cyclic_core_word_length hn w fixed isolated hIso
  omega

set_option maxHeartbeats 2200000 in
theorem physical_layer_of_realized_replacements (G : SimpleGraph V) {n : ℕ}
    (e : C ↪ V) (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ C)
    (fixed : Finset (Fin (n+1))) (isolated : Finset C) {D : Digraph C}
    (P : Realization D (cyclicLayout hn w fixed isolated))
    (hIso : ∀ i,w i ∉ isolated)
    (hHost : ∀ u v,D.Adj u v → G.Adj (e u) (e v))
    (external : Fin (n+1) → List V) (gaps : Finset (Sym2 V))
    (hFixedPath : ∀ i ∈ fixed,(e (w i) :: external i ++ [e (w (finRotate (n+1) i))]).IsChain
      (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hFixedSimple : ∀ i ∈ fixed,(e (w i) :: external i).Nodup)
    (hFixedOutside : ∀ i ∈ fixed,∀ v,v ∈ external i → v ∉ Set.range e)
    (hFixedDisjoint : ∀ i ∈ fixed,∀ j ∈ fixed,i ≠ j → List.Disjoint (external i) (external j)) :
    let body := realizedReplacementInterior e fixed P.interior external
    3 ≤ n+1+∑ i,(body i).length →
    (Even (n+1+∑ i,(body i).length) ∨
      ∃ i ∈ fixed,∃ a b,s(a,b) ∈ gaps ∧
        List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) →
    ∃ Q : SimpleGraph V,Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v,v ∉ isolated → (∀ u,s(e v,u) ∉ gaps) → Q.degree (e v) = 2) ∧
      (∀ v ∈ isolated,Q.degree (e v) = 0) ∧
      (∀ a b,Q.Adj a b ↔ s(a,b) ∉ gaps ∧
        ∃ i,List.IsInfix [a,b] (e (w i) :: body i ++ [e (w (finRotate (n+1) i))]) ∨
          List.IsInfix [b,a] (e (w i) :: body i ++ [e (w (finRotate (n+1) i))])) ∧
      ((∀ edge ∈ gaps,∃ i ∈ fixed,∃ a b,edge = s(a,b) ∧
        List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) →
      ∀ v,Q.degree v+(trimmingGapGraph gaps).degree v =
        if (∃ u ∉ isolated,e u = v) ∨ (∃ i ∈ fixed,v ∈ external i) then 2 else 0) := by
  intro body hLarge hParity
  let w' := w.trans e
  have hAt (i : Fin (n+1)) : w' i = e (w i) := rfl
  have hFixed (i : Fin (n+1)) (hi : i ∈ fixed) : body i = external i := if_pos hi
  have hFlex (i : Fin (n+1)) (hi : i ∉ fixed) : body i = (P.interior i).map e := if_neg hi
  have hPath (i : Fin (n+1)) :
      (w' i :: body i ++ [w' (finRotate (n+1) i)]).IsChain
        (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps) := by
    by_cases hi : i ∈ fixed
    · rw [hAt,hAt,hFixed i hi]
      exact hFixedPath i hi
    · rw [hAt,hAt,hFlex i hi]
      have h := List.isChain_map_of_isChain (S := fun a b => G.Adj a b ∨ s(a,b) ∈ gaps) e
        (fun u v h => Or.inl (hHost u v h))
        (P.flexible_chain i hi)
      simpa only [cyclicLayout,List.map_cons,List.map_append,List.map_nil,Function.Embedding.coeFn_mk]
        using h
  have hSimple (i : Fin (n+1)) : (w' i :: body i).Nodup := by
    by_cases hi : i ∈ fixed
    · rw [hAt,hFixed i hi]
      exact hFixedSimple i hi
    · rw [hAt,hFlex i hi]
      have h := (P.simple i).sublist (List.sublist_append_left _ _)
      exact List.Nodup.map e.injective h
  have hOutside (i : Fin (n+1)) (v : V) (hv : v ∈ body i) : v ∉ Set.range w' := by
    rintro ⟨j,rfl⟩
    by_cases hi : i ∈ fixed
    · rw [hFixed i hi] at hv
      exact hFixedOutside i hi _ hv ⟨w j,rfl⟩
    · rw [hFlex i hi] at hv
      obtain ⟨u,hu,he⟩ := List.mem_map.mp hv
      have hh := e.injective he
      exact P.outside i _ hu (mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,hh.symm⟩))
  have hDisjoint (i j : Fin (n+1)) (hij : i ≠ j) : List.Disjoint (body i) (body j) := by
    intro v hv hv'
    by_cases hi : i ∈ fixed <;> by_cases hj : j ∈ fixed
    · rw [hFixed i hi] at hv
      rw [hFixed j hj] at hv'
      exact hFixedDisjoint i hi j hj hij hv hv'
    · rw [hFixed i hi] at hv
      rw [hFlex j hj] at hv'
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv'
      exact hFixedOutside i hi _ hv ⟨u,rfl⟩
    · rw [hFlex i hi] at hv
      rw [hFixed j hj] at hv'
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
      exact hFixedOutside j hj _ hv' ⟨u,rfl⟩
    · rw [hFlex i hi] at hv
      rw [hFlex j hj] at hv'
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      obtain ⟨v,hv,he⟩ := List.mem_map.mp hv'
      exact P.unique i j hij hu ((e.injective he) ▸ hv)
  have hParity' : Even (n+1+∑ i,(body i).length) ∨
      ∃ i a b,s(a,b) ∈ gaps ∧ List.IsInfix [a,b] (w' i :: body i ++ [w' (finRotate (n+1) i)]) := by
    rcases hParity with hEven | ⟨i,hi,a,b,hab,hInfix⟩
    · exact Or.inl hEven
    · exact Or.inr ⟨i,a,b,hab,by rwa [hAt,hAt,hFixed i hi]⟩
  obtain ⟨Q,hLe,hColour,hDegree,hTwo,hZero,hEdges,hBalance⟩ :=
    physical_layer_of_cyclic_layout_words G w' body gaps hPath hSimple hOutside hDisjoint hLarge hParity'
  obtain ⟨_,_,_,hMem⟩ := open_cycle_word_of_disjoint_interiors
    (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps) w' body hPath hSimple hOutside hDisjoint
  have hOccur (v : C) : e v ∈ openCycleWord w' body ↔ v ∉ isolated := by
    rw [hMem]
    constructor
    · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
      · have he : w i = v := e.injective hi
        exact he ▸ hIso i
      · by_cases hf : i ∈ fixed
        · rw [hFixed i hf] at hi
          exact (hFixedOutside i hf _ hi ⟨v,rfl⟩).elim
        · rw [hFlex i hf] at hi
          obtain ⟨u,hu,he⟩ := List.mem_map.mp hi
          have hv := e.injective he
          exact hv ▸ (fun h => P.outside i _ hu (mem_union_right _ h))
    · intro hv
      by_cases h : v ∈ Set.range w
      · obtain ⟨i,rfl⟩ := h
        exact Or.inl ⟨i,rfl⟩
      · have hBoundary : v ∉ (cyclicLayout hn w fixed isolated).boundary := by
          simp only [cyclicLayout,mem_union,mem_image,mem_univ,true_and,not_or]
          exact ⟨h,hv⟩
        obtain ⟨i,hi⟩ := P.spans v hBoundary
        have hf : i ∉ fixed := by
          intro he
          rw [P.fixed_empty i he] at hi
          exact List.not_mem_nil hi
        exact Or.inr ⟨i,by rw [hFlex i hf]; exact List.mem_map.mpr ⟨v,hi,rfl⟩⟩
  have hAll (v : V) : v ∈ openCycleWord w' body ↔
      (∃ u ∉ isolated,e u = v) ∨ (∃ i ∈ fixed,v ∈ external i) := by
    constructor
    · intro hv
      rcases (hMem v).mp hv with ⟨i,rfl⟩ | ⟨i,hi⟩
      · exact Or.inl ⟨w i,hIso i,rfl⟩
      · by_cases hf : i ∈ fixed
        · exact Or.inr ⟨i,hf,(hFixed i hf) ▸ hi⟩
        · rw [hFlex i hf] at hi
          obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
          exact Or.inl ⟨u,(hOccur u).mp hv,rfl⟩
    · rintro (⟨u,hu,rfl⟩|⟨i,hi,hv⟩)
      · exact (hOccur u).mpr hu
      · exact (hMem _).mpr (Or.inr ⟨i,(hFixed i hi).symm ▸ hv⟩)
  refine ⟨Q,hLe,hColour,hDegree,fun v hv => hTwo _ ((hOccur v).mpr hv),
    fun v hv => hZero _ (fun h => (hOccur v).mp h hv),hEdges,?_⟩
  intro hGap v
  have hGap' : ∀ edge ∈ gaps,∃ i a b,edge = s(a,b) ∧
      List.IsInfix [a,b] (w' i :: body i ++ [w' (finRotate (n+1) i)]) := by
    intro edge he
    obtain ⟨i,hi,a,b,hPair,hWord⟩ := hGap edge he
    exact ⟨i,a,b,hPair,by rwa [hAt,hAt,hFixed i hi]⟩
  simpa only [hAll] using hBalance hGap' v

end RealizedLayout

end OverfullWork.CMSTrimmingRound
