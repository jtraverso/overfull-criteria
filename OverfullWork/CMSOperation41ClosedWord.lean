module

public import OverfullWork.CMSOperation41UnbasedCycle

@[expose] public section


/-! Convert the cyclic word produced by the layout realization into
the actual two-colour layer. Designated gaps are omitted even if the
original graph happens to contain an edge joining their endpoints. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The same cyclic coordinates serve the colouring and the degree
accounting. The consecutive pairs include the closing edge. -/
theorem closed_word_cycle_coordinates {n : ℕ} (T : List V) (hLen : T.length = n+3)
    (hT : T.Nodup) (x : V) (hHead : T.head? = some x) :
    ∃ w : Fin (n+3) ↪ V, (∀ v,v ∈ T ↔ v ∈ Set.range w) ∧
      ∀ a b,List.IsInfix [a,b] (T ++ [x]) ↔
        ∃ i,w i = a ∧ w (finRotate (n+3) i) = b := by
  let L := T ++ [x]
  let σ := finRotate (n+3)
  let w : Fin (n+3) ↪ V :=
    ⟨fun i => T.get (Fin.cast hLen.symm i),
      fun _ _ h => Fin.ext (congrArg (fun i : Fin T.length => i.val) (hT.injective_get h))⟩
  have hRange (v : V) : v ∈ T ↔ v ∈ Set.range w := by
    rw [List.mem_iff_get]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨Fin.cast hLen i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨Fin.cast hLen.symm i,hi⟩
  have hI (i : Fin (n+3)) : i.val < T.length := by rw [hLen]; exact i.isLt
  have hSome (i : Fin (n+3)) : T[i.val]? = some (w i) := List.getElem?_eq_getElem (hI i)
  have hLenL : L.length = n+4 := by simp [L,hLen]
  have hAt (i : Fin (n+3)) : L[i.val]? = some (w i) ∧ L[i.val+1]? = some (w (σ i)) := by
    refine ⟨(List.getElem?_append_left (hI i)).trans (hSome i),?_⟩
    by_cases hi : i = Fin.last (n+2)
    · subst i
      have hEq : (Fin.last (n+2)).val+1 = T.length := by simp [hLen]
      have hFirst : some x = some (w 0) := by
        have hh : T[0]? = some x := List.head?_eq_getElem?.symm.trans hHead
        exact hh.symm.trans (hSome 0)
      change (T ++ [x])[(Fin.last (n+2)).val+1]? = some (w (finRotate (n+3) (Fin.last (n+2))))
      rw [finRotate_last,hEq,List.getElem?_append_right le_rfl,Nat.sub_self]
      exact hFirst
    · have hNext : (σ i).val = i.val+1 := coe_finRotate_of_ne_last hi
      change (T ++ [x])[i.val+1]? = some (w (σ i))
      rw [←hNext,List.getElem?_append_left (hI (σ i))]
      exact hSome (σ i)
  have hConsecutive (a b : V) : List.IsInfix [a,b] L ↔ ∃ i,w i = a ∧ w (σ i) = b := by
    rw [List.infix_iff_getElem?]
    constructor
    · rintro ⟨p,hp,hEntries⟩
      have hb : p < n+3 := by simp only [List.length_cons,List.length_nil,hLenL] at hp; omega
      let i : Fin (n+3) := ⟨p,hb⟩
      have hA : L[i.val]? = some a := by simpa [i] using hEntries 0 (by simp)
      have hB : L[i.val+1]? = some b := by simpa [i,Nat.add_comm] using hEntries 1 (by simp)
      exact ⟨i,Option.some.inj ((hAt i).1.symm.trans hA),
        Option.some.inj ((hAt i).2.symm.trans hB)⟩
    · rintro ⟨i,rfl,rfl⟩
      refine ⟨i.val,by simp [hLenL]; omega,?_⟩
      intro p hp
      have hp' : p < 2 := hp
      rcases (show p=0 ∨ p=1 by omega) with rfl | rfl
      · simpa using (hAt i).1
      · simpa [Nat.add_comm] using (hAt i).2
  exact ⟨w,hRange,hConsecutive⟩

theorem physical_layer_of_closed_word (G : SimpleGraph V) {n : ℕ}
    (T : List V) (hLen : T.length = n+3) (hT : T.Nodup) (x : V)
    (hHead : T.head? = some x) (gaps : Finset (Sym2 V))
    (hChain : (T ++ [x]).IsChain (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hParity : Even T.length ∨
      ∃ a b,s(a,b) ∈ gaps ∧ List.IsInfix [a,b] (T ++ [x])) :
    ∃ Q : SimpleGraph V,Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v ∈ T,(∀ u,s(v,u) ∉ gaps) → Q.degree v = 2) ∧
      (∀ v,v ∉ T → Q.degree v = 0) ∧
      ∀ a b,Q.Adj a b ↔ s(a,b) ∉ gaps ∧
        (List.IsInfix [a,b] (T ++ [x]) ∨ List.IsInfix [b,a] (T ++ [x])) := by
  obtain ⟨w,hRange,hConsecutive⟩ := closed_word_cycle_coordinates T hLen hT x hHead
  let σ := finRotate (n+3)
  let A : Finset (Fin (n+3)) := univ.filter (fun i => s(w i,w (σ i)) ∉ gaps)
  have hMarked (i : Fin (n+3)) : i ∈ A ↔ s(w i,w (σ i)) ∉ gaps := by simp [A]
  have hEdges (i : Fin (n+3)) (hi : i ∈ A) : G.Adj (w i) (w (σ i)) := by
    have hi' := (hConsecutive (w i) (w (σ i))).mpr ⟨i,rfl,rfl⟩
    exact ((hChain.infix hi').rel).resolve_right ((hMarked i).mp hi)
  have hPhysical : Even (n+3) ∨ ∃ i,i ∉ A := by
    rcases hParity with h | ⟨a,b,hab,hInfix⟩
    · exact Or.inl (hLen ▸ h)
    · obtain ⟨i,rfl,rfl⟩ := (hConsecutive a b).mp hInfix
      exact Or.inr ⟨i,fun hi => (hMarked i).mp hi hab⟩
  obtain ⟨Q,hQ,hLe,hColour,hDegree,hOff⟩ :=
    physical_layer_of_marked_cycle_any_gap G w A hEdges hPhysical
  refine ⟨Q,hLe,hColour,?_,?_,?_,?_⟩
  · intro v
    by_cases hv : v ∈ Set.range w
    · obtain ⟨i,rfl⟩ := hv
      rw [hDegree]
      split_ifs <;> decide
    · rw [hOff v hv]
      decide
  · intro v hv hNo
    obtain ⟨i,rfl⟩ := (hRange v).mp hv
    have hPrev : (σ.symm i) ∈ A := by
      apply (hMarked _).mpr
      rw [Equiv.apply_symm_apply,Sym2.eq_swap]
      exact hNo _
    rw [hDegree,if_pos ((hMarked i).mpr (hNo _)),if_pos hPrev]
  · intro v hv
    exact hOff v (fun h => hv ((hRange v).mpr h))
  · intro a b
    rw [hQ,map_adj]
    constructor
    · rintro ⟨i,j,hij,rfl,rfl⟩
      change (i ∈ A ∧ σ i = j) ∨ (j ∈ A ∧ σ j = i) at hij
      rcases hij with ⟨hi,rfl⟩ | ⟨hj,rfl⟩
      · exact ⟨(hMarked _).mp hi,Or.inl ((hConsecutive _ _).mpr ⟨i,rfl,rfl⟩)⟩
      · exact ⟨by simpa only [Sym2.eq_swap] using (hMarked _).mp hj,
          Or.inr ((hConsecutive _ _).mpr ⟨j,rfl,rfl⟩)⟩
    · rintro ⟨hNo,hInfix | hInfix⟩
      · obtain ⟨i,rfl,rfl⟩ := (hConsecutive a b).mp hInfix
        exact ⟨i,σ i,Or.inl ⟨(hMarked i).mpr hNo,rfl⟩,rfl,rfl⟩
      · obtain ⟨i,rfl,rfl⟩ := (hConsecutive b a).mp hInfix
        refine ⟨σ i,i,Or.inr ⟨(hMarked i).mpr ?_,rfl⟩,rfl,rfl⟩
        simpa only [Sym2.eq_swap] using hNo

end OverfullWork.CMSTrimmingRound
