module

public import OverfullWork.CMSOperation41SkeletonPrescriptions
public import OverfullWork.CMSOperation41ChargedWords

@[expose] public section


/-! The branches with zero or one initial auxiliary edge use the same
packing format as S2.1. A one-edge prescription may mark a missing
connector or keep a genuine edge from the singleton's other matching. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TrimmingReplacementWords

/-- S2.3 starts with no auxiliary edge before S2.5 adds its spokes. -/
def empty (G : SimpleGraph V) (U : Finset V) : TrimmingReplacementWords G U (Fin 0) where
  endpoint := ⟨fun p => p.1.elim0,fun p => p.1.elim0⟩
  body := Fin.elim0
  gaps := ∅
  chain := fun i => i.elim0
  gap_witness := fun e he => (notMem_empty e he).elim
  simple := fun i => i.elim0
  outside := fun i => i.elim0
  disjoint := fun i => i.elim0

set_option maxHeartbeats 1600000 in
theorem exists_single_word (G : SimpleGraph V) (U : Finset V)
    (a b : ↥(Uᶜ : Finset V)) (hne : a ≠ b) (L : List V) (gaps : Finset (Sym2 V))
    (hStart : L.head? = some a.val) (hEnd : L.getLast? = some b.val) (hSimple : L.Nodup)
    (hChain : L.IsChain (fun x y => G.Adj x y ∨ s(x,y) ∈ gaps))
    (hWitness : ∀ e ∈ gaps,∃ x y,e = s(x,y) ∧ List.IsInfix [x,y] L)
    (hCore : ∀ v,v ∈ L → v ∉ U → v = a.val ∨ v = b.val) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.endpoint (0,false) = a ∧ R.endpoint (0,true) = b ∧ R.gaps = gaps ∧ R.word 0 = L := by
  let e : (Fin 1 × Bool) ↪ ↥(Uᶜ : Finset V) :=
    ⟨fun p => if p.2 then b else a,by
      rintro ⟨i,j⟩ ⟨k,l⟩ h
      have he : i = k := Subsingleton.elim _ _
      subst k
      cases j <;> cases l <;> simp_all⟩
  have hA (i : Fin 1) : e (i,false) = a := rfl
  have hB (i : Fin 1) : e (i,true) = b := rfl
  obtain ⟨R,hE,hG,hW⟩ := exists_of_full_words G U e (fun _ => L) gaps
    (fun i => by simpa only [hA] using hStart) (fun i => by simpa only [hB] using hEnd)
    (fun _ => hSimple) (fun _ => hChain)
    (fun x hx => by obtain ⟨u,v,hEq,hGap⟩ := hWitness x hx; exact ⟨0,u,v,hEq,hGap⟩)
    (fun i x hx hOut => by simpa only [hA,hB] using hCore x hx hOut)
    (fun i j hij => (hij (Subsingleton.elim _ _)).elim)
  exact ⟨R,hE.symm ▸ hA 0,hE.symm ▸ hB 0,hG,hW 0⟩

end TrimmingReplacementWords

set_option maxHeartbeats 1700000 in
theorem exists_charged_pair_prescription {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.endpoint (0,false) = P.representative a ∧ R.endpoint (0,true) = P.representative b ∧
      R.gaps = {s(a.val,b.val)} ∧ (∀ v ∈ R.body 0,v = a.val ∨ v = b.val) := by
  obtain ⟨L,hNode,hA,hB,hChain,hGap,hException,hCore⟩ :=
    charged_pair_replacement_word_with_core_endpoints P a b hab
  let gaps : Finset (Sym2 V) := {s(a.val,b.val)}
  have hChain' : L.IsChain (fun x y => G.Adj x y ∨ s(x,y) ∈ gaps) := by
    apply hChain.imp
    rintro _ _ (h|⟨rfl,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (mem_singleton_self _)
  obtain ⟨R,hRA,hRB,hRG,hRL⟩ := TrimmingReplacementWords.exists_single_word G U
    (P.representative a) (P.representative b) (fun h => hab (P.injective h)) L gaps hA hB
    hNode hChain' (fun e he => ⟨a.val,b.val,mem_singleton.mp he,hGap⟩) hCore
  refine ⟨R,hRA,hRB,hRG,?_⟩
  intro v hv
  apply hException v _ (R.outside 0 v hv)
  rw [←hRL]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)

set_option maxHeartbeats 1700000 in
theorem exists_singleton_prescription_with_leaf_positions {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b)
    (w : V) (hw : w ∈ U) (hwa : G.Adj w a.val) (hwb : w ≠ b.val)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b.val) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.endpoint (0,false) = P.representative a ∧ R.endpoint (0,true) = P.representative b ∧
      R.gaps = (if omitEdge then {s(w,b.val)} else ∅) ∧
      (∀ v,v ∈ R.body 0 ↔ v ∈ U ∧ (v = w ∨ v = a.val ∨ v = b.val)) ∧
      (R.body 0).length = 1+(if a.val ∈ U then 1 else 0)+(if b.val ∈ U then 1 else 0) ∧
      (omitEdge = false → ∀ omitted,R.degreeCredit omitted w = 0) ∧
      R.prescribedGraph.Adj w a.val ∧
      (omitEdge = false → R.prescribedGraph.Adj w b.val) := by
  obtain ⟨L,hNode,hA,hB,hChain,hGap,hKeep,hException,hCore,hLength,hFirst⟩ :=
    singleton_projected_replacement_word_with_leaf_positions P a b hab w hw hwa hwb
  let gaps : Finset (Sym2 V) := if omitEdge then {s(w,b.val)} else ∅
  have hChain' : L.IsChain (fun x y => G.Adj x y ∨ s(x,y) ∈ gaps) := by
    cases h : omitEdge
    · exact (hKeep (hActual h)).imp (fun _ _ hadj => Or.inl hadj)
    · apply hChain.imp
      rintro _ _ (hAdj|⟨rfl,rfl⟩)
      · exact Or.inl hAdj
      · exact Or.inr (by simp [gaps,h])
  have hWitness (e : Sym2 V) (he : e ∈ gaps) : ∃ x y,e = s(x,y) ∧ List.IsInfix [x,y] L := by
    cases h : omitEdge
    · exact (notMem_empty e (by simpa only [gaps,h,Bool.false_eq_true,if_false] using he)).elim
    · have he' : e = s(w,b.val) := by simpa [gaps,h] using he
      exact ⟨w,b.val,he',hGap⟩
  obtain ⟨R,hRA,hRB,hRG,hRL⟩ := TrimmingReplacementWords.exists_single_word G U
    (P.representative a) (P.representative b) (fun h => hab (P.injective h)) L gaps hA hB
    hNode hChain' hWitness hCore
  have hBody (v : V) (hv : v ∈ U) : v ∈ R.body 0 ↔ v ∈ L := by
    rw [←hRL]
    constructor
    · intro h
      exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact (mem_compl.mp (R.endpoint (0,false)).property (h ▸ hv)).elim
      · rcases List.mem_append.mp h with h | h
        · exact h
        · exact (mem_compl.mp (R.endpoint (0,true)).property ((List.mem_singleton.mp h) ▸ hv)).elim
  refine ⟨R,hRA,hRB,hRG,?_,?_,?_,?_,?_⟩
  · intro v
    exact ⟨fun h => ⟨R.outside 0 v h,((hBody v (R.outside 0 v h)).trans
      (hException v (R.outside 0 v h))).mp h⟩,fun ⟨hv,h⟩ => ((hBody v hv).trans (hException v hv)).mpr h⟩
  · have h := congrArg List.length hRL
    simp only [TrimmingReplacementWords.word,List.length_cons,List.length_append,List.length_nil] at h
    omega
  · intro hKeepEdge omitted
    have hwWord : w ∈ R.word 0 := by rw [hRL]; exact hGap.mem List.mem_cons_self
    have hwBody : w ∈ R.body 0 := (hBody w hw).mpr ((hRL ▸ hwWord))
    rw [TrimmingReplacementWords.degreeCredit,if_pos (Or.inr ⟨0,hwBody⟩),hRG]
    simp [gaps,hKeepEdge,trimming_gap_degree_eq_card_incident_pairs]
  · apply (R.prescribedGraph_adj w a.val).mpr
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    refine ⟨?_,0,Or.inr (hRL.symm ▸ hFirst)⟩
    cases h : omitEdge <;> simp [hRG,gaps,h,hne,hwb]
  · intro h
    apply (R.prescribedGraph_adj w b.val).mpr
    exact ⟨by simp [hRG,gaps,h],0,Or.inl (hRL.symm ▸ hGap)⟩

theorem exists_singleton_prescription {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b)
    (w : V) (hw : w ∈ U) (hwa : G.Adj w a.val) (hwb : w ≠ b.val)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b.val) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.endpoint (0,false) = P.representative a ∧ R.endpoint (0,true) = P.representative b ∧
      R.gaps = (if omitEdge then {s(w,b.val)} else ∅) ∧
      (∀ v ∈ R.body 0,v = w ∨ v = a.val ∨ v = b.val) ∧
      (R.body 0).length = 1+(if a.val ∈ U then 1 else 0)+(if b.val ∈ U then 1 else 0) ∧
      (omitEdge = false → ∀ omitted,R.degreeCredit omitted w = 0) := by
  obtain ⟨R,hA,hB,hGap,hBody,hLength,hCredit,_,_⟩ :=
    exists_singleton_prescription_with_leaf_positions P a b hab w hw hwa hwb omitEdge hActual
  exact ⟨R,hA,hB,hGap,fun v h => ((hBody v).mp h).2,hLength,hCredit⟩

end OverfullWork.CMSTrimmingRound
