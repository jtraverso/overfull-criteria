module

public import OverfullWork.KuhnOsthusFactorCycleBreaking

@[expose] public section


/-! Complete the missing exceptional incidences in the first part of
Kühn–Osthus Lemma 8.1. Different styles separate the ordinary vertices. -/
namespace OverfullWork.DirectedRobustExpansion

variable {V : Type*}

structure IsDirectedPathSystem (D : Digraph V) : Prop where
  acyclic : NoDirectedCycle D
  out_unique : ∀ {x y z}, D.Adj x y → D.Adj x z → y = z
  in_unique : ∀ {x y z}, D.Adj y x → D.Adj z x → y = z

def CoversExceptional (D : Digraph V) (Z : Finset V) : Prop :=
  ∀ x ∈ Z, (∃ y, D.Adj x y) ∧ (∃ y, D.Adj y x)

def fillExceptionalSlots (H C : Digraph V) (Z : Finset V) : Digraph V :=
  ⟨fun x y => C.Adj x y ∧
    ((x ∈ Z ∧ ¬ ∃ z, H.Adj x z) ∨ (y ∈ Z ∧ ¬ ∃ z, H.Adj z y))⟩

theorem no_directed_cycle_sup_of_fresh_ends (A B : Digraph V)
    (hA : NoDirectedCycle A)
    (hLeaf : ∀ x y, B.Adj x y →
      (∀ w, ¬ (A ⊔ B).Adj w x) ∨ (∀ w, ¬ (A ⊔ B).Adj y w)) :
    NoDirectedCycle (A ⊔ B) := by
  have clean {x y : V} (h : Relation.TransGen (A ⊔ B).Adj x y)
      (hIn : ∃ w, (A ⊔ B).Adj w x) (hOut : ∃ w, (A ⊔ B).Adj y w) :
      Relation.TransGen A.Adj x y := by
    have edge {u v : V} (huv : (A ⊔ B).Adj u v)
        (hin : ∃ w, (A ⊔ B).Adj w u) (hout : ∃ w, (A ⊔ B).Adj v w) :
        A.Adj u v := by
      rcases (Digraph.sup_adj _ _ _ _).mp huv with ha | hb
      · exact ha
      · obtain ⟨p,hp⟩ := hin
        obtain ⟨q,hq⟩ := hout
        exact (Or.elim (hLeaf u v hb) (fun h => h p hp) (fun h => h q hq)).elim
    induction h with
    | single huv => exact .single (edge huv hIn hOut)
    | @tail u v huv hvt ih =>
      obtain ⟨p,_,hp⟩ := Relation.TransGen.tail'_iff.mp huv
      exact .tail (ih ⟨_,hvt⟩) (edge hvt ⟨p,hp⟩ hOut)
  intro x hx
  obtain ⟨p,_,hp⟩ := Relation.TransGen.tail'_iff.mp hx
  obtain ⟨q,hq,_⟩ := Relation.TransGen.head'_iff.mp hx
  exact hA x (clean hx ⟨p,hp⟩ ⟨q,hq⟩)

theorem complete_exceptional_slots {H C : Digraph V} {Z : Finset V}
    (hH : IsDirectedPathSystem H)
    (hCover : CoversExceptional C Z)
    (hCross : ∀ {x y}, C.Adj x y → (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z))
    (hOut : ∀ {x y z}, C.Adj x y → C.Adj x z → y = z)
    (hIn : ∀ {x y z}, C.Adj y x → C.Adj z x → y = z)
    (hMatching : ∀ {x y z}, x ∉ Z → C.Adj y x → ¬ C.Adj x z)
    (hFresh : ∀ {x y}, C.Adj x y → ∀ v, (v = x ∨ v = y) → v ∉ Z →
      (∀ w, ¬ H.Adj v w) ∧ (∀ w, ¬ H.Adj w v)) :
    let Q := H ⊔ fillExceptionalSlots H C Z
    IsDirectedPathSystem Q ∧ CoversExceptional Q Z := by
  let B := fillExceptionalSlots H C Z
  have hSource {x y : V} (hb : B.Adj x y) : ∀ z, ¬ H.Adj x z := by
    rcases hb.2 with ⟨_,hx⟩ | ⟨hy,_⟩
    · exact fun z hz => hx ⟨z,hz⟩
    · rcases hCross hb.1 with h | h
      · exact (h.2 hy).elim
      · exact (hFresh hb.1 x (Or.inl rfl) h.1).1
  have hTarget {x y : V} (hb : B.Adj x y) : ∀ z, ¬ H.Adj z y := by
    rcases hb.2 with ⟨hx,_⟩ | ⟨_,hy⟩
    · rcases hCross hb.1 with h | h
      · exact (hFresh hb.1 y (Or.inr rfl) h.2).2
      · exact (h.1 hx).elim
    · exact fun z hz => hy ⟨z,hz⟩
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · apply no_directed_cycle_sup_of_fresh_ends H B hH.acyclic
    intro x y hb
    rcases hCross hb.1 with ⟨_,hy⟩ | ⟨hx,_⟩
    · right
      intro w hw
      rcases (Digraph.sup_adj _ _ _ _).mp hw with hw | hw
      · exact (hFresh hb.1 y (Or.inr rfl) hy).1 w hw
      · exact hMatching hy hb.1 hw.1
    · left
      intro w hw
      rcases (Digraph.sup_adj _ _ _ _).mp hw with hw | hw
      · exact (hFresh hb.1 x (Or.inl rfl) hx).2 w hw
      · exact hMatching hx hw.1 hb.1
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with hy | hy <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
    · exact hH.out_unique hy hz
    · exact (hSource hz y hy).elim
    · exact (hSource hy z hz).elim
    · exact hOut hy.1 hz.1
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with hy | hy <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
    · exact hH.in_unique hy hz
    · exact (hTarget hz y hy).elim
    · exact (hTarget hy z hz).elim
    · exact hIn hy.1 hz.1
  · intro x hx
    obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩ := hCover x hx
    constructor
    · by_cases h : ∃ w, H.Adj x w
      · obtain ⟨w,hw⟩ := h
        exact ⟨w,(Digraph.sup_adj _ _ _ _).mpr (Or.inl hw)⟩
      · exact ⟨y,(Digraph.sup_adj _ _ _ _).mpr (Or.inr ⟨hy,Or.inl ⟨hx,h⟩⟩)⟩
    · by_cases h : ∃ w, H.Adj w x
      · obtain ⟨w,hw⟩ := h
        exact ⟨w,(Digraph.sup_adj _ _ _ _).mpr (Or.inl hw)⟩
      · exact ⟨z,(Digraph.sup_adj _ _ _ _).mpr (Or.inr ⟨hz,Or.inr ⟨hx,h⟩⟩)⟩

/-- The arcs of the complete exceptional sequences that were not used by
the corresponding slot completion. -/
def unusedExceptionalArcs {ι : Type*} (H C : ι → Digraph V) (Z : Finset V) : Digraph V :=
  ⟨fun x y => ∃ i, (C i).Adj x y ∧ ¬ (fillExceptionalSlots (H i) (C i) Z).Adj x y⟩

/-- The leftover complete-sequence arcs form the additional exceptional
path system in Kühn–Osthus Lemma 8.1. -/
theorem unused_exceptional_arcs_path_system {ι : Type*} (H C : ι → Digraph V)
    (Z : Finset V)
    (hCover : ∀ i, CoversExceptional (C i) Z)
    (hCross : ∀ i {x y}, (C i).Adj x y → (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z))
    (hOut : ∀ i {x y z}, (C i).Adj x y → (C i).Adj x z → y = z)
    (hIn : ∀ i {x y z}, (C i).Adj y x → (C i).Adj z x → y = z)
    (hNormalOut : ∀ i j {x y z}, x ∉ Z → (C i).Adj x y → (C j).Adj x z → y = z)
    (hNormalIn : ∀ i j {x y z}, x ∉ Z → (C i).Adj y x → (C j).Adj z x → y = z)
    (hNormalMatch : ∀ i j {x y z}, x ∉ Z → (C i).Adj y x → ¬ (C j).Adj x z)
    (hHOut : ∀ x ∈ Z, ∃! i, ∃ y, (H i).Adj x y)
    (hHIn : ∀ x ∈ Z, ∃! i, ∃ y, (H i).Adj y x) :
    IsDirectedPathSystem (unusedExceptionalArcs H C Z) ∧
      CoversExceptional (unusedExceptionalArcs H C Z) Z := by
  classical
  let R := unusedExceptionalArcs H C Z
  have outSlot (i : ι) {x y : V} (hc : (C i).Adj x y) (hx : x ∈ Z) :
      (¬ (fillExceptionalSlots (H i) (C i) Z).Adj x y) ↔ (∃ w, (H i).Adj x w) := by
    have hy := (hCross i hc).resolve_right (fun h => h.1 hx)
    change (¬ ((C i).Adj x y ∧
      ((x ∈ Z ∧ ¬ ∃ w, (H i).Adj x w) ∨ (y ∈ Z ∧ ¬ ∃ w, (H i).Adj w y)))) ↔ _
    simp [hc,hx,hy.2]
  have inSlot (i : ι) {x y : V} (hc : (C i).Adj x y) (hy : y ∈ Z) :
      (¬ (fillExceptionalSlots (H i) (C i) Z).Adj x y) ↔ (∃ w, (H i).Adj w y) := by
    have hx := (hCross i hc).resolve_left (fun h => h.2 hy)
    change (¬ ((C i).Adj x y ∧
      ((x ∈ Z ∧ ¬ ∃ w, (H i).Adj x w) ∨ (y ∈ Z ∧ ¬ ∃ w, (H i).Adj w y)))) ↔ _
    simp [hc,hx.1,hy]
  have hAcyclic : NoDirectedCycle ((⊥ : Digraph V) ⊔ R) := by
    apply no_directed_cycle_sup_of_fresh_ends
    · intro x h
      obtain ⟨y,hxy,_⟩ := Relation.TransGen.head'_iff.mp h
      exact hxy
    · intro x y h
      obtain ⟨i,hi,_⟩ := h
      rcases hCross i hi with h | h
      · right
        intro z hz
        rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
        · exact hz
        · obtain ⟨j,hj,_⟩ := hz
          exact hNormalMatch i j h.2 hi hj
      · left
        intro z hz
        rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
        · exact hz
        · obtain ⟨j,hj,_⟩ := hz
          exact hNormalMatch j i h.1 hj hi
  refine ⟨⟨by simpa only [bot_sup_eq] using hAcyclic,?_,?_⟩,?_⟩
  · intro x y z hy hz
    obtain ⟨i,hi,hni⟩ := hy
    obtain ⟨j,hj,hnj⟩ := hz
    by_cases hx : x ∈ Z
    · obtain ⟨k,_,hk⟩ := hHOut x hx
      have hij := (hk i ((outSlot i hi hx).mp hni)).trans (hk j ((outSlot j hj hx).mp hnj)).symm
      subst j
      exact hOut i hi hj
    · exact hNormalOut i j hx hi hj
  · intro x y z hy hz
    obtain ⟨i,hi,hni⟩ := hy
    obtain ⟨j,hj,hnj⟩ := hz
    by_cases hx : x ∈ Z
    · obtain ⟨k,_,hk⟩ := hHIn x hx
      have hij := (hk i ((inSlot i hi hx).mp hni)).trans (hk j ((inSlot j hj hx).mp hnj)).symm
      subst j
      exact hIn i hi hj
    · exact hNormalIn i j hx hi hj
  · intro x hx
    obtain ⟨i,hi,_⟩ := hHOut x hx
    obtain ⟨j,hj,_⟩ := hHIn x hx
    obtain ⟨y,hy⟩ := (hCover i x hx).1
    obtain ⟨z,hz⟩ := (hCover j x hx).2
    exact ⟨⟨y,i,hy,(outSlot i hy hx).mpr hi⟩,⟨z,j,hz,(inSlot j hz hx).mpr hj⟩⟩

/-- Complete a class of exceptional arcs pointing in only one direction
relative to the exceptional set. Their ordinary endpoints are sources or
sinks in the resulting system, even with the ordinary arcs of the complete
exceptional path system present. -/
theorem complete_one_sided_exceptional_paths {H C : Digraph V} {Z : Finset V}
    (hH : IsDirectedPathSystem H) (hC : IsDirectedPathSystem C)
    (hCover : CoversExceptional C Z)
    (hNoInternal : ∀ {x y}, C.Adj x y → x ∈ Z → y ∉ Z)
    (hSide : (∀ {x y}, H.Adj x y → x ∈ Z ∧ y ∉ Z) ∨
      (∀ {x y}, H.Adj x y → x ∉ Z ∧ y ∈ Z))
    (hFresh : ∀ {v}, v ∉ Z → ((∃ w, H.Adj v w) ∨ (∃ w, H.Adj w v)) →
      (∀ w, ¬ C.Adj v w) ∧ (∀ w, ¬ C.Adj w v)) :
    ∃ Q : Digraph V, IsDirectedPathSystem Q ∧ CoversExceptional Q Z ∧
      ∀ x y, Q.Adj x y ↔ H.Adj x y ∨
        (C.Adj x y ∧ (∀ w, ¬ H.Adj x w) ∧ (∀ w, ¬ H.Adj w y)) := by
  let R : Digraph V := ⟨fun x y => C.Adj x y ∧ (∀ w, ¬ H.Adj x w) ∧ (∀ w, ¬ H.Adj w y)⟩
  have hRC : R ≤ C := fun _ _ h => h.1
  have hRA : NoDirectedCycle R := fun x h => hC.acyclic x (Relation.TransGen.mono (fun _ _ h => hRC h) x x h)
  have hA : NoDirectedCycle (R ⊔ H) := by
    apply no_directed_cycle_sup_of_fresh_ends R H hRA
    intro x y hxy
    rcases hSide with h | h
    · have hy := (h hxy).2
      right
      intro w hw
      rcases (Digraph.sup_adj _ _ _ _).mp hw with hw | hw
      · exact (hFresh hy (Or.inr ⟨x,hxy⟩)).1 w hw.1
      · exact hy (h hw).1
    · have hx := (h hxy).1
      left
      intro w hw
      rcases (Digraph.sup_adj _ _ _ _).mp hw with hw | hw
      · exact (hFresh hx (Or.inl ⟨y,hxy⟩)).2 w hw.1
      · exact hx (h hw).2
  refine ⟨H ⊔ R,⟨by simpa only [sup_comm R H] using hA,?_,?_⟩,?_,fun _ _ => Iff.rfl⟩
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with hy | hy <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
    · exact hH.out_unique hy hz
    · exact (hz.2.1 y hy).elim
    · exact (hy.2.1 z hz).elim
    · exact hC.out_unique hy.1 hz.1
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with hy | hy <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with hz | hz
    · exact hH.in_unique hy hz
    · exact (hz.2.2 y hy).elim
    · exact (hy.2.2 z hz).elim
    · exact hC.in_unique hy.1 hz.1
  · intro x hx
    obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩ := hCover x hx
    constructor
    · by_cases h : ∃ w, H.Adj x w
      · obtain ⟨w,hw⟩ := h
        exact ⟨w,(Digraph.sup_adj _ _ _ _).mpr (Or.inl hw)⟩
      · have hTarget : ∀ w, ¬ H.Adj w y := by
          intro w hw
          exact (hFresh (hNoInternal hy hx) (Or.inr ⟨w,hw⟩)).2 x hy
        exact ⟨y,(Digraph.sup_adj _ _ _ _).mpr (Or.inr ⟨hy,fun w hw => h ⟨w,hw⟩,hTarget⟩)⟩
    · by_cases h : ∃ w, H.Adj w x
      · obtain ⟨w,hw⟩ := h
        exact ⟨w,(Digraph.sup_adj _ _ _ _).mpr (Or.inl hw)⟩
      · have hSource : ∀ w, ¬ H.Adj z w := by
          intro w hw
          have hzN : z ∉ Z := fun hZ => hNoInternal hz hZ hx
          exact (hFresh hzN (Or.inl ⟨w,hw⟩)).1 x hz
        exact ⟨z,(Digraph.sup_adj _ _ _ _).mpr (Or.inr ⟨hz,hSource,fun w hw => h ⟨w,hw⟩⟩)⟩

end OverfullWork.DirectedRobustExpansion
