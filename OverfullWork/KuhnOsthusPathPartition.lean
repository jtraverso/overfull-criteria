module

public import OverfullWork.KuhnOsthusExceptionalCoverCompletion

@[expose] public section


/-! Assemble the exceptional corrections, the residual exceptional
cover and the ordinary path pieces in Kühn–Osthus Lemma 8.1. -/
namespace OverfullWork.DirectedRobustExpansion

variable {V : Type*}

/-- A vertex lies on at least one arc of the system. -/
def IncidentTo (D : Digraph V) (v : V) : Prop :=
  (∃ w, D.Adj v w) ∨ (∃ w, D.Adj w v)

theorem IsDirectedPathSystem.sup_of_disjoint_vertices {A B : Digraph V}
    (hA : IsDirectedPathSystem A) (hB : IsDirectedPathSystem B)
    (hDis : ∀ v, IncidentTo A v → ¬ IncidentTo B v) :
    IsDirectedPathSystem (A ⊔ B) := by
  have stays {x y : V} (h : Relation.TransGen (A ⊔ B).Adj x y) :
      Relation.TransGen A.Adj x y ∨ Relation.TransGen B.Adj x y := by
    induction h with
    | single h =>
      exact ((Digraph.sup_adj _ _ _ _).mp h).imp Relation.TransGen.single Relation.TransGen.single
    | tail _ huv ih =>
      rcases ih with ha | hb <;> rcases (Digraph.sup_adj _ _ _ _).mp huv with h | h
      · exact Or.inl (ha.tail h)
      · obtain ⟨w,_,hw⟩ := Relation.TransGen.tail'_iff.mp ha
        exact (hDis _ (Or.inr ⟨w,hw⟩) (Or.inl ⟨_,h⟩)).elim
      · obtain ⟨w,_,hw⟩ := Relation.TransGen.tail'_iff.mp hb
        exact (hDis _ (Or.inl ⟨_,h⟩) (Or.inr ⟨w,hw⟩)).elim
      · exact Or.inr (hb.tail h)
  refine ⟨fun v h => (stays h).elim (hA.acyclic v) (hB.acyclic v),?_,?_⟩
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with ha | hb <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with ha' | hb'
    · exact hA.out_unique ha ha'
    · exact (hDis x (Or.inl ⟨y,ha⟩) (Or.inl ⟨z,hb'⟩)).elim
    · exact (hDis x (Or.inl ⟨z,ha'⟩) (Or.inl ⟨y,hb⟩)).elim
    · exact hB.out_unique hb hb'
  · intro x y z hy hz
    rcases (Digraph.sup_adj _ _ _ _).mp hy with ha | hb <;>
      rcases (Digraph.sup_adj _ _ _ _).mp hz with ha' | hb'
    · exact hA.in_unique ha ha'
    · exact (hDis x (Or.inr ⟨y,ha⟩) (Or.inr ⟨z,hb'⟩)).elim
    · exact (hDis x (Or.inr ⟨z,ha'⟩) (Or.inr ⟨y,hb⟩)).elim
    · exact hB.in_unique hb hb'

/-- The exceptional arcs of a complete exceptional path system, in the
original digraph. -/
def exceptionalPart (C : Digraph V) (Z : Finset V) : Digraph V :=
  ⟨fun x y => C.Adj x y ∧ (x ∈ Z ∨ y ∈ Z)⟩

/-- The original complete exceptional systems may be assigned slots
before applying this theorem. Each arc of the input has exactly one
owner in the output, including the residual slot indexed by `none`. -/
theorem exists_path_partition_of_prepared_pieces {ι : Type*}
    (H A C : ι → Digraph V) (Z : Finset V)
    (hH : ∀ i, IsDirectedPathSystem (H i))
    (hA : ∀ i, IsDirectedPathSystem (A i))
    (hC : ∀ i, IsDirectedPathSystem (C i))
    (hCover : ∀ i, CoversExceptional (C i) Z)
    (hSide : ∀ i, (∀ {x y}, (H i).Adj x y → x ∈ Z ∧ y ∉ Z) ∨
      (∀ {x y}, (H i).Adj x y → x ∉ Z ∧ y ∈ Z))
    (hInternal : ∀ i {x y}, (C i).Adj x y → x ∈ Z → y ∉ Z)
    (hFresh : ∀ i v, v ∉ Z → IncidentTo (H i) v → ¬ IncidentTo (C i) v)
    (hOrdinary : ∀ i v, IncidentTo (A i) v →
      ¬ IncidentTo (H i) v ∧ ¬ IncidentTo (C i) v)
    (hNormalOut : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj x y → (exceptionalPart (C j) Z).Adj x z → y = z)
    (hNormalIn : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj y x → (exceptionalPart (C j) Z).Adj z x → y = z)
    (hNormalMatch : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj y x → ¬ (exceptionalPart (C j) Z).Adj x z)
    (hHOut : ∀ x ∈ Z, ∃! i, ∃ y, (H i).Adj x y)
    (hHIn : ∀ x ∈ Z, ∃! i, ∃ y, (H i).Adj y x)
    (hHDis : ∀ i j {x y}, (H i).Adj x y → (H j).Adj x y → i = j)
    (hADis : ∀ i j {x y}, (A i).Adj x y → (A j).Adj x y → i = j)
    (hCDis : ∀ i j {x y}, (C i).Adj x y → (C j).Adj x y → i = j)
    (hHADis : ∀ i j {x y}, (H i).Adj x y → ¬ (A j).Adj x y)
    (hHCDis : ∀ i j {x y}, (H i).Adj x y → ¬ (C j).Adj x y)
    (hACDis : ∀ i j {x y}, (A i).Adj x y → ¬ (C j).Adj x y) :
    ∃ Q : Option ι → Digraph V,
      (∀ i, IsDirectedPathSystem (Q i) ∧ CoversExceptional (Q i) Z) ∧
      (∀ x y, (∃ i, (H i).Adj x y ∨ (A i).Adj x y ∨ (C i).Adj x y) ↔
         ∃! i, (Q i).Adj x y) ∧
      (∀ i, Q (some i) ≤ A i ⊔ H i ⊔ C i) ∧
      (∀ x y, (Q none).Adj x y → (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z)) ∧
      (∀ x y, (Q none).Adj x y ↔ ∃ i, (C i).Adj x y ∧
        ((∃ w, (H i).Adj x w) ∨ (∃ w, (H i).Adj w y))) := by
  classical
  let E i := exceptionalPart (C i) Z
  let U := unusedExceptionalArcs H E Z
  have cross (i : ι) {x y : V} (he : (E i).Adj x y) :
      (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z) := by
    rcases he.2 with hx | hy
    · exact Or.inl ⟨hx,hInternal i he.1 hx⟩
    · exact Or.inr ⟨fun hx => hInternal i he.1 hx hy,hy⟩
  have hU := unused_exceptional_arcs_path_system H E Z
    (fun i x hx => by
      obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩ := hCover i x hx
      exact ⟨⟨y,hy,Or.inl hx⟩,⟨z,hz,Or.inr hx⟩⟩)
    cross (fun i _ _ _ h g => (hC i).out_unique h.1 g.1)
    (fun i _ _ _ h g => (hC i).in_unique h.1 g.1)
    hNormalOut hNormalIn hNormalMatch hHOut hHIn
  have hPrepared (i : ι) := complete_one_sided_exceptional_paths
    (hH i) (hC i) (hCover i) (hInternal i) (hSide i)
    (fun hv hh => ⟨fun w hw => hFresh i _ hv hh (Or.inl ⟨w,hw⟩),
      fun w hw => hFresh i _ hv hh (Or.inr ⟨w,hw⟩)⟩)
  choose P hP hCoverP hAdj using hPrepared
  let Q : Option ι → Digraph V := fun i => i.elim U (fun j => A j ⊔ P j)
  have qAdj (i : ι) (x y : V) :
      (Q (some i)).Adj x y ↔ (A i).Adj x y ∨ (H i).Adj x y ∨
        ((C i).Adj x y ∧ (∀ w, ¬ (H i).Adj x w) ∧ (∀ w, ¬ (H i).Adj w y)) :=
    (Digraph.sup_adj _ _ _ _).trans (or_congr Iff.rfl (hAdj i x y))
  have kept (i : ι) {x y : V} (hc : (C i).Adj x y) :
      ((∀ w, ¬ (H i).Adj x w) ∧ (∀ w, ¬ (H i).Adj w y)) ↔
        ((E i).Adj x y → (fillExceptionalSlots (H i) (E i) Z).Adj x y) := by
    have freshOut (hx : x ∉ Z) (w : V) (hw : (H i).Adj x w) : False :=
      hFresh i x hx (Or.inl ⟨w,hw⟩) (Or.inl ⟨y,hc⟩)
    have freshIn (hy : y ∉ Z) (w : V) (hw : (H i).Adj w y) : False :=
      hFresh i y hy (Or.inr ⟨w,hw⟩) (Or.inr ⟨x,hc⟩)
    constructor
    · rintro ⟨ho,hi⟩ he
      refine ⟨he,?_⟩
      rcases he.2 with hx | hy
      · exact Or.inl ⟨hx,fun ⟨w,hw⟩ => ho w hw⟩
      · exact Or.inr ⟨hy,fun ⟨w,hw⟩ => hi w hw⟩
    · intro h
      by_cases hx : x ∈ Z
      · have hy := hInternal i hc hx
        have hf := (h ⟨hc,Or.inl hx⟩).2.resolve_right (fun hp => hy hp.1)
        exact ⟨fun w hw => hf.2 ⟨w,hw⟩,freshIn hy⟩
      · by_cases hy : y ∈ Z
        · have hf := (h ⟨hc,Or.inr hy⟩).2.resolve_left (fun hp => hx hp.1)
          exact ⟨freshOut hx,fun w hw => hf.2 ⟨w,hw⟩⟩
        · exact ⟨freshOut hx,freshIn hy⟩
  refine ⟨Q,?_,?_,?_,?_,?_⟩
  · rintro (_ | i)
    · exact hU
    · refine ⟨(hA i).sup_of_disjoint_vertices (hP i) ?_,?_⟩
      · intro v ha hp
        have ⟨hnH,hnC⟩ := hOrdinary i v ha
        rcases hp with ⟨w,hw⟩ | ⟨w,hw⟩
        · exact ((hAdj i v w).mp hw).elim
            (fun hh => hnH (Or.inl ⟨w,hh⟩)) (fun hc => hnC (Or.inl ⟨w,hc.1⟩))
        · exact ((hAdj i w v).mp hw).elim
            (fun hh => hnH (Or.inr ⟨w,hh⟩)) (fun hc => hnC (Or.inr ⟨w,hc.1⟩))
      · intro v hv
        obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩ := hCoverP i v hv
        exact ⟨⟨y,(Digraph.sup_adj _ _ _ _).mpr (Or.inr hy)⟩,
          ⟨z,(Digraph.sup_adj _ _ _ _).mpr (Or.inr hz)⟩⟩
  · intro x y
    have hOwners {i j : Option ι} (hi : (Q i).Adj x y) (hj : (Q j).Adj x y) : i = j := by
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j =>
          obtain ⟨l,he,hn⟩ := hi
          rcases (qAdj j x y).mp hj with ha | hh | hc
          · exact (hACDis j l ha he.1).elim
          · exact (hHCDis j l hh he.1).elim
          · have hlj := hCDis l j he.1 hc.1
            subst l
            exact (hn ((kept j hc.1).mp hc.2 he)).elim
      | some i =>
        cases j with
        | none =>
          obtain ⟨l,he,hn⟩ := hj
          rcases (qAdj i x y).mp hi with ha | hh | hc
          · exact (hACDis i l ha he.1).elim
          · exact (hHCDis i l hh he.1).elim
          · have hli := hCDis l i he.1 hc.1
            subst l
            exact (hn ((kept i hc.1).mp hc.2 he)).elim
        | some j =>
          rcases (qAdj i x y).mp hi with ha | hh | hc <;>
            rcases (qAdj j x y).mp hj with ha' | hh' | hc'
          · exact congrArg some (hADis i j ha ha')
          · exact (hHADis j i hh' ha).elim
          · exact (hACDis i j ha hc'.1).elim
          · exact (hHADis i j hh ha').elim
          · exact congrArg some (hHDis i j hh hh')
          · exact (hHCDis i j hh hc'.1).elim
          · exact (hACDis j i ha' hc.1).elim
          · exact (hHCDis j i hh' hc.1).elim
          · exact congrArg some (hCDis i j hc.1 hc'.1)
    constructor
    · rintro ⟨i,hh | ha | hc⟩
      · have hi := (qAdj i x y).mpr (Or.inr (Or.inl hh))
        exact ⟨some i,hi,fun j hj => hOwners hj hi⟩
      · have hi := (qAdj i x y).mpr (Or.inl ha)
        exact ⟨some i,hi,fun j hj => hOwners hj hi⟩
      · by_cases h : (∀ w, ¬ (H i).Adj x w) ∧ (∀ w, ¬ (H i).Adj w y)
        · have hi := (qAdj i x y).mpr (Or.inr (Or.inr ⟨hc,h⟩))
          exact ⟨some i,hi,fun j hj => hOwners hj hi⟩
        · obtain ⟨he,hn⟩ := Classical.not_imp.mp (fun hk => h ((kept i hc).mpr hk))
          have hi : (Q none).Adj x y := ⟨i,he,hn⟩
          exact ⟨none,hi,fun j hj => hOwners hj hi⟩
    · rintro ⟨i,hi,_⟩
      cases i with
      | none =>
        obtain ⟨j,he,_⟩ := hi
        exact ⟨j,Or.inr (Or.inr he.1)⟩
      | some j =>
        rcases (qAdj j x y).mp hi with ha | hh | hc
        · exact ⟨j,Or.inr (Or.inl ha)⟩
        · exact ⟨j,Or.inl hh⟩
        · exact ⟨j,Or.inr (Or.inr hc.1)⟩

  · intro i x y h
    rcases (qAdj i x y).mp h with ha | hh | hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hc.1
  · rintro x y ⟨i,he,_⟩
    exact cross i he

  · intro x y
    constructor
    · rintro ⟨i,he,hn⟩
      refine ⟨i,he.1,?_⟩
      by_contra h
      apply hn
      exact (kept i he.1).mp
        ⟨fun w hw => h (Or.inl ⟨w,hw⟩),fun w hw => h (Or.inr ⟨w,hw⟩)⟩ he
    · rintro ⟨i,hc,h⟩
      have hk : ¬ ((∀ w, ¬ (H i).Adj x w) ∧ (∀ w, ¬ (H i).Adj w y)) := by
        rintro ⟨ho,hi⟩
        rcases h with ⟨w,hw⟩ | ⟨w,hw⟩
        · exact ho w hw
        · exact hi w hw
      obtain ⟨he,hn⟩ := Classical.not_imp.mp (fun h => hk ((kept i hc).mpr h))
      exact ⟨i,he,hn⟩

end OverfullWork.DirectedRobustExpansion
