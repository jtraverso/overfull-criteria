module

public import OverfullWork.RobustFreeMatching
public import OverfullWork.CanonicalAnchorBundles

@[expose] public section


/-! # Construct the prescribed crossing matching covering both anchors

A positive available first-row mass and two second-row neighbors suffice
to choose one or two actual free copies. The result includes capacities,
color compatibility and the two saturated anchor equations.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 32000000

structure AnchorPrescription (P : M.PartialColouring k) (i : Fin k) (A : Finset V) (a b : V) where
  graph : MultiGraph V
  capacity : ∀ e, graph.mult e ≤ P.available.mult e
  compatible : ∀ v, (P.colouring.colourGraph i).degree v+graph.degree v ≤ 1
  first : (P.colouring.colourGraph i).degree a+graph.degree a=1
  second : (P.colouring.colourGraph i).degree b+graph.degree b=1
  crossing : ∀ u v, (u ∈ A ↔ v ∈ A) → graph.mult s(u,v)=0
  small : graph.edgeCount ≤ 2

theorem unit_edge_crossing_zero (A : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∉ A)
    (hne : u ≠ v) (x y : V) (hSame : x ∈ A ↔ y ∈ A) :
    (unitEdge u v hne).mult s(x,y)=0 := by
  apply if_neg
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩|⟨hx,hy⟩
  · subst x;subst y;exact hv (hSame.mp hu)
  · subst y;subst x;exact hv (hSame.mpr hu)

theorem exists_anchor_prescription (P : M.PartialColouring k) (i : Fin k) (A : Finset V)
    (a b : V) (ha : a ∈ A) (hb : b ∉ A) (hMissing : (P.colouring.colourGraph i).degree a=0)
    (hFirst : 0 < P.available.degreeInto (P.colouring.missingSet Aᶜ i) a)
    (hSecond : (P.colouring.colourGraph i).degree b=0 →
      1 < (P.available.neighboursInto (P.colouring.missingSet A i) b).card) :
    Nonempty (AnchorPrescription P i A a b) := by
  obtain ⟨x,hx,hax⟩ := sum_pos_iff.mp hFirst
  have hxSide : x ∉ A := mem_compl.mp (mem_filter.mp hx).1
  have hxZero : (P.colouring.colourGraph i).degree x=0 := (mem_filter.mp hx).2
  have haxNe : a ≠ x := by intro he;exact hxSide (he ▸ ha)
  have hOneCapacity : ∀ e, (unitEdge a x haxNe).mult e ≤ P.available.mult e := by
    intro e
    change (if e=s(a,x) then 1 else 0) ≤ _
    split_ifs with he
    · subst e;omega
    · exact Nat.zero_le _
  have hOneCompatible : ∀ v, (P.colouring.colourGraph i).degree v+(unitEdge a x haxNe).degree v ≤ 1 := by
    intro v
    rw [degree_unitEdge]
    split_ifs with hv
    · rcases hv with rfl|rfl <;> omega
    · exact P.colouring.colourGraph_degree_le_one i v
  have hOneFirst : (P.colouring.colourGraph i).degree a+(unitEdge a x haxNe).degree a=1 := by
    simp [degree_unitEdge,hMissing]
  by_cases hNeed : (P.colouring.colourGraph i).degree b=0 ∧ x ≠ b
  · have hMany := hSecond hNeed.1
    have hCandidates : ((P.available.neighboursInto (P.colouring.missingSet A i) b).erase a).Nonempty := by
      apply card_pos.mp
      by_cases han : a ∈ P.available.neighboursInto (P.colouring.missingSet A i) b
      · have hh := card_erase_add_one han;omega
      · rw [erase_eq_of_notMem han];omega
    obtain ⟨y,hy⟩ := hCandidates
    obtain ⟨hya,hyN⟩ := mem_erase.mp hy
    obtain ⟨hyMissing,hby⟩ := mem_filter.mp hyN
    have hySide : y ∈ A := (mem_filter.mp hyMissing).1
    have hyZero : (P.colouring.colourGraph i).degree y=0 := (mem_filter.mp hyMissing).2
    have hyb : y ≠ b := by intro he;exact hb (he ▸ hySide)
    have hxy : x ≠ y := by intro he;exact hxSide (he ▸ hySide)
    have hab : a ≠ b := by intro he;exact hb (he ▸ ha)
    have hEdgeNe : s(a,x) ≠ s(y,b) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨hay,hxb⟩|⟨hab',hxy'⟩
      · exact hya hay.symm
      · exact hab hab'
    let J := (unitEdge a x haxNe).addCopies (unitEdge y b hyb)
    refine ⟨{
      graph := J, capacity := ?_, compatible := ?_, first := ?_, second := ?_,
      crossing := ?_, small := by simp [J,edgeCount_addCopies,edgeCount_unitEdge]
    }⟩
    · intro e
      change (if e=s(a,x) then 1 else 0)+(if e=s(y,b) then 1 else 0) ≤ P.available.mult e
      have hby' : 0 < P.available.mult s(y,b) := by rwa [Sym2.eq_swap]
      split_ifs with he₁ he₂
      · exact False.elim (hEdgeNe (he₁.symm.trans he₂))
      · subst e;omega
      · subst e;omega
      · exact Nat.zero_le _
    · intro v
      dsimp only [J]
      rw [degree_addCopies,degree_unitEdge,degree_unitEdge]
      by_cases hva : v=a
      · subst v;simp [hMissing,Ne.symm hya,hab]
      by_cases hvx : v=x
      · subst v;simp [hxZero,hxy,hNeed.2]
      by_cases hvy : v=y
      · subst v;simp [hyZero,hya,Ne.symm hxy]
      by_cases hvb : v=b
      · subst v;simp [hNeed.1,Ne.symm hab,Ne.symm hNeed.2]
      · simpa [hva,hvx,hvy,hvb] using P.colouring.colourGraph_degree_le_one i v
    · simp [J,degree_addCopies,degree_unitEdge,hMissing,Ne.symm hya,hab]
    · simp [J,degree_addCopies,degree_unitEdge,hNeed.1,Ne.symm hab,Ne.symm hNeed.2]
    · intro u v hSame
      change (unitEdge a x haxNe).mult s(u,v)+(unitEdge y b hyb).mult s(u,v)=0
      rw [unit_edge_crossing_zero A a x ha hxSide haxNe u v hSame,
        unit_edge_crossing_zero A y b hySide hb hyb u v hSame]
  · refine ⟨{
      graph := unitEdge a x haxNe, capacity := hOneCapacity, compatible := hOneCompatible,
      first := hOneFirst, second := ?_,
      crossing := unit_edge_crossing_zero A a x ha hxSide haxNe,
      small := by rw [edgeCount_unitEdge];omega
    }⟩
    by_cases hxb : x=b
    · subst b;simp [degree_unitEdge,hxZero]
    · have hPos : (P.colouring.colourGraph i).degree b ≠ 0 := by tauto
      have hOne := P.colouring.colourGraph_degree_le_one i b
      have hba : b ≠ a := by intro he;exact hb (he ▸ ha)
      simp only [degree_unitEdge,if_neg (show ¬(b=a ∨ b=x) by tauto)]
      omega

end SimpleGraph.MultiGraph.PartialColouring
