module

public import OverfullWork.DirectedReserveStitching
public import OverfullWork.RankedDirectedPathCover

@[expose] public section


/-! Connect the dense path cover of GGKLO Lemma 7.3(i) to the
reserve stitching theorem. All paths in the cover remain segments. -/
namespace OverfullWork.DirectedReserveStitching

open Finset DirectedAbsorbingLadder DirectedRobustExpansion RankedDirectedPathCover
open scoped Classical
universe u v w

private theorem request_of_terminal {Y : Type*} [Fintype Y] {V : Type*}
    {H : Digraph Y} {D : Digraph V} (d : Y ↪ V)
    (hLift : ∀ {x y}, H.Adj x y → D.Adj (d x) (d y))
    (C : Cover H.Adj univ) (t : terminals H.Adj (univ : Finset Y)) :
    ∃ P : PathRequest D, P.vertices = (C.path t.val).map d := by
  have hLast := C.ends t.val t.prop
  have hChain := C.chain t.val t.prop
  have hSimple := C.simple t.val t.prop
  cases he : C.path t.val with
  | nil => simp [he] at hLast
  | cons x l =>
    rw [he] at hLast hChain hSimple
    have hCh := List.isChain_map_of_isChain (d : Y → V) (fun _ _ he => hLift he) hChain
    have hEnd : (List.map d (x :: l)).getLast? = some (d t.val) := by
      rw [List.getLast?_map,hLast]
      rfl
    refine ⟨⟨d x,d t.val,l.map d,⟨hCh,hEnd⟩,hSimple.map d.injective⟩,?_⟩
    rfl

/-- Construct the mixed directed cycle from an actual spanning cover
of the dense vertices, with the reserve and the dense vertices embedded
disjointly. Each dense path occurs as a consecutive segment. -/
theorem exists_cycle_of_dense_cover_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} {W : Type v} [Fintype W] {Y : Type w} [Fintype Y] [Nonempty Y]
      (D : Digraph V) (Γ : Digraph W) (e : W ↪ V) (H : Digraph Y) (d : Y ↪ V),
      N ≤ Fintype.card W → IsRealRobust Γ ν τ →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (inDegree Γ v:ℝ)) →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (outDegree Γ v:ℝ)) →
      (∀ {x y}, H.Adj x y → D.Adj (d x) (d y)) →
      Disjoint (Set.range d) (Set.range e) →
      ∀ C : Cover H.Adj univ,
        ((terminals H.Adj (univ : Finset Y)).card:ℝ) ≤ (ν/4)^3*(Fintype.card W:ℝ) →
        (∀ y, 2*(terminals H.Adj (univ : Finset Y)).card ≤
          ((univ : Finset W).filter (fun w => D.Adj (d y) (e w))).card) →
        (∀ y, 2*(terminals H.Adj (univ : Finset Y)).card ≤
          ((univ : Finset W).filter (fun w => D.Adj (e w) (d y))).card) →
        ∃ T : List V, ∃ x : V, T.Nodup ∧ T.head? = some x ∧
          (T ++ [x]).IsChain (mixed D Γ e).Adj ∧
          (∀ v, v ∈ T ↔ v ∈ Set.range e ∨ v ∈ Set.range d) ∧
          ∀ t ∈ terminals H.Adj (univ : Finset Y), List.IsInfix ((C.path t).map d) T := by
  obtain ⟨N,hN⟩ := exists_stitched_cycle_threshold.{u,v} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V W _ Y _ hY D Γ e H d hn hR hIn hOut hLift hApart C hCount hTo hFrom
  let S := terminals H.Adj (univ : Finset Y)
  have hS : 0 < S.card := by
    obtain ⟨t,ht,_⟩ := C.covers (Classical.choice hY) (mem_univ _)
    exact card_pos.mpr ⟨t,ht⟩
  let k := S.card-1
  have hk : S.card = k+1 := (Nat.sub_add_cancel hS).symm
  let idx := (Finset.equivFinOfCardEq hk).symm
  choose Q hQ using request_of_terminal d hLift C
  let P : Fin (k+1) → PathRequest D := fun i => Q (idx i)
  have hVertices : ∀ i, (P i).vertices = (C.path (idx i).val).map d := fun i => hQ (idx i)
  have hDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices := by
    intro i j he x hi hj
    rw [hVertices] at hi hj
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    obtain ⟨b,hb,hab⟩ := List.mem_map.mp hj
    have hEq := d.injective hab
    subst b
    have hij : (idx i).val ≠ (idx j).val := fun h => he (idx.injective (Subtype.ext h))
    exact C.disjoint _ (idx i).prop _ (idx j).prop hij ha hb
  have hPSet : ∀ x, (∃ i, x ∈ (P i).vertices) ↔ x ∈ Set.range d := by
    intro x
    constructor
    · rintro ⟨i,hi⟩
      rw [hVertices] at hi
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hi
      exact ⟨y,rfl⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨t,ht,hy⟩ := C.covers y (mem_univ _)
      obtain ⟨i,hi⟩ := idx.surjective ⟨t,ht⟩
      exact ⟨i,by rw [hVertices,hi]; exact List.mem_map.mpr ⟨y,hy,rfl⟩⟩
  have hOutside : ∀ i x, x ∈ (P i).vertices → x ∉ Set.range e :=
    fun i x hx he => Set.disjoint_left.mp hApart ((hPSet x).mp ⟨i,hx⟩) he
  have hEnd (i : Fin (k+1)) : (P i).target = d (idx i).val := by
    have hLast : (P i).vertices.getLast? = some (P i).target := (P i).route.2
    rw [hVertices,List.getLast?_map,C.ends _ (idx i).prop] at hLast
    exact (Option.some.inj hLast).symm
  have hStart (i : Fin (k+1)) : (P i).source ∈ Set.range d :=
    (hPSet _).mp ⟨i,List.mem_cons_self ..⟩
  have hTo' : ∀ i, 2*(k+1) ≤ ((univ : Finset W).filter
      (fun w => D.Adj (P i).target (e w))).card := by
    intro i
    rw [← hk,hEnd]
    exact hTo (idx i).val
  have hFrom' : ∀ i, 2*(k+1) ≤ ((univ : Finset W).filter
      (fun w => D.Adj (e w) (P i).source)).card := by
    intro i
    obtain ⟨y,hy⟩ := hStart i
    rw [← hk,← hy]
    exact hFrom y
  obtain ⟨T,hND,hHead,hCycle,hSpan,hSeg⟩ := hN D Γ e hn hR hIn hOut k
    (by rw [← hk]; exact hCount) P hDis hOutside hTo' hFrom'
  refine ⟨T,(P 0).source,hND,hHead,hCycle,?_ ,?_⟩
  · intro x
    rw [hSpan,hPSet]
  · intro t ht
    obtain ⟨i,hi⟩ := idx.surjective ⟨t,ht⟩
    simpa only [hVertices,hi] using hSeg i

end OverfullWork.DirectedReserveStitching
