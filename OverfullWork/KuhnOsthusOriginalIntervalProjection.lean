module

public import OverfullWork.KuhnOsthusOriginalInterval
public import OverfullWork.KuhnOsthusProjectedExceptionalArcs
public import OverfullWork.KuhnOsthusChordAbsorptionLink

@[expose] public section


/-! Retain the projected paths used to construct an original
exceptional interval. The projection and the original arcs are
therefore two descriptions of the same interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedRegularPairs DirectedAbsorbingLadder DirectedSpanningConfiguration
open scoped Classical

/-- Pull a path cover back through an embedding whose image contains
the support. Every ordered arc, including a shortcut, is preserved. -/
theorem IntervalPathCover.exists_pull_of_map {W V : Type*} [Nonempty V]
    (e : V ↪ W) {H : Digraph W} {A S T : Finset V}
    (P : IntervalPathCover H (A.map e) (S.map e) (T.map e)) :
    ∃ Q : IntervalPathCover (pullDirectedPair e e H) A S T,
      Q.digraph = pullDirectedPair e e P.digraph := by
  let f : W → V := invFun e
  have hLeft : LeftInverse f e := leftInverse_invFun e.injective
  let tEquiv := T.equivMap e
  let sEquiv := S.equivMap e
  let M (i : T) := P.path (tEquiv i)
  have hBack {i : T} {v : W} (hv : v ∈ (M i).vertices) : e (f v) = v := by
    obtain ⟨x,_,rfl⟩ := mem_map.mp ((P.spans v).mpr ⟨tEquiv i,hv⟩)
    rw [hLeft]
  have hTrace (i : T) : (((M i).vertices.map f).map e) = (M i).vertices := by
    rw [List.map_map]
    exact (List.map_congr_left (g := id) (fun v hv => hBack hv)).trans (List.map_id _)
  let p (i : T) : PathRequest (pullDirectedPair e e H) := {
    source := f (M i).source
    target := f (M i).target
    tail := (M i).tail.map f
    route := ⟨by
      change ((M i).vertices.map f).IsChain (fun x y => H.Adj (e x) (e y))
      apply List.isChain_of_isChain_map e (fun _ _ h => h)
      rw [hTrace]
      exact (M i).route.1,by
      change ((M i).vertices.map f).getLast? = some (f (M i).target)
      have hLast : (M i).vertices.getLast? = some (M i).target := (M i).route.2
      rw [List.getLast?_map,hLast]
      rfl⟩
    simple := (M i).simple.map_on (fun x hx y hy he =>
      (hBack hx).symm.trans ((congrArg e he).trans (hBack hy))) }
  have hP (i : T) : (p i).vertices = (M i).vertices.map f := rfl
  let Q : IntervalPathCover (pullDirectedPair e e H) A S T := {
    path := p
    starts := tEquiv.trans (P.starts.trans sEquiv.symm)
    ends := by
      intro i
      have hS (x : ↑(S.map e)) : f x.val = (sEquiv.symm x).val := by
        have h := congrArg Subtype.val (sEquiv.apply_symm_apply x)
        change e (sEquiv.symm x).val = x.val at h
        rw [← h,hLeft]
      have he := P.ends (tEquiv i)
      change f (M i).source = (sEquiv.symm (P.starts (tEquiv i))).val ∧
        f (M i).target = i.val
      rw [he.1,he.2,hS]
      exact ⟨rfl,hLeft i.val⟩
    disjoint := by
      intro i j hij v
      rw [hP,hP]
      intro h₁ h₂
      obtain ⟨x,hx,hxf⟩ := List.mem_map.mp h₁
      obtain ⟨y,hy,hyf⟩ := List.mem_map.mp h₂
      have hxy : x = y := (hBack hx).symm.trans ((congrArg e (hxf.trans hyf.symm)).trans (hBack hy))
      exact P.disjoint _ _ (tEquiv.injective.ne hij) hx (hxy.symm ▸ hy)
    spans := by
      intro v
      constructor
      · intro hv
        have he : e v ∈ A.map e := mem_map.mpr ⟨v,hv,rfl⟩
        obtain ⟨i,hi⟩ := (P.spans _).mp he
        obtain ⟨i,rfl⟩ := tEquiv.surjective i
        exact ⟨i,(hP i).symm ▸ List.mem_map.mpr ⟨e v,hi,hLeft _⟩⟩
      · rintro ⟨i,hi⟩
        obtain ⟨w,hw,hv⟩ := List.mem_map.mp (hP i ▸ hi)
        have he : e v = w := congrArg e hv.symm |>.trans (hBack hw)
        obtain ⟨u,hu,hu'⟩ := mem_map.mp ((P.spans w).mpr ⟨tEquiv i,hw⟩)
        exact e.injective (hu'.trans he.symm) ▸ hu }
  refine ⟨Q,?_⟩
  ext x y
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp h
    change [x,y] <:+: (p i).vertices at hi
    have he := hi.map e
    rw [hP,hTrace] at he
    exact Digraph.iSup_adj.mpr ⟨tEquiv i,he⟩
  · intro h
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp h
    obtain ⟨i,rfl⟩ := tEquiv.surjective i
    change [e x,e y] <:+: (M i).vertices at hi
    have he := hi.map f
    rw [← hP i] at he
    refine Digraph.iSup_adj.mpr ⟨i,?_⟩
    change [x,y] <:+: (p i).vertices
    simpa only [List.map_cons,List.map_nil,hLeft x,hLeft y] using he

/-- Extract the marked shortcuts of the retained projection in
ordinary coordinates, with exact equality after reinsertion. -/
theorem OriginalInterval.exists_projected_exceptional_arcs {W : Type*} [Fintype W]
    {G : Digraph W} {Z : Finset W} [Nonempty ↥Zᶜ]
    {A S T : Finset ↥Zᶜ} :
    let a : ↥Zᶜ ↪ W := Embedding.subtype _
    let e := (exceptionalCoordinates Z).toEmbedding
    ∀ (P : OriginalInterval G Z (A.map a) (S.map a) (T.map a)),
      ∃ (H : Digraph ↥Zᶜ) (Q : IntervalPathCover H A S T)
        (L : ProjectedExceptionalArcs (pullDirectedPair e e G) Q.digraph (id : ↥Z → ↥Z)),
        L.original = pullDirectedPair e e P.digraph := by
  intro a e P
  obtain ⟨H,Q,endpoint,hInj,hEnd,hKeep,hExact⟩ := P.projection
  obtain ⟨R,hR⟩ := Q.exists_pull_of_map a
  have hQ (x y : ↥Zᶜ) : R.digraph.Adj x y ↔ Q.digraph.Adj x.val y.val := by
    rw [hR]
    rfl
  have hEnd' (p : Bool × ↥Z) : endpoint p ∈ Zᶜ := by
    obtain ⟨x,_,hx⟩ := mem_map.mp (mem_sdiff.mp (hEnd p)).1
    exact hx ▸ x.prop
  let b (l : Bool) (z : ↥Z) : ↥Zᶜ := ⟨endpoint (l,z),hEnd' (l,z)⟩
  let src : ↥Z ↪ ↥Zᶜ := ⟨b false,fun x y h =>
    congrArg Prod.snd (hInj (congrArg Subtype.val h))⟩
  have hOrd (x y : ↥Zᶜ) :
      P.digraph.Adj x.val y.val ↔ R.digraph.Adj x y ∧ x ∉ Set.range src := by
    rw [hExact, hQ]
    have h1 (z : ↥Z) : z.val ≠ x.val := fun he => (mem_compl.mp x.prop) (he ▸ z.prop)
    have h2 (z : ↥Z) : z.val ≠ y.val := fun he => (mem_compl.mp y.prop) (he ▸ z.prop)
    constructor
    · rintro (⟨h,hn⟩ | ⟨z,_,hz⟩ | ⟨z,hz,_⟩)
      · refine ⟨h,?_⟩
        rintro ⟨z,hz⟩
        have hz' : endpoint (false,z) = x.val := congrArg Subtype.val hz
        have hy : endpoint (true,z) = y.val :=
          Q.is_path_system.out_unique (hKeep z) (hz'.symm ▸ h)
        exact hn ⟨z,hz',hy⟩
      · exact (h2 z hz).elim
      · exact (h1 z hz).elim
    · rintro ⟨h,hn⟩
      exact .inl ⟨h,fun ⟨z,hz,_⟩ => hn ⟨z,Subtype.ext hz⟩⟩
  have hOut (x : ↥Zᶜ) (z : ↥Z) : P.digraph.Adj x.val z.val ↔ src z = x := by
    rw [hExact]
    constructor
    · rintro (⟨h,_⟩ | ⟨w,hx,hz⟩ | ⟨w,hw,_⟩)
      · have hT := (mem_sdiff.mp ((Q.slots z.val).2.mp ⟨x.val,h⟩)).1
        obtain ⟨v,_,hv⟩ := mem_map.mp hT
        change v.val = z.val at hv
        exact ((mem_compl.mp v.prop) (hv.symm ▸ z.prop)).elim
      · exact Subtype.ext ((Subtype.ext hz : w = z) ▸ hx)
      · exact ((mem_compl.mp x.prop) (hw ▸ w.prop)).elim
    · intro h
      exact .inr (.inl ⟨z,congrArg Subtype.val h,rfl⟩)
  have hIn (z : ↥Z) (y : ↥Zᶜ) : P.digraph.Adj z.val y.val ↔ b true z = y := by
    rw [hExact]
    constructor
    · rintro (⟨h,_⟩ | ⟨w,_,hw⟩ | ⟨w,hz,hy⟩)
      · have hS := (mem_sdiff.mp ((Q.slots z.val).1.mp ⟨y.val,h⟩)).1
        obtain ⟨v,_,hv⟩ := mem_map.mp hS
        change v.val = z.val at hv
        exact ((mem_compl.mp v.prop) (hv.symm ▸ z.prop)).elim
      · exact ((mem_compl.mp y.prop) (hw ▸ w.prop)).elim
      · exact Subtype.ext ((Subtype.ext hz : w = z) ▸ hy)
    · intro h
      exact .inr (.inr ⟨z,rfl,congrArg Subtype.val h⟩)
  let L : ProjectedExceptionalArcs (pullDirectedPair e e G) R.digraph (id : ↥Z → ↥Z) := {
    source := src
    target := b true
    shortcut := fun z => (hQ _ _).mpr (hKeep z)
    path_arcs := fun z => ⟨P.le ((hOut _ _).mpr rfl),P.le ((hIn _ _).mpr rfl)⟩
    ordinary := fun h hn => P.le ((hOrd _ _).mpr ⟨h,hn⟩) }
  refine ⟨_,R,L,?_⟩
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · exact (hOrd x y).symm
  · refine ⟨?_,?_⟩
    · rintro ⟨z,h,zEq⟩
      exact (hOut x y).mpr (zEq ▸ h)
    · intro h
      exact ⟨y,(hOut x y).mp h,rfl⟩
  · refine ⟨?_,?_⟩
    · rintro ⟨z,zEq,h⟩
      exact (hIn x y).mpr (zEq ▸ h)
    · intro h
      exact ⟨x,rfl,(hIn x y).mp h⟩
  · exact iff_false_intro (fun h => P.no_internal h x.prop y.prop) |>.symm

end OverfullWork.DirectedRobustExpansion
