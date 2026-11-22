module

public import OverfullWork.KuhnOsthusChordRoundPaths
public import OverfullWork.KuhnOsthusExceptionalContraction
public import OverfullWork.ThinReserveAssembly

@[expose] public section


/-! Read the prepared systems of a chord round in the original
vertex set. The only contracted arcs are those inside its assigned
complete exceptional path system. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V W : Type*} [Fintype V]

omit [Fintype V] in
private theorem lift_path_system (e : W ↪ V) {D : Digraph W} (hD : IsDirectedPathSystem D) :
    IsDirectedPathSystem (liftDirectedPair e e D) := by
  let L := liftDirectedPair e e D
  have hPath {x y : V} (h : Relation.TransGen L.Adj x y) :
      ∃ a b, e a = x ∧ e b = y ∧ Relation.TransGen D.Adj a b := by
    induction h with
    | single he =>
      obtain ⟨a,b,ha,hb,hab⟩ := he
      exact ⟨a,b,ha,hb,.single hab⟩
    | tail _ hb ih =>
      obtain ⟨a,b,ha,hb',hp⟩ := ih
      obtain ⟨c,d,hc,hd,hcd⟩ := hb
      have ht : b = c := e.injective (hb'.trans hc.symm)
      exact ⟨a,d,ha,hd,hp.tail (ht.symm ▸ hcd)⟩
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨a,b,ha,hb,hab⟩ := hPath hv
    exact hD.acyclic a ((e.injective (hb.trans ha.symm)) ▸ hab)
  · rintro x y z ⟨a,b,hax,hby,hab⟩ ⟨a',c,ha'x,hcz,ha'c⟩
    have ha : a' = a := e.injective (ha'x.trans hax.symm)
    have he : b = c := hD.out_unique hab (ha ▸ ha'c)
    exact hby.symm.trans ((congrArg e he).trans hcz)
  · rintro x y z ⟨a,b,hax,hbz,hab⟩ ⟨a',b',ha'y,hb'z,ha'b'⟩
    have hb : b' = b := e.injective (hb'z.trans hbz.symm)
    have he : a = a' := hD.in_unique hab (hb ▸ ha'b')
    exact hax.symm.trans ((congrArg e he).trans ha'y)

/-- Adding an ordinary path system commutes with contraction. Its
arcs are actual physical arcs, and all its vertices avoid the
exceptional set. -/
theorem chord_basic_union_of_ordinary (Z : Finset V) (D : Digraph ↥Zᶜ) (E : Digraph V) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let L := liftDirectedPair e e D
    basicExceptionalPathSystem (L ⊔ E) Z = D ⊔ basicExceptionalPathSystem E Z := by
  intro e L
  have hOrd (x y : V) (h : L.Adj x y) : x ∉ Z ∧ y ∉ Z := by
    obtain ⟨a,b,rfl,rfl,_⟩ := h
    exact ⟨mem_compl.mp a.prop,mem_compl.mp b.prop⟩
  ext x y
  constructor
  · rintro ((h | h) | ⟨z,hz,hxz,hzy⟩)
    · exact Or.inl ((liftDirectedPair_adj e e D x y).mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z,hz,hxz.resolve_left (fun h => (hOrd _ _ h).2 hz),
        hzy.resolve_left (fun h => (hOrd _ _ h).1 hz)⟩)
  · rintro (h | h | ⟨z,hz,hxz,hzy⟩)
    · exact Or.inl (Or.inl ((liftDirectedPair_adj e e D x y).mpr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨z,hz,Or.inr hxz,Or.inr hzy⟩

/-- The physical system obtained by adding ordinary paths to a
complete exceptional system. The same footprint separation used
for the basic case ensures the physical path property. -/
theorem chord_original_system_of_ordinary (Z : Finset V) (D : Digraph ↥Zᶜ) (E : Digraph V)
    (hD : IsDirectedPathSystem D) (hE : IsDirectedPathSystem E)
    (hCover : CoversExceptional E Z) (hNo : ∀ x y, E.Adj x y → x ∈ Z → y ∉ Z)
    (hApart : ∀ v, IncidentTo D v → ¬ IncidentTo (basicExceptionalPathSystem E Z) v) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let P := liftDirectedPair e e D ⊔ E
    IsDirectedPathSystem P ∧ CoversExceptional P Z ∧
      (∀ x y, P.Adj x y → x ∈ Z → y ∉ Z) ∧
      basicExceptionalPathSystem P Z = D ⊔ basicExceptionalPathSystem E Z := by
  intro e P
  have hL : IsDirectedPathSystem (liftDirectedPair e e D) := lift_path_system e hD
  refine ⟨hL.sup_of_disjoint_vertices hE ?_,?_,?_,chord_basic_union_of_ordinary Z D E⟩
  · intro v hv he
    have hOrd : ∃ w : ↥Zᶜ, w.val = v ∧ IncidentTo D w := by
      rcases hv with ⟨_,a,b,ha,hb,h⟩ | ⟨_,a,b,ha,hb,h⟩
      · exact ⟨a,ha,Or.inl ⟨b,h⟩⟩
      · exact ⟨b,hb,Or.inr ⟨a,h⟩⟩
    obtain ⟨w,hw,hPath⟩ := hOrd
    have hSlot := basic_exceptional_endpoint_slots E Z hCover hNo w
    apply hApart w hPath
    exact (hw.symm ▸ he : IncidentTo E w.val).imp hSlot.1.mpr hSlot.2.mpr
  · intro v hv
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hCover v hv
    exact ⟨⟨a,Or.inr ha⟩,⟨b,Or.inr hb⟩⟩
  · rintro x y (⟨a,b,rfl,rfl,_⟩ | h) hx
    · exact ((mem_compl.mp a.prop) hx).elim
    · exact hNo x y h hx

end OverfullWork.DirectedRobustExpansion
