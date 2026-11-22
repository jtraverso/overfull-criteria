module

public import OverfullWork.DirectedLayoutRound
public import OverfullWork.InducedDigraphSampling

@[expose] public section


/-! Realize the short portions in the subdigraph induced by the complement
of the assigned block, while retaining the original layout indices. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion InducedDigraphSampling
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

/-- The reserve kept for the short paths excludes the whole assigned block,
including all arcs incident to that block. -/
def outsideBlock (Γ : Digraph V) (A : Finset V) : Digraph V where
  Adj x y := Γ.Adj x y ∧ x ∉ A ∧ y ∉ A

omit [Fintype V] in
private theorem card_filtered_subtype_le (A B : Finset V) :
    ((univ : Finset A).filter (fun x => x.val ∈ B)).card ≤ B.card := by
  apply card_le_card_of_injOn (fun x => x.val)
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x _ y _ h
    exact Subtype.ext h

/-- Construct the short paths in the actual induced complement. Their
interiors leave the assigned block intact for the long path. -/
theorem exists_shortPortion_outside_block (Γ : Digraph V) (A : Finset V)
    (L : Layout V I) (long : I) (Z : Finset V) {r s t h : ℕ}
    (hA : Disjoint L.boundary A) (hZ : Disjoint L.boundary Z)
    (hR : IsRobustAt (induced Γ Aᶜ) r t) (hs : 0 < s)
    (hLen : Fintype.card (Aᶜ : Finset V)/s+5 ≤ h)
    (hBudget : Z.card+L.boundary.card+(univ \ insert long L.fixed).card*h+s ≤ r)
    (hIn : ∀ v : (Aᶜ : Finset V), t ≤ inDegree (induced Γ Aᶜ) v)
    (hOut : ∀ v : (Aᶜ : Finset V),
      t+Z.card+L.boundary.card+(univ \ insert long L.fixed).card*h+1 ≤
        outDegree (induced Γ Aᶜ) v) :
    ∃ S : ShortPortion (outsideBlock Γ A) L long,
      (∀ x ∈ A, S.remaining x) ∧
      ∀ i ∉ insert long L.fixed, (S.interior i).length ≤ h ∧
        ∀ x ∈ S.interior i, x ∉ Z := by
  let B : Finset V := Aᶜ
  let M : Finset B := univ.filter (fun x => x.val ∈ L.boundary)
  let Z' : Finset B := univ.filter (fun x => x.val ∈ Z)
  let L' : Layout B I := {
    boundary := M
    source := fun i => ⟨L.source i,mem_compl.mpr (disjoint_left.mp hA (L.ends i).1)⟩
    target := fun i => ⟨L.target i,mem_compl.mpr (disjoint_left.mp hA (L.ends i).2.1)⟩
    fixed := L.fixed
    ends := fun i => ⟨mem_filter.mpr ⟨mem_univ _,(L.ends i).1⟩,
      mem_filter.mpr ⟨mem_univ _,(L.ends i).2.1⟩,
      fun he => (L.ends i).2.2 (congrArg Subtype.val he)⟩ }
  have hApart : Disjoint L'.boundary Z' :=
    disjoint_left.mpr fun _ hm hz => disjoint_left.mp hZ (mem_filter.mp hm).2 (mem_filter.mp hz).2
  have hm : L'.boundary.card ≤ L.boundary.card := card_filtered_subtype_le B L.boundary
  have hz : Z'.card ≤ Z.card := card_filtered_subtype_le B Z
  obtain ⟨T,hT⟩ := exists_shortPortion (induced Γ B) L' long Z' hR hs hLen hApart
    (by change Z'.card+L'.boundary.card+(univ \ insert long L.fixed).card*h+s ≤ r; omega)
    hIn (fun v => by
      have hv := hOut v
      change t+Z'.card+L'.boundary.card+(univ \ insert long L.fixed).card*h+1 ≤
        outDegree (induced Γ Aᶜ) v
      omega)
  let f (i : I) := (T.interior i).map (fun x => x.val)
  have hMem i x (hx : x ∈ f i) : ∃ v : B, v ∈ T.interior i ∧ v.val = x :=
    List.mem_map.mp hx
  let S : ShortPortion (outsideBlock Γ A) L long := {
    interior := f
    nonempty := fun i hi he => T.nonempty i hi (List.map_eq_nil_iff.mp he)
    simple := by
      intro i hi
      simpa only [f,List.map_cons,List.map_append,List.map_nil] using
        (T.simple i hi).map (f := fun x : B => x.val) Subtype.val_injective
    chain := by
      intro i hi
      have hh := List.isChain_map_of_isChain (fun x : B => x.val)
        (fun x y he => (show (outsideBlock Γ A).Adj x.val y.val from
          ⟨he,mem_compl.mp x.prop,mem_compl.mp y.prop⟩)) (T.chain i hi)
      simpa only [f,List.map_cons,List.map_append,List.map_nil] using hh
    outside := by
      intro i hi x hx hX
      obtain ⟨y,hy,rfl⟩ := hMem i x hx
      exact T.outside i hi y hy (mem_filter.mpr ⟨mem_univ _,hX⟩)
    disjoint := by
      intro i hi j hj he x hx hy
      obtain ⟨v,hvi,hv⟩ := hMem i x hx
      obtain ⟨w,hwj,hw⟩ := hMem j x hy
      exact T.disjoint i hi j hj he hvi (Subtype.ext (hv.trans hw.symm) ▸ hwj) }
  refine ⟨S,?_,?_⟩
  · intro x hx
    refine ⟨fun h => disjoint_left.mp hA h hx,?_⟩
    intro i hi hmem
    obtain ⟨y,_,rfl⟩ := hMem i x hmem
    exact (mem_compl.mp y.prop) hx
  · intro i hi
    obtain ⟨hLength,hAvoid⟩ := hT i hi
    refine ⟨by simpa only [S,f,List.length_map] using hLength,?_⟩
    intro x hx hxZ
    obtain ⟨y,hy,rfl⟩ := hMem i x hx
    exact hAvoid y hy (mem_filter.mpr ⟨mem_univ _,hxZ⟩)

end OverfullWork.DirectedSpanningConfiguration
