module

public import OverfullWork.KuhnOsthusPathPartition
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section


/-! Kühn–Osthus Proposition 7.3. Each corrected arc is followed by the
chords correcting it, with the final chord followed by the original
arc. The permutation of these cyclic lists gives local balance. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I : Type*} [Fintype V]

noncomputable def freeOut (D : Digraph V) (cluster : V → I) (i : I) : Finset V :=
  univ.filter (fun x => cluster x = i ∧ ¬ ∃ y, D.Adj x y)

noncomputable def freeIn (D : Digraph V) (cluster : V → I) (i : I) : Finset V :=
  univ.filter (fun x => cluster x = i ∧ ¬ ∃ y, D.Adj y x)

theorem mem_freeOut {D : Digraph V} {cluster : V → I} {i : I} {x : V} :
    x ∈ freeOut D cluster i ↔ cluster x = i ∧ ¬ ∃ y, D.Adj x y := by
  simp [freeOut]

theorem mem_freeIn {D : Digraph V} {cluster : V → I} {i : I} {x : V} :
    x ∈ freeIn D cluster i ↔ cluster x = i ∧ ¬ ∃ y, D.Adj y x := by
  simp [freeIn]

/-- Enumerate the arcs of the corrected system by their two endpoints.
Each cyclic list pairs the target cluster of one arc with the successor
of the source cluster of the next arc. -/
theorem locally_balanced_of_arc_permutation {E : Type*} [Fintype E]
    (D : Digraph V) (cluster : V → I) (s : Equiv.Perm I)
    (src dst : E → V) (rot : Equiv.Perm E)
    (hArcs : ∀ x y, D.Adj x y ↔ ∃ e, src e = x ∧ dst e = y)
    (hSrc : Function.Injective src) (hDst : Function.Injective dst)
    (hStep : ∀ e, cluster (dst e) = s (cluster (src (rot e))))
    (hSize : ∀ i, (univ.filter (fun x => cluster x = i)).card =
      (univ.filter (fun x => cluster x = s i)).card) :
    ∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card := by
  classical
  intro i
  let S : Finset E := univ.filter (fun e => cluster (src e) = i)
  let T : Finset E := univ.filter (fun e => cluster (dst e) = s i)
  have hMap : T.map rot.toEmbedding = S := by
    ext e
    rw [mem_map]
    constructor
    · rintro ⟨f,hf,he⟩
      have ht : cluster (dst f) = s i := (mem_filter.mp hf).2
      have hs := s.injective ((hStep f).symm.trans ht)
      exact mem_filter.mpr ⟨mem_univ _,by change rot f = e at he; rwa [←he]⟩
    · intro he
      have hs : cluster (src e) = i := (mem_filter.mp he).2
      refine ⟨rot.symm e,mem_filter.mpr ⟨mem_univ _,?_⟩,rot.apply_symm_apply e⟩
      rw [hStep,rot.apply_symm_apply,hs]
  have hCounts : S.card = T.card := by rw [←hMap,card_map]
  have hOut :
      (univ.filter (fun x => cluster x = i ∧ ∃ y, D.Adj x y)) =
        S.map ⟨src,hSrc⟩ := by
    ext x
    rw [mem_filter,mem_map]
    constructor
    · rintro ⟨_,hx,y,hy⟩
      obtain ⟨e,he,hd⟩ := (hArcs x y).mp hy
      exact ⟨e,mem_filter.mpr ⟨mem_univ _,he.symm ▸ hx⟩,he⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨mem_univ _,(mem_filter.mp he).2,dst e,(hArcs _ _).mpr ⟨e,rfl,rfl⟩⟩
  have hIn :
      (univ.filter (fun x => cluster x = s i ∧ ∃ y, D.Adj y x)) =
        T.map ⟨dst,hDst⟩ := by
    ext x
    rw [mem_filter,mem_map]
    constructor
    · rintro ⟨_,hx,y,hy⟩
      obtain ⟨e,he,hd⟩ := (hArcs y x).mp hy
      exact ⟨e,mem_filter.mpr ⟨mem_univ _,hd.symm ▸ hx⟩,hd⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨mem_univ _,(mem_filter.mp he).2,src e,(hArcs _ _).mpr ⟨e,rfl,rfl⟩⟩
  have hCo := card_filter_add_card_filter_not (s := univ.filter (fun x => cluster x = i))
    (fun x => ∃ y, D.Adj x y)
  have hCi := card_filter_add_card_filter_not (s := univ.filter (fun x => cluster x = s i))
    (fun x => ∃ y, D.Adj y x)
  rw [filter_filter,hOut,card_map,filter_filter] at hCo
  rw [filter_filter,hIn,card_map,filter_filter] at hCi
  change S.card + (freeOut D cluster i).card = _ at hCo
  change T.card + (freeIn D cluster (s i)).card = _ at hCi
  have hc := hSize i
  omega

/-- The usual indexing of a corrected path system. Position zero is the
original arc, the other positions are consecutive chords. The rotation
also accounts for the transition from the final chord to position zero. -/
theorem locally_balanced_of_chord_lists {E : Type*} [Fintype E] (k : E → ℕ)
    (D : Digraph V) (cluster : V → I) (s : Equiv.Perm I)
    (src dst : (Σ e, Fin (k e + 1)) → V)
    (hArcs : ∀ x y, D.Adj x y ↔ ∃ e, src e = x ∧ dst e = y)
    (hSrc : Function.Injective src) (hDst : Function.Injective dst)
    (hStep : ∀ e (j : Fin (k e + 1)),
       cluster (dst ⟨e,j⟩) = s (cluster (src ⟨e,finRotate (k e+1) j⟩)))
    (hSize : ∀ i, (univ.filter (fun x => cluster x = i)).card =
      (univ.filter (fun x => cluster x = s i)).card) :
    ∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card := by
  let rot : Equiv.Perm (Σ e, Fin (k e + 1)) :=
    Equiv.sigmaCongrRight (fun e => finRotate (k e+1))
  exact locally_balanced_of_arc_permutation D cluster s src dst rot hArcs hSrc hDst
    (fun ⟨e,j⟩ => hStep e j) hSize

end OverfullWork.DirectedRobustExpansion
