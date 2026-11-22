module

public import OverfullWork.SuperregularGreedyEmbedding

@[expose] public section


/-! Replace a bounded group of disjoint packed pieces by one more
piece, using cyclic shifts of their slots. It is enough to realize
the edges of the shifted pattern. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

structure LayeredTilePacking {p : ℕ} (X : Fin p → Finset V)
    (E : Fin p → Fin p → Bool) (R : Fin p → Fin p → Digraph V) (k : ℕ) where
  vertices : Fin k × Fin p ↪ V
  mem : ∀ i a, vertices (i,a) ∈ X a
  edge : ∀ i a b, E a b = true → (R a b).Adj (vertices (i,a)) (vertices (i,b))

def tilesTouch {p : ℕ} (E : Fin p → Fin p → Bool) (a b : Fin p) : Prop :=
  E a b = true ∨ E b a = true

/-- A constraint on two origins of slots in a shifted tile. -/
def shiftedTileConstraint {p h : ℕ} (E : Fin p → Fin p → Bool) (shift : Fin p → Fin (h+1))
    (x y : Fin (h+1)) (a b : Fin p) : Prop :=
  ∃ t : Fin (h+1), tilesTouch E a b ∧ t + shift a = x ∧ t + shift b = y

theorem shiftedTileConstraint.symm {p h : ℕ} {E : Fin p → Fin p → Bool}
    {shift : Fin p → Fin (h+1)} {x y : Fin (h+1)} {a b : Fin p}
    (H : shiftedTileConstraint E shift x y a b) : shiftedTileConstraint E shift y x b a := by
  obtain ⟨t,he,hx,hy⟩ := H
  exact ⟨t,he.symm,hy,hx⟩

/-- Distinct differences for the two orientations of every slot edge
give at most one constraint per pair of origins. -/
structure TileShiftPattern {p h : ℕ} (E : Fin p → Fin p → Bool) (shift : Fin p → Fin (h+1)) : Prop where
  distinct : ∀ a b, tilesTouch E a b → shift a ≠ shift b
  unique : ∀ a b c d, tilesTouch E a b → tilesTouch E c d →
    shift b - shift a = shift d - shift c → a = c ∧ b = d

theorem TileShiftPattern.constraint_unique {p h : ℕ} {E : Fin p → Fin p → Bool}
    {shift : Fin p → Fin (h+1)} (H : TileShiftPattern E shift)
    {x y : Fin (h+1)} {a b c d : Fin p}
    (h₁ : shiftedTileConstraint E shift x y a b) (h₂ : shiftedTileConstraint E shift x y c d) :
    a = c ∧ b = d := by
  obtain ⟨t,ht,ha,hb⟩ := h₁
  obtain ⟨s,hs,hc,hd⟩ := h₂
  have hAt : shift b - shift a = y - x := by rw [←ha,←hb]; abel
  have hAs : shift d - shift c = y - x := by rw [←hc,←hd]; abel
  exact H.unique a b c d ht hs (hAt.trans hAs.symm)

theorem TileShiftPattern.constraint_distinct {p h : ℕ} {E : Fin p → Fin p → Bool}
    {shift : Fin p → Fin (h+1)} (H : TileShiftPattern E shift)
    {x y : Fin (h+1)} {a b : Fin p}
    (h₁ : shiftedTileConstraint E shift x y a b) : x ≠ y := by
  obtain ⟨t,ht,rfl,rfl⟩ := h₁
  exact fun he => H.distinct a b ht (add_left_cancel he)

def LayeredTilePacking.augmentationVertex {p k h : ℕ} {X : Fin p → Finset V}
    {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R k) (root : Fin p ↪ V) (old : Fin h ↪ Fin k)
    (i : Fin (h+1)) (a : Fin p) : V :=
  Fin.cases (root a) (fun j => P.vertices (old j,a)) i

/-- In each slot, perform the cyclic shift on the selected indices
and fix every other index. All vertices of the old packing, together
with the unmatched root vertices, occur exactly once. -/
noncomputable def LayeredTilePacking.augmentByShift {p k h : ℕ} {X : Fin p → Finset V}
    {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R k) (root : Fin p ↪ V)
    (hRoot : ∀ a, root a ∈ X a) (hFree : ∀ a i b, root a ≠ P.vertices (i,b))
    (old : Fin h ↪ Fin k) (shift : Fin p → Fin (h+1))
    (hEdges : ∀ i a b, E a b = true → (R a b).Adj
      (P.augmentationVertex root old (i + shift a) a)
      (P.augmentationVertex root old (i + shift b) b)) :
    LayeredTilePacking X E R (k+1) := by
  let f (i : Fin (k+1)) (a : Fin p) : V := Fin.lastCases (root a) (fun j => P.vertices (j,a)) i
  have hfInj : Injective (fun z : Fin (k+1) × Fin p => f z.1 z.2) := by
    rintro ⟨i,a⟩ ⟨j,b⟩
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro he
        have he' : root a = root b := by simpa [f] using he
        rw [root.injective he']
      · intro he
        exact (hFree a j' b (by simpa [f] using he)).elim
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro he
        exact (hFree b i' a (by simpa [f] using he.symm)).elim
      · intro he
        have he' : P.vertices (i',a) = P.vertices (j',b) := by simpa [f] using he
        have h := P.vertices.injective he'
        exact Prod.ext (congrArg (fun z : Fin k × Fin p => z.1.castSucc) h)
          (congrArg (fun z : Fin k × Fin p => z.2) h)
  have hfMem (i : Fin (k+1)) (a : Fin p) : f i a ∈ X a := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [f] using hRoot a
    · simpa [f] using P.mem j a
  let tag (i : Fin (h+1)) : Fin (k+1) := Fin.cases (Fin.last k) (fun j => (old j).castSucc) i
  have hTag : Injective tag := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun j' => ?_) j
      intro h
      have he : Fin.last k = (old j').castSucc := by simpa [tag] using h
      exact ((Fin.castSucc_ne_last (old j')) he.symm).elim
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro h
        have he : (old i').castSucc = Fin.last k := by simpa only [tag,Fin.cases_succ,Fin.cases_zero] using h
        exact ((Fin.castSucc_ne_last (old i')) he).elim
      · intro h
        have he : (old i').castSucc = (old j').castSucc := by simpa [tag] using h
        rw [old.injective (Fin.castSucc_injective _ he)]
  let e := Equiv.ofInjective tag hTag
  let onSelected (a : Fin p) : Equiv.Perm (Set.range tag) :=
    e.symm.trans ((Equiv.addRight (shift a)).trans e)
  let rotate (a : Fin p) : Equiv.Perm (Fin (k+1)) := Equiv.Perm.ofSubtype (onSelected a)
  have hRotate (i : Fin (h+1)) (a : Fin p) : rotate a (tag i) = tag (i + shift a) := by
    change Equiv.Perm.ofSubtype (onSelected a) (tag i) = _
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ (show tag i ∈ Set.range tag from ⟨i,rfl⟩)]
    change tag (e.symm (e i) + shift a) = _
    rw [e.symm_apply_apply]
  have hOff (i : Fin (k+1)) (hi : i ∉ Set.range tag) (a : Fin p) : rotate a i = i :=
    Equiv.Perm.ofSubtype_apply_of_not_mem _ hi
  have hAt (i : Fin (h+1)) (a : Fin p) : f (tag i) a = P.augmentationVertex root old i a := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [f,tag,LayeredTilePacking.augmentationVertex]
    · simp [f,tag,LayeredTilePacking.augmentationVertex]
  let q (z : Fin (k+1) × Fin p) := (rotate z.2 z.1,z.2)
  have hq : Injective q := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hab : a = b := congrArg Prod.snd he
    subst b
    exact Prod.ext ((rotate a).injective (congrArg Prod.fst he)) rfl
  refine ⟨⟨fun z => f (q z).1 (q z).2,hfInj.comp hq⟩,fun i a => hfMem _ _,?_⟩
  intro i a b hab
  change (R a b).Adj (f (rotate a i) a) (f (rotate b i) b)
  by_cases hi : i ∈ Set.range tag
  · obtain ⟨j,rfl⟩ := hi
    rw [hRotate,hRotate,hAt,hAt]
    exact hEdges j a b hab
  · rw [hOff i hi,hOff i hi]
    revert hi
    refine Fin.lastCases ?_ (fun j _ => ?_) i
    · intro hn
      exact (hn ⟨0,rfl⟩).elim
    · simpa [f] using P.edge j a b hab

end OverfullWork.DirectedRobustExpansion
