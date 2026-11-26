module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace OverfullWork.ChenShan

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

/-- A residual coloring uses only available colors and uses each available
color once at its endpoint. The latter condition is automatic for a
proper full coloring in the regular application. -/
structure SaturatedResidualColoring (E : A → B → Prop) (left : A → W → Prop)
    (right : B → W → Prop) where
  color : {p : A × B // E p.1 p.2} → W
  available : ∀ e, left e.val.1 (color e) ∧ right e.val.2 (color e)
  coversLeft : ∀ a w, left a w → ∃! b : B, ∃ h : E a b, color ⟨(a, b), h⟩ = w
  coversRight : ∀ b w, right b w → ∃! a : A, ∃ h : E a b, color ⟨(a, b), h⟩ = w

/-- Each edge of the tripartite graph is used by exactly one triangle. -/
structure TripartiteTriangleDecomposition (E : A → B → Prop) (left : A → W → Prop)
    (right : B → W → Prop) where
  triangle : A → B → W → Prop
  supported : ∀ a b w, triangle a b w → E a b ∧ left a w ∧ right b w
  coversBase : ∀ a b, E a b → ∃! w, triangle a b w
  coversLeft : ∀ a w, left a w → ∃! b, triangle a b w
  coversRight : ∀ b w, right b w → ∃! a, triangle a b w

/-- The triangle correspondence of Chen–Shan, Lemma 4.4. The three
exact-cover conditions account for base edges and both incidence sides. -/
theorem residual_coloring_iff_triangle_decomposition (E : A → B → Prop)
    (left : A → W → Prop) (right : B → W → Prop) :
    Nonempty (SaturatedResidualColoring E left right) ↔
      Nonempty (TripartiteTriangleDecomposition E left right) := by
  constructor
  · rintro ⟨C⟩
    refine ⟨⟨fun a b w => ∃ h : E a b, C.color ⟨(a,b),h⟩ = w, ?_, ?_,
      C.coversLeft, C.coversRight⟩⟩
    · intro a b w ht
      obtain ⟨h, rfl⟩ := ht
      exact ⟨h, C.available ⟨(a,b),h⟩⟩
    · intro a b h
      refine ⟨C.color ⟨(a,b),h⟩, ⟨h,rfl⟩, ?_⟩
      rintro w ⟨h', hw⟩
      exact hw.symm
  · rintro ⟨T⟩
    let color (e : {p : A × B // E p.1 p.2}) : W :=
      (T.coversBase e.val.1 e.val.2 e.property).exists.choose
    have hSelected (e : {p : A × B // E p.1 p.2}) :
        T.triangle e.val.1 e.val.2 (color e) :=
      (T.coversBase e.val.1 e.val.2 e.property).exists.choose_spec
    have hUnique (a : A) (b : B) (w : W) :
        T.triangle a b w ↔ ∃ h : E a b, color ⟨(a,b),h⟩ = w := by
      constructor
      · intro ht
        have h := (T.supported a b w ht).1
        refine ⟨h, ?_⟩
        obtain ⟨w₀, _, hU⟩ := T.coversBase a b h
        exact (hU _ (hSelected ⟨(a,b),h⟩)).trans (hU w ht).symm
      · rintro ⟨h, rfl⟩
        exact hSelected ⟨(a,b),h⟩
    refine ⟨⟨color, fun e => (T.supported _ _ _ (hSelected e)).2, ?_, ?_⟩⟩
    · intro a w h
      exact existsUnique_congr (fun b => hUnique a b w) |>.mp (T.coversLeft a w h)
    · intro b w h
      exact existsUnique_congr (fun a => hUnique a b w) |>.mp (T.coversRight b w h)


open scoped Classical in
private theorem exact_coverage_of_card {V W : Type*} [Fintype V] [Fintype W]
    (P : V → Prop) (Q : W → Prop) (f : {v // P v} → W)
    (hAvail : ∀ v, Q (f v)) (hInjective : Function.Injective f)
    (hCard : Fintype.card {v // P v} = Fintype.card {w // Q w})
    (w : W) (hw : Q w) :
    ∃! v : V, ∃ h : P v, f ⟨v, h⟩ = w := by
  let g (v : {v // P v}) : {w // Q w} := ⟨f v, hAvail v⟩
  have hg : Function.Injective g := fun a b h => hInjective (congrArg Subtype.val h)
  have hSurj := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hCard⟩).2
  obtain ⟨v,hv⟩ := hSurj ⟨w,hw⟩
  refine ⟨v.val, ⟨v.property,congrArg Subtype.val hv⟩, ?_⟩
  rintro u ⟨hu,he⟩
  apply congrArg Subtype.val (hInjective ?_ : (⟨u,hu⟩ : {v // P v}) = v)
  exact he.trans (congrArg Subtype.val hv).symm

open scoped Classical in
/-- In a proper residual coloring, equality of the residual degree and
the number of available colors gives the incidence coverage of Lemma 4.4. -/
theorem saturate_residual_coloring [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (left : A → W → Prop) (right : B → W → Prop)
    (color : {p : A × B // E p.1 p.2} → W)
    (hAvail : ∀ e, left e.val.1 (color e) ∧ right e.val.2 (color e))
    (hProperLeft : ∀ a, Function.Injective (fun b : {b // E a b} =>
      color ⟨(a,b.val),b.property⟩))
    (hProperRight : ∀ b, Function.Injective (fun a : {a // E a b} =>
      color ⟨(a.val,b),a.property⟩))
    (hCardLeft : ∀ a, Fintype.card {b // E a b} = Fintype.card {w // left a w})
    (hCardRight : ∀ b, Fintype.card {a // E a b} = Fintype.card {w // right b w}) :
    Nonempty (SaturatedResidualColoring E left right) := by
  refine ⟨⟨color,hAvail,?_,?_⟩⟩
  · intro a w hw
    exact exact_coverage_of_card (E a) (left a) (fun b => color ⟨(a,b.val),b.property⟩)
      (fun b => (hAvail ⟨(a,b.val),b.property⟩).1) (hProperLeft a) (hCardLeft a) w hw
  · intro b w hw
    exact exact_coverage_of_card (fun a => E a b) (right b)
      (fun a => color ⟨(a.val,b),a.property⟩)
      (fun a => (hAvail ⟨(a.val,b),a.property⟩).2) (hProperRight b) (hCardRight b) w hw


open scoped Classical in
/-- Neighbor counts agree across the two other classes at each vertex. -/
def TripartiteLocallyBalanced [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (left : A → W → Prop) (right : B → W → Prop) : Prop :=
  (∀ a, Fintype.card {b // E a b} = Fintype.card {w // left a w}) ∧
  (∀ b, Fintype.card {a // E a b} = Fintype.card {w // right b w}) ∧
  ∀ w, Fintype.card {a // left a w} = Fintype.card {b // right b w}

open scoped Classical in
/-- The leftover graph is locally balanced. Its two base-side degree
conditions express regularity after subtracting the proper precoloring.
At a color vertex, the prescribed matching covers equally many vertices
on both sides. -/
theorem residual_tripartite_balanced [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (usedLeft : A → W → Prop) (usedRight : B → W → Prop)
    (hSides : Fintype.card A = Fintype.card B)
    (hLeft : ∀ a, Fintype.card {b // E a b} + Fintype.card {w // usedLeft a w} = Fintype.card W)
    (hRight : ∀ b, Fintype.card {a // E a b} + Fintype.card {w // usedRight b w} = Fintype.card W)
    (hUsed : ∀ w, Fintype.card {a // usedLeft a w} = Fintype.card {b // usedRight b w}) :
    TripartiteLocallyBalanced E (fun a w => ¬ usedLeft a w) (fun b w => ¬ usedRight b w) ∧
      (∀ a, Fintype.card W - Fintype.card {w // ¬ usedLeft a w} = Fintype.card {w // usedLeft a w}) ∧
      (∀ b, Fintype.card W - Fintype.card {w // ¬ usedRight b w} = Fintype.card {w // usedRight b w}) ∧
      ∀ w,
        Fintype.card A - Fintype.card {a // ¬ usedLeft a w} = Fintype.card {a // usedLeft a w} ∧
        Fintype.card B - Fintype.card {b // ¬ usedRight b w} = Fintype.card {b // usedRight b w} := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a
    rw [Fintype.card_subtype_compl]
    have h := hLeft a
    omega
  · intro b
    rw [Fintype.card_subtype_compl]
    have h := hRight b
    omega
  · intro w
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hSides, hUsed w]
  · intro a
    rw [Fintype.card_subtype_compl]
    have h := hLeft a
    omega
  · intro b
    rw [Fintype.card_subtype_compl]
    have h := hRight b
    omega
  · intro w
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    have hA := Fintype.card_le_of_injective (fun a : {a // usedLeft a w} => a.val) Subtype.val_injective
    have hB := Fintype.card_le_of_injective (fun b : {b // usedRight b w} => b.val) Subtype.val_injective
    omega


theorem exact_cover_union {T : Type*} {p q : Prop} {A B : T → Prop}
    (hDis : p → q → False) (hA : ∀ t, A t → p) (hB : ∀ t, B t → q)
    (hOne : p → ∃! t, A t) (hTwo : q → ∃! t, B t)
    (h : p ∨ q) : ∃! t, A t ∨ B t := by
  rcases h with hp | hq
  · obtain ⟨t,ht,hU⟩ := hOne hp
    refine ⟨t,Or.inl ht,?_⟩
    rintro u (hu | hu)
    · exact hU u hu
    · exact (hDis hp (hB u hu)).elim
  · obtain ⟨t,ht,hU⟩ := hTwo hq
    refine ⟨t,Or.inr ht,?_⟩
    rintro u (hu | hu)
    · exact (hDis (hA u hu) hq).elim
    · exact hU u hu

/-- Edge-disjoint tripartite decompositions can be combined. Disjointness
is required on each of the three edge types, even when vertices overlap. -/
def TripartiteTriangleDecomposition.union
    {E F : A → B → Prop} {l l' : A → W → Prop} {r r' : B → W → Prop}
    (D : TripartiteTriangleDecomposition E l r) (D' : TripartiteTriangleDecomposition F l' r')
    (hBase : ∀ a b, E a b → F a b → False)
    (hLeft : ∀ a w, l a w → l' a w → False)
    (hRight : ∀ b w, r b w → r' b w → False) :
    TripartiteTriangleDecomposition (fun a b => E a b ∨ F a b)
      (fun a w => l a w ∨ l' a w) (fun b w => r b w ∨ r' b w) where
  triangle a b w := D.triangle a b w ∨ D'.triangle a b w
  supported a b w := by
    rintro (h | h)
    · obtain ⟨hE,hL,hR⟩ := D.supported a b w h
      exact ⟨Or.inl hE,Or.inl hL,Or.inl hR⟩
    · obtain ⟨hF,hL,hR⟩ := D'.supported a b w h
      exact ⟨Or.inr hF,Or.inr hL,Or.inr hR⟩
  coversBase a b := exact_cover_union (hBase a b)
    (fun w h => (D.supported a b w h).1) (fun w h => (D'.supported a b w h).1)
    (D.coversBase a b) (D'.coversBase a b)
  coversLeft a w := exact_cover_union (hLeft a w)
    (fun b h => (D.supported a b w h).2.1) (fun b h => (D'.supported a b w h).2.1)
    (D.coversLeft a w) (D'.coversLeft a w)
  coversRight b w := exact_cover_union (hRight b w)
    (fun a h => (D.supported a b w h).2.2) (fun a h => (D'.supported a b w h).2.2)
    (D.coversRight b w) (D'.coversRight b w)


/-- Exact triangle decompositions assemble over a finite family with
pairwise disjoint edges, even when its members share vertices. -/
theorem tripartite_decomposition_finite_union {I : Type*} [DecidableEq I]
    (S : Finset I) (E : I → A → B → Prop) (l : I → A → W → Prop)
    (r : I → B → W → Prop)
    (hDecomp : ∀ i ∈ S, Nonempty (TripartiteTriangleDecomposition (E i) (l i) (r i)))
    (hBase : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a b, E i a b → E j a b → False)
    (hLeft : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a w, l i a w → l j a w → False)
    (hRight : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ b w, r i b w → r j b w → False) :
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => ∃ i ∈ S, E i a b)
      (fun a w => ∃ i ∈ S, l i a w)
      (fun b w => ∃ i ∈ S, r i b w)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨fun _ _ _ => False, ?_, ?_, ?_, ?_⟩⟩
    · intro _ _ _ h
      exact h.elim
    all_goals simp
  | @insert i S hi ih =>
    have hIn (j : I) (hj : j ∈ S) : j ∈ insert i S := Finset.mem_insert_of_mem hj
    obtain ⟨D⟩ := hDecomp i (Finset.mem_insert_self _ _)
    obtain ⟨R⟩ := ih (fun j hj => hDecomp j (hIn j hj))
      (fun j hj k hk => hBase j (hIn j hj) k (hIn k hk))
      (fun j hj k hk => hLeft j (hIn j hj) k (hIn k hk))
      (fun j hj k hk => hRight j (hIn j hj) k (hIn k hk))
    have hDis (j : I) (hj : j ∈ S) : i ≠ j := fun he => hi (he.symm ▸ hj)
    have hU := D.union R
      (fun a b h => by
        rintro ⟨j,hj,h'⟩
        exact hBase i (Finset.mem_insert_self _ _) j (hIn j hj) (hDis j hj) a b h h')
      (fun a w h => by
        rintro ⟨j,hj,h'⟩
        exact hLeft i (Finset.mem_insert_self _ _) j (hIn j hj) (hDis j hj) a w h h')
      (fun b w h => by
        rintro ⟨j,hj,h'⟩
        exact hRight i (Finset.mem_insert_self _ _) j (hIn j hj) (hDis j hj) b w h h')
    have hInsert (P : I → Prop) :
        (∃ j ∈ insert i S, P j) ↔ P i ∨ ∃ j ∈ S, P j := by
      constructor
      · rintro ⟨j,hj,hP⟩
        rcases Finset.mem_insert.mp hj with rfl | h
        · exact Or.inl hP
        · exact Or.inr ⟨j,h,hP⟩
      · rintro (h | ⟨j,hj,hP⟩)
        · exact ⟨i,Finset.mem_insert_self _ _,h⟩
        · exact ⟨j,hIn j hj,hP⟩
    simpa only [hInsert] using (show Nonempty _ from ⟨hU⟩)


private theorem indexed_union_add_one {I : Type*} (S : Finset I) (j : I) (hj : j ∈ S)
    (E : I → Prop) (F : Prop) :
    (∃ i ∈ S, E i ∨ (i = j ∧ F)) ↔ (∃ i ∈ S, E i) ∨ F := by
  constructor
  · rintro ⟨i,hi,he | hf⟩
    · exact Or.inl ⟨i,hi,he⟩
    · exact Or.inr hf.2
  · rintro (⟨i,hi,he⟩ | hf)
    · exact ⟨i,hi,Or.inl he⟩
    · exact ⟨j,hj,Or.inr ⟨rfl,hf⟩⟩

private theorem indexed_edges_add_one_disjoint {I : Type*} {E : I → Prop} {F : Prop}
    {i j k : I} (hik : i ≠ k) (hE : E i → E k → False)
    (hFi : F → E i → False) (hFk : F → E k → False) :
    (E i ∨ (i = j ∧ F)) → (E k ∨ (k = j ∧ F)) → False := by
  rintro (hi | ⟨hij,hi⟩) (hk | ⟨hkj,hk⟩)
  · exact hE hi hk
  · exact hFi hk hi
  · exact hFk hi hk
  · exact hik (hij.trans hkj.symm)

/-- The assembly step in Lemma 4.6. If all chosen absorbers are
edge-disjoint and avoid each possible remainder, their union absorbs
any one of the remainders that a member absorbs. -/
theorem tripartite_absorber_union_absorbs {I : Type*} [DecidableEq I]
    (S : Finset I) (j : I) (hj : j ∈ S)
    (E : I → A → B → Prop) (l : I → A → W → Prop) (r : I → B → W → Prop)
    (F : A → B → Prop) (lF : A → W → Prop) (rF : B → W → Prop)
    (hDecomp : ∀ i ∈ S, Nonempty (TripartiteTriangleDecomposition (E i) (l i) (r i)))
    (hAbsorb : Nonempty (TripartiteTriangleDecomposition (fun a b => E j a b ∨ F a b)
      (fun a w => l j a w ∨ lF a w) (fun b w => r j b w ∨ rF b w)))
    (hBase : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ∀ a b, E i a b → E k a b → False)
    (hLeft : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ∀ a w, l i a w → l k a w → False)
    (hRight : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ∀ b w, r i b w → r k b w → False)
    (hNewBase : ∀ i ∈ S, ∀ a b, F a b → E i a b → False)
    (hNewLeft : ∀ i ∈ S, ∀ a w, lF a w → l i a w → False)
    (hNewRight : ∀ i ∈ S, ∀ b w, rF b w → r i b w → False) :
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => (∃ i ∈ S, E i a b) ∨ F a b)
      (fun a w => (∃ i ∈ S, l i a w) ∨ lF a w)
      (fun b w => (∃ i ∈ S, r i b w) ∨ rF b w)) := by
  let E' (i : I) (a : A) (b : B) := E i a b ∨ (i = j ∧ F a b)
  let l' (i : I) (a : A) (w : W) := l i a w ∨ (i = j ∧ lF a w)
  let r' (i : I) (b : B) (w : W) := r i b w ∨ (i = j ∧ rF b w)
  have hDec (i : I) (hi : i ∈ S) : Nonempty (TripartiteTriangleDecomposition (E' i) (l' i) (r' i)) := by
    by_cases he : i = j
    · subst i
      simpa only [E',l',r',true_and] using hAbsorb
    · simpa only [E',l',r',he,false_and,or_false] using hDecomp i hi
  have hD := tripartite_decomposition_finite_union S E' l' r' hDec
    (fun i hi k hk hne a b => indexed_edges_add_one_disjoint (E := fun t => E t a b) (F := F a b) (j := j) hne
      (hBase i hi k hk hne a b) (hNewBase i hi a b) (hNewBase k hk a b))
    (fun i hi k hk hne a w => indexed_edges_add_one_disjoint (E := fun t => l t a w) (F := lF a w) (j := j) hne
      (hLeft i hi k hk hne a w) (hNewLeft i hi a w) (hNewLeft k hk a w))
    (fun i hi k hk hne b w => indexed_edges_add_one_disjoint (E := fun t => r t b w) (F := rF b w) (j := j) hne
      (hRight i hi k hk hne b w) (hNewRight i hi b w) (hNewRight k hk b w))
  simpa only [E',l',r',indexed_union_add_one S j hj] using hD

end OverfullWork.ChenShan
