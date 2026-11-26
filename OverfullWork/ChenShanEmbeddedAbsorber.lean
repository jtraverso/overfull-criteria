module

public import OverfullWork.ChenShanAbsorberChoices
public import OverfullWork.ChenShanTripartiteCycles

@[expose] public section

namespace OverfullWork.ChenShan

variable {A B W A' B' W' I : Type*}

/-- The image of a relation under two injections. -/
def imageEdge (f : A ↪ A') (g : B ↪ B') (E : A → B → Prop) (a : A') (b : B') : Prop :=
  ∃ x y, f x = a ∧ g y = b ∧ E x y

theorem imageEdge_or (f : A ↪ A') (g : B ↪ B') (E F : A → B → Prop) :
    imageEdge f g (fun a b => E a b ∨ F a b) =
      fun a b => imageEdge f g E a b ∨ imageEdge f g F a b := by
  funext a b
  apply propext
  constructor
  · rintro ⟨x,y,hx,hy,h | h⟩
    · exact Or.inl ⟨x,y,hx,hy,h⟩
    · exact Or.inr ⟨x,y,hx,hy,h⟩
  · rintro (⟨x,y,hx,hy,h⟩ | ⟨x,y,hx,hy,h⟩)
    · exact ⟨x,y,hx,hy,Or.inl h⟩
    · exact ⟨x,y,hx,hy,Or.inr h⟩

/-- Injective relabeling preserves exact coverage of the three edge classes. -/
def TripartiteTriangleDecomposition.map {E : A → B → Prop} {l : A → W → Prop}
    {r : B → W → Prop} (D : TripartiteTriangleDecomposition E l r)
    (f : A ↪ A') (g : B ↪ B') (k : W ↪ W') :
    TripartiteTriangleDecomposition (imageEdge f g E) (imageEdge f k l) (imageEdge g k r) where
  triangle a b w := ∃ x y z, f x = a ∧ g y = b ∧ k z = w ∧ D.triangle x y z
  supported := by
    rintro a b w ⟨x,y,z,hx,hy,hz,h⟩
    obtain ⟨hE,hl,hr⟩ := D.supported x y z h
    exact ⟨⟨x,y,hx,hy,hE⟩,⟨x,z,hx,hz,hl⟩,⟨y,z,hy,hz,hr⟩⟩
  coversBase := by
    rintro _ _ ⟨x,y,rfl,rfl,h⟩
    obtain ⟨z,hz,hU⟩ := D.coversBase x y h
    refine ⟨k z,⟨x,y,z,rfl,rfl,rfl,hz⟩,?_⟩
    rintro _ ⟨x',y',z',hx,hy,rfl,h'⟩
    have hx' := f.injective hx
    have hy' := g.injective hy
    subst x'
    subst y'
    exact congrArg k (hU _ h')
  coversLeft := by
    rintro _ _ ⟨x,z,rfl,rfl,h⟩
    obtain ⟨y,hy,hU⟩ := D.coversLeft x z h
    refine ⟨g y,⟨x,y,z,rfl,rfl,rfl,hy⟩,?_⟩
    rintro _ ⟨x',y',z',hx,rfl,hz,h'⟩
    have hx' := f.injective hx
    have hz' := k.injective hz
    subst x'
    subst z'
    exact congrArg g (hU _ h')
  coversRight := by
    rintro _ _ ⟨y,z,rfl,rfl,h⟩
    obtain ⟨x,hx,hU⟩ := D.coversRight y z h
    refine ⟨f x,⟨x,y,z,rfl,rfl,rfl,hx⟩,?_⟩
    rintro _ ⟨x',y',z',rfl,hy,hz,h'⟩
    have hy' := g.injective hy
    have hz' := k.injective hz
    subst y'
    subst z'
    exact congrArg f (hU _ h')

private theorem imageEdge_range_pairs {X Y X' Y' : Type*} (a : X ↪ X') (b : Y ↪ Y')
      (u : I → X) (v : I → Y) :
      imageEdge a b (fun x y => (x,y) ∈ Set.range (fun i => (u i,v i))) =
        fun x y => ∃ i, a (u i) = x ∧ b (v i) = y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_,_,hx,hy,i,h⟩
    cases h
    exact ⟨i,hx,hy⟩
  · rintro ⟨i,hx,hy⟩
    exact ⟨u i,v i,hx,hy,i,rfl⟩

/-- Both sides of the absorber identity remain triangle-decomposable in
any injective realization of its vertices. -/
theorem embedded_cycle_absorber_decompositions (s : Equiv.Perm I)
    (f : (I ⊕ I) ↪ A) (g : (I ⊕ I) ↪ B) (k : Option I ↪ W) :
    let E := imageEdge f g (fun a b => (a,b) ∈ Set.range (absorberAB ∘ cycleAbsorberBefore s))
    let l := imageEdge f k (fun a w => (a,w) ∈ Set.range (absorberAW ∘ cycleAbsorberBefore s))
    let r := imageEdge g k (fun b w => (b,w) ∈ Set.range (absorberBW ∘ cycleAbsorberBefore s))
    Nonempty (TripartiteTriangleDecomposition E l r) ∧
      Nonempty (TripartiteTriangleDecomposition
        (fun a b => E a b ∨ ∃ i, f (.inl i) = a ∧ g (.inl i) = b)
        (fun a w => l a w ∨ ∃ i, f (.inl (s i)) = a ∧ k (some i) = w)
        (fun b w => r b w ∨ ∃ i, g (.inl i) = b ∧ k (some i) = w)) := by
  obtain ⟨⟨D⟩,⟨D'⟩⟩ := cycleAbsorber_decompositions s
  refine ⟨⟨D.map f g k⟩,?_⟩
  exact ⟨by simpa only [Set.mem_union, imageEdge_or,
    imageEdge_range_pairs f g Sum.inl Sum.inl,
    imageEdge_range_pairs f k (fun i => Sum.inl (s i)) some,
    imageEdge_range_pairs g k Sum.inl some] using D'.map f g k⟩

open Finset
open scoped Classical

private def disjointSumEmbedding (x : I ↪ A) (a : I ↪ A)
    (h : ∀ i j, x i ≠ a j) : (I ⊕ I) ↪ A where
  toFun := Sum.elim x a
  inj' := by
    rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (x.injective hij)
    · exact (h i j hij).elim
    · exact (h j i hij.symm).elim
    · exact congrArg Sum.inr (a.injective hij)

private def optionEmbedding (w : I ↪ W) (z : W)
    (h : ∀ i, w i ≠ z) : Option I ↪ W where
  toFun := fun i => i.elim z w
  inj' := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact (h j hij.symm).elim
    · exact (h i hij).elim
    · exact congrArg some (w.injective hij)

/-- The edge touches its own footprint and both endpoints are accounted for. -/
def FootprintEdge {V : Type*} (Q Z : Finset V) (u v : V) : Prop :=
  (u ∈ Q ∧ (v ∈ Q ∨ v ∈ Z)) ∨ (v ∈ Q ∧ (u ∈ Q ∨ u ∈ Z))

theorem FootprintEdge.disjoint {V : Type*} {P Q Z : Finset V} {u v : V}
    (hPQ : Disjoint P Q) (hPZ : Disjoint P Z)
    (hP : FootprintEdge P Z u v) (hQ : FootprintEdge Q Z u v) : False := by
  rcases hP with ⟨hPu,_⟩ | ⟨hPv,_⟩ <;>
    rcases hQ with ⟨hQu,hQv⟩ | ⟨hQv,hQu⟩
  · exact disjoint_left.mp hPQ hPu hQu
  · exact hQu.elim (disjoint_left.mp hPQ hPu) (disjoint_left.mp hPZ hPu)
  · exact hQv.elim (disjoint_left.mp hPQ hPv) (disjoint_left.mp hPZ hPv)
  · exact disjoint_left.mp hPQ hPv hQv

private theorem embedded_absorber_arc_count_le [Fintype I] [Fintype A] [Fintype B] [Fintype W]
    (s : Equiv.Perm I) (f : I ⊕ I ↪ A) (g : I ⊕ I ↪ B) (k : Option I ↪ W) :
    (tripartiteArcs
      (imageEdge f g (fun a b => (a,b) ∈ Set.range (absorberAB ∘ cycleAbsorberBefore s)))
      (imageEdge f k (fun a w => (a,w) ∈ Set.range (absorberAW ∘ cycleAbsorberBefore s)))
      (imageEdge g k (fun b w => (b,w) ∈ Set.range (absorberBW ∘ cycleAbsorberBefore s)))).card
        ≤ 9 * Fintype.card I := by
  let S := (univ : Finset (Fin 3 × I))
  let a (i) : A ⊕ (B ⊕ W) := Sum.inl (f (cycleAbsorberBefore s i).1)
  let b (i) : A ⊕ (B ⊕ W) := Sum.inr (Sum.inl (g (cycleAbsorberBefore s i).2.1))
  let w (i) : A ⊕ (B ⊕ W) := Sum.inr (Sum.inr (k (cycleAbsorberBefore s i).2.2))
  let X := S.image (fun i => (a i,b i))
  let Y := S.image (fun i => (b i,w i))
  let Z := S.image (fun i => (w i,a i))
  calc
    _ ≤ ((X ∪ Y) ∪ Z).card := by
      apply card_le_card
      rintro ⟨u,v⟩ h
      have h' := (mem_filter.mp h).2
      rcases u with a' | (b' | w') <;> rcases v with a'' | (b'' | w'') <;>
        simp only [tripartiteArc] at h'
      · obtain ⟨_,_,rfl,rfl,i,hi⟩ := h'
        cases hi
        exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
      · obtain ⟨_,_,rfl,rfl,i,hi⟩ := h'
        cases hi
        exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
      · obtain ⟨_,_,rfl,rfl,i,hi⟩ := h'
        cases hi
        exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    _ ≤ X.card + Y.card + Z.card := (card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ S.card + S.card + S.card := by
      exact Nat.add_le_add (Nat.add_le_add card_image_le card_image_le) card_image_le
    _ = _ := by simp [S,Fintype.card_prod]; omega

/-- A footprint avoiding the cycle vertices realizes the absorber in the
host graph. Every absorber edge has an endpoint in the footprint. -/
theorem exists_embedded_cycle_absorber_of_footprint [Fintype I] [Fintype A] [Fintype B] [Fintype W]
    {AB : A → B → Prop} {AW : A → W → Prop} {BW : B → W → Prop}
    (s : Equiv.Perm I) (x : I ↪ A) (y : I ↪ B) (w : I ↪ W)
    {Z Q : Finset (A ⊕ (B ⊕ W))}
    (hX : ∀ i, Sum.inl (x i) ∈ Z)
    (hY : ∀ i, Sum.inr (Sum.inl (y i)) ∈ Z)
    (hW : ∀ i, Sum.inr (Sum.inr (w i)) ∈ Z)
    (hDis : Disjoint Q Z) (hFoot : CycleAbsorberFootprint AB AW BW s x y w Q) :
    ∃ (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop),
      (∀ a b, E a b → AB a b ∧ FootprintEdge Q Z (Sum.inl a) (Sum.inr (Sum.inl b))) ∧
      (∀ a z, l a z → AW a z ∧ FootprintEdge Q Z (Sum.inl a) (Sum.inr (Sum.inr z))) ∧
      (∀ b z, r b z → BW b z ∧ FootprintEdge Q Z (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inr z))) ∧
      (tripartiteArcs E l r).card ≤ 9 * Fintype.card I ∧
      Nonempty (TripartiteTriangleDecomposition E l r) ∧
      Nonempty (TripartiteTriangleDecomposition
        (fun a b => E a b ∨ ∃ i, x i = a ∧ y i = b)
        (fun a z => l a z ∨ ∃ i, x (s i) = a ∧ w i = z)
        (fun b z => r b z ∨ ∃ i, y i = b ∧ w i = z)) := by
  obtain ⟨z,a,b,hQ,hEdges⟩ := hFoot
  have hA (i) : Sum.inl (a i) ∈ Q := by
    rw [hQ,inl_mem_disjSum]
    exact mem_map.mpr ⟨i,mem_univ _,rfl⟩
  have hB (i) : Sum.inr (Sum.inl (b i)) ∈ Q := by
    rw [hQ,inr_mem_disjSum,inl_mem_disjSum]
    exact mem_map.mpr ⟨i,mem_univ _,rfl⟩
  have hZ : Sum.inr (Sum.inr z) ∈ Q := by
    simp [hQ]
  have hx (i j) : x i ≠ a j := by
    intro h
    exact disjoint_left.mp hDis (hA j) (h ▸ hX i)
  have hy (i j) : y i ≠ b j := by
    intro h
    exact disjoint_left.mp hDis (hB j) (h ▸ hY i)
  have hw (i) : w i ≠ z := by
    intro h
    exact disjoint_left.mp hDis hZ (h ▸ hW i)
  let f := disjointSumEmbedding x a hx
  let g := disjointSumEmbedding y b hy
  let k := optionEmbedding w z hw
  refine ⟨imageEdge f g _,imageEdge f k _,imageEdge g k _,?_,?_,?_,
    embedded_absorber_arc_count_le s f g k,
    (embedded_cycle_absorber_decompositions s f g k).1,
    (embedded_cycle_absorber_decompositions s f g k).2⟩
  · rintro _ _ ⟨u,v,rfl,rfl,⟨⟨row,i⟩,h⟩⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change _ = u at h1
    change _ = v at h2
    rw [← h1,← h2]
    obtain ⟨_,_,h₃,h₄,h₅,_,_,_,_⟩ := hEdges i
    fin_cases row
    · exact ⟨h₃,Or.inr ⟨hB i,Or.inr (hX (s i))⟩⟩
    · exact ⟨h₅,Or.inl ⟨hA i,Or.inl (hB i)⟩⟩
    · exact ⟨h₄,Or.inl ⟨hA i,Or.inr (hY i)⟩⟩
  · rintro _ _ ⟨u,v,rfl,rfl,⟨⟨row,i⟩,h⟩⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change _ = u at h1
    change _ = v at h2
    rw [← h1,← h2]
    obtain ⟨h₁,_,_,_,_,h₆,h₇,_,_⟩ := hEdges i
    fin_cases row
    · exact ⟨h₁,Or.inr ⟨hZ,Or.inr (hX (s i))⟩⟩
    · exact ⟨h₆,Or.inl ⟨hA i,Or.inr (hW i)⟩⟩
    · exact ⟨h₇,Or.inl ⟨hA i,Or.inl hZ⟩⟩
  · rintro _ _ ⟨u,v,rfl,rfl,⟨⟨row,i⟩,h⟩⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change _ = u at h1
    change _ = v at h2
    rw [← h1,← h2]
    obtain ⟨_,h₂,_,_,_,_,_,h₈,h₉⟩ := hEdges i
    fin_cases row
    · exact ⟨h₉,Or.inl ⟨hB i,Or.inl hZ⟩⟩
    · exact ⟨h₈,Or.inl ⟨hB i,Or.inr (hW i)⟩⟩
    · exact ⟨h₂,Or.inr ⟨hZ,Or.inr (hY i)⟩⟩

end OverfullWork.ChenShan
