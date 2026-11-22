module

public import OverfullWork.KuhnOsthusChordMatching
public import OverfullWork.NearRegularBipartiteMatching
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! The defect-Hall argument of Kühn–Osthus Lemma 4.12(i),
used for the candidate chord matchings of Lemma 8.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset NearRegularBipartiteMatching
open scoped Classical

theorem exists_matching_with_rectangle_deficit {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (e : ℕ) (hSize : Fintype.card A = Fintype.card B)
    (hRect : ∀ S : Finset A, ∀ T : Finset B, e < S.card → e < T.card →
      ∃ a ∈ S, ∃ b ∈ T, R a b) :
    ∃ M : PartialMatching R, Fintype.card A ≤ M.domain.card + e := by
  apply exists_of_deficit R e
  intro S
  by_cases hSmall : S.card ≤ e
  · omega
  let T := univ \ neighbours R S
  have hT : T.card ≤ e := by
    by_contra! h
    obtain ⟨a,ha,b,hb,hab⟩ := hRect S T (by omega) h
    exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨mem_univ _,a,ha,hab⟩)
  have hCard := card_sdiff_add_card_eq_card (subset_univ (neighbours R S))
  rw [card_univ] at hCard
  change T.card + (neighbours R S).card = Fintype.card B at hCard
  have hS := card_le_univ S
  omega

/-- Move the defect-Hall matching back to the physical vertices
of two disjoint sides. -/
theorem exists_physical_matching_of_rectangle_deficit {V : Type*} [Fintype V]
    (D : Digraph V) (A B : Finset V) (e : ℕ)
    (hSize : A.card = B.card) (hDis : Disjoint A B)
    (hRect : ∀ S ⊆ A, ∀ T ⊆ B, e < S.card → e < T.card → 0 < incidences D S T) :
    ∃ M : Finset (V × V), A.card ≤ M.card + e ∧
      (∀ z ∈ M, z.1 ∈ A ∧ z.2 ∈ B ∧ D.Adj z.1 z.2 ∧ z.1 ≠ z.2) ∧
      Set.InjOn Prod.fst (↑M : Set (V × V)) ∧ Set.InjOn Prod.snd (↑M : Set (V × V)) := by
  classical
  let R (a : A) (b : B) := D.Adj a b
  have hSmall (S : Finset A) (T : Finset B) (hs : e < S.card) (ht : e < T.card) :
      ∃ a ∈ S, ∃ b ∈ T, R a b := by
    let X := S.image (fun a : A => a.val)
    let Y := T.image (fun b : B => b.val)
    have hX : X ⊆ A := by
      rintro x hx
      obtain ⟨a,_,rfl⟩ := mem_image.mp hx
      exact a.prop
    have hY : Y ⊆ B := by
      rintro y hy
      obtain ⟨b,_,rfl⟩ := mem_image.mp hy
      exact b.prop
    have hXS : X.card = S.card := card_image_of_injective _ Subtype.coe_injective
    have hYT : Y.card = T.card := card_image_of_injective _ Subtype.coe_injective
    have h := hRect X hX Y hY (by omega) (by omega)
    have hP : ∃ y ∈ Y, 0 < inNeighbours D X y := by
      by_contra! hAll
      unfold incidences at h
      have hZero : (∑ y ∈ Y, inNeighbours D X y) = 0 :=
        sum_eq_zero (fun y hy => Nat.eq_zero_of_le_zero (hAll y hy))
      omega
    obtain ⟨y,hy,hny⟩ := hP
    obtain ⟨x,hx⟩ := card_pos.mp hny
    obtain ⟨a,ha,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    exact ⟨a,ha,b,hb,(mem_filter.mp hx).2⟩
  obtain ⟨P,hP⟩ := exists_matching_with_rectangle_deficit R e
    (by simpa only [Fintype.card_coe] using hSize) hSmall
  let f (x : P.domain) : V × V := (x.val.val,(P.target x).val)
  have hFirst : Function.Injective (fun x : P.domain => (f x).1) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have hSecond : Function.Injective (fun x : P.domain => (f x).2) := by
    intro a b h
    exact P.target.injective (Subtype.ext h)
  let M := (univ : Finset P.domain).image f
  have hCount : M.card = P.domain.card := by
    rw [card_image_of_injective _ (fun a b he => hFirst (congrArg Prod.fst he)),card_univ,Fintype.card_coe]
  have hP' := hP
  rw [Fintype.card_coe] at hP'
  refine ⟨M,by omega,?_,?_,?_⟩
  · intro z hz
    obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    refine ⟨a.val.prop,(P.target a).prop,P.adjacent a,?_⟩
    intro heq
    change a.val.val = (P.target a).val at heq
    exact disjoint_left.mp hDis a.val.prop (heq.symm ▸ (P.target a).prop)
  · intro a ha b hb hab
    obtain ⟨x,_,rfl⟩ := mem_image.mp (show a ∈ M from ha)
    obtain ⟨y,_,rfl⟩ := mem_image.mp (show b ∈ M from hb)
    exact congrArg f (hFirst hab)
  · intro a ha b hb hab
    obtain ⟨x,_,rfl⟩ := mem_image.mp (show a ∈ M from ha)
    obtain ⟨y,_,rfl⟩ := mem_image.mp (show b ∈ M from hb)
    exact congrArg f (hSecond hab)

/-- Produce a physical matching inside the 24 selected styles of a chord
pair. The rectangle cutoff may be at most one fiftieth of a cluster. -/
theorem exists_chord_candidate_matching {V : Type*} [Fintype V]
    (D : Digraph V) (A B : Finset V) (m e : ℕ)
    (hSize : A.card = B.card) (hA : 24*m ≤ 50*A.card) (he : 50*e ≤ m)
    (hDis : Disjoint A B)
    (hRect : ∀ S ⊆ A, ∀ T ⊆ B, e < S.card → e < T.card → 0 < incidences D S T) :
    ∃ M : Finset (V × V), 23*m ≤ 50*M.card ∧
      (∀ z ∈ M, z.1 ∈ A ∧ z.2 ∈ B ∧ D.Adj z.1 z.2 ∧ z.1 ≠ z.2) ∧
      Set.InjOn Prod.fst (↑M : Set (V × V)) ∧ Set.InjOn Prod.snd (↑M : Set (V × V)) := by
  obtain ⟨M,hM,hArcs,hLeft,hRight⟩ :=
    exists_physical_matching_of_rectangle_deficit D A B e hSize hDis hRect
  exact ⟨M,by omega,hArcs,hLeft,hRight⟩

/-- Realize every chord request in the physical restricted pairs using
only the rectangle condition and the total incidence bound (8.2). -/
theorem exists_physical_chords_of_restricted_pairs {V I J : Type*}
    [Fintype V] [Fintype J] (D : Digraph V) (cluster : V → I)
    (source target : J → I) (A : I → Finset V) (m e : ℕ)
    (hm : 0 < m) (he : 50*e ≤ m)
    (hSize : ∀ j, (A (source j)).card = (A (target j)).card)
    (h24 : ∀ j, 24*m ≤ 50*(A (source j)).card)
    (hIn : ∀ i x, x ∈ A i → cluster x = i)
    (hApart : ∀ j, Disjoint (A (source j)) (A (target j)))
    (hRect : ∀ j, ∀ S ⊆ A (source j), ∀ T ⊆ A (target j),
      e < S.card → e < T.card → 0 < incidences D S T)
    (hLoad : ∀ i, 100*((univ.filter (fun j => source j = i)).card +
      (univ.filter (fun j => target j = i)).card) ≤ 21*m) :
    ∃ f : J → V × V,
      (∀ j, (f j).1 ∈ A (source j) ∧ (f j).2 ∈ A (target j) ∧
        D.Adj (f j).1 (f j).2 ∧ (f j).1 ≠ (f j).2) ∧
      ∀ j k, j ≠ k →
        (f j).1 ≠ (f k).1 ∧ (f j).1 ≠ (f k).2 ∧
        (f j).2 ≠ (f k).1 ∧ (f j).2 ≠ (f k).2 := by
  have hM (j : J) := exists_chord_candidate_matching D (A (source j)) (A (target j))
    m e (hSize j) (h24 j) he (hApart j) (hRect j)
  choose M hCard hArcs hSource hTarget using hM
  obtain ⟨f,hf,hDis⟩ := exists_disjoint_chords_at_kuhn_osthus_load cluster source target
    M m hm (fun j z hz => ⟨hIn _ _ (hArcs j z hz).1,hIn _ _ (hArcs j z hz).2.1⟩)
    (fun j z hz => (hArcs j z hz).2.2.2) (fun j => ⟨hSource j,hTarget j⟩) hLoad hCard
  exact ⟨f,fun j => hArcs j _ (hf j).1,hDis⟩

/-- The lower half of the paper's relative regularity condition
implies the rectangle hypothesis for the restricted chord pairs. -/
theorem chord_rectangles_of_relative_density {V : Type*} [Fintype V]
    (D : Digraph V) (U W A B : Finset V) (d ε : ℝ) (e : ℕ)
    (hd : 0 < d) (hε : ε < 1) (hA : A ⊆ U) (hB : B ⊆ W)
    (hCutU : ε*(U.card:ℝ) ≤ e + 1) (hCutW : ε*(W.card:ℝ) ≤ e + 1)
    (hRelative : ∀ X ⊆ U, ∀ Y ⊆ W,
      ε*(U.card:ℝ) ≤ X.card → ε*(W.card:ℝ) ≤ Y.card →
      (1-ε)*d ≤ OverfullWork.DirectedRegularPairs.density D X Y) :
    ∀ X ⊆ A, ∀ Y ⊆ B, e < X.card → e < Y.card → 0 < incidences D X Y := by
  intro X hx Y hy hX hY
  have hx' : (e:ℝ)+1 ≤ X.card := by exact_mod_cast (show e+1 ≤ X.card by omega)
  have hy' : (e:ℝ)+1 ≤ Y.card := by exact_mod_cast (show e+1 ≤ Y.card by omega)
  have hLower := hRelative X (hx.trans hA) Y (hy.trans hB) (hCutU.trans hx') (hCutW.trans hy')
  have hPositive := (mul_pos (sub_pos.mpr hε) hd).trans_le hLower
  unfold OverfullWork.DirectedRegularPairs.density at hPositive
  have hDen : (0:ℝ) < (X.card:ℝ)*(Y.card:ℝ) := by
    have : (0:ℝ) < X.card := by linarith
    have : (0:ℝ) < Y.card := by linarith
    positivity
  have hPos := (lt_div_iff₀ hDen).mp hPositive
  simp only [zero_mul] at hPos
  exact_mod_cast hPos

end OverfullWork.DirectedRobustExpansion
