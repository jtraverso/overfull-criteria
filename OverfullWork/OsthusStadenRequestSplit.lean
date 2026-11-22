module

public import OverfullWork.OsthusStadenH1RedProfiles
public import OverfullWork.DirectedMultiwaySplit

@[expose] public section


/-! The bounded-overlap edge allocation of Claim 5.4. Split separately
on the finitely many request sets of an arc, so that the same uniform
edge-sampling theorem supplies both endpoint estimates. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u v

def requestedArcs {V J : Type*} (D : Digraph V) (allowed : V → V → Finset J) (j : J) :
    Digraph V :=
  ⟨fun x y => D.Adj x y ∧ j ∈ allowed x y⟩

/-- An arc is available to at most `k` requests. All requests receive
one `k`th of their available arcs up to additive semidegree error, and
the allocated subgraphs are mutually edge-disjoint. -/
theorem exists_bounded_request_arc_split (J : Type v) [Fintype J]
    (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (allowed : V → V → Finset J),
      N ≤ Fintype.card V → (∀ x y, D.Adj x y → (allowed x y).card ≤ k) →
      ∃ F : J → Digraph V,
        (∀ j, F j ≤ requestedArcs D allowed j) ∧
        (∀ j l, j ≠ l → Disjoint (F j) (F l)) ∧
        ∀ j s x, |(pairSemidegree s (F j) x : ℝ) -
          (pairSemidegree s (requestedArcs D allowed j) x : ℝ)/(k:ℝ)| ≤
            η*(Fintype.card V:ℝ) := by
  classical
  let G := {S : Finset J // S.card ≤ k}
  letI : Nonempty G := ⟨⟨∅,by simp⟩⟩
  have hG : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  let ζ := η/((Fintype.card G:ℝ)*(k:ℝ))
  have hζ : 0 < ζ := div_pos hη (mul_pos hG hkR)
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} ζ hζ
  refine ⟨N,?_⟩
  intro V _ D allowed hn hAllowed
  let A (g : G) : Digraph V := ⟨fun x y => D.Adj x y ∧ allowed x y = g.val⟩
  let code (g : G) : g.val ↪ Fin k :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe g.val)).toEmbedding.trans (Fin.castLEEmb g.property)
  choose part residue hPart hRes hDis hRDis hCover using fun g =>
    hN k (1/(k:ℝ)) (one_div_pos.mpr hkR) (by rw [mul_one_div_cancel hkR.ne']) (A g) hn
  have hLe (g : G) (c : Fin k) : part g c ≤ A g :=
    fun x y h => (hCover g x y).mpr (Or.inr ⟨c,h⟩)
  have hA (g f : G) (h : g ≠ f) : Disjoint (A g) (A f) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨_,hg⟩,⟨_,hf⟩⟩
    exact h (Subtype.ext (hg.symm.trans hf))
  let original (j : J) (g : G) : Digraph V := if j ∈ g.val then A g else ⊥
  let picked (j : J) (g : G) : Digraph V :=
    if h : j ∈ g.val then part g (code g ⟨j,h⟩) else ⊥
  have hPicked (j : J) (g : G) : picked j g ≤ original j g := by
    by_cases h : j ∈ g.val
    · simpa [picked,original,h] using hLe g (code g ⟨j,h⟩)
    · simp [picked,original,h]
  have hOriginal (j : J) (g : G) : original j g ≤ A g := by
    by_cases h : j ∈ g.val <;> simp [original,h]
  have hUnion (j : J) : indexedArcUnion univ (original j) = requestedArcs D allowed j := by
    ext x y
    constructor
    · rintro ⟨g,_,hg⟩
      by_cases hj : j ∈ g.val
      · have he : D.Adj x y ∧ allowed x y = g.val := by simpa [original,hj,A] using hg
        exact ⟨he.1,he.2.symm ▸ hj⟩
      · simpa [original,hj,Digraph.bot_adj] using hg
    · rintro ⟨h,hj⟩
      let g : G := ⟨allowed x y,hAllowed x y h⟩
      exact ⟨g,mem_univ _,by
        have hg : j ∈ g.val := hj
        simpa [original,hg,A,g] using h⟩
  let F (j : J) := indexedArcUnion (univ : Finset G) (picked j)
  refine ⟨F,?_,?_,?_⟩
  · intro j
    rw [← hUnion]
    rintro x y ⟨g,hg,h⟩
    exact ⟨g,hg,hPicked j g h⟩
  · intro j l hjl
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨g,_,hg⟩,⟨f,_,hf⟩⟩
    by_cases he : g = f
    · subst f
      by_cases hj : j ∈ g.val
      · by_cases hl : l ∈ g.val
        · have hc : code g ⟨j,hj⟩ ≠ code g ⟨l,hl⟩ :=
            fun h => hjl (congrArg Subtype.val ((code g).injective h))
          exact disjoint_iff_inf_le.mp (hDis g _ _ hc)
            ⟨by simpa [picked,hj] using hg,by simpa [picked,hl] using hf⟩
        · simpa [picked,hl,Digraph.bot_adj] using hf
      · simpa [picked,hj,Digraph.bot_adj] using hg
    · exact disjoint_iff_inf_le.mp (hA g f he)
        ⟨hOriginal j g (hPicked j g hg),hOriginal l f (hPicked l f hf)⟩
  · intro j s x
    have hSum (D : G → Digraph V) (hh : ∀ g, D g ≤ A g) :
        pairSemidegree s (indexedArcUnion univ D) x = ∑ g,pairSemidegree s (D g) x := by
      have h := indexedArcUnion_semidegrees (univ : Finset G) D
        (fun g _ f _ h => (hA g f h).mono (hh g) (hh f)) x
      cases s
      · exact h.2
      · exact h.1
    have hOne (g : G) : |(pairSemidegree s (picked j g) x:ℝ) -
        (pairSemidegree s (original j g) x:ℝ)/(k:ℝ)| ≤ (k:ℝ)*ζ*(Fintype.card V:ℝ) := by
      by_cases hj : j ∈ g.val
      · rw [show picked j g = part g (code g ⟨j,hj⟩) by simp [picked,hj],
          show original j g = A g by simp [original,hj]]
        cases s
        · simpa only [pairSemidegree,if_neg Bool.false_ne_true,ArcStatistic.value,ArcStatistic.scale,
            one_div,mul_comm ((k:ℝ)⁻¹),←div_eq_mul_inv]
            using hPart g (code g ⟨j,hj⟩) (.inl x)
        · simpa only [pairSemidegree,if_true,ArcStatistic.value,ArcStatistic.scale,
            one_div,mul_comm ((k:ℝ)⁻¹),←div_eq_mul_inv]
            using hPart g (code g ⟨j,hj⟩) (.inr (.inl x))
      · have hn : 0 ≤ (k:ℝ)*ζ*(Fintype.card V:ℝ) := by positivity
        cases s <;> simp [picked,original,hj,pairSemidegree,outDegree,inDegree,inNeighbours,
          Digraph.bot_adj,hn]
    change |(pairSemidegree s (indexedArcUnion univ (picked j)) x:ℝ) -
      (pairSemidegree s (requestedArcs D allowed j) x:ℝ)/(k:ℝ)| ≤ _
    rw [←hUnion j,hSum (picked j) (fun g => (hPicked j g).trans (hOriginal j g)),
      hSum (original j) (hOriginal j),Nat.cast_sum,Nat.cast_sum,div_eq_mul_inv,Finset.sum_mul,←sum_sub_distrib]
    simp only [←div_eq_mul_inv]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (fun g _ => hOne g)).trans
    simp only [sum_const, card_univ, nsmul_eq_mul]
    dsimp [ζ]
    field_simp
    exact le_rfl

/-- The two endpoint bounds of Claim 5.4 for one orientation.
The overlap budget counts how often a vertex is exceptional. The
incoming and outgoing applications can use disjoint H1 reserves. -/
theorem exists_special_exception_arc_split (J : Type v) [Fintype J]
    (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (s : Bool)
      (exceptional red : J → Finset V) (κ cap : ℝ), N ≤ Fintype.card V →
      (∀ x, ((univ : Finset J).filter (fun j => x ∈ exceptional j)).card ≤ k) →
      (∀ j x, x ∈ exceptional j →
        let P := if s then outProfile D x else inProfile D x
        κ+η*(Fintype.card V:ℝ) ≤ profileCount (red j) P/(k:ℝ)) →
      (∀ j, ((exceptional j).card:ℝ)/(k:ℝ)+η*(Fintype.card V:ℝ) ≤ cap) →
      ∃ F : J → Digraph V,
        (∀ j x y, (F j).Adj x y → D.Adj x y ∧
          if s then x ∈ exceptional j ∧ y ∈ red j else y ∈ exceptional j ∧ x ∈ red j) ∧
        (∀ j l, j ≠ l → Disjoint (F j) (F l)) ∧
        (∀ j x, x ∈ exceptional j → κ ≤ (pairSemidegree s (F j) x:ℝ)) ∧
        ∀ j y, (pairSemidegree (!s) (F j) y:ℝ) ≤ cap := by
  obtain ⟨N,hN⟩ := exists_bounded_request_arc_split.{u,v} J η hη k hk
  refine ⟨N,?_⟩
  intro V _ D s exceptional red κ cap hn hOcc hLower hUpper
  let allowed (x y : V) := (univ : Finset J).filter (fun j =>
    if s then x ∈ exceptional j ∧ y ∈ red j else y ∈ exceptional j ∧ x ∈ red j)
  have hAllow (x y : V) (j : J) : j ∈ allowed x y ↔
      if s then x ∈ exceptional j ∧ y ∈ red j else y ∈ exceptional j ∧ x ∈ red j := by
    simp [allowed]
  have hCount (x y : V) : (allowed x y).card ≤ k := by
    cases s
    · refine (card_le_card (t := univ.filter (fun j => y ∈ exceptional j)) ?_).trans (hOcc y)
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,((hAllow x y j).mp hj).1⟩
    · refine (card_le_card (t := univ.filter (fun j => x ∈ exceptional j)) ?_).trans (hOcc x)
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,((hAllow x y j).mp hj).1⟩
  obtain ⟨F,hF,hDis,hApprox⟩ := hN D allowed hn (fun x y _ => hCount x y)
  have hDegrees (j : J) (x : V) (hx : x ∈ exceptional j) :
      (pairSemidegree s (requestedArcs D allowed j) x:ℝ) =
        profileCount (red j) (if s then outProfile D x else inProfile D x) := by
    cases s
    · change (((univ : Finset V).filter (fun y => (requestedArcs D allowed j).Adj y x)).card:ℝ) =
        profileCount (red j) (inProfile D x)
      unfold profileCount
      congr 1
      apply congrArg Finset.card
      ext y
      simpa [inProfile,requestedArcs,hAllow,hx,and_comm]
    · change (((univ : Finset V).filter ((requestedArcs D allowed j).Adj x)).card:ℝ) =
        profileCount (red j) (outProfile D x)
      unfold profileCount
      congr 1
      apply congrArg Finset.card
      ext y
      simpa [outProfile,requestedArcs,hAllow,hx,and_comm]
  have hCap (j : J) (y : V) :
      pairSemidegree (!s) (requestedArcs D allowed j) y ≤ (exceptional j).card := by
    cases s
    · change ((univ : Finset V).filter ((requestedArcs D allowed j).Adj y)).card ≤ _
      apply card_le_card
      intro x hx
      have h := (mem_filter.mp hx).2
      exact ((hAllow y x j).mp h.2).1
    · change ((univ : Finset V).filter (fun x => (requestedArcs D allowed j).Adj x y)).card ≤ _
      apply card_le_card
      intro x hx
      have h := (mem_filter.mp hx).2
      exact ((hAllow x y j).mp h.2).1
  refine ⟨F,fun j x y h => ⟨(hF j h).1,(hAllow x y j).mp (hF j h).2⟩,hDis,?_,?_⟩
  · intro j x hx
    have ha := (abs_le.mp (hApprox j s x)).1
    rw [hDegrees j x hx] at ha
    have hb := hLower j x hx
    linarith only [ha,hb]
  · intro j y
    have ha := (abs_le.mp (hApprox j (!s) y)).2
    have hb : (pairSemidegree (!s) (requestedArcs D allowed j) y:ℝ) ≤ (exceptional j).card :=
      by exact_mod_cast hCap j y
    have hc := div_le_div_of_nonneg_right hb (Nat.cast_nonneg k : (0:ℝ) ≤ _)
    linarith only [ha,hc,hUpper j]

/-- The overlap count for Claim 5.4. Each affected original type
contributes at most all its refined slices, and the compensation
deletions may add at most one extra slice per vertex. -/
theorem exceptional_slice_occurrences_le {T A B : Type*} [Fintype A] [Fintype B]
    (types : Finset T) (compensating exceptional : Finset (T × A × B))
    (hComp : compensating.card ≤ 1)
    (hSub : ∀ j ∈ exceptional, j.1 ∈ types ∨ j ∈ compensating) :
    exceptional.card ≤ types.card*(Fintype.card A*Fintype.card B)+1 := by
  let inherited := types ×ˢ ((univ : Finset A) ×ˢ (univ : Finset B))
  have hContain : exceptional ⊆ inherited ∪ compensating := by
    intro j hj
    rcases hSub j hj with h | h
    · exact mem_union_left _ (mem_product.mpr ⟨h,mem_product.mpr ⟨mem_univ _,mem_univ _⟩⟩)
    · exact mem_union_right _ h
  have h := (card_le_card hContain).trans (card_union_le inherited compensating)
  have hCard : inherited.card = types.card*(Fintype.card A*Fintype.card B) := by
    simp [inherited,card_product]
  rw [hCard] at h
  exact h.trans (Nat.add_le_add_left hComp _)

end OverfullWork.DirectedRobustExpansion
