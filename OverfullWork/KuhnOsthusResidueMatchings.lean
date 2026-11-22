module

public import OverfullWork.KuhnOsthusBalancedChordExtension

@[expose] public section


/-! Split the arcs of a 1-factor into the small monochromatic pieces
of Kühn–Osthus Lemma 8.7. Each label records the size bin, a matching
color, and the unordered pair of intervals containing the endpoints. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The arcs of a loopless permutation admit a three-coloring in
which consecutive arcs always have different colors. -/
theorem exists_factor_arc_three_coloring (σ : Equiv.Perm V) (hFixed : ∀ x, σ x ≠ x) :
    ∃ color : V → Fin 3, ∀ x, color x ≠ color (σ x) := by
  have step (S : Finset V) :
      ∃ color : V → Fin 3, ∀ x ∈ S, σ x ∈ S → color x ≠ color (σ x) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0,fun x hx => (notMem_empty x hx).elim⟩
    | @insert v S hv ih =>
      obtain ⟨f,hf⟩ := ih
      let used : Finset (Fin 3) := {f (σ v),f (σ.symm v)}
      have hUsed : used ≠ univ := by
        intro he
        have h : used.card ≤ 2 := by
          exact (card_insert_le _ _).trans (by simp)
        rw [he,card_univ,Fintype.card_fin] at h
        omega
      obtain ⟨c,hc⟩ : ∃ c, c ∉ used := by
        by_contra! h
        exact hUsed (eq_univ_iff_forall.mpr h)
      have h₁ : c ≠ f (σ v) := fun h => hc (h.symm ▸ mem_insert_self _ _)
      have h₂ : c ≠ f (σ.symm v) := fun h => hc (mem_insert_of_mem (mem_singleton.mpr h))
      refine ⟨Function.update f v c,?_⟩
      intro x hx hσx
      by_cases h : x = v
      · subst x
        simpa only [Function.update_self,Function.update_of_ne (hFixed v)] using h₁
      by_cases hy : σ x = v
      · have hEq : x = σ.symm v := σ.eq_symm_apply.mpr hy
        rw [hy,Function.update_self,Function.update_of_ne h,hEq]
        exact h₂.symm
      · rw [Function.update_of_ne h,Function.update_of_ne hy]
        exact hf x ((mem_insert.mp hx).resolve_left h) ((mem_insert.mp hσx).resolve_left hy)
  obtain ⟨f,hf⟩ := step univ
  exact ⟨f,fun x => hf x (mem_univ _) (mem_univ _)⟩

/-- Assign each element to one of the equally sized bins, allowing
empty bins and the usual integer rounding through the capacity. -/
theorem exists_residue_size_bins (b m : ℕ) (hb : 0 < b) (h : Fintype.card V ≤ b*m) :
    ∃ f : V → Fin b, ∀ j, ((univ : Finset V).filter (fun v => f v = j)).card ≤ m := by
  let e := Fintype.equivFin V
  let f (v : V) : Fin b := ⟨(e v).val % b,Nat.mod_lt _ hb⟩
  refine ⟨f,?_⟩
  intro j
  let T := (univ : Finset V).filter (fun v => f v = j)
  let q (v : V) := (e v).val / b
  have hq (v : V) : q v < m := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    rw [Nat.mul_comm]
    exact (e v).isLt.trans_le h
  have hCard : T.card ≤ (range m).card := by
    apply card_le_card_of_injOn q (fun v _ => mem_range.mpr (hq v))
    intro v hv w hw hEq
    have hmod : (e v).val % b = (e w).val % b := congrArg Fin.val
      (((mem_filter.mp hv).2).trans ((mem_filter.mp hw).2).symm)
    have h₁ := Nat.mod_add_div (e v).val b
    have h₂ := Nat.mod_add_div (e w).val b
    change (e v).val / b = (e w).val / b at hEq
    rw [hmod,hEq] at h₁
    exact e.injective (Fin.ext (h₁.symm.trans h₂))
  simpa only [card_range] using hCard

/-- Unordered pairs of different intervals. An arc whose endpoints
lie in one interval can be assigned any pair containing it. -/
abbrev ResidueDoubleType (g : ℕ) :=
  ↥((univ : Finset (Fin g)).powersetCard 2)

theorem card_residue_double_type (g : ℕ) : Fintype.card (ResidueDoubleType g) = g.choose 2 := by
  rw [Fintype.card_coe,card_powersetCard,card_univ,Fintype.card_fin]

theorem exists_residue_double_type (g : ℕ) (hg : 2 ≤ g) (i j : Fin g) :
    ∃ u : ResidueDoubleType g, i ∈ u.val ∧ j ∈ u.val := by
  have mk (x y : Fin g) (h : x ≠ y) : ({x,y} : Finset (Fin g)) ∈
      (univ : Finset (Fin g)).powersetCard 2 := by
    apply mem_powersetCard.mpr
    exact ⟨subset_univ _,by simp [h]⟩
  by_cases h : i = j
  · let x : Fin g := ⟨0,by omega⟩
    let y : Fin g := ⟨1,by omega⟩
    by_cases h₀ : i = x
    · subst j
      have hn : i ≠ y := fun he => by
        have hh := congrArg Fin.val (h₀.symm.trans he)
        simp [x,y] at hh
      exact ⟨⟨{i,y},mk i y hn⟩,mem_insert_self _ _,mem_insert_self _ _⟩
    · subst j
      exact ⟨⟨{i,x},mk i x h₀⟩,mem_insert_self _ _,mem_insert_self _ _⟩
  · exact ⟨⟨{i,j},mk i j h⟩,mem_insert_self _ _,mem_insert_of_mem (mem_singleton_self _)⟩

/-- Each matching has at most one bin's worth of arcs, and every
arc receives its own unique batch label. -/
theorem exists_residue_matching_labels (σ : Equiv.Perm V) (hFixed : ∀ x, σ x ≠ x)
    (g b m : ℕ) (hg : 2 ≤ g) (hb : 0 < b) (hSize : Fintype.card V ≤ b*m)
    (interval : V → Fin g) :
    ∃ tag : V → Fin b × Fin 3 × ResidueDoubleType g,
      (∀ x, interval x ∈ (tag x).2.2.val ∧ interval (σ x) ∈ (tag x).2.2.val) ∧
      (∀ i, ((univ : Finset V).filter (fun x => tag x = i)).card ≤ m) ∧
      ∀ x, tag x ≠ tag (σ x) := by
  obtain ⟨sizeBin,hBin⟩ := exists_residue_size_bins b m hb hSize
  obtain ⟨color,hColor⟩ := exists_factor_arc_three_coloring σ hFixed
  choose type hType using fun x => exists_residue_double_type g hg (interval x) (interval (σ x))
  let tag (x : V) := (sizeBin x,color x,type x)
  refine ⟨tag,hType,?_,?_⟩
  · intro i
    refine (card_le_card (t := univ.filter (fun x => sizeBin x = i.1)) ?_).trans (hBin i.1)
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,congrArg Prod.fst (mem_filter.mp hx).2⟩
  · intro x he
    exact hColor x (congrArg (fun p : Fin b × Fin 3 × ResidueDoubleType g => p.2.1) he)

omit [Fintype V] in
/-- The graph on arcs of a single batch is a matching, represented as
an acyclic digraph with no adjacent pair of arcs. -/
theorem residue_matching_of_label {B : Type*} (σ : Equiv.Perm V) (tag : V → B)
    (hColor : ∀ x, tag x ≠ tag (σ x)) (j : B) :
    let D : Digraph V := ⟨fun x y => tag x = j ∧ σ x = y⟩
    IsDirectedPathSystem D ∧ ∀ x y z, D.Adj x y → ¬ D.Adj y z := by
  intro D
  have hNo (x y z : V) (hxy : D.Adj x y) (hyz : D.Adj y z) : False :=
    hColor x (hxy.2.symm ▸ hxy.1.trans hyz.1.symm)
  have single {x y : V} (h : Relation.TransGen D.Adj x y) : D.Adj x y := by
    induction h with
    | single h => exact h
    | tail _ h ih => exact (hNo _ _ _ ih h).elim
  refine ⟨⟨fun x h => hNo x x x (single h) (single h),?_,?_⟩,hNo⟩
  · intro x y z hy hz
    exact hy.2.symm.trans hz.2
  · intro x y z hy hz
    exact σ.injective (hy.2.trans hz.2.symm)

end OverfullWork.DirectedRobustExpansion
