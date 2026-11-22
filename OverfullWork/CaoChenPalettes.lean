module

public import Overfull.KempeTools
public import OverfullWork.CommonMissingColour
public import Mathlib.Data.Real.Basic

@[expose] public section


/-! # The actual colour palettes of Cao--Chen's earlier discharging paper

Low and high colours are defined by existing coloured edges, without
choosing an endpoint function. All thresholds q are real, as in R1.
-/
namespace OverfullWork.CaoChenPalettes
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def presentColours {k : ℕ} (c : PEC G (Fin k)) (v : V) : Finset (Fin k) :=
  univ \ missing c v

noncomputable def lowColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) : Finset (Fin k) :=
  univ.filter fun η => ∃ w, c.col v w = some η ∧ (G.degree w : ℝ) < q

noncomputable def highColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) : Finset (Fin k) :=
  univ.filter fun η => ∃ w, c.col v w = some η ∧ q ≤ (G.degree w : ℝ)

noncomputable def badColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) : Finset (Fin k) :=
  missing c v ∪ lowColours c q v

noncomputable def paletteA {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) : Finset (Fin k) :=
  (presentColours c x ∩ presentColours c y) ∩ lowColours c q y

noncomputable def paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) : Finset (Fin k) :=
  (presentColours c x ∩ presentColours c y) ∩ highColours c q y

noncomputable def paletteS {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) : Finset (Fin k) :=
  (paletteA c q x y ∪ missing c x) ∪ missing c y

noncomputable def neighboursS {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) : Finset V :=
  (G.neighborFinset x).filter fun z => ∃ η ∈ paletteS c q x y, c.col x z = some η

noncomputable def neighboursB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) : Finset V :=
  (G.neighborFinset x).filter fun z => ∃ η ∈ paletteB c q x y, c.col x z = some η

theorem mem_presentColours {k : ℕ} (c : PEC G (Fin k)) (v : V) (η : Fin k) :
    η ∈ presentColours c v ↔ ¬ c.IsFree v η := by
  simp only [presentColours, mem_sdiff, mem_univ, true_and, mem_missing]

theorem mem_lowColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) (η : Fin k) :
    η ∈ lowColours c q v ↔ ∃ w, c.col v w = some η ∧ (G.degree w : ℝ) < q := by
  simp only [lowColours, mem_filter, mem_univ, true_and]

theorem mem_highColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) (η : Fin k) :
    η ∈ highColours c q v ↔ ∃ w, c.col v w = some η ∧ q ≤ (G.degree w : ℝ) := by
  simp only [highColours, mem_filter, mem_univ, true_and]

theorem mem_badColours {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) (η : Fin k) :
    η ∈ badColours c q v ↔ c.IsFree v η ∨ ∃ w, c.col v w = some η ∧ (G.degree w : ℝ) < q := by
  simp only [badColours, mem_union, mem_missing, mem_lowColours]

theorem presentColours_iff_coloured {k : ℕ} (c : PEC G (Fin k)) (v : V) (η : Fin k) :
    η ∈ presentColours c v ↔ ∃ w, c.col v w = some η := by
  rw [mem_presentColours]
  simp only [IsFree, not_forall, not_not]

theorem lowColours_subset_present {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    lowColours c q v ⊆ presentColours c v := by
  intro η hη
  obtain ⟨w, hw, _⟩ := (mem_lowColours c q v η).mp hη
  exact (presentColours_iff_coloured c v η).mpr ⟨w, hw⟩

theorem highColours_subset_present {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    highColours c q v ⊆ presentColours c v := by
  intro η hη
  obtain ⟨w, hw, _⟩ := (mem_highColours c q v η).mp hη
  exact (presentColours_iff_coloured c v η).mpr ⟨w, hw⟩

theorem missing_union_present {k : ℕ} (c : PEC G (Fin k)) (v : V) :
    missing c v ∪ presentColours c v = univ := by
  ext η
  simp [presentColours]

theorem disjoint_missing_present {k : ℕ} (c : PEC G (Fin k)) (v : V) :
    Disjoint (missing c v) (presentColours c v) := by
  exact disjoint_sdiff_self_right

theorem low_high_partition {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    lowColours c q v ∪ highColours c q v = presentColours c v := by
  ext η
  constructor
  · intro h
    rcases mem_union.mp h with hl | hh
    · exact lowColours_subset_present c q v hl
    · exact highColours_subset_present c q v hh
  · intro h
    obtain ⟨w, hw⟩ := (presentColours_iff_coloured c v η).mp h
    by_cases hlow : (G.degree w : ℝ) < q
    · exact mem_union.mpr (Or.inl ((mem_lowColours c q v η).mpr ⟨w, hw, hlow⟩))
    · exact mem_union.mpr (Or.inr ((mem_highColours c q v η).mpr ⟨w, hw, le_of_not_gt hlow⟩))

theorem low_high_disjoint {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    Disjoint (lowColours c q v) (highColours c q v) := by
  apply Finset.disjoint_left.mpr
  intro η hl hh
  obtain ⟨w, hw, hlow⟩ := (mem_lowColours c q v η).mp hl
  obtain ⟨z, hz, hhigh⟩ := (mem_highColours c q v η).mp hh
  have he := c.col_proper hw hz
  subst z
  exact (not_lt_of_ge hhigh) hlow

theorem bad_high_partition {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    badColours c q v ∪ highColours c q v = univ := by
  rw [badColours, union_assoc, low_high_partition, missing_union_present]

theorem bad_high_disjoint {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    Disjoint (badColours c q v) (highColours c q v) := by
  rw [badColours, disjoint_union_left]
  exact ⟨(disjoint_missing_present c v).mono_right (highColours_subset_present c q v), low_high_disjoint c q v⟩

theorem bad_card_add_high_card {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) :
    (badColours c q v).card + (highColours c q v).card = k := by
  rw [← card_union_of_disjoint (bad_high_disjoint c q v), bad_high_partition, card_univ, Fintype.card_fin]

theorem mem_paletteA {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) (η : Fin k) :
    η ∈ paletteA c q x y ↔ η ∈ presentColours c x ∧ ∃ z, c.col y z = some η ∧ (G.degree z : ℝ) < q := by
  simp only [paletteA, mem_inter, mem_lowColours]
  constructor
  · rintro ⟨⟨hx,_⟩, hz⟩; exact ⟨hx,hz⟩
  · rintro ⟨hx,z,hz,hq⟩
    exact ⟨⟨hx,(presentColours_iff_coloured c y η).mpr ⟨z,hz⟩⟩,z,hz,hq⟩

theorem mem_paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) (η : Fin k) :
    η ∈ paletteB c q x y ↔ η ∈ presentColours c x ∧ ∃ z, c.col y z = some η ∧ q ≤ (G.degree z : ℝ) := by
  simp only [paletteB, mem_inter, mem_highColours]
  constructor
  · rintro ⟨⟨hx,_⟩, hz⟩; exact ⟨hx,hz⟩
  · rintro ⟨hx,z,hz,hq⟩
    exact ⟨⟨hx,(presentColours_iff_coloured c y η).mpr ⟨z,hz⟩⟩,z,hz,hq⟩

theorem paletteA_union_paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) :
    paletteA c q x y ∪ paletteB c q x y = presentColours c x ∩ presentColours c y := by
  ext η
  simp only [paletteA,paletteB,mem_union,mem_inter]
  have hp := congrArg (fun T : Finset (Fin k) => η ∈ T) (low_high_partition c q y)
  simp only [mem_union] at hp
  tauto

theorem disjoint_paletteA_paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) :
    Disjoint (paletteA c q x y) (paletteB c q x y) :=
  (low_high_disjoint c q y).mono inter_subset_right inter_subset_right

/-- A useful selector-free form: S is missing(x) union bad(y). -/
theorem mem_paletteS_iff_free_or_bad {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) (η : Fin k) :
    η ∈ paletteS c q x y ↔ c.IsFree x η ∨ η ∈ badColours c q y := by
  simp only [paletteS, mem_union, mem_missing, mem_paletteA, mem_badColours]
  constructor
  · rintro ((⟨hx,hl⟩ | hx) | hy)
    · exact Or.inr (Or.inr hl)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
  · rintro (hx | hy | hl)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hy
    · by_cases hx : c.IsFree x η
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl ⟨(mem_presentColours c x η).mpr hx,hl⟩)

theorem paletteS_union_paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) :
    paletteS c q x y ∪ paletteB c q x y = univ := by
  ext η
  simp only [paletteS,mem_union,mem_univ,mem_missing]
  have hp := congrArg (fun T : Finset (Fin k) => η ∈ T) (paletteA_union_paletteB c q x y)
  simp only [mem_union,mem_inter,mem_presentColours] at hp
  tauto

theorem disjoint_paletteS_paletteB {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) :
    Disjoint (paletteS c q x y) (paletteB c q x y) := by
  rw [paletteS,disjoint_union_left,disjoint_union_left]
  refine ⟨⟨disjoint_paletteA_paletteB c q x y,?_⟩,?_⟩
  · exact (disjoint_missing_present c x).mono_right (fun η hη => (mem_inter.mp (mem_inter.mp hη).1).1)
  · exact (disjoint_missing_present c y).mono_right (fun η hη => (mem_inter.mp (mem_inter.mp hη).1).2)

theorem paletteS_card_add_paletteB_card {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (x y : V) :
    (paletteS c q x y).card + (paletteB c q x y).card = k := by
  rw [← card_union_of_disjoint (disjoint_paletteS_paletteB c q x y), paletteS_union_paletteB,
    card_univ, Fintype.card_fin]

theorem paletteS_inter_present_left (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y) (q : ℝ) :
    paletteS c q x y ∩ presentColours c x = paletteA c q x y ∪ missing c y := by
  ext η
  have hd := (hcm.ab_facts hG).1
  simp only [paletteS,mem_inter,mem_union,mem_missing,mem_presentColours]
  have hA : η ∈ paletteA c q x y → ¬c.IsFree x η := fun h =>
    (mem_presentColours c x η).mp ((mem_paletteA c q x y η).mp h).1
  constructor
  · rintro ⟨(ha | hx) | hy,hpx⟩
    · exact Or.inl ha
    · exact False.elim (hpx hx)
    · exact Or.inr hy
  · rintro (ha | hy)
    · exact ⟨Or.inl (Or.inl ha),hA ha⟩
    · exact ⟨Or.inr hy,fun hx => hd η hx hy⟩

end OverfullWork.CaoChenPalettes
