module

public import OverfullWork.ChenShanPaletteCopyBalance
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {D V : Type*}

/-- A core copy uses at least one core vertex and all of its core
endpoints belong to the assigned block. -/
def CopyInCoreBlock (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (d : D) : Prop :=
  ((role (ends d).1).isCore ∨ (role (ends d).2).isCore) ∧
    ((role (ends d).1).isCore → (ends d).1 ∈ block) ∧
    ((role (ends d).2).isCore → (ends d).2 ∈ block)

private theorem copy_in_unique_exceptional_row (ends : D → V × V)
    (role : V → PaletteVertexRole) (v w : V)
    (_hv : (role v).isCore = false) (hw : (role w).isCore = false)
    (d : D) :
    (((ends d).1 = v ∧ (role (ends d).2).isCore) ∨
      ((ends d).2 = v ∧ (role (ends d).1).isCore)) →
    (((ends d).1 = w ∧ (role (ends d).2).isCore) ∨
      ((ends d).2 = w ∧ (role (ends d).1).isCore)) → v = w := by
  rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) (⟨h₃,h₄⟩ | ⟨h₃,h₄⟩)
  · exact h₁.symm.trans h₃
  · rw [h₃,hw] at h₂
    contradiction
  · rw [h₃,hw] at h₂
    contradiction
  · exact h₁.symm.trans h₃

private theorem no_core_has_zero_correction (u v : PaletteVertexRole) :
    u.isCore = false → v.isCore = false →
      u.plus v = false ∧ u.minus v = false ∧ u.isLowCore v = false := by
  cases u <;> cases v <;> decide

private theorem nonzero_preferredSign_is_exceptional (u : PaletteVertexRole) :
    u.preferredSign ≠ 0 → u.isCore = false := by
  cases u <;> decide

/-- Construct the selected copies for one palette in §5.1.4. The
correction copies have already been drawn from the capacity pools.
Fill each exceptional row from its remaining preferred copies, and
retain the original exceptional-to-exceptional edges. -/
theorem exists_balanced_palette_selection_of_corrections [Fintype V]
    (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (original available correction : Finset D) (pool : V → Finset D)
    (hOld : paletteCopyCoreGap ends role original = 0)
    (hOldLow : ∀ d ∈ original, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hKAvail : correction ⊆ available)
    (hKBlock : ∀ d ∈ correction, CopyInCoreBlock ends role block d)
    (hKLow : ∀ d ∈ correction, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hKGap :
      ((palettePlusCopies ends role correction).card:ℤ)-((paletteMinusCopies ends role correction).card:ℤ) =
      ((palettePlusCopies ends role original).card:ℤ)-((paletteMinusCopies ends role original).card:ℤ))
    (hCap : ∀ v, (role v).isCore = false →
      (paletteCoreRow ends role correction v).card ≤ (paletteCoreRow ends role original v).card)
    (hPool : ∀ v, (role v).isCore = false →
      (paletteCoreRow ends role original v).card ≤ (pool v).card)
    (hPoolAvail : ∀ v, (role v).isCore = false → pool v ⊆ available)
    (hPoolBlock : ∀ v, (role v).isCore = false → ∀ d ∈ pool v,
      CopyInCoreBlock ends role block d)
    (hPoolRow : ∀ v, (role v).isCore = false → pool v ⊆ paletteCoreRow ends role (pool v) v)
    (hPoolNeutral : ∀ v, (role v).isCore = false → ∀ d ∈ pool v,
      (role (ends d).1).plus (role (ends d).2) = false ∧
      (role (ends d).1).minus (role (ends d).2) = false ∧
      (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hPoolDisj : ∀ v, (role v).isCore = false → Disjoint correction (pool v)) :
    ∃ core : Finset D, correction ⊆ core ∧ core ⊆ available ∧
      (∀ d ∈ core, CopyInCoreBlock ends role block d) ∧
      let selected := paletteExceptionalCopies ends role original ∪ core
      paletteCopyCoreGap ends role selected = 0 ∧
      (∀ v, (role v).isCore = false →
        paletteCopyDegree ends selected v = paletteCopyDegree ends original v) ∧
      palettePlusCopies ends role core = palettePlusCopies ends role correction ∧
      paletteMinusCopies ends role core = paletteMinusCopies ends role correction := by
  classical
  let Z := (univ : Finset V).filter (fun v => (role v).isCore = false)
  have hZ (v : V) : v ∈ Z ↔ (role v).isCore = false := by simp [Z]
  have hChoose (v : ↥Z) : ∃ S ⊆ pool v.val,
      Disjoint (paletteCoreRow ends role correction v.val) S ∧
      ((paletteCoreRow ends role correction v.val) ∪ S).card =
        (paletteCoreRow ends role original v.val).card :=
    exists_preferred_copies_completing_row _ _ _
      ((hPoolDisj v.val ((hZ _).mp v.property)).mono (filter_subset _ _) Subset.rfl)
      (hCap v.val ((hZ _).mp v.property)) (hPool v.val ((hZ _).mp v.property))
  choose pick hPick hPickDisj hPickSize using hChoose
  let P := (univ : Finset ↥Z).biUnion pick
  let core := correction ∪ P
  let exceptional := paletteExceptionalCopies ends role original
  let selected := exceptional ∪ core
  have hPX (d : D) (hd : d ∈ P) :
      ∃ v, (role v).isCore = false ∧ d ∈ pool v ∧
        d ∈ paletteCoreRow ends role (pool v) v := by
    obtain ⟨v,_,hv⟩ := mem_biUnion.mp hd
    have h := (hZ _).mp v.property
    exact ⟨v.val,h,hPick v hv,hPoolRow v.val h (hPick v hv)⟩
  have hN (d : D) (hd : d ∈ exceptional) :
      (role (ends d).1).isCore = false ∧ (role (ends d).2).isCore = false := by
    simpa [exceptional, paletteExceptionalCopies] using (mem_filter.mp hd).2
  have hCore (d : D) (hd : d ∈ core) : CopyInCoreBlock ends role block d := by
    rcases mem_union.mp hd with h | h
    · exact hKBlock d h
    · obtain ⟨v,hv,hd,_⟩ := hPX d h
      exact hPoolBlock v hv d hd
  have hAvail : core ⊆ available := by
    intro d hd
    rcases mem_union.mp hd with h | h
    · exact hKAvail h
    · obtain ⟨v,hv,hd,_⟩ := hPX d h
      exact hPoolAvail v hv hd
  have hInternal : paletteExceptionalCopies ends role selected = exceptional := by
    ext d
    constructor
    · intro hd
      rcases mem_union.mp (mem_filter.mp hd).1 with he | hc
      · exact he
      · have hNon : (role (ends d).1).isCore = false ∧ (role (ends d).2).isCore = false := by
          simpa using (mem_filter.mp hd).2
        have h := (hCore d hc).1
        simp [hNon.1,hNon.2] at h
    · intro hd
      exact mem_filter.mpr ⟨mem_union_left _ hd,by simp [(hN d hd).1,(hN d hd).2]⟩
  have hRows (v : V) (hv : (role v).isCore = false) :
      (paletteCoreRow ends role selected v).card = (paletteCoreRow ends role original v).card := by
    let z : ↥Z := ⟨v,(hZ v).mpr hv⟩
    have hSet : paletteCoreRow ends role selected v =
        (paletteCoreRow ends role correction v) ∪ pick z := by
      ext d
      constructor
      · intro hd
        have hr := (mem_filter.mp hd).2
        rcases mem_union.mp (mem_filter.mp hd).1 with he | hc
        · simp [(hN d he).1,(hN d he).2] at hr
        · rcases mem_union.mp hc with hk | hP
          · exact mem_union_left _ (mem_filter.mpr ⟨hk,hr⟩)
          · obtain ⟨y,_,hy⟩ := mem_biUnion.mp hP
            have hy' := (hZ _).mp y.property
            have hY := (mem_filter.mp (hPoolRow y.val hy' (hPick y hy))).2
            have hyv : y = z := Subtype.ext
              (copy_in_unique_exceptional_row ends role y.val v hy' hv d hY hr)
            exact mem_union_right _ (hyv ▸ hy)
      · intro hd
        rcases mem_union.mp hd with hk | hP
        · obtain ⟨hK,hr⟩ := mem_filter.mp hk
          exact mem_filter.mpr ⟨mem_union_right _ (mem_union_left _ hK),hr⟩
        · have hr := (mem_filter.mp (hPoolRow v hv (hPick z hP))).2
          have hP' : d ∈ P := mem_biUnion.mpr ⟨z,mem_univ _,hP⟩
          exact mem_filter.mpr ⟨mem_union_right _ (mem_union_right _ hP'),hr⟩
    rw [hSet]
    exact hPickSize z
  have hNeutral (d : D) (hd : d ∈ exceptional ∪ P) :
      (role (ends d).1).plus (role (ends d).2) = false ∧
      (role (ends d).1).minus (role (ends d).2) = false ∧
      (role (ends d).1).isLowCore (role (ends d).2) = false := by
    rcases mem_union.mp hd with he | he
    · exact no_core_has_zero_correction _ _ (hN d he).1 (hN d he).2
    · obtain ⟨v,hv,he,_⟩ := hPX d he
      exact hPoolNeutral v hv d he
  have hExt (test : D → Bool) (ht : ∀ d ∈ exceptional ∪ P, test d = false) :
      selected.filter (fun d => test d) = correction.filter (fun d => test d) ∧
        core.filter (fun d => test d) = correction.filter (fun d => test d) := by
    constructor <;> ext d <;> simp only [selected,core,mem_filter,mem_union]
    · constructor
      · rintro ⟨he | hk | hp, h⟩
        · simp [ht d (mem_union_left _ he)] at h
        · exact ⟨hk,h⟩
        · simp [ht d (mem_union_right _ hp)] at h
      · exact fun ⟨hk,h⟩ => ⟨Or.inr (Or.inl hk),h⟩
    · constructor
      · rintro ⟨hk | hp,h⟩
        · exact ⟨hk,h⟩
        · simp [ht d (mem_union_right _ hp)] at h
      · exact fun ⟨hk,h⟩ => ⟨Or.inl hk,h⟩
  have hPlus := hExt (fun d => (role (ends d).1).plus (role (ends d).2)) (fun d h => (hNeutral d h).1)
  have hMinus := hExt (fun d => (role (ends d).1).minus (role (ends d).2))
    (fun d h => (hNeutral d h).2.1)
  have hLow (d : D) (hd : d ∈ selected) :
      (role (ends d).1).isLowCore (role (ends d).2) = false := by
    rcases mem_union.mp hd with h | h
    · exact (hNeutral d (mem_union_left _ h)).2.2
    · rcases mem_union.mp h with h | h
      · exact hKLow d h
      · exact (hNeutral d (mem_union_right _ h)).2.2
  refine ⟨core,subset_union_left,hAvail,hCore,?_,?_,hPlus.2,hMinus.2⟩
  · apply palette_selection_balanced_of_rows_and_corrections ends role original selected
      hOldLow hLow hOld (fun v hv => hRows v (nonzero_preferredSign_is_exceptional _ hv))
    unfold palettePlusCopies paletteMinusCopies at hKGap ⊢
    rw [hPlus.1,hMinus.1]
    exact hKGap
  · exact paletteCopyDegree_preserved_at_exceptionals ends role original selected hInternal hRows


/-- The requirements on correction copies and on the preferred copies
available to one block, before filling its exceptional rows. -/
structure PaletteBlockSelectionInput (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (original available : Finset D) where
  correction : Finset D
  pool : V → Finset D
  correction_available : correction ⊆ available
  correction_in_block : ∀ d ∈ correction, CopyInCoreBlock ends role block d
  correction_no_low : ∀ d ∈ correction, (role (ends d).1).isLowCore (role (ends d).2) = false
  plus_size : (palettePlusCopies ends role correction).card =
    (palettePlusCopies ends role original).card-(paletteMinusCopies ends role original).card
  minus_size : (paletteMinusCopies ends role correction).card =
    (paletteMinusCopies ends role original).card-(palettePlusCopies ends role original).card
  cap : ∀ v, (role v).isCore = false →
    (paletteCoreRow ends role correction v).card ≤ (paletteCoreRow ends role original v).card
  enough_preferred : ∀ v, (role v).isCore = false →
    (paletteCoreRow ends role original v).card ≤ (pool v).card
  preferred_available : ∀ v, (role v).isCore = false → pool v ⊆ available
  preferred_in_block : ∀ v, (role v).isCore = false → ∀ d ∈ pool v, CopyInCoreBlock ends role block d
  preferred_in_row : ∀ v, (role v).isCore = false → pool v ⊆ paletteCoreRow ends role (pool v) v
  preferred_neutral : ∀ v, (role v).isCore = false → ∀ d ∈ pool v,
    (role (ends d).1).plus (role (ends d).2) = false ∧
    (role (ends d).1).minus (role (ends d).2) = false ∧
    (role (ends d).1).isLowCore (role (ends d).2) = false
  preferred_disjoint : ∀ v, (role v).isCore = false → Disjoint correction (pool v)

/-- The core copies of the completed palette, together with the facts
needed to pass from fine to coarse blocks. -/
structure IsPaletteBlockSelection (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (original available core : Finset D) : Prop where
  available_copies : core ⊆ available
  in_block : ∀ d ∈ core, CopyInCoreBlock ends role block d
  balanced : paletteCopyCoreGap ends role (paletteExceptionalCopies ends role original ∪ core) = 0
  degree : ∀ v, (role v).isCore = false →
    paletteCopyDegree ends (paletteExceptionalCopies ends role original ∪ core) v =
      paletteCopyDegree ends original v
  plus_size : (palettePlusCopies ends role core).card =
    (palettePlusCopies ends role original).card-(paletteMinusCopies ends role original).card
  minus_size : (paletteMinusCopies ends role core).card =
    (paletteMinusCopies ends role original).card-(palettePlusCopies ends role original).card

theorem PaletteBlockSelectionInput.exists_selection [Fintype V]
    {ends : D → V × V} {role : V → PaletteVertexRole}
    {block : Finset V} {original available : Finset D}
    (A : PaletteBlockSelectionInput ends role block original available)
    (hOld : paletteCopyCoreGap ends role original = 0)
    (hLow : ∀ d ∈ original, (role (ends d).1).isLowCore (role (ends d).2) = false) :
    ∃ core, IsPaletteBlockSelection ends role block original available core := by
  have hGap := palette_correction_gap_of_exact_sizes _ _ _ _ A.plus_size A.minus_size
  obtain ⟨S,_,hAvail,hBlock,hBal,hDeg,hPlus,hMinus⟩ :=
    exists_balanced_palette_selection_of_corrections ends role block original available
      A.correction A.pool hOld hLow A.correction_available A.correction_in_block
      A.correction_no_low hGap A.cap A.enough_preferred A.preferred_available
      A.preferred_in_block A.preferred_in_row A.preferred_neutral A.preferred_disjoint
  exact ⟨S,hAvail,hBlock,hBal,hDeg,(congrArg Finset.card hPlus).trans A.plus_size,
    (congrArg Finset.card hMinus).trans A.minus_size⟩

/-- Select all fine blocks first, and choose coarse data only after
deleting the selected fine core copies. At this point both families
are pairwise edge-disjoint, and deleting their union preserves balance
in the remainder. -/
theorem exists_staged_palette_selections {F C K : Type*}
    [Fintype F] [Fintype C] [Fintype D] [Fintype V] [DecidableEq K]
    (ends : D → V × V) (role : V → PaletteVertexRole) (colour : D → K)
    (block : F ⊕ C → Finset V) (palette : F ⊕ C → Finset K) (boundary : Finset D)
    (hFineBlock : Pairwise (fun f g : F => Disjoint (block (.inl f)) (block (.inl g))))
    (hCoarseBlock : Pairwise (fun f g : C => Disjoint (block (.inr f)) (block (.inr g))))
    (hPalette : Pairwise (fun f g => Disjoint (palette f) (palette g)))
    (hWhole : paletteCopyCoreGap ends role (univ : Finset D) = 0) :
    let original (b : F ⊕ C) := (univ : Finset D).filter (fun d => colour d ∈ palette b)
    let fineAvail := (univ : Finset D) \ boundary
    let coarseAvail (fine : F → Finset D) := fineAvail \ univ.biUnion fine
    (∀ b, paletteCopyCoreGap ends role (original b) = 0) →
    (∀ b d, d ∈ original b → (role (ends d).1).isLowCore (role (ends d).2) = false) →
    (∀ f : F, Nonempty (PaletteBlockSelectionInput ends role (block (.inl f)) (original (.inl f)) fineAvail)) →
    (∀ fine : F → Finset D,
      (∀ f, IsPaletteBlockSelection ends role (block (.inl f)) (original (.inl f)) fineAvail (fine f)) →
      ∀ c : C, Nonempty (PaletteBlockSelectionInput ends role (block (.inr c))
        (original (.inr c)) (coarseAvail fine))) →
    ∃ (fine : F → Finset D) (coarse : C → Finset D),
      (∀ f, IsPaletteBlockSelection ends role (block (.inl f)) (original (.inl f)) fineAvail (fine f)) ∧
      (∀ c, IsPaletteBlockSelection ends role (block (.inr c)) (original (.inr c))
        (coarseAvail fine) (coarse c)) ∧
      let selected (b : F ⊕ C) := paletteExceptionalCopies ends role (original b) ∪ Sum.elim fine coarse b
      Pairwise (fun f g => Disjoint (selected f) (selected g)) ∧
      paletteCopyCoreGap ends role ((univ : Finset D) \ univ.biUnion selected) = 0 := by
  classical
  intro original fineAvail coarseAvail hOld hLow fineData coarseData
  have hFine (f : F) := (Classical.choice (fineData f)).exists_selection
    (hOld (.inl f)) (hLow (.inl f))
  choose fine hF using hFine
  have hCoarse (c : C) := (Classical.choice (coarseData fine hF c)).exists_selection
    (hOld (.inr c)) (hLow (.inr c))
  choose coarse hC using hCoarse
  let exceptional (b : F ⊕ C) := paletteExceptionalCopies ends role (original b)
  let core : F ⊕ C → Finset D := Sum.elim fine coarse
  let selected (b : F ⊕ C) := exceptional b ∪ core b
  have hLabel (b : F ⊕ C) (d : D) (hd : d ∈ exceptional b) : colour d ∈ palette b :=
    (mem_filter.mp (mem_filter.mp hd).1).2
  have hExc (b : F ⊕ C) (d : D) (hd : d ∈ exceptional b) :
      (role (ends d).1).isCore = false ∧ (role (ends d).2).isCore = false := by
    simpa using (mem_filter.mp hd).2
  have hInBlock (b : F ⊕ C) (d : D) (hd : d ∈ core b) : CopyInCoreBlock ends role (block b) d := by
    cases b with
    | inl f => exact (hF f).in_block d hd
    | inr c => exact (hC c).in_block d hd
  have hExcDisj (b t : F ⊕ C) : Disjoint (exceptional b) (core t) := by
    refine disjoint_left.mpr (fun d hd ht => ?_)
    have h := hExc b d hd
    have hc := (hInBlock t d ht).1
    simp [h.1,h.2] at hc
  have hApart : Pairwise (fun f g => Disjoint (selected f) (selected g)) := by
    intro b t hne
    refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨?_, hExcDisj b t⟩,
      disjoint_union_right.mpr ⟨(hExcDisj t b).symm, ?_⟩⟩
    · exact disjoint_left.mpr (fun d hb ht =>
        disjoint_left.mp (hPalette hne) (hLabel b d hb) (hLabel t d ht))
    · rcases b with f | c <;> rcases t with g | j
      · exact disjoint_copies_of_disjoint_core_blocks ends role
          (hFineBlock (fun h => hne (congrArg Sum.inl h)))
          (fun d hd => (hInBlock (.inl f) d hd).1)
          (fun d hd => (hInBlock (.inl f) d hd).2) (fun d hd => (hInBlock (.inl g) d hd).2)
      · refine disjoint_left.mpr (fun d hd hj => ?_)
        exact (mem_sdiff.mp ((hC j).available_copies hj)).2 (mem_biUnion.mpr ⟨f,mem_univ _,hd⟩)
      · refine disjoint_left.mpr (fun d hc hd => ?_)
        exact (mem_sdiff.mp ((hC c).available_copies hc)).2 (mem_biUnion.mpr ⟨g,mem_univ _,hd⟩)
      · exact disjoint_copies_of_disjoint_core_blocks ends role
          (hCoarseBlock (fun h => hne (congrArg Sum.inr h)))
          (fun d hd => (hInBlock (.inr c) d hd).1)
          (fun d hd => (hInBlock (.inr c) d hd).2) (fun d hd => (hInBlock (.inr j) d hd).2)
  refine ⟨fine,coarse,hF,hC,hApart,?_⟩
  refine palette_copy_remainder_balanced ends role univ selected (fun _ => subset_univ _)
    hApart hWhole ?_
  intro b
  cases b with
  | inl f => exact (hF f).balanced
  | inr c => exact (hC c).balanced


/-- A completed fine selection uses at most the original palette
count in either of the two correction pools. -/
theorem IsPaletteBlockSelection.side_losses [Fintype D]
    {ends : D → V × V} {role : V → PaletteVertexRole}
    {block : Finset V} {original available core : Finset D}
    (S : IsPaletteBlockSelection ends role block original available core) :
    (core ∩ palettePlusCopies ends role univ).card ≤ (palettePlusCopies ends role original).card ∧
      (core ∩ paletteMinusCopies ends role univ).card ≤ (paletteMinusCopies ends role original).card := by
  have h (test : D → Bool) : core ∩ univ.filter (fun d => test d) = core.filter (fun d => test d) := by
    ext d
    simp
  constructor
  · have hPlus : core ∩ palettePlusCopies ends role univ = palettePlusCopies ends role core := h _
    rw [hPlus,S.plus_size]
    exact Nat.sub_le _ _
  · have hMinus : core ∩ paletteMinusCopies ends role univ = paletteMinusCopies ends role core := h _
    rw [hMinus,S.minus_size]
    exact Nat.sub_le _ _

/-- With (5.4) and the last inequality of (5.2), the actual selected
fine core copies leave the coarse deletion budget valid for either side. -/
theorem fine_selection_keeps_coarse_budget {F : Type*} [Fintype F] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : F → Finset V) (original fine : F → Finset D) (boundary available : Finset D)
    (p₂ lambda₁ : ℝ)
    (hFine : ∀ f, IsPaletteBlockSelection ends role (block f) (original f) available (fine f))
    (hPalette : (5/4:ℝ)*(Fintype.card F:ℝ)*lambda₁ ≤ p₂^2/1024) :
    let EPlus := palettePlusCopies ends role (univ : Finset D)
    let EMinus := paletteMinusCopies ends role (univ : Finset D)
    (∀ f, ((palettePlusCopies ends role (original f)).card:ℝ) ≤ (5/4:ℝ)*lambda₁*EPlus.card) →
    (∀ f, ((paletteMinusCopies ends role (original f)).card:ℝ) ≤ (5/4:ℝ)*lambda₁*EMinus.card) →
    ((boundary ∩ EPlus).card:ℝ) ≤ p₂^2*(EPlus.card:ℝ)/1024 →
    ((boundary ∩ EMinus).card:ℝ) ≤ p₂^2*(EMinus.card:ℝ)/1024 →
    let removed := boundary ∪ univ.biUnion fine
    (((removed ∩ EPlus).card:ℝ) ≤ p₂^2*(EPlus.card:ℝ)/512) ∧
      (((removed ∩ EMinus).card:ℝ) ≤ p₂^2*(EMinus.card:ℝ)/512) := by
  intro EPlus EMinus hp hm hbp hbm removed
  constructor
  · have h := fine_and_boundary_deletion_budget EPlus boundary fine (fun _ => ∅) p₂ lambda₁
      (fun _ => by simp) (fun f => le_trans (by exact_mod_cast (hFine f).side_losses.1) (hp f))
      hbp hPalette
    simpa only [union_empty] using h
  · have h := fine_and_boundary_deletion_budget EMinus boundary fine (fun _ => ∅) p₂ lambda₁
      (fun _ => by simp) (fun f => le_trans (by exact_mod_cast (hFine f).side_losses.2) (hm f))
      hbm hPalette
    simpa only [union_empty] using h

/-- The selected fine copies cost at most q k₁ incidences at any
exceptional vertex, including both preferred and correction edges. -/
theorem fine_selection_exceptional_loss {F : Type*} [Fintype F] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : F → Finset V) (original fine : F → Finset D) (available : Finset D)
    (k₁ : ℕ) (v : V) (hv : (role v).isCore = false)
    (hFine : ∀ f, IsPaletteBlockSelection ends role (block f) (original f) available (fine f))
    (hDegree : ∀ f, paletteCopyDegree ends (original f) v ≤ k₁) :
    paletteCopyDegree ends ((univ : Finset F).biUnion fine) v ≤ Fintype.card F*k₁ := by
  classical
  let S := (univ : Finset D).filter (fun d => (ends d).1 = v ∨ (ends d).2 = v)
  have hFilter (T : Finset D) : T ∩ S = T.filter (fun d => (ends d).1 = v ∨ (ends d).2 = v) := by
    ext d
    simp [S]
  rw [paletteCopyDegree, ← hFilter]
  apply fine_exceptional_row_loss S fine k₁
  intro f
  rw [hFilter]
  change paletteCopyDegree ends (fine f) v ≤ _
  have h : paletteCopyDegree ends (fine f) v ≤
      paletteCopyDegree ends (paletteExceptionalCopies ends role (original f) ∪ fine f) v :=
    card_le_card (filter_subset_filter _ subset_union_right)
  exact h.trans (((hFine f).degree v hv).trans_le (hDegree f))

end OverfullWork.ChenShan
