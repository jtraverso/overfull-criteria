module

public import OverfullWork.ChenShanPaletteSelections
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {D V : Type*}

def correctionSide (plus : Bool) (a b : PaletteVertexRole) : Bool :=
  if plus then a.plus b else a.minus b

private theorem correctionSide_no_low (plus : Bool) (a b : PaletteVertexRole) :
    correctionSide plus a b = true → a.isLowCore b = false := by
  cases plus <;> cases a <;> cases b <;> decide

private theorem correctionSide_other (plus : Bool) (a b : PaletteVertexRole) :
    correctionSide plus a b = true → correctionSide (!plus) a b = false := by
  cases plus <;> cases a <;> cases b <;> decide

noncomputable def availableCorrectionCopies (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (available : Finset D) (plus : Bool) : Finset D :=
  available.filter (fun d => CopyInCoreBlock ends role block d ∧
    correctionSide plus (role (ends d).1) (role (ends d).2))

noncomputable def internalCorrectionCopies (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) : Finset D :=
  S.filter (fun d => (role (ends d).1).isCore && (role (ends d).2).isCore)

private theorem exceptional_row_disjoint (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) {v w : V} (_hv : (role v).isCore = false) (hw : (role w).isCore = false)
    (hne : v ≠ w) : Disjoint (paletteCoreRow ends role S v) (paletteCoreRow ends role S w) := by
  refine disjoint_left.mpr (fun d hV hW => ?_)
  rcases (mem_filter.mp hV).2 with ⟨a,b⟩ | ⟨a,b⟩ <;>
    rcases (mem_filter.mp hW).2 with ⟨c,e⟩ | ⟨c,e⟩
  · exact hne (a.symm.trans c)
  · rw [c,hw] at b
    contradiction
  · rw [c,hw] at b
    contradiction
  · exact hne (a.symm.trans c)

/-- The surviving capacity in one sign supplies the positive part of
the imbalance. The exceptional caps apply to the actual incidences of
the chosen copies. No capacity assumption is needed on a side with
zero request. -/
theorem exists_available_correction_side [Fintype V]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (available E : Finset D) (plus : Bool) (p lambda : ℝ) (e eOther : ℕ)
    (cap : V → ℕ) (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ lambda)
    (hScale : 64*lambda ≤ p^2)
    (hCapacity : eOther < e →
      let S := availableCorrectionCopies ends role block available plus
      (e:ℝ) ≤ (5/4:ℝ)*lambda*E.card ∧
      (3/2:ℝ)*lambda*E.card ≤
        (64*lambda/p^2)*(internalCorrectionCopies ends role S).card +
        ∑ v ∈ univ.filter (fun v => (role v).isCore = false),
          min ((64*lambda/p)*(paletteCoreRow ends role S v).card) (cap v)) :
    ∃ K ⊆ availableCorrectionCopies ends role block available plus,
      K.card = e-eOther ∧
      ∀ v, (role v).isCore = false → (paletteCoreRow ends role K v).card ≤ cap v := by
  classical
  by_cases he : eOther < e
  · let S := availableCorrectionCopies ends role block available plus
    let Z := (univ : Finset V).filter (fun v => (role v).isCore = false)
    let I := internalCorrectionCopies ends role S
    let rows := paletteCoreRow ends role S
    have hZ (v : V) : v ∈ Z ↔ (role v).isCore = false := by simp [Z]
    have hI (v : V) (hv : v ∈ Z) : Disjoint I (rows v) := by
      refine disjoint_left.mpr (fun d hd hr => ?_)
      simp only [I, internalCorrectionCopies, mem_filter, Bool.and_eq_true] at hd
      have hc := hd.2
      have h := (hZ v).mp hv
      rcases (mem_filter.mp hr).2 with ⟨a,_⟩ | ⟨a,_⟩
      · exact Bool.noConfusion ((by simpa only [a] using hc.1 : (role v).isCore = true).symm.trans h)
      · exact Bool.noConfusion ((by simpa only [a] using hc.2 : (role v).isCore = true).symm.trans h)
    obtain ⟨K,hK,hSize,hCap⟩ := exists_correction_copies_of_palette_bound E I Z rows cap
      p lambda e eOther hp hpOne hf hScale (hCapacity he).1 hI
      (fun v hv w hw hne => exceptional_row_disjoint ends role S ((hZ _).mp hv) ((hZ _).mp hw) hne)
      (hCapacity he).2
    have hSub : K ⊆ S := by
      intro d hd
      rcases mem_union.mp (hK hd) with h | h
      · exact (mem_filter.mp h).1
      · obtain ⟨v,_,hv⟩ := mem_biUnion.mp h
        exact (mem_filter.mp hv).1
    refine ⟨K,hSub,hSize,fun v hv => ?_⟩
    have hRow : paletteCoreRow ends role K v ⊆ K ∩ rows v := by
      intro d hd
      obtain ⟨hk,hr⟩ := mem_filter.mp hd
      exact mem_inter.mpr ⟨hk,mem_filter.mpr ⟨hSub hk,hr⟩⟩
    exact (card_le_card hRow).trans (hCap v ((hZ v).mpr hv))
  · exact ⟨∅,empty_subset _,by simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt he)],
      fun _ _ => by simp [paletteCoreRow]⟩


def paletteSideCopies (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) (plus : Bool) : Finset D :=
  if plus then palettePlusCopies ends role S else paletteMinusCopies ends role S

def isPreferredCopy (a b : PaletteVertexRole) : Bool :=
  match a,b with
  | .coreA,.prefersA | .prefersA,.coreA | .coreB,.prefersB | .prefersB,.coreB => true
  | _,_ => false

private theorem preferredCopy_neutral (a b : PaletteVertexRole) :
    isPreferredCopy a b = true → a.plus b = false ∧ a.minus b = false ∧ a.isLowCore b = false := by
  cases a <;> cases b <;> decide

/-- Retain only eligible preferred copies from the representatives or
the special-vertex incidence set, as appropriate. -/
noncomputable def availablePreferredCopies (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : Finset V) (available : Finset D) (source : V → Finset D) (v : V) : Finset D :=
  paletteCoreRow ends role ((source v ∩ available).filter (fun d => CopyInCoreBlock ends role block d ∧
    isPreferredCopy (role (ends d).1) (role (ends d).2))) v


/-- The surviving lower bound is required only for a side whose
original palette count exceeds the opposite count. -/
def HasPaletteCorrectionCapacity [Fintype V] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (original available : Finset D) (p lambda : ℝ) (cap : V → ℕ) : Prop :=
  ∀ side : Bool,
    let e := (paletteSideCopies ends role original side).card
    let other := (paletteSideCopies ends role original (!side)).card
    let E := paletteSideCopies ends role univ side
    let S := availableCorrectionCopies ends role block available side
    other < e →
    (e:ℝ) ≤ (5/4:ℝ)*lambda*E.card ∧
    (3/2:ℝ)*lambda*E.card ≤
      (64*lambda/p^2)*(internalCorrectionCopies ends role S).card +
      ∑ v ∈ univ.filter (fun v => (role v).isCore = false),
        min ((64*lambda/p)*(paletteCoreRow ends role S v).card) (cap v)

/-- The two sides' surviving capacity and the preferred-edge count
give exactly the input required by the block selection theorem. -/
theorem paletteBlockSelectionInput_of_capacity [Fintype V] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (original available : Finset D) (source : V → Finset D) (p lambda : ℝ)
    (cap : V → ℕ) (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ lambda) (hScale : 64*lambda ≤ p^2)
    (hCap : ∀ v, (role v).isCore = false → cap v ≤ (paletteCoreRow ends role original v).card)
    (hPreferred : ∀ v, (role v).isCore = false →
      (paletteCoreRow ends role original v).card ≤
        (availablePreferredCopies ends role block available source v).card)
    (hCapacity : HasPaletteCorrectionCapacity ends role block original available p lambda cap) :
    Nonempty (PaletteBlockSelectionInput ends role block original available) := by
  classical
  let ePlus := (palettePlusCopies ends role original).card
  let eMinus := (paletteMinusCopies ends role original).card
  obtain ⟨Kp,hKp,hSp,hCp⟩ := exists_available_correction_side ends role block available
    (palettePlusCopies ends role univ) true p lambda ePlus eMinus cap hp hpOne hf hScale
    (hCapacity true)
  obtain ⟨Km,hKm,hSm,hCm⟩ := exists_available_correction_side ends role block available
    (paletteMinusCopies ends role univ) false p lambda eMinus ePlus cap hp hpOne hf hScale
    (hCapacity false)
  let K := Kp ∪ Km
  let P := availablePreferredCopies ends role block available source
  have hSide (b : Bool) (d : D) (h : d ∈ availableCorrectionCopies ends role block available b) :
      d ∈ available ∧ CopyInCoreBlock ends role block d ∧
        correctionSide b (role (ends d).1) (role (ends d).2) = true := mem_filter.mp h
  have hP (v : V) (d : D) (hd : d ∈ P v) :
      d ∈ available ∧ CopyInCoreBlock ends role block d ∧
        isPreferredCopy (role (ends d).1) (role (ends d).2) = true := by
    have h := mem_filter.mp ((mem_filter.mp hd).1)
    exact ⟨(mem_inter.mp h.1).2,h.2⟩
  have hN (v : V) (d : D) (hd : d ∈ P v) :=
    preferredCopy_neutral _ _ (hP v d hd).2.2
  have hKpT (d : D) (hd : d ∈ Kp) := hSide true d (hKp hd)
  have hKmT (d : D) (hd : d ∈ Km) := hSide false d (hKm hd)
  refine ⟨⟨K,P,?_,?_,?_,?_,?_,?_,hPreferred,?_,?_,?_,?_,?_⟩⟩
  · intro d hd
    rcases mem_union.mp hd with h | h
    · exact (hKpT d h).1
    · exact (hKmT d h).1
  · intro d hd
    rcases mem_union.mp hd with h | h
    · exact (hKpT d h).2.1
    · exact (hKmT d h).2.1
  · intro d hd
    rcases mem_union.mp hd with h | h
    · exact correctionSide_no_low _ _ _ (hKpT d h).2.2
    · exact correctionSide_no_low _ _ _ (hKmT d h).2.2
  · have h : palettePlusCopies ends role K = Kp := by
      ext d
      constructor
      · intro hd
        rcases mem_union.mp (mem_filter.mp hd).1 with h | h
        · exact h
        · have hn := correctionSide_other _ _ _ (hKmT d h).2.2
          exact Bool.noConfusion (hn.symm.trans (mem_filter.mp hd).2)
      · exact fun hd => mem_filter.mpr ⟨mem_union_left _ hd,(hKpT d hd).2.2⟩
    rw [h]
    exact hSp
  · have h : paletteMinusCopies ends role K = Km := by
      ext d
      constructor
      · intro hd
        rcases mem_union.mp (mem_filter.mp hd).1 with h | h
        · have hn := correctionSide_other _ _ _ (hKpT d h).2.2
          exact Bool.noConfusion (hn.symm.trans (mem_filter.mp hd).2)
        · exact h
      · exact fun hd => mem_filter.mpr ⟨mem_union_right _ hd,(hKmT d hd).2.2⟩
    rw [h]
    exact hSm
  · intro v hv
    have h : (paletteCoreRow ends role K v).card ≤ cap v := by
      dsimp only [K]
      by_cases hle : eMinus ≤ ePlus
      · have hm : Km = ∅ := card_eq_zero.mp (hSm.trans (Nat.sub_eq_zero_of_le hle))
        rw [hm,union_empty]
        exact hCp v hv
      · have hp' : Kp = ∅ := card_eq_zero.mp (hSp.trans (Nat.sub_eq_zero_of_le
          (Nat.le_of_lt (Nat.lt_of_not_ge hle))))
        rw [hp',empty_union]
        exact hCm v hv
    exact h.trans (hCap v hv)
  · exact fun v _ d hd => (hP v d hd).1
  · exact fun v _ d hd => (hP v d hd).2.1
  · intro v _ d hd
    exact mem_filter.mpr ⟨hd,(mem_filter.mp hd).2⟩
  · exact fun v _ d hd => hN v d hd
  · intro v _
    apply disjoint_left.mpr
    intro d hd hPreferred'
    have hn := hN v d hPreferred'
    rcases mem_union.mp hd with h | h
    · exact Bool.noConfusion (hn.1.symm.trans (hKpT d h).2.2)
    · exact Bool.noConfusion (hn.2.1.symm.trans (hKmT d h).2.2)


/-- The cap of (5.5), extended by zero to vertices that are not active. -/
noncomputable def paletteExceptionalCap (role : V → PaletteVertexRole) (c : V → ℝ)
    (lambda : ℝ) (v : V) : ℕ :=
  if (role v).preferredSign = 0 then 0 else ⌊(15/16:ℝ)*lambda*c v⌋₊

private theorem low_palette_core_row_empty (ends : D → V × V) (role : V → PaletteVertexRole)
    (original : Finset D) (v : V) (hv : role v = .low)
    (hLow : ∀ d ∈ original, (role (ends d).1).isLowCore (role (ends d).2) = false) :
    paletteCoreRow ends role original v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨hD,hR⟩ := mem_filter.mp hd
  have hn := hLow d hD
  rcases hR with ⟨h,hh⟩ | ⟨h,hh⟩
  · rw [h,hv] at hn
    cases hRole : role (ends d).2 <;> simp_all [PaletteVertexRole.isCore, PaletteVertexRole.isLowCore]
  · rw [h,hv] at hn
    cases hRole : role (ends d).1 <;> simp_all [PaletteVertexRole.isCore, PaletteVertexRole.isLowCore]

/-- The incidence bounds (5.3) and the preferred-edge reserve supply
the two exceptional-row inequalities required by selection. -/
theorem paletteBlockSelectionInput_of_reserves [Fintype V] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (original available : Finset D) (source : V → Finset D)
    (c : V → ℝ) (β theta p lambda : ℝ)
    (hβ : 0 ≤ β) (hβOne : β ≤ 1) (hTheta : theta ≤ 1)
    (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ lambda)
    (hSize : lambda ≤ β*p^2*theta/(2:ℝ)^18)
    (hLow : ∀ d ∈ original, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hc : ∀ v, 0 ≤ c v)
    (hIncidence : ∀ v, (role v).preferredSign ≠ 0 →
      (15/16:ℝ)*lambda*c v ≤ ((paletteCoreRow ends role original v).card:ℝ) ∧
      ((paletteCoreRow ends role original v).card:ℝ) ≤ 2*lambda*c v)
    (hReserve : ∀ v, (role v).preferredSign ≠ 0 →
      β*p*c v/16 ≤ (availablePreferredCopies ends role block available source v).card)
    (hCapacity : HasPaletteCorrectionCapacity ends role block original available p lambda
      (paletteExceptionalCap role c lambda)) :
    Nonempty (PaletteBlockSelectionInput ends role block original available) := by
  have hScale : 64*lambda ≤ p^2 := by
    have hBN : 0 ≤ β*p^2 := mul_nonneg hβ (sq_nonneg p)
    have hT := mul_le_mul_of_nonneg_left hTheta hBN
    have hB := mul_le_mul_of_nonneg_right hβOne (sq_nonneg p)
    norm_num at hSize
    nlinarith only [hSize,hT,hB,sq_nonneg p]
  apply paletteBlockSelectionInput_of_capacity ends role block original available source p lambda
    (paletteExceptionalCap role c lambda) hp hpOne hf hScale _ _ hCapacity
  · intro v _
    by_cases h : (role v).preferredSign = 0
    · simp [paletteExceptionalCap,h]
    · rw [paletteExceptionalCap,ite_eq_right h]
      have hh := (Nat.floor_le (show 0 ≤ (15/16:ℝ)*lambda*c v from mul_nonneg (by positivity) (hc v))).trans
        (hIncidence v h).1
      exact_mod_cast hh
  · intro v hv
    by_cases h : (role v).preferredSign = 0
    · have hRole : role v = .low := by
        cases hR : role v <;> simp_all [PaletteVertexRole.preferredSign, PaletteVertexRole.isCore]
      rw [low_palette_core_row_empty ends role original v hRole hLow,card_empty]
      exact Nat.zero_le _
    · have hReq := palette_request_le_preferred_reserve β p theta lambda (c v)
        (paletteCoreRow ends role original v).card hβ hp.le hpOne hTheta (hc v) hSize
        (hIncidence v h).2
      exact_mod_cast hReq.trans (hReserve v h)


/-- Apply the copy-loss bound to the actual filters defining the
correction pool. The same theorem applies to a boundary alone or a
boundary together with the fine selections. -/
theorem paletteCorrectionCapacity_after_deletions [Fintype V] [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (original removed : Finset D) (p lambda : ℝ) (cap : V → ℕ)
    (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ lambda)
    (hBefore : ∀ side : Bool,
      let e := (paletteSideCopies ends role original side).card
      let other := (paletteSideCopies ends role original (!side)).card
      let E := paletteSideCopies ends role (univ : Finset D) side
      let S := availableCorrectionCopies ends role block (univ : Finset D) side
      other < e →
      (e:ℝ) ≤ (5/4:ℝ)*lambda*E.card ∧
      ((removed ∩ E).card:ℝ) ≤ p^2*(E.card:ℝ)/512 ∧
      (13/8:ℝ)*lambda*E.card ≤
        (64*lambda/p^2)*(internalCorrectionCopies ends role S).card +
        ∑ v ∈ univ.filter (fun v => (role v).isCore = false),
          min ((64*lambda/p)*(paletteCoreRow ends role S v).card) (cap v)) :
    HasPaletteCorrectionCapacity ends role block original (univ \ removed) p lambda cap := by
  classical
  intro side
  dsimp only
  intro he
  obtain ⟨hCount,hLoss,hSample⟩ := hBefore side he
  let E := paletteSideCopies ends role (univ : Finset D) side
  let S := availableCorrectionCopies ends role block (univ : Finset D) side
  let Z := (univ : Finset V).filter (fun v => (role v).isCore = false)
  let I := internalCorrectionCopies ends role S
  let rows := paletteCoreRow ends role S
  have hZ (v : V) : v ∈ Z ↔ (role v).isCore = false := by simp [Z]
  have hS : S ⊆ E := by
    intro d hd
    have h := (mem_filter.mp hd).2.2
    cases side
    · exact mem_filter.mpr ⟨mem_univ _,h⟩
    · exact mem_filter.mpr ⟨mem_univ _,h⟩
  have hI (v : V) (hv : v ∈ Z) : Disjoint I (rows v) := by
    refine disjoint_left.mpr (fun d hd hr => ?_)
    simp only [I, internalCorrectionCopies, mem_filter, Bool.and_eq_true] at hd
    have h := (hZ v).mp hv
    rcases (mem_filter.mp hr).2 with ⟨a,_⟩ | ⟨a,_⟩
    · exact Bool.noConfusion ((by simpa only [a] using hd.2.1 : (role v).isCore = true).symm.trans h)
    · exact Bool.noConfusion ((by simpa only [a] using hd.2.2 : (role v).isCore = true).symm.trans h)
  have h := fine_capacity_after_boundary E removed I Z rows p lambda (fun v => (cap v:ℝ))
    hp hpOne hf hLoss ((filter_subset _ _).trans hS) (fun _ _ => (filter_subset _ _).trans hS)
    hI (fun v hv w hw hne => exceptional_row_disjoint ends role S ((hZ _).mp hv) ((hZ _).mp hw) hne)
    hSample
  have hAvailable : availableCorrectionCopies ends role block (univ \ removed) side = S \ removed := by
    ext d
    simp only [S, availableCorrectionCopies, mem_filter, mem_sdiff, mem_univ, true_and]
    tauto
  have hInternal : internalCorrectionCopies ends role (S \ removed) = I \ removed := by
    ext d
    simp only [I, internalCorrectionCopies, mem_sdiff, mem_filter]
    tauto
  have hRow (v : V) : paletteCoreRow ends role (S \ removed) v = rows v \ removed := by
    ext d
    simp only [rows, paletteCoreRow, mem_sdiff, mem_filter]
    tauto
  refine ⟨hCount,?_⟩
  rw [hAvailable,hInternal]
  simp only [hRow]
  exact h


/-- Removing copies from the available set removes precisely those
copies from the preferred pool. -/
theorem availablePreferredCopies_sdiff
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (available removed : Finset D) (source : V → Finset D) (v : V) :
    availablePreferredCopies ends role block (available \ removed) source v =
      availablePreferredCopies ends role block available source v \ removed := by
  ext d
  simp only [availablePreferredCopies, paletteCoreRow, mem_filter, mem_inter, mem_sdiff]
  tauto

/-- In either stage, the preferred pools retain the paper's threshold.
The original pool and boundary bounds distinguish ordinary and special
vertices; the cost of any earlier fine selections is a common bound. -/
theorem availablePreferredCopies_retains_reserve [Fintype D]
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (boundary fine : Finset D) (source : V → Finset D) (v : V) (special : Bool)
    (β p₁ p c : ℝ) (hβ : 0 ≤ β) (hβOne : β ≤ 1)
    (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p) (hc : 0 ≤ c) :
    let S := availablePreferredCopies ends role block (univ : Finset D) source v
    (if special then p*c/3 else β*p*c/8) ≤ (S.card:ℝ) →
    ((S ∩ boundary).card:ℝ) ≤ (if special then p₁*c/12 else β*p₁*c/32) →
    ((S ∩ fine).card:ℝ) ≤ β*p*c/400 →
    β*p*c/16 ≤ (availablePreferredCopies ends role block
      (((univ : Finset D) \ boundary) \ fine) source v).card := by
  intro S hBefore hBoundary hFine
  rw [availablePreferredCopies_sdiff, availablePreferredCopies_sdiff]
  change β*p*c/16 ≤ (((S \ boundary) \ fine).card:ℝ)
  have hR := preferred_copies_after_two_deletions S boundary fine _ _ _ hBefore hBoundary hFine
  have hP := mul_le_mul_of_nonneg_right hp hc
  have hPB := mul_le_mul_of_nonneg_left hP hβ
  have hPC : 0 ≤ p*c := mul_nonneg (hp₁.trans hp) hc
  have hBC : 0 ≤ β*(p*c) := mul_nonneg hβ hPC
  have hβC := mul_le_mul_of_nonneg_right hβOne hPC
  cases special <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hR <;>
    nlinarith only [hR,hP,hPB,hPC,hBC,hβC]

/-- An exceptional vertex loses at most its fine incidence count
from any preferred pool, regardless of which copies were used. -/
theorem preferred_inter_card_le_fine_degree
    (ends : D → V × V) (role : V → PaletteVertexRole) (block : Finset V)
    (available fine : Finset D) (source : V → Finset D) (v : V) :
    ((availablePreferredCopies ends role block available source v) ∩ fine).card ≤
      paletteCopyDegree ends fine v := by
  apply card_le_card
  intro d hd
  obtain ⟨hP,hF⟩ := mem_inter.mp hd
  have hRow := (mem_filter.mp hP).2
  exact mem_filter.mpr ⟨hF,hRow.imp And.left And.left⟩

end OverfullWork.ChenShan
