module

public import OverfullWork.ChenShanFineCoarseDeletion
public import OverfullWork.ChenShanFactorization42
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph
open scoped Classical

/-- Core sides, active vertices by preferred side, and low vertices
in §5.1.4. An edge from a low vertex to the core is excluded. -/
inductive PaletteVertexRole
  | coreA | coreB | prefersA | prefersB | low
  deriving DecidableEq

namespace PaletteVertexRole

def coreSign : PaletteVertexRole → ℤ
  | .coreA => 1
  | .coreB => -1
  | _ => 0

def preferredSign : PaletteVertexRole → ℤ
  | .prefersA => 1
  | .prefersB => -1
  | _ => 0

def isCore : PaletteVertexRole → Bool
  | .coreA | .coreB => true
  | _ => false

def isLowCore : PaletteVertexRole → PaletteVertexRole → Bool
  | .low, .coreA | .low, .coreB | .coreA, .low | .coreB, .low => true
  | _, _ => false

/-- E₊ contains copies within B and from vertices preferring A to B. -/
def plus : PaletteVertexRole → PaletteVertexRole → Bool
  | .coreB, .coreB | .prefersA, .coreB | .coreB, .prefersA => true
  | _, _ => false

/-- E₋ contains copies within A and from vertices preferring B to A. -/
def minus : PaletteVertexRole → PaletteVertexRole → Bool
  | .coreA, .coreA | .prefersB, .coreA | .coreA, .prefersB => true
  | _, _ => false

def preferredLoad (u v : PaletteVertexRole) : ℤ :=
  (if v.isCore then u.preferredSign else 0) +
    (if u.isCore then v.preferredSign else 0)

theorem preferredLoad_eq (u v : PaletteVertexRole) :
    u.isLowCore v = false →
    u.preferredLoad v =
      u.coreSign+v.coreSign + 2*((if u.plus v then (1:ℤ) else 0) -
        (if u.minus v then 1 else 0)) := by
  cases u <;> cases v <;> decide

theorem plus_excludes_minus (u v : PaletteVertexRole) :
    u.plus v = true → u.minus v = false := by
  cases u <;> cases v <;> decide

end PaletteVertexRole

section Copies

variable {D V : Type*}

def palettePlusCopies (ends : D → V × V) (role : V → PaletteVertexRole) (S : Finset D) :
    Finset D :=
  S.filter (fun d => (role (ends d).1).plus (role (ends d).2))

def paletteMinusCopies (ends : D → V × V) (role : V → PaletteVertexRole) (S : Finset D) :
    Finset D :=
  S.filter (fun d => (role (ends d).1).minus (role (ends d).2))

def paletteCopyCoreGap (ends : D → V × V) (role : V → PaletteVertexRole) (S : Finset D) :
    ℤ := ∑ d ∈ S, ((role (ends d).1).coreSign + (role (ends d).2).coreSign)

def paletteCopyPreferredGap (ends : D → V × V) (role : V → PaletteVertexRole) (S : Finset D) :
    ℤ := ∑ d ∈ S, (role (ends d).1).preferredLoad (role (ends d).2)

/-- The preferred-only imbalance for actual indexed copies. Copies
within a core side contribute twice, and crossing core copies cancel. -/
theorem palette_copy_preferred_gap_eq (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) (hLow : ∀ d ∈ S, (role (ends d).1).isLowCore (role (ends d).2) = false) :
    paletteCopyPreferredGap ends role S =
      paletteCopyCoreGap ends role S +
        2*(((palettePlusCopies ends role S).card:ℤ)-((paletteMinusCopies ends role S).card:ℤ)) := by
  unfold paletteCopyPreferredGap paletteCopyCoreGap palettePlusCopies paletteMinusCopies
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [PaletteVertexRole.preferredLoad_eq _ _ (hLow d hd)]
  ring

/-- Exceptional-to-core copies at a vertex of an arbitrary set of
copies. A core-to-core or exceptional-to-exceptional copy contributes
to none of the preferred loads. -/
noncomputable def paletteCoreRow (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) (v : V) : Finset D :=
  S.filter (fun d => ((ends d).1 = v ∧ (role (ends d).2).isCore) ∨
    ((ends d).2 = v ∧ (role (ends d).1).isCore))

/-- The preferred-only imbalance depends just on how many core copies
each active vertex receives, regardless of the chosen core endpoints. -/
theorem paletteCopyPreferredGap_eq_sum_rows [Fintype V] (ends : D → V × V)
    (role : V → PaletteVertexRole) (S : Finset D) :
    paletteCopyPreferredGap ends role S =
      ∑ v, (role v).preferredSign * ((paletteCoreRow ends role S v).card:ℤ) := by
  classical
  unfold paletteCopyPreferredGap paletteCoreRow
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  let x := (ends d).1
  let y := (ends d).2
  change (role x).preferredLoad (role y) =
    ∑ v, (role v).preferredSign * (if (x = v ∧ (role y).isCore = true) ∨
      (y = v ∧ (role x).isCore = true) then 1 else 0)
  have hCore (v : V) : (role v).isCore = true → (role v).preferredSign = 0 := by
    cases role v <;> decide
  by_cases hx : (role x).isCore = true
  · by_cases hy : (role y).isCore = true
    · have hZ (v : V) : (role v).preferredSign *
          (if (x = v ∧ (role y).isCore = true) ∨ (y = v ∧ (role x).isCore = true)
            then (1:ℤ) else 0) = 0 := by
        by_cases h : x = v ∨ y = v
        · rcases h with rfl | rfl
          · rw [hCore x hx,zero_mul]
          · rw [hCore y hy,zero_mul]
        · push Not at h
          simp [h.1,h.2]
      simp only [hZ, sum_const_zero]
      simp only [PaletteVertexRole.preferredLoad, hx, hy,
        ite_eq_left, hCore x hx, hCore y hy, add_zero]
    · simp [PaletteVertexRole.preferredLoad, hx, hy, eq_comm]
  · by_cases hy : (role y).isCore = true
    · simp [PaletteVertexRole.preferredLoad, hx, hy, eq_comm]
    · simp [PaletteVertexRole.preferredLoad, hx, hy]

/-- Equation (5.8) for a collection of balanced copies with no
low-to-core copies. -/
theorem palette_copy_imbalance [Fintype V] (ends : D → V × V)
    (role : V → PaletteVertexRole) (S : Finset D)
    (hLow : ∀ d ∈ S, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hBalance : paletteCopyCoreGap ends role S = 0) :
    (∑ v, (role v).preferredSign * ((paletteCoreRow ends role S v).card:ℤ)) =
      2*(((palettePlusCopies ends role S).card:ℤ)-((paletteMinusCopies ends role S).card:ℤ)) := by
  rw [← paletteCopyPreferredGap_eq_sum_rows, palette_copy_preferred_gap_eq _ _ _ hLow, hBalance,
    zero_add]

/-- Balancing one selected palette is equivalent to preserving
its exceptional-to-core row sizes and its net correction count. -/
theorem palette_selection_balanced_of_rows_and_corrections [Fintype V]
    (ends : D → V × V) (role : V → PaletteVertexRole) (original selected : Finset D)
    (hLowOld : ∀ d ∈ original, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hLowNew : ∀ d ∈ selected, (role (ends d).1).isLowCore (role (ends d).2) = false)
    (hOld : paletteCopyCoreGap ends role original = 0)
    (hRows : ∀ v, (role v).preferredSign ≠ 0 →
      (paletteCoreRow ends role selected v).card = (paletteCoreRow ends role original v).card)
    (hCorrections :
      ((palettePlusCopies ends role selected).card:ℤ)-((paletteMinusCopies ends role selected).card:ℤ) =
      ((palettePlusCopies ends role original).card:ℤ)-((paletteMinusCopies ends role original).card:ℤ)) :
    paletteCopyCoreGap ends role selected = 0 := by
  have hPref : paletteCopyPreferredGap ends role selected = paletteCopyPreferredGap ends role original := by
    rw [paletteCopyPreferredGap_eq_sum_rows, paletteCopyPreferredGap_eq_sum_rows]
    apply sum_congr rfl
    intro v _
    by_cases hv : (role v).preferredSign = 0
    · simp only [hv, zero_mul]
    · rw [hRows v hv]
  rw [palette_copy_preferred_gap_eq _ _ _ hLowNew, palette_copy_preferred_gap_eq _ _ _ hLowOld,
    hCorrections, hOld] at hPref
  linarith only [hPref]


/-- Counting the contributions of a copy at its two endpoints equals
summing the incidence counts on the two core sides. -/
theorem paletteCopyCoreGap_eq_degree_sum [Fintype V] [DecidableEq V] (ends : D → V × V)
    (role : V → PaletteVertexRole) (S : Finset D)
    (hEnds : ∀ d ∈ S, (ends d).1 ≠ (ends d).2) :
    paletteCopyCoreGap ends role S =
      ∑ v, (role v).coreSign *
        (((S.filter fun d => (ends d).1 = v ∨ (ends d).2 = v).card):ℤ) := by
  classical
  unfold paletteCopyCoreGap
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_zero,
    Nat.cast_one, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  let x := (ends d).1
  let y := (ends d).2
  have hn : x ≠ y := hEnds d hd
  have h (v : V) : (role v).coreSign * (if x = v ∨ y = v then (1:ℤ) else 0) =
      (if v = x then (role x).coreSign else 0) + (if v = y then (role y).coreSign else 0) := by
    by_cases hx : v = x
    · subst v
      simp [hn,hn.symm]
    · by_cases hy : v = y
      · subst v
        simp [hx,hn]
      · simp [hx,hy,Ne.symm hx,Ne.symm hy]
  change (role x).coreSign + (role y).coreSign = ∑ v, (role v).coreSign * (if x = v ∨ y = v then (1:ℤ) else 0)
  simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]

/-- Summing core imbalance over a palette equals summing over the
union of its color classes. -/
theorem paletteCopyCoreGap_colour_union {K : Type*} [DecidableEq K] [Fintype D] (ends : D → V × V)
    (role : V → PaletteVertexRole) (colour : D → K) (P : Finset K) :
    paletteCopyCoreGap ends role (univ.filter (fun d => colour d ∈ P)) =
      ∑ j ∈ P, paletteCopyCoreGap ends role (univ.filter (fun d => colour d = j)) := by
  classical
  unfold paletteCopyCoreGap
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_ite_eq]


/-- The exact positive-part correction sizes in the two pools have
the same signed difference as the original palette counts. -/
theorem palette_correction_gap_of_exact_sizes (ePlus eMinus cPlus cMinus : ℕ)
    (hp : cPlus = ePlus-eMinus) (hm : cMinus = eMinus-ePlus) :
    (cPlus:ℤ)-(cMinus:ℤ) = (ePlus:ℤ)-(eMinus:ℤ) := by
  omega

/-- Disjoint core blocks cannot share a selected copy whose core
ends all lie in its assigned block. -/
theorem disjoint_copies_of_disjoint_core_blocks (ends : D → V × V)
    (role : V → PaletteVertexRole) {X Y : Finset V} {S T : Finset D}
    (hBlocks : Disjoint X Y)
    (hCore : ∀ d ∈ S, (role (ends d).1).isCore ∨ (role (ends d).2).isCore)
    (hS : ∀ d ∈ S, ((role (ends d).1).isCore → (ends d).1 ∈ X) ∧
      ((role (ends d).2).isCore → (ends d).2 ∈ X))
    (hT : ∀ d ∈ T, ((role (ends d).1).isCore → (ends d).1 ∈ Y) ∧
      ((role (ends d).2).isCore → (ends d).2 ∈ Y)) :
    Disjoint S T := by
  refine disjoint_left.mpr (fun d hs ht => ?_)
  rcases hCore d hs with h | h
  · exact disjoint_left.mp hBlocks ((hS d hs).1 h) ((hT d ht).1 h)
  · exact disjoint_left.mp hBlocks ((hS d hs).2 h) ((hT d ht).2 h)

/-- Internal exceptional copies retain their palette labels, while
the selected core copies occupy disjoint blocks. Their combined
selections are pairwise disjoint within one family. -/
theorem pairwise_disjoint_palette_selections {F K : Type*}
    (ends : D → V × V) (role : V → PaletteVertexRole)
    (block : F → Finset V) (palette : F → Finset K) (colour : D → K)
    (exceptional core : F → Finset D)
    (hBlocks : Pairwise (fun f g => Disjoint (block f) (block g)))
    (hPalettes : Pairwise (fun f g => Disjoint (palette f) (palette g)))
    (hLabels : ∀ f d, d ∈ exceptional f → colour d ∈ palette f)
    (hExceptional : ∀ f d, d ∈ exceptional f →
      (role (ends d).1).isCore = false ∧ (role (ends d).2).isCore = false)
    (hCore : ∀ f d, d ∈ core f → (role (ends d).1).isCore ∨ (role (ends d).2).isCore)
    (hInBlock : ∀ f d, d ∈ core f →
      ((role (ends d).1).isCore → (ends d).1 ∈ block f) ∧
      ((role (ends d).2).isCore → (ends d).2 ∈ block f)) :
    Pairwise (fun f g => Disjoint (exceptional f ∪ core f) (exceptional g ∪ core g)) := by
  intro f g hfg
  have hCross (f g : F) : Disjoint (exceptional f) (core g) := by
    refine disjoint_left.mpr (fun d hd he => ?_)
    have h := hExceptional f d hd
    rcases hCore g d he with hd | hd
    · exact Bool.noConfusion (h.1.symm.trans hd)
    · exact Bool.noConfusion (h.2.symm.trans hd)
  refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨?_,hCross f g⟩,
    disjoint_union_right.mpr ⟨(hCross g f).symm,?_⟩⟩
  · exact disjoint_left.mpr (fun d hd he =>
      disjoint_left.mp (hPalettes hfg) (hLabels f d hd) (hLabels g d he))
  · exact disjoint_copies_of_disjoint_core_blocks ends role (hBlocks hfg)
      (hCore f) (hInBlock f) (hInBlock g)

/-- If the whole copy set and each member of a disjoint selected family
have balanced core degree sums, then so does the remainder. -/
theorem palette_copy_remainder_balanced {F : Type*} [Fintype F]
    (ends : D → V × V) (role : V → PaletteVertexRole)
    (all : Finset D) (selected : F → Finset D)
    (hSub : ∀ f, selected f ⊆ all)
    (hDisj : Pairwise (fun f g => Disjoint (selected f) (selected g)))
    (hAll : paletteCopyCoreGap ends role all = 0)
    (hSelected : ∀ f, paletteCopyCoreGap ends role (selected f) = 0) :
    paletteCopyCoreGap ends role (all \ (univ : Finset F).biUnion selected) = 0 := by
  let T := (univ : Finset F).biUnion selected
  have hT : T ⊆ all := by
    intro d hd
    obtain ⟨f,_,hf⟩ := mem_biUnion.mp hd
    exact hSub f hf
  have hUnion : (all \ T) ∪ T = all := sdiff_union_of_subset hT
  have hBal : paletteCopyCoreGap ends role T = 0 := by
    unfold paletteCopyCoreGap
    dsimp only [T]
    rw [sum_biUnion (fun _ _ _ _ h => hDisj h)]
    exact sum_eq_zero (fun f _ => hSelected f)
  change paletteCopyCoreGap ends role (all \ T) = 0
  have h := congrArg (paletteCopyCoreGap ends role) hUnion
  unfold paletteCopyCoreGap at h hBal hAll ⊢
  rw [sum_union sdiff_disjoint, hBal, add_zero, hAll] at h
  exact h


/-- Count the exceptional-to-exceptional copies retained from the
original palette. -/
def paletteExceptionalCopies (ends : D → V × V) (role : V → PaletteVertexRole)
    (S : Finset D) : Finset D :=
  S.filter (fun d => !(role (ends d).1).isCore && !(role (ends d).2).isCore)

noncomputable def paletteCopyDegree (ends : D → V × V) (S : Finset D) (v : V) : ℕ :=
  (S.filter fun d => (ends d).1 = v ∨ (ends d).2 = v).card

/-- At an exceptional vertex the incident copies split into its
retained internal exceptional copies and its core row. -/
theorem paletteCopyDegree_exceptional (ends : D → V × V)
    (role : V → PaletteVertexRole) (S : Finset D) (v : V)
    (hv : (role v).isCore = false) :
    paletteCopyDegree ends S v =
      paletteCopyDegree ends (paletteExceptionalCopies ends role S) v +
        (paletteCoreRow ends role S v).card := by
  classical
  let A := (paletteExceptionalCopies ends role S).filter
    (fun d => (ends d).1 = v ∨ (ends d).2 = v)
  let B := paletteCoreRow ends role S v
  have hD : Disjoint A B := by
    refine disjoint_left.mpr (fun d hA hB => ?_)
    simp only [A, B, paletteExceptionalCopies, paletteCoreRow, mem_filter,
      Bool.and_eq_true] at hA hB
    rcases hB.2 with h | h
    · have hh := hA.1.2.2
      simp [h.2] at hh
    · have hh := hA.1.2.1
      simp [h.2] at hh
  have hUnion : S.filter (fun d => (ends d).1 = v ∨ (ends d).2 = v) = A ∪ B := by
    ext d
    have h₁ (h : (ends d).1 = v) : (role (ends d).1).isCore = false := by rw [h,hv]
    have h₂ (h : (ends d).2 = v) : (role (ends d).2).isCore = false := by rw [h,hv]
    by_cases hL : (ends d).1 = v <;> by_cases hR : (ends d).2 = v <;>
      cases hc₁ : (role (ends d).1).isCore <;> cases hc₂ : (role (ends d).2).isCore <;>
      simp_all [A, B, paletteExceptionalCopies, paletteCoreRow]
  unfold paletteCopyDegree
  rw [hUnion, card_union_of_disjoint hD]

/-- Keeping the original exceptional-inside copies and filling each
core row to its original size preserves the exceptional degrees. -/
theorem paletteCopyDegree_preserved_at_exceptionals (ends : D → V × V)
    (role : V → PaletteVertexRole) (original selected : Finset D)
    (hInternal : paletteExceptionalCopies ends role selected = paletteExceptionalCopies ends role original)
    (hRows : ∀ v, (role v).isCore = false →
      (paletteCoreRow ends role selected v).card = (paletteCoreRow ends role original v).card)
    (v : V) (hv : (role v).isCore = false) :
    paletteCopyDegree ends selected v = paletteCopyDegree ends original v := by
  rw [paletteCopyDegree_exceptional ends role selected v hv,
    paletteCopyDegree_exceptional ends role original v hv, hInternal, hRows v hv]

end Copies


section ColouredCopies

variable {V : Type*} [Fintype V] [DecidableEq V]

open MultiGraph.GeneralCopies

/-- The balanced coloring from Lemma 3.9 provides actual copies whose
union over any palette is balanced. The numbering agrees with the
original color of each copy. -/
theorem exists_labelled_balanced_palette_copies {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) (A B : Finset V) (role : V → PaletteVertexRole)
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hBalance : ∀ j, sideCount C A j = sideCount C B j) :
    ∃ colour : Copies M → Fin k,
      (∀ d, C.col d.1 (colour d) = 1) ∧
      (∀ v j d e, v ∈ d.1 → v ∈ e.1 → colour d = j → colour e = j → d = e) ∧
      (∀ v j, (∃ d, v ∈ d.1 ∧ colour d = j) ↔ (C.colourGraph j).degree v = 1) ∧
      ∀ P : Finset (Fin k), paletteCopyCoreGap (ends M) role
        (univ.filter (fun d => colour d ∈ P)) = 0 := by
  obtain ⟨colour,hUnique,hUsed⟩ := exists_copy_colours_with_incidence C
  refine ⟨colour,hUnique.1,hUnique.2,hUsed,?_⟩
  intro P
  rw [paletteCopyCoreGap_colour_union (ends M) role colour P]
  apply sum_eq_zero
  intro j _
  let S := (univ : Finset (Copies M)).filter (fun d => colour d = j)
  change paletteCopyCoreGap (ends M) role S = 0
  rw [paletteCopyCoreGap_eq_degree_sum _ _ _ (fun d _ => MultiGraph.GeneralCopies.loopless M d)]
  have hRow (v : V) :
      (S.filter fun d => (ends M d).1 = v ∨ (ends M d).2 = v).card =
        (C.colourGraph j).degree v := by
    let T := S.filter (fun d => (ends M d).1 = v ∨ (ends M d).2 = v)
    have hMem (d : Copies M) : d ∈ T ↔ v ∈ d.1 ∧ colour d = j := by
      have hI := incident_iff M d v
      change ((ends M d).1 = v ∨ (ends M d).2 = v) ↔ v ∈ d.1 at hI
      simp only [T,S,mem_filter,mem_univ,true_and,hI,and_comm]
    have hOne : T.card ≤ 1 := card_le_one.mpr (fun d hd e he =>
      hUnique.2 v j d e ((hMem d).mp hd).1 ((hMem e).mp he).1
        ((hMem d).mp hd).2 ((hMem e).mp he).2)
    have hNonempty : 0 < T.card ↔ (C.colourGraph j).degree v = 1 := by
      rw [← hUsed, card_pos]
      exact exists_congr hMem
    have hDeg := C.colourGraph_degree_le_one j v
    change T.card = (C.colourGraph j).degree v
    by_cases hPos : 0 < T.card
    · have hG := hNonempty.mp hPos
      omega
    · have hz : T.card = 0 := by omega
      have hG : (C.colourGraph j).degree v ≠ 1 := fun h => hPos (hNonempty.mpr h)
      omega
  simp_rw [hRow]
  have hRole (v : V) : (role v).coreSign =
      (if v ∈ A then (1:ℤ) else 0) - (if v ∈ B then 1 else 0) := by
    cases h : role v <;> simp [PaletteVertexRole.coreSign, ← hA v, ← hB v, h]
  simp_rw [hRole, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, ← sum_filter]
  have hFilter (U : Finset V) : univ.filter (fun v => v ∈ U) = U := by
    ext v
    simp
  rw [hFilter A,hFilter B]
  change sideCount C A j - sideCount C B j = 0
  rw [hBalance,sub_self]

end ColouredCopies

end OverfullWork.ChenShan
