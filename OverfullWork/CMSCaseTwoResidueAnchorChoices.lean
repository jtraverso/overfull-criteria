module

public import OverfullWork.CMSCaseTwoResidueAssembly
public import OverfullWork.FirstAnchorUnitMass
public import OverfullWork.UnitInternalAnchor
public import OverfullWork.SecondAnchorNeighbourAvailability
public import OverfullWork.CentreResidualSupport

@[expose] public section


/-! The local anchor choices for a fresh residue colour in CMS 4.2.
Separate the combinatorial Stage I case split from the estimates
that leave free copies in the prescribed centre bundles. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k f : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

theorem CaseTwoPartition.second_anchor_neighbours
    (s : CaseTwoPartition M a b d m L r t η) (Q : M.PartialColouring k)
    (S : M.PartialColouring (k+f)) (i : Fin (k+f)) (occ del E₀ : ℕ) (κ : ℝ)
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e) (hSat : Q.graph.degree b = k)
    (hCross : (Q.graph.crossingSupport s.part).degree b ≤ del)
    (hOcc : (s.part \ S.colouring.missingSet s.part i).card ≤ occ)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E₀)
    (hPair : (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ))
    (hPay : η*(m:ℝ)+2*((occ+del+f:ℕ):ℝ)+2+(E₀:ℝ) ≤ κ*(m:ℝ)) :
    1 < (S.available.neighboursInto (S.colouring.missingSet s.part i) b).card := by
  have hProfileR : (d:ℝ) ≤ (M.supportGraph.degree b:ℝ)+(M.mult s(a,b):ℝ)+(E₀:ℝ) := by
    exact_mod_cast hProfile
  have hSupport : κ*(m:ℝ)-(E₀:ℝ) ≤ M.supportGraph.degree b :=
    by linarith only [hProfileR,hPair]
  have hCross' := (Q.crossing_degree_after_fresh_palette S s.part b hMono hSat).trans
    (Nat.add_le_add_right hCross f)
  have hCrossR : ((S.graph.crossingSupport s.part).degree b:ℝ) ≤ (del:ℝ)+(f:ℝ) := by
    exact_mod_cast hCross'
  have hOccR : ((s.part \ S.colouring.missingSet s.part i).card:ℝ) ≤ (occ:ℝ) := by exact_mod_cast hOcc
  apply S.two_missing_neighbours_of_support_budget s.part b s.second_not_mem i
    (κ*(m:ℝ)-(E₀:ℝ)) (η*(m:ℝ)) hSupport (s.simple_discrepancy b)
  push_cast at hPay
  linarith only [hCrossR,hOccR,hPay]

set_option maxHeartbeats 1700000 in
theorem CaseTwoPartition.stage_one_first_anchor
    (s : CaseTwoPartition M a b d m L r t η) (Q : M.PartialColouring k)
    (C : (Q.available.internalPart s.part).EdgeColoring f) (S : M.PartialColouring (k+f))
    (j : Fin f) (Λ : ℕ) (U : ℝ) (hΛ : L ≤ Λ) (hReg : M.IsRegularOfDegree d)
    (hCover : S.CoversInternal s.part)
    (hSame : S.colouring.colourGraph (Fin.natAdd k j) = C.colourGraph j)
    (hUnit : (C.colourGraph j).edgesWithin s.partᶜ = 1)
    (hUpper : (S.available.mult s(a,b):ℝ) ≤ U)
    (hLight : ((k+f:ℕ):ℝ)+U+2*(Λ:ℝ) < (d:ℝ))
    (hLargeFree : ∀ v, v ≠ a → v ≠ b → Λ < M.mult s(a,v) →
      0 < S.available.mult s(a,v) ∧ 0 < S.available.mult s(a,b))
    (hUniqueZero : ∀ v, v ≠ a → v ≠ b → Λ < M.mult s(a,v) →
      (∀ x, x ≠ a → x ≠ b → Λ < M.mult s(a,x) → x = v) →
      Q.available.mult s(b,v) = 0) :
    0 < S.available.degreeInto (S.colouring.missingSet s.partᶜ (Fin.natAdd k j)) a := by
  let i := Fin.natAdd k j
  have hEq : S.colouring.missingSet s.partᶜ i = C.missingSet s.partᶜ j := by
    simp only [i,MultiGraph.EdgeColoring.missingSet,hSame]
  have hCard : (s.partᶜ \ S.colouring.missingSet s.partᶜ i).card = 2 := by
    rw [hEq]
    have hh := C.internal_missing_count_compl s.part j
    have hs := card_sdiff_add_card_eq_card (show C.missingSet s.partᶜ j ⊆ s.partᶜ from filter_subset _ _)
    rw [hUnit] at hh
    omega
  let Z := univ.filter (fun v => v ≠ a ∧ v ≠ b ∧ Λ < M.mult s(a,v))
  have hData (v : V) (hv : v ∈ Z) :
      v ≠ a ∧ v ≠ b ∧ Λ < M.mult s(a,v) := (mem_filter.mp hv).2
  have hAcross (v : V) (hv : v ∈ Z) : v ∈ s.partᶜ :=
    mem_compl.mpr (s.heavy_across v (hData v hv).2.1 (hΛ.trans_lt (hData v hv).2.2))
  by_cases hZ : Z.Nonempty
  · obtain ⟨v,hv⟩ := hZ
    obtain ⟨hva,hvb,hvL⟩ := hData v hv
    obtain ⟨hvFree,hbFree⟩ := hLargeFree v hva hvb hvL
    by_cases hAll : ∀ x ∈ Z, x = v
    · have hZero := hUniqueZero v hva hvb hvL
        (fun x hxa hxb hxL => hAll x (mem_filter.mpr ⟨mem_univ _,hxa,hxb,hxL⟩))
      have hh := C.unit_internal_pair_has_missing j b v
        (mem_compl.mpr s.second_not_mem) (hAcross v hv) hvb.symm hUnit hZero
      rw [←hEq] at hh
      exact hh.elim (fun h => S.first_anchor_mass_of_missing_candidate s.part a b i h hbFree)
        (fun h => S.first_anchor_mass_of_missing_candidate s.part a v i h hvFree)
    · push Not at hAll
      obtain ⟨x,hx,hxv⟩ := hAll
      obtain ⟨hxa,hxb,hxL⟩ := hData x hx
      have hxFree := (hLargeFree x hxa hxb hxL).1
      have hh : b ∈ S.colouring.missingSet s.partᶜ i ∨
          v ∈ S.colouring.missingSet s.partᶜ i ∨ x ∈ S.colouring.missingSet s.partᶜ i := by
        by_contra! hn
        have hSub : ({b,v,x} : Finset V) ⊆ s.partᶜ \ S.colouring.missingSet s.partᶜ i := by
          simp only [insert_subset_iff,singleton_subset_iff]
          exact ⟨mem_sdiff.mpr ⟨mem_compl.mpr s.second_not_mem,hn.1⟩,
            mem_sdiff.mpr ⟨hAcross v hv,hn.2.1⟩,mem_sdiff.mpr ⟨hAcross x hx,hn.2.2⟩⟩
        have hThree : ({b,v,x} : Finset V).card = 3 := by simp [hvb.symm,hxb.symm,hxv.symm]
        have hLe := card_le_card hSub
        omega
      rcases hh with hh | hh | hh
      · exact S.first_anchor_mass_of_missing_candidate s.part a b i hh hbFree
      · exact S.first_anchor_mass_of_missing_candidate s.part a v i hh hvFree
      · exact S.first_anchor_mass_of_missing_candidate s.part a x i hh hxFree
  · apply S.first_anchor_mass_of_two_light_blockers s.part a b d i Λ U
      s.centre_mem hReg hCover hCard.le (Nat.cast_nonneg _) hUpper ?_ hLight
    intro v hv hvb
    have hva : v ≠ a := fun he => (mem_compl.mp hv) (he ▸ s.centre_mem)
    have hh : M.mult s(a,v) ≤ Λ := by
      by_contra! hn
      exact hZ ⟨v,mem_filter.mpr ⟨mem_univ _,hva,hvb,hn⟩⟩
    exact_mod_cast hh

/-- When there is exactly one large non-anchor bundle, the pair
joining its endpoint to the second anchor has no remaining copy. -/
theorem CaseTwoPartition.unique_large_bundle_has_no_residue
    (s : CaseTwoPartition M a b d m L r t η) (Q : M.PartialColouring k) (Λ : ℕ)
    (hw : w ∉ s.part)
    (hException : if (exceptionCandidates M a b Λ).card = 1 then
      w ∈ exceptionCandidates M a b Λ else w = b)
    (hProtected : (Q.available.internalPart s.part).mult s(b,w) = 0)
    (v : V) (hva : v ≠ a) (hvb : v ≠ b) (hvL : Λ < M.mult s(a,v))
    (hUnique : ∀ x, x ≠ a → x ≠ b → Λ < M.mult s(a,x) → x = v) :
    Q.available.mult s(b,v) = 0 := by
  by_cases hq : 0 < M.mult s(b,v)
  · have hSet : exceptionCandidates M a b Λ = {v} := by
      ext x
      simp only [exceptionCandidates,mem_filter,mem_univ,true_and,mem_singleton]
      exact ⟨fun h => hUnique x h.1 h.2.1 h.2.2.1,
        fun h => h.symm ▸ ⟨hva,hvb,hvL,hq⟩⟩
    have hwv : w = v := by simpa only [hSet,card_singleton,if_true,mem_singleton] using hException
    rw [←hwv]
    rw [MultiGraph.internalPart_mult,if_pos (iff_of_false s.second_not_mem hw)] at hProtected
    exact hProtected
  · change M.mult s(b,v)-Q.graph.mult s(b,v) = 0
    omega

/-- Protect the original spare neighbours when there are few of
them. If there are many, keep just the two anchors protected. -/
theorem exists_protected_centre_neighbours (A : Finset V) (R : M.PartialColouring k)
    (a b : V) (u : ℕ) :
    ∃ E : Finset V, a ∈ E ∧ b ∈ E ∧ E.card ≤ u+2 ∧
      ((R.available.crossingSupport A).neighborFinset a ⊆ E ∨
        u < (R.available.crossingSupport A).degree a) := by
  let Z := (R.available.crossingSupport A).neighborFinset a
  by_cases hz : Z.card ≤ u
  · refine ⟨insert a (insert b Z),mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _),?_,?_⟩
    · have h₁ := card_insert_le a (insert b Z)
      have h₂ := card_insert_le b Z
      omega
    · exact Or.inl (fun v hv => mem_insert_of_mem (mem_insert_of_mem hv))
  · refine ⟨{a,b},by simp,by simp,(card_insert_le _ _).trans (by simp),Or.inr ?_⟩
    have hh : u < Z.card := by omega
    simpa only [Z,card_neighborFinset_eq_degree] using hh

theorem protected_centre_available_neighbours {A E : Finset V} {h ell n u : ℕ}
    {R Q : M.PartialColouring k} (run : GoodRouteRun A E h ell R Q n u)
    (ha : a ∈ E) (hSat : R.graph.degree a = k) :
    (Q.available.crossingSupport A).neighborFinset a =
      (R.available.crossingSupport A).neighborFinset a := by
  ext v
  simp only [mem_neighborFinset]
  change (0 < M.mult s(a,v)-Q.graph.mult s(a,v) ∧ _) ↔
    (0 < M.mult s(a,v)-R.graph.mult s(a,v) ∧ _)
  rw [run.protected_saturated_bundle a ha hSat v]

theorem CaseTwoPartition.stage_two_first_anchor
    (s : CaseTwoPartition M a b d m L r t η) (Q : M.PartialColouring k)
    (S : M.PartialColouring (k+f)) (i : Fin (k+f)) (E : Finset V)
    (hReg : M.IsRegularOfDegree d) (hk : k+f < d) (hSat : Q.graph.degree a = k)
    (hCover : S.CoversInternal s.part) (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hClear : ∀ v ∈ E, v ∈ s.partᶜ → (S.colouring.colourGraph i).degree v = 0)
    (hChoice : (Q.available.crossingSupport s.part).neighborFinset a ⊆ E ∨
      (s.partᶜ \ S.colouring.missingSet s.partᶜ i).card+f <
        (Q.available.crossingSupport s.part).degree a) :
    0 < S.available.degreeInto (S.colouring.missingSet s.partᶜ i) a := by
  have hAvail (v : V) : S.available.mult s(a,v) ≤ Q.available.mult s(a,v) :=
    Nat.sub_le_sub_left (hMono _) _
  rcases hChoice with hProtected | hLarge
  · apply S.first_anchor_mass_of_cleared_available_neighbours s.part E a d i
      s.centre_mem hReg hk hCover ?_ hClear
    intro v hv
    have hvA : v ∉ s.part := by
      intro hvA
      have hh := hCover a v (iff_of_true s.centre_mem hvA)
      change 0 < M.mult s(a,v)-S.graph.mult s(a,v) at hv
      omega
    apply hProtected
    exact (mem_neighborFinset _ a v).mpr ⟨hv.trans_le (hAvail v),by simp [s.centre_mem,hvA]⟩
  · apply S.first_anchor_mass_of_many_neighbours s.part a i s.centre_mem
    have hGrowth := MultiGraph.crossing_support_row_growth S.available Q.available s.part a hAvail
    have hQ := Q.available_degree a
    have hS := S.available_degree a
    have hDegree := S.colouring.degree_le_palette a
    omega

end OverfullWork.CMSBalancedCut
