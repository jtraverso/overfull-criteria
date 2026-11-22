module

public import OverfullWork.FirstAnchorLargeBundles

@[expose] public section


/-! CMS Step 4: the complete Stage I case split for the first anchor.

The unique-large-bundle vertex is chosen as the protected initial vertex.
All bundle reserves are derived from the completed seed and source errors.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.stage_one_first_anchor_mass
    (r : p.CaseTwoMiddleCopies s w) (Q : p.completed.PartialColouring r.seedPalette)
    (q h : ℕ) (C : (Q.available.internalPart s.part).EdgeColoring (q+3*h))
    (S : p.completed.PartialColouring (r.seedPalette+(q+3*h))) (j : Fin q) (ρ : ℝ)
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hFilled : Q.graph.degree p.centre=r.seedPalette)
    (hRow : ∀ v ∈ s.partᶜ, r.count v ≤ Q.graph.mult s(p.centre,v) ∧
      Q.graph.mult s(p.centre,v) ≤ r.count v+Nat.ceil r.seedError)
    (hCover : S.CoversInternal s.part)
    (hSame : S.colouring.colourGraph (Fin.natAdd r.seedPalette (Fin.castAdd (3*h) j))=
      C.colourGraph (Fin.castAdd (3*h) j))
    (hUnit : (C.colourGraph (Fin.castAdd (3*h) j)).edgesWithin s.partᶜ=1)
    (hProtected : (Q.available.internalPart s.part).mult s(b,w)=0)
    (hw : w ∉ s.part) (hbw : b ≠ w)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hCentre : p.centre=(0,false)) (hSecond : b=(0,true))
    (hq : (q:ℝ) < 5*r.seedError)
    (hError : r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (hCap : (h:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/1024)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (hNonheavy : (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree)
    (hChoice : ∀ v, v ≠ p.centre → v ≠ b →
      ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ) →
      (∀ u, u ≠ p.centre → u ≠ b →
        ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,u):ℝ) → u=v) → v=w) :
    0 < S.available.degreeInto
      (S.colouring.missingSet s.partᶜ (Fin.natAdd r.seedPalette (Fin.castAdd (3*h) j))) p.centre := by
  let i := Fin.natAdd r.seedPalette (Fin.castAdd (3*h) j)
  have hMissing : S.colouring.missingSet s.partᶜ i=C.missingSet s.partᶜ (Fin.castAdd (3*h) j) := by
    ext v
    simp only [MultiGraph.EdgeColoring.missingSet,mem_filter]
    rw [hSame]
  have hCard : (s.partᶜ\S.colouring.missingSet s.partᶜ i).card=2 := by
    rw [hMissing]
    have hm := C.internal_missing_count_compl s.part (Fin.castAdd (3*h) j)
    have hc := card_sdiff_add_card_eq_card (show C.missingSet s.partᶜ (Fin.castAdd (3*h) j) ⊆ s.partᶜ from filter_subset _ _)
    rw [hUnit] at hm
    omega
  have hRowUpper := fun v hv => (hRow v hv).2
  have hFree := r.large_bundle_free_in_fresh_state Q q h S ρ hMono hFilled hRowUpper hw hq hError hCap hLoss
  have hCompare : ∀ v, v ≠ p.centre → p.completed.mult s(p.centre,v) ≤ p.completed.mult s(p.centre,b)+B+c.setᶜ.card := by
    intro v hv
    simpa only [←hSecond] using p.first_ordinary_bundle_dominates hCentre v hv
  let Z := univ.filter (fun v => v ≠ p.centre ∧ v ≠ b ∧
    ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ))
  by_cases hEmpty : Z=∅
  · have hLight : ∀ v ∈ s.partᶜ, v ≠ b → (p.completed.mult s(p.centre,v):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/32 := by
      intro v hv hvb
      by_contra! hh
      have hvc : v ≠ p.centre := fun he => (mem_compl.mp hv) (he ▸ s.centre_mem)
      have hz : v ∈ Z := mem_filter.mpr ⟨mem_univ _,hvc,hvb,hh⟩
      rw [hEmpty] at hz
      exact notMem_empty v hz
    have hBound := r.fresh_second_bundle_upper Q (q+3*h) S hMono
      (hRow b (mem_compl.mpr s.second_not_mem)).1 hw hD hT
    have hBasic := r.seed_error_basics
    have hρm : 0 ≤ ρ*(p.pairIndex+1:ℕ) := by linarith
    apply S.first_anchor_mass_of_two_light_blockers s.part p.centre b G.maxDegree i
      (ρ*(p.pairIndex+1:ℕ)/32) ((p.completed.mult s(p.centre,b):ℝ)/2+r.seedError)
      s.centre_mem p.completion.regular hCover (by omega) (by positivity) (by linarith) hLight
    have hk := r.seed_palette_lt_half_add_error
    have hReserve : (r.seedPalette+(q+3*h):ℕ)=r.seedPalette+q+3*h := by omega
    rw [hReserve]
    push_cast
    simp only [Nat.cast_add,Nat.cast_one] at hError hCap hNonheavy
    linarith
  have hNonempty : Z.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨v,hv⟩ := hNonempty
  have hvData := (mem_filter.mp hv).2
  have hvAcross := r.large_bundle_across ρ hError v hvData.2.1 hvData.2.2
  have hvFree : 0 < S.available.mult s(p.centre,v) := by
    apply hFree v hvAcross
    have hl : (0:ℝ) ≤ (B+c.setᶜ.card:ℕ) := Nat.cast_nonneg _
    linarith [hvData.2.2]
  have hbFree : 0 < S.available.mult s(p.centre,b) := by
    apply hFree b (mem_compl.mpr s.second_not_mem)
    have hc : (p.completed.mult s(p.centre,v):ℝ) ≤ (p.completed.mult s(p.centre,b):ℝ)+(B+c.setᶜ.card:ℕ) := by
      have hc : p.completed.mult s(p.centre,v) ≤ p.completed.mult s(p.centre,b)+(B+c.setᶜ.card) := by
        have hh := hCompare v hvData.1
        omega
      exact_mod_cast hc
    linarith [hvData.2.2]
  by_cases hUnique : ∀ u ∈ Z, u=v
  · have hvw : v=w := hChoice v hvData.1 hvData.2.1 hvData.2.2
      (fun u huc hub hu => hUnique u (mem_filter.mpr ⟨mem_univ _,huc,hub,hu⟩))
    have hZero : Q.available.mult s(b,w)=0 := by
      rw [MultiGraph.internalPart_mult,if_pos (iff_of_false s.second_not_mem hw)] at hProtected
      exact hProtected
    have hMissingPair := C.unit_internal_pair_has_missing (Fin.castAdd (3*h) j) b w
      (mem_compl.mpr s.second_not_mem) (mem_compl.mpr hw) hbw hUnit hZero
    rw [←hMissing] at hMissingPair
    rcases hMissingPair with hbMissing|hwMissing
    · exact S.first_anchor_mass_of_missing_candidate s.part p.centre b i hbMissing hbFree
    · exact S.first_anchor_mass_of_missing_candidate s.part p.centre w i hwMissing (hvw ▸ hvFree)
  push_neg at hUnique
  obtain ⟨u,hu,huv⟩ := hUnique
  have huData := (mem_filter.mp hu).2
  have huAcross := r.large_bundle_across ρ hError u huData.2.1 huData.2.2
  have huFree : 0 < S.available.mult s(p.centre,u) := by
    apply hFree u huAcross
    have hl : (0:ℝ) ≤ (B+c.setᶜ.card:ℕ) := Nat.cast_nonneg _
    linarith [huData.2.2]
  have hSome : b ∈ S.colouring.missingSet s.partᶜ i ∨
      v ∈ S.colouring.missingSet s.partᶜ i ∨ u ∈ S.colouring.missingSet s.partᶜ i := by
    by_contra! hh
    have hSub : ({b,v,u} : Finset (Fin (p.pairIndex+1) × Bool)) ⊆
        s.partᶜ\S.colouring.missingSet s.partᶜ i := by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨mem_sdiff.mpr ⟨mem_compl.mpr s.second_not_mem,hh.1⟩,
        mem_sdiff.mpr ⟨hvAcross,hh.2.1⟩,mem_sdiff.mpr ⟨huAcross,hh.2.2⟩⟩
    have hThree : ({b,v,u} : Finset (Fin (p.pairIndex+1) × Bool)).card=3 := by
      simp [Ne.symm hvData.2.1,Ne.symm huData.2.1,Ne.symm huv]
    have hc := card_le_card hSub
    omega
  rcases hSome with hh|hh|hh
  · exact S.first_anchor_mass_of_missing_candidate s.part p.centre b i hh hbFree
  · exact S.first_anchor_mass_of_missing_candidate s.part p.centre v i hh hvFree
  · exact S.first_anchor_mass_of_missing_candidate s.part p.centre u i hh huFree

end OverfullWork.NormalizedCanonicalCandidate
