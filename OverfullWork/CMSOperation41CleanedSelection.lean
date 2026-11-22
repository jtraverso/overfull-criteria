module

public import OverfullWork.CMSOperation41StepSelection
public import OverfullWork.CMSOperation41InitialHost

@[expose] public section


/-! The independent Step 1 selects an actual cleaned graph, updates
the virtual record and restricts the exceptional sets to its support. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasCleanedTrimmingSelection (S : SimpleGraph V) (initial current W : Finset V)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (d floor testBudget : ℕ)
    (used : ℕ → Finset V) (j cap : ℕ) : Prop :=
    let degree := auxiliaryPhysicalDegree S initial P credit j
    ∃ T : SimpleGraph V,
      let cleaned := auxiliaryPhysicalDegree T initial P credit j
      let support := univ.filter (fun v => 0 < cleaned v)
      let exceptional := current ∩ support
      let active := W.filter (fun w => 0 < T.degree w)
      DeletionRun W S T ∧ T ≤ S ∧ active ⊆ exceptional ∧ initialᶜ ⊆ support ∧
      (∀ v,(sdiff S T).degree v ≤ W.card) ∧
      (∀ v,cleaned v+(sdiff S T).degree v = degree v) ∧
      (HasAlmostOverfullRecord support d testBudget cleaned ∨
        Nonempty (TrimmingStepSelection T initial exceptional active cleaned d floor used j cap) ∨
        (active = ∅ ∧ ∃ A ⊆ exceptional,1 ≤ A.card ∧ A.card ≤ 2 ∧
          (Even support.card ↔ A.card = 2) ∧
          (∀ z ∈ exceptional,cleaned z < floor+2) ∧
          Odd (support \ exceptional).card ∧
          (∑ v ∈ support \ exceptional,(d-cleaned v)) ≤ 1 ∧
          ((Even exceptional.card ∧ ∃ a ∈ exceptional,A = {a} ∧
            ∀ v ∈ exceptional,cleaned a ≤ cleaned v) ∨
            (Odd exceptional.card ∧ ∃ a ∈ exceptional,∃ b ∈ exceptional,a ≠ b ∧ A = {a,b} ∧
              (∀ v ∈ exceptional,cleaned a ≤ cleaned v) ∧
              ∀ v ∈ exceptional,v ≠ a → cleaned b ≤ cleaned v))))

set_option maxHeartbeats 2400000 in
/-- A single independent cleanup followed by Step 2, with the stopping
test evaluated on the corrected record. Its input degree and projection
reserves are measured before the cleanup. -/
theorem exists_cleaned_trimming_selection (S : SimpleGraph V)
    (initial current W : Finset V) (hCurrent : current ⊆ initial) (hW : W ⊆ current)
    (hInd : S.IsIndepSet (W : Set V))
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (d floor testBudget : ℕ)
    (hD : 2 ≤ d) (hSize : 4 ≤ initialᶜ.card) (hTest : 1 ≤ testBudget)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap) :
    let degree := auxiliaryPhysicalDegree S initial P credit j
    (∀ v,degree v ≤ d) →
    (∀ v ∈ current,degree v+2 ≤ d) →
    (∀ v,v ∉ initial → W.card+2 ≤ degree v) →
    (∀ v ∈ initial,v ∉ W → 0 < S.degree v →
      5*initial.card+k+4+W.card ≤ S.degree v) →
    HasCleanedTrimmingSelection S initial current W P credit d floor testBudget used j cap := by
  intro degree hBound hDef hCore hReserve
  unfold HasCleanedTrimmingSelection
  obtain ⟨T,hClean,hLe,hIndependent,hStrict⟩ := exists_independent_active_cleanup S W hInd
  let cleaned := auxiliaryPhysicalDegree T initial P credit j
  let support := univ.filter (fun v => 0 < cleaned v)
  let exceptional := current ∩ support
  let active := W.filter (fun w => 0 < T.degree w)
  have hLoss (v : V) : (sdiff S T).degree v ≤ W.card := by
    have hC : T.degree v+(sdiff S T).degree v = S.degree v := by
      simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le S T hLe v
    have hBound := independent_auxiliary_preprocessing_degree_loss hClean hInd v
    omega
  have hCompare (v : V) : cleaned v = degree v-(sdiff S T).degree v :=
    auxiliary_physical_degree_after_cleanup S T initial P credit j hLe v
  have hExact (v : V) (hv : v ∈ initial) : cleaned v = T.degree v := by
    simp only [cleaned,auxiliaryPhysicalDegree,if_pos hv]
  have hAdd (v : V) : cleaned v+(sdiff S T).degree v = degree v := by
    by_cases hv : v ∈ initial
    · have hC : T.degree v+(sdiff S T).degree v = S.degree v := by
        simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le S T hLe v
      rw [hExact v hv]
      simpa only [degree,auxiliaryPhysicalDegree,if_pos hv] using hC
    · have h := hCore v hv
      have hl := hLoss v
      have he := hCompare v
      omega
  have hSub : active ⊆ exceptional := by
    intro v hv
    have ⟨hw,hp⟩ := mem_filter.mp hv
    have hc := hW hw
    exact mem_inter.mpr ⟨hc,mem_filter.mpr ⟨mem_univ _,by rwa [hExact v (hCurrent hc)]⟩⟩
  have hCoreSupport : initialᶜ ⊆ support := by
    intro v hv
    have h := hCore v (mem_compl.mp hv)
    have hl := hLoss v
    have he := hAdd v
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  refine ⟨T,hClean,hLe,hSub,hCoreSupport,hLoss,hAdd,?_⟩
  by_cases hStop : HasAlmostOverfullRecord support d testBudget cleaned
  · exact Or.inl hStop
  right
  have hBound' (v : V) : cleaned v ≤ d := by
    rw [hCompare]
    exact (Nat.sub_le _ _).trans (hBound v)
  have hDef' (v : V) (hv : v ∈ exceptional) : cleaned v+2 ≤ d := by
    have h := hDef v (mem_inter.mp hv).1
    have he := hAdd v
    omega
  refine exists_trimming_step_selection T initial exceptional active (inter_subset_left.trans hCurrent)
    hSub (fun w hw => (mem_filter.mp hw).2) (Or.inl ⟨hIndependent,hStrict⟩)
    cleaned d floor testBudget hD hBound' hExact hDef' hSize used j cap k budget
    hCap hUsed hTotal inter_subset_right hCoreSupport hTest hStop ?_
  intro v hv hna hp
  have hnW : v ∉ W := fun hw => hna (mem_filter.mpr ⟨hw,hp⟩)
  have hS : T.degree v ≤ S.degree v := degree_le_of_le hLe
  have hBefore := hReserve v hv hnW (hp.trans_le hS)
  have hBoundT := independent_auxiliary_preprocessing_degree_loss hClean hInd v
  omega

set_option maxHeartbeats 1800000 in
/-- Initialize Step 1 and the selector with an empty packing history.
The initial density and small exceptional set pay all degree reserves. -/
theorem exists_initial_cleaned_trimming_selection
    (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/16)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (testBudget : ℕ) (hTest : 1 ≤ testBudget) :
    let n := Fintype.card V
    let initial := initialExceptionalSet G η
    let W := initialLowSet G η
    let cap := ⌊η*(n:ℝ)⌋₊
    let floor := ⌊(G.maxDegree:ℝ)/3-η*(n:ℝ)⌋₊
    12 ≤ η*(n:ℝ) → 24*η*(n:ℝ) ≤ (G.maxDegree:ℝ) →
    (initial.card:ℝ) ≤ η^2*(n:ℝ) →
    HasCleanedTrimmingSelection G initial initial W (fun _ => ⊥) (fun _ _ => 2)
      G.maxDegree floor testBudget (fun _ => ∅) 0 cap := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v))
  intro n initial W cap floor hn hD hFew
  have hW : W ⊆ initial := filter_subset _ _
  have hWC := card_le_card hW
  have hInd : G.IsIndepSet (W : Set V) := initial_low_set_independent G η hη hVAL
  have hCap : 0 < cap := by
    have h₁ : 1 ≤ cap := Nat.le_floor (by simpa using (show (1:ℝ) ≤ η*(n:ℝ) by linarith only [hn]))
    omega
  have hDegree : 2 ≤ G.maxDegree := by
    exact_mod_cast (show (2:ℝ) ≤ G.maxDegree by linarith only [hD,hn])
  have hNearlyAll : (initial.card:ℝ) ≤ (n:ℝ)/16 := by
    have hProd := mul_le_mul_of_nonneg_right hSmall (mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n))
    have hProd' := mul_le_mul_of_nonneg_right hSmall (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hFew,hProd,hProd']
  have hCard : (initial.card:ℝ)+(initialᶜ.card:ℝ) = n := by
    exact_mod_cast card_add_card_compl initial
  have hCore : 4 ≤ initialᶜ.card := by
    have hN := mul_le_mul_of_nonneg_right hSmall (Nat.cast_nonneg (α := ℝ) n)
    exact_mod_cast (show (4:ℝ) ≤ initialᶜ.card by linarith only [hCard,hNearlyAll,hN,hn])
  have hRoom : 5*initial.card+cap+4+(4*initial.card+2) ≤ floor :=
    cms_projection_margin_after_trimming_losses n G.maxDegree initial.card η hη hSmall hn hD hFew
  have hRead (v : V) : auxiliaryPhysicalDegree G initial (fun _ => ⊥) (fun _ _ => 2) 0 v =
      G.degree v := by
    simp [auxiliaryPhysicalDegree]
  refine exists_cleaned_trimming_selection G initial initial W Subset.rfl hW hInd
    (fun _ => ⊥) (fun _ _ => 2) G.maxDegree floor testBudget hDegree hCore hTest
    (fun _ => ∅) 0 cap cap 0 hCap (by simp) (by simp) ?_ ?_ ?_ ?_
  · intro v
    rw [hRead]
    exact G.degree_le_maxDegree v
  · intro v hv
    rw [hRead]
    have hDef := (mem_filter.mp hv).2
    exact_mod_cast (show (G.degree v:ℝ)+2 ≤ G.maxDegree by linarith only [hDef,hn])
  · intro v hv
    rw [hRead]
    have hDef : (G.maxDegree:ℝ)-G.degree v ≤ η*(n:ℝ) := by
      by_contra! h
      exact hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hWC' : (W.card:ℝ) ≤ initial.card := by exact_mod_cast hWC
    have hMargin := mul_le_mul_of_nonneg_right hSmall (mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n))
    have hWsmall : (W.card:ℝ) ≤ η*(n:ℝ)/16 := by nlinarith only [hWC',hFew,hMargin]
    exact_mod_cast (show (W.card:ℝ)+2 ≤ G.degree v by linarith only [hDef,hWsmall,hD,hn])
  · intro v hv hNot _
    have hV : (G.maxDegree:ℝ)/3-η*(n:ℝ) ≤ G.degree v := by
      by_contra! h
      exact hNot (mem_filter.mpr ⟨hv,h⟩)
    have hFloor : floor ≤ G.degree v := Nat.floor_le_of_le hV
    omega

end OverfullWork.CMSTrimmingRound
