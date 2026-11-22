module

public import OverfullWork.UniformHallCompletionData

@[expose] public section


/-! The existing Case 2 completion with the actual no-overfull property
as input. Criticality was used only to establish that property. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 48000000

theorem exists_uniform_case_two_hall_completion_of_no_overfull
    (ε : ℝ) (hε : 0 < ε) (P : ℕ) (hP : 8 ≤ P) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ell : ℕ, ∃ δ : ℝ, ∃ Qs : ℕ, 0 < δ ∧ P ≤ Qs ∧
      ∀ T : ℕ, 16 ≤ T → 4 ≤ δ*(T:ℝ) → ∀ η : ℝ, 0 ≤ η → η ≤ min (δ/4) (1/32) →
        ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
          (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
          (c : Certificate G B K) (p : Candidate c),
          N ≤ Fintype.card W → (¬p.completed.HasOverfullSubset G.maxDegree) →
          ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
          B ≤ 6*(Fintype.card W/(4096*Qs^2))+6 → K ≤ Fintype.card W/(4096*Qs^2)+1 →
          (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
          p.centre=(0,false) → ∀ b : Fin (p.pairIndex+1) × Bool, b=(0,true) →
          ∀ s : p.CaseTwoPartition P T η b,
            (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree →
            Nonempty (p.CaseTwoHallCompletion s ell ρ) := by
  let τ := FirstAnchorScale.rate P ρ
  have hτ : 0 < τ := FirstAnchorScale.rate_pos P hP ρ hρ
  obtain ⟨ell,δ₀,Q₀,hδ₀,hPQ₀,hSource⟩ := exists_uniform_case_two_seed_completion_with_protected_set.{u} P hP τ hτ
  let Qs := Q₀
  let δ := min δ₀ (τ/10000)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδτ : δ ≤ τ/10000 := min_le_right _ _
  have h₀Qs : Q₀ ≤ Qs := le_refl _
  have hPQs : P ≤ Qs := hPQ₀.trans h₀Qs
  refine ⟨ell,δ,Qs,hδ,hPQs,?_⟩
  intro T hT hTδ η hη₀ hη
  have hTδ₀ : 4 ≤ δ₀*(T:ℝ) := hTδ.trans (mul_le_mul_of_nonneg_right hδ₀le (Nat.cast_nonneg _))
  have hη' : η ≤ min (δ₀/4) (1/32) := le_min ((le_min_iff.mp hη).1.trans (by linarith)) (le_min_iff.mp hη).2
  obtain ⟨N₀,hN₀⟩ := hSource T hT hTδ₀ η hη₀ hη'
  refine ⟨max N₀ (64*Qs),?_⟩
  intro W _ _ G _ B K c p hn hNoCompleted hdense hB hK hMin hCentre b hSecond s hNonheavy
  have hnQs : 64*Qs ≤ Fintype.card W := by omega
  have hWeak : Fintype.card W ≤ 2*G.maxDegree := by
    have he : 0 ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hDiv₀ : Fintype.card W/(4096*Qs^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₀Qs 2)) (by
      have hh : 0 < Q₀ := by omega
      positivity)
  have hSmall := CaseTwoMiddleScales.small_budget Qs (Fintype.card W) G.maxDegree B (by omega) hnQs hWeak hB
  have hHalf := p.image_half_order_le_delta hWeak
  have hImage := p.maxDegree_lt_image_order_at_source_scale Qs (by omega) hnQs hB hK
  have hD : G.maxDegree ≤ 3*(p.pairIndex+1) := by omega
  have hCut := FirstAnchorScale.threshold_at_source_cutoff T (p.pairIndex+1) (by omega) δ τ hτ hδτ hTδ
  obtain ⟨w,hw,hbw,hChoice⟩ := s.exists_first_anchor_exception τ hCut
  obtain ⟨r⟩ := s.exists_middle_copies hw hbw hNoCompleted hSmall
  have hGap : (p.completed.mult s(p.centre,b):ℝ)+τ*(p.pairIndex+1:ℕ) ≤ G.maxDegree := by
    have hh := mul_le_mul_of_nonneg_right (FirstAnchorScale.rate_le_gap P ρ)
      (show (0:ℝ) ≤ (p.pairIndex+1:ℕ) from Nat.cast_nonneg _)
    linarith
  obtain ⟨R,Q,h,n,t,budget,run,hFactors,hCap,hCapSmall,hError,hCapRho,hErrorRho,hLoss,hOrder,hRatio,
      hRow,hCross,hOrdinary,hCentreZero,hProtected,hResidue,hScalars,hFixed⟩ :=
    hN₀ G c p (by omega) hWeak (by omega) (by omega) hCentre b hSecond s w hw hbw r
      r.anchorClearSet r.anchorClearSet_card hGap
  obtain ⟨q,hCount,C,hBalance,hPalette,hCover,hOccupied,hAnchors⟩ :=
    budget.exists_bounded_complete_residue_anchor_conditions run hFactors hCap hCentreZero hProtected hHalf hD
      hP (by omega) hw hbw hCentre hSecond ρ hρ hGap hError hCapSmall hErrorRho hCapRho hLoss hOrder hRatio hRow hCross hChoice
  obtain ⟨sc,hsc⟩ := hScalars
  exact ⟨{
    exception := w, exception_across := hw, exception_ne := hbw, middle := r,
    initial := R, seed := Q, cap := h, rounds := n, steps := t, budget := budget,
    run := run, factors := hFactors, residue_cap := hCap, fresh := q, fresh_bound := hCount,
    palette := C, balance := hBalance, palette_lt := hPalette, covers := hCover, anchors := hAnchors,
    centre_id := hCentre, second_id := hSecond, half_order := hHalf,
    error_rate := hErrorRho, cap_rate := hCapRho, loss_rate := hLoss, large_order := hOrder,
    ordinary_deleted := hOrdinary, robust_rate := sc.robust_rate, window := sc.seed_window,
    occupied := hOccupied
  }⟩

end OverfullWork.NormalizedCanonicalCandidate
