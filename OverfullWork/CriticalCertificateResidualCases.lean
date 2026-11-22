module

public import OverfullWork.TripleSparseBudgetMargin

@[expose] public section


/-! At an original critical source the second-low branch is excluded.

This classification is not asserted for noncritical normalized states:
their class-two property alone does not authorize the CCJS argument.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 48000000

theorem above_half_critical_certificate_residual_cases (ε : ℝ) (hε : 0 < ε) :
    ∃ Qs : ℕ, 8 ≤ Qs ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G → (∀ v, 0 < G.degree v) →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) → ¬G.HasOverfullSubgraph →
        let k := Fintype.card W/(4096*Qs^2)
        ∀ c : Certificate G (6*k+6) (k+1),
          ∃ x ∈ c.set, (∀ v ∈ c.set, G.degree x ≤ G.degree v) ∧
            G.degree x < (∑ y ∈ c.setᶜ, G.degree y) ∧
            ((∀ v ∈ c.set, G.degree v=G.maxDegree) ∨
              Nonempty (PaperFirstRoundAboveHalf.CleanStep G c x)) := by
  obtain ⟨Q₀,hQ₀,N₀,hExclude⟩ := above_half_small_centre_critical_exclusion.{u} ε hε
  obtain ⟨QM,hQM,NM,hMargins⟩ := PaperFirstRoundAboveHalf.uniform_margins ε hε
  let Qs := max Q₀ (2*QM)
  have h₀Q : Q₀ ≤ Qs := le_max_left _ _
  have hMQ2 : 2*QM ≤ Qs := le_max_right _ _
  have hMQ : QM ≤ Qs := by omega
  refine ⟨Qs,hQ₀.trans h₀Q,max N₀ (max NM (4096*QM^2)),?_⟩
  intro W _ _ G _ hn hcrit hActive hdense hNo
  dsimp only
  intro c
  have hDiv₀ : Fintype.card W/(4096*Qs^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₀Q 2)) (by positivity)
  have hDivM : Fintype.card W/(4096*Qs^2) ≤ Fintype.card W/(4096*QM^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMQ 2)) (by positivity)
  have hM := hMargins (Fintype.card W) G.maxDegree (by omega) hdense
  have hNotMin : ¬∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x := by
    intro hh
    exact hExclude G c (by omega) hcrit hdense hNo (by omega) (by omega) hh
  have hNonempty : c.set.Nonempty := by
    apply card_pos.mp
    obtain ⟨m,hm⟩ := c.odd
    omega
  obtain ⟨x,hx,hMin⟩ := c.set.exists_min_image (fun v => G.degree v) hNonempty
  have hLarge : G.degree x < ∑ y ∈ c.setᶜ, G.degree y := by
    by_contra! hh
    exact hNotMin (fun v hv => hh.trans (hMin v hv))
  refine ⟨x,hx,hMin,hLarge,?_⟩
  by_cases hxMax : G.degree x=G.maxDegree
  · left
    intro v hv
    have hlo := hMin v hv
    have hhi := G.degree_le_maxDegree v
    omega
  · right
    have hTriple := SparseBudgetMargin.triple_budget_of_coarse_margin
      (Fintype.card W) G.maxDegree QM Qs (6*(Fintype.card W/(4096*Qs^2))+6)
      hQM hMQ2 (by omega) (le_refl _) hM.1
    apply PaperFirstRoundAboveHalf.exists_clean_step G hcrit c x hx hLarge
      (lt_of_le_of_ne (G.degree_le_maxDegree x) hxMax) hNo
    · intro v hv hvx
      exact no_second_low_in_critical_large_centre G c hcrit hActive hTriple x hx hLarge v hv hvx
    · have hy := c.complement_small
      have hh := hM.1
      omega
    · have hh := hM.2.1
      omega
    · have hh := hM.2.2
      omega

end OverfullWork.NormalizedCanonicalCandidate
