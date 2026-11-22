module

public import OverfullWork.NoncriticalNonheavyFactorization
public import OverfullWork.NoncriticalHeavyFactorization
public import OverfullWork.InitialAnchorCaseSplit
public import OverfullWork.PaperFirstRoundAboveHalf

@[expose] public section


/-! Colour the actual candidate from its structural no-overfull property.
Both heavy and nonheavy factorizations are constructed; source criticality
is absent from the interface. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 48000000

theorem above_half_centred_colourable_of_completed_no_overfull (ε : ℝ) (hε : 0 < ε) :
    ∃ Qs : ℕ, 8 ≤ Qs ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → (¬p.completed.HasOverfullSubset G.maxDegree) →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Qs^2))+6 → K ≤ Fintype.card W/(4096*Qs^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        p.centre=(0,false) → G.EdgeColorable G.maxDegree := by
  obtain ⟨H,hH,NH,hHeavy⟩ := above_half_heavy_factorization_of_completed_no_overfull.{u} ε hε
  let ρ : ℝ := 1/(64*(H:ℝ))
  have hρ : 0 < ρ := by dsimp only [ρ];positivity
  obtain ⟨Q₀,hQ₀,N₀,hNonheavy⟩ := above_half_nonheavy_factorization_of_completed_no_overfull.{u} ε ρ hε hρ
  let Qs := max H Q₀
  have hHQ : H ≤ Qs := le_max_left _ _
  have h₀Q : Q₀ ≤ Qs := le_max_right _ _
  refine ⟨Qs,hQ₀.trans h₀Q,max NH N₀,?_⟩
  intro W _ _ G _ B K c p hn hNoCompleted hdense hB hK hMin hCentre
  have hDivH : Fintype.card W/(4096*Qs^2) ≤ Fintype.card W/(4096*H^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHQ 2)) (by positivity)
  have hDiv₀ : Fintype.card W/(4096*Qs^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₀Q 2)) (by positivity)
  let b : Fin (p.pairIndex+1) × Bool := (0,true)
  have hab : p.centre ≠ b := by simp [hCentre,b]
  by_cases hCase : G.maxDegree-p.completed.mult s(p.centre,b) ≤ Fintype.card W/(64*H)
  · obtain ⟨C⟩ := hHeavy G c p (by omega) hNoCompleted hdense (by omega) (by omega) hMin b hab hCase
    exact p.source_colourable_of_completed C
  · have hGap := p.nonheavy_gap_at_source_cutoff H (by omega) b (by omega)
    obtain ⟨C,_⟩ := hNonheavy G c p (by omega) hNoCompleted hdense (by omega) (by omega) hMin hCentre hGap
    exact p.source_colourable_of_completed C

end OverfullWork.NormalizedCanonicalCandidate
