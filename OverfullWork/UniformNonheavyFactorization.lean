module

public import OverfullWork.CanonicalNonheavyFactorization

@[expose] public section


/-! Uniform Case 2 factorization, including construction of the partition and parameters. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 48000000

theorem above_half_small_centre_nonheavy_factorization (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ Qs : ℕ, 8 ≤ Qs ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Qs^2))+6 → K ≤ Fintype.card W/(4096*Qs^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        p.centre=(0,false) →
        (p.completed.mult s(p.centre,(0,true)):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree →
        ∃ C : p.completed.EdgeColoring G.maxDegree, C.IsFactorization := by
  obtain ⟨P,hP,hPartition⟩ := exists_uniform_case_two_partition.{u} ε hε
  obtain ⟨ell,δ,Q₀,hδ,hPQ₀,hHall⟩ := exists_uniform_case_two_hall_completion.{u} ε hε P hP ρ hρ
  obtain ⟨T,hT⟩ := exists_nat_gt (max (16:ℝ) (4/δ))
  have hT16 : 16 ≤ T := by exact_mod_cast (le_max_left _ _).trans hT.le
  have hTδ : 4 ≤ δ*(T:ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hT)
    linarith
  let η := min (δ/4) (1/32)
  have hη : 0 < η := by dsimp only [η];positivity
  obtain ⟨NHall,hNHall⟩ := hHall T hT16 hTδ η hη.le (le_refl _)
  obtain ⟨NPart,hNPart⟩ := hPartition T (by omega) η hη
  refine ⟨Q₀,hP.trans hPQ₀,max NHall NPart,?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin hCentre hGap
  have hDivP : Fintype.card W/(4096*Q₀^2) ≤ Fintype.card W/(4096*P^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPQ₀ 2)) (by positivity)
  let b : Fin (p.pairIndex+1) × Bool := (0,true)
  have hab : p.centre ≠ b := by simp [hCentre,b]
  obtain ⟨s⟩ := hNPart G c p (by omega) hdense (by omega) (by omega) b hab
  obtain ⟨a⟩ := hNHall G c p (by omega) hcrit hdense hB hK hMin hCentre b rfl s hGap
  exact a.exists_factorization hP hρ

end OverfullWork.NormalizedCanonicalCandidate
