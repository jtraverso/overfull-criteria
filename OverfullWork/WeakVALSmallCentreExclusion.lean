module

public import OverfullWork.WeakVALCanonicalNoOverfull
public import OverfullWork.NoncriticalCanonicalColouring

@[expose] public section


/-! The entire small-centre colouring endpoint under actual weak VAL.
The source need not be critical. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 24000000

theorem above_half_weak_val_small_centre_colourable (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        p.centre=(0,false) → G.EdgeColorable G.maxDegree := by
  obtain ⟨QN,hQN,NN,hNo⟩ := above_half_weak_val_completion_no_overfull.{u} ε hε
  obtain ⟨QC,hQC,NC,hCol⟩ := above_half_centred_colourable_of_completed_no_overfull.{u} ε hε
  let Q := max QN QC
  have hNQ : QN ≤ Q := le_max_left _ _
  have hCQ : QC ≤ Q := le_max_right _ _
  refine ⟨Q,hQC.trans hCQ,max NN NC,?_⟩
  intro W _ _ G _ B K c p hn hDense hB hK hWeak hMin hCentre
  have hDivN : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*QN^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNQ 2)) (by positivity)
  have hDivC : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*QC^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hCQ 2)) (by positivity)
  have hNoCompleted := hNo G c p (by omega) hDense (by omega) (by omega) hWeak hMin
  exact hCol G c p (by omega) hNoCompleted hDense (by omega) (by omega) hMin hCentre

theorem above_half_weak_val_small_centre_source_colourable (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K),
        N ≤ Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        G.EdgeColorable G.maxDegree := by
  obtain ⟨QC,hQC,NC,hColour⟩ := above_half_weak_val_small_centre_colourable.{u} ε hε
  obtain ⟨QM,hQM,NM,hMargins⟩ := PaperFirstRoundAboveHalf.uniform_margins ε hε
  let Q := max QC QM
  have hCQ : QC ≤ Q := le_max_left _ _
  have hMQ : QM ≤ Q := le_max_right _ _
  refine ⟨Q,hQC.trans hCQ,max NC NM,?_⟩
  intro W _ _ G _ B K c hn hDense hNo hB hK hWeak hMin
  have hDivC : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*QC^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hCQ 2)) (by positivity)
  have hDivM : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*QM^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMQ 2)) (by positivity)
  have hMargin := (hMargins (Fintype.card W) G.maxDegree (by omega) hDense).1
  have hParts := card_add_card_compl c.set
  have hY := c.complement_small
  obtain ⟨p,hCentre⟩ := exists_centred_candidate G c hNo (by omega) hMin
  exact hColour G c p (by omega) hDense (by omega) (by omega) hWeak hMin hCentre

end OverfullWork.NormalizedCanonicalCandidate
