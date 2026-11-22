module

public import OverfullWork.CompleteFirstAnchorConditions

@[expose] public section


/-! Choose the actual protected vertex required in the unique-heavy case. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b : Fin (p.pairIndex+1) × Bool}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoPartition.exists_first_anchor_exception
    (s : p.CaseTwoPartition P T η b) (τ : ℝ)
    (hCut : (((p.pairIndex+1)/T:ℕ):ℝ) < τ*(p.pairIndex+1:ℕ)/32) :
    ∃ w, w ∉ s.part ∧ b ≠ w ∧
      ∀ v, v ≠ p.centre → v ≠ b →
        τ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ) →
        (∀ u, u ≠ p.centre → u ≠ b →
          τ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,u):ℝ) → u=v) → v=w := by
  let heavy := fun v => v ≠ p.centre ∧ v ≠ b ∧
    τ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ)
  by_cases hOne : ∃ v, heavy v ∧ ∀ u, heavy u → u=v
  · obtain ⟨v,hv,hUnique⟩ := hOne
    have hLarge : (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) := by
      exact_mod_cast lt_trans hCut hv.2.2
    refine ⟨v,s.heavy_across v hv.2.1 hLarge,Ne.symm hv.2.1,?_⟩
    intro u huc hub hu _
    exact hUnique u ⟨huc,hub,hu⟩
  · have hSize : 2 ≤ s.partᶜ.card := by
      rw [s.card_compl]
      have hh := s.nonvacuous
      change 2*((p.pairIndex+1)/(1024*P)+2*(3*T+1)) ≤ p.pairIndex+1 at hh
      nlinarith [Nat.zero_le ((p.pairIndex+1)/(1024*P)),Nat.zero_le T]
    have hErase : (s.partᶜ.erase b).Nonempty := by
      apply card_pos.mp
      have hh := card_erase_add_one (mem_compl.mpr s.second_not_mem)
      omega
    obtain ⟨w,hw⟩ := hErase
    refine ⟨w,mem_compl.mp (mem_erase.mp hw).2,Ne.symm (mem_erase.mp hw).1,?_⟩
    intro v hvc hvb hv hUnique
    exact (hOne ⟨v,⟨hvc,hvb,hv⟩,fun u hu => hUnique u hu.1 hu.2.1 hu.2.2⟩).elim

end OverfullWork.NormalizedCanonicalCandidate
