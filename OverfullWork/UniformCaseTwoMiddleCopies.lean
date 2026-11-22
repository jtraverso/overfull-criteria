module

public import OverfullWork.CaseTwoMiddleCopies
public import OverfullWork.CaseTwoMiddleDegreeProfile
public import OverfullWork.CanonicalImageDegreeRange

@[expose] public section


/-! # Pay the middle-copy construction from the original source budgets

The source scale is fixed before the heavy cutoff and discrepancy.
Completed no-overfullness and the finite off-centre reserve are derived,
not added as premises at the uniform endpoint.
-/
namespace OverfullWork.CaseTwoMiddleScales
set_option maxHeartbeats 6000000

theorem small_budget (Q n d B : ℕ) (hQ : 8 ≤ Q) (hn : 64*Q ≤ n)
    (hd : n ≤ 2*d) (hB : B ≤ 6*(n/(4096*Q^2))+6) : 2*(B+1) ≤ d := by
  let k := n/(4096*Q^2)
  have hcoef : 128 ≤ 4096*Q^2 := by nlinarith only [hQ]
  have hk : 128*k ≤ n := (Nat.mul_le_mul_right k hcoef).trans (Nat.mul_div_le n _)
  change B ≤ 6*k+6 at hB
  omega

end OverfullWork.CaseTwoMiddleScales

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 12000000

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_middle_copies (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, P ≤ Q ∧ ∀ T : ℕ, 1 ≤ T → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          ∃ s : p.CaseTwoPartition P T η b,
            ∀ w, w ∉ s.part → b ≠ w → Nonempty (p.CaseTwoMiddleCopies s w) := by
  obtain ⟨P,hP,hPartitions⟩ := exists_uniform_case_two_partition.{u} ε hε
  obtain ⟨Q₀,hQ₀,N₀,hNo⟩ := above_half_small_centre_completion_no_overfull.{u} ε hε
  let Q := max P Q₀
  have hPQ : P ≤ Q := le_max_left _ _
  have h₀Q : Q₀ ≤ Q := le_max_right _ _
  have hQ : 8 ≤ Q := hP.trans hPQ
  refine ⟨P,hP,Q,hPQ,?_⟩
  intro T hT η hη
  obtain ⟨N₁,hN₁⟩ := hPartitions T hT η hη
  refine ⟨max N₁ (max N₀ (64*Q)),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  have hDivP : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*P^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hPQ 2)) (by positivity)
  have hDiv₀ : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h₀Q 2)) (by positivity)
  obtain ⟨s⟩ := hN₁ G c p (by omega) hdense (by omega) (by omega) b hab
  have hNoCompleted := hNo G c p (by omega) hcrit hdense (by omega) (by omega) hMin
  have hWeak : Fintype.card W ≤ 2*G.maxDegree := by
    have he : 0 ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hSmall := CaseTwoMiddleScales.small_budget Q (Fintype.card W) G.maxDegree B
    hQ (by omega) hWeak hB
  refine ⟨s,?_⟩
  intro w hw hbw
  exact s.exists_middle_copies hw hbw hNoCompleted hSmall

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_middle_profile (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, P ≤ Q ∧ ∀ T : ℕ, 1 ≤ T → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          ∃ s : p.CaseTwoPartition P T η b,
            ∀ w, w ∉ s.part → b ≠ w → ∃ r : p.CaseTwoMiddleCopies s w, ∀ v,
              |2*(r.graph.degree v:ℝ)-(G.maxDegree:ℝ)| ≤
                η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7 := by
  obtain ⟨P,hP,Q,hPQ,hConstruct⟩ := exists_uniform_case_two_middle_copies.{u} ε hε
  refine ⟨P,hP,Q,hPQ,?_⟩
  intro T hT η hη
  obtain ⟨N₀,hN₀⟩ := hConstruct T hT η hη
  refine ⟨max N₀ (64*Q),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  obtain ⟨s,hs⟩ := hN₀ G c p (by omega) hcrit hdense hB hK hMin b hab
  have hD := p.maxDegree_lt_image_order_at_source_scale Q (by omega) (by omega) hB hK
  refine ⟨s,?_⟩
  intro w hw hbw
  obtain ⟨r⟩ := hs w hw hbw
  exact ⟨r,fun v => r.degree_profile_at_cutoff hw (by omega) hT v⟩

end OverfullWork.NormalizedCanonicalCandidate
