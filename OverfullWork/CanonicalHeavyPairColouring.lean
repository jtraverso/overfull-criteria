module

public import OverfullWork.CanonicalHeavyPairPeeling
public import OverfullWork.HeavyPairFactorizationScales

@[expose] public section


/-! # Actual Delta-colouring in the uniform heavy-pair small-centre branch

All layers, the ordinary residual factorization, their colourings, and
all numeric reserves are constructed. The final theorem chooses its
source scale before the graph. The nonheavy colouring case and the
other terminal branches of G2 are not asserted here.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun HeavyPairBoundary IndependentSetIdentification
open Gate8J2I
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

theorem Candidate.heavy_pair_colourable_at_source_scale (p : Candidate c)
    (C Q : ℕ) (hC : 4000 ≤ C) (hQ : 2 ≤ Q) (hCQ : C ≤ Q)
    (hAQ : (10:ℕ)^24*C^6 ≤ Q) (hn : 64*Q ≤ Fintype.card V)
    (hdenseQ : (Q+2)*Fintype.card V ≤ 2*Q*G.maxDegree)
    (hdenseC : (C+128)*Fintype.card V ≤ 2*C*G.maxDegree)
    (hB : B ≤ 6*(Fintype.card V/(4096*Q^2))+6)
    (hK : K ≤ Fintype.card V/(4096*Q^2)+1)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (hNo : ¬ p.completed.HasOverfullSubset G.maxDegree)
    (hHeavy : G.maxDegree-p.completed.mult s(p.centre,b) ≤ Fintype.card V/(64*Q)) :
    Nonempty (p.completed.EdgeColoring G.maxDegree) := by
  obtain ⟨peel⟩ := p.heavy_pair_peeling_at_source_scale Q hQ hn hdenseQ hB hK b hab hNo hHeavy
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : Fintype.card V+1 = 2*(p.pairIndex+1)+c.setᶜ.card := by omega
  obtain ⟨hsize,hdense⟩ := HeavyPairPeeling.source_linear_reserves C Q (Fintype.card V)
    p.pairIndex G.maxDegree (G.maxDegree-p.completed.mult s(p.centre,b)) B c.setᶜ.card
    hC hQ hCQ hAQ hn hCard hB (c.complement_small.trans hK) hHeavy hdenseC
  have hGraph : p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N) =
      p.completed := by
    apply MultiGraph.ext_mult
    intro t
    exact (Nat.add_assoc _ _ _).symm
  have hreg : (p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N)).IsRegularOfDegree
      G.maxDegree := by rw [hGraph]; exact p.completion.regular
  have hpeel : HeavyPairPeeling.Certificate
      (p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N)) G.maxDegree
      (G.maxDegree-p.completed.mult s(p.centre,b)) p.centre b := by rwa [hGraph]
  have hOrdinaryCard : Fintype.card ↥(outside p.centre b) = 2*p.pairIndex := by
    have ho := card_outside p.centre b hab
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at ho
    omega
  have hc := HeavyPairPeeling.colourable_of_linear_reserve p.orderedBase
    (p.completion.L.addCopies p.completion.N) G.maxDegree
    (G.maxDegree-p.completed.mult s(p.centre,b)) B C p.pairIndex p.centre b hpeel hab
    p.ordered_star hreg (by rw [hGraph]) p.added_off_centre_internal_le hC hsize hOrdinaryCard hdense
  rwa [hGraph] at hc

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Uniform closure of the heavy-pair branch. No residual colourability,
factorization, or numeric order reserve is assumed after Q,N are chosen. -/
theorem above_half_small_centre_heavy_pair_colourable (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ N : ℕ,
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
      B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
      (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
      ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
      G.maxDegree-p.completed.mult s(p.centre,b) ≤ Fintype.card W/(64*Q) →
      Nonempty (p.completed.EdgeColoring G.maxDegree) := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (4000:ℝ) (64/ε))
  have hCReal : (4000:ℝ) ≤ C := (le_max_left _ _).trans hC.le
  have hCN : 4000 ≤ C := by exact_mod_cast hCReal
  have hCε : 64 ≤ ε*(C:ℝ) := by
    have hh : 64/ε < C := (le_max_right _ _).trans_lt hC
    have ht := (div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  obtain ⟨Q₀,hQ₀,N₀,hN₀⟩ := above_half_small_centre_completion_no_overfull.{u} ε hε
  let Q := max Q₀ (max C ((10:ℕ)^24*C^6))
  have hQ₀Q : Q₀ ≤ Q := le_max_left _ _
  have hCQ : C ≤ Q := (le_max_left _ _).trans (le_max_right _ _)
  have hAQ : (10:ℕ)^24*C^6 ≤ Q := (le_max_right _ _).trans (le_max_right _ _)
  have hQ : 2 ≤ Q := hQ₀.trans hQ₀Q
  have hQε : 1 ≤ ε*(Q:ℝ) := by
    have hcq : (C:ℝ) ≤ Q := by exact_mod_cast hCQ
    have hm := mul_le_mul_of_nonneg_left hcq hε.le
    linarith only [hm,hCε]
  refine ⟨Q,hQ,max N₀ (64*Q),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab hHeavy
  have hDiv : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hQ₀Q 2)) (by positivity)
  have hNo := hN₀ G c p (by omega) hcrit hdense (by omega) (by omega) hMin
  exact p.heavy_pair_colourable_at_source_scale C Q hCN hQ hCQ hAQ (by omega)
    (scaled_density_of_above_half ε Q _ _ hQε hdense)
    (HeavyPairPeeling.strong_scaled_density ε C _ _ hCε hdense) hB hK b hab hNo hHeavy

end OverfullWork.NormalizedCanonicalCandidate
