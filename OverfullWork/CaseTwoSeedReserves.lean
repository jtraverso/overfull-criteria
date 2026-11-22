module

public import OverfullWork.CaseTwoEquitableSeed
public import OverfullWork.CaseTwoCutScales

@[expose] public section


/-! # The constructed Case 2 seed uses strictly fewer than Delta colors

Pay the finite palette reserve from the original source budgets. The
partition/source scales are fixed before the cutoff and discrepancy;
only the order threshold grows with those parameters.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 12000000

theorem Candidate.CaseTwoMiddleCopies.palette_lt_maxDegree_of_reserves
    (r : p.CaseTwoMiddleCopies s w) (hT : 16 ≤ T) (hη : η ≤ 1/16)
    (hm : 64*(T+2) ≤ p.pairIndex+1) (hB : 64*B ≤ p.pairIndex+1)
    (hD : 2*(p.pairIndex+1) ≤ 3*G.maxDegree) : r.seedPalette < G.maxDegree := by
  have hη0 : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hηm := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (p.pairIndex+1))
  have hcut : 16*((p.pairIndex+1)/T) ≤ p.pairIndex+1 :=
    (Nat.mul_le_mul_right ((p.pairIndex+1)/T) hT).trans (Nat.mul_div_le _ _)
  have hconst : 8*(6*T+11) ≤ p.pairIndex+1 := by omega
  have hcutR : 16*(((p.pairIndex+1)/T:ℕ):ℝ) ≤ (p.pairIndex+1:ℕ) := by exact_mod_cast hcut
  have hconstR : 8*(6*(T:ℝ)+11) ≤ (p.pairIndex+1:ℕ) := by exact_mod_cast hconst
  have hBR : 64*(B:ℝ) ≤ (p.pairIndex+1:ℕ) := by exact_mod_cast hB
  have hDR : 2*(p.pairIndex+1:ℕ) ≤ 3*(G.maxDegree:ℝ) := by exact_mod_cast hD
  have hmR : 64*((T:ℝ)+2) ≤ (p.pairIndex+1:ℕ) := by exact_mod_cast hm
  have hbase : 0 ≤ ((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+
      ((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2 := by positivity
  have hceil := Nat.ceil_lt_add_one hbase
  change (r.seedDegreeBound:ℝ) < _ at hceil
  have hk : (r.seedPalette:ℝ) = (r.seedDegreeBound:ℝ)+(B:ℝ)+1 := by
    simp only [Candidate.CaseTwoMiddleCopies.seedPalette,Nat.cast_add,Nat.cast_one]
    ring
  exact_mod_cast (show (r.seedPalette:ℝ) < (G.maxDegree:ℝ) by linarith)

theorem pay_case_two_seed_reserves (Q n m Y B T : ℕ) (hQ : 8 ≤ Q)
    (hn : 3*max (2^50*Q^4) (64*(T+2)) ≤ n) (hCard : n+1=2*m+Y)
    (hY : Y ≤ n/(4096*Q^2)+1) (hB : B ≤ 6*(n/(4096*Q^2))+6) :
    64*(T+2) ≤ m ∧ 64*B ≤ m := by
  let M := max (2^50*Q^4) (64*(T+2))
  let k := n/(4096*Q^2)
  have hcoef : 4 ≤ 4096*Q^2 := by nlinarith only [hQ]
  have hk : 4*k ≤ n := (Nat.mul_le_mul_right k hcoef).trans (Nat.mul_div_le n _)
  change Y ≤ k+1 at hY
  have hm : M ≤ m := by dsimp only [M];nlinarith only [hn,hCard,hY,hk]
  have hbudget := CaseTwoCutScales.source_budget_le_q Q n m B Y hQ
    ((le_max_left _ _).trans hm) hCard hY hB
  have hscale : 64 ≤ 1024*Q := by omega
  have hpaid : 64*(m/(1024*Q)) ≤ m :=
    (Nat.mul_le_mul_right (m/(1024*Q)) hscale).trans (Nat.mul_div_le m _)
  exact ⟨(le_max_right _ _).trans hm,(Nat.mul_le_mul_left 64 hbudget).trans hpaid⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_proper_seed (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, P ≤ Q ∧ ∀ T : ℕ, 16 ≤ T →
      ∀ η : ℝ, 0 < η → η ≤ 1/16 → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          ∃ s : p.CaseTwoPartition P T η b,
            ∀ w, w ∉ s.part → b ≠ w → ∃ r : p.CaseTwoMiddleCopies s w,
              ∃ C : r.graph.EdgeColoring r.seedPalette,
                C.IsEquitable ∧ r.seedPalette < G.maxDegree ∧ ∀ v,
                  ((C.missingPalette v).card:ℝ) <
                    η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9 := by
  obtain ⟨P,hP,Q,hPQ,hConstruct⟩ := exists_uniform_case_two_equitable_seed.{u} ε hε
  refine ⟨P,hP,Q,hPQ,?_⟩
  intro T hT η hη hηsmall
  obtain ⟨N₀,hN₀⟩ := hConstruct T (by omega) η hη
  let M := max (2^50*Q^4) (64*(T+2))
  refine ⟨max N₀ (3*M),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  obtain ⟨s,hs⟩ := hN₀ G c p (by omega) hcrit hdense hB hK hMin b hab
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : Fintype.card W+1=2*(p.pairIndex+1)+c.setᶜ.card := by omega
  obtain ⟨hm,hBudget⟩ := pay_case_two_seed_reserves Q (Fintype.card W) (p.pairIndex+1)
    c.setᶜ.card B T (by omega) (by omega) hCard (c.complement_small.trans hK) hB
  have hWeak : Fintype.card W ≤ 2*G.maxDegree := by
    have he : 0 ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD := p.image_order_le_three_delta hWeak
  refine ⟨s,?_⟩
  intro w hw hbw
  obtain ⟨r,C,hC,hMissing⟩ := hs w hw hbw
  exact ⟨r,C,hC,r.palette_lt_maxDegree_of_reserves hT hηsmall hm hBudget hD,hMissing⟩

end OverfullWork.NormalizedCanonicalCandidate
