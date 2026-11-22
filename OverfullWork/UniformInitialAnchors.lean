module

public import OverfullWork.SecondAnchorGapScales

@[expose] public section


/-! # Uniform construction of both initial anchors in the nonheavy branch

The source scale is fixed before T, eta and the graph. Only the order
threshold depends on T and eta. The center-bundle gap rho m is the
explicit nonheavy branch condition; the neighbor reserve and the
displayed recoloring-error inequality are both derived, not assumed.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
set_option maxHeartbeats 16000000

theorem exists_uniform_case_two_initial_anchors (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, P ≤ Q ∧
      ∀ T : ℕ, 16 ≤ T → 24 ≤ ρ*(T:ℝ) →
      ∀ η : ℝ, 0 < η → η ≤ 1/16 → η ≤ ρ/28 → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree →
          ∃ s : p.CaseTwoPartition P T η b,
            ∀ w, w ∉ s.part → b ≠ w → ∃ r : p.CaseTwoMiddleCopies s w,
              ∃ C : r.graph.EdgeColoring r.seedPalette,
                C.IsEquitable ∧ r.seedPalette < G.maxDegree ∧
                ∃ R : p.completed.PartialColouring r.seedPalette,
                  (∀ i, (R.colouring.colourGraph i).degree p.centre=1 ∧
                    (R.colouring.colourGraph i).degree b=1) ∧
                  R.graph.mult s(b,w)=p.completed.mult s(b,w) ∧
                  (∀ v ∈ s.part, R.graph.mult s(p.centre,v)=p.completed.mult s(p.centre,v)) ∧
                  (∀ x y, x ≠ p.centre → y ≠ p.centre → x ≠ b → y ≠ b →
                    ¬(x ∈ s.part ↔ y ∈ s.part) → R.graph.mult s(x,y)=0) ∧
                  (∀ v, ((R.colouring.missingPalette v).card:ℝ) <
                    6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)) ∧
                  ∃ D : PriorityMCCPairing.Family R.colouring s.part, ∀ i,
                    ((R.colouring.missingSet univ i).card:ℝ) ≤
                      6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  obtain ⟨P,hP,Q₀,hPQ₀,hSeeds⟩ := exists_uniform_case_two_proper_seed.{u} ε hε
  have hQ₀ : 8 ≤ Q₀ := hP.trans hPQ₀
  obtain ⟨L,hL⟩ := exists_nat_gt (3600/ρ)
  let Q := max Q₀ L
  have h₀Q : Q₀ ≤ Q := le_max_left _ _
  have hPQ : P ≤ Q := hPQ₀.trans h₀Q
  have hQ : 8 ≤ Q := hP.trans hPQ
  have hLQ : (L:ℝ) ≤ Q := by exact_mod_cast (le_max_right Q₀ L)
  have hScale : 3600 ≤ ρ*((4096*Q^2:ℕ):ℝ) := by
    have hρL := (div_lt_iff₀ hρ).mp hL
    have hDen : Q ≤ 4096*Q^2 := by nlinarith only [hQ]
    have hDenR : (Q:ℝ) ≤ ((4096*Q^2:ℕ):ℝ) := by exact_mod_cast hDen
    nlinarith only [hρ,hρL,hLQ,hDenR]
  refine ⟨P,hP,Q,hPQ,?_⟩
  intro T hT hTρ η hη hηsmall hηρ
  obtain ⟨N₀,hN₀⟩ := hSeeds T hT η hη hηsmall
  obtain ⟨M,hM⟩ := exists_nat_gt ((144*(T:ℝ)+1200)/ρ)
  refine ⟨max N₀ (max (3*M) (64*Q)),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab hNonheavy
  have hDiv₀ : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h₀Q 2)) (by positivity)
  obtain ⟨s,hs⟩ := hN₀ G c p (by omega) hcrit hdense (by omega) (by omega) hMin b hab
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : Fintype.card W+1=2*(p.pairIndex+1)+c.setᶜ.card := by omega
  have hY := c.complement_small.trans hK
  have hnm := source_half_order_bound Q (Fintype.card W) (p.pairIndex+1) c.setᶜ.card hQ hCard hY
  have hMm : M ≤ p.pairIndex+1 := by omega
  have hMmR : (M:ℝ) ≤ (p.pairIndex+1:ℕ) := by exact_mod_cast hMm
  have hOrder : 144*(T:ℝ)+1200 ≤ ρ*(p.pairIndex+1:ℕ) := by
    have hh := (div_lt_iff₀ hρ).mp hM
    nlinarith only [hh,hMmR,hρ]
  have hPaidB := pay_second_anchor_source_budget Q (Fintype.card W) (p.pairIndex+1)
    c.setᶜ.card B ρ hρ hQ hCard hY hB hScale (by linarith [Nat.cast_nonneg T (α := ℝ)])
  have hGap := pay_second_anchor_gap (p.pairIndex+1) B T η ρ
    (p.completed.mult s(p.centre,b)) G.maxDegree hρ hηρ hTρ hPaidB (by linarith) hNonheavy
  have hD := p.maxDegree_lt_image_order_at_source_scale Q (by omega) (by omega) hB hK
  have hWeak : Fintype.card W ≤ 2*G.maxDegree := by
    have he : 0 ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hHalf := p.image_half_order_le_delta hWeak
  refine ⟨s,?_⟩
  intro w hw hbw
  obtain ⟨r,C,hC,hPalette,_⟩ := hs w hw hbw
  obtain ⟨Q₁,R,t₁,t₂,hFirst,hSecond,ht₁,ht₂,hSat,hBundle,hInternal,hMissing,D,hPerColour⟩ :=
    r.exists_initial_anchor_runs hw hbw (by omega) (by omega) hHalf C hC hPalette.le hGap
  exact ⟨r,C,hC,hPalette,R,hSat,hBundle,hInternal,
    fun x y hxa hya hxb hyb hCross =>
      r.initial_runs_away_crossing_zero C hFirst hSecond x y hxa hya hxb hyb hCross,
    hMissing,D,hPerColour⟩

end OverfullWork.NormalizedCanonicalCandidate
