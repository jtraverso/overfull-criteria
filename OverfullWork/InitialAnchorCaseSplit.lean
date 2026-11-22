module

public import OverfullWork.UniformInitialAnchors
public import OverfullWork.CanonicalHeavyPairColouring

@[expose] public section


/-! # Compatible heavy/nonheavy split for the initial anchors

Keep the existing heavy cutoff H separate from the finer source scale
Q used to pay the seed and recoloring errors. Thus the complementary
nonheavy branch supplies rho=1/(64H) without a circular scale choice.
The output is a full coloring in the heavy branch or actual prepared
initial anchors in the complementary branch, not a full G2 coloring.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 16000000

def Candidate.InitialAnchorsReady (p : Candidate c) (P T : ℕ) (η : ℝ)
    (b : Fin (p.pairIndex+1) × Bool) : Prop :=
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
              6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2

theorem Candidate.nonheavy_gap_at_source_cutoff (p : Candidate c) (H : ℕ) (hH : 1 ≤ H)
    (b : Fin (p.pairIndex+1) × Bool)
    (hNonheavy : Fintype.card V/(64*H) < G.maxDegree-p.completed.mult s(p.centre,b)) :
    (p.completed.mult s(p.centre,b):ℝ)+(1/(64*(H:ℝ)))*(p.pairIndex+1:ℕ) ≤ G.maxDegree := by
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : Fintype.card V+1=2*(p.pairIndex+1)+c.setᶜ.card := by omega
  have hmn : p.pairIndex+1 ≤ Fintype.card V := by omega
  have hMul := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 64*H)).mp hNonheavy
  have hqPos : 0 < G.maxDegree-p.completed.mult s(p.centre,b) :=
    lt_of_le_of_lt (Nat.zero_le _) hNonheavy
  have hPos : p.completed.mult s(p.centre,b) ≤ G.maxDegree := by omega
  have hSub : ((G.maxDegree-p.completed.mult s(p.centre,b):ℕ):ℝ)=
      (G.maxDegree:ℝ)-(p.completed.mult s(p.centre,b):ℝ) := Nat.cast_sub hPos
  have hMulR : (Fintype.card V:ℝ) <
      ((G.maxDegree-p.completed.mult s(p.centre,b):ℕ):ℝ)*(64*(H:ℝ)) := by exact_mod_cast hMul
  have hmnR : (p.pairIndex+1:ℕ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hmn
  have hDen : 0 < 64*(H:ℝ) := by positivity
  have hDiv : ((p.pairIndex+1:ℕ):ℝ)/(64*(H:ℝ)) ≤
      (G.maxDegree:ℝ)-(p.completed.mult s(p.centre,b):ℝ) := by
    apply (div_le_iff₀ hDen).mpr
    rw [hSub] at hMulR
    linarith
  have hResult : (p.completed.mult s(p.centre,b):ℝ)+
      ((p.pairIndex+1:ℕ):ℝ)/(64*(H:ℝ)) ≤ G.maxDegree := by linarith
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hResult

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem initial_anchor_parameters_exist (H : ℕ) (hH : 2 ≤ H) :
    ∃ T : ℕ, 16 ≤ T ∧ 24 ≤ (1/(64*(H:ℝ)))*(T:ℝ) ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1/16 ∧ η ≤ (1/(64*(H:ℝ)))/28 := by
  let ρ : ℝ := 1/(64*(H:ℝ))
  have hρ : 0 < ρ := by dsimp only [ρ];positivity
  obtain ⟨T,hT⟩ := exists_nat_gt (max (16:ℝ) (24/ρ))
  have hT16 : 16 ≤ T := by exact_mod_cast (le_max_left _ _).trans hT.le
  have hPaid := (div_lt_iff₀ hρ).mp ((le_max_right _ _).trans_lt hT)
  refine ⟨T,hT16,by dsimp only [ρ] at hPaid;linarith,min (1/16) (ρ/28),?_,min_le_left _ _,min_le_right _ _⟩
  exact lt_min (by norm_num) (by positivity)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_initial_anchor_case_split (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, 2 ≤ H ∧ ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, H ≤ Q ∧ P ≤ Q ∧
      ∀ T : ℕ, 16 ≤ T → 24 ≤ (1/(64*(H:ℝ)))*(T:ℝ) →
      ∀ η : ℝ, 0 < η → η ≤ 1/16 → η ≤ (1/(64*(H:ℝ)))/28 → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          Nonempty (p.completed.EdgeColoring G.maxDegree) ∨ p.InitialAnchorsReady P T η b := by
  obtain ⟨H,hH,NH,hHeavy⟩ := above_half_small_centre_heavy_pair_colourable.{u} ε hε
  have hρ : 0 < (1/(64*(H:ℝ))) := by positivity
  obtain ⟨P,hP,Q₀,hPQ₀,hInitial⟩ := exists_uniform_case_two_initial_anchors.{u} ε _ hε hρ
  let Q := max H Q₀
  have hHQ : H ≤ Q := le_max_left _ _
  have h₀Q : Q₀ ≤ Q := le_max_right _ _
  have hPQ : P ≤ Q := hPQ₀.trans h₀Q
  have hQ₀ : 8 ≤ Q₀ := hP.trans hPQ₀
  refine ⟨H,hH,P,hP,Q,hHQ,hPQ,?_⟩
  intro T hT hTρ η hη hηsmall hηρ
  obtain ⟨N₀,hN₀⟩ := hInitial T hT hTρ η hη hηsmall hηρ
  refine ⟨max NH N₀,?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  have hDivH : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*H^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hHQ 2)) (by positivity)
  have hDiv₀ : Fintype.card W/(4096*Q^2) ≤ Fintype.card W/(4096*Q₀^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h₀Q 2)) (by positivity)
  by_cases hCase : G.maxDegree-p.completed.mult s(p.centre,b) ≤ Fintype.card W/(64*H)
  · exact Or.inl (hHeavy G c p (by omega) hcrit hdense (by omega) (by omega) hMin b hab hCase)
  · exact Or.inr (hN₀ G c p (by omega) hcrit hdense (by omega) (by omega) hMin b hab
      (p.nonheavy_gap_at_source_cutoff H (by omega) b (by omega)))

end OverfullWork.NormalizedCanonicalCandidate
