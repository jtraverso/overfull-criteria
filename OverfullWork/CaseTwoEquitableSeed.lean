module

public import OverfullWork.OffCentreVizing
public import OverfullWork.CaseTwoSeedCriticalReduction
public import OverfullWork.UniformCaseTwoMiddleCopies

@[expose] public section


/-! # Construct the equitable Case 2 seed and its missing-color bounds

CMS Lemma 3.10 is now proved for the actual multigraph. McDiarmid's
existing recoloring construction balances the seed on the same palette.
All estimates use our previously proved explicit degree-profile error.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 12000000

theorem Candidate.CaseTwoMiddleCopies.exists_equitable_seed
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) :
    ∃ C : r.graph.EdgeColoring r.seedPalette, C.IsEquitable := by
  obtain ⟨C⟩ := r.graph.exists_edgeColoring_off_centre_bound p.centre r.seedDegreeBound (B+1)
    (r.degree_le_seed_bound hw hD hT) r.off_centre_multiplicity_le
  exact C.exists_equitable

theorem Candidate.CaseTwoMiddleCopies.seed_missing_bound
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (C : r.graph.EdgeColoring r.seedPalette) (v : Fin (p.pairIndex+1) × Bool) :
    ((C.missingPalette v).card:ℝ) <
      η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9 := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hbase : 0 ≤ ((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+
      ((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2 := by positivity
  have hceil := Nat.ceil_lt_add_one hbase
  change (r.seedDegreeBound:ℝ) < _ at hceil
  have hk : (r.seedPalette:ℝ) = (r.seedDegreeBound:ℝ)+(B:ℝ)+1 := by
    simp only [Candidate.CaseTwoMiddleCopies.seedPalette,Nat.cast_add,Nat.cast_one]
    ring
  have hm : ((C.missingPalette v).card:ℝ)+(r.graph.degree v:ℝ) = (r.seedPalette:ℝ) := by
    exact_mod_cast C.missingPalette_card_add_degree v
  have hlow := (abs_le.mp (r.degree_profile_at_cutoff hw hD hT v)).1
  linarith

theorem Candidate.CaseTwoMiddleCopies.seed_total_missing_bound
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (C : r.graph.EdgeColoring r.seedPalette) :
    (∑ v, ((C.missingPalette v).card:ℝ)) ≤ 2*(p.pairIndex+1:ℕ)*
      (η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9) := by
  have hh := sum_le_sum (s := (univ : Finset (Fin (p.pairIndex+1) × Bool)))
    (fun v _ => (r.seed_missing_bound hw hD hT C v).le)
  simpa only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hh

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_equitable_seed (ε : ℝ) (hε : 0 < ε) :
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
            ∀ w, w ∉ s.part → b ≠ w → ∃ r : p.CaseTwoMiddleCopies s w,
              ∃ C : r.graph.EdgeColoring r.seedPalette, C.IsEquitable ∧ ∀ v,
                ((C.missingPalette v).card:ℝ) <
                  η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9 := by
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
  obtain ⟨C,hC⟩ := r.exists_equitable_seed hw (by omega) hT
  exact ⟨r,C,hC,fun v => r.seed_missing_bound hw (by omega) hT C v⟩

end OverfullWork.NormalizedCanonicalCandidate
