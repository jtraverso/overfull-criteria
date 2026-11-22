module

public import OverfullWork.CanonicalPostPrescriptionBounds
public import OverfullWork.MonotonePrescribedExtension

@[expose] public section


/-! Complete an actual fresh residue colour; all Hall inequalities are source-paid. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T ell : ℕ} {η ρ : ℝ} {b : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoHallCompletion.exists_full_residue_colour_extension
    (a : p.CaseTwoHallCompletion s ell ρ) (hP : 8 ≤ P) (hρ : 0 < ρ)
    (S : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)))
    (hMono : ∀ e, a.seed.graph.mult e ≤ S.graph.mult e) (hCover : S.CoversInternal s.part)
    (j : Fin (a.fresh+3*a.cap))
    (hSame : S.colouring.colourGraph (Fin.natAdd a.middle.seedPalette j)=a.palette.colourGraph j) :
    ∃ Q : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)),
      (∀ v, (Q.colouring.colourGraph (Fin.natAdd a.middle.seedPalette j)).degree v=1) ∧
      (∀ i, i ≠ Fin.natAdd a.middle.seedPalette j → Q.colouring.colourGraph i=S.colouring.colourGraph i) ∧
      (∀ e, S.graph.mult e ≤ Q.graph.mult e) ∧
      (∀ v, Q.graph.degree v+(S.colouring.colourGraph (Fin.natAdd a.middle.seedPalette j)).degree v=S.graph.degree v+1) ∧
      ∀ x y, (x ∈ s.part ↔ y ∈ s.part) → Q.graph.mult s(x,y)=S.graph.mult s(x,y) := by
  obtain ⟨z⟩ := a.anchors S hMono hCover j hSame
  have hRates := FirstAnchorScale.rate_order_bounds P (p.pairIndex+1)
    ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)) hP ρ hρ a.robust_rate
  have hRateR : FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ) ≤
      ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1):ℕ) := by
    have hPos : 0 ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ) := a.large_order.trans' (by norm_num)
    linarith [hRates.2]
  apply z.exists_monotone_full_colour_extension
    ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)) ((p.pairIndex+1)/(1024*P)+2*(3*T+1))
    s.robust (s.card_part.trans s.card_compl.symm)
    (by rw [hSame];exact a.balance j)
  · have hV := a.occupied_after_prescription S j hSame z s.partᶜ (Or.inr rfl)
    exact_mod_cast hV.trans hRateR
  · intro v hv
    have hvAll : v ∈ z.result.colouring.missingSet univ (Fin.natAdd a.middle.seedPalette j) :=
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
    have hD := a.deleted_after_prescription S hMono j z v hvAll
    exact_mod_cast hD.trans_le hRateR
  · intro v hv
    have hvA := (mem_filter.mp hv).1
    have hvAll : v ∈ z.result.colouring.missingSet univ (Fin.natAdd a.middle.seedPalette j) :=
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
    exact a.minimum_after_prescription hP hρ S hMono j hSame z v hvAll s.partᶜ (Or.inl ⟨hvA,rfl⟩)
  · intro v hv
    have hvB := (mem_filter.mp hv).1
    have hvAll : v ∈ z.result.colouring.missingSet univ (Fin.natAdd a.middle.seedPalette j) :=
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
    exact a.minimum_after_prescription hP hρ S hMono j hSame z v hvAll s.part (Or.inr ⟨mem_compl.mp hvB,rfl⟩)

end OverfullWork.NormalizedCanonicalCandidate
