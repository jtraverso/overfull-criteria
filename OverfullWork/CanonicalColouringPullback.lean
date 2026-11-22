module

public import OverfullWork.CanonicalHeavyPairColouring

@[expose] public section


/-! # Pull a completed canonical colouring back to the original graph

Restriction selects actual coloured copies, then the vertex equivalence
is undone. The existing identification theorem colours every original
labelled edge. This closes the heavy branch as a critical exclusion.
-/
namespace OverfullWork.CanonicalColouringPullback
open SimpleGraph Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
set_option maxHeartbeats 6000000

theorem restrict_copies (M N : MultiGraph V) {k : ℕ} (C : N.EdgeColoring k)
    (hle : ∀ t, M.mult t ≤ N.mult t) : Nonempty (M.EdgeColoring k) := by
  have halloc : ∀ t, ∃ f : Fin k → ℕ, (∀ i, f i ≤ C.col t i) ∧ ∑ i, f i = M.mult t := by
    intro t
    exact MultiGraph.bounded_allocation_fin k (C.col t) (M.mult t) (by rw [C.sum_col]; exact hle t)
  choose f hf hsum using halloc
  exact ⟨{
    col := f
    sum_col := hsum
    proper := fun v i => (sum_le_sum (fun t _ => hf t i)).trans (C.proper v i)
  }⟩

def reindex_colouring (M : MultiGraph V) (e : W ≃ V) {k : ℕ} (C : M.EdgeColoring k) :
    (OrderedCanonicalTransport.reindex M e).EdgeColoring k where
  col t i := C.col (Sym2.map e t) i
  sum_col t := C.sum_col (Sym2.map e t)
  proper w i := by
    have hd := OrderedCanonicalTransport.degree_reindex (C.colourGraph i) e w
    exact hd.trans_le (C.colourGraph_degree_le_one i (e w))

theorem undo_reindex (M : MultiGraph V) (e : W ≃ V) {k : ℕ}
    (C : (OrderedCanonicalTransport.reindex M e).EdgeColoring k) : Nonempty (M.EdgeColoring k) := by
  have F := reindex_colouring _ e.symm C
  have hgraph : OrderedCanonicalTransport.reindex (OrderedCanonicalTransport.reindex M e) e.symm = M := by
    apply MultiGraph.ext_mult
    intro t
    induction t using Sym2.inductionOn with
    | hf x y =>
      change M.mult s(e (e.symm x), e (e.symm y)) = M.mult s(x,y)
      rw [e.apply_symm_apply,e.apply_symm_apply]
  exact ⟨by rwa [hgraph] at F⟩

end OverfullWork.CanonicalColouringPullback

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.source_colourable_of_completed (p : Candidate c) {k : ℕ}
    (C : p.completed.EdgeColoring k) : G.EdgeColorable k := by
  obtain ⟨F⟩ := CanonicalColouringPullback.restrict_copies p.orderedBase p.completed C (by
    intro t
    change p.orderedBase.mult t ≤ p.orderedBase.mult t+p.completion.L.mult t+p.completion.N.mult t
    omega)
  obtain ⟨I⟩ := CanonicalColouringPullback.undo_reindex c.image p.coordinates F
  have hInd : G.IsIndepSet (↑(c.setᶜ):Set V) := by
    simpa only [Finset.coe_compl] using c.independent
  exact IndependentSetIdentification.colourable_of_identification G c.setᶜ hInd I

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A critical small-centre candidate must lie in the nonheavy case.
This does not exclude that remaining case or prove the original G2. -/
theorem above_half_small_centre_no_heavy_pair (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ N : ℕ,
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
      B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
      (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
      ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
      Fintype.card W/(64*Q) < G.maxDegree-p.completed.mult s(p.centre,b) := by
  obtain ⟨Q,hQ,N,hN⟩ := above_half_small_centre_heavy_pair_colourable.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  by_contra hnot
  obtain ⟨C⟩ := hN G c p hn hcrit hdense hB hK hMin b hab (by omega)
  exact hcrit.2.1 (p.source_colourable_of_completed C)

end OverfullWork.NormalizedCanonicalCandidate
