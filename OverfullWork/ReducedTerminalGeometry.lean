module

public import OverfullWork.ReducedCriticalSourceFork
public import OverfullWork.NormalizedTerminalLiteratureBridge

@[expose] public section


/-! Exact terminal inputs still needed after advancing every all-maximum core.

These are actual noncritical Class 2 states. Their small-centre candidate
or low independent even-complement geometry is constructed, not excluded.
-/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem reduced_terminal_geometry {B K : ℕ} (s : State V B K) (hM : Margins s)
    (hT : ReducedTerminal s) :
    (∃ p : NormalizedCanonicalCandidate.Candidate s.cut, p.centre=(0,false)) ∨
    ∃ x ∈ s.cut.set, ∃ Z : Finset V,
      Z=insert x s.cut.setᶜ ∧ s.graph.IsIndepSet (Z:Set V) ∧ Z.card ≤ K+1 ∧ Even Zᶜ.card ∧
      (∀ z ∈ Z, s.graph.degree z ≤ s.graph.degree x) ∧
      2*s.graph.degree x < (∑ z ∈ Z, s.graph.degree z) ∧
      (∑ z ∈ Z, s.graph.degree z) ≤ 2*B := by
  rcases hT with hSmall|hLow
  · left
    apply NormalizedCanonicalCandidate.exists_centred_candidate s.graph s.cut s.no_overfull _ hSmall
    have hY := s.cut.complement_small
    have hParts := card_add_card_compl s.cut.set
    have hMatch := hM.1
    omega
  · right
    obtain ⟨x,hx,hMin,hLarge,v,hv,hvx,hLow,hInd⟩ := hLow
    have hBounds := NormalizedTerminalLiteratureBridge.second_low_degree_bounds s.graph s.cut hx hLarge hv hvx hLow
    let Z := insert x s.cut.setᶜ
    have hxY : x ∉ s.cut.setᶜ := by simpa using hx
    have hCard : Z.card ≤ K+1 := by
      dsimp only [Z]
      rw [card_insert_of_notMem hxY]
      have hh := s.cut.complement_small
      omega
    have hEven : Even Zᶜ.card := by
      have hZc : Zᶜ=s.cut.set.erase x := by
        ext u
        simp only [Z,mem_compl,mem_insert,not_or,not_not,mem_erase]
      rw [hZc,card_erase_of_mem hx]
      obtain ⟨m,hm⟩ := s.cut.odd
      exact ⟨m,by omega⟩
    have hSum : (∑ z ∈ Z, s.graph.degree z)=s.graph.degree x+(∑ y ∈ s.cut.setᶜ, s.graph.degree y) :=
      sum_insert hxY
    refine ⟨x,hx,Z,rfl,hInd,hCard,hEven,?_,?_,?_⟩
    · intro z hz
      rcases mem_insert.mp hz with rfl|hz
      · exact le_refl _
      · exact s.cut.ordered z hz x hx
    · omega
    · omega

end OverfullWork.NormalizedClassTwoStep
