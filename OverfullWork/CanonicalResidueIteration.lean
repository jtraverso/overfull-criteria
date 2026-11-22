module

public import OverfullWork.CanonicalFullResidueStep

@[expose] public section


/-! Iterate the proved local extension for every actual fresh colour.

No family of matchings or extensions is supplied as a hypothesis. Every
successor invokes the source-paid prescribed matching and Hall step.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T ell : ℕ} {η ρ : ℝ} {b : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 48000000

theorem Candidate.CaseTwoHallCompletion.exists_completed_residue_palette
    (a : p.CaseTwoHallCompletion s ell ρ) (hP : 8 ≤ P) (hρ : 0 < ρ) :
    ∃ Q : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)),
      (∀ e, a.seed.graph.mult e ≤ Q.graph.mult e) ∧ Q.CoversInternal s.part ∧
      ∀ i v, (Q.colouring.colourGraph i).degree v=1 := by
  let k := a.middle.seedPalette
  let f := a.fresh+3*a.cap
  have hStages : ∀ t : ℕ, t ≤ f →
      ∃ S : p.completed.PartialColouring (k+f),
        (∀ e, a.seed.graph.mult e ≤ S.graph.mult e) ∧ S.CoversInternal s.part ∧
        (∀ i : Fin k, ∀ v, (S.colouring.colourGraph (Fin.castAdd f i)).degree v=1) ∧
        (∀ j : Fin f, j.val < t → ∀ v, (S.colouring.colourGraph (Fin.natAdd k j)).degree v=1) ∧
        ∀ j : Fin f, t ≤ j.val → S.colouring.colourGraph (Fin.natAdd k j)=a.palette.colourGraph j := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨a.seed.attach_internal_residue s.part a.palette,?_,a.covers,?_,?_,?_⟩
      · intro e
        change a.seed.graph.mult e ≤ a.seed.graph.mult e+(a.seed.available.internalPart s.part).mult e
        omega
      · exact a.toCaseTwoFirstAnchorCompletion.initial_seed_factors
      · intro j hj
        omega
      · intro j _
        exact a.seed.attach_internal_residue_fresh_colour s.part a.palette j
    | succ t ih =>
      intro ht
      obtain ⟨S,hMono,hCover,hOld,hDone,hUntreated⟩ := ih (by omega)
      let j : Fin f := ⟨t,by omega⟩
      have hSame := hUntreated j (by dsimp only [j];omega)
      obtain ⟨Q,hFull,hOther,hGrowth,hDegree,hInternal⟩ :=
        a.exists_full_residue_colour_extension hP hρ S hMono hCover j hSame
      refine ⟨Q,(fun e => (hMono e).trans (hGrowth e)),?_,?_,?_,?_⟩
      · intro x y hSide
        exact (hInternal x y hSide).trans (hCover x y hSide)
      · intro i v
        have hNe : Fin.castAdd f i ≠ Fin.natAdd k j := by
          intro hh
          have hVal := congrArg Fin.val hh
          change i.val=k+j.val at hVal
          have hi := i.isLt
          omega
        rw [hOther _ hNe]
        exact hOld i v
      · intro u hu v
        by_cases he : u.val=t
        · have huj : u=j := Fin.ext he
          subst u
          exact hFull v
        · have hNe : Fin.natAdd k u ≠ Fin.natAdd k j := by
            intro hh
            have hVal := congrArg Fin.val hh
            change k+u.val=k+t at hVal
            omega
          rw [hOther _ hNe]
          exact hDone u (by omega) v
      · intro u hu
        have hNe : Fin.natAdd k u ≠ Fin.natAdd k j := by
          intro hh
          have hVal := congrArg Fin.val hh
          change k+u.val=k+t at hVal
          omega
        rw [hOther _ hNe]
        exact hUntreated u (by omega)
  obtain ⟨Q,hMono,hCover,hOld,hDone,_⟩ := hStages f (le_refl _)
  refine ⟨Q,hMono,hCover,?_⟩
  intro i
  exact Fin.addCases (fun j => hOld j) (fun j => hDone j j.isLt) i

end OverfullWork.NormalizedCanonicalCandidate
