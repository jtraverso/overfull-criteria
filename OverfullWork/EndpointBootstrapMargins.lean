module

public import OverfullWork.EndpointBootstrapCounting
public import OverfullWork.GoodRouteRuns

@[expose] public section


/-! # Start a robust layer at a current missing endpoint

Missing sets shrink pointwise along the recorded run. Saturated anchors
therefore stay excluded. The endpoint estimate uses the initial ordinary
crossing degree, even when the endpoint belongs to the larger exceptional
set used for the internal matching.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PrunedCore OverfullWork.RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 20000000

theorem bootstrapSet_subset_opposite (P : M.PartialColouring k) (A W : Finset V) (v : V)
    (D : Finset V) (hSide : (v ∈ A ∧ D=Aᶜ) ∨ (v ∉ A ∧ D=A)) :
    P.bootstrapSet A W v ⊆ D ∩ (univ\W) := by
  intro x hx
  obtain ⟨hEdge,hW⟩ := P.bootstrapSet_member A W v x hx
  refine mem_inter.mpr ⟨?_,mem_sdiff.mpr ⟨mem_univ _,hW⟩⟩
  rcases hSide with ⟨hv,rfl⟩|⟨hv,rfl⟩
  · exact mem_compl.mpr (fun hxA => hEdge.2 (by tauto))
  · by_contra hn
    exact hEdge.2 (by tauto)

theorem bootstrap_card_gt_eighth (P : M.PartialColouring k) (A W : Finset V) (v : V)
    (D : Finset V) (hSide : (v ∈ A ∧ D=Aᶜ) ∨ (v ∉ A ∧ D=A))
    (m Δ : ℕ) (loss ξ : ℝ) (hDelta : m ≤ Δ)
    (hSupport : (Δ:ℝ)/2-loss ≤ M.supportGraph.degree v)
    (hDis : |(neighboursIn M.supportGraph A v:ℝ)-(neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ)
    (hLoss : loss+ξ ≤ (m:ℝ)/16) (hW : (W.card:ℝ) ≤ (m:ℝ)/32)
    (hDeleted : ((P.graph.crossingSupport A).degree v:ℝ) ≤ (m:ℝ)/32) :
    (m:ℝ)/8 < (P.bootstrapSet A W v).card := by
  have hh := P.bootstrap_from_support_discrepancy A W v D hSide ((Δ:ℝ)/2-loss) ξ hSupport hDis
  have hd : (m:ℝ) ≤ Δ := by exact_mod_cast hDelta
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

namespace GoodRouteRun
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem missingSet_subset (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) :
    Q.colouring.missingSet univ j ⊆ P.colouring.missingSet univ j := by
  induction run with
  | refl P => exact Subset.rfl
  | @step P Q n t i a b s hGood hAdd hProtected hLen tail ih =>
    by_cases hj : j=i
    · subst j
      exact ih.trans (by rw [s.missingSet_exact];exact (erase_subset _ _).trans (erase_subset _ _))
    · have heq := s.other_colour j hj
      have hMissing : s.result.colouring.missingSet univ j=P.colouring.missingSet univ j := by
        ext v
        simp only [EdgeColoring.missingSet,mem_filter]
        rw [heq]
      rwa [hMissing] at ih

theorem missing_endpoint_ne_saturated (run : GoodRouteRun A E h ell P Q n t)
    (j : Fin k) (a v : V) (hSat : (P.colouring.colourGraph j).degree a ≠ 0)
    (hv : v ∈ Q.colouring.missingSet univ j) : v ≠ a := by
  have hvP := run.missingSet_subset j hv
  have hvZero : (P.colouring.colourGraph j).degree v=0 := (mem_filter.mp hvP).2
  intro he
  exact hSat (he ▸ hvZero)

theorem missing_endpoint_deleted_bound (run : GoodRouteRun A E h ell P Q n t)
    (a b : V) (j : Fin k) (B : ℕ)
    (hSatA : (P.colouring.colourGraph j).degree a ≠ 0)
    (hSatB : (P.colouring.colourGraph j).degree b ≠ 0)
    (hInitial : ∀ v, v ≠ a → v ≠ b → (P.graph.crossingSupport A).degree v ≤ 2)
    (hMissing : ∀ v, (P.colouring.missingPalette v).card ≤ B)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h)
    (v : V) (hv : v ∈ Q.colouring.missingSet univ j) :
    (Q.graph.crossingSupport A).degree v ≤ 2+B+h := by
  have ha := run.missing_endpoint_ne_saturated j a v hSatA hv
  have hb := run.missing_endpoint_ne_saturated j b v hSatB hv
  have hh := run.deleted_degree_budget hCap v
  have h₀ := hInitial v ha hb
  have hM := hMissing v
  omega

end GoodRouteRun
end SimpleGraph.MultiGraph.PartialColouring
