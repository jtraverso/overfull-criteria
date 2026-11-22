module

public import OverfullWork.KuhnOsthusWindingNeighbourhoods
public import OverfullWork.OsthusStadenSliceRegularity

@[expose] public section


/-! Translate the original neighbourhood estimates of CSys8 into
both endpoint counts used before deleting the prefix factors. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem neighbourhood_profile_count (A : Finset V) (p : V → Prop) :
    profileCount A (univ.filter p) = ((A.filter p).card:ℝ) := by
  have he : A ∩ univ.filter p = A.filter p := by ext x; simp
  rw [profileCount,he]

/-- Apply the friendly-cluster argument in both directions. A single
real lower bound pays for the required number of endpoints and for
the prefix degree loss at each exceptional vertex. -/
theorem winding_interval_endpoint_counts {p b k : ℕ}
    (G : Digraph V) (hk : 0 < k) (i : Fin p) (boundary : Fin (b*k))
    (P : Fin k → Finset V) (C A : Fin (p*(b*k)) → Finset V) (Z₀ Z : Finset V)
    (M K demand : ℕ) (hM : 0 < M)
    (α θ τ ε : ℝ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hτ : τ ≤ α/3) (hε : ε ≤ 1)
    (hP : ∀ u, (P u).card = M)
    (hPDis : ∀ u v, u ≠ v → Disjoint (P u) (P v))
    (hCoarseCover : ∀ v, v ∉ Z₀ → v ∈ univ.biUnion P)
    (hExceptional : (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ))
    (hDegrees : ∀ v ∈ Z, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ) ∧
      α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ))
    (hCDis : ∀ x y, x ≠ y → Disjoint (C x) (C y))
    (hA : ∀ x, A x ⊆ C x)
    (hSplitIn : ∀ v ∈ Z, ∀ x, τ*(M:ℝ) ≤ profileCount (P (windingParent k hk x)) (inProfile G v) →
      θ*profileCount (P (windingParent k hk x)) (inProfile G v)/((p*b:ℕ):ℝ) ≤
        profileCount (C x) (inProfile G v))
    (hSplitOut : ∀ v ∈ Z, ∀ x, τ*(M:ℝ) ≤ profileCount (P (windingParent k hk x)) (outProfile G v) →
      θ*profileCount (P (windingParent k hk x)) (outProfile G v)/((p*b:ℕ):ℝ) ≤
        profileCount (C x) (outProfile G v))
    (hThresh : ∀ x, ε*((C x).card:ℝ) ≤ θ*((α/3)*(M:ℝ))/((p*b:ℕ):ℝ))
    (hRefIn : ∀ x, UniformProfileCell (inProfile G) (C x) (A x) K ε)
    (hRefOut : ∀ x, UniformProfileCell (outProfile G) (C x) (A x) K ε)
    (hDemand : (demand:ℝ) < (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*
      ((1-ε)*((θ*((α/3)*(M:ℝ))/((p*b:ℕ):ℝ))/(K:ℝ)))) :
    let E := (windingEndpointPositions boundary).biUnion (fun j => A (intervalPosition i j))
    ∀ v ∈ Z, demand < inNeighbours G E v ∧ demand < outTo G E v := by
  dsimp only
  let E := (windingEndpointPositions boundary).biUnion (fun j => A (intervalPosition i j))
  have hProfile (Q : Finset V) (hq : α*(Fintype.card V:ℝ) ≤ (Q.card:ℝ))
      (hSplit : ∀ x, τ*(M:ℝ) ≤ profileCount (P (windingParent k hk x)) Q →
        θ*profileCount (P (windingParent k hk x)) Q/((p*b:ℕ):ℝ) ≤ profileCount (C x) Q)
      (hRef : ∀ x, UniformProfileCell (fun _ : Unit => Q) (C x) (A x) K ε) :
      (demand:ℝ) < profileCount E Q := by
    have hMass := coarse_cluster_profile_lower k M P Z₀ Q α hα hP hPDis hCoarseCover hExceptional hq
    have hCount := winding_interval_style_profile_lower hk i boundary P C A Q M K hM
      α θ τ ε hα hθ hτ hε hP hPDis hCDis hA hMass hSplit hThresh hRef
    exact hDemand.trans_le hCount
  intro v hv
  have hIn := hProfile (inProfile G v) (hDegrees v hv).1 (hSplitIn v hv) (fun x _ hx => hRefIn x v hx)
  have hOut := hProfile (outProfile G v) (hDegrees v hv).2 (hSplitOut v hv) (fun x _ hx => hRefOut x v hx)
  rw [inProfile,neighbourhood_profile_count] at hIn
  rw [outProfile,neighbourhood_profile_count] at hOut
  exact ⟨by exact_mod_cast hIn,by exact_mod_cast hOut⟩

end OverfullWork.DirectedRobustExpansion
