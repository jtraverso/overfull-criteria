module

public import OverfullWork.KuhnOsthusWindingEndpointCounts
public import OverfullWork.KuhnOsthusWoundSetup
public import OverfullWork.KuhnOsthusSharedResidualHost

@[expose] public section


/-! Obtain the endpoint hypothesis of Lemma 7.6 in the residual
host from the wound refinement in the original graph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]

/-- This choice pays for the number of clusters whose endpoint
capacity is exhausted during the greedy construction. -/
theorem exceptional_endpoint_cluster_budget (z cap : ℕ) (hCap : 0 < cap) :
    2*z < cap*((2*z)/cap+1) :=
  Nat.lt_mul_div_succ _ hCap

set_option maxHeartbeats 650000 in
/-- Winding, trimming and a style refinement give the two endpoint
counts after any earlier reserve deletion. The resulting lower
bound uses the retained style size, even when the coarse cells
are larger than the union of their retained descendants. -/
theorem winding_endpoint_counts_in_residual_host {l b k K m M : ℕ}
    (G H : Digraph V) (hH : H ≤ G) (Z₀ Z : Finset V)
    (P : Fin k → Finset V) (A X : Fin (l*(b*k)) → Finset V)
    (C : Fin K × Fin (l*(b*k)) → Finset V)
    (hl : 0 < l) (hb : 0 < b) (hk : 0 < k) (hK : 0 < K) (hM : 0 < M)
    (α θ τ ε₀ ε : ℝ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hτ : τ ≤ α/3)
    (hε₀τ : ε₀ ≤ τ) (hθε : θ ≤ 1-ε₀) (hε : ε ≤ 1)
    (hStyle : ε ≤ θ*(α/3)) (hVolume : (l*b)*(K*m) ≤ M)
    (hP : ∀ u, (P u).card = M)
    (hPDis : ∀ u v, u ≠ v → Disjoint (P u) (P v))
    (hCover : ∀ v, v ∉ Z₀ → v ∈ univ.biUnion P)
    (hZ₀ : (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ))
    (hDegree : ∀ z ∈ Z, α*(Fintype.card V:ℝ) ≤ (inDegree G z:ℝ) ∧
      α*(Fintype.card V:ℝ) ≤ (outDegree G z:ℝ))
    (hX : ∀ i, (X i).card = K*m ∧ X i ⊆ A i)
    (hXDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hTrim : ∀ i, ((A i \ X i).card:ℝ) ≤ (1-ε₀-θ)*(τ*(M:ℝ)/((l*b:ℕ):ℝ)))
    (hUIn : ∀ i, UniformProfileCell (inProfile G) (P (windingParent k hk i)) (A i) (l*b) ε₀)
    (hUOut : ∀ i, UniformProfileCell (outProfile G) (P (windingParent k hk i)) (A i) (l*b) ε₀)
    (hC : ∀ i, C i ⊆ X i.2)
    (hRefIn : ∀ i, UniformProfileCell (inProfile G) (X i.2) (C i) K ε)
    (hRefOut : ∀ i, UniformProfileCell (outProfile G) (X i.2) (C i) K ε)
    (demand loss : ℕ)
    (hLoss : ∀ z ∈ Z, inDegree H z ≤ loss ∧ outDegree H z ≤ loss)
    (hDemand : ((demand+loss:ℕ):ℝ) < (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*
      ((1-ε)*(θ*(α/3)*(m:ℝ)))) :
    let E (j : Fin K × Fin l) :=
      (windingEndpointPositions (⟨0,Nat.mul_pos hb hk⟩ : Fin (b*k))).biUnion
        (fun i => C (j.1,intervalPosition j.2 i))
    ∀ j z, z ∈ Z → demand < inNeighbours (G \ H) (E j) z ∧
      demand < outTo (G \ H) (E j) z := by
  intro E j z hz
  have hℓR : 0 < ((l*b:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hl hb
  have hKR : 0 < (K:ℝ) := by exact_mod_cast hK
  have hFine : ((K*m:ℕ):ℝ) ≤ (M:ℝ)/((l*b:ℕ):ℝ) := by
    apply (le_div_iff₀ hℓR).mpr
    simpa only [←Nat.cast_mul,Nat.mul_comm (K*m) (l*b)] using
      (show (((l*b)*(K*m):ℕ):ℝ) ≤ (M:ℝ) by exact_mod_cast hVolume)
  have hθa : 0 ≤ θ*(α/3) := by positivity
  have hFloor : θ*(α/3)*((K*m:ℕ):ℝ) ≤ θ*((α/3)*(M:ℝ))/((l*b:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hFine hθa
    simpa only [mul_div_assoc,mul_assoc] using h
  have hStyleFloor :
      θ*(α/3)*(m:ℝ) ≤ (θ*((α/3)*(M:ℝ))/((l*b:ℕ):ℝ))/(K:ℝ) := by
    apply (le_div_iff₀ hKR).mpr
    rw [Nat.cast_mul] at hFloor
    nlinarith only [hFloor]
  have hBound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hStyleFloor (sub_nonneg.mpr hε))
    (show 0 ≤ (α/3*(k:ℝ))*((b-3:ℕ):ℝ) by positivity)
  have hEnd := winding_interval_endpoint_counts G hk j.2 ⟨0,Nat.mul_pos hb hk⟩
    P X (fun i => C (j.1,i)) Z₀ Z M K (demand+loss) hM α θ τ ε hα hθ hτ hε hP hPDis
    hCover hZ₀ hDegree hXDis (fun i => hC (j.1,i)) ?_ ?_ ?_
    (fun i => hRefIn (j.1,i)) (fun i => hRefOut (j.1,i)) (hDemand.trans_le hBound)
  · have he : demand+loss < inNeighbours G (E j) z ∧ demand+loss < outTo G (E j) z := hEnd z hz
    obtain ⟨hi,ho⟩ := endpoint_neighbourhoods_after_reserve_deletion G H hH (E j) z
    obtain ⟨hI,hO⟩ := hLoss z hz
    exact ⟨by omega,by omega⟩
  · intro v _ x hx
    have hh := UniformProfileCell.lower_after_trimming (hUIn x) (hX x).2
      (Nat.mul_pos hl hb) hε₀τ hθε (by simpa only [hP] using hTrim x) v
      (by simpa only [hP] using hx)
    simpa only [mul_div_assoc] using hh
  · intro v _ x hx
    have hh := UniformProfileCell.lower_after_trimming (hUOut x) (hX x).2
      (Nat.mul_pos hl hb) hε₀τ hθε (by simpa only [hP] using hTrim x) v
      (by simpa only [hP] using hx)
    simpa only [mul_div_assoc] using hh
  · intro x
    rw [(hX x).1]
    calc
      ε*((K*m:ℕ):ℝ) ≤ θ*(α/3)*((K*m:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right hStyle (Nat.cast_nonneg _)
      _ ≤ _ := hFloor

end OverfullWork.DirectedRobustExpansion
