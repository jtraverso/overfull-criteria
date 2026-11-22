module

public import OverfullWork.KuhnOsthusSharedStyleRefinement
public import OverfullWork.KuhnOsthusWoundEndpointBudget
public import OverfullWork.KuhnOsthusWindingChordParameters
public import OverfullWork.KuhnOsthusWindingExceptionalDegrees

@[expose] public section


/-! Construct the original exceptional factors from a wound,
trimmed partition and one physical residual host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 950000 in
/-- Lemma 7.6 from explicit margins on a wound setup. The style cells,
endpoint budgets and reduced routing parameters are computed on
the same partition. The original arcs of every factor are chosen
in the complement of the previously allocated reserve. -/
theorem kuhn_osthus_lemma_7_6_from_wound_host
    (B σ d δ ε ν τ γ : ℝ) (hB : 0 < B) (hσ : 0 < σ)
    (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hFloor : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε)
    (K : ℕ) (hK : 0 < K) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {l b k : ℕ}
      (G H : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
      (A X : Fin (l*(b*k)) → Finset V) (R₀ : Digraph (Fin k))
      (_hl : 2 ≤ l) (hb : 0 < b) (hk : 0 < k)
      (m M r e endpointCap routeCap priorLoss : ℕ) (α θ εOld μ τ₀ a η : ℝ),
      let D := G \ H
      let parent := windingParent (n := l*(b*k)) k hk
      let R := fibrePullback R₀ parent parent
      let endpointBudget := (2*Z.card)/endpointCap
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      H ≤ G → 0 < endpointCap →
      (∀ u, (P u).card = M) → 0 < M →
      (∀ u v, u ≠ v → Disjoint (P u) (P v)) →
      (∀ v, v ∉ Z₀ → v ∈ univ.biUnion P) →
      (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ) →
      (∀ z ∈ Z, α*(Fintype.card V:ℝ) ≤ (inDegree G z:ℝ) ∧
        α*(Fintype.card V:ℝ) ≤ (outDegree G z:ℝ)) →
      (∀ z ∈ Z, inDegree H z ≤ priorLoss ∧ outDegree H z ≤ priorLoss) →
      (∀ i, (X i).card = K*m ∧ X i ⊆ A i) →
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ i, Disjoint (X i) Z) → (∀ v ∉ Z, ∃ i, v ∈ X i) →
      (l*b)*(K*m) ≤ M → N ≤ K*m →
      4*(Fintype.card V:ℝ) ≤ B*((K*m:ℕ):ℝ) →
      0 ≤ α → 0 ≤ θ → τ₀ ≤ α/3 → εOld ≤ τ₀ → θ ≤ 1-εOld → σ ≤ 1 →
      σ ≤ θ*(α/3) →
      (∀ i, ((A i \ X i).card:ℝ) ≤ (1-εOld-θ)*(τ₀*(M:ℝ)/((l*b:ℕ):ℝ))) →
      (∀ i, UniformProfileCell (inProfile G) (P (parent i)) (A i) (l*b) εOld) →
      (∀ i, UniformProfileCell (outProfile G) (P (parent i)) (A i) (l*b) εOld) →
      (((2*Z.card+endpointBudget*m+K*l*r+priorLoss):ℕ):ℝ) <
        (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) →
      (∀ i, ¬ R₀.Adj i i) → 0 < μ → μ ≤ τ₀ → τ₀ ≤ 1/4 →
      2 ≤ τ₀*(k:ℝ) → IsRealRobust R₀ μ τ₀ →
      (∀ u, α*(k:ℝ) ≤ (inDegree R₀ u:ℝ)) → (∀ u, α*(k:ℝ) ≤ (outDegree R₀ u:ℝ)) →
      8 ≤ (μ^2/2)*((b*k:ℕ):ℝ) →
      (2*τ₀+(μ^2/2)/2)*((b*k:ℕ):ℝ)+2 ≤ α*((b*k:ℕ):ℝ) →
      (Z.card:ℝ)*(8/(μ^2/2)+6) < (routeCap:ℝ)*((μ^2/2)*((b*k:ℕ):ℝ)/16) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 ≤ a → 0 < η → η ≤ 1 →
      K*σ ≤ η → 2*(σ+a) ≤ η → (r:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-σ-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*σ ≤ d →
      2*(max 2 (K:ℝ)*σ+a) ≤ δ → (r:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ i j, R.Adj i j → IsUniform D σ (X i) (X j) ∧ d ≤ density D (X i) (X j)) →
      (∀ i, IsLowerSuperregularPair D σ d (X i) (X (finRotate (l*(b*k)) i))) →
      ∃ C : Fin K × Fin (l*(b*k)) → Finset V,
        (∀ j, (C j).card = m ∧ C j ⊆ X j.2) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        (∀ i, (univ : Finset (Fin K)).biUnion (fun a => C (a,i)) = X i) ∧
        (∀ j, UniformProfileCell (inProfile D) (X j.2) (C j) K σ ∧
          UniformProfileCell (outProfile D) (X j.2) (C j) K σ) ∧
        let U (j : Fin K × Fin l) := (univ : Finset (Fin (b*k))).biUnion
          (fun i => C (j.1,intervalPosition j.2 i))
        let S (j : Fin K × Fin l) := C (j.1,intervalPosition j.2 ⟨0,Nat.mul_pos hb hk⟩)
        let next := (Equiv.refl (Fin K)).prodCongr (finRotate l)
        ∃ F : Fin r → ∀ j, OriginalInterval D Z (U j ∪ S (next j)) (S j) (S (next j)),
          let E (i : Fin r) := ⨆ j, (F i j).digraph
          Pairwise (fun i j => Disjoint (E i) (E j)) ∧ (⨆ i, E i) ≤ D ∧
          ∀ v, let h := if v ∈ Z then (K*l)*r else r
            inDegree (⨆ i, E i) v = h ∧ outDegree (⨆ i, E i) v = h := by
  obtain ⟨N₁,hN₁⟩ := exists_shared_exceptional_style_refinement.{u} B σ hB hσ K hK
  obtain ⟨N₂,hN₂⟩ := pack_original_intervals_on_winding_intervals.{u}
    d δ ε ν τ γ hν hWidth hε hε₁ hτγ hγ hd hCost hFloor hTol
  refine ⟨max N₁ N₂,?_⟩
  intro V _ l b k G H Z₀ Z P A X R₀ hl hb hk m M r e endpointCap routeCap priorLoss
    α θ εOld μ τ₀ a η D parent R endpointBudget loss hH hCap hP hM hPDis hCover hZ₀
    hDegree hPrior hX hXDis hXZ hOrdCover hVolume hSize₁ hProfiles hα hθ hτ₀α hεOld hθε
    hσ₁ hStyle hTrim hOldIn hOldOut hDemand hNoLoop hμ hμτ hτ₀ hOrder hRob hIn hOut
    hLarge hDeg hLoad hRoom hm hSize₂ hHall hPay ha hη hη₁ hScale hCTol hCLoss hGap hCut
    hδ hδ₁ hFloor' hSTol hSLoss hReg hSup
  have hq : 0 < b*k := Nat.mul_pos hb hk
  obtain ⟨C,hC,hDisC,hCoverC,hRef⟩ := hN₁ G D X m
    ((le_max_left N₁ N₂).trans hSize₁) (fun j => (hX j).1) hProfiles hXDis
  have hCover' (x : V) (hx : x ∉ Z) : ∃ j, x ∈ C j := by
    obtain ⟨i,hi⟩ := hOrdCover x hx
    rw [←hCoverC i] at hi
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hi
    exact ⟨(j,i),hj⟩
  have hEnds := winding_endpoint_counts_in_residual_host G H hH Z₀ Z P A X C
    (by omega : 0 < l) hb hk hK hM α θ τ₀ εOld σ hα hθ hτ₀α hεOld hθε hσ₁ hStyle
    hVolume hP hPDis hCover hZ₀ hDegree hX hXDis hTrim hOldIn hOldOut
    (fun j => (hC j).2) (fun j => (hRef j).1) (fun j => (hRef j).2.1)
    (2*Z.card+endpointBudget*m+K*l*r) priorLoss hPrior hDemand
  let Q (j : Fin l) : Digraph (Fin (b*k)) :=
    ⟨fun x y => R.Adj (intervalPosition j x) (intervalPosition j y)⟩
  have hRoutes (j : Fin l) :
      ∃ radius growth cutoff budget : ℕ, IsRobustAt (Q j) radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree (Q j) i) ∧
        (∀ i, cutoff ≤ inDegree (Q j) i) ∧
        Z.card*(2*((b*k)/growth+3)) < routeCap*(budget+1) :=
    winding_interval_chord_parameters R₀ R j hb hk (fun _ _ => Iff.rfl) μ τ₀ α hμ hμτ hτ₀
      hOrder hRob hIn hOut Z.card routeCap hLarge hDeg hLoad
  obtain ⟨F,hApart,_⟩ := hN₂ D Z Q X C m r e endpointCap endpointBudget routeCap σ a η hq hK hl
    hDisC hCover' (fun j => (hC j).1) (fun j => (hX j).1) (fun j => (hC j).2) hXZ
    (fun j => (hRef j).2.2.1) (fun j => (hRef j).2.2.2)
    (exceptional_endpoint_cluster_budget Z.card endpointCap hCap)
    (fun j z hz => (hEnds j z hz).1) (fun j z hz => (hEnds j z hz).2)
    hRoom (fun j i => hNoLoop (parent (intervalPosition j i))) hRoutes hm
    ((le_max_right N₁ N₂).trans hSize₂) hHall hPay hσ.le ha hη hη₁ hScale hCTol hCLoss hGap hCut
    hδ hδ₁ hFloor' hSTol hSLoss (fun j i h hij => hReg (intervalPosition j i) (intervalPosition j h) hij)
    hSup
  refine ⟨C,hC,hDisC,hCoverC,(fun j => (hRef j).2.2),F,hApart,
    iSup_le (fun i => iSup_le (fun j => (F i j).le)),?_⟩
  intro v
  simpa only [Fintype.card_fin] using
    winding_exceptional_reserve_exact_semidegrees C hq hl m (fun j => (hC j).1) hDisC hCover' F hApart v

end OverfullWork.DirectedRobustExpansion
