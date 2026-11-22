module

public import OverfullWork.KuhnOsthusExceptionalFactorScales
public import OverfullWork.KuhnOsthusExceptionalFactorsFromWoundHost

@[expose] public section


/-! Use the same original partition in all three calls to Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- The coarse, wound and trimmed cells and the common reduced graph.
Every application retains these data, regardless of the number of
intervals or styles and the reserves already removed. -/
structure WoundExceptionalPartition {V : Type*} [Fintype V] {k n : ℕ}
    (G : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
    (A X : Fin n → Finset V) (R₀ : Digraph (Fin k)) (hk : 0 < k)
    (L M m : ℕ) (α θ εOld μ τ₀ : ℝ) : Prop where
  coarse_size : ∀ i, (P i).card = M
  coarse_disjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  coarse_cover : ∀ v, v ∉ Z₀ → v ∈ univ.biUnion P
  initial_exceptional_size : (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ)
  exceptional_degrees : ∀ z ∈ Z, α*(Fintype.card V:ℝ) ≤ (inDegree G z:ℝ) ∧
    α*(Fintype.card V:ℝ) ≤ (outDegree G z:ℝ)
  fine_size : ∀ i, (X i).card = m ∧ X i ⊆ A i
  fine_disjoint : ∀ i j, i ≠ j → Disjoint (X i) (X j)
  fine_ordinary : ∀ i, Disjoint (X i) Z
  fine_cover : ∀ v ∉ Z, ∃ i, v ∈ X i
  volume : L*m ≤ M
  trimmed_loss : ∀ i, ((A i \ X i).card:ℝ) ≤ (1-εOld-θ)*(τ₀*(M:ℝ)/(L:ℝ))
  profile_in : ∀ i, UniformProfileCell (inProfile G) (P (windingParent k hk i)) (A i) L εOld
  profile_out : ∀ i, UniformProfileCell (outProfile G) (P (windingParent k hk i)) (A i) L εOld
  reduced_loopless : ∀ i, ¬ R₀.Adj i i
  reduced_expansion : IsRealRobust R₀ μ τ₀
  reduced_in : ∀ i, α*(k:ℝ) ≤ (inDegree R₀ i:ℝ)
  reduced_out : ∀ i, α*(k:ℝ) ≤ (outDegree R₀ i:ℝ)

set_option maxHeartbeats 1100000 in
/-- Reindex the common partition, choose integral capacities and cut
thresholds, and invoke Lemma 7.6 in the actual complement of `H`.
The endpoint degrees of the earlier reserve are paid separately from
the loss in the two ordinary pair families. -/
theorem kuhn_osthus_exceptional_factors_from_common_partition
    (B σ d δ ε ν τ γ : ℝ) (hB : 0 < B) (hσ : 0 < σ)
    (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hDensity : 6*ε ≤ d)
    (hCost : ν ≤ (d-2*ε)*τ) (hFloor : γ ≤ d-2*ε) (hTol : 4*δ ≤ ε)
    (K c : ℕ) (hK : 0 < K) (hc : 32 ≤ c) (hScaleCap : 20 ≤ (c:ℝ)*ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {l b k n L : ℕ}
      (G H : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
      (A X : Fin n → Finset V) (R₀ : Digraph (Fin k))
      (_hl : 2 ≤ l) (hb : 0 < b) (hk : 0 < k)
      (hIndex : n = l*(b*k)) (_hWinding : L = l*b)
      (m M r loss priorLoss : ℕ) (α θ εOld μ τ₀ a η ξ β : ℝ),
      let parent := windingParent (n := n) k hk
      let R := fibrePullback R₀ parent parent
      let Y (i : Fin (l*(b*k))) := X (finCongr hIndex.symm i)
      WoundExceptionalPartition G Z₀ Z P A X R₀ hk L M (K*m) α θ εOld μ τ₀ →
      H ≤ G → 0 < M → 2*N ≤ m → 2*c ≤ m → 1 ≤ ε*(m:ℝ) →
      4*(Fintype.card V:ℝ) ≤ B*((K*m:ℕ):ℝ) →
      (∀ v, inDegree H v ≤ loss ∧ outDegree H v ≤ loss) →
      (∀ z ∈ Z, inDegree H z ≤ priorLoss ∧ outDegree H z ≤ priorLoss) →
      0 ≤ β → 2*(ξ+β) ≤ σ → (loss:ℝ) ≤ β*(((K*m:ℕ):ℝ)*σ) →
      (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ d+(ξ+β) ≤ density G (X i) (X j)) →
      (∀ i, IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i))) →
      0 ≤ α → 0 ≤ θ → τ₀ ≤ α/3 → εOld ≤ τ₀ → θ ≤ 1-εOld → σ ≤ 1 → σ ≤ θ*(α/3) →
      (((4*c+2)*Z.card+K*l*r+priorLoss:ℕ):ℝ) <
        (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) →
      0 < μ → μ ≤ τ₀ → τ₀ ≤ 1/4 → 2 ≤ τ₀*(k:ℝ) →
      8 ≤ (μ^2/2)*((b*k:ℕ):ℝ) →
      (2*τ₀+(μ^2/2)/2)*((b*k:ℕ):ℝ)+2 ≤ α*((b*k:ℕ):ℝ) →
      (Z.card:ℝ)*(8/(μ^2/2)+6) <
        ((m:ℝ)/(2*(c:ℝ)))*((μ^2/2)*((b*k:ℕ):ℝ)/16) →
      0 ≤ a → 0 < η → η ≤ 1/4 → K*σ ≤ η → 2*(σ+a) ≤ η →
      (r:ℝ) ≤ a*((m:ℝ)*η) → η < d-σ-a →
      0 < δ → δ ≤ 1 → 2*σ ≤ d → 2*(max 2 (K:ℝ)*σ+a) ≤ δ →
      (r:ℝ) ≤ a*((m:ℝ)*δ) →
      ∃ C : Fin K × Fin (l*(b*k)) → Finset V,
        (∀ j, (C j).card = m ∧ C j ⊆ Y j.2) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        (∀ i, (univ : Finset (Fin K)).biUnion (fun a => C (a,i)) = Y i) ∧
        (∀ j, UniformProfileCell (inProfile (G \ H)) (Y j.2) (C j) K σ ∧
          UniformProfileCell (outProfile (G \ H)) (Y j.2) (C j) K σ) ∧
        let U (j : Fin K × Fin l) := (univ : Finset (Fin (b*k))).biUnion
          (fun i => C (j.1,intervalPosition j.2 i))
        let S (j : Fin K × Fin l) := C (j.1,intervalPosition j.2 ⟨0,Nat.mul_pos hb hk⟩)
        let next := (Equiv.refl (Fin K)).prodCongr (finRotate l)
        ∃ F : Fin r → ∀ j, OriginalInterval (G \ H) Z (U j ∪ S (next j)) (S j) (S (next j)),
          let E (i : Fin r) := ⨆ j, (F i j).digraph
          Pairwise (fun i j => Disjoint (E i) (E j)) ∧ (⨆ i, E i) ≤ G \ H ∧
          ∀ v, let h := if v ∈ Z then (K*l)*r else r
            inDegree (⨆ i, E i) v = h ∧ outDegree (⨆ i, E i) v = h := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_7_6_from_wound_host.{u} B σ d δ ε ν τ γ hB hσ
    hν hWidth hε hε₁ hτγ hγ (by linarith only [hDensity,hε]) hCost hFloor
    (by linarith only [hTol,hε]) K hK
  refine ⟨N,?_⟩
  intro V _ l b k n L G H Z₀ Z P A X R₀ hl hb hk hIndex hWinding
  subst n
  subst L
  intro m M r loss priorLoss α θ εOld μ τ₀ a η ξ β parent R Y hPartition hH hM hmN hm hLarge hProfile
    hLoss hPrior hβ hTolβ hLossβ hReg hSup hα hθ hτ₀α hεOld hθε hσ₁ hStyle hDemand
    hμ hμτ hτ₀ hOrder hLargeR hDegreeR hLoad ha hη hη₁ hScale hCTol hCLoss hGap hδ hδ₁ hFloor' hSTol hSLoss
  let e := ⌊(m:ℝ)*η⌋₊
  let cap := m/c
  have hm' : 0 < m := by omega
  obtain ⟨hCap,hEnds,hCapLower,hRoom,hLossM,hNm,hHall,hPay,hCut⟩ :=
    wound_exceptional_integral_budgets m c Z.card N ε δ η d hc hm hmN hε hη.le hη₁
      hScaleCap hTol hDensity hLarge
  obtain ⟨hRegD,hSupD⟩ := wound_host_pairs_after_deletion G H X R (finRotate (l*(b*k))) (K*m) loss
    ξ σ β d hH (Nat.mul_pos hK hm') (fun i => (hPartition.fine_size i).1) hσ hσ₁ hβ
    (by linarith only [hDensity,hε]) hTolβ hLossβ hLoss hReg hSup
  have hLoad' : (Z.card:ℝ)*(8/(μ^2/2)+6) < (cap:ℝ)*((μ^2/2)*((b*k:ℕ):ℝ)/16) :=
    hLoad.trans_le (mul_le_mul_of_nonneg_right hCapLower (by positivity))
  have hDemand' : (((2*Z.card+(2*Z.card)/cap*m+K*l*r+priorLoss):ℕ):ℝ) <
      (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) := by
    apply lt_of_le_of_lt _ hDemand
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hEnds (K*l*r)) priorLoss
  exact hN G H Z₀ Z P A X R₀ hl hb hk m M r e cap cap priorLoss α θ εOld μ τ₀ a η
    hH hCap hPartition.coarse_size hM hPartition.coarse_disjoint hPartition.coarse_cover
    hPartition.initial_exceptional_size hPartition.exceptional_degrees hPrior hPartition.fine_size
    hPartition.fine_disjoint hPartition.fine_ordinary hPartition.fine_cover hPartition.volume
    ((by omega : N ≤ m).trans (Nat.le_mul_of_pos_left _ hK)) hProfile hα hθ hτ₀α hεOld hθε hσ₁ hStyle
    hPartition.trimmed_loss hPartition.profile_in hPartition.profile_out hDemand'
    hPartition.reduced_loopless hμ hμτ hτ₀ hOrder hPartition.reduced_expansion hPartition.reduced_in
    hPartition.reduced_out hLargeR hDegreeR hLoad' hRoom hLossM hNm hHall hPay ha hη (by linarith only [hη₁])
    hScale hCTol hCLoss hGap hCut hδ hδ₁ hFloor' hSTol hSLoss hRegD hSupD

end OverfullWork.DirectedRobustExpansion
