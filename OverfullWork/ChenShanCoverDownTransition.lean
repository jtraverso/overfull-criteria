module

public import OverfullWork.ChenShanCoverDownRoundComposition
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

set_option maxHeartbeats 600000 in
/-- The concrete Step 2 transition, from residual prefix estimates and
explicit size and hierarchy inequalities. It selects the crossing
reserve, carries out the repair and both triangle covers, and returns
the next balanced graph with its protected prefix intact. -/
theorem exists_cover_down_transition
    {η η₀ μ ζ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hη₀ : 0 < η₀) (hη₀small : η₀ ≤ 1/80) (hEta : 40*η₀ ≤ η) (hηhalf : η ≤ 1/2)
    (hμ : 0 < μ) (hμsmall : 10*μ ≤ 1) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ n₀ N₀ : ℕ, ε₀ = coverDownPackingCap (η/2/2) ∧ 0 < ε₀ ∧
    ∀ (S : NestedTripartitePrefixes A B W ρ m k l) (i N : ℕ), i+1 ≤ l →
    ∀ (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop) (δ ξ : ℝ),
    let n := nestedCoreSize ρ m i
    let s := nestedCoreSize ρ m (i+1)
    let U := S.vertices (i+1)
    let X := S.vertices i \ U
    let K := coverDownProtected S i
    let G := tripartiteArcs E P Q
    let GU := G ∩ (U ×ˢ U)
    let ε := δ+4*ρ+10*μ
    n₀ ≤ n → N₀ ≤ N → 0 < m → 0 ≤ δ → 0 < ξ →
    6 ≤ ρ*(n:ℝ) → 1 ≤ δ*n →
    1/2+η ≤ (k:ℝ)/m → (k:ℝ)/m ≤ 3/2 → 1/2 ≤ η*n →
    18*δ ≤ η*ρ → (8/η)*(16*δ/ρ) ≤ η₀/100 → ξ ≤ η₀*(μ*ρ)/2 →
    5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < (n:ℝ) →
    1/2 ≤ ξ*n → ε ≤ η/2 → ε ≤ 1/16 →
    Real.sqrt (4*ξ) ≤ min ((η/2)/32) (1/128) →
    ε+5*Real.sqrt (4*ξ) ≤ ε₀ → 5*Real.sqrt (4*ξ) ≤ ζ/2 →
    ρ*(n:ℝ) ≤ N → (N:ℝ) ≤ 4*ρ*n → U.card ≤ 3*N → (X.card : ℝ) ≤ 4*n →
    120000*μ^(3/2:ℝ)*n ≤ η₀*μ*(ρ*n)/8 → ζ*n ≤ μ*(ρ*n)/8 →
    2*ζ*n < μ^2*ρ*n/20 → ζ*n ≤ 10*μ*n →
    (∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+ξ*n+(3/2+η₀)*(ζ*n) ≤
      7*η₀*(μ*(ρ*n)/4)) →
    TripartiteResidualPrefixBounds E P Q S i (δ*n) →
    G ⊆ S.vertices i ×ˢ S.vertices i → ArcBalanced G →
    (∀ v, |(arcDivergence GU v : ℝ)| ≤ 2*ξ*s+1/2) →
    ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)), ∃ M : TripartiteArcSet A B W,
      (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = G \ (GU \ M) ∧
      M ⊆ GU \ (K ×ˢ K) ∧ (∀ v, (incidentDegree M v : ℝ) ≤ 20*μ*n) ∧
      ArcBalanced (GU \ M) ∧ (GU \ M) ∩ (K ×ˢ K) = GU ∩ (K ×ˢ K) := by
  have hη : 0 < η := by linarith only [hEta,hη₀]
  have hρone : ρ ≤ 1 := by linarith only [hρsmall]
  have hμcap : μ < 1/4 := by linarith only [hμsmall]
  obtain ⟨ε₀,n₀,hPackingCap,hε₀,hCut⟩ := exists_concrete_cover_down_leave
    (A := A) (B := B) (W := W) (ρ := ρ) (m := m) (k := k) (l := l) η ζ hη hηhalf hζ
  obtain ⟨N₀,hAfter⟩ := exists_cover_down_transition_after_cut
    (A := A) (B := B) (W := W) (ρ := ρ) (m := m) (k := k) (l := l)
    hρ hρone hμ hμsmall hη₀.le
  refine ⟨ε₀,n₀,N₀,hPackingCap,hε₀,?_⟩
  intro S i N hi E P Q δ ξ n s U X K G GU ε hn hN₀ hm hδ hξ hInit hδn
    hDensity hRatio hηn hMin hClose hξsmall hLarge hRound hMargin hCap hSmall hThreshold hRepair
    hN hNup hU hX hCost hζSmall hExteriorCost hLoadCost hProtect hb hSupport hBal hInterior
  obtain ⟨R,hR,hCross,hR1,hR2,hR3,hR4,hR5⟩ :=
    exists_crossing_graph_reserve_all_five S i hi hm hη₀ hη₀small hEta hηhalf hρ hρsmall hδ
      hInit hδn hDensity hRatio hMin hClose hμ hμcap hξ hξsmall hb hLarge
  have hR' : R ⊆ G \ GU := by
    intro e he
    have hh := hR he
    simp only [mem_sdiff] at hh ⊢
    exact ⟨hh.1,fun hu => hh.2 (mem_inter.mp hu).2⟩
  have hInit' : 1 ≤ ρ*(n:ℝ) := by linarith only [hInit]
  obtain ⟨L,T,hL,hLDeg,hT,hCovered,hTBal⟩ := hCut S i hi E P Q R δ μ ξ hn hm hρ
    hρsmall hInit' hDensity hRatio hηn hξ.le hRound (by positivity) hMargin hCap hSmall
    hThreshold hRepair hb hSupport hR' hBal hInterior hR1
  let f := prefixVertexEmbedding S i
  let T₀ := (triangleHypergraph T).map (mapEmbedding (f.prodMap f)).toEmbedding
  obtain ⟨hT₀,hCert₀,hMap⟩ := map_cover_down_packing f (triangleHypergraph T) hT
    (triangleHypergraph_cover_down_certificate T)
  let Lmap := L.map (f.prodMap f)
  have hL' : Lmap ⊆ (G \ GU) \ R := by
    intro e he
    have hh := hL he
    simp only [G,GU,U,coverDownRemainder,mem_sdiff,mem_inter,mem_product] at hh ⊢
    exact hh
  have hCov₀ : coveredEdges T₀ = ((G \ GU) \ R) \ Lmap := by
    rw [hMap]
    convert hCovered.symm using 1 <;> first | rfl | (ext e; simp only [G,GU,U,Lmap,f,coverDownRemainder,mem_sdiff,mem_inter,mem_product])
  have hFilter (Z : Finset (TripartiteVertex A B W)) (v : TripartiteVertex A B W) :
      arcNeighborsIn Z R v = Z.filter (fun z => (v,z) ∈ R ∨ (z,v) ∈ R) := by
    ext z
    simp only [mem_arcNeighborsIn,mem_filter]
  have h := hAfter N hN₀ S i E P Q R Lmap T₀ ξ ζ hN hNup hU hX hCost hζSmall
    (by positivity) hExteriorCost hLoadCost hProtect hSupport hR'
    (fun ⟨a,b⟩ he => hCross a b he) (fun v => (hR1 v).2)
    (by
      intro v hv c hc
      rw [hFilter]
      convert (hR2 v hv c hc).1 using 1)
    (by
      intro u hu v hv hne
      have hh := hR3 u hu v hv hne
      have he : arcNeighborsIn U R u ∩ arcNeighborsIn U R v =
          U.filter (fun z => ((u,z) ∈ R ∨ (z,u) ∈ R) ∧ ((v,z) ∈ R ∨ (z,v) ∈ R)) := by
        ext z
        simp only [mem_inter,mem_arcNeighborsIn,mem_filter]
        exact ⟨fun h => ⟨h.1.1,h.1.2,h.2.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,⟨h.1,h.2.2⟩⟩⟩
      dsimp only at hh ⊢
      rw [he]
      exact hh)
    (by
      intro u hu x hx hne
      dsimp only
      rw [hFilter]
      convert hR4 u hu x hx hne using 1)
    (by
      intro v hv c
      dsimp only
      rw [hFilter]
      convert hR5 v hv c using 1)
    hL' hLDeg hT₀ hCert₀ hCov₀ hTBal
  exact h

end OverfullWork.ChenShan
