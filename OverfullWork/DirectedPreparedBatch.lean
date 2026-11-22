module

public import OverfullWork.DirectedGreedyBatch
public import OverfullWork.DirectedInducedPerturbation

@[expose] public section


/-! The small-batch construction with numerical margins on the initial
blocks. All profile and expansion requirements of later rounds follow
from these margins and the actual used-arc invariant. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage DirectedReserveStitching InducedDigraphSampling
open scoped Classical
universe u v w

private theorem incoming_profile_loss {V : Type*} [Fintype V] {D E : Digraph V}
    (h : E ≤ D) (g : ℕ) (hg : ∀ v, inDegree (D \ E) v ≤ g) (A : Finset V) (x : V) :
    (A.filter (fun v => D.Adj v x)).card ≤ (A.filter (fun v => E.Adj v x)).card+g ∧
    (A.filter (fun v => E.Adj v x)).card ≤ (A.filter (fun v => D.Adj v x)).card := by
  simpa only [sdiff_self,bot_eq_empty,card_empty,Nat.add_zero] using
    profile_count_perturbation A A (fun v => D.Adj v x) (fun v => E.Adj v x)
      (fun _ he => h he) g (by simpa only [inDegree,inNeighbours,Digraph.sdiff_adj] using hg x)

private theorem outgoing_profile_loss {V : Type*} [Fintype V] {D E : Digraph V}
    (h : E ≤ D) (g : ℕ) (hg : ∀ v, outDegree (D \ E) v ≤ g) (A : Finset V) (x : V) :
    (A.filter (D.Adj x)).card ≤ (A.filter (E.Adj x)).card+g ∧
    (A.filter (E.Adj x)).card ≤ (A.filter (D.Adj x)).card := by
  simpa only [sdiff_self,bot_eq_empty,card_empty,Nat.add_zero] using
    profile_count_perturbation A A (D.Adj x) (E.Adj x)
      (fun _ he => h he) g (by simpa only [outDegree,Digraph.sdiff_adj] using hg x)

private theorem induced_inDegree_filter {V : Type*} [Fintype V] (D : Digraph V)
    (A : Finset V) (x : A) :
    inDegree (induced D A) x = (A.filter (fun v => D.Adj v x.val)).card := by
  rw [induced_inDegree]
  congr 1
  ext v
  simp [inProfile]

private theorem induced_outDegree_filter {V : Type*} [Fintype V] (D : Digraph V)
    (A : Finset V) (x : A) :
    outDegree (induced D A) x = (A.filter (D.Adj x.val)).card := by
  rw [induced_outDegree]
  congr 1
  ext v
  simp [outProfile]

private theorem abs_deviation_after_loss (old now g : ℕ) (c e : ℝ)
    (h₁ : old ≤ now+g) (h₂ : now ≤ old) (h : |(old:ℝ)-c| ≤ e) :
    |(now:ℝ)-c| ≤ e+(g:ℝ) := by
  obtain ⟨hL,hH⟩ := abs_le.mp h
  have hLo : (old:ℝ) ≤ (now:ℝ)+g := by exact_mod_cast h₁
  have hHi : (now:ℝ) ≤ old := by exact_mod_cast h₂
  have hg : 0 ≤ (g:ℝ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith only [hL,hLo],by linarith only [hH,hHi,hg]⟩

/-- Pack all layouts of a small batch from initial block margins. The
reserve budget depends on block visits and short-interior capacity,
whereas dense profiles can pay for every round of this small batch. -/
theorem exists_prepared_batch_uniform_in_density (ν τ α d₀ ρ η : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η)
    (hGap : 8*η ≤ d₀) (hScale : 52*η ≤ ρ*d₀) :
    ∃ N₀ N₁ : ℕ, ∀ (δ : ℝ), d₀ ≤ δ → δ ≤ 1 →
    ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
      (D Γ : Digraph V) (L : J → Layout V I) (long : J → I) (A : J → Finset V)
      (b a cap q z h : ℕ) (ν₀ μ₀ μ ε₀ ε : ℝ),
      let d := Fintype.card J+b
      let g := b+2*cap+2*a
      Disjoint D Γ → 0 ≤ μ → 0 < cap → Fintype.card J*q ≤ cap*z →
      (∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b) →
      (∀ v, visits A v ≤ a) →
      (∀ i, let B : Finset V := (A i)ᶜ
        let k := (univ \ insert (long i) (L i).fixed).card*h
        let r := ⌈μ*(B.card:ℝ)⌉₊
        let t := ⌈τ*(B.card:ℝ)⌉₊
        long i ∉ (L i).fixed ∧ Disjoint (L i).boundary (A i) ∧
        0 < (A i).card ∧ N₀ ≤ (A i).card ∧ N₁+(L i).boundary.card+k ≤ B.card ∧ k ≤ q ∧
        IsRealRobust (induced Γ (A i)) ν₀ τ ∧
        ν*((A i).card:ℝ)+(g:ℝ) ≤ ν₀*((A i).card:ℝ) ∧
        (∀ x : A i, α*((A i).card:ℝ)+(g:ℝ) ≤ (inDegree (induced Γ (A i)) x:ℝ) ∧
          α*((A i).card:ℝ)+(g:ℝ) ≤ (outDegree (induced Γ (A i)) x:ℝ)) ∧
        IsRealRobust (induced Γ B) μ₀ τ ∧ μ*(B.card:ℝ)+(g:ℝ) ≤ μ₀*(B.card:ℝ) ∧
        (∃ s : ℕ, 0 < s ∧ B.card/s+5 ≤ h ∧ z+(L i).boundary.card+k+s ≤ r) ∧
        (∀ x : B, t+g ≤ inDegree (induced Γ B) x ∧
          t+z+(L i).boundary.card+k+1+g ≤ outDegree (induced Γ B) x) ∧
        ProfilesAround D B δ ε₀ ∧ ε₀*(B.card:ℝ)+(d:ℝ) ≤ ε*(B.card:ℝ) ∧
        ε*(B.card:ℝ)+((L i).boundary.card+k:ℕ)+1 ≤ η*((B.card:ℝ)-((L i).boundary.card+k:ℕ)) ∧
        ρ*((B.card:ℝ)+1) ≤ (ν/4)^3*((A i).card:ℝ) ∧
        (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1)+(d:ℝ) ≤ (((A i).filter (fun x => D.Adj y x)).card:ℝ) ∧
          2*ρ*((B.card:ℝ)+1)+(d:ℝ) ≤ (((A i).filter (fun x => D.Adj x y)).card:ℝ))) →
      Nonempty (BatchPrefix D Γ L long A (univ : Finset J) cap q) := by
  obtain ⟨N₀,N₁,hExec⟩ := exists_layout_round_uniform_in_density.{u,v}
    ν τ α d₀ ρ η hν hντ hτα hα hd₀ hρ hη hGap hScale
  refine ⟨N₀,N₁,?_⟩
  intro δ hδ₀ hδ₁
  intro V _ I _ J _ D Γ L long A b a cap q z h ν₀ μ₀ μ ε₀ ε
  dsimp only
  intro hDΓ hμ hcap hz hEnds hBlocks hMargins
  apply exists_batch_of_rounds D Γ hDΓ L long A b a cap q z hcap hz hEnds hBlocks
  intro i D' Γ' Z hD hΓ hZ hZS hLossD hLossΓ
  let B : Finset V := (A i)ᶜ
  let d := Fintype.card J+b
  let g := b+2*cap+2*a
  let k := (univ \ insert (long i) (L i).fixed).card*h
  let r := ⌈μ*(B.card:ℝ)⌉₊
  let t := ⌈τ*(B.card:ℝ)⌉₊
  obtain ⟨hLong,hApart,hPos,hN₀,hN₁,hk,hRA,hReserveA,hMinA,hRB,hReserveB,
    ⟨s,hs,hLen,hRBudget⟩,hMinB,hProfile,hPBudget,hSlack,hCount,hAttach⟩ := hMargins i
  have hRA' := induced_real_robust_of_perturbation Γ Γ' (A i) (A i) ν₀ τ ν τ g hRA hΓ
    (fun x => (hLossΓ x).1) (by simp) (by rfl) (by simpa [g] using hReserveA)
  have hRB' := induced_real_robust_of_perturbation Γ Γ' B B μ₀ τ μ τ g hRB hΓ
    (fun x => (hLossΓ x).1) (by simp) (by rfl) (by simpa [g,B] using hReserveB)
  have hShortRob : IsRobustAt (induced Γ' B) r t := by
    simpa only [r,t,Fintype.card_coe] using integer_of_real (induced Γ' B) μ τ hμ hRB'
  have hIn (X : Finset V) (x : X) :
      inDegree (induced Γ X) x ≤ inDegree (induced Γ' X) x+g := by
    simpa only [induced_inDegree_filter] using
      (incoming_profile_loss hΓ g (fun v => (hLossΓ v).1) X x.val).1
  have hOut (X : Finset V) (x : X) :
      outDegree (induced Γ X) x ≤ outDegree (induced Γ' X) x+g := by
    simpa only [induced_outDegree_filter] using
      (outgoing_profile_loss hΓ g (fun v => (hLossΓ v).2) X x.val).1
  have hMinInA (x : A i) : α*(Fintype.card (A i):ℝ) ≤ (inDegree (induced Γ' (A i)) x:ℝ) := by
    have hh : (inDegree (induced Γ (A i)) x:ℝ) ≤ (inDegree (induced Γ' (A i)) x:ℝ)+g := by
      exact_mod_cast hIn (A i) x
    simpa only [Fintype.card_coe] using (show α*((A i).card:ℝ) ≤ _ by
      linarith only [hh,(hMinA x).1])
  have hMinOutA (x : A i) : α*(Fintype.card (A i):ℝ) ≤ (outDegree (induced Γ' (A i)) x:ℝ) := by
    have hh : (outDegree (induced Γ (A i)) x:ℝ) ≤ (outDegree (induced Γ' (A i)) x:ℝ)+g := by
      exact_mod_cast hOut (A i) x
    simpa only [Fintype.card_coe] using (show α*((A i).card:ℝ) ≤ _ by
      linarith only [hh,(hMinA x).2])
  have hProfile' : ProfilesAround D' B δ ε := by
    intro x hx
    have hi := incoming_profile_loss hD d (fun v => (hLossD v).1) B x
    have ho := outgoing_profile_loss hD d (fun v => (hLossD v).2) B x
    exact ⟨(abs_deviation_after_loss _ _ _ _ _ hi.1 hi.2 (hProfile x hx).1).trans hPBudget,
      (abs_deviation_after_loss _ _ _ _ _ ho.1 ho.2 (hProfile x hx).2).trans hPBudget⟩
  have hTo (x : V) (hx : x ∈ B) : 2*ρ*((B.card:ℝ)+1) ≤
      (((A i).filter (fun y => D'.Adj x y)).card:ℝ) := by
    have hl := (outgoing_profile_loss hD d (fun v => (hLossD v).2) (A i) x).1
    have hh : (((A i).filter (fun y => D.Adj x y)).card:ℝ) ≤
        (((A i).filter (fun y => D'.Adj x y)).card:ℝ)+(d:ℝ) := by exact_mod_cast hl
    linarith only [hh,(hAttach x hx).1]
  have hFrom (x : V) (hx : x ∈ B) : 2*ρ*((B.card:ℝ)+1) ≤
      (((A i).filter (fun y => D'.Adj y x)).card:ℝ) := by
    have hl := (incoming_profile_loss hD d (fun v => (hLossD v).1) (A i) x).1
    have hh : (((A i).filter (fun y => D.Adj y x)).card:ℝ) ≤
        (((A i).filter (fun y => D'.Adj y x)).card:ℝ)+(d:ℝ) := by exact_mod_cast hl
    linarith only [hh,(hAttach x hx).2]
  obtain ⟨R,hPath,hShort⟩ := hExec δ hδ₀ hδ₁ D' Γ' (L i) (long i) (A i) Z r s t h ε
    hLong hApart hZ hPos hN₀ (by simpa only [k,Nat.add_assoc] using hN₁) hRA' hMinInA hMinOutA
    hShortRob hs (by simpa only [Fintype.card_coe] using hLen)
    (by
      change Z.card+((L i).boundary.card+k)+s ≤ r
      have hBase : z+((L i).boundary.card+k)+s ≤ r := by
        simpa only [k,Nat.add_assoc] using hRBudget
      omega)
    (fun x => by
      have h₁ := (hMinB x).1
      have h₂ := hIn B x
      change t+g ≤ inDegree (induced Γ B) x at h₁
      change t ≤ inDegree (induced Γ' B) x
      omega)
    (fun x => by
      have h₁ := (hMinB x).2
      have h₂ := hOut B x
      change t+z+(L i).boundary.card+k+1+g ≤ outDegree (induced Γ B) x at h₁
      change t+Z.card+((L i).boundary.card+k)+1 ≤ outDegree (induced Γ' B) x
      omega)
    hProfile' hSlack hCount hTo hFrom
  refine ⟨R,?_,?_,hPath⟩
  · apply le_trans _ hk
    apply card_biUnion_le_card_mul
    intro j hj
    exact (List.toFinset_card_le _).trans (hShort j (mem_sdiff.mp hj).2).2.1
  · apply disjoint_left.mpr
    intro x hx hz
    obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp hx
    exact (hShort j (mem_sdiff.mp hj).2).2.2 x (List.mem_toFinset.mp hxj) hz

theorem exists_batch_from_prepared_blocks_threshold (ν τ α δ ρ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ N₁ : ℕ,
    ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
      (D Γ : Digraph V) (L : J → Layout V I) (long : J → I) (A : J → Finset V)
      (b a cap q z h : ℕ) (ν₀ μ₀ μ ε₀ ε : ℝ),
      let d := Fintype.card J+b
      let g := b+2*cap+2*a
      Disjoint D Γ → 0 ≤ μ → 0 < cap → Fintype.card J*q ≤ cap*z →
      (∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b) →
      (∀ v, visits A v ≤ a) →
      (∀ i, let B : Finset V := (A i)ᶜ
        let k := (univ \ insert (long i) (L i).fixed).card*h
        let r := ⌈μ*(B.card:ℝ)⌉₊
        let t := ⌈τ*(B.card:ℝ)⌉₊
        long i ∉ (L i).fixed ∧ Disjoint (L i).boundary (A i) ∧
        0 < (A i).card ∧ N₀ ≤ (A i).card ∧ N₁+(L i).boundary.card+k ≤ B.card ∧ k ≤ q ∧
        IsRealRobust (induced Γ (A i)) ν₀ τ ∧
        ν*((A i).card:ℝ)+(g:ℝ) ≤ ν₀*((A i).card:ℝ) ∧
        (∀ x : A i, α*((A i).card:ℝ)+(g:ℝ) ≤ (inDegree (induced Γ (A i)) x:ℝ) ∧
          α*((A i).card:ℝ)+(g:ℝ) ≤ (outDegree (induced Γ (A i)) x:ℝ)) ∧
        IsRealRobust (induced Γ B) μ₀ τ ∧ μ*(B.card:ℝ)+(g:ℝ) ≤ μ₀*(B.card:ℝ) ∧
        (∃ s : ℕ, 0 < s ∧ B.card/s+5 ≤ h ∧ z+(L i).boundary.card+k+s ≤ r) ∧
        (∀ x : B, t+g ≤ inDegree (induced Γ B) x ∧
          t+z+(L i).boundary.card+k+1+g ≤ outDegree (induced Γ B) x) ∧
        ProfilesAround D B δ ε₀ ∧ ε₀*(B.card:ℝ)+(d:ℝ) ≤ ε*(B.card:ℝ) ∧
        ε*(B.card:ℝ)+((L i).boundary.card+k:ℕ)+1 ≤ η*((B.card:ℝ)-((L i).boundary.card+k:ℕ)) ∧
        ρ*((B.card:ℝ)+1) ≤ (ν/4)^3*((A i).card:ℝ) ∧
        (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1)+(d:ℝ) ≤ (((A i).filter (fun x => D.Adj y x)).card:ℝ) ∧
          2*ρ*((B.card:ℝ)+1)+(d:ℝ) ≤ (((A i).filter (fun x => D.Adj x y)).card:ℝ))) →
      Nonempty (BatchPrefix D Γ L long A (univ : Finset J) cap q) := by
  let η := min (δ/8) (ρ*δ/52)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hGap : 8*η ≤ δ := by
    have h : η ≤ δ/8 := min_le_left _ _
    linarith only [h]
  have hScale : 52*η ≤ ρ*δ := by
    have h : η ≤ ρ*δ/52 := min_le_right _ _
    linarith only [h]
  obtain ⟨N₀,N₁,hN⟩ := exists_prepared_batch_uniform_in_density.{u,v,w} ν τ α δ ρ η
    hν hντ hτα hα hδ hρ hη hGap hScale
  exact ⟨η,hη,N₀,N₁,hN δ le_rfl hδ₁⟩

end OverfullWork.DirectedSpanningConfiguration
