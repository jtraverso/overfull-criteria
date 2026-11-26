module

public import PseudorandomLib.Theorem12

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Pseudorandom
open scoped Classical

/-- Relabel the vertices and weight functions by finite ordinals to apply
Ehard–Glock–Joos to finite types in arbitrary universes. -/
theorem egj_triangle_matching :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      IsUniform H 3 →
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 / 2 : ℝ)) →
      (H.card : ℝ) ≤ Real.exp (Δ ^ ((1 / 900 : ℝ) ^ 2)) →
      ∀ (J : Type*) [Fintype J] (w : J → Finset V → ℝ),
      (∀ j, ∀ S ∈ H, 0 ≤ w j S) →
      (Fintype.card J : ℝ) ≤ Real.exp (Δ ^ ((1 / 900 : ℝ) ^ 2)) →
      ∃ M ⊆ H, IsMatching M ∧
        ∀ j, (∀ S ∈ H, w j S * Δ ^ (3 / 2 : ℝ) ≤ weight (w j) H) →
          |weight (w j) M - weight (w j) H / Δ| ≤
            Δ ^ (-(1 / 900) : ℝ) * (weight (w j) H / Δ) := by
  obtain ⟨Δ₀,hΔ₀⟩ := Pseudorandom.theorem_1_2 (1/2) (by norm_num) (by norm_num) 3 (by decide)
  refine ⟨Δ₀,?_⟩
  intro Δ hΔ V _ _ H hu hd hc hH J _ w hw hJ
  let e := Fintype.equivFin V
  let f := e.finsetCongr
  let j := Fintype.equivFin J
  let H' := H.map f.toEmbedding
  let w' (i : Fin (Fintype.card J)) (S : Finset (Fin (Fintype.card V))) :=
    w (j.symm i) (f.symm S)
  have hMem (u : V) (S : Finset V) : e u ∈ f S ↔ u ∈ S := by
    simp [f,Equiv.finsetCongr_apply]
  have hWeight (i : J) (K : Finset (Finset V)) :
      weight (w' (j i)) (K.map f.toEmbedding) = weight (w i) K := by
    simp [weight,sum_map,w']
  have hU : IsUniform H' 3 := by
    intro S hS
    obtain ⟨T,hT,rfl⟩ := mem_map.mp hS
    simpa [f,Equiv.finsetCongr_apply] using hu T hT
  have hD (v : Fin (Fintype.card V)) : (degree H' v : ℝ) ≤ Δ := by
    obtain ⟨u,rfl⟩ := e.surjective v
    simpa [degree,H',filter_map,Function.comp_def,hMem] using hd u
  have hC (u v : Fin (Fintype.card V)) (hne : u ≠ v) :
      (codegree H' u v : ℝ) ≤ Δ ^ (1 / 2 : ℝ) := by
    obtain ⟨a,rfl⟩ := e.surjective u
    obtain ⟨b,rfl⟩ := e.surjective v
    simpa [codegree,H',filter_map,Function.comp_def,hMem] using hc a b (ne_of_apply_ne e hne)
  have hW (i : Fin (Fintype.card J)) (S : Finset (Fin (Fintype.card V))) (hS : S ∈ H') :
      0 ≤ w' i S := by
    obtain ⟨T,hT,rfl⟩ := mem_map.mp hS
    simpa [w'] using hw (j.symm i) T hT
  have he₁ : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  have he₂ : (1 : ℝ) + 1/2 = 3/2 := by norm_num
  have he₃ : (1/2 : ℝ) / (50 * (3 : ℕ) ^ 2) = 1/900 := by norm_num
  have hApply := hΔ₀ Δ hΔ (Fin (Fintype.card V)) H' hU hD
  rw [he₁,he₃,he₂] at hApply
  obtain ⟨M',hM',hMatch,hApprox⟩ := hApply hC (by simpa [H'] using hH)
    (Fin (Fintype.card J)) w' hW (by simpa using hJ)
  let M := M'.map f.symm.toEmbedding
  have hMap : M.map f.toEmbedding = M' := by
    ext S
    simp [M]
  refine ⟨M,?_,?_,?_⟩
  · intro S hS
    have hS' : f S ∈ M' := hMap ▸ mem_map.mpr ⟨S,hS,rfl⟩
    simpa [H'] using hM' hS'
  · intro S hS T hT hNe
    have hS' : f S ∈ M' := hMap ▸ mem_map.mpr ⟨S,hS,rfl⟩
    have hT' : f T ∈ M' := hMap ▸ mem_map.mpr ⟨T,hT,rfl⟩
    have hDisj := hMatch _ hS' _ hT' (fun h => hNe (f.injective h))
    exact disjoint_left.mpr fun u huS huT =>
      disjoint_left.mp hDisj ((hMem u S).mpr huS) ((hMem u T).mpr huT)
  · intro i hi
    have hWeightH := hWeight i H
    change weight (w' (j i)) H' = weight (w i) H at hWeightH
    have hWeightM := hWeight i M
    rw [hMap] at hWeightM
    have hApprox' := hApprox (j i) (by
      intro S hS
      obtain ⟨T,hT,rfl⟩ := mem_map.mp hS
      rw [hWeightH]
      simpa [w'] using hi T hT)
    simpa [hWeightH,hWeightM] using hApprox'

end OverfullWork.ChenShan
