module

public import OverfullWork.EfficientSeed

@[expose] public section


namespace SimpleGraph.MultiGraph

open scoped Classical

/-- The vertex partition's sixth-moment bound also suffices for splitting
the palette used by the approximate multicolouring theorem. -/
theorem palette_size_of_partition_size (m D r : ℕ) (hm : 1≤m) (hD : D≤2*m)
    (hr : r≤m) (hsize : 30*(m:ℝ)^4<(r:ℝ)^6) :
    15*(2*m:ℝ)*((D/2+r)/2+1:ℕ)^3<(2*r:ℝ)^6 := by
  have hq : (D/2+r)/2+1≤2*m := by omega
  have hq' : (((D/2+r)/2+1:ℕ):ℝ)≤2*(m:ℝ) := by exact_mod_cast hq
  have hpow:=pow_le_pow_left₀ (Nat.cast_nonneg ((D/2+r)/2+1)) hq' 3
  have hmul:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
  have he : (15:ℝ)*(2*(m:ℝ))*(2*(m:ℝ))^3=240*(m:ℝ)^4 := by ring
  have hr0 : (0:ℝ)≤(r:ℝ)^6 := by positivity
  calc
    _ ≤ 240*(m:ℝ)^4 := by simpa only [he] using hmul
    _ < 64*(r:ℝ)^6 := by linarith
    _ = _ := by ring

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Direct small-deficiency seed for the original saturated graph. No
choice of colouring, balancing permutation or missing-vertex pairing is
assumed. The size condition is an explicit numerical sixth-moment bound. -/
theorem exists_point_efficient_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m r : ℕ) (hr1 : 1≤r) (hrm : r≤m)
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree)
    (hsize : 30*(m:ℝ)^4<(r:ℝ)^6) :
    ∃ (L : Finset (Option V)) (k : ℕ)
      (C : ((pointExtension G).internalPart L).EdgeColoring k),
      L.card=m ∧ Lᶜ.card=m ∧ none∈L ∧ some y∉L ∧
      k≤G.maxDegree/2+3*r+2 ∧ m≤2*k ∧
      (∀ i,(C.colourGraph i).edgesWithin L=(C.colourGraph i).edgesWithin Lᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin L≤(C.colourGraph j).edgesWithin L+1) ∧
      (∀ v,(C.missingPalette v).card≤4*r+4) ∧
      (∀ i,(C.missingSet L i).card=(C.missingSet Lᶜ i).card) ∧
      ∀ i,(C.missingSet L i).card≤8*r+10 := by
  obtain ⟨L,hL,hB,hx,hy,hdis⟩:=exists_balanced_point_partition G y m hcard hgap
    (r:ℝ) (Nat.cast_nonneg _) hsize
  haveI : Nonempty V:=⟨y⟩
  have hn : 1≤Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hm : 1≤m := by omega
  have hc : Fintype.card (Option V)=2*m := by simpa only [Fintype.card_option] using hcard
  have hD : G.maxDegree≤2*m := by have h:=G.maxDegree_lt_card_verts; omega
  have hmD : m≤G.maxDegree := by omega
  have hpalette:=MultiGraph.palette_size_of_partition_size m G.maxDegree r hm hD hrm hsize
  obtain ⟨k,C,hk,hkm,hbal,heq,hvert,hmiss,hcol⟩ := (pointExtension G).exists_efficient_balanced_internal
    L m G.maxDegree r hr1 hc hL hB (regular_of_saturated G hn hsat)
    (multiplicity_le_two G hgap) hmD hdis hpalette
  exact ⟨L,k,C,hL,hB,hx,hy,hk,hkm,hbal,heq,hvert,hmiss,hcol⟩

end OverfullWork.MultigraphExtension
