module

public import OverfullWork.NearRegularBipartiteMatching
public import OverfullWork.RankedDirectedPathCover

@[expose] public section


/-! The dense-part path cover in Girão–Granet–Kühn–Lo–Osthus, Lemma
7.3(i): join near-perfect matchings between consecutive classes and
count the paths by the vertices with no leaving matching arc. -/
namespace OverfullWork.AdjacentLayerPathCover

open Finset NearRegularBipartiteMatching RankedDirectedPathCover
open scoped Classical
variable {V : Type*} [Fintype V]

abbrev Layer {k : ℕ} (rank : V → Fin (k+1)) (i : Fin (k+1)) := {x : V // rank x = i}

/-- Matchings are supplied only between consecutive layers. Their union
is a path cover of the entire host, including all isolated vertices. -/
theorem cover_of_adjacent_matchings (D : Digraph V) {k : ℕ} (rank : V → Fin (k+1))
    (M : ∀ i : Fin k, PartialMatching
      (fun x : Layer rank i.castSucc => fun y : Layer rank i.succ => D.Adj x.val y.val)) :
    ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
      (terminals H.Adj (univ : Finset V)).card+(∑ i, (M i).domain.card) = Fintype.card V := by
  classical
  let H : Digraph V :=
    ⟨fun x y => ∃ (i : Fin k) (a : (M i).domain), a.val.val = x ∧ ((M i).target a).val = y⟩
  let domains : Fin k → Finset V :=
    fun i => (M i).domain.map ⟨Subtype.val, Subtype.val_injective⟩
  have hLayer : ∀ i v, v ∈ domains i → rank v = i.castSucc := by
    intro i v hv
    obtain ⟨x,_,rfl⟩ := mem_map.mp hv
    exact x.prop
  have hApart : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint domains := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro v hi hj
    exact hij (Fin.castSucc_injective _ ((hLayer i v hi).symm.trans (hLayer j v hj)))
  let T : Finset V := (univ : Finset (Fin k)).biUnion domains
  have hCount : T.card = ∑ i, (M i).domain.card := by
    rw [show T = univ.biUnion domains from rfl, card_biUnion hApart]
    simp only [domains, card_map]
  have hLeaves : ∀ x, x ∈ T ↔ ∃ y, H.Adj x y := by
    intro x
    constructor
    · intro hx
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
      obtain ⟨a,ha,he⟩ := mem_map.mp hi
      exact ⟨((M i).target ⟨a,ha⟩).val,i,⟨a,ha⟩,he,rfl⟩
    · rintro ⟨y,i,a,rfl,_⟩
      exact mem_biUnion.mpr ⟨i,mem_univ _, mem_map.mpr ⟨a.val,a.prop,rfl⟩⟩
  have hTerm : terminals H.Adj (univ : Finset V) = univ \ T := by
    ext x
    simp only [terminals, mem_filter, mem_sdiff, mem_univ, true_and, true_implies, hLeaves, not_exists]
  have hRank : ∀ {x y}, H.Adj x y → (rank x).val < (rank y).val := by
    rintro x y ⟨i,a,rfl,rfl⟩
    rw [a.val.prop, ((M i).target a).prop]
    exact Nat.lt_succ_self _
  have hIn : ∀ {x y z}, H.Adj x z → H.Adj y z → x = y := by
    rintro x y z ⟨i,a,rfl,ha⟩ ⟨j,b,rfl,hb⟩
    have hij : i.succ = j.succ := by
      rw [← ((M i).target a).prop, ← ((M j).target b).prop, ha,hb]
    have he : i = j := Fin.succ_injective _ hij
    subst j
    have hb' : a = b := (M i).target.injective (Subtype.ext (ha.trans hb.symm))
    exact congrArg (fun (w : (M i).domain) => w.val.val) hb'
  refine ⟨H,?_,exists_cover H.Adj (fun x => (rank x).val) hRank hIn univ,?_⟩
  · rintro x y ⟨i,a,rfl,rfl⟩
    exact (M i).adjacent a
  · rw [hTerm, ← hCount]
    exact (card_sdiff_add_card_eq_card (subset_univ T)).trans card_univ

/-- A near-biregular sequence of layers gives an actual directed path
cover with a real bound on the number of paths. The width and degree
errors are separate, as in the proof of Lemma 7.3(i). -/
theorem exists_cover_of_near_regular_layers (D : Digraph V) {k : ℕ}
    (rank : V → Fin (k+1)) (b δ a e : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ha : 0 ≤ a)
    (hae : a ≤ e) (he : e ≤ δ)
    (hLower : ∀ i, (1-a)*b ≤ (Fintype.card (Layer rank i):ℝ))
    (hUpper : ∀ i, (Fintype.card (Layer rank i):ℝ) ≤ (1+a)*b)
    (hOut : ∀ (i : Fin k) (x : Layer rank i.castSucc),
      (δ-e)*b ≤ (((univ : Finset (Layer rank i.succ)).filter (fun y => D.Adj x.val y.val)).card:ℝ))
    (hIn : ∀ (i : Fin k) (y : Layer rank i.succ),
      (((univ : Finset (Layer rank i.castSucc)).filter (fun x => D.Adj x.val y.val)).card:ℝ) ≤
        (δ+e)*b) :
    ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
      ((terminals H.Adj (univ : Finset V)).card:ℝ) ≤ (1+a)*b+(k:ℝ)*(a+3*e/δ)*b := by
  classical
  have hLayer : ∀ i : Fin k, ∃ M : PartialMatching
      (fun x : Layer rank i.castSucc => fun y : Layer rank i.succ => D.Adj x.val y.val),
      (1-3*e/δ)*b ≤ (M.domain.card:ℝ) := by
    intro i
    have hLo := hLower i.castSucc
    have hScale := mul_le_mul_of_nonneg_right hae hb.le
    exact exists_near_regular_matching _ b δ e hb (ha.trans hae) he hδ hδ₁
      (by linarith only [hScale,hLo]) (hOut i) (hIn i)
  choose M hM using hLayer
  obtain ⟨H,hD,hC,hCount⟩ := cover_of_adjacent_matchings D rank M
  let idx : V ≃ Σ i, Layer rank i := (Equiv.sigmaFiberEquiv rank).symm
  have hn : Fintype.card V = ∑ i : Fin (k+1), Fintype.card (Layer rank i) := by
    rw [Fintype.card_congr idx, Fintype.card_sigma]
  have hTot : (Fintype.card V:ℝ) ≤ ((k:ℝ)+1)*((1+a)*b) := by
    have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (k+1)))) => hUpper i)
    rw [hn, Nat.cast_sum]
    simpa using h
  have hGood : (k:ℝ)*((1-3*e/δ)*b) ≤ ∑ i : Fin k, ((M i).domain.card:ℝ) := by
    simpa using (sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin k))) => hM i) :
      (∑ _i : Fin k, (1-3*e/δ)*b) ≤ ∑ i : Fin k, ((M i).domain.card:ℝ))
  have hEq : ((terminals H.Adj (univ : Finset V)).card:ℝ)+
      (∑ i : Fin k, ((M i).domain.card:ℝ)) = (Fintype.card V:ℝ) := by
    exact_mod_cast hCount
  refine ⟨H,hD,hC,?_⟩
  calc
    _ ≤ ((k:ℝ)+1)*((1+a)*b)-(k:ℝ)*((1-3*e/δ)*b) := by linarith only [hEq,hTot,hGood]
    _ = _ := by ring

end OverfullWork.AdjacentLayerPathCover
