module

public import OverfullWork.CaoChenKempeAugmentation
public import OverfullWork.FiniteImageSelection

@[expose] public section


/-! # Cao--Chen Proposition A, Claim 5.3

The good-leaf potential is maximized over actual rooted colourings. If
there are too few distinct good anchors, two bad edges share a non-A colour.
A protected common missing colour and an actual Kempe swap then improve the
potential. Both the selectors and the protected colour set are constructed.
-/
namespace OverfullWork.CaoChenForkSelection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenForkCounting
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 8000000

/-- The precise anchor family used in Claim 5.3. -/
def GoodAnchorFamily (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ) : Prop :=
  ∃ z t : Fin (d + 2) → V, Function.Injective z ∧ Function.Injective t ∧
    ∀ i, z i ∈ goodNeighbours c a b u ∧ t i ∈ goodSecondNeighbours c a b u ∧
      G.degree (t i) ≤ d ∧ Good c a b (z i) (t i)

private theorem second_leaf_ne_left {c : PEC G (Fin G.maxDegree)} {a b u t : V}
    (ht : t ∈ goodSecondNeighbours c a b u) : t ≠ a := by
  intro he
  subst t
  exact (mem_sdiff.mp ht).2 (mem_insert_self _ _)

private theorem second_leaf_coloured {c : PEC G (Fin G.maxDegree)} {a b u t z : V}
    (hcm : IsColMinus c a b) {α : Fin G.maxDegree} (hbu : c.col b u = some α)
    (ht : t ∈ goodSecondNeighbours c a b u) (hzt : G.Adj z t) : c.col z t ≠ none := by
  have hta := second_leaf_ne_left ht
  have htb : t ≠ b := by
    intro he
    subst t
    exact (mem_sdiff.mp ht).2 (mem_insert_of_mem (mem_insert_of_mem
      ((mem_neighborFinset G u b).mpr (c.col_adj hbu).symm)))
  have hh := hcm.total t z hzt.symm (sym2_ne_ab ⟨hta, htb⟩)
  rwa [c.col_symm] at hh

/-- Actual construction of a colouring and d+2 distinct A-good anchor edges.
No fork configuration, matching, or potential lower bound is supplied as a hypothesis. -/
theorem exists_good_anchor_family (hcrit : IsDeltaCritical G)
    (c₀ : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ)
    (hrooted : RootedAdmissible c₀ a b u) (hd : 2 ≤ d) (hda : G.degree a ≤ d)
    (hdelta : (d + 1) * (d + 3) ≤ G.maxDegree)
    (hbig : (d - 1)^2 + (d + 1) * (d - 1) + (d - 2) + 1 ≤
      (twoStepVertices G u ∩ smallVertices G d).card) :
    ∃ c : PEC G (Fin G.maxDegree), RootedAdmissible c a b u ∧ GoodAnchorFamily c a b u d := by
  classical
  obtain ⟨c, hc, hmaximal⟩ := exists_maximal_goodForkLeaves c₀ a b u d hrooted
  refine ⟨c, hc, ?_⟩
  by_contra hno
  obtain ⟨hcm, α, hbu, hα⟩ := hc
  let L := goodSecondNeighbours c a b u ∩ smallVertices G d
  let P := goodForkLeaves c a b u d
  have hPL : P ⊆ L := filter_subset _ _
  have hthreshold : 2 * d < G.maxDegree + 2 := by nlinarith
  have hPcard : P.card ≤ (d + 1) * (d - 1) := by
    by_contra hn
    have hcount : (d + 1) * (d - 1) < P.card := by omega
    exact hno (exists_good_anchors_of_many_goodForkLeaves hcrit c a b u d hd hthreshold hcount)
  have hsel : ∀ t ∈ L, ∃ z ∈ goodNeighbours c a b u,
      G.Adj z t ∧ (t ∈ P → Good c a b z t) := by
    intro t ht
    by_cases htp : t ∈ P
    · obtain ⟨z, hz, hgood⟩ := ((mem_goodForkLeaves c a b u d t).mp htp).2.2
      obtain ⟨ε, he, hε⟩ := hgood
      exact ⟨z, hz, c.col_adj he, fun _ => ⟨ε, he, hε⟩⟩
    · obtain ⟨z, hz, hzt⟩ := mem_biUnion.mp (mem_sdiff.mp (mem_inter.mp ht).1).1
      exact ⟨z, hz, (mem_neighborFinset G z t).mp hzt, fun hp => False.elim (htp hp)⟩
  let f : V → V := fun t => if ht : t ∈ L then Classical.choose (hsel t ht) else t
  have hf : ∀ t ∈ L, f t ∈ goodNeighbours c a b u ∧
      G.Adj (f t) t ∧ (t ∈ P → Good c a b (f t) t) := by
    intro t ht
    dsimp only [f]
    rw [dif_pos ht]
    exact Classical.choose_spec (hsel t ht)
  have hfGood : ∀ t ∈ P, f t ∈ goodNeighbours c a b u ∧ Good c a b (f t) t := by
    intro t ht
    exact ⟨(hf t (hPL ht)).1, (hf t (hPL ht)).2.2 ht⟩
  let Z := P.image f
  have hZcard : Z.card ≤ d + 1 := by
    by_contra hn
    have hm : d + 2 ≤ Z.card := by omega
    obtain ⟨z, t, hz, ht, hzt⟩ := exists_distinct_pairs_of_image_card P f (d + 2) hm
    apply hno
    refine ⟨z, t, hz, ht, ?_⟩
    intro i
    have hleaf := (mem_goodForkLeaves c a b u d (t i)).mp (hzt i).1
    have hgood := hfGood (t i) (hzt i).1
    rw [(hzt i).2] at hgood
    exact ⟨hgood.1, hleaf.1, hleaf.2.1, hgood.2⟩
  let B := L \ P
  have hL := good_second_small_card_lower_bound hcrit hcm hbu hα d hd hda hdelta hbig
  have hsplit : B.card + P.card = L.card := card_sdiff_add_card_eq_card hPL
  have hBadCard : d - 1 ≤ B.card := by change _ ≤ B.card; change _ ≤ L.card at hL; omega
  let κ : V → Fin G.maxDegree := fun t => (c.col (f t) t).getD α
  let β : V → Fin G.maxDegree := fun z => (c.col u z).getD α
  have hκ : ∀ t ∈ B, c.col (f t) t = some (κ t) := by
    intro t ht
    have htL := (mem_sdiff.mp ht).1
    have hcol := second_leaf_coloured hcm hbu (mem_inter.mp htL).1 (hf t htL).2.1
    cases he : c.col (f t) t with
    | none => exact False.elim (hcol he)
    | some ε => simp only [κ, he, Option.getD_some]
  have hκB : ∀ t ∈ B, κ t ∈ nonA c a b := by
    intro t ht
    apply mem_nonA.mpr
    intro hA
    have htL := (mem_sdiff.mp ht).1
    have hLeaf : t ∈ P := (mem_goodForkLeaves c a b u d t).mpr
      ⟨(mem_inter.mp htL).1, (mem_filter.mp (mem_inter.mp htL).2).2,
        f t, (hf t htL).1, κ t, hκ t ht, hA⟩
    exact (mem_sdiff.mp ht).2 hLeaf
  have hnonA := nonA_card_add_two_le_degree hcrit.2.1 hcm
  have hcard : (nonA c a b).card < B.card := by omega
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hcard hκB
  let γ := κ t₁
  have hγ : ¬ InA c a b γ := mem_nonA.mp (hκB t₁ ht₁)
  have hcol₁ : c.col (f t₁) t₁ = some γ := hκ t₁ ht₁
  have hcol₂ : c.col (f t₂) t₂ = some γ := by
    change c.col (f t₂) t₂ = some (κ t₁)
    rw [heq]
    exact hκ t₂ ht₂
  have ht₁L := (mem_sdiff.mp ht₁).1
  have ht₂L := (mem_sdiff.mp ht₂).1
  have ht₁small : G.degree t₁ ≤ d := (mem_filter.mp (mem_inter.mp ht₁L).2).2
  have ht₂small : G.degree t₂ ≤ d := (mem_filter.mp (mem_inter.mp ht₂L).2).2
  let F : Finset (Fin G.maxDegree) := ({α, β (f t₁), β (f t₂)} ∪ P.image κ) ∪ Z.image β
  have hFcard : F.card ≤ 3 + P.card + Z.card := by
    have h₁ := card_union_le ({α, β (f t₁), β (f t₂)} : Finset (Fin G.maxDegree)) (P.image κ)
    have h₂ := card_union_le (({α, β (f t₁), β (f t₂)} : Finset (Fin G.maxDegree)) ∪ P.image κ) (Z.image β)
    have h₃ : ({α, β (f t₁), β (f t₂)} : Finset (Fin G.maxDegree)).card ≤ 3 := card_le_three
    have h₄ := card_image_le (s := P) (f := κ)
    have h₅ := card_image_le (s := Z) (f := β)
    change (({α, β (f t₁), β (f t₂)} ∪ P.image κ) ∪ Z.image β).card ≤ 3 + P.card + Z.card
    omega
  let S : Finset V := {a, t₁, t₂}
  have hSdeg : (∑ v ∈ S, G.degree v) ≤ 3 * d := by
    have hp : ∀ v ∈ S, G.degree v ≤ d := by
      intro v hv
      simp only [S, mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hda
      · exact ht₁small
      · exact ht₂small
    calc
      _ ≤ ∑ _v ∈ S, d := sum_le_sum hp
      _ = S.card * d := by simp
      _ ≤ 3 * d := Nat.mul_le_mul_right d (card_le_three : S.card ≤ 3)
  have hbudget : (∑ v ∈ S, G.degree v) + F.card ≤ G.maxDegree := by
    have hm : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    nlinarith
  obtain ⟨δ, hδF, hδfree⟩ := CommonMissingColour.exists_common_free_outside_of_colMinus_budget
    hcm S F (by simp [S]) hbudget
  have hδα : δ ≠ α := by intro he; apply hδF; simp [F, he]
  have hβ₁ : β (f t₁) ≠ δ := by intro he; apply hδF; simp [F, ← he]
  have hβ₂ : β (f t₂) ≠ δ := by intro he; apply hδF; simp [F, ← he]
  have hδa : c.IsFree a δ := hδfree a (by simp [S])
  have hδ₁ : c.IsFree t₁ δ := hδfree t₁ (by simp [S])
  have hδ₂ : c.IsFree t₂ δ := hδfree t₂ (by simp [S])
  have hprotect : ∀ t ∈ P, c.col u (f t) ≠ some δ ∧ c.col (f t) t ≠ some δ := by
    intro t ht
    constructor
    · intro he
      have hβeq : β (f t) = δ := by simp [β, he]
      apply hδF
      exact mem_union.mpr (Or.inr (mem_image.mpr ⟨f t, mem_image.mpr ⟨t, ht, rfl⟩, hβeq⟩))
    · intro he
      have hκeq : κ t = δ := by simp [κ, he]
      apply hδF
      exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_image.mpr ⟨t, ht, hκeq⟩))))
  have hroot₁ : c.col u (f t₁) ≠ some δ := by intro he; apply hβ₁; simp [β, he]
  have hroot₂ : c.col u (f t₂) ≠ some δ := by intro he; apply hβ₂; simp [β, he]
  have ha₁ : a ≠ t₁ := (second_leaf_ne_left (mem_inter.mp ht₁L).1).symm
  have ha₂ : a ≠ t₂ := (second_leaf_ne_left (mem_inter.mp ht₂L).1).symm
  rcases exists_unlinked_of_two_free_leaves c ha₁ ha₂ hne hδa hδ₁ hδ₂ with hoff | hoff
  · obtain ⟨c', hc', hmore⟩ := promote_good_fork_leaf hcrit.2.1 hcm hbu hα hδα.symm
      ht₁L (mem_sdiff.mp ht₁).2 (hf t₁ ht₁L).1 hcol₁ hγ hδa hoff hroot₁ f hfGood hprotect
    exact (Nat.not_lt_of_ge (hmaximal c' hc')) hmore
  · obtain ⟨c', hc', hmore⟩ := promote_good_fork_leaf hcrit.2.1 hcm hbu hα hδα.symm
      ht₂L (mem_sdiff.mp ht₂).2 (hf t₂ ht₂L).1 hcol₂ hγ hδa hoff hroot₂ f hfGood hprotect
    exact (Nat.not_lt_of_ge (hmaximal c' hc')) hmore

end OverfullWork.CaoChenForkSelection
