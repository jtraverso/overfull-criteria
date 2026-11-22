module

public import OverfullWork.KuhnOsthusAugmentedChordBalance
public import OverfullWork.KuhnOsthusOrderedResidue

@[expose] public section


/-! Calculate the exact locally balanced loads of each matching of
an ordinary 1-factor in Kühn–Osthus Lemma 9.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedDemandHall
open scoped Classical
variable {W I E : Type*} [Fintype W] [Fintype I] [Fintype E]

/-- Express the arc partition of a permutation by the label of
the source of each arc. -/
theorem OrderedResidueMatchings.exists_source_labels {H : Digraph W} {g q c m h : ℕ}
    [NeZero g] {coarse : W → Fin g} (P : OrderedResidueMatchings H coarse q c m h)
    (σ : Equiv.Perm W) (hσ : ∀ x y, H.Adj x y ↔ σ x = y) :
    ∃ tag : W → Fin q, ∀ i x y, (P.matching i).Adj x y ↔ tag x = i ∧ σ x = y := by
  classical
  have hOwn (x : W) : ∃! i, (P.matching i).Adj x (σ x) :=
    (P.partition _ _).mp ((hσ _ _).mpr rfl)
  choose tag hT hUnique using hOwn
  refine ⟨tag,fun i x y => ⟨?_,?_⟩⟩
  · intro he
    have hxy : σ x = y := (hσ _ _).mp (P.matching_le i he)
    exact ⟨(hUnique x i (hxy.symm ▸ he)).symm,hxy⟩
  · rintro ⟨h,rfl⟩
    exact h ▸ hT x

/-- Convert the balanced request counts of the whole permutation
into a load for each matching and each fine pair. The total of
every fine pair is prescribed exactly, even with integer rounding. -/
theorem exists_balanced_matching_chord_loads (s : Equiv.Perm I) (root : I)
    (σ : Equiv.Perm W) (cluster : W → I) {q scale target : ℕ}
    (H : Fin q → Digraph W) (tag : W → Fin q) (src dst own : E → I)
    (hCycle : ∀ i, s.SameCycle root i)
    (hCluster : ∀ i, ((univ : Finset W).filter (fun x => cluster x = i)).card =
      ((univ : Finset W).filter (fun x => cluster x = s i)).card)
    (hArc : ∀ i x y, (H i).Adj x y ↔ tag x = i ∧ σ x = y)
    (hSize : ∀ i, Fintype.card (Arc (H i)) ≤ scale/2)
    (hBlock : ∀ j x,
      (∑ e, if own e = j ∧ src e = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ e, if own e = j ∧ dst e = s x then (1:ℕ) else 0) + (if j = s x then 1 else 0))
    (hScale : 24 ≤ scale) (hLo : q*(12*scale) ≤ target) (hHi : target ≤ q*(12*(scale+1))) :
    ∃ load : Fin q → E → ℕ,
      (∀ i e, 11*scale ≤ load i e ∧ load i e ≤ 13*scale) ∧
      (∀ e, (∑ i, load i e) = target) ∧
      ∀ i x,
        (∑ e, if src e = x then load i e else 0) +
          (∑ a : Arc (H i), if cluster a.val.1 = x then (1:ℕ) else 0) =
        (∑ e, if dst e = s x then load i e else 0) +
          (∑ a : Arc (H i), if cluster a.val.2 = s x then (1:ℕ) else 0) := by
  let a (v : W) := cluster (σ v)
  let b (v : W) := s (cluster v)
  obtain ⟨len,hEnd,hSmall,total,_,hTotal⟩ := exists_balanced_forward_chord_loads s root a b hCycle
    (balanced_requests_of_factor cluster s σ hCluster)
  let R (i : Fin q) := (univ : Finset W).filter (fun v => tag v = i)
  let f (v : W) (x : I) := ∑ p ∈ range (len v), if (s : I → I)^[p] (a v) = x then (1:ℕ) else 0
  let count (i : Fin q) (x : I) := ∑ v ∈ R i, f v x
  let e (i : Fin q) : R i ≃ Arc (H i) :=
    ⟨fun v => ⟨(v.val,σ v.val),(hArc _ _ _).mpr ⟨(mem_filter.mp v.prop).2,rfl⟩⟩,
      fun z => ⟨z.val.1,mem_filter.mpr ⟨mem_univ _,((hArc _ _ _).mp z.prop).1⟩⟩,
      fun _ => rfl,fun z => Subtype.ext (Prod.ext rfl ((hArc _ _ _).mp z.prop).2)⟩
  have hBound (i : Fin q) (x : I) : count i x ≤ scale/2 := by
    have h := sum_le_sum (s := R i) (fun v _ => hSmall v x)
    have hc : (R i).card = Fintype.card (Arc (H i)) :=
      (Fintype.card_coe _).symm.trans (Fintype.card_congr (e i))
    calc
      count i x ≤ (R i).card := by
        simpa only [count,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] using h
      _ = _ := hc
      _ ≤ _ := hSize i
  have hCount (x : I) : (∑ i, count i x) = total := by
    simp only [count,R,sum_filter]
    rw [sum_comm]
    simpa only [sum_ite_eq,mem_univ,if_true] using hTotal x
  have hC : total ≤ q*(scale/2) := by
    rw [←hCount root]
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      (sum_le_sum (s := (univ : Finset (Fin q))) (fun i _ => hBound i root))
  obtain ⟨pad,hPad,hAll⟩ := exists_rounded_chord_padding q scale total target count hScale
    hBound hCount hC hLo hHi
  refine ⟨fun i e => count i (own e)+pad i,fun i e => hPad i (own e),fun e => hAll (own e),?_⟩
  intro i x
  have hh := locally_balanced_augmented_chord_loads s own src dst
    (fun v : R i => a v.val) (fun v : R i => b v.val) (fun v : R i => len v.val)
    (pad i) (fun v => (hEnd v.val).2) hBlock x
  have hOut :
      (∑ z : Arc (H i), if cluster z.val.1 = x then (1:ℕ) else 0) =
      ∑ v : R i, if b v.val = s x then (1:ℕ) else 0 := by
    symm
    apply Fintype.sum_equiv (e i)
    intro v
    change (if s (cluster v.val) = s x then (1:ℕ) else 0) =
      if cluster v.val = x then 1 else 0
    rw [s.injective.eq_iff]
  have hIn :
      (∑ z : Arc (H i), if cluster z.val.2 = s x then (1:ℕ) else 0) =
      ∑ v : R i, if a v.val = s x then (1:ℕ) else 0 := by
    symm
    apply Fintype.sum_equiv (e i)
    intro v
    rfl
  rw [hOut,hIn]
  have he (j : I) : (∑ v : R i, f v.val j) = count i j :=
    Finset.sum_coe_sort (R i) (fun v => f v j)
  change ((∑ e, if src e = x then (∑ v : R i, f v.val (own e))+pad i else 0) +
      ∑ v : R i, if b v.val = s x then (1:ℕ) else 0) =
    ((∑ e, if dst e = s x then (∑ v : R i, f v.val (own e))+pad i else 0) +
      ∑ v : R i, if a v.val = s x then (1:ℕ) else 0) at hh
  simpa only [he] using hh

end OverfullWork.DirectedRobustExpansion
