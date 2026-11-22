module

public import OverfullWork.DenseHall
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section


/-! The adjacent-layer matching of Girão–Granet–Kühn–Lo–Osthus,
Proposition 4.19. Only a lower bound on the left degrees and an upper
bound on the right degrees enter the deficiency calculation. -/
namespace OverfullWork.NearRegularBipartiteMatching

open Finset
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

/-- A partial matching, recorded by the left vertices it actually matches. -/
structure PartialMatching (R : A → B → Prop) where
  domain : Finset A
  target : domain ↪ B
  adjacent : ∀ a : domain, R a.val (target a)

noncomputable def neighbours (R : A → B → Prop) (S : Finset A) : Finset B :=
  univ.filter fun b => ∃ a ∈ S, R a b

private theorem density_count (R : A → B → Prop) (S : Finset A) (lo hi : ℝ)
    (hlo : ∀ a, lo ≤ ((univ.filter (R a)).card:ℝ))
    (hhi : ∀ b, ((univ.filter fun a => R a b).card:ℝ) ≤ hi) :
    lo*(S.card:ℝ) ≤ hi*((neighbours R S).card:ℝ) := by
  let T := neighbours R S
  have hRow : ∀ a ∈ S, (T.filter (R a)).card = (univ.filter (R a)).card := by
    intro a ha
    congr 1
    ext b
    constructor
    · intro hb
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hb).2⟩
    · intro hb
      have h := (mem_filter.mp hb).2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, a, ha, h⟩, h⟩
  have hCol : ∀ b, ((S.filter fun a => R a b).card:ℝ) ≤ hi := by
    intro b
    have hc := card_le_card (filter_subset_filter (fun a => R a b) (subset_univ S))
    exact (by exact_mod_cast hc : ((S.filter fun a => R a b).card:ℝ) ≤
      ((univ.filter fun a => R a b).card:ℝ)).trans (hhi b)
  calc
    lo*(S.card:ℝ) = ∑ _a ∈ S, lo := by simp [mul_comm]
    _ ≤ ∑ a ∈ S, ((T.filter (R a)).card:ℝ) :=
      sum_le_sum (fun a ha => by rw [hRow a ha]; exact hlo a)
    _ = ∑ b ∈ T, ((S.filter fun a => R a b).card:ℝ) := by
      simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [sum_comm]
    _ ≤ ∑ _b ∈ T, hi := sum_le_sum (fun b _ => hCol b)
    _ = _ := by simp [T, mul_comm]

/-- A uniform upper bound on the Hall deficit yields an actual matching
with at most that many unmatched left vertices. -/
theorem exists_of_deficit (R : A → B → Prop) (e : ℕ)
    (hHall : ∀ S : Finset A, S.card ≤ (neighbours R S).card+e) :
    ∃ M : PartialMatching R, Fintype.card A ≤ M.domain.card+e := by
  classical
  let R' : A → B ⊕ Fin e → Prop := fun a b => b.elim (R a) (fun _ => True)
  have hHall' : ∀ S : Finset A, S.card ≤ (neighbours R' S).card := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl|⟨a,ha⟩
    · simp
    · have hEq : neighbours R' S = (neighbours R S).disjSum (univ : Finset (Fin e)) := by
        ext b
        cases b with
        | inl b => simp [neighbours, R']
        | inr i => simp [neighbours, R']; exact ⟨a,ha⟩
      rw [hEq, card_disjSum, card_univ, Fintype.card_fin]
      exact hHall S
  obtain ⟨f, hf, ha⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R').mp hHall'
  let S := univ.filter fun a => ∃ b, f a = Sum.inl b
  let T := univ \ S
  have hLeft : ∀ a : S, ∃ b, f a.val = Sum.inl b := fun a => (mem_filter.mp a.prop).2
  choose g hg using hLeft
  let M : PartialMatching R :=
    ⟨S, ⟨g, fun x y he => Subtype.ext (hf ((hg x).trans (he ▸ (hg y).symm)))⟩,
      fun x => by have hh := ha x.val; rw [hg x] at hh; exact hh⟩
  have hRight : ∀ a : T, ∃ i : Fin e, f a.val = Sum.inr i := by
    intro a
    have hz := (mem_sdiff.mp a.prop).2
    cases h : f a.val with
    | inl b => exact False.elim (hz (mem_filter.mpr ⟨mem_univ _, b, h⟩))
    | inr i => exact ⟨i,rfl⟩
  choose g' hg' using hRight
  have hInject : Function.Injective g' := by
    intro x y he
    exact Subtype.ext (hf ((hg' x).trans (he ▸ (hg' y).symm)))
  have hRightCard := Fintype.card_le_of_injective g' hInject
  rw [Fintype.card_coe, Fintype.card_fin] at hRightCard
  have hSum : T.card+S.card = Fintype.card A :=
    (card_sdiff_add_card_eq_card (subset_univ S)).trans card_univ
  exact ⟨M, by change Fintype.card A ≤ S.card+e; omega⟩

/-- A degree-ratio form of the adjacent-layer matching bound, with no
rounding loss. The deficit is the floor of the real edge-count bound. -/
theorem exists_of_degree_ratio (R : A → B → Prop) (lo hi : ℝ)
    (hhi : 0 < hi) (hOrder : lo ≤ hi)
    (hLeft : ∀ a, lo ≤ ((univ.filter (R a)).card:ℝ))
    (hRight : ∀ b, ((univ.filter fun a => R a b).card:ℝ) ≤ hi) :
    ∃ M : PartialMatching R, (lo/hi)*(Fintype.card A:ℝ) ≤ (M.domain.card:ℝ) := by
  let loss := (1-lo/hi)*(Fintype.card A:ℝ)
  have hLoss : 0 ≤ loss := mul_nonneg (sub_nonneg.mpr ((div_le_iff₀ hhi).mpr (by simpa using hOrder)))
    (Nat.cast_nonneg _)
  let e := ⌊loss⌋₊
  have he : (e:ℝ) ≤ loss := Nat.floor_le hLoss
  have hHall : ∀ S : Finset A, S.card ≤ (neighbours R S).card+e := by
    intro S
    have hCount := density_count R S lo hi hLeft hRight
    have hScaled : (lo/hi)*(S.card:ℝ) ≤ ((neighbours R S).card:ℝ) := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hhi).mpr (hCount.trans_eq (mul_comm _ _))
    have hCard : (S.card:ℝ) ≤ Fintype.card A := by exact_mod_cast card_le_univ S
    have hN : 0 ≤ 1-lo/hi := sub_nonneg.mpr ((div_le_iff₀ hhi).mpr (by simpa using hOrder))
    have hPay := mul_le_mul_of_nonneg_left hCard hN
    have hDef : ((S.card-(neighbours R S).card:ℕ):ℝ) ≤ loss := by
      by_cases hs : (neighbours R S).card ≤ S.card
      · rw [Nat.cast_sub hs]
        dsimp [loss]
        nlinarith only [hPay, hScaled]
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
        exact hLoss
    have hFin := (Nat.le_floor_iff hLoss).mpr hDef
    change S.card-(neighbours R S).card ≤ e at hFin
    omega
  obtain ⟨M,hM⟩ := exists_of_deficit R e hHall
  have hM' : (Fintype.card A:ℝ) ≤ (M.domain.card:ℝ)+(e:ℝ) := by exact_mod_cast hM
  exact ⟨M, by dsimp [loss] at he; nlinarith only [he,hM']⟩

/-- Proposition 4.19 with the published lower bound on matching size. -/
theorem exists_near_regular_matching (R : A → B → Prop) (n δ ε : ℝ)
    (hn : 0 < n) (hε : 0 ≤ ε) (hGap : ε ≤ δ) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hA : (1-ε)*n ≤ (Fintype.card A:ℝ))
    (hLeft : ∀ a, (δ-ε)*n ≤ ((univ.filter (R a)).card:ℝ))
    (hRight : ∀ b, ((univ.filter fun a => R a b).card:ℝ) ≤ (δ+ε)*n) :
    ∃ M : PartialMatching R, (1-3*ε/δ)*n ≤ (M.domain.card:ℝ) := by
  have hUpper : 0 < (δ+ε)*n := mul_pos (by linarith) hn
  obtain ⟨M,hM⟩ := exists_of_degree_ratio R _ _ hUpper
    (by gcongr; linarith) hLeft hRight
  have hRatio : ((δ-ε)*n)/((δ+ε)*n) = (δ-ε)/(δ+ε) := by
    rw [div_eq_div_iff hUpper.ne' (by linarith : δ+ε ≠ 0)]
    ring
  rw [hRatio] at hM
  have hA' := mul_le_mul_of_nonneg_left hA
    (div_nonneg (sub_nonneg.mpr hGap) (by linarith : 0 ≤ δ+ε))
  have hScalar : 1-3*ε/δ ≤ (δ-ε)/(δ+ε)*(1-ε) := by
    have hDecomp : (δ-ε)/(δ+ε)*(1-ε) = ((δ-ε)*(1-ε))/(δ+ε) := by ring
    rw [hDecomp]
    apply (le_div_iff₀ (show 0 < δ+ε by linarith)).mpr
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hPay : (3:ℝ)*ε/δ*δ = 3*ε := by field_simp
    calc
      _ = δ*(δ+ε)-3*ε*(δ+ε) := by
        calc
          _ = δ*(δ+ε)-(3*ε/δ*δ)*(δ+ε) := by ring
          _ = _ := by rw [hPay]
      _ ≤ _ := by nlinarith only
        [mul_nonneg (mul_nonneg hε hδ.le) (sub_nonneg.mpr hδ'), mul_nonneg (sq_nonneg ε) hδ.le, sq_nonneg ε]
  have hh := mul_le_mul_of_nonneg_right hScalar hn.le
  rw [mul_assoc] at hh
  exact ⟨M, hh.trans (hA'.trans hM)⟩

end OverfullWork.NearRegularBipartiteMatching
