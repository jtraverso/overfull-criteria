module

public import OverfullWork.DirectedStageParameters
public import OverfullWork.DirectedBatchIteration

@[expose] public section


/-! Construct one entire stage of GGKLO 7.3(ii) by resampling the actual
residual at the start of each small batch. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage
open scoped Classical
universe u v w

/-- Interpret a packing of every element of a restricted index as a
packing on the corresponding finite subset of the original index. -/
def PackingPrefix.fromRestriction {V I J : Type*} {H : Digraph V}
    {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix H (fun j : S => L j.val) univ) : PackingPrefix H L S where
  round j := P.round ⟨j,mem_univ _⟩
  disjoint := by
    intro i j hij
    exact P.disjoint (fun h => hij (congrArg Subtype.val h))

theorem PackingPrefix.used_fromRestriction {V I J : Type*} {H : Digraph V}
    {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix H (fun j : S => L j.val) univ) :
    P.fromRestriction.used = P.used := by
  ext x y
  simp only [PackingPrefix.used,Digraph.iSup_adj]
  exact ⟨fun ⟨j,hj⟩ => ⟨⟨j,mem_univ _⟩,hj⟩,fun ⟨j,hj⟩ => ⟨j.val,hj⟩⟩

private theorem stage_prefix_sum_le {J : Type*} [Fintype J] (S : Finset J) (f : J → ℕ) :
    (∑ i : S, f i.val) ≤ ∑ i, f i := by
  rw [← sum_subtype S (fun _ => Iff.rfl) f]
  exact sum_le_sum_of_subset (subset_univ _)

private theorem reserve_difference {V : Type*} (Γ U : Digraph V) :
    Γ \ (U ⊓ Γ) = Γ \ U := by
  ext x y
  simp only [Digraph.sdiff_adj,Digraph.inf_adj]
  tauto

/-- From global hypotheses, execute a stage of linear order and retain
a uniform half-stage bound on the reserve loss. All constants are
chosen before the host and the current dense center. -/
theorem exists_packing_stage (ν τ α d₀ σ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hα : α ≤ 1) (hτα : 256*(8*τ) ≤ α) (hd₀ : 0 < d₀) (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℝ, 0 < s → 16*s ≤ κ → s ≤ ν →
      ∃ e : ℝ, 0 < e ∧ e ≤ s ∧ ∃ h N : ℕ, 5 ≤ h ∧
        ∀ (δ γ : ℝ), δ ≤ 1 → α+σ ≤ γ → γ ≤ 1 →
        ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
          (D Γ : Digraph V) (L : J → Layout V I) (long : J → I),
          let n := Fintype.card V
          let m := Fintype.card J
          let b := ⌈(e/2)*(n:ℝ)⌉₊
          N ≤ n → Disjoint D Γ → IsRealRobust Γ (2*ν) τ →
          SemidegreesAround D (δ*(n:ℝ)) (s*(n:ℝ)) →
          SemidegreesAround Γ (γ*(n:ℝ)) (s*(n:ℝ)) →
          (m:ℝ) ≤ (κ/64)*(n:ℝ) → m ≤ n → d₀*(n:ℝ)+(m:ℝ) ≤ δ*(n:ℝ) →
          (∀ i, (L i).boundary.card ≤ b ∧ long i ∉ (L i).fixed ∧
            (univ \ insert (long i) (L i).fixed).card*h ≤ b) →
          (∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b) →
          (∀ v, visits (fun i => (L i).boundary) v ≤ ⌊s*(n:ℝ)⌋₊) →
          ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
            ∀ v, ((inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v:ℕ):ℝ) ≤ (s/2)*(n:ℝ) := by
  obtain ⟨κ,hκ,hLocal⟩ := exists_small_batch_parameters.{u,v,w} ν τ α d₀ σ
    hν hντ hτ hα hτα hd₀ hσ
  refine ⟨κ,hκ,?_⟩
  intro s hs hSmall hsν
  obtain ⟨k,hWidth,hRecip⟩ := exists_stage_block_count κ s hκ hs hSmall
  let K := k+2
  let l := κ/(K:ℝ)
  have hl : 0 < l := div_pos hκ (by positivity)
  have hK : 0 < K := by dsimp [K]; omega
  obtain ⟨h,N₀,hh,hPack⟩ := hLocal k
  obtain ⟨r,N₁,hr,hGroup⟩ := exists_layout_groups_below_fraction l hl
  let e := min s (s/(24*(r:ℝ)))
  have hrR : 0 < (r:ℝ) := by exact_mod_cast hr
  have he : 0 < e := lt_min hs (by positivity)
  have hes : e ≤ s := min_le_left _ _
  have hel : e ≤ l := by linarith only [hes,hWidth,hs]
  obtain ⟨N₂,hN₂⟩ := exists_nat_ge (max (2/e) (16*(r:ℝ)/s))
  refine ⟨e,he,hes,h,max 1 (max N₀ (max N₁ N₂)),hh,?_⟩
  intro δ γ hδ₁ hγ hγ₁ V _ I _ J _ D Γ L long
  dsimp only
  intro hn hDis hRob hD hG hm hmN hδ hLayout hEnd hAppearance
  let n := Fintype.card V
  let m := Fintype.card J
  let b := ⌈(e/2)*(n:ℝ)⌉₊
  let a := ⌊s*(n:ℝ)⌋₊
  have hOrder : 1 ≤ n ∧ N₀ ≤ n ∧ N₁ ≤ n ∧ N₂ ≤ n := by
    simpa only [max_le_iff] using hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hOrder.1
  have hBound := hN₂.trans (show (N₂:ℝ) ≤ (n:ℝ) by exact_mod_cast hOrder.2.2.2)
  have heN : 2 ≤ e*(n:ℝ) := by
    have h := (div_le_iff₀ he).mp ((le_max_left _ _).trans hBound)
    linarith only [h]
  have hrN : 16*(r:ℝ) ≤ s*(n:ℝ) := by
    have h := (div_le_iff₀ hs).mp ((le_max_right _ _).trans hBound)
    linarith only [h]
  have hb : (b:ℝ) ≤ e*(n:ℝ) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (e/2)*(n:ℝ) by positivity)
    change (b:ℝ) < _ at h
    linarith only [h,heN]
  have hbS := hb.trans (mul_le_mul_of_nonneg_right hes hnR.le)
  have ha : (a:ℝ) ≤ s*(n:ℝ) := Nat.floor_le (by positivity)
  obtain ⟨group,hGroupSize,hGroups,hCover⟩ := hGroup n hOrder.2.2.1 hmN
  let cost (i : Fin r) := 3*b+2*(((group i).card+K-1)/K)
  have hCardSum : (∑ i : Fin r,(group i).card) = m :=
    (card_biUnion (s := (univ : Finset (Fin r))) (fun _ _ _ _ hij => hGroups hij)).symm.trans
      (by rw [hCover,card_univ])
  have hCost : ((∑ i,cost i:ℕ):ℝ) ≤ (s/2)*(n:ℝ) := by
    have hBS : 24*(r:ℝ)*(b:ℝ) ≤ s*(n:ℝ) := by
      have h := (le_div_iff₀ (show 0 < 24*(r:ℝ) by positivity)).mp
        (show e ≤ s/(24*(r:ℝ)) from min_le_right _ _)
      have hc := mul_le_mul_of_nonneg_right h hnR.le
      have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 24*(r:ℝ) by positivity)
      nlinarith only [hc,hb']
    have hOver : (∑ _i : Fin r, ((b+2*b:ℕ):ℝ))+2*((univ : Finset (Fin r)).card:ℝ) ≤
        (s/4)*(n:ℝ) := by
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      nlinarith only [hBS,hrN]
    have hsizes : (∑ i : Fin r,((group i).card:ℝ)) ≤ (κ/64)*(n:ℝ) := by
      rw [← Nat.cast_sum,hCardSum]; exact hm
    have h := total_stage_reserve_charge univ κ s n K hκ hK hRecip
      (fun i : Fin r => (group i).card) (fun _ => b) (fun _ => b) hsizes hOver
    have hid : ∀ i : Fin r, b+2*b+2*(((group i).card+K-1)/K) = cost i := by
      intro i; dsimp [cost]; omega
    simpa only [hid,Nat.cast_sum] using h
  obtain ⟨P,hLoss,_⟩ := exists_batch_iteration D Γ L group cost hGroups hCover (2*ν) τ ν
    (by positivity) (hν.trans_le hντ).le hRob
    (by have h := mul_le_mul_of_nonneg_right hsν hnR.le; linarith only [h,hCost])
    (by
      intro S i hi P hLoss
      let U := P.used
      let T := S.biUnion group
      let D' := D \ U
      let Γ' := Γ \ U
      let g := ∑ j ∈ S,cost j
      let δ' := δ-(T.card:ℝ)/(n:ℝ)
      have hPrefix : (g:ℝ) ≤ (s/2)*(n:ℝ) := by
        have h : g ≤ ∑ j,cost j := sum_le_sum_of_subset (subset_univ _)
        exact (show (g:ℝ) ≤ _ by exact_mod_cast h).trans hCost
      have hQ : IsRealRobust Γ' ν τ := by
        change IsRealRobust (Γ \ U) ν τ
        rw [← reserve_difference Γ U]
        exact real_robust_after_reserve_use Γ (U ⊓ Γ) (2*ν) τ ν g (by positivity)
          (hν.trans_le hντ).le hRob (fun v => (Nat.le_add_right _ _).trans (hLoss v))
          (by have h := mul_le_mul_of_nonneg_right hsν hnR.le; linarith only [h,hPrefix])
      have hA (v : V) : visits (fun j : T => (L j.val).boundary) v ≤ a :=
        (visits_prefix_le T _ v).trans (hAppearance v)
      have hB (v : V) (d : Bool) : (∑ j : T,(L j.val).endpointLoad d v) ≤ b := by
        apply (stage_prefix_sum_le T (fun j => (L j).endpointLoad d v)).trans
        apply le_trans _ (hEnd v)
        apply sum_le_sum
        intro j _
        cases d <;> omega
      have hMax : ((max b (a+g):ℕ):ℝ) ≤ (3*s/2)*(n:ℝ) := by
        have h : ((max b (a+g):ℕ):ℝ) = max (b:ℝ) ((a:ℝ)+(g:ℝ)) := by
          exact_mod_cast (rfl : max b (a+g) = max b (a+g))
        rw [h]
        exact max_le (by linarith only [hbS,mul_nonneg hs.le hnR.le])
          (by linarith only [ha,hPrefix])
      have hBnd : s*(n:ℝ)+((max b (a+g):ℕ):ℝ) ≤ l*(n:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hWidth hnR.le
        linarith only [hMax,h, mul_nonneg hs.le hnR.le]
      have hRBnd : s*(n:ℝ)+(g:ℝ) ≤ l*(n:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hWidth hnR.le
        linarith only [hPrefix,h,mul_nonneg hs.le hnR.le]
      have hδN : δ'*(n:ℝ) = δ*(n:ℝ)-(T.card:ℝ) := by
        dsimp [δ']; rw [sub_mul,div_mul_cancel₀ _ hnR.ne']
      have hδ' : d₀ ≤ δ' := by
        apply (mul_le_mul_iff_left₀ hnR).mp
        rw [hδN]
        have hc : (T.card:ℝ) ≤ (m:ℝ) := by exact_mod_cast card_le_univ T
        linarith only [hδ,hc]
      have hδ₁' : δ' ≤ 1 := (sub_le_self _ (by positivity)).trans hδ₁
      have hDev := P.residual_degree_deviations hDis a b g (δ*(n:ℝ)) (γ*(n:ℝ))
        (s*(n:ℝ)) (s*(n:ℝ)) hA hB hLoss hD hG
      have hD' : SemidegreesAround D' (δ'*(n:ℝ)) (l*(n:ℝ)) := by
        intro v
        rw [hδN]
        exact ⟨(hDev v).1.trans hBnd,(hDev v).2.1.trans hBnd⟩
      have hG' : SemidegreesAround Γ' (γ*(n:ℝ)) (l*(n:ℝ)) := fun v =>
        ⟨(hDev v).2.2.1.trans hRBnd,(hDev v).2.2.2.trans hRBnd⟩
      have hLayout' (j : group i) :
          (L j.val).boundary.card ≤ b ∧ long j.val ∉ (L j.val).fixed ∧
            (univ \ insert (long j.val) (L j.val).fixed).card*h ≤ b := hLayout j.val
      have hEnd' (v : V) : (∑ j : group i, ((L j.val).endpointLoad true v+
          (L j.val).endpointLoad false v)) ≤ b :=
        (stage_prefix_sum_le (group i) _).trans (hEnd v)
      obtain ⟨Q,hQloss⟩ := hPack δ' γ e hδ' hδ₁' hγ hγ₁ he hel D' Γ'
        (fun j : group i => L j.val) (fun j => long j.val) hOrder.2.1 heN
        (hDis.mono sdiff_le sdiff_le) hQ hD' hG'
        (by simpa only [Fintype.card_coe] using hGroupSize i) hLayout' hEnd'
      have hHost : (D ⊔ Γ) \ U = D' ⊔ Γ' := sup_sdiff
      rw [hHost]
      refine ⟨Q.fromRestriction,fun v => ?_⟩
      rw [PackingPrefix.used_fromRestriction]
      simpa only [cost,Fintype.card_coe] using hQloss v)
  exact ⟨P,fun v => (show ((inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v:ℕ):ℝ) ≤
    ((∑ i,cost i:ℕ):ℝ) by exact_mod_cast hLoss v).trans hCost⟩

end OverfullWork.DirectedSpanningConfiguration
