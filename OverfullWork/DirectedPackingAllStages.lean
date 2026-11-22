module

public import OverfullWork.DirectedPackingStage

@[expose] public section


/-! The two-scale layout packing of GGKLO 7.3. The stage budget depends
on the number of completed stages, and the dense center depends on
the number of completed layouts. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage
open scoped Classical
universe u v w

/-- Uniform directed layout packing with robust remainder. The single
small input tolerance can enforce all four layout bounds because the
number of stages is fixed before the host order. -/
theorem exists_directed_layout_packing (ν τ α d₀ σ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hα : α ≤ 1) (hτα : 256*(8*τ) ≤ α) (hd₀ : 0 < d₀) (hσ : 0 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (δ γ : ℝ), δ ≤ 1 → α+σ ≤ γ → γ ≤ 1 →
      ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
        (D Γ : Digraph V) (L : J → Layout V I) (long : J → I),
        let n := Fintype.card V
        let m := Fintype.card J
        N ≤ n → m ≤ n → Disjoint D Γ → IsRealRobust Γ (3*ν) τ →
        d₀*(n:ℝ)+(m:ℝ) ≤ δ*(n:ℝ) →
        SemidegreesAround D (δ*(n:ℝ)) (ε*(n:ℝ)) →
        SemidegreesAround Γ (γ*(n:ℝ)) (ε*(n:ℝ)) →
        (∀ i, ((L i).boundary.card:ℝ) ≤ ε*(n:ℝ) ∧ long i ∉ (L i).fixed ∧
          (((univ \ insert (long i) (L i).fixed).card:ℕ):ℝ) ≤ ε*(n:ℝ)) →
        (∀ v, ((∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v):ℕ):ℝ)
          ≤ ε*(n:ℝ)) →
        (∀ v, (visits (fun i => (L i).boundary) v:ℝ) ≤ ε*(n:ℝ)) →
        ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
          IsRealRobust (Γ \ P.used) (2*ν) τ := by
  obtain ⟨κ,hκ,hStage⟩ := exists_packing_stage.{u,v,w} ν τ α d₀ σ hν hντ hτ hα hτα hd₀ hσ
  obtain ⟨r,N₁,hr,hGroup⟩ := exists_layout_groups_below_fraction (κ/64) (by positivity)
  let top := min ν (κ/16)
  have htop : 0 < top := lt_min hν (by positivity)
  obtain ⟨s,hS,_,hSbudget⟩ := exists_batch_scale_schedule r top (1/2) htop (by norm_num)
  have hSν (i : ℕ) (hi : i ≤ r) : s i ≤ ν := (hS i hi).2.trans (min_le_left _ _)
  have hSκ (i : ℕ) (hi : i ≤ r) : 16*s i ≤ κ := by
    have h := (hS i hi).2.trans (min_le_right ν (κ/16))
    linarith only [h]
  let funLevel := fun i : Fin r => hStage (s i.val) (hS i.val i.isLt.le).1
    (hSκ i.val i.isLt.le) (hSν i.val i.isLt.le)
  choose e he hes h N₂ hFive hRun using funLevel
  let H := (univ : Finset (Fin r)).sup h
  let threshold := (univ : Finset (Fin r)).sup N₂
  let E := ((univ : Finset (Fin r)).image e)
  haveI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have hE : E.Nonempty := ⟨e ⟨0,hr⟩,mem_image.mpr ⟨⟨0,hr⟩,mem_univ _,rfl⟩⟩
  let small := E.min' hE
  have hSmall : 0 < small := by
    obtain ⟨i,_,hi⟩ := mem_image.mp (min'_mem E hE)
    change 0 < E.min' hE
    rw [← hi]
    exact he i
  have hSmallLe (i : Fin r) : small ≤ e i := min'_le E _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  let ε := min (s 0/2) (small/(2*((H:ℝ)+1)))
  have hε : 0 < ε := lt_min (by have := (hS 0 (Nat.zero_le _)).1; positivity) (by positivity)
  have hεS : 2*ε ≤ s 0 := by
    have h : ε ≤ s 0/2 := min_le_left _ _
    linarith only [h]
  have hεH : 2*ε*((H:ℝ)+1) ≤ small := by
    have h := (le_div_iff₀ (show 0 < 2*((H:ℝ)+1) by positivity)).mp
      (show ε ≤ small/(2*((H:ℝ)+1)) from min_le_right _ _)
    nlinarith only [h]
  obtain ⟨N₃,hN₃⟩ := exists_nat_ge (2/small)
  refine ⟨ε,hε,max 1 (max N₁ (max threshold N₃)),?_⟩
  intro δ γ hδ₁ hγ hγ₁ V _ I _ J _ D Γ L long
  dsimp only
  intro hn hmN hDis hRob hδ hD hΓ hLayout hEndpoint hApp
  let n := Fintype.card V
  let m := Fintype.card J
  let a := ⌊ε*(n:ℝ)⌋₊
  have hOrder : 1 ≤ n ∧ N₁ ≤ n ∧ threshold ≤ n ∧ N₃ ≤ n := by
    simpa only [max_le_iff] using hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hOrder.1
  have ha : (a:ℝ) ≤ ε*(n:ℝ) := Nat.floor_le (by positivity)
  have hApp' (v : V) : visits (fun i => (L i).boundary) v ≤ a :=
    Nat.le_floor (hApp v)
  have hEnd' (v : V) : (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ a :=
    Nat.le_floor (hEndpoint v)
  obtain ⟨group,hGroupSize,hGroups,hCover⟩ := hGroup n hOrder.2.1 hmN
  let cost (i : ℕ) := ⌊(s i/2)*(n:ℝ)⌋₊
  let budget (S : Finset (Fin r)) := ∑ i ∈ range S.card,cost i
  have hBudget (j : ℕ) (hj : j ≤ r) :
      s 0*(n:ℝ)+((∑ i ∈ range j,cost i:ℕ):ℝ) ≤ s j*(n:ℝ) := by
    have hf := hSbudget (fun i => s i/2)
      (fun i hi => ⟨by have := (hS i hi.le).1; positivity,by ring_nf; rfl⟩) j hj
    have hsum : ((∑ i ∈ range j,cost i:ℕ):ℝ) ≤ (∑ i ∈ range j,s i/2)*(n:ℝ) := by
      rw [Nat.cast_sum, sum_mul]
      apply sum_le_sum
      intro i hi
      exact Nat.floor_le (by have := (hS i ((mem_range.mp hi).le.trans hj)).1; positivity)
    have hh := mul_le_mul_of_nonneg_right hf hnR.le
    linarith only [hsum,hh]
  have hAll : (budget (univ : Finset (Fin r)):ℝ) ≤ ν*(n:ℝ) := by
    have hh := hBudget r le_rfl
    have h := mul_le_mul_of_nonneg_right (hSν r le_rfl) hnR.le
    have hz := mul_nonneg (hS 0 (Nat.zero_le _)).1.le hnR.le
    change ((∑ i ∈ range ((univ : Finset (Fin r)).card),cost i:ℕ):ℝ) ≤ _
    rw [card_univ,Fintype.card_fin]
    linarith only [hh,h,hz]
  obtain ⟨P,_,hFinal⟩ := exists_batch_iteration_with_prefix_budget D Γ L group budget (by simp [budget])
    hGroups hCover (3*ν) τ (2*ν) (by positivity) (hν.trans_le hντ).le hRob
    (by linarith only [hAll]) (by
      intro S i hi P hLoss
      let U := P.used
      let T := S.biUnion group
      let j : Fin r := ⟨S.card,by
        simpa only [Fintype.card_fin] using card_lt_univ_of_notMem hi⟩
      let D' := D \ U
      let Γ' := Γ \ U
      let δ' := δ-(T.card:ℝ)/(n:ℝ)
      have hPre : s 0*(n:ℝ)+(budget S:ℝ) ≤ s j.val*(n:ℝ) := hBudget _ j.isLt.le
      have hA (v : V) : visits (fun x : T => (L x.val).boundary) v ≤ a :=
        (visits_prefix_le T _ v).trans (hApp' v)
      have hB (v : V) (b : Bool) : (∑ x : T,(L x.val).endpointLoad b v) ≤ a := by
        rw [← sum_subtype T (fun _ => Iff.rfl) (fun x => (L x).endpointLoad b v)]
        apply (sum_le_sum_of_subset (subset_univ T)).trans
        apply le_trans _ (hEnd' v)
        apply sum_le_sum
        intro x _
        cases b <;> omega
      have hError : ε*(n:ℝ)+((max a (a+budget S):ℕ):ℝ) ≤ s j.val*(n:ℝ) := by
        have hEq : max a (a+budget S) = a+budget S := max_eq_right (by omega)
        rw [hEq]
        push_cast
        have h := mul_le_mul_of_nonneg_right hεS hnR.le
        linarith only [hPre,h,ha]
      have hΓError : ε*(n:ℝ)+(budget S:ℝ) ≤ s j.val*(n:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hεS hnR.le
        linarith only [hPre,h,mul_nonneg hε.le hnR.le]
      have hδN : δ'*(n:ℝ) = δ*(n:ℝ)-(T.card:ℝ) := by
        dsimp [δ']; rw [sub_mul,div_mul_cancel₀ _ hnR.ne']
      have hDisj : Disjoint T (group i) := by
        apply disjoint_left.mpr
        intro x hx hxi
        obtain ⟨k,hk,hxk⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp (hGroups (ne_of_mem_of_not_mem hk hi)) hxk hxi
      have hT : T.card+(group i).card ≤ m := by
        rw [← card_union_of_disjoint hDisj]
        exact card_le_univ _
      have hδ' : d₀*(n:ℝ)+((group i).card:ℝ) ≤ δ'*(n:ℝ) := by
        rw [hδN]
        have h : (T.card:ℝ)+((group i).card:ℝ) ≤ (m:ℝ) := by exact_mod_cast hT
        linarith only [h,hδ]
      have hδ₁' : δ' ≤ 1 := (sub_le_self _ (by positivity)).trans hδ₁
      have hDev := P.residual_degree_deviations hDis a a (budget S) (δ*(n:ℝ)) (γ*(n:ℝ))
        (ε*(n:ℝ)) (ε*(n:ℝ)) hA hB hLoss hD hΓ
      have hD' : SemidegreesAround D' (δ'*(n:ℝ)) (s j.val*(n:ℝ)) := by
        intro v
        rw [hδN]
        exact ⟨(hDev v).1.trans hError,(hDev v).2.1.trans hError⟩
      have hΓ' : SemidegreesAround Γ' (γ*(n:ℝ)) (s j.val*(n:ℝ)) := fun v =>
        ⟨(hDev v).2.2.1.trans hΓError,(hDev v).2.2.2.trans hΓError⟩
      have hRes : IsRealRobust Γ' (2*ν) τ := by
        have he : Γ \ (U ⊓ Γ) = Γ' := by
          ext x y; simp only [Γ',Digraph.sdiff_adj,Digraph.inf_adj]; tauto
        rw [← he]
        exact real_robust_after_reserve_use Γ (U ⊓ Γ) (3*ν) τ (2*ν) (budget S) (by positivity)
          (hν.trans_le hντ).le hRob (fun v => (Nat.le_add_right _ _).trans (hLoss v))
          (by
            have h := mul_le_mul_of_nonneg_right (hSν j.val j.isLt.le) hnR.le
            linarith only [h,hPre,mul_nonneg (hS 0 (Nat.zero_le _)).1.le hnR.le])
      have hNj : N₂ j ≤ n := (le_sup (f := N₂) (mem_univ j)).trans hOrder.2.2.1
      have hHj : h j ≤ H := le_sup (f := h) (mem_univ j)
      have hεj : ε*((h j:ℕ):ℝ) ≤ e j/2 := by
        have h := mul_le_mul_of_nonneg_left
          (show (h j:ℝ) ≤ (H:ℝ)+1 by exact_mod_cast (show h j ≤ H+1 by omega)) hε.le
        nlinarith only [h,hεH,hSmallLe j]
      have hεj' : ε ≤ e j/2 := by
        have h := mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) H)
        nlinarith only [h,hεH,hSmallLe j]
      let b := ⌈(e j/2)*(n:ℝ)⌉₊
      have hLay (x : group i) : (L x.val).boundary.card ≤ b ∧ long x.val ∉ (L x.val).fixed ∧
          (univ \ insert (long x.val) (L x.val).fixed).card*h j ≤ b := by
        obtain ⟨h₁,h₂,h₃⟩ := hLayout x.val
        have hUp := Nat.le_ceil ((e j/2)*(n:ℝ))
        have hεN := mul_le_mul_of_nonneg_right hεj' hnR.le
        have h₁' : ((L x.val).boundary.card:ℝ) ≤ (b:ℝ) := h₁.trans (hεN.trans hUp)
        have h₃' : ((((univ \ insert (long x.val) (L x.val).fixed).card*h j:ℕ)):ℝ) ≤ (b:ℝ) := by
          push_cast
          have hPay := mul_le_mul_of_nonneg_right h₃ (Nat.cast_nonneg (α := ℝ) (h j))
          have hh := mul_le_mul_of_nonneg_right hεj hnR.le
          nlinarith only [hPay,hh,hUp]
        exact ⟨by exact_mod_cast h₁',h₂,by exact_mod_cast h₃'⟩
      have hEnd (v : V) : (∑ x : group i, ((L x.val).endpointLoad true v+
          (L x.val).endpointLoad false v)) ≤ b := by
        rw [← sum_subtype (group i) (fun _ => Iff.rfl) (fun x =>
          (L x).endpointLoad true v+(L x).endpointLoad false v)]
        apply (sum_le_sum_of_subset (subset_univ (group i))).trans
        have hεN := mul_le_mul_of_nonneg_right hεj' hnR.le
        exact_mod_cast (hEndpoint v).trans (hεN.trans (Nat.le_ceil ((e j/2)*(n:ℝ))))
      have hAp (v : V) :
          visits (fun x : group i => (L x.val).boundary) v ≤ ⌊s j.val*(n:ℝ)⌋₊ := by
        apply Nat.le_floor
        have hPre' := hPre
        have hb : 0 ≤ (budget S:ℝ) := Nat.cast_nonneg _
        have h := mul_le_mul_of_nonneg_right hεS hnR.le
        have hle : (visits (fun x : group i => (L x.val).boundary) v:ℝ) ≤ ε*(n:ℝ) :=
          (show (visits (fun x : group i => (L x.val).boundary) v:ℝ) ≤
              (visits (fun x => (L x).boundary) v:ℝ) by
            exact_mod_cast visits_prefix_le (group i) (fun x => (L x).boundary) v).trans (hApp v)
        linarith only [hPre',hb,h,hle,mul_nonneg hε.le hnR.le]
      obtain ⟨Q,hQL⟩ := hRun j δ' γ hδ₁' hγ hγ₁ D' Γ'
        (fun x : group i => L x.val) (fun x => long x.val) hNj
        (hDis.mono sdiff_le sdiff_le) hRes hD' hΓ'
        (by simpa only [Fintype.card_coe] using hGroupSize i)
        (by simpa only [Fintype.card_coe] using (card_le_univ (group i)).trans hmN)
        (by simpa only [Fintype.card_coe] using hδ') hLay hEnd hAp
      have hHost : (D ⊔ Γ) \ U = D' ⊔ Γ' := sup_sdiff
      rw [hHost]
      refine ⟨Q.fromRestriction,fun v => ?_⟩
      rw [PackingPrefix.used_fromRestriction]
      have hQL' := Nat.le_floor (hQL v)
      letI : DecidableEq (Fin r) := Classical.decEq _
      have hEq : budget (insert i S) = budget S+cost S.card := by
        simp only [budget,card_insert_of_notMem hi,sum_range_succ]
      change inDegree (Q.used ⊓ Γ') v + outDegree (Q.used ⊓ Γ') v + budget S ≤ budget (insert i S)
      rw [hEq,Nat.add_comm (budget S)]
      exact Nat.add_le_add_right hQL' _)
  exact ⟨P,hFinal⟩

end OverfullWork.DirectedSpanningConfiguration
